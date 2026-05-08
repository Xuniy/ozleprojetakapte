functor
import
   System
   Application
export
   decode:Decode
   executeBlockchain:ExecuteBlockchain
define
   %% --- FONCTIONS DE BASE ---
   fun {Puissance X N}
      if N == 0 then 1 else X * {Puissance X N-1} end
   end

   fun {TransactionHash T}
      (T.nonce + T.sender + T.receiver + T.value) mod {Puissance 10 6}
   end

   fun {Somme_T_lst Liste}
      case Liste of nil then 0
      [] H|T then {TransactionHash H} + {Somme_T_lst T}
      end
   end

   fun {BlockHash B}
      (B.number + B.previousHash + {Somme_T_lst B.transactions}) mod {Puissance 10 6}
   end

   fun {Effort T N Acc}
      if T.value > 10 then
         {Effort transition(value: T.value div 10) N+1 Acc+{Puissance 2 N}}
      else Acc end
   end

   %% --- GESTION DE L'ÉTAT (Conforme 2.1.6) ---
   
   %% Correction de AdaptGenesis : pas besoin d'import Record spécial
   fun {AdaptGenesis GenesisState}
      {Record.mapInd GenesisState 
       fun {$ _ Balance} user(balance:Balance nonce:0) end}
   end

   fun {Valid_transaction T State}
      local 
         %% Utilise CondSelect pour gérer les nouveaux utilisateurs (solde montant reçu)
         Sender = {CondSelect State T.sender user(balance:0 nonce:0)}
      in
         if T.max_effort >= 0 andthen
            T.max_effort >= {Effort T 1 1} andthen
            T.value >= 0 andthen
            Sender.balance >= T.value andthen
            T.hash == {TransactionHash T} andthen
            T.nonce == Sender.nonce + 1 
         then true else false end
      end
   end

   fun {NewState State T}
      local
         S = T.sender R = T.receiver V = T.value
         OldS = {CondSelect State S user(balance:0 nonce:0)}
         OldR = {CondSelect State R user(balance:0 nonce:0)}
         %% Nouveau sender : balance - value, nonce + 1
         NS = user(balance: OldS.balance - V nonce: OldS.nonce + 1)
         %% Nouveau receiver : balance + value, garde son nonce
         NR = user(balance: OldR.balance + V nonce: OldR.nonce)
      in
         {AdjoinAt {AdjoinAt State S NS} R NR}
      end
   end

   %% --- LOGIQUE BLOCKCHAIN ---

   fun {CheckBlockTransactions Trans State Num AccEffort}
      case Trans of nil then nil
      [] T|Reste then
         local E = {Effort T 1 1} in
            if {Valid_transaction T State} andthen 
               T.block_number == Num andthen (AccEffort + E) =< 300 
            then
               T | {CheckBlockTransactions Reste {NewState State T} Num AccEffort + E}
            else {CheckBlockTransactions Reste State Num AccEffort} end
         end
      end
   end

   fun {CreateBlock Transactions State Num PrevHash}
      local
         ValidT = {CheckBlockTransactions Transactions State Num 0}
         B = block(number: Num previousHash: PrevHash transactions: ValidT)
      in
         {Adjoin B block(hash: {BlockHash B})}
      end
   end

   fun {BuildChain State Trans Num PrevHash}
      local B = {CreateBlock Trans State Num PrevHash} in
         if B.transactions == nil then nil # State
         else
            local 
               NextS = {UpdateStateWithList State B.transactions}
               Rec = {BuildChain NextS Trans Num+1 B.hash}
            in (B | Rec.1) # Rec.2 end
         end
      end
   end

   fun {UpdateStateWithList State Lst}
      case Lst of nil then State
      [] H|T then {UpdateStateWithList {NewState State H} T}
      end
   end

   Tableau_Sharelock=tableau(10:a 11:b 12:c 13:d 14:e 15:f 16:g 17:h 18:i 19:j 20:k 21:l 22:m 23:n 24:o 25:p 26:q 27:r 28:s 29:t 30:u 31:v 32:w 33:x 34:y 35:z 36:' ')

   fun {Decrypt Number}
      local N = (Number mod 37) in
         if N < 10 then Tableau_Sharelock.36 %% Renvoie ' ' (espace)
         else Tableau_Sharelock.N
         end
      end
   end

   fun {TransformToList N}
      {Map {IntToString N} fun {$ Char} Char - 48 end}
   end

   fun {Phrase_Liste Liste}
      case Liste of nil then nil
      []H|H2|T then {Decrypt (10*H+H2)}|{Phrase_Liste T}
      []H|nil then nil
      end
   end

   fun {Phrase Hash} %Transforme un Hash en Liste puis print la liste traduite selon le tableau de Sharelock
      local Actual in
         Actual={TransformToList Hash}
         {Phrase_Liste Actual}
      end
   end
   %% --- DÉCODAGE (2.2) ---
   
   fun {Decode BChain}
   %% Flatten transforme la liste de listes en une simple liste de caractères (String)
      {Flatten 
      case BChain of nil then nil
      [] B|R then {Phrase B.hash} | {Decode R}
      end}
   end

   %% ... (Garder tes fonctions Phrase, Phrase_Liste, etc.) ...

   %% --- EXÉCUTION FINALE ---

   proc {ExecuteBlockchain Genesis Transactions FinalState FinalBlockchain}
      local
         S0 = {AdaptGenesis Genesis}
         %% On ajoute l'effort calculé à chaque transaction
         TransWithEffort = {Map Transactions fun {$ T} {Adjoin T transition(effort:{Effort T 1 1})} end}
         Res = {BuildChain S0 TransWithEffort 0 0}
      in
         FinalBlockchain = Res.1
         FinalState = Res.2
      end
   end
end