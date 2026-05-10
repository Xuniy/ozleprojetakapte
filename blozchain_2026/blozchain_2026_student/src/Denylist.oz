functor
export
   decode:Decode
   executeBlockchain:ExecuteBlockchain
define
    %La plupart des commentaires de ce fichier sont similaires à ceux de BaseModule.oz. Les différences ont été commentées
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
      if T.value >= 10 then
         {Effort transition(value: T.value div 10) N+1 Acc+{Puissance 2 N}}
      else Acc end
   end

   fun {Contains Sender List} %Vérifie si le sender est déjà dans la denylist
      case List of nil then false
      [] H|T then
         if H == Sender then true else {Contains Sender T} end
      end
   end

   fun {AddToDenylist Sender Denylist} %Rajoute le sender à la denylist s'il n'y est pas encore
        if {Contains Sender Denylist} then Denylist else Sender|Denylist end
   end

    fun {RegisterSender Sender Counts Denylist}
        local
            OldCount = {CondSelect Counts Sender 0} %Le compte est à 0 si le sender n'a pas encore fait de transaction dans ce bloc
            NewCount = OldCount + 1 %On incrémente de 1
            NewCounts = {AdjoinAt Counts Sender NewCount} %Modifie le compte de transactions du sender pour un bloc
            NewDenylist = if NewCount >= 3 then {AddToDenylist Sender Denylist} else Denylist end %S'il y a 3 transactions ou plus sur le même bloc, on rajoute le sender à la denylist
        in
            NewCounts#NewDenylist %On renvoie un tuple avec les comptes des utilisateurs et la denylist actualisée
        end
    end

   fun {AdaptGenesis GenesisState}
      {Record.mapInd GenesisState
       fun {$ _ Balance} user(balance:Balance nonce:0) end} %On met _ pour dire qu'on a pas besoin de cette info de l'ancien génésis
   end

   fun {Valid_transaction T State}
      local
         Sender = {CondSelect State T.sender user(balance:0 nonce:0)}
      in
         if T.max_effort >= 0 andthen
            T.max_effort >= {Effort T 1 1} andthen
            T.value >= 0 andthen
            Sender.balance >= T.value andthen
            T.hash \= 0 andthen
            T.hash == {TransactionHash T} andthen
            T.nonce == Sender.nonce + 1
         then true else false end
      end
   end

   fun {NewState State T}
      local
         Sender = T.sender 
         Receiver = T.receiver 
         Value = T.value
         OldSender = {CondSelect State Sender user(balance:0 nonce:0)}
         OldReceiver = {CondSelect State Receiver user(balance:0 nonce:0)}
         NewSender = user(balance: OldSender.balance - Value nonce: OldSender.nonce + 1)
         NewReceiver = user(balance: OldReceiver.balance + Value nonce: OldReceiver.nonce)
      in
         {AdjoinAt {AdjoinAt State Sender NewSender} Receiver NewReceiver}
      end
   end

   fun {CheckBlockTransactions Trans State Num AccEffort Denylist Counts}
      case Trans of nil then nil#Denylist %Lorsqu'on a finit la liste, on renvoie celle-ci ainsi que la Denylist dans un tuple
      [] T|Reste then
         if T.block_number == Num then
            if {Contains T.sender Denylist} then %Si le sender est dans la denylist, on saute cette transaction et on continue avec le reste
               {CheckBlockTransactions Reste State Num AccEffort Denylist Counts}
            else
               local
                  Eff = {Effort T 1 1}
                  IsValid = {Valid_transaction T State} andthen (AccEffort + Eff) =< 300 %On vérifie que la transaction est valide et que l'effort total ne dépasse pas 300
                  NextState = if IsValid then {NewState State T} else State end %On ne change l'état que si la transaction est valide
                  NextEffort =if IsValid then AccEffort + Eff else AccEffort end %Pareil pour l'effort total
                  Updated = {RegisterSender T.sender Counts Denylist}
                  Rec ={CheckBlockTransactions Reste NextState Num NextEffort Updated.2 Updated.1} %On rappelle la fonction avec les valeurs actualisées
               in
                  if IsValid then (T|Rec.1)#Rec.2 else Rec end %Si la transaction est valide, on l'ajoute à la liste des transactions du block
               end
            end
         else
            {CheckBlockTransactions Reste State Num AccEffort Denylist Counts}
         end
      end
   end

   fun {CreateBlock Transactions State Num PrevHash Denylist}
      local
         Checked = {CheckBlockTransactions Transactions State Num 0 Denylist counts} %On mets counts sans majuscule car il doit être à 0 pour le premier appel 
         ValidT = Checked.1
         NewDenylist = Checked.2
         Block = block(number: Num previousHash: PrevHash transactions: ValidT)
      in
         {Adjoin Block block(hash: {BlockHash Block})}#NewDenylist %On rajoute le hash du block au record et on ajoute la denylist au tuple
      end
   end

   fun {UpdateStateWithList State Lst}
      case Lst of nil then State
      [] H|T then {UpdateStateWithList {NewState State H} T}
      end
   end

   fun {CreateBlockChain State Trans Num PrevHash Denylist}
      local Created = {CreateBlock Trans State Num PrevHash Denylist}
         Block = Created.1
         NextDenylist = Created.2
      in
         if Block.transactions == nil then nil#State %Si le bloc n'a pas de transactions, la blockchain est finie donc on la retourne avec l'état final dans un tuple
         else
            local
               NextState = {UpdateStateWithList State Block.transactions}
               Rec = {CreateBlockChain NextState Trans Num+1 Block.hash NextDenylist}
            in
               (Block | Rec.1)#Rec.2 %On rajoute le bloc à la blockchain et on retourne la blockchain avec l'état final dans un tuple
            end
         end
      end
   end

   Tableau_Sharelock=tableau(10:&a 11:&b 12:&c 13:&d 14:&e 15:&f 16:&g 17:&h 18:&i 19:&j 20:&k 21:&l 22:&m 23:&n 24:&o 25:&p 26:&q 27:&r 28:&s 29:&t 30:&u 31:&v 32:&w 33:&x 34:&y 35:&z 36:& )
   
   fun {Decrypt Number}
      local N = (Number mod 37) in
         if N < 10 then Tableau_Sharelock.36
         else Tableau_Sharelock.N
         end
      end
   end

   fun {TransformToList N}
      {Map {IntToString N} fun {$ Char} Char - 48 end}
   end

   fun {Phrase_Liste Liste}
      case Liste of nil then nil
      [] H|H2|T then {Decrypt (10*H+H2)}|{Phrase_Liste T}
      [] H|nil then nil
      end
   end

   fun {Phrase Hash}
      {Phrase_Liste {TransformToList Hash}}
   end

   fun {Decode BlockChain}
      {Flatten
       case BlockChain of nil then nil
       [] B|R then {Phrase B.hash} | {Decode R}
       end}
   end

   proc {ExecuteBlockchain Genesis Transactions FinalState FinalBlockchain}
      local
         StartState = {AdaptGenesis Genesis}
         TransWithEffort = {Map Transactions fun {$ T} {Adjoin T transition(effort:{Effort T 1 1})} end}
         Res = {CreateBlockChain StartState TransWithEffort 0 0 nil}
      in
         FinalBlockchain = Res.1
         FinalState = Res.2
      end
   end
end
