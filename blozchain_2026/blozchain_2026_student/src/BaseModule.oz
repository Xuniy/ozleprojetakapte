functor
import
   System
   Application
export
   decode:Decode
   executeBlockchain:ExecuteBlockchain
define

   fun {Puissance X N} %Calcule X^N car Oz ne le fait pas
      if N == 0 then 1 else X * {Puissance X N-1} end
   end

   fun {TransactionHash T} %Calcule le hash d'une transaction
      (T.nonce + T.sender + T.receiver + T.value) mod {Puissance 10 6}
   end

   fun {Somme_T_lst Liste} %Calcule la somme des hashs des transactions d'une liste pour {BlockHash B}
      case Liste of nil then 0
      [] H|T then {TransactionHash H} + {Somme_T_lst T}
      end
   end

   fun {BlockHash B} %Calcule le hash d'un block
      (B.number + B.previousHash + {Somme_T_lst B.transactions}) mod {Puissance 10 6}
   end

   fun {Effort T N Acc} %Calcule l'effort d'une transaction
      if T.value >= 10 then
         {Effort transition(value: T.value div 10) N+1 Acc+{Puissance 2 N}}
      else Acc end
   end

   fun {AdaptGenesis GenesisState} %Adapte le génésis pour qu'il aie le même format que le state qu'on doit garder à jour
      {Record.mapInd GenesisState %Record.mapInd sert à modifier l'ancien génésis en gardant la balance et en rajoutant le nonce
       fun {$ _ Balance} user(balance:Balance nonce:0) end}
   end

   fun {Valid_transaction T State}%Vérifie qu'une transaction respecte bien les consignes
      local 
         %Utilise CondSelect pour gérer les nouveaux utilisateurs (solde montant reçu). Le système ne crashera pas grâce à ça car il créera un nouvel utilisateur si T.sender n'existe pas encore
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

   fun {NewState State T} %Adapte l'état avec une transaction validée
      local
         Sender = T.sender 
         Receiver = T.receiver 
         Value = T.value
         OldSender = {CondSelect State Sender user(balance:0 nonce:0)}
         OldReceiver = {CondSelect State Receiver user(balance:0 nonce:0)}
         
         NewSender = user(balance: OldSender.balance - Value nonce: OldSender.nonce + 1) %Enlève la valeur de la transaction au solde du sender et incrémente son nonce
         
         NewReceiver = user(balance: OldReceiver.balance + Value nonce: OldReceiver.nonce)%Rajoute la valeur de la transaction au solde du receiver
      in
         {AdjoinAt {AdjoinAt State Sender NewSender} Receiver NewReceiver}%Modifie l'ancien sender et l'ancien receiver dans state avec les nouvelles valeurs
      end
   end

   fun {UpdateStateWithList State Lst} %Adapte l'état à chaque transaction d'une liste
      case Lst of nil then State
      [] H|T then {UpdateStateWithList {NewState State H} T}
      end
   end

   fun {CheckBlockTransactions Trans State Num AccEffort}
      case Trans of nil then nil
      [] T|Reste then
         local 
            E = {Effort T 1 1} in
            if {Valid_transaction T State} andthen 
               T.block_number == Num andthen (AccEffort + E) =< 300 %Si la transaction est valide, que le numéro du block correspond et que l'effort total ne dépasse pas 300, on ajoute la transaction à la liste
            then
               T | {CheckBlockTransactions Reste {NewState State T} Num AccEffort + E}
            else {CheckBlockTransactions Reste State Num AccEffort} end %Sinon, on passe à la transaction suivante
         end
      end
   end

   fun {CreateBlock Transactions State Num PrevHash} %Crée un block avec les transactions valides pour ce block
      local
         ValidT = {CheckBlockTransactions Transactions State Num 0}
         B = block(number: Num previousHash: PrevHash transactions: ValidT) %Crée le record
      in
         {Adjoin B block(hash: {BlockHash B})} %Rajoute le hash du block au record
      end
   end

   fun {CreateBlockChain State Transactions Num PrevHash}%Crée une blockchain depuis l'état génésis modifié avec toutes les transactions. On fait le 1er appel avec PrevHash=0 comme dit dans les consignes et Num=0 pour le premier block 
      local B = {CreateBlock Transactions State Num PrevHash} in
         if B.transactions == nil then nil # State %On fait un tuple pour retourner la blockchain et le state
         else
            local
               NextS = {UpdateStateWithList State B.transactions} %On adapte l'état avec les transactions du block
               Rec = {CreateBlockChain NextS Transactions Num+1 B.hash} %On crée le prochain block avec le nouvel état, le numéro +1 et le PrevHash valant le Hash du block précédent
            in (B | Rec.1) # Rec.2 end %On retourne la blockchain et le state final sous forme de tuple
         end
      end
   end

   Tableau_Sharelock=tableau(10:&a 11:&b 12:&c 13:&d 14:&e 15:&f 16:&g 17:&h 18:&i 19:&j 20:&k 21:&l 22:&m 23:&n 24:&o 25:&p 26:&q 27:&r 28:&s 29:&t 30:&u 31:&v 32:&w 33:&x 34:&y 35:&z 36:& )
   %Tableau qui permet de déchiffrer les hashs des blocks selon le code de Sharelock
   fun {Decrypt Number}
      local N = (Number mod 37) in %mod 37 car demandé comme ça
         if N < 10 then Tableau_Sharelock.36 %% Renvoie ' ' (espace)
         else Tableau_Sharelock.N %On prend la valeur correspondante dans le tableau 
         end
      end
   end

   fun {TransformToList N}%Transforme un hash en une liste de chiffre pour aider au déchiffrage
      {Map {IntToString N} fun {$ Char} Char - 48 end} %On fait -48 pour passer du code ASCII de {IntToString} à la valeur numérique correspondante
   end

   fun {Phrase_Liste Liste}
      case Liste of nil then nil
      []H|H2|T then {Decrypt (10*H+H2)}|{Phrase_Liste T}%On prend les 2 premiers de la liste pour les déchiffrer et on continue avec le reste de la liste 
      []H|nil then nil %Si y'a qu'un seul chiffre, on ne le déchiffre pas 
      end
   end

   fun {Phrase Hash} %Transforme un Hash en Liste puis print la liste traduite selon le tableau de Sharelock
      local Actual in
         Actual={TransformToList Hash} %Transforme le hash en liste
         {Phrase_Liste Actual}% Renvoie la liste traduite
      end
   end

   
   fun {Decode BlockChain}
   % Flatten transforme la liste de listes en une simple liste de caractères (String)
      {Flatten 
      case BlockChain of nil then nil
      [] B|R then {Phrase B.hash} | {Decode R} %On traduit le hash du block et on continue la blockchain
      end}
   end


   proc {ExecuteBlockchain Genesis Transactions FinalState FinalBlockchain}
      local
         StartState = {AdaptGenesis Genesis}%On prépare le génésis pour qu'il contienne les nonce
         TransWithEffort = {Map Transactions fun {$ T} {Adjoin T transition(effort:{Effort T 1 1})} end} %On ajoute l'effort calculé à chaque transaction
         Res = {CreateBlockChain StartState TransWithEffort 0 0}%On crée la blockchain avec l'état de départ, la liste des transactions avec effort,
            %le 1er block à 0 et le PrevHash à 0 pour le 1er block 
      in
         FinalBlockchain = Res.1 %On prend l'élément 1 du tuple qui est la blockchain
         FinalState = Res.2 %On prend l'élément 2 du tuple qui est le state final
      end
   end
end