local
   %% 1. Copiez vos fonctions ici
   %J'ai fait les trucs jusque 2.1.4 et aussi 2.2
   fun {Puissance X N} % Marche comme l'exposant car y'a pas en Oz. {Puissance 2 3} = 2 au cube=8
      if N == 0 then 1
      else X * {Puissance X N-1}
      end
   end

   fun {TransactionHash Transition} % Calcule le Hash d'une transaction
      (Transition.nonce + Transition.sender + Transition.receiver + Transition.value) mod {Puissance 10 6}
   end

   
   fun{Somme_T_lst Liste} % Calcule la somme des Hash des transactions dans un bloc. Je dois encore l'adapter au bloc mais elle marche pour une liste
      case Liste of nil then 0
      []H|T then {TransactionHash H}+{Somme_T_lst T} 
      end
   end 
   
   fun {BlockHash Block} % Calcule le Hash d'un bloc
      (Block.number + Block.previousHash+{Somme_T_lst Block.list_of_transactions}) mod {Puissance 10 6}
   end

   fun {Effort Transaction N Acc} % L'appeler en mettant {Effort Transaction 1 1}
      if (Transaction.value>10) then
         local NewTrans = transition(nonce: Transaction.nonce 
                                  sender: Transaction.sender 
                                  receiver: Transaction.receiver 
                                  value: (Transaction.value div 10)) 
         NewAcc =Acc+{Puissance 2 N}
      in
         {Effort NewTrans N+1 NewAcc}
      end
      else 
         Acc
      end
   end

   fun {Balance_sender Id State} % Donne la balance du sender
      State.Id.balance
   end

   fun {Nonce_sender Id State} % Donne le nonce du sender 
      State.Id.nonce
   end

   fun {Valid_transaction T State} % T est la transaction à vérifier et State est l'ensemble des users (senders et receivers)
      if T.max_effort >= 0 andthen
         T.max_effort>=T.effort andthen
         T.value >= 0 andthen
         {Balance_sender T.sender State} >= T.value andthen
         T.hash == {TransactionHash T} andthen
         T.nonce == {Nonce_sender T.sender State} + 1 
      then 1 
      else 0 
      end
   end

   fun {NewState State Transaction}
      local Sender Receiver Value AncienSender AncienReceiver NewUser1 NewUser2 NewState FinalState
         Sender=Transaction.sender
         Receiver=Transaction.receiver
         Value=Transaction.value

         AncienSender=State.Sender
         AncienReceiver={CondSelect State Receiver user(balance:0 nonce:0)}

         NewUser1=user(balance:AncienSender.balance-Value nonce:AncienSender.nonce+1)
         NewUser2=user(balance:AncienReceiver.balance+Value nonce:AncienReceiver.nonce)
      in
         NewState = {Adjoin State state(Sender:NewUser1)}
         FinalState= {Adjoin NewState state(Receiver:NewUser2)}
         FinalState
         end
   end
   Tableau_Sharelock=tableau(10:a 11:b 12:c 13:d 14:e 15:f 16:g 17:h 18:i 19:j 20:k 21:l 22:m 23:n 24:o 25:p 26:q 27:r 28:s 29:t 30:u 31:v 32:w 33:x 34:y 35:z 36:' ')

   fun {Decrypt Number}
      if (Number mod 37)<10 then ' '
      else Tableau_Sharelock.(Number mod 37)
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

   
   %% 2. Définissez vos données de test (Variables avec Majuscule !)
   Trans = transition(nonce:2 block_number:0 hash:1403 sender:0 receiver:1 value:1400 effort:15 max_effort:30000)
   Trans2 = transition(nonce:1 sender:1 receiver:2 value:10)

   MonBloc = block(number:2 previousHash:5 list_of_transactions:[Trans Trans2])

   State = state(0 : user(balance:12000 nonce:1)
            1 : user(balance:1000 nonce:1))
in
   
   {Browse {Valid_transaction Trans State}}
   %{Browse {Decrypt 9}}
   %{Browse {Phrase 291428661}} %Test pour traduire un Hash en Liste qui donne la réponse de Sharelock
   %{Browse {TransformToList 101010}}
   %{Browse {NewState State Trans}}
end