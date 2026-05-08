functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
    transitionHash:TransitionHash  
    blockHash:BlockHash
    somme_T_lst:Somme_T_lst
    puissance:Puissance
    effort:Effort
    balance_sender:Balance_sender
    nonce_sender:Nonce_sender
    valid_transaction:Valid_transaction
define
    %% STUDENT START:
    
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

   fun {Valid_transaction T State} % T est la transaction à vérifier et State est l'ensemble des users (senders et receivers). Renvoie 1 si elle est acceptée et 0 sinon
      if T.max_effort >= 0 andthen
         T.max_effort>=T.effort andthen
         T.value >= 0 andthen
         {Balance_sender T.sender State} >= T.value andthen
         T.hash == {TransactionHash T} andthen
         T.nonce == {Nonce_sender T.sender State} + 1 
      then 1 
      else 0 
      end
   
      
      fun {Valid_tout_transaction Transactions State} % Fonction qui valide toutes les transactions d'un bloc
    case Transactions of nil then 1
    [] H|T then
        if {Valid_transaction H State} == 1 then
            {AllValidTransactions T State}
        else 0
        end
    end
end


   fun {GetBlock Blockchain K} % Fonction pour avoir le bloc de Blockchain à l'indice K 
    case Blockchain of nil then nil
    [] H|T then
        if K == 0 then H
        else {GetBlock T K-1}
        end
    end
   end

   fun {Valid_Bloc Blockchain BlocInd State} % Blockp = block présent, Blocka = block avant
    Blockp = {GetBlock Blockchain BlocInd}

    if BlocInd == 0 then
        if Blockp.hash == {BlockHash Blockp} andthen
           {AllValidTransactions Blockp.list_of_transactions State} == 1 andthen
           {SumEfforts Blockp.list_of_transactions} =< 300
        then 1 else 0 end
    else
         Blocka = {GetBlock Blockchain BlocInd-1} 
         if Blockp.number == Blocka.number + 1 andthen
            Blockp.previousHash == {BlockHash Blocka} andthen
            Blockp.hash == {BlockHash Blockp} andthen
            {AllValidTransactions Blockp.list_of_transactions State} == 1 andthen
            {SumEfforts Blockp.list_of_transactions} =< 300
         then 1 else 0 end
        end
    end
end
    
    %% PUT ANY AUXILIARY/HELPER FUNCTIONS THAT YOU NEED

    %% STUDENT END

    %% Return a string representation of the secret
    fun {Decode Blockchain}
        1
        %% STUDENT START:
        %% TODO
        %% STUDENT END
    end


    % This function is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        1
        %% STUDENT START:
        %% TODO
        %% STUDENT END
    end
end