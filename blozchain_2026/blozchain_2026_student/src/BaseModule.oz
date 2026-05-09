functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
    transitionHash:TransactionHash
    blockHash:BlockHash
    somme_T_lst:Somme_T_lst
    puissance:Puissance
    effort:Effort
    balance_sender:Balance_sender
    nonce_sender:Nonce_sender
    valid_transaction:Valid_transaction
    newState:NewState
    decrypt:Decrypt
    phrase:Phrase
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

   fun {Somme_tout_effort Transactions} % Somme les efforts (T.effort) de toutes les transactions d'un bloc
      case Transactions of nil then 0
      [] H|T then H.effort + {Somme_tout_effort T}
      end
   end

   fun {BlockHash Block} % Calcule le Hash d'un bloc
      (Block.number + Block.previousHash+{Somme_T_lst Block.list_of_transactions}) mod {Puissance 10 6}
   end

   fun {Effort Transaction N Acc} % L'appeler en mettant {Effort Transaction 1 1}
      % Bug-fix : >=10 (et non >10) sinon value=10/100/1000 retourne un effort
      % trop petit (value=10 a 2 chiffres -> doit donner 1+2=3, pas 1).
      if (Transaction.value >= 10) then
         local NewTrans = transition(nonce: Transaction.nonce
                                  sender: Transaction.sender
                                  receiver: Transaction.receiver
                                  value: (Transaction.value div 10))
         NewAcc = Acc + {Puissance 2 N}
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
   end

   fun {Valid_tout_transaction Transactions State} % Fonction qui valide toutes les transactions d'un bloc
    case Transactions of nil then 1
    [] H|T then
        if {Valid_transaction H State} == 1 then
            {Valid_tout_transaction T State}
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

   fun {NewState State Transaction}
      % Met à jour l'état après une transaction VALIDE (à n'appeler qu'après Valid_transaction == 1).
      % Si le receiver n'existe pas encore -> il est créé avec balance = value reçu et nonce = 0.
      local
         Sender = Transaction.sender
         Receiver = Transaction.receiver
         Value = Transaction.value
         AncienSender = State.Sender
         AncienReceiver = {CondSelect State Receiver user(balance:0 nonce:0)}
         NewSender = user(balance: AncienSender.balance - Value
                          nonce:   AncienSender.nonce + 1)
         NewReceiver = user(balance: AncienReceiver.balance + Value
                            nonce:   AncienReceiver.nonce)
         StateApresSender = {AdjoinAt State Sender NewSender}
      in
         {AdjoinAt StateApresSender Receiver NewReceiver}
      end
   end

   fun {GenesisToState Genesis}
      % genesis(1:100 2:50) -> state(1:user(balance:100 nonce:0) 2:user(balance:50 nonce:0))
      fun {ToPairs Fs}
         case Fs of nil then nil
         [] F|T then F#user(balance:Genesis.F nonce:0) | {ToPairs T}
         end
      end
   in
      {List.toRecord state {ToPairs {Arity Genesis}}}
   end

fun {Valid_Bloc Blockchain BlocInd State}
   local Blockp = {GetBlock Blockchain BlocInd}
   in 
      if BlocInd == 0 then
         if Blockp.hash == {BlockHash Blockp} andthen
            {Valid_tout_transaction Blockp.list_of_transactions State} == 1 andthen
            {Somme_tout_effort Blockp.list_of_transactions} =< 300
      then 1 else 0 end
      else
         local Blocka = {GetBlock Blockchain BlocInd-1}
         in
            if Blockp.number == Blocka.number + 1 andthen
               Blockp.previousHash == {BlockHash Blocka} andthen
               Blockp.hash == {BlockHash Blockp} andthen
               {Valid_tout_transaction Blockp.list_of_transactions State} == 1 andthen
               {Somme_tout_effort Blockp.list_of_transactions} =< 300
         then 1 else 0 end
end
end
end
end






    Tableau_Sharelock = tableau(10:&a 11:&b 12:&c 13:&d 14:&e 15:&f 16:&g 17:&h
                                18:&i 19:&j 20:&k 21:&l 22:&m 23:&n 24:&o 25:&p
                                26:&q 27:&r 28:&s 29:&t 30:&u 31:&v 32:&w 33:&x
                                34:&y 35:&z 36:& )

    fun {Decrypt Number} 
       Mod = Number mod 37
    in
       if Mod < 10 then & 
       else Tableau_Sharelock.Mod
       end
    end

    fun {TransformToList N} % 284110 -> [2 8 4 1 1 0]
       {List.map {IntToString N} fun {$ Char} Char - &0 end}
    end

    fun {Phrase_Liste Liste} % Liste de chiffres -> liste de codes de caractères, par paires
       case Liste of nil then nil
       [] H|H2|T then {Decrypt 10*H+H2}|{Phrase_Liste T}
       [] _|nil then nil  % chiffre orphelin (longueur impaire) ignoré
       end
    end

    fun {Phrase Hash} % Hash d'un bloc -> liste de codes de caractères
       {Phrase_Liste {TransformToList Hash}}
    end

    %% PUT ANY AUXILIARY/HELPER FUNCTIONS THAT YOU NEED

    %% STUDENT END

    %% Return a string representation of the secret
    fun {Decode Blockchain}
        %% STUDENT START:
        case Blockchain of nil then nil
        [] H|T then {List.append {Phrase H.hash} {Decode T}}
        end
        %% STUDENT END
    end


    % This function is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        %% STUDENT START:
        %% Traite toutes les transactions d'un même bloc (block_number == BlockNum).
        %% Filtre les transactions invalides et celles qui feraient dépasser 300 d'effort.
        %% Retourne un record res(state:... accepted:... rest:...).
        fun {ProcessBlock Txs BlockNum State AcceptedRev EffortSum}
           case Txs of nil then
              res(state:State accepted:{List.reverse AcceptedRev} rest:nil)
           [] H|T then
              if H.block_number \= BlockNum then
                 res(state:State accepted:{List.reverse AcceptedRev} rest:Txs)
              else
                 local
                    TxAvecEffort = {AdjoinAt H effort {Effort H 1 1}}
                    TxEff = TxAvecEffort.effort
                 in
                    if EffortSum + TxEff > 300 then
                       %% Dépasserait l'effort max -> on saute, on continue le bloc
                       {ProcessBlock T BlockNum State AcceptedRev EffortSum}
                    elseif {Valid_transaction TxAvecEffort State} == 1 then
                       {ProcessBlock T BlockNum
                          {NewState State TxAvecEffort}
                          TxAvecEffort|AcceptedRev
                          EffortSum + TxEff}
                    else
                       %% Invalide -> on saute
                       {ProcessBlock T BlockNum State AcceptedRev EffortSum}
                    end
                 end
              end
           end
        end

        %% Construit récursivement la blockchain. PrevHash = 0 pour le 1er bloc.
        fun {BuildBlocks Txs State PrevHash}
           case Txs of nil then res(state:State chain:nil)
           [] H|_ then
              local
                 BlockNum = H.block_number
                 PR = {ProcessBlock Txs BlockNum State nil 0}
                 BlocSansHash = block(number: BlockNum
                                       previousHash: PrevHash
                                       list_of_transactions: PR.accepted)
                 HashBloc = {BlockHash BlocSansHash}
                 BlocComplet = {AdjoinAt BlocSansHash hash HashBloc}
                 RR = {BuildBlocks PR.rest PR.state HashBloc}
              in
                 res(state: RR.state chain: BlocComplet|RR.chain)
              end
           end
        end

        Result
    in
        Result = {BuildBlocks Transactions {GenesisToState GenesisState} 0}
        FinalState = Result.state
        FinalBlockchain = Result.chain
        %% STUDENT END
    end
end