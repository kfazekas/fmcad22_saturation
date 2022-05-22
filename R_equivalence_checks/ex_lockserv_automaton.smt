(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort Node 0)

(declare-fun lock_msg (Node) Bool)
(declare-fun unlock_msg (Node) Bool)
(declare-fun grant_msg (Node) Bool)
(declare-fun holds_lock (Node) Bool)
(declare-const held Bool)

(assert
    (xor
        ;conjunction of invariants
        (and
            (forall ((N1 Node)) 
                (or
                    held
                    (not (grant_msg N1))
                )
            )
            (forall ((N1 Node)) 
                (or
                    held
                    (not (holds_lock N1))
                )
            )
            (forall ((N1 Node)) 
                (or
                    held
                    (not (unlock_msg N1))
                )
            )
            (forall ((N1 Node)) 
                (forall ((N2 Node)) 
                    (or
                        (= N1 N2)
                        (not (grant_msg N1))
                        (not (grant_msg N2))
                    )
                )
            )
            (forall ((N1 Node)) 
                (forall ((N2 Node)) 
                    (or
                        (not (grant_msg N2))
                        (not (holds_lock N1))
                    )
                )
            )
            (forall ((N1 Node)) 
                (forall ((N2 Node)) 
                    (or
                        (not (grant_msg N2))
                        (not (unlock_msg N1))
                    )
                )
            )
            (forall ((N1 Node)) 
                (forall ((N2 Node)) 
                    (or
                        (= N1 N2)
                        (not (holds_lock N1))
                        (not (holds_lock N2))
                    )
                )
            )
            (forall ((N1 Node)) 
                (forall ((N2 Node)) 
                    (or
                        (not (holds_lock N2))
                        (not (unlock_msg N1))
                    )
                )    
            )
            (forall ((N1 Node)) 
                (forall ((N2 Node))
                    (or
                        (= N1 N2)
                        (not (unlock_msg N1))
                        (not (unlock_msg N2))
                    ) 
                )
            )
            (exists ((N Node))
                (or
                    (grant_msg N)
                    (holds_lock N)
                    (unlock_msg N)
                    (not held)
                )
            )
        )

        ;disjunction of configs
        (or
            ;A
            (and
                (forall ((N1 Node)) 
                    (not (grant_msg N1))
                )
                (not held)
                (forall ((N1 Node)) 
                    (not (holds_lock N1))
                )
                (forall ((N1 Node)) 
                    (not (unlock_msg N1))
                )
            )
            ;B
            (and
                held
                (forall ((N1 Node))
                    (not (holds_lock N1))
                )
                (forall ((N1 Node))
                    (not (unlock_msg N1))
                )
                (forall ((N1 Node))
                    (forall ((N2 Node))
                        (or
                            (= N1 N2) 
                            (not (grant_msg N1))
                            (not (grant_msg N2))
                        )
                    )
                )
                (exists ((N1 Node)) 
                    (grant_msg N1)
                )
            )
            ;C
            (and
                held
                (forall ((N1 Node))
                    (not (grant_msg N1))
                )
                (forall ((N1 Node))
                    (not (unlock_msg N1))
                )
                (forall ((N1 Node))
                    (forall ((N2 Node))
                        (or
                            (= N1 N2) 
                            (not (holds_lock N1))
                            (not (holds_lock N2))
                        )
                    )
                )
                (exists ((N1 Node)) 
                    (holds_lock N1)
                )
            )
            ;D
            (and
                held
                (forall ((N1 Node))
                    (not (grant_msg N1))
                )
                (forall ((N1 Node))
                    (not (holds_lock N1))
                )
                (forall ((N1 Node))
                    (forall ((N2 Node))
                        (or
                            (= N1 N2) 
                            (not (unlock_msg N1))
                            (not (unlock_msg N2))
                        )
                    )
                )
                (exists ((N1 Node)) 
                    (unlock_msg N1)
                )
            )
        )
    )
)


(check-sat) 
(get-model)
