(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort Node 0)

(declare-fun lock_msg (Node) Bool)
(declare-fun unlock_msg (Node) Bool)
(declare-fun grant_msg (Node) Bool)
(declare-fun holds_lock (Node) Bool)
(declare-const held Bool)
(declare-fun lock_msg* (Node) Bool)
(declare-fun unlock_msg* (Node) Bool)
(declare-fun grant_msg* (Node) Bool)
(declare-fun holds_lock* (Node) Bool)
(declare-const held* Bool)

(declare-fun unchanged (Node) Bool)
(assert 
    (forall ((n Node))
        (= 
            (unchanged n)
            (and
                (= (lock_msg n) (lock_msg* n))
                (= (unlock_msg n) (unlock_msg* n))
                (= (grant_msg n) (grant_msg* n))
                (= (holds_lock n) (holds_lock* n))
            )
        )
    )
)

(assert
    (and
        ;disjunction of configs
        (or
            ;config1
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
            ;config2
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
            ;config3
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
            ;config4
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

        ;T
        (or
            ;lock
            (exists ((n Node))
                (and
                    (lock_msg* n)
                    (= held held*)
                    (forall ((n1 Node))
                        (=>
                            (not (= n n1))
                            (unchanged n1)
                        )
                    )
                )
            )

            ;unlock
            (exists ((n Node))
                (and
                    (holds_lock n)
                    (not (holds_lock* n))
                    (unlock_msg* n)
                    (= held held*)
                    (forall ((n1 Node))
                        (=>
                            (not (= n n1))
                            (unchanged n1)
                        )
                    )
                )
            )

            ;recv_lock
            (exists ((n Node))
                (and
                    (lock_msg n)
                    (not held)
                    held*
                    (not(lock_msg* n))
                    (grant_msg* n)
                    (forall ((n1 Node))
                        (=>
                            (not (= n n1))
                            (unchanged n1)
                        )
                    )
                )
            )

            ;recv_grant
            (exists ((n Node))
                (and
                    (grant_msg n)
                    (not (grant_msg* n))
                    (holds_lock* n)
                    (= held held*)
                    (forall ((n1 Node))
                        (=>
                            (not (= n n1))
                            (unchanged n1)
                        )
                    )
                )
            )

            ;recv_unlock
            (exists ((n Node))
                (and
                    (unlock_msg n)
                    (not held*)
                    (not (unlock_msg* n))
                    (forall ((n1 Node))
                        (=>
                            (not (= n n1))
                            (unchanged n1)
                        )
                    )
                )
            )
        )

        ;not R' as conjunction of invariants
        (not
            ;disjunction of configs
            (or
                ;config1
                (and
                    (forall ((N1 Node)) 
                        (not (grant_msg* N1))
                    )
                    (not held*)
                    (forall ((N1 Node)) 
                        (not (holds_lock* N1))
                    )
                    (forall ((N1 Node)) 
                        (not (unlock_msg* N1))
                    )
                )
                ;config2
                (and
                    held*
                    (forall ((N1 Node))
                        (not (holds_lock* N1))
                    )
                    (forall ((N1 Node))
                        (not (unlock_msg* N1))
                    )
                    (forall ((N1 Node))
                        (forall ((N2 Node))
                            (or
                                (= N1 N2) 
                                (not (grant_msg* N1))
                                (not (grant_msg* N2))
                            )
                        )
                    )
                    (exists ((N1 Node)) 
                        (grant_msg* N1)
                    )
                )
                ;config3
                (and
                    held*
                    (forall ((N1 Node))
                        (not (grant_msg* N1))
                    )
                    (forall ((N1 Node))
                        (not (unlock_msg* N1))
                    )
                    (forall ((N1 Node))
                        (forall ((N2 Node))
                            (or
                                (= N1 N2) 
                                (not (holds_lock* N1))
                                (not (holds_lock* N2))
                            )
                        )
                    )
                    (exists ((N1 Node)) 
                        (holds_lock* N1)
                    )
                )
                ;config4
                (and
                    held*
                    (forall ((N1 Node))
                        (not (grant_msg* N1))
                    )
                    (forall ((N1 Node))
                        (not (holds_lock* N1))
                    )
                    (forall ((N1 Node))
                        (forall ((N2 Node))
                            (or
                                (= N1 N2) 
                                (not (unlock_msg* N1))
                                (not (unlock_msg* N2))
                            )
                        )
                    )
                    (exists ((N1 Node)) 
                        (unlock_msg* N1)
                    )
                )
            )
        )
    )
)



(check-sat) 
(get-model)
