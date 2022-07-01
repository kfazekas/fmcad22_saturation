(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort Node 0)

(declare-fun has_lock (Node) Bool)
(declare-fun message (Node Node) Bool)
(declare-fun start_node (Node) Bool)
(declare-fun has_lock* (Node) Bool)
(declare-fun message* (Node Node) Bool)
(declare-fun unchanged (Node Node) Bool)
(assert 
    (forall ((s Node) (d Node))
        (= 
            (unchanged s d)
            (and
                (= (has_lock d) (has_lock* d))
                (= (has_lock s) (has_lock* s))
                (= (message s d) (message* s d))
            )
        )
    )
)

(assert
    (and
        ;R as conjunction of constraints
        (and
            (forall ((n1 Node) (n2 Node))
                (or
                    (not (has_lock n1))
                    (not (has_lock n2))
                    (= n1 n2)
                )
            )
            (forall ((n Node) (s Node) (d Node))
                (or
                    (not (has_lock n))
                    (not(message s d))
                )
            )
            (forall ((s1 Node) (d1 Node) (s2 Node) (d2 Node))
                (or
                    (not (message s1 d1))
                    (not (message s2 d2))
                    (and (= s1 s2) (= d1 d2))
                )
            )
            (forall ((n1 Node) (n2 Node))
                (or
                    (not (start_node n1))
                    (not (start_node n2))
                    (= n1 n2)
                )
            )  
            (exists ((n Node))
                (start_node n)
            )
            (exists ((n Node) (s Node) (d Node))
                (or 
                    (has_lock n)
                    (message s d)
                )
            )
        )

        ;T
        (or
            ;send
            (exists ((s Node) (d Node))
                (and
                    (has_lock s)
                    (message* s d)
                    (not (has_lock* s))
                    (forall ((s1 Node) (d1 Node))
                        (=>
                            (not
                                (and 
                                    (= s1 s)
                                    (= d1 d)
                                )
                            )
                            (unchanged s1 d1)
                        )
                    )
                )
            )

            ;recv
            (exists ((s Node) (d Node))
                (and
                    (has_lock* d)
                    (message s d)
                    (not (message* s d))
                    (not (has_lock d))
                    (forall ((s1 Node) (d1 Node))
                        (=>
                            (not
                                (and 
                                    (= s1 s)
                                    (= d1 d)
                                )
                            )
                            (unchanged s1 d1)
                        )
                    )
                )
            )
        )

        ;not R'
        (not
            (and
                (forall ((n1 Node) (n2 Node))
                    (or
                        (not (has_lock* n1))
                        (not (has_lock* n2))
                        (= n1 n2)
                    )
                )
                (forall ((n Node) (s Node) (d Node))
                    (or
                        (not (has_lock* n))
                        (not(message* s d))
                    )
                )
                (forall ((s1 Node) (d1 Node) (s2 Node) (d2 Node))
                    (or
                        (not (message* s1 d1))
                        (not (message* s2 d2))
                        (and (= s1 s2) (= d1 d2))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (not (start_node n1))
                        (not (start_node n2))
                        (= n1 n2)
                    )
                )  
                (exists ((n Node))
                    (start_node n)
                )
                (exists ((n Node) (s Node) (d Node))
                    (or 
                        (has_lock* n)
                        (message* s d)
                    )
                )
            )
        )
    )
)



(check-sat) 
(get-model)
