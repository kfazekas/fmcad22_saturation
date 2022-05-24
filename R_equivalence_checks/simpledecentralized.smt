(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort Node 0)

(declare-fun has_lock (Node) Bool)
(declare-fun message (Node Node) Bool)
(declare-fun start_node (Node) Bool)

(assert
    (xor
        ;constraints
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

        ;configs
        (or
            ;config1
            (and
                (forall ((n1 Node) (n2 Node))
                    (not (message n2 n1))
                )
                (forall ((n Node))
                    (or
                        (not (start_node n))
                        (has_lock n)
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (has_lock n1))
                        (not (has_lock n2))
                    )
                )
                (exists ((n Node))
                    (start_node n)
                )
            )

            ;config2
            (and
                ;no one has lock
                (forall ((n Node))
                    (not (has_lock n))
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                         (= n1 n2)
                         (not (message n2 n1))
                    )
                )
                (forall ((n Node))
                    (or
                        (message n n)
                        (not (start_node n))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (message n1 n1))
                        (not (message n2 n2))
                    )
                )
                (exists ((n Node))
                    (start_node n)
                )
                
            )

            ;config3
            (and
                ;no one has lock
                (forall ((n Node))
                    (not (has_lock n))
                )
                ;no self messages
                (forall ((n Node))
                    (not (message n n))
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (start_node n2)
                        (not (message n2 n1))
                    )
                )  
                (forall ((n1 Node) (n2 Node) (n3 Node))
                    (or
                        (= n1 n2)
                        (= n1 n3)
                        (= n2 n3)
                        (not (message n3 n1))
                        (not (message n3 n2))
                    )

                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (start_node n1))
                        (not (start_node n2))
                    )
                )
                (exists ((n1 Node) (n2 Node))
                    (and
                        (not (= n1 n2))
                        (message n1 n2)
                    )
                )
            )

            ;config4
            (and
                (forall ((n1 Node) (n2 Node))
                    (not (message n2 n1))
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (has_lock n1))
                        (not (has_lock n2))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (start_node n1))
                        (not (start_node n2))
                    )
                )
                (forall ((n1 Node))
                    (exists ((n2 Node))
                        (and
                            (not (= n1 n2))
                            (or
                                (has_lock n2)
                                (start_node n2)
                            )
                        )
                    )
                )
            )

            ;config5
            (and
                (forall ((n1 Node))
                    (not (has_lock n1))
                )
                (forall ((n1 Node))
                    (not (message n1 n1))
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (start_node n2)
                        (not (message n1 n2))
                    )
                )
                (forall ((n1 Node) (n2 Node) (n3 Node))
                    (or
                        (= n1 n2)
                        (= n1 n3)
                        (= n2 n3)
                        (not (message n2 n1))
                        (not (message n3 n1))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (start_node n1))
                        (not (start_node n2))
                    )
                )
                (exists ((n1 Node) (n2 Node))
                    (and
                        (not (= n1 n2))
                        (message n1 n2)
                    )
                )
            )

            ;config6
            (and
                (forall ((n1 Node))
                    (not (has_lock n1))
                ) 
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (message n2 n1))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (message n1 n1))
                        (not (message n2 n2))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (start_node n1))
                        (not (start_node n2))
                    )
                )
                (forall ((n1 Node))
                    (exists ((n2 Node))
                        (and
                            (not (= n1 n2))
                            (or
                                (message n2 n2)
                                (start_node n2)
                            )
                        )
                    )
                )
            )

            ;config7
            (and
                (forall ((n Node))
                    (not (has_lock n))
                )
                (forall ((n1 Node))
                    (not (message n1 n1))
                )
                (forall ((s1 Node) (s2 Node) (d1 Node) (d2 Node))
                    (or
                        (and
                            (= s1 s2)
                            (= d1 d2)
                        )
                        (= s1 d1)
                        (= s2 d2)
                        (not (message s1 d1))
                        (not (message s2 d2))
                    )
                )
                (forall ((n1 Node) (n2 Node))
                    (or
                        (= n1 n2)
                        (not (start_node n1))
                        (not (start_node n2))
                    )
                )
                (forall ((n Node))
                    (exists ((s Node) (d Node))
                        (or
                            (and
                                (not (= n s))
                                (not (= n d))
                                (not (= s d))
                                (message s d)
                            )
                            (and
                                (not (= n s))
                                (start_node s)
                            )
                        )
                    )
                )
            )
        )
    )
)



(check-sat) 
(get-model)
