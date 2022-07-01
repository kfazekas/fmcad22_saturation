(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort Client 0)
(declare-sort Server 0)

(declare-fun link (Client Server) Bool)
(declare-fun link* (Client Server) Bool)
(declare-fun semaphore (Server) Bool)
(declare-fun semaphore* (Server) Bool)

(declare-fun unchanged (Client Server) Bool)
(assert 
    (forall ((c Client) (s Server))
        (= 
            (unchanged c s)
            (and
                (= (semaphore s) (semaphore* s))
                (= (link c s) (link* c s))
            )
        )
    )
)

            
(assert
    (and 
        ;disjunction of configs
        (or
            ;config1
            ;all locked
            (and
                (forall ((s Server))
                    (semaphore s)
                )
                (forall ((c Client) (s Server)) 
                    (not(link c s))
                )
            )

            ;config2
            ;at least one locked, at least one linked
            (and
                (exists ((c Client) (s Server))
                    (link c s)
                )
                (exists ((s Server))
                    (semaphore s)
                )
                (forall ((s Server))
                    (exists ((c Client))
                        (or
                            (semaphore s)
                            (link c s)
                        )
                    )
                )
                (forall ((s Server) (c Client))
                    (or
                        (not (semaphore s))
                        (not(link c s))
                    )
                )
                (forall ((s Server) (c1 Client) (c2 Client))
                    (or
                        (not (link c1 s))
                        (not (link c2 s))
                        (= c1 c2)
                    )
                )
            )

            ;config3
            ;all linked
            (and 
                (forall ((s Server)) (exists ((c Client))
                    (link c s))
                )
                (forall ((s Server) (c1 Client) (c2 Client))
                    (or
                        (not (link c1 s))
                        (not (link c2 s))
                        (= c1 c2)
                    )
                )
                (forall ((s Server))
                    (not(semaphore s))
                )
            )
        )

        ;T
        (or
            ;connect
            (exists ((c Client) (s Server))
                (and
                    (semaphore s)
                    (link* c s)
                    (not(semaphore* s))
                    (forall ((c1 Client) (s1 Server))
                        (=>
                            (not
                                (and
                                    (= c c1)
                                    (= s s1)
                                )
                            )
                            (unchanged c1 s1)
                        )
                    )
                )
            )

            ;disconnect
            (exists ((c Client) (s Server))
                (and
                    (link c s)
                    (not(link* c s))
                    (semaphore* s)
                    (forall ((c1 Client) (s1 Server))
                        (=>
                            (not
                                (and
                                    (= c c1)
                                    (= s s1)
                                )
                            )
                            (unchanged c1 s1)
                        )
                    )
                )
            )

        )

        ;not R*
        (not
            ;disjunction of configs
            (or
                ;config1
                ;all locked
                (and
                    (forall ((s Server))
                        (semaphore* s)
                    )
                    (forall ((c Client) (s Server)) 
                        (not(link* c s))
                    )
                )

                ;config2
                ;at least one locked, at least one linked
                (and
                    (exists ((c Client) (s Server))
                        (link* c s)
                    )
                    (exists ((s Server))
                        (semaphore* s)
                    )
                    (forall ((s Server))
                        (exists ((c Client))
                            (or
                                (semaphore* s)
                                (link* c s)
                            )
                        )
                    )
                    (forall ((s Server) (c Client))
                        (or
                            (not (semaphore* s))
                            (not(link* c s))
                        )
                    )
                    (forall ((s Server) (c1 Client) (c2 Client))
                        (or
                            (not (link* c1 s))
                            (not (link* c2 s))
                            (= c1 c2)
                        )
                    )
                )

                ;config3
                ;all linked
                (and 
                    (forall ((s Server)) (exists ((c Client))
                        (link* c s))
                    )
                    (forall ((s Server) (c1 Client) (c2 Client))
                        (or
                            (not (link* c1 s))
                            (not (link* c2 s))
                            (= c1 c2)
                        )
                    )
                    (forall ((s Server))
                        (not(semaphore* s))
                    )
                )
            )
        )
    )
)


(check-sat) 
(get-model)
