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
        ;R as a conjuction of constraints
        (and
            ;either linked or locked
            (forall ((s Server)) (exists ((c Client))
                (or 
                    (semaphore s) 
                    (link c s))
                )
            )
            ;a server cannot be connected to two distinct clients
            (forall ((c1 Client) (c2 Client) (s Server))
                (or 
                    (= c1 c2)
                    (not(link c1 s))
                    (not(link c2 s))
                )
            )
            ;a server is not both linked and locked
            (forall ((c Client) (s Server))
                (or 
                    (not(link c s))
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
            (and
                ;either linked or locked
                (forall ((s Server)) (exists ((c Client))
                    (or 
                        (semaphore* s) 
                        (link* c s))
                    )
                )
                ;a server cannot be connected to two distinct clients
                (forall ((c1 Client) (c2 Client) (s Server))
                    (or 
                        (= c1 c2)
                        (not(link* c1 s))
                        (not(link* c2 s))
                    )
                )
                ;a server is not both linked and locked
                (forall ((c Client) (s Server))
                    (or 
                        (not(link* c s))
                        (not(semaphore* s))
                    )
                )
            )
        )
    )
)


(check-sat) 
(get-model)
