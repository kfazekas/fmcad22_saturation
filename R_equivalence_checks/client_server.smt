(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort Client 0)
(declare-sort Server 0)

(declare-fun link (Client Server) Bool)
(declare-fun semaphore (Server) Bool)

(assert 
(xor
    ;conjuction of constraints
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

    ;disjunction of configs
    (or
        ;all locked
        (and
            (forall ((s Server))
                (semaphore s)
            )
            (forall ((c Client) (s Server)) 
                (not(link c s))
            )
        )

        ;at least one locked, at least one linked
        (and
            (exists ((s Server))
                (semaphore s)
            )
            (exists ((s Server))
                (not(semaphore s))
            )
            (forall ((s Server))
                (=>
                    (not (semaphore s))
                    (exists ((c Client))
                        (link c s)
                    )
                )
            )
            (forall ((s Server) (c Client))
                (=>
                    (semaphore s)
                    (not(link c s))
                )
            )
            (forall ((s Server) (c1 Client) (c2 Client))
                (=>
                    (and
                        (link c1 s)
                        (link c2 s)
                    )
                    (= c1 c2)
                )
            )
        )

        ;all linked
        (and 
            (forall ((s Server)) (exists ((c Client))
                (link c s))
            )
            (forall ((s Server) (c1 Client) (c2 Client))
                (or
                    (not
                        (and
                            (link c1 s)
                            (link c2 s)
                        )
                    )
                    (= c1 c2)
                )
            )
            (forall ((s Server))
                (not(semaphore s))
            )
        )
    )
))


(check-sat) 
(get-model)
