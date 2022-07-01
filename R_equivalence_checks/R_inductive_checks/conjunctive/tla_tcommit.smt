(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort RM 0)

(declare-fun aborted (RM) Bool)
(declare-fun committed (RM) Bool)
(declare-fun prepared (RM) Bool)
(declare-fun working (RM) Bool)
(declare-fun aborted* (RM) Bool)
(declare-fun committed* (RM) Bool)
(declare-fun prepared* (RM) Bool)
(declare-fun working* (RM) Bool)
(declare-fun unchanged (RM) Bool)
(assert 
    (forall ((r RM))
        (= 
            (unchanged r)
            (and
                (= (aborted r) (aborted* r))
                (= (committed r) (committed* r))
                (= (prepared r) (prepared* r))
                (= (working r) (working* r))
            )
        )
    )
)

(assert
    (and
        ;R as conjunction of invariants
        (and
            (forall ((R1 RM)) 
                (or
                    (not (aborted R1)) 
                    (not (committed R1))
                )
            )
            (forall ((R1 RM)) 
                (or
                    (not (aborted R1)) 
                    (not (prepared R1))
                )
            )
            (forall ((R1 RM)) 
                (or
                    (not (aborted R1)) 
                    (not (working R1))
                )
            )
            (forall ((R1 RM)) 
                (or
                    (not (committed R1)) 
                    (not (prepared R1))
                )
            )
            (forall ((R1 RM)) 
                (or
                    (not (committed R1)) 
                    (not (working R1))
                )
            )
            (forall ((R1 RM)) 
                (or
                    (not (prepared R1)) 
                    (not (working R1))
                )
            )
            (forall ((R1 RM)) 
                (or
                    (aborted R1) 
                    (committed R1)
                    (prepared R1)
                    (working R1)
                )
            )
            (forall ((R1 RM)) 
                (forall ((R2 RM)) 
                    (or
                        (= R1 R2)
                        (aborted R2)
                        (committed R1)
                        (prepared R1)
                        (prepared R2)
                        (working R2)
                    )
                )
            )
        )

        ;T
        (or
            ;prepare
            (exists ((r RM))
                (and
                    (working r)
                    (not (working* r))
                    (prepared* r)
                    (not (committed* r))
                    (not (aborted* r))
                    (forall ((r1 RM))
                        (=> (not (= r r1))
                            (unchanged r1)
                        )
                    )
                )
            )

            ;commit
            (exists ((r RM))
                (and
                    (prepared r)
                    (forall ((r2 RM))
                        (or
                            (prepared r2)
                            (committed r2)
                        )
                    )
                    (not (prepared* r))
                    (committed* r)
                    (not (aborted* r))
                    (not (working* r))
                    (forall ((r1 RM))
                        (=> (not (= r r1))
                            (unchanged r1)
                        )
                    )
                )
            )

            ;abort
            (exists ((r RM))
                (and
                    (forall ((r2 RM))
                        (not (committed r2))
                    )
                    (forall ((r2 RM))
                        (or
                            (prepared r2)
                            (working r2)
                        )
                    )
                    (not (prepared* r))
                    (aborted* r)
                    (not (committed* r))
                    (not (working* r))
                    (forall ((r1 RM))
                        (=> (not (= r r1))
                            (unchanged r1)
                        )
                    )
                )
            )
        )

        ;not R'
        (not
            (and
                (forall ((R1 RM)) 
                    (or
                        (not (aborted* R1)) 
                        (not (committed* R1))
                    )
                )
                (forall ((R1 RM)) 
                    (or
                        (not (aborted* R1)) 
                        (not (prepared* R1))
                    )
                )
                (forall ((R1 RM)) 
                    (or
                        (not (aborted* R1)) 
                        (not (working* R1))
                    )
                )
                (forall ((R1 RM)) 
                    (or
                        (not (committed* R1)) 
                        (not (prepared* R1))
                    )
                )
                (forall ((R1 RM)) 
                    (or
                        (not (committed* R1)) 
                        (not (working* R1))
                    )
                )
                (forall ((R1 RM)) 
                    (or
                        (not (prepared* R1)) 
                        (not (working* R1))
                    )
                )
                (forall ((R1 RM)) 
                    (or
                        (aborted* R1) 
                        (committed* R1)
                        (prepared* R1)
                        (working* R1)
                    )
                )
                (forall ((R1 RM)) 
                    (forall ((R2 RM)) 
                        (or
                            (= R1 R2)
                            (aborted* R2)
                            (committed* R1)
                            (prepared* R1)
                            (prepared* R2)
                            (working* R2)
                        )
                    )
                )
            )
        )
    )
)




(check-sat) 
(get-model)
