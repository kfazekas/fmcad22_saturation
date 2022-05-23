(set-option :print-success false)
(set-option :produce-models true)

(set-logic UF)

(declare-sort node 0)
(declare-sort value 0)
(declare-sort quorum 0)

(declare-fun member (node quorum) Bool)
;quorum intersections are nonempty
(assert
    (forall ((q1 quorum) (q2 quorum))
        (exists ((n node))
            (and
                (member n q1)
                (member n q2)
            )
        )
    )
)
(declare-fun vote (node value) Bool)
(declare-fun didNotVote (node) Bool)
;didNotVote isn't a free function, rather an alias for a formula
;didNotVote(n) := \forall v . ~vote(n, v)
(assert
    (forall ((n node))
        (=
            (didNotVote n)
            (forall ((v value))
                (not (vote n v))
            )
        )
    )
)
(declare-fun decision (value) Bool)
(declare-fun chosenAt (quorum value) Bool)
;chosenAt(q, v) := \forall n . (n \in q) -> vote(n, v)
(assert
    (forall ((q quorum) (v value))
        (=
            (chosenAt q v)
            (forall ((n node))
                (=>
                    (member n q)
                    (vote n v)
                )
            )
        )
    )
)

(assert
    (xor
        ;conjunction of invariants
        (and
            (forall ((n node) (v value))
                (or
                    (not (didNotVote n))
                    (not (vote n v))
                )
            )
            (forall ((n node))
                (exists ((v value))
                    (or 
                        (didNotVote n)
                        (vote n v)
                    )
                )
            )
            (forall ((n node) (v1 value) (v2 value))
                (or
                    (not (vote n v1))
                    (not (vote n v2))
                    (= v1 v2)
                )
            )
            (forall ((v value))
                (exists ((q quorum))
                    (or
                        (not (decision v)
                        (chosenAt q v)
                    )
                )
            )
            (forall ((n node) (q quorum) (v value))
                (=>
                    (member n q)
                    (=>
                        (chosenAt q v)
                        (vote n v)    
                    )
                )
            )
            (forall ((q quorum) (v1 value))
                (=>
                    (not (chosenAt q v1))
                    (exists ((n node) (v2 value))
                        (and
                            (member n q)
                            (or
                                (didNotVote n)
                                (and
                                    (not(= v1 v2))
                                    (vote n v2)
                                )
                            )
                        )
                    )
                )
            )
        )

        ;disjunction of configs
        (or
            ;config 1
            (and
                (forall ((q quorum) (v value))
                    (not (chosenAt q v))
                )
                (forall ((v value))
                    (not (decision v))
                )
                (forall ((n node))
                    (didNotVote n)
                )
                (forall ((n node) (v value))
                    (not (vote n v))
                )
            )
            ;config 2
            (and
                (forall ((q quorum) (v value))
                    (not (chosenAt q v))
                )
                (forall ((v value))
                    (not (decision v))
                )
                (exists ((n node))
                    (didNotVote n)
                )
                (exists ((n node) (v value))
                    (vote n v)
                )
                (forall ((n node) (v1 value) (v2 value))
                    (=>
                        (and
                            (vote n v1)
                            (vote n v2)
                        )
                        (= v1 v2)
                    )
                )
            )
            ;config 3
            (and
                (forall ((q quorum) (v value))
                    (not (chosenAt q v))
                )
                (forall ((v value))
                    (not (decision v))
                )
                (forall ((n node))
                    (exists ((v value))
                        (or
                            (didNotVote n)
                            (vote n v)
                        )
                    )
                )
                (forall ((n node) (v1 value) (v2 value))
                    (=>
                        (and
                            (vote n v1)
                            (vote n v2)
                        )
                        (= v1 v2)
                    )
                )
            )
            ;config 4
            (and
                (exists ((q quorum) (v value))
                    (chosenAt q v)
                )
                (forall ((v value))
                    (not (decision v))
                )
                (forall ((n node))
                    (exists ((v value))
                        (or
                            (didNotVote n)
                            (vote n v)
                        )
                    )
                )
                (forall ((n node) (v1 value) (v2 value))
                    (=>
                        (and
                            (vote n v1)
                            (vote n v2)
                        )
                        (= v1 v2)
                    )
                )
            )
            ;config 5
            (and
                (exists ((q quorum) (v value))
                    (chosenAt q v)
                )
                (exists ((v value))
                    (decision v)
                )
                (forall ((v1 value) (v2 value))
                    (=>
                        (and
                            (decision v1)
                            (decision v2)
                        )
                        (= v1 v2)
                    )
                )
                (forall ((q quorum) (v value))
                    (=>
                        (chosenAt q v)
                        (decision v)
                    )
                )
                (forall ((n node))
                    (exists ((v value))
                        (or
                            (didNotVote n)
                            (vote n v)
                        )
                    )
                )
                (forall ((n node) (v1 value) (v2 value))
                    (=>
                        (and
                            (vote n v1)
                            (vote n v2)
                        )
                        (= v1 v2)
                    )
                )
            )
        )
    )
)

(check-sat)
(get-model)