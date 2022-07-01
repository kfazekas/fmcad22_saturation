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

(declare-fun vote* (node value) Bool)
(declare-fun didNotVote* (node) Bool)
;didNotVote isn't a free function, rather an alias for a formula
;didNotVote(n) := \forall v . ~vote(n, v)
(assert
    (forall ((n node))
        (=
            (didNotVote* n)
            (forall ((v value))
                (not (vote* n v))
            )
        )
    )
)
(declare-fun decision* (value) Bool)
(declare-fun chosenAt* (quorum value) Bool)
;chosenAt(q, v) := \forall n . (n \in q) -> vote(n, v)
(assert
    (forall ((q quorum) (v value))
        (=
            (chosenAt* q v)
            (forall ((n node))
                (=>
                    (member n q)
                    (vote* n v)
                )
            )
        )
    )
)

(assert
    (and
        ;R as a conjunction of invariants
        (and
            (forall ((n node) (v value))
                (or
                    (not (didNotVote n))
                    (not (vote n v))
                )
            )
            (forall ((n node))
                (exists ((v value))
                    (or (didNotVote n) (vote n v))
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
                        (not (decision v))
                        (chosenAt q v)
                    )
                )
            )
            (forall ((n node) (q quorum) (v value))
                (or
                    (not (member n q))
                    (not (chosenAt q v))
                    (vote n v)
                )
            )
            (forall ((q quorum) (v1 value))
                (exists ((n node) (v2 value))
                    (or
                        (chosenAt q v1)
                            (and
                                (member n q)
                                (didNotVote n)
                            )
                            (and
                                (member n q)
                                (and
                                    (not(= v1 v2))
                                    (vote n v2)
                                )
                            )
                    )
                )
            )
        )

        ;T
        (or
            ;cast_vote
            (exists ((n node) (v value))
                (and
                    (didNotVote n)
                    (vote* n v)
                    (forall ((v1 value) (q1 quorum))
                        (and
                            (= (chosenAt q1 v1) (chosenAt* q1 v1))
                            (= (decision v1) (decision* v1))
                        )
                    )
                    (forall ((n1 node) (v1 value))
                        (=>
                            (not 
                                (and
                                    (= n1 n)
                                    (= v1 v)
                                )
                            )
                            (and
                                (= (vote n1 v1) (vote* n1 v1))
                                (= (didNotVote n1) (didNotVote* n1))
                            )
                        )
                    )
                )
            )

            ;decide
            (exists ((v value) (q quorum))
                (and
                    (chosenAt q v)
                    (decision* v)
                    (forall ((n node) (v1 value))
                        (and
                            (= (vote n v1) (vote* n v1))
                            (= (didNotVote n) (didNotVote* n))
                        )
                    )
                    (forall ((v1 value) (q1 quorum))
                        (=>
                            (not 
                                (and
                                    (= v1 v)
                                    (= q1 q)
                                )
                            )
                            (and
                                (= (chosenAt q1 v1) (chosenAt* q1 v1))
                                (= (decision v1) (decision* v1))
                            )
                        )
                    )
                )
            )
        )

        ;not R'
        (not
            (and
                (forall ((n node) (v value))
                    (or
                        (not (didNotVote* n))
                        (not (vote* n v))
                    )
                )
                (forall ((n node))
                    (exists ((v value))
                        (or (didNotVote* n) (vote* n v))
                    )
                )
                (forall ((n node) (v1 value) (v2 value))
                    (or
                        (not (vote* n v1))
                        (not (vote* n v2))
                        (= v1 v2)
                    )
                )
                (forall ((v value))
                    (exists ((q quorum))
                        (or
                            (not (decision* v))
                            (chosenAt* q v)
                        )
                    )
                )
                (forall ((n node) (q quorum) (v value))
                    (or
                        (not (member n q))
                        (not (chosenAt* q v))
                        (vote* n v)
                    )
                )
                (forall ((q quorum) (v1 value))
                    (exists ((n node) (v2 value))
                        (or
                            (chosenAt* q v1)
                                (and
                                    (member n q)
                                    (didNotVote* n)
                                )
                                (and
                                    (member n q)
                                    (and
                                        (not(= v1 v2))
                                        (vote* n v2)
                                    )
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