axiom excluded_middle A : A or not A.

proposition Knight A := A.
proposition Knave A := not A.
proposition Statement A S := (Knight A -> S) and (Knave A -> not S).

-- Puzzle 1
--
-- Alice says, "We are both knaves"

theorem puzzle1 Alice Bob : Statement Alice (Knave Alice and Knave Bob) <-> (Knave Alice and Knight Bob) :=
    (
        fun (h : (Knight Alice -> (Knave Alice and Knave Bob)) and (Knave Alice -> not (Knave Alice and Knave Bob))) =>
            case excluded_middle [Alice] of
                | inl x => (fst (fst h x), absurd [Knight Bob] (fst (fst h x) x))
                | inr x => (x, case excluded_middle [Bob] of
                    | inl y => y
                    | inr y => absurd [Knight Bob] (snd h x (x, y))
                ),
        fun (h : Knave Alice and Knight Bob) => (
            fun (h' : Knight Alice) => (
                fst h,
                absurd [not Bob] (fst h h')
            ),
            fun (h' : Knave Alice) => fun (h'' : Knave Alice and Knave Bob) => snd h'' (snd h)
        )
    ).
