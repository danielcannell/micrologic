axiom excluded_middle A : A or not A.

theorem by_contradiction A : not not A -> A := by
    -- Assume not not A, then the goal is to show A
    intro not_not_a;

    -- Either A is true or A is false; examine the two cases
    have a_or_not_a : A or not A := excluded_middle [A];
    cases a_or_not_a as a not_a;
    {
        -- If A is true, then that is exactly our goal
        exact a
    };
    {
        -- If A is false, then not not A leads to a contradiction
        absurd not_not_a; exact not_a
    }.

proposition Knight A := A.
proposition Knave A := not A.
proposition Statement A S := (Knight A -> S) and (Knave A -> not S).

-- Puzzle 1: Alice says, "We are both knaves"
proposition Puzzle1 Alice Bob := Statement Alice (Knave Alice and Knave Bob).

-- Prove using terms
theorem puzzle1 Alice Bob : Puzzle1 Alice Bob <-> (Knave Alice and Knight Bob) :=
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

-- Prove using tactics
theorem puzzle1' Alice Bob : Puzzle1 Alice Bob <-> (Knave Alice and Knight Bob) := by
    split;
    {
        -- If Alice's statement is consistent, then Alice is a knave and Bob is a knight

        -- Split Alice's statement into the knight and knave cases
        intro statement;
        destruct statement as if_knight if_knave;

        -- Alice is a knave:
        have knave_alice : Knave Alice;
        {
            -- Suppose Alice were a knight
            intro knight_alice;

            -- Then her statement is true, making her a knave
            have knave_alice : Knave Alice := fst (if_knight knight_alice);

            -- Which is a contradiction
            exact knave_alice knight_alice
        };

        -- Bob is a knight:
        have knight_bob : Knight Bob;
        {
            -- Suppose Bob were a knave
            apply by_contradiction [Bob]; intro knave_bob;

            -- Alice is a knave, so her statement is false and they are not both knaves
            apply if_knave; { exact knave_alice };

            -- Which is a contradiction
            exact (knave_alice, knave_bob)
        };

        -- So Alice is a knave and Bob is a knight
        exact (knave_alice, knight_bob)
    };
    {
        -- If Alice is a knave and Bob is a knight, then Alice's statement is consistent

        -- Split the solution: Alice is a knave; Bob is a knight
        intro solution;
        destruct solution as knave_alice knight_bob;

        -- Split Alice's statement into the knight and knave cases
        split;
        {
            -- Alice isn't a knight, so this case can't happen
            intro knight_alice; absurd knave_alice; exact knight_alice
        };
        {
            -- Alice and Bob are both knaves, which is the opposite of Alice's statement. This is consistent with her
            -- being a knave
            intro _; intro both_knaves;
            destruct both_knaves as _ knave_bob;
            exact knave_bob knight_bob
        }
    }.