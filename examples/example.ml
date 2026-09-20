-- The modus ponens theorem
theorem modus_ponens : A and (A -> B) -> B :=
    fun (h : A and (A -> B)) = (snd h) (fst h).

-- Examples from CS 15-317 --------------------

theorem truth : True :=
    fun (h : False) = h.

theorem true_and : True and True :=
    (truth, truth).

theorem true_or : True or A :=
    inl [A] truth.

theorem imp : A -> A :=
    fun (h: A) = h.

theorem and_id : (A and B) -> (A and B) :=
    fun (h: A and B) = h.

theorem complicated : (A -> (B -> C)) -> (B -> (A -> C)) :=
    fun (h: A -> (B -> C)) =
        fun (b: B) =
            fun (a: A) = h a b.

theorem impl_and_distrib : ((A -> D) and (B -> D) and (C -> D)) -> ((A or B or C) -> D) :=
    fun (h1: (A -> D) and (B -> D) and (C -> D)) =
        fun (h2 : A or B or C) =
            case h2 of
                | inl x => fst h1 x
                | inr x => case x of
                    | inl y => fst (snd h1) y
                    | inr y => snd (snd h1) y.

theorem impl_or_distrib : ((A or B or C) -> D) -> ((A -> D) and (B -> D) and (C -> D)) :=
    fun (h1 : (A or B or C) -> D) =
        (
            fun (a : A) = h1 (inl [B or C] a),
            (
                fun (b : B) = h1 (inr [A] inl [C] b),
                fun (c : C) =  h1 (inr [A] inr [B] c)
            )
        ).
