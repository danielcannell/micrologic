-- Examples from CS 15-317 --------------------

theorem truth : True :=
    fun (h : False) => h.

theorem true_and : True and True :=
    (truth, truth).

theorem true_or A : True or A :=
    inl [A] truth.

theorem imp A : A -> A :=
    fun (h: A) => h.

theorem and_id A B : (A and B) -> (A and B) :=
    fun (h: A and B) => h.

theorem complicated A B C : (A -> (B -> C)) -> (B -> (A -> C)) :=
    fun (h: A -> (B -> C)) =>
        fun (b: B) =>
            fun (a: A) => h a b.

theorem impl_and_distrib A B C D : ((A -> D) and (B -> D) and (C -> D)) -> ((A or B or C) -> D) :=
    fun (h1: (A -> D) and (B -> D) and (C -> D)) =>
        fun (h2 : A or B or C) =>
            case h2 of
                | inl x => fst h1 x
                | inr x => case x of
                    | inl y => fst (snd h1) y
                    | inr y => snd (snd h1) y.

theorem impl_or_distrib A B C D : ((A or B or C) -> D) -> ((A -> D) and (B -> D) and (C -> D)) :=
    fun (h1 : (A or B or C) -> D) =>
        (
            fun (a : A) => h1 (inl [B or C] a),
            fun (b : B) => h1 (inr [A] inl [C] b),
            fun (c : C) =>  h1 (inr [A] inr [B] c)
        ).

theorem diag_and_proj A : (A -> (A and A)) and ((A and A) -> A) :=
    (
        fun (a : A) => (a, a),
        fun (a_and_a : A and A) => fst a_and_a
    ).

theorem double_neg A : not not (A or not A) :=
    fun (h1 : not (A or not A)) =>
        h1 (inr [A] (fun (a : A) => h1 (inl [not A] a))).

theorem triple_neg_simp A : not not not A -> not A :=
    fun (h : not not not A) =>
        fun (a : A) => h (fun (h1 : not A) => h1 a).

axiom excluded_middle A : A or not A.

theorem double_neg' A : not not A -> A :=
    fun (h : not not A) => case excluded_middle [A] of
        | inl x => x
        | inr x => absurd [A] (h x).

theorem equiv_is_reflexive A : A <-> A :=
    (fun (h: A) => h, fun (h: A) => h).

theorem equiv_is_commutative A B : (A <-> B) -> (B <-> A) :=
    fun (h : A <-> B) => (snd h, fst h).
