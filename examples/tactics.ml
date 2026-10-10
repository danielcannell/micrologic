theorem imp A : A -> A := by
    intro h;
    exact h.

theorem and_swap_curried A B : A -> B -> B and A := by
    intro a; intro b;
    split;
    exact b;
    exact a.

theorem and_assoc_curried A B C : A -> B -> C -> (A and B) and C := by
    intro a;
    intro b;
    intro c;
    split;
    split;
    exact a;
    exact b;
    exact c.

theorem or_intro A B : A -> B or A := by
    intro a;
    right;
    assumption.

theorem not_not_intro A : A -> not not A := by
    intro a; intro na;
    exact na a.

theorem exfalso A : False -> A := by
    intro false; exfalso; assumption.

theorem and_swap A B : A and B -> B and A := by
    intro h;
    destruct h as a b;
    split;
    { exact b };
    { exact a }.

theorem or_comm A B : A or B -> B or A := by
    intro h;
    cases h as a b;
    { right; exact a };
    { left; exact b }.

theorem modus_tollens A B : (A -> B) -> not B -> not A := by
    intro f; intro nb; intro a;
    apply nb;
    apply f;
    exact a.

theorem explode A B : A -> not A -> B := by
    intro a; intro na;
    exfalso;
    apply na;
    exact a.

axiom excluded_middle A : A or not A.

theorem not_not A : not not A -> A := by
    have h : A or not A;
    exact excluded_middle [A];
    cases h as a not_a;
    { intro _; assumption };
    { intro h; exfalso; exact h not_a }.
