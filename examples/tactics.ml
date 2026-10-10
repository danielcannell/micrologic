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
