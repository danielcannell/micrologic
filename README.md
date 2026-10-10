# Micrologic

Micrologic is a theorem prover and proof assistant for intuitionistic propositional logic based on the Curry-Howard
correspondence. The purpose of this project is to learn how 'real' proof assistants like Lean and Rocq work.

Here is a small example:

```
-- Micrologic is based on intuitionistic logic, which does not assume the law
-- of excluded middle. If we want to work with classical logic we have to
-- introduce it as an axiom.
axiom excluded_middle A : A or not A.

-- With the law of excluded middle as an axiom, we can prove double negation
-- elimination.
theorem double_negation_elimination A : not not A -> A := by
    -- Assume `not not A`, then the goal is to show `A`
    intro not_not_a;

    -- Either `A` or `not A`; examine the two cases
    have a_or_not_a : A or not A := excluded_middle [A];
    cases a_or_not_a as a not_a;
    {
        -- If `A`, then that is exactly our goal
        exact a
    };
    {
        -- If `not A`, then `not not A` leads to a contradiction
        absurd not_not_a; exact not_a
    }.
```

The full language reference is in [docs/reference.md](docs/reference.md).
