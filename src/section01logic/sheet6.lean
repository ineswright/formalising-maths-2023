/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro hP,
  left,
  exact hP,
end

example : Q → P ∨ Q :=
begin
  intro hQ,
  right,
  exact hQ,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros hPQ hPR hQR,
  cases hPQ with hP hQ,
  exact hPR hP,
  exact hQR hQ,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  sorry
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  sorry,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  sorry,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  sorry,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  sorry,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  sorry
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  sorry
end
