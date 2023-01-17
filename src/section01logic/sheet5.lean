/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : P ↔ P :=
begin
  exact iff.rfl, -- this is what the above has found
end

example : P ↔ P :=
begin
  split,
  { exact id, }, -- identity function
  { intro hP,
    exact hP, },
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hPQ,
  cases hPQ with hPQ hQP,
  split,
  exact hQP,
  exact hPQ,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hPQ,
  cases hPQ with hPQ hQP,
  split; -- do exactly the same to both goals.
  assumption,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro hPQ,
  rw hPQ,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  rintro ⟨hPQ, hQP⟩, --intro then cases
  exact ⟨hQP, hPQ⟩,
end

-- very intriguing... why does this work? rw has something to 
-- close goals in it
example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro hPQ,
  rw hPQ,
  intro hQP,
  rw hQP, 
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hPQ hQR,
  rw [hPQ, hQR], -- how cute
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩,
  rintro ⟨hQ, hP⟩,
  exact ⟨hP, hQ⟩,
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split;
  exact (λ hPQ, ⟨hPQ.right, hPQ.left⟩)
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  { rintro ⟨⟨hP, hQ⟩, hR⟩,
    exact ⟨hP, hQ, hR⟩, },
  { rintro ⟨hP, hQ, hR⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩, },
end

example : P ↔ (P ∧ true) :=
begin
  split,
  { intro hP, 
    exact ⟨hP, true.intro⟩ },
  { rintro ⟨hP, _⟩,
    exact hP, }, 
end

example : false ↔ (P ∧ false) :=
begin
  sorry
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  sorry
end

example : ¬ (P ↔ ¬ P) :=
begin
  sorry,
end
