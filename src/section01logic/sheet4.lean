/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro hPQ,
  exact hPQ.left,
end

example : P ∧ Q → P :=
begin
  rintro ⟨hP, hQ⟩,
  exact hP,
end

-- Alternative solution
example : P ∧ Q → P :=
begin
  intro hPQ,
  cases hPQ with hP _,
  exact hP,
end

example : P ∧ Q → Q :=
begin
  intro hPQ,
  cases hPQ with _ hQ,
  exact hQ,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intros hPQR hPQ,
  exact hPQR hPQ.left hPQ.right,
end

example : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  exact ⟨hP, hQ⟩,
end

example : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  exact hP, -- DON'T DO THIS! Will dock marks. After split, put each goal in { } or exacts if it's this simple
  exact hQ,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro hPQ,
  exact ⟨hPQ.right, hPQ.left⟩,
end

example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  split,
  exacts [hQ, hP],
end

example : P → P ∧ true :=
begin
  intro hP,
  split, -- gross
  exact hP,
  triv,
end

example : P → P ∧ true :=
begin
  intro hP,
  exact ⟨hP, true.intro⟩,
end

example : P → P ∧ true :=
λ hP, ⟨hP, true.intro⟩ -- yum

example : false → P ∧ false :=
begin
  intro hF,
  split,
  exfalso,
  exacts [hF, hF],
end

-- TODO: improve this
example : false → P ∧ false :=
begin
  intro hF,
  split, -- how do I do the thing where you solve part of a goal
  exfalso, -- and then the rest becomes the rest of the goal?
  { exact hF, }, 
  { exact hF, },
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros hPQ hQR,
  exact ⟨hPQ.left, hQR.right⟩,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros hPQR hP hQ,
  exact hPQR ⟨hP, hQ⟩,
end



