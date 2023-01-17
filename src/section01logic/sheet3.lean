/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro hT,
  apply hT,
  triv,
end

-- using the proof of true
example : ¬ true → false :=
begin
  intro hT,
  exact hT true.intro,
end

example : false → ¬ true :=
begin
  intros hF _,
  exact hF,
end

example : ¬ false → true :=
begin
  intro _,
  triv,
end

example : true → ¬ false :=
begin
  intros _ hF,
  exact hF,
end

example : false → ¬ P :=
begin
  intros hF _,
  exact hF,
end

example : P → ¬ P → false :=
begin
  intros hP hNP,
  exact hNP hP,
end

example : P → ¬ (¬ P) :=
begin
  intros hP hPF,
  exact hPF hP,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros hPQ hQF hP,
  exact hQF (hPQ hP),
end

-- TODO: what the what kinda proof is this
example : ¬ ¬ false → false :=
begin
  intro hF,
  apply hF,
  intro hF1,
  exact hF1,
end

example : ¬ ¬ P → P :=
begin
  intro hPFF,
  by_contra,
  exact hPFF h,
end

-- using the proof above
example : ¬ ¬ false → false :=
begin
  intro hF,
  by_contra,
  exact hF h,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros hNQP hP,
  by_contra hQ,
  exact hNQP hQ hP,
end