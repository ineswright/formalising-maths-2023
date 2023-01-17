/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : true :=
begin
  triv,
end

example : true :=
begin
  exact true.intro,
end

example : true → true :=
begin
  intro _,
  triv,
end

example : false → true :=
begin
  intro _,
  triv,
end

example : false → false :=
begin
  intro f,
  exact f,
end

example : false → P :=
begin
  intro f,
  cases f, -- there are no cases to examine, so trivially true
end

example : (true → false) → false :=
begin
  intro hTF,
  apply hTF,
  triv,
end

example : false → P :=
begin
  intro h,
  exfalso,
  exact h,
end

example : true → false → true → false → true → false :=
begin
  intros _ hf,
  exfalso,
  exact hf,
end

example : P → ((P → false) → false) :=
begin
  intros hP hPF,
  exact hPF hP,
end

example : (P → false) → P → Q :=
begin
  intros hPF hP,
  exfalso,
  exact hPF hP,
end

example : (true → false) → P :=
begin
  intro hTF,
  exfalso,
  apply hTF,
  triv,
end