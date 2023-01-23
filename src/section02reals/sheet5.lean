/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tends_to` from a previous sheet

-- to get a proof from a type class
-- apply_instance tactic should figure it out 
-- so can write have : linear_order ℝ := {apply_instance,},

-- you can maybe do this one now
theorem tends_to_neg {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  rw tends_to at *,
  intros ε hε,
  specialize ha ε hε, -- try to do linear rewriting?
  cases ha with B ha,
  use B,
  intros n hB,
  specialize ha n hB,
  -- or simp, rw abs_sub_comm, exact ha, 
  rw [←abs_neg] at ha,
  rw ←neg_add',
  exact ha,
end

/-
`tends_to_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful. 
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tends_to_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n + b n) (t + u) :=
begin
  rw tends_to at *,
  intros e he,
  specialize ha (e/2) (half_pos he),
  specialize hb (e/2) (half_pos he),
  cases ha with k ha,
  cases hb with j hb,
  use (max k j),
  intros n hn,
  specialize ha n (le_of_max_le_left hn),
  specialize hb n (le_of_max_le_right hn),
  have h3 : a n - t + (b n - u) = a n + b n - (t + u), -- how to get rid of this?
  { ring, },
  rw [←h3, ←(add_halves e)],
  exact lt_of_le_of_lt (abs_add (a n - t) (b n - u)) (add_lt_add ha hb),
end

-- what is simp_rw -- rw but deeper

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n - b n) (t - u) :=
begin
  exact tends_to_add ha (tends_to_neg hb),
end

