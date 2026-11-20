/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Scalar actions on modules killed by an ideal

Let `A` be a `k`-algebra and `N` an `A`-module killed by an ideal `J`. Elements of `A` that are
congruent modulo `J` act in the same way on `N`. In particular, if `a * f ≡ c • f` modulo `J`
for a scalar `c : k`, then `a` acts as `c` on every vector fixed by `f`, and if
`f * a ≡ c • f` modulo `J`, then `f * a` acts as `c • f` on all of `N`.

## Main results

* `Module.IsTorsionBySet.smul_eq_smul_of_smul_eq_self`: on a vector fixed by `f`, `a` acts as
  `c` when `a * f ≡ c • f` modulo `J`.
* `Module.IsTorsionBySet.smul_smul_eq_smul_smul`: `f • a • x = c • f • x` when
  `f * a ≡ c • f` modulo `J`.
-/

public section

namespace Module.IsTorsionBySet

variable {k A N : Type*} [CommSemiring k] [Ring A] [Algebra k A] {J : Ideal A}
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- On a vector fixed by `f` in a module killed by `J`, an element `a` acts as the scalar `c`
with `a * f ≡ c • f` modulo `J`. -/
theorem smul_eq_smul_of_smul_eq_self (hN : Module.IsTorsionBySet A N J) {f a : A} {c : k}
    (hr : a * f - c • f ∈ J) {n : N} (hn : f • n = n) : a • n = c • n :=
  calc a • n = a • f • n := by rw [hn]
    _ = (a * f - c • f) • n + (c • f) • n := by rw [← add_smul, sub_add_cancel, mul_smul]
    _ = c • n := by rw [@hN n ⟨_, hr⟩, zero_add, smul_assoc, hn]

/-- In a module killed by `J`, `f * a` acts as the scalar `c • f` with `f * a ≡ c • f`
modulo `J`. -/
theorem smul_smul_eq_smul_smul (hN : Module.IsTorsionBySet A N J) {f a : A} {c : k}
    (hl : f * a - c • f ∈ J) (x : N) : f • a • x = c • f • x :=
  calc f • a • x = (f * a - c • f) • x + (c • f) • x := by
        rw [← add_smul, sub_add_cancel, mul_smul]
    _ = c • f • x := by rw [@hN x ⟨_, hl⟩, zero_add, smul_assoc]

end Module.IsTorsionBySet
