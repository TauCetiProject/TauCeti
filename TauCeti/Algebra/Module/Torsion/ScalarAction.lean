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
* `TauCeti.map_le_ker_toSpanSingleton_of_mem_torsionBySet`: an ideal of `k` killing `x` pushes
  forward to `I.map (algebraMap k A)` killing `x`.
* `TauCeti.smul_eq_of_sub_algebraMap_mem_map`: for an element killed by an ideal `I` of `k`,
  any `a : A` congruent to `algebraMap k A c` modulo `I.map (algebraMap k A)` acts as `c`.
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

namespace TauCeti

/-- In a module over a `k`-algebra `A`, if `x` is killed by an ideal `I` of `k`, then
`I.map (algebraMap k A)` lies in the kernel of `a ↦ a • x`. -/
theorem map_le_ker_toSpanSingleton_of_mem_torsionBySet {k A N : Type*}
    [CommSemiring k] [Semiring A] [Algebra k A]
    [AddCommMonoid N] [Module A N] [Module k N] [IsScalarTower k A N]
    {I : Ideal k} {x : N} (hx : x ∈ Submodule.torsionBySet k N ↑I) :
    I.map (algebraMap k A) ≤ LinearMap.ker (LinearMap.toSpanSingleton A N x) := by
  rw [Ideal.map_le_iff_le_comap]
  intro m hm
  simpa [LinearMap.mem_ker, algebraMap_smul] using
    (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨m, hm⟩

/-- In a module over a `k`-algebra `A`, if `x` is killed by an ideal `I` of `k` and
`a - algebraMap k A c` lies in `I.map (algebraMap k A)`, then `a • x = c • x`. -/
theorem smul_eq_of_sub_algebraMap_mem_map {k A N : Type*} [CommSemiring k] [Ring A] [Algebra k A]
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    {I : Ideal k} {x : N} (hx : x ∈ Submodule.torsionBySet k N ↑I)
    {a : A} {c : k} (ha : a - algebraMap k A c ∈ I.map (algebraMap k A)) :
    a • x = c • x := by
  have hzero : (a - algebraMap k A c) • x = 0 :=
    map_le_ker_toSpanSingleton_of_mem_torsionBySet hx ha
  rwa [sub_smul, algebraMap_smul, sub_eq_zero] at hzero

end TauCeti
