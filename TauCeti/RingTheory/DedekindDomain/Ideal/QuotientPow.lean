/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Quotients by consecutive powers of an ideal

For an ideal `P` of a commutative ring `B` and an element `a ∈ P ^ n`, multiplication by `a`
descends to a `B`-linear map `B ⧸ P → B ⧸ P ^ (n + 1)`. This file studies the sequence

`0 → B ⧸ P --· a--> B ⧸ P ^ (n + 1) → B ⧸ P ^ n → 0`

for `a ∈ P ^ n` with `a ∉ P ^ (n + 1)`. The first map is injective as soon as `P` is maximal, and
the sequence is exact in the middle when `P` is a nonzero prime of a Dedekind domain, where
`P ^ n / P ^ (n + 1)` is a one-dimensional `B ⧸ P`-vector space spanned by the class of `a`.

## Main results

* `Ideal.le_comap_mulLeft_pow_succ`: multiplication by `a ∈ I ^ n` carries `I` into `I ^ (n + 1)`.
* `Ideal.mapQ_mulLeft_pow_succ_injective`: for `P` maximal, multiplication by `a` is injective
  on `B ⧸ P → B ⧸ P ^ (n + 1)`.
* `Ideal.exact_mapQ_mulLeft_pow_succ`: for `P` a nonzero prime of a Dedekind domain, the sequence
  `B ⧸ P → B ⧸ P ^ (n + 1) → B ⧸ P ^ n` is exact.
-/

public section

namespace Ideal

/-- Multiplication by an element `a ∈ I ^ n` carries `I` into `I ^ (n + 1)`. This is the
compatibility condition under which `LinearMap.mulLeft B a` descends, via `Submodule.mapQ`, to a
`B`-linear map `B ⧸ I → B ⧸ I ^ (n + 1)`. -/
theorem le_comap_mulLeft_pow_succ {B : Type*} [CommSemiring B] {I : Ideal B} {a : B} {n : ℕ}
    (ha : a ∈ I ^ n) : I ≤ Submodule.comap (LinearMap.mulLeft B a) (I ^ (n + 1)) := fun x hx ↦ by
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, pow_succ]
  exact mul_mem_mul ha hx

variable {B : Type*} [CommRing B] {P : Ideal B} {a : B} {n : ℕ}

/-- For a maximal ideal `P` and `a ∈ P ^ n` with `a ∉ P ^ (n + 1)`, multiplication by `a` induces
an injective `B`-linear map `B ⧸ P → B ⧸ P ^ (n + 1)`. -/
theorem mapQ_mulLeft_pow_succ_injective [P.IsMaximal] (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) :
    Function.Injective
      (Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a) (le_comap_mulLeft_pow_succ ha)) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at hy
  exact (Submodule.Quotient.mk_eq_zero _).2 ((IsMaximal.mem_pow_mul P hy).resolve_left ha')

/-- For a nonzero prime `P` of a Dedekind domain and `a ∈ P ^ n` with `a ∉ P ^ (n + 1)`, the
sequence `B ⧸ P → B ⧸ P ^ (n + 1) → B ⧸ P ^ n`, whose first map is multiplication by `a` and
whose second map is the quotient map, is exact. -/
theorem exact_mapQ_mulLeft_pow_succ [IsDedekindDomain B] [P.IsPrime] (hP : P ≠ ⊥)
    (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) :
    Function.Exact
      (Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a) (le_comap_mulLeft_pow_succ ha))
      (Submodule.factor (pow_le_pow_right (I := P) (n.le_add_right 1))) := by
  intro y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range,
    (Submodule.Quotient.mk_surjective _).exists, LinearMap.mulLeft_apply, Submodule.Quotient.eq]
  refine ⟨fun hu ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨x, w, hw, rfl⟩ := exists_mul_add_mem_pow_succ hP a u ha ha' hu
    exact ⟨x, by rwa [sub_add_cancel_left, neg_mem_iff]⟩
  · exact (Submodule.sub_mem_iff_right _ (mul_mem_right x _ ha)).1 (pow_le_pow_right n.le_succ hx)

end Ideal
