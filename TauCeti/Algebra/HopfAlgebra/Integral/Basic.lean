/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Integral submodules of a bialgebra

The left integrals satisfy `h * t = ε(h) • t`; right integrals satisfy the reversed
identity. Both submodules include zero, and no normalization of the counit is imposed.
They are defined over a commutative semiring, without a finite generation assumption.

Bialgebra isomorphisms identify integral submodules. The antipode takes left integrals
to right integrals and conversely; if it is bijective, it identifies the two submodules.
These comparisons allow existence and dimension results for integrals to be transferred
between presentations and between the two handedness conventions.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
-/

public section

namespace TauCeti

open Coalgebra HopfAlgebra
open scoped Coalgebra

variable (R H : Type*) [CommSemiring R] [Semiring H]

section Bialgebra

variable [Bialgebra R H]

/-- The submodule of left integrals, including zero. A nonzero integral need not have
nonzero counit. -/
def leftIntegral : Submodule R H where
  carrier := {t | ∀ h : H, h * t = counit (R := R) h • t}
  zero_mem' := by simp
  add_mem' ht hu h := by simp [mul_add, ht h, hu h, smul_add]
  smul_mem' r t ht h := by
    rw [mul_smul_comm, ht h, smul_comm r]

/-- The submodule of right integrals, including zero. -/
def rightIntegral : Submodule R H where
  carrier := {t | ∀ h : H, t * h = counit (R := R) h • t}
  zero_mem' := by simp
  add_mem' ht hu h := by simp [add_mul, ht h, hu h, smul_add]
  smul_mem' r t ht h := by
    rw [smul_mul_assoc, ht h, smul_comm r]

variable {R H}

theorem mem_leftIntegral_iff {t : H} :
    t ∈ leftIntegral R H ↔ ∀ h : H, h * t = counit (R := R) h • t :=
  Iff.rfl

theorem mem_rightIntegral_iff {t : H} :
    t ∈ rightIntegral R H ↔ ∀ h : H, t * h = counit (R := R) h • t :=
  Iff.rfl

/-- Right multiplication preserves left integrals. -/
theorem mul_mem_leftIntegral {t : H} (ht : t ∈ leftIntegral R H) (a : H) :
    t * a ∈ leftIntegral R H := by
  intro h
  rw [← mul_assoc, ht h, smul_mul_assoc]

/-- Left multiplication preserves right integrals. -/
theorem mul_mem_rightIntegral {t : H} (ht : t ∈ rightIntegral R H) (a : H) :
    a * t ∈ rightIntegral R H := by
  intro h
  rw [mul_assoc, ht h, mul_smul_comm]

/-- Over the base semiring every element is a left integral. -/
@[simp]
theorem leftIntegral_self : leftIntegral R R = ⊤ := by
  ext t
  simp [mem_leftIntegral_iff, smul_eq_mul]

/-- Over the base semiring every element is a right integral. -/
@[simp]
theorem rightIntegral_self : rightIntegral R R = ⊤ := by
  ext t
  simp [mem_rightIntegral_iff, smul_eq_mul, mul_comm]

end Bialgebra

section Antipode

variable {R H} [HopfAlgebra R H]

/-- The antipode takes left integrals to right integrals, without requiring bijectivity. -/
theorem antipode_mem_rightIntegral {t : H} (ht : t ∈ leftIntegral R H) :
    antipode R t ∈ rightIntegral R H := by
  intro h
  classical
  let r := ℛ R h
  have hs (x : H) : antipode R t * antipode R x = counit (R := R) x • antipode R t := by
    rw [← antipode_mul_antidistrib, ht x, map_smul]
  calc
    antipode R t * h = ∑ i ∈ r.index, (counit (R := R) (r.left i) • antipode R t) *
        r.right i := by
      conv_lhs => rw [← sum_counit_smul r]
      simp [Finset.mul_sum]
    _ = antipode R t * (∑ i ∈ r.index, antipode R (r.left i) * r.right i) := by
      simp [Finset.mul_sum, ← mul_assoc, hs]
    _ = counit (R := R) h • antipode R t := by
      rw [sum_antipode_mul_eq_algebraMap_counit r]
      simp [Algebra.smul_def, Algebra.commutes]

/-- The antipode takes right integrals to left integrals, without requiring bijectivity. -/
theorem antipode_mem_leftIntegral {t : H} (ht : t ∈ rightIntegral R H) :
    antipode R t ∈ leftIntegral R H := by
  intro h
  classical
  let r := ℛ R h
  have hs (x : H) : antipode R x * antipode R t = counit (R := R) x • antipode R t := by
    rw [← antipode_mul_antidistrib, ht x, map_smul]
  calc
    h * antipode R t = ∑ i ∈ r.index, r.left i *
        (counit (R := R) (r.right i) • antipode R t) := by
      have hc : ∑ i ∈ r.index, counit (R := R) (r.right i) • r.left i = h := by
        simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using
          congrArg (TensorProduct.rid R H) (sum_tmul_counit_eq r)
      conv_lhs => rw [← hc]
      simp [Finset.sum_mul]
    _ = (∑ i ∈ r.index, r.left i * antipode R (r.right i)) * antipode R t := by
      simp [Finset.sum_mul, mul_assoc, hs]
    _ = counit (R := R) h • antipode R t := by
      rw [sum_mul_antipode_eq_algebraMap_counit r, ← Algebra.smul_def]

/-- When the antipode is injective, membership in the right-integral submodule
can be tested after applying it. -/
theorem antipode_mem_rightIntegral_iff (hS : Function.Injective (antipode R : H → H))
    {t : H} : antipode R t ∈ rightIntegral R H ↔ t ∈ leftIntegral R H := by
  refine ⟨fun ht h => hS ?_, antipode_mem_rightIntegral⟩
  simpa only [antipode_mul_antidistrib, map_smul, counit_antipode] using ht (antipode R h)

/-- When the antipode is injective, membership in the left-integral submodule
can be tested after applying it. -/
theorem antipode_mem_leftIntegral_iff (hS : Function.Injective (antipode R : H → H))
    {t : H} : antipode R t ∈ leftIntegral R H ↔ t ∈ rightIntegral R H := by
  refine ⟨fun ht h => hS ?_, antipode_mem_leftIntegral⟩
  simpa only [antipode_mul_antidistrib, map_smul, counit_antipode] using ht (antipode R h)

/-- A bijective antipode identifies the left and right integral submodules. -/
noncomputable def integralAntipodeEquiv (hS : Function.Bijective (antipode R : H → H)) :
    leftIntegral R H ≃ₗ[R] rightIntegral R H :=
  LinearEquiv.ofBijective
    ((antipode R).restrict (fun _ ht => antipode_mem_rightIntegral ht))
    ⟨fun x y h => Subtype.ext (hS.injective (congrArg Subtype.val h)), fun y => by
      obtain ⟨x, hx⟩ := hS.surjective (y : H)
      refine ⟨⟨x, (antipode_mem_rightIntegral_iff hS.injective).mp ?_⟩, Subtype.ext hx⟩
      simpa only [hx] using y.property⟩

@[simp]
theorem integralAntipodeEquiv_apply (hS : Function.Bijective (antipode R : H → H))
    (t : leftIntegral R H) :
    (integralAntipodeEquiv hS t : H) = antipode R (t : H) :=
  (rfl)

/-- The inverse integral comparison is an inverse image under the antipode. -/
@[simp]
theorem antipode_integralAntipodeEquiv_symm_apply
    (hS : Function.Bijective (antipode R : H → H)) (t : rightIntegral R H) :
    antipode R ((integralAntipodeEquiv hS).symm t : H) = (t : H) := by
  simpa only [integralAntipodeEquiv_apply] using
    congrArg Subtype.val ((integralAntipodeEquiv hS).apply_symm_apply t)

end Antipode

end TauCeti

namespace BialgEquiv

open Coalgebra TauCeti

variable {R H K : Type*} [CommSemiring R] [Semiring H] [Semiring K]
  [Bialgebra R H] [Bialgebra R K]

/-- A bialgebra isomorphism preserves and reflects left integrals. -/
@[simp]
theorem apply_mem_leftIntegral_iff (e : H ≃ₐc[R] K) {t : H} :
    e t ∈ leftIntegral R K ↔ t ∈ leftIntegral R H := by
  constructor
  · intro ht h
    apply EquivLike.injective e
    simpa using ht (e h)
  · intro ht k
    obtain ⟨h, rfl⟩ := EquivLike.surjective e k
    simpa using congrArg e (ht h)

/-- A bialgebra isomorphism preserves and reflects right integrals. -/
@[simp]
theorem apply_mem_rightIntegral_iff (e : H ≃ₐc[R] K) {t : H} :
    e t ∈ rightIntegral R K ↔ t ∈ rightIntegral R H := by
  constructor
  · intro ht h
    apply EquivLike.injective e
    simpa using ht (e h)
  · intro ht k
    obtain ⟨h, rfl⟩ := EquivLike.surjective e k
    simpa using congrArg e (ht h)

/-- Restrict a bialgebra isomorphism to the left integral submodules. -/
def leftIntegralEquiv (e : H ≃ₐc[R] K) : leftIntegral R H ≃ₗ[R] leftIntegral R K :=
  e.toAlgEquiv.toLinearEquiv.ofSubmodules _ _ (by
    ext k
    rw [Submodule.mem_map_equiv]
    exact e.symm.apply_mem_leftIntegral_iff)

/-- Restrict a bialgebra isomorphism to the right integral submodules. -/
def rightIntegralEquiv (e : H ≃ₐc[R] K) : rightIntegral R H ≃ₗ[R] rightIntegral R K :=
  e.toAlgEquiv.toLinearEquiv.ofSubmodules _ _ (by
    ext k
    rw [Submodule.mem_map_equiv]
    exact e.symm.apply_mem_rightIntegral_iff)

@[simp]
theorem leftIntegralEquiv_apply (e : H ≃ₐc[R] K) (t : leftIntegral R H) :
    (e.leftIntegralEquiv t : K) = e (t : H) :=
  (rfl)

@[simp]
theorem rightIntegralEquiv_apply (e : H ≃ₐc[R] K) (t : rightIntegral R H) :
    (e.rightIntegralEquiv t : K) = e (t : H) :=
  (rfl)

@[simp]
theorem leftIntegralEquiv_symm_apply (e : H ≃ₐc[R] K) (t : leftIntegral R K) :
    ((e.leftIntegralEquiv).symm t : H) = e.symm (t : K) := by
  rw [leftIntegralEquiv, LinearEquiv.ofSubmodules_symm_apply]
  rfl

@[simp]
theorem rightIntegralEquiv_symm_apply (e : H ≃ₐc[R] K) (t : rightIntegral R K) :
    ((e.rightIntegralEquiv).symm t : H) = e.symm (t : K) := by
  rw [rightIntegralEquiv, LinearEquiv.ofSubmodules_symm_apply]
  rfl

end BialgEquiv
