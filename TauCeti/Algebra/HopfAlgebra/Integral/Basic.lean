/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.Algebra.Module.Submodule.Equiv
public import TauCeti.Algebra.Bialgebra.Coop
public import TauCeti.Algebra.Bialgebra.MulOpposite

/-!
# Integral submodules of a bialgebra

The left integrals satisfy `h * t = ε(h) • t`; right integrals satisfy the reversed
identity. Both submodules include zero, and no normalization of the counit is imposed.
They are defined over a commutative semiring, without a finite generation assumption.

Bialgebra isomorphisms identify integral submodules. The antipode takes left integrals
to right integrals and conversely; if it is bijective, it identifies the two submodules.
For a left integral `t`, `rTensor_mulLeft_lTensor_antipode_comul_of_mem_leftIntegral` gives the
tensor–antipode commutation identity `(x * t₁) ⊗ S(t₂) = t₁ ⊗ (S(t₂) * x)`, which underlies the
dual-basis partner formulas. We also record integral correspondences under `TauCeti.Coop`
(`TauCeti.Coop.mk_mem_leftIntegral_iff`, `TauCeti.Coop.mk_mem_rightIntegral_iff`) and `ᵐᵒᵖ`
(`MulOpposite.op_mem_leftIntegral_iff`, `MulOpposite.op_mem_rightIntegral_iff`).
These comparisons allow existence and dimension results for integrals to be transferred
between presentations and between the two handedness conventions.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
-/

public section

namespace TauCeti

open Coalgebra HopfAlgebra
open scoped Coalgebra TensorProduct

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

/-- A bialgebra is unimodular when its left and right integral submodules agree. -/
def IsUnimodular : Prop := leftIntegral R H = rightIntegral R H

/-- Unimodularity is equality of the two integral spaces. -/
theorem isUnimodular_iff : IsUnimodular R H ↔ leftIntegral R H = rightIntegral R H :=
  Iff.rfl

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

private noncomputable def leftIntegralPhi (R H : Type*) [CommSemiring R] [Semiring H]
    [HopfAlgebra R H] (t : H) : (H ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] H :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun ab c ↦ (((LinearMap.mul R H).flip c ∘ₗ antipode R).lTensor H)
      (ab * comul (R := R) t))
    (fun _ _ _ ↦ by simp [add_mul])
    (fun _ _ _ ↦ by simp)
    (fun ab c₁ c₂ ↦ by simp [LinearMap.add_comp, LinearMap.lTensor_add])
    (fun r ab c ↦ by simp [LinearMap.smul_comp, LinearMap.lTensor_smul])

private theorem leftIntegralPhi_rTensor_comul {t : H} (ht : t ∈ leftIntegral R H)
    (w : H ⊗[R] H) :
    leftIntegralPhi R H t ((comul (R := R)).rTensor H w) =
      (((LinearMap.mul R H).flip (TensorProduct.lid R H ((counit (R := R)).rTensor H w)) ∘ₗ
        antipode R).lTensor H) (comul t) := by
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [map_add, hu, hv, LinearMap.add_comp, LinearMap.lTensor_add, LinearMap.add_apply]
  | tmul d c =>
    have hdt : comul (R := R) d * comul (R := R) t =
        counit (R := R) d • comul (R := R) t := by
      rw [← Bialgebra.comul_mul, (mem_leftIntegral_iff.mp ht) d, map_smul]
    simp [leftIntegralPhi, hdt, LinearMap.smul_comp, LinearMap.lTensor_smul]

private theorem leftIntegralPhi_assoc_symm_tmul (t a : H) (z : H ⊗[R] H) :
    leftIntegralPhi R H t ((TensorProduct.assoc R H H H).symm (a ⊗ₜ[R] z)) =
      (LinearMap.mul R H a).rTensor H
        ((((LinearMap.mul R H).flip (LinearMap.mul' R H ((antipode R).rTensor H z)) ∘ₗ
          antipode R).lTensor H) (comul (R := R) t)) := by
  induction z using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.tmul_add, map_add, hu, hv, LinearMap.add_comp, LinearMap.lTensor_add,
      LinearMap.add_apply]
  | tmul b c =>
    simp only [TensorProduct.assoc_symm_tmul, leftIntegralPhi, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
    induction comul (R := R) t using TensorProduct.inductionOn with
    | add u v hu hv => simp only [mul_add, map_add, hu, hv]
    | tmul u v => simp [antipode_mul_antidistrib, mul_assoc]

private theorem leftIntegralPhi_assoc_symm_lTensor_comul (t : H) (w : H ⊗[R] H) :
    leftIntegralPhi R H t ((TensorProduct.assoc R H H H).symm
      ((comul (R := R)).lTensor H w)) =
      (LinearMap.mul R H (TensorProduct.rid R H
        ((counit (R := R)).lTensor H w))).rTensor H
          ((antipode R).lTensor H (comul (R := R) t)) := by
  induction w using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [map_add, hu, hv, LinearMap.rTensor_add, LinearMap.add_apply]
  | tmul a d =>
    have hmulR (r : R) :
        (LinearMap.mul R H).flip (algebraMap R H r) ∘ₗ antipode R = r • antipode R :=
      LinearMap.ext fun y ↦ by simp [Algebra.algebraMap_eq_smul_one]
    simp [leftIntegralPhi_assoc_symm_tmul, hmulR, LinearMap.lTensor_smul, LinearMap.rTensor_smul]

/-- For a left integral `t`, multiplying the first coproduct leg on the left by `x` after
applying `S` to the second leg equals multiplying `S(t₂)` on the right by `x`:
`x * t₁ ⊗ S(t₂) = t₁ ⊗ S(t₂) * x`. -/
theorem rTensor_mulLeft_lTensor_antipode_comul_of_mem_leftIntegral
    {t : H} (ht : t ∈ leftIntegral R H) (x : H) :
    (LinearMap.mulLeft R x).rTensor H ((antipode R).lTensor H (comul t)) =
      ((LinearMap.mulRight R x ∘ₗ antipode R).lTensor H) (comul t) := by
  have hL : LinearMap.mulLeft R x = LinearMap.mul R H x := LinearMap.ext fun _ ↦ rfl
  have hR : LinearMap.mulRight R x = (LinearMap.mul R H).flip x := LinearMap.ext fun _ ↦ rfl
  have hco : (comul (R := R)).rTensor H (comul x) =
      (TensorProduct.assoc R H H H).symm ((comul (R := R)).lTensor H (comul x)) := by
    apply (TensorProduct.assoc R H H H).injective
    simp [coassoc_apply x]
  have heq := congrArg (leftIntegralPhi R H t) hco
  rw [leftIntegralPhi_rTensor_comul ht, leftIntegralPhi_assoc_symm_lTensor_comul,
    rTensor_counit_comul, lTensor_counit_comul] at heq
  simpa [hL, hR] using heq.symm

end Antipode

end TauCeti

namespace TauCeti.Coop

open Coalgebra TauCeti

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- Left integrals in `Coop H` are the same elements as left integrals in `H`. -/
@[simp]
theorem mk_mem_leftIntegral_iff {t : H} :
    mk t ∈ leftIntegral R (Coop H) ↔ t ∈ leftIntegral R H := by
  simp only [mem_leftIntegral_iff]
  constructor
  · intro ht h
    simpa only [val_mul, val_smul, val_mk, counit_mk] using congrArg val (ht (mk h))
  · intro ht h
    induction h with | mk h =>
    exact ext (by simpa only [val_mul, val_smul, val_mk, counit_mk] using ht h)

/-- Right integrals in `Coop H` are the same elements as right integrals in `H`. -/
@[simp]
theorem mk_mem_rightIntegral_iff {t : H} :
    mk t ∈ rightIntegral R (Coop H) ↔ t ∈ rightIntegral R H := by
  simp only [mem_rightIntegral_iff]
  constructor
  · intro ht h
    simpa only [val_mul, val_smul, val_mk, counit_mk] using congrArg val (ht (mk h))
  · intro ht h
    induction h with | mk h =>
    exact ext (by simpa only [val_mul, val_smul, val_mk, counit_mk] using ht h)

end TauCeti.Coop

namespace MulOpposite

open Coalgebra TauCeti

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- Left integrals in `Hᵐᵒᵖ` correspond to right integrals in `H`. -/
@[simp]
theorem op_mem_leftIntegral_iff {t : H} :
    op t ∈ leftIntegral R Hᵐᵒᵖ ↔ t ∈ rightIntegral R H := by
  simp only [mem_leftIntegral_iff, mem_rightIntegral_iff]
  refine ⟨fun ht h ↦ op_injective (by
    simpa only [← op_mul, counit_op, op_smul] using ht (op h)), fun ht h ↦ ?_⟩
  induction h using MulOpposite.rec' with | h h =>
  simpa only [← op_mul, counit_op, op_smul] using congrArg op (ht h)

/-- Right integrals in `Hᵐᵒᵖ` correspond to left integrals in `H`. -/
@[simp]
theorem op_mem_rightIntegral_iff {t : H} :
    op t ∈ rightIntegral R Hᵐᵒᵖ ↔ t ∈ leftIntegral R H := by
  simp only [mem_rightIntegral_iff, mem_leftIntegral_iff]
  refine ⟨fun ht h ↦ op_injective (by
    simpa only [← op_mul, counit_op, op_smul] using ht (op h)), fun ht h ↦ ?_⟩
  induction h using MulOpposite.rec' with | h h =>
  simpa only [← op_mul, counit_op, op_smul] using congrArg op (ht h)

end MulOpposite

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
