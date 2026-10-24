/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Renorming a unital algebra by left multiplication

The left regular representation identifies a unital normed algebra `A` with a subalgebra of
`A →L[𝕜] A`. Its inherited operator norm is submultiplicative and satisfies
`‖a‖ / ‖1‖ ≤ ‖a‖_* ≤ ‖a‖`. Thus this subalgebra realizes an equivalent algebra norm,
with identity norm one whenever `A` is nonzero. Completeness is preserved.

`LeftRegularRenorm` is this range with its inherited norm; `leftRegularRenormEquiv` is the
bounded algebra equivalence. Its inverse evaluates a multiplication operator at `1`.
No normalization of the original identity norm is required.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The construction uses Mathlib's `ContinuousLinearMap.mul`, `AlgEquiv.ofLeftInverse`, and
  the inherited normed-algebra structure on a subalgebra of bounded operators.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The unital left regular representation in bounded operators, sending `a` to `x ↦ a * x`. -/
def leftRegular : A →ₐ[𝕜] (A →L[𝕜] A) :=
  AlgHom.ofLinearMap (mul 𝕜 A).toLinearMap
    (by ext x; simp) (map_mul (NonUnitalAlgHom.Lmul 𝕜 A))

/-- The left regular representation acts by left multiplication. -/
@[simp]
theorem leftRegular_apply (a x : A) : leftRegular 𝕜 A a x = a * x := (rfl)

/-- A unital normed algebra with the equivalent operator norm of left multiplication.
It is realized as the range of its left regular representation. -/
abbrev LeftRegularRenorm := (leftRegular 𝕜 A).range

private def leftRegularAlgEquiv : A ≃ₐ[𝕜] LeftRegularRenorm 𝕜 A :=
  AlgEquiv.ofLeftInverse (g := fun T : A →L[𝕜] A ↦ T 1) (fun a ↦ by simp)

private theorem coe_leftRegularAlgEquiv (a : A) :
    (leftRegularAlgEquiv 𝕜 A a : A →L[𝕜] A) = mul 𝕜 A a := (rfl)

private theorem leftRegularAlgEquiv_symm_apply (T : LeftRegularRenorm 𝕜 A) :
    (leftRegularAlgEquiv 𝕜 A).symm T = (T : A →L[𝕜] A) 1 := (rfl)

/-- The canonical bounded algebra equivalence to the left multiplication renorming.
Its forward map is contractive and its inverse is bounded by the original norm of `1`. -/
def leftRegularRenormEquiv : A ≃A[𝕜] LeftRegularRenorm 𝕜 A where
  __ := leftRegularAlgEquiv 𝕜 A
  continuous_toFun := continuous_induced_rng.mpr (by
    exact (mul 𝕜 A).continuous.congr fun a ↦ (coe_leftRegularAlgEquiv 𝕜 A a).symm)
  continuous_invFun := by
    exact ((apply 𝕜 A (1 : A)).continuous.comp continuous_subtype_val).congr
      (fun T ↦ (leftRegularAlgEquiv_symm_apply 𝕜 A T).symm)

/-- The renorming equivalence sends an element to its left multiplication operator. -/
@[simp]
theorem leftRegularRenormEquiv_apply (a : A) :
    (leftRegularRenormEquiv 𝕜 A a : A →L[𝕜] A) = mul 𝕜 A a := (rfl)

/-- The inverse renorming equivalence evaluates an operator at the identity. -/
@[simp]
theorem leftRegularRenormEquiv_symm_apply (T : LeftRegularRenorm 𝕜 A) :
    (leftRegularRenormEquiv 𝕜 A).symm T = (T : A →L[𝕜] A) 1 := (rfl)

/-- Left multiplication renorming does not increase the norm. -/
theorem norm_leftRegularRenormEquiv_le (a : A) :
    ‖leftRegularRenormEquiv 𝕜 A a‖ ≤ ‖a‖ := by
  simpa only [AddSubgroupClass.coe_norm, leftRegularRenormEquiv_apply] using
    opNorm_mul_apply_le 𝕜 A a

/-- The inverse renorming has bound given by the original norm of the identity. -/
theorem norm_leftRegularRenormEquiv_symm_le (T : LeftRegularRenorm 𝕜 A) :
    ‖(leftRegularRenormEquiv 𝕜 A).symm T‖ ≤ ‖(1 : A)‖ * ‖T‖ := by
  rw [leftRegularRenormEquiv_symm_apply, mul_comm]
  exact (T : A →L[𝕜] A).le_opNorm 1

/-- The lower comparison bound for the left multiplication norm, without normalizing `‖1‖`. -/
theorem div_norm_one_le_norm_leftRegularRenormEquiv [Nontrivial A] (a : A) :
    ‖a‖ / ‖(1 : A)‖ ≤ ‖leftRegularRenormEquiv 𝕜 A a‖ := by
  rw [div_le_iff₀ (norm_pos_iff.mpr one_ne_zero), mul_comm]
  simpa only [ContinuousAlgEquiv.symm_apply_apply] using
    norm_leftRegularRenormEquiv_symm_le 𝕜 A (leftRegularRenormEquiv 𝕜 A a)

/-- Left multiplication operators form a closed subalgebra, even before assuming completeness. -/
theorem isClosed_leftRegularRenorm :
    IsClosed (LeftRegularRenorm 𝕜 A : Set (A →L[𝕜] A)) := by
  have hset : (LeftRegularRenorm 𝕜 A : Set (A →L[𝕜] A)) =
      {T | mul 𝕜 A (T 1) = T} := by
    ext T
    constructor
    · rintro ⟨a, rfl⟩
      ext x
      simp
    · intro h
      exact ⟨T 1, h⟩
  rw [hset]
  exact isClosed_eq ((mul 𝕜 A).continuous.comp (apply 𝕜 A (1 : A)).continuous) continuous_id

/-- The left multiplication norm is complete whenever the original norm is complete. -/
instance [CompleteSpace A] : CompleteSpace (LeftRegularRenorm 𝕜 A) :=
  (isClosed_leftRegularRenorm 𝕜 A).completeSpace_coe

end TauCeti
