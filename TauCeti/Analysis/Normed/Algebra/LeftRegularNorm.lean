/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Normalizing the identity by the left regular representation

A unital normed algebra is boundedly isomorphic to its left regular representation,
with norm `‖a‖_* = ‖ContinuousLinearMap.mul 𝕜 A a‖`. This norm is submultiplicative,
lies between `‖a‖ / ‖1‖` and `‖a‖`, and is complete when the original norm is complete.
For a nonzero algebra its identity has norm one. Thus norm-one constructions can be
applied after a bounded algebra equivalence, rather than imposing a normalization on
the original algebra. The equivalence is not in general an isometry.

`LeftRegularNorm` is realized as a subalgebra of bounded operators, so its algebra and
norm structures are inherited rather than reconstructed on the original carrier.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The construction uses Mathlib's `NonUnitalAlgHom.Lmul`, `AlgEquiv.ofInjective`,
  and the operator norm on `ContinuousLinearMap`.
-/

public section

namespace TauCeti

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The left regular renorming of a unital normed algebra, realized as the range of
its left regular representation with the inherited operator norm. -/
noncomputable abbrev LeftRegularNorm := (AlgHom.Lmul 𝕜 A).range

namespace LeftRegularNorm

private noncomputable def algEquiv : A ≃ₐ[𝕜] LeftRegularNorm 𝕜 A :=
  AlgEquiv.ofInjective (AlgHom.Lmul 𝕜 A) (AlgHom.Lmul_injective 𝕜 A)

private theorem algEquiv_apply_coe (a : A) :
    (algEquiv 𝕜 A a : A →L[𝕜] A) = ContinuousLinearMap.mul 𝕜 A a := by
  simp only [algEquiv, AlgEquiv.ofInjective_apply, AlgHom.coe_Lmul]

private theorem norm_algEquiv_le (a : A) : ‖algEquiv 𝕜 A a‖ ≤ ‖a‖ := by
  rw [AddSubgroupClass.coe_norm, algEquiv_apply_coe]
  exact ContinuousLinearMap.opNorm_mul_apply_le 𝕜 A a

private theorem norm_algEquiv_symm_le (x : LeftRegularNorm 𝕜 A) :
    ‖(algEquiv 𝕜 A).symm x‖ ≤ ‖x‖ * ‖(1 : A)‖ := by
  calc
    ‖(algEquiv 𝕜 A).symm x‖ ≤
        ‖ContinuousLinearMap.mul 𝕜 A ((algEquiv 𝕜 A).symm x)‖ * ‖(1 : A)‖ :=
      ContinuousLinearMap.norm_le_opNorm_mul_apply_mul_norm_one _
    _ = ‖x‖ * ‖(1 : A)‖ := by
      rw [← algEquiv_apply_coe, AlgEquiv.apply_symm_apply, ← AddSubgroupClass.coe_norm]

/-- The original algebra and its left regular renorming are boundedly algebra isomorphic.
The forward map is contractive and the inverse is bounded by the original norm of one. -/
noncomputable def equiv : A ≃A[𝕜] LeftRegularNorm 𝕜 A :=
  { algEquiv 𝕜 A with
    continuous_toFun := AddMonoidHomClass.continuous_of_bound (algEquiv 𝕜 A) 1 fun a ↦ by
      simpa only [one_mul] using norm_algEquiv_le 𝕜 A a
    continuous_invFun := AddMonoidHomClass.continuous_of_bound
      (algEquiv 𝕜 A).symm ‖(1 : A)‖ fun x ↦ by
        simpa only [mul_comm] using norm_algEquiv_symm_le 𝕜 A x }

-- Adding continuity leaves the underlying algebra equivalence unchanged.
private theorem equiv_toAlgEquiv : (equiv 𝕜 A).toAlgEquiv = algEquiv 𝕜 A := rfl

/-- The equivalence sends an element to its bounded left multiplication operator. -/
@[simp]
theorem equiv_apply_coe (a : A) :
    (equiv 𝕜 A a : A →L[𝕜] A) = ContinuousLinearMap.mul 𝕜 A a := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, equiv_toAlgEquiv]
  exact algEquiv_apply_coe 𝕜 A a

/-- The original element corresponding to an operator in the renormed algebra is its
value at the original identity. -/
@[simp]
theorem equiv_symm_apply (x : LeftRegularNorm 𝕜 A) :
    (equiv 𝕜 A).symm x = (x : A →L[𝕜] A) 1 := by
  have h := DFunLike.congr_fun (equiv_apply_coe 𝕜 A ((equiv 𝕜 A).symm x)) (1 : A)
  simpa using h.symm

/-- The renormed norm is the operator norm of left multiplication in the original algebra. -/
theorem norm_equiv (a : A) :
    ‖equiv 𝕜 A a‖ = ‖ContinuousLinearMap.mul 𝕜 A a‖ :=
  congrArg norm (equiv_apply_coe 𝕜 A a)

/-- Left regular renorming does not increase norms. -/
theorem norm_equiv_le (a : A) : ‖equiv 𝕜 A a‖ ≤ ‖a‖ := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, equiv_toAlgEquiv]
  exact norm_algEquiv_le 𝕜 A a

/-- The original norm is controlled by the left regular norm with comparison constant `‖1‖`. -/
theorem norm_le_norm_equiv_mul_norm_one (a : A) :
    ‖a‖ ≤ ‖equiv 𝕜 A a‖ * ‖(1 : A)‖ := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, equiv_toAlgEquiv]
  simpa only [AlgEquiv.symm_apply_apply] using
    norm_algEquiv_symm_le 𝕜 A (algEquiv 𝕜 A a)

/-- The lower comparison in division form, including for the zero algebra. -/
theorem div_norm_one_le_norm_equiv (a : A) :
    ‖a‖ / ‖(1 : A)‖ ≤ ‖equiv 𝕜 A a‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _)
    (norm_le_norm_equiv_mul_norm_one 𝕜 A a)

/-- The equivalent left regular norm is complete whenever the original norm is complete. -/
instance [CompleteSpace A] : CompleteSpace (LeftRegularNorm 𝕜 A) := by
  -- Fix the inherited normed structure before synthesizing the uniform additive group.
  let : NormedRing (LeftRegularNorm 𝕜 A) := inferInstance
  exact (completeSpace_congr (e := (equiv 𝕜 A).toEquiv)
    (ContinuousAlgEquiv.isUniformEmbedding (E₁ := A) (E₂ := LeftRegularNorm 𝕜 A)
      (equiv 𝕜 A))).1 inferInstance

end LeftRegularNorm

end TauCeti
