/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialOrthogonal
public import TauCeti.Geometry.Lie.Exponential.OneParameter
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special
import TauCeti.LinearAlgebra.Matrix.Alternating.Basic
import TauCeti.SetTheory.Cardinal.Finite

/-!
# The Lie algebra of the special orthogonal group

The special orthogonal group `SO(n) = Matrix.specialOrthogonalGroup n ℝ` is a Lie group, with the
native structure of the special unitary group `Matrix.specialUnitaryGroup n ℝ`
(`TauCeti.Geometry.Manifold.Instances.Unitary.Special`), embedded in the matrices. This file
identifies its Lie algebra with the orthogonal Lie algebra `so(n) = LieAlgebra.Orthogonal.so n ℝ`
of skew-symmetric matrices: the differential at the identity of the inclusion
`SO(n) → Matrix n n ℝ` is a linear isomorphism onto `so(n)`
(`TauCeti.specialOrthogonalLieAlgebraEquiv`).

* It takes values in `so(n)`, because `SO(n)` lies in the orthogonal group, whose Lie algebra
  consists of skew-adjoint elements
  (`Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint`): differentiating `Aᵀ A = 1` at
  `A = 1` gives `Xᵀ + X = 0`.
* It is injective, because the inclusion is an immersion
  (`Matrix.specialUnitaryGroup.isImmersion_val`).
* It is surjective: a skew-symmetric matrix `X` is the velocity at `t = 0` of the smooth curve
  `t ↦ exp (t X)`, which stays in `SO(n)` (`Matrix.exp_mem_specialOrthogonalGroup_of_mem_so`).

Only this vector-space identification is constructed here; compatibility with the Lie brackets is
not proved.

As for the special unitary group, matrices carry the `ℓ²` operator norm: the statements are made
with `open scoped Matrix.Norms.L2Operator` and the local instance `Matrix.l2OpNormedAlgebraReal`.

## Main declarations

* `TauCeti.specialOrthogonalLieAlgebraEquiv`: the Lie algebra of `SO(n)` is linearly isomorphic to
  `so(n)`, by the differential of the inclusion at the identity.
* `TauCeti.finrank_specialOrthogonalLieAlgebra`: the dimension of the Lie algebra of `SO(n)`
  is the number of strictly upper-triangular entries.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Sections 3.3 and 3.4 (the Lie algebras of the matrix Lie groups `O(n)` and `SO(n)`).
-/

public section

noncomputable section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The differential at the identity of the inclusion of `SO(n)` into the matrices takes values
in the skew-symmetric matrices `so(n)`. -/
theorem mvfderiv_specialOrthogonalGroup_val_mem_so
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
        (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 ξ ∈
      LieAlgebra.Orthogonal.so n ℝ := by
  -- The inclusion factors through the orthogonal group `unitary (Matrix n n ℝ)`, whose Lie algebra
  -- consists of skew-adjoint matrices.
  let ι := Submonoid.inclusion
    (Matrix.specialUnitaryGroup_le_unitaryGroup (n := n) (α := ℝ))
  have hcomp : (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) =
      (Subtype.val : unitary (Matrix n n ℝ) → Matrix n n ℝ) ∘ ι := rfl
  have hι : MDifferentiableAt (Matrix.specialUnitaryGroup.model n ℝ)
      (Unitary.model (Matrix n n ℝ)) ι 1 :=
    Matrix.specialUnitaryGroup.isSmoothEmbedding_inclusion_unitaryGroup.contMDiff
      |>.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (Unitary.model (Matrix n n ℝ)) 𝓘(ℝ, Matrix n n ℝ)
      (Subtype.val : unitary (Matrix n n ℝ) → Matrix n n ℝ) 1 :=
    Unitary.contMDiff_val.mdifferentiableAt (by simp)
  rw [hcomp, mvfderiv_apply_eq_mfderiv_apply, mfderiv_comp_of_eq hval hι (map_one ι)]
  exact (Matrix.mem_so_iff_mem_skewAdjoint _).2
    (Unitary.tangentSpaceCastModel_mfderiv_val_mem_skewAdjoint _)

variable (n) in
/-- The differential at the identity of the inclusion `SO(n) → Matrix n n ℝ`, with values in
`so(n)`. -/
private def specialOrthogonalLieAlgebraMap :
    GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ) (Matrix.specialOrthogonalGroup n ℝ) →ₗ[ℝ]
      LieAlgebra.Orthogonal.so n ℝ :=
  LinearMap.codRestrict (LieAlgebra.Orthogonal.so n ℝ).toSubmodule
    (mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
      (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1).toLinearMap
    mvfderiv_specialOrthogonalGroup_val_mem_so

private theorem coe_specialOrthogonalLieAlgebraMap_apply
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    (specialOrthogonalLieAlgebraMap n ξ : Matrix n n ℝ) =
      mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
        (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 ξ := by
  rw [specialOrthogonalLieAlgebraMap, LinearMap.codRestrict_apply]
  rfl

private theorem injective_specialOrthogonalLieAlgebraMap :
    Function.Injective (specialOrthogonalLieAlgebraMap n) := by
  intro ξ η h
  have h' := congrArg (fun A : LieAlgebra.Orthogonal.so n ℝ ↦ (A : Matrix n n ℝ)) h
  -- `h'` says that the differentials of the inclusion at `1` agree on `ξ` and `η`.
  exact (Matrix.specialUnitaryGroup.isImmersion_val.isImmersionAt 1).mfderiv_injective (by simp) h'

private theorem surjective_specialOrthogonalLieAlgebraMap :
    Function.Surjective (specialOrthogonalLieAlgebraMap n) := by
  rintro ⟨A, hA⟩
  -- The exponential line of `A` is a smooth curve in `SO(n)` through `1` with velocity `A`.
  let γ : ℝ → Matrix.specialOrthogonalGroup n ℝ := fun t ↦
    ⟨exp (t • A), Matrix.exp_mem_specialOrthogonalGroup_of_mem_so _
      ((LieAlgebra.Orthogonal.so n ℝ).smul_mem t hA)⟩
  have hγ0 : γ 0 = 1 := Subtype.ext (by simp [γ])
  have hγs : ContMDiff 𝓘(ℝ) (Matrix.specialUnitaryGroup.model n ℝ) ∞ γ :=
    Matrix.specialUnitaryGroup.contMDiff_iff.2 ((contDiff_exp_smul A).of_le le_top).contMDiff
  have hγ : MDifferentiableAt 𝓘(ℝ) (Matrix.specialUnitaryGroup.model n ℝ) γ 0 :=
    hγs.mdifferentiableAt (by simp)
  have hval : MDifferentiableAt (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ)
      (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 :=
    Matrix.specialUnitaryGroup.contMDiff_val.mdifferentiableAt (by simp)
  have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, Matrix n n ℝ) (Subtype.val ∘ γ) 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight A) := by
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    rw [zero_smul, exp_zero, one_mul] at h
    exact h.hasFDerivAt.hasMFDerivAt
  -- The chain rule along `Subtype.val ∘ γ = fun t ↦ exp (t • A)`, evaluated on the unit vector.
  have h1 := DFunLike.congr_fun ((mfderiv_comp_of_eq hval hγ hγ0).symm.trans hd.mfderiv) (1 : ℝ)
  -- The differential of the inclusion is taken at `γ 0`, which is `1`; at `1` the map is its
  -- codomain restriction to `so(n)`.
  have h2 : ∀ e : Matrix.specialOrthogonalGroup n ℝ, e = 1 →
      ∀ v, mfderiv (Matrix.specialUnitaryGroup.model n ℝ) 𝓘(ℝ, Matrix n n ℝ) Subtype.val e v =
        (specialOrthogonalLieAlgebraMap n v : Matrix n n ℝ) := by
    rintro e rfl v
    rw [coe_specialOrthogonalLieAlgebraMap_apply, mvfderiv_apply_eq_mfderiv_apply]
  refine ⟨mfderiv 𝓘(ℝ) (Matrix.specialUnitaryGroup.model n ℝ) γ 0 (1 : ℝ), Subtype.ext ?_⟩
  rw [← h2 _ hγ0]
  -- Both sides of `h1` evaluate by definition: `(L ∘ M) 1 = L (M 1)` and `(t ↦ t • A) 1 = 1 • A`.
  exact h1.trans (one_smul ℝ A)

private theorem bijective_specialOrthogonalLieAlgebraMap :
    Function.Bijective (specialOrthogonalLieAlgebraMap n) :=
  ⟨injective_specialOrthogonalLieAlgebraMap, surjective_specialOrthogonalLieAlgebraMap⟩

variable (n) in
/-- **The Lie algebra of the special orthogonal group is linearly isomorphic to `so(n)`.** The
differential at the identity of the inclusion of `SO(n) = Matrix.specialOrthogonalGroup n ℝ` into
the matrices is a linear isomorphism from its Lie algebra onto the skew-symmetric matrices
`so(n) = LieAlgebra.Orthogonal.so n ℝ`. This is an identification of vector spaces; it is not shown
here to preserve the brackets. -/
def specialOrthogonalLieAlgebraEquiv :
    GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ) (Matrix.specialOrthogonalGroup n ℝ) ≃ₗ[ℝ]
      LieAlgebra.Orthogonal.so n ℝ :=
  LinearEquiv.ofBijective (specialOrthogonalLieAlgebraMap n)
    bijective_specialOrthogonalLieAlgebraMap

/-- The element of `so(n)` attached to `ξ` is the differential of the inclusion
`SO(n) → Matrix n n ℝ` at the identity, applied to `ξ`. -/
@[simp]
theorem coe_specialOrthogonalLieAlgebraEquiv_apply
    (ξ : GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    (specialOrthogonalLieAlgebraEquiv n ξ : Matrix n n ℝ) =
      mvfderiv (Matrix.specialUnitaryGroup.model n ℝ)
        (Subtype.val : Matrix.specialOrthogonalGroup n ℝ → Matrix n n ℝ) 1 ξ := by
  rw [specialOrthogonalLieAlgebraEquiv, LinearEquiv.ofBijective_apply,
    coe_specialOrthogonalLieAlgebraMap_apply]

/-- The dimension of the real special orthogonal Lie algebra counts the strictly
upper-triangular entries of a skew-symmetric matrix. -/
theorem finrank_specialOrthogonalLieAlgebra :
    Module.finrank ℝ (GroupLieAlgebra (Matrix.specialUnitaryGroup.model n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) = (Fintype.card n).choose 2 := by
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  let e : LieAlgebra.Orthogonal.so n ℝ ≃ Matrix.skewAddSubgroup n ℝ :=
    Equiv.subtypeEquiv (Equiv.refl _) fun A ↦
      (LieAlgebra.Orthogonal.mem_so n ℝ A).trans (Matrix.mem_skewAddSubgroup A).symm
  let c : LieAlgebra.Orthogonal.so n ℝ ≃ₗ[ℝ] ({p : n × n // p.1 < p.2} → ℝ) :=
    { toEquiv := e.trans (Matrix.skewStrictUpperAddEquiv (by intro x hx; linarith)).toEquiv
      map_add' := by intro A B; ext p; simp [e]
      map_smul' := by intro a A; ext p; simp [e] }
  calc
    _ = Module.finrank ℝ ({p : n × n // p.1 < p.2} → ℝ) :=
      ((specialOrthogonalLieAlgebraEquiv n).trans c).finrank_eq
    _ = (Fintype.card n).choose 2 := by
      rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
        Fintype.natCard_subtype_lt]

end TauCeti
