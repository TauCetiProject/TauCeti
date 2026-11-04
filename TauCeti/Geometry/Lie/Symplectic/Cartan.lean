/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Cartan
public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Cartan
public import TauCeti.Analysis.Matrix.Normed

/-!
# Smoothness and differential of the symplectic involution

The symplectic inverse-transpose involution is inner, hence smooth for every Lie-group
structure on the symplectic group. In particular this applies to the embedded structure
supplied by the closed-subgroup theorem. Its ambient extension is conjugation by `J` on
the general linear group. The differential of this extension at the identity restricts
to negative transpose on `LieAlgebra.Symplectic.sp`, the symplectic Lie algebra.

We use `TauCeti.Lie.conjDiffeomorph` for smoothness and
`TauCeti.Lie.tangentAd_units` for the differential in matrix coordinates.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition.
-/

public section

noncomputable section

open Manifold Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace TauCeti.GLSymplectic

variable {l : Type*} [Fintype l] [DecidableEq l]

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace (GLSymplectic l ℝ)]
  [ChartedSpace H (GLSymplectic l ℝ)] [LieGroup I ∞ (GLSymplectic l ℝ)]

/-- The inverse-transpose involution is smooth in any Lie-group structure on the
real symplectic group. -/
theorem contMDiff_cartanInvolution :
    ContMDiff I I ∞ (cartanInvolution : GLSymplectic l ℝ → GLSymplectic l ℝ) := by
  exact ((Lie.conjDiffeomorph (I := I) (n := ∞) (symJ l ℝ)).contMDiff).congr
    fun g ↦ (cartanInvolution_apply g).trans
      (Lie.conjDiffeomorph_apply (I := I) (n := ∞) _ g).symm

end Smooth

-- Use the operator-norm matrix topology for the general linear Lie group.
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- In ambient matrix coordinates the differential at the identity of conjugation by `J`
restricts to the symplectic Lie involution `X ↦ -Xᵀ`. This conjugation extends the
symplectic inverse-transpose involution. -/
theorem mfderiv_conj_symJ_one_apply (X : LieAlgebra.Symplectic.sp l ℝ) :
    (show Matrix (l ⊕ l) (l ⊕ l) ℝ from
      mfderiv 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ) 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (fun g : GL (l ⊕ l) ℝ ↦
        (symJ l ℝ : GL (l ⊕ l) ℝ) * g * (symJ l ℝ : GL (l ⊕ l) ℝ)⁻¹)
      1 (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)) =
        (LieAlgebra.Symplectic.cartanInvolution l ℝ X : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by
  -- For matrix units the tangent model is the matrix algebra. Expose that identification
  -- explicitly when passing the matrix to the abstract differential API.
  have hd := Lie.adjointContinuousLinearMap_apply
    (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ)) (symJ l ℝ : GL (l ⊕ l) ℝ)
    ((X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
      GroupLieAlgebra 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ) (GL (l ⊕ l) ℝ))
  have ht := Lie.tangentAd_apply
    (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ)) (symJ l ℝ : GL (l ⊕ l) ℝ)
    ((X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
      GroupLieAlgebra 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ) (GL (l ⊕ l) ℝ))
  have he : (fun g : GL (l ⊕ l) ℝ ↦
      (symJ l ℝ : GL (l ⊕ l) ℝ) * g * (symJ l ℝ : GL (l ⊕ l) ℝ)⁻¹) =
      Lie.conjDiffeomorph (I := 𝓘(ℝ, Matrix (l ⊕ l) (l ⊕ l) ℝ)) (n := 1)
        (symJ l ℝ : GL (l ⊕ l) ℝ) := by
    funext g
    exact (Lie.conjDiffeomorph_apply _ g).symm
  rw [he]
  have h := Lie.tangentAd_units (symJ l ℝ : GL (l ⊕ l) ℝ)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ)
  simp only [coe_symJ, coe_units_inv] at h
  have hc := LieAlgebra.Symplectic.J_conj_eq_neg_transpose X.property
  rw [← LieAlgebra.Symplectic.coe_cartanInvolution] at hc
  exact hd.symm.trans (ht.symm.trans (h.trans hc))

end TauCeti.GLSymplectic
