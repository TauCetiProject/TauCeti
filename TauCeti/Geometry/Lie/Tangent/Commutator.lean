/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Related
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lie bracket of a matrix group is the commutator

Let `G` be a real Lie group and `R` a complete normed real algebra, for instance a matrix algebra,
and let `φ : G →* R` be a `C²` map with `φ (g * h) = φ g * φ h` and `φ 1 = 1`, such as the
inclusion of a matrix Lie group into the matrices. This file proves that the differential of `φ`
at the identity carries the Lie bracket of the Lie algebra `GroupLieAlgebra I G` to the
commutator of `R`:

`dφ_1 ⁅ξ, η⁆ = dφ_1 ξ * dφ_1 η - dφ_1 η * dφ_1 ξ`

(`MonoidHom.mvfderiv_lie`). So every identification of the Lie algebra of a matrix group with a
Lie algebra of matrices by the differential of the inclusion preserves brackets.

The proof uses the naturality of the Lie bracket of vector fields under related vector fields
(`TauCeti.mfderiv_mlieBracket_of_eventually_related`). Differentiating `φ (g * h) = φ g * φ h` in
`h` at `h = 1` shows that `φ` relates the left-invariant vector field of `ξ` on `G` to the linear
vector field `M ↦ M * A` on `R`, with `A = dφ_1 ξ`. The bracket of the linear vector fields
`M ↦ M * A` and `M ↦ M * B` is `M ↦ M * (A * B - B * A)`, which is `A * B - B * A` at `M = 1`.

## Main results

* `MonoidHom.mfderiv_mulInvariantVectorField`: `φ` relates the left-invariant vector field of `ξ`
  to the linear vector field `M ↦ M * dφ_1 ξ`.
* `MonoidHom.mvfderiv_lie`: the differential of `φ` at the identity carries the Lie bracket to
  the commutator.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Theorem 3.20 (the Lie algebra of a matrix Lie group is closed under the commutator, which is
  its bracket).
-/

public section

noncomputable section

open Manifold VectorField
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

namespace MonoidHom

/-- A differentiable multiplicative map `φ : G →* R` into a normed algebra relates the
left-invariant vector field of `ξ` to the linear vector field `M ↦ M * dφ_1 ξ`: its differential at
`g` sends `ξ^L g` to `φ g * dφ_1 ξ`. -/
theorem mfderiv_mulInvariantVectorField (φ : G →* R) (hφ : MDifferentiable I 𝓘(ℝ, R) φ)
    (ξ : GroupLieAlgebra I G) (g : G) :
    mfderiv I 𝓘(ℝ, R) φ g (mulInvariantVectorField ξ g) = φ g * mvfderiv I φ 1 ξ := by
  have hφd : ∀ x : G, MDifferentiableAt I 𝓘(ℝ, R) φ x := hφ
  -- Left translation by `g` on `G` becomes left multiplication by `φ g` on `R`.
  have hfun : (φ : G → R) ∘ (fun h : G ↦ g * h) =
      (ContinuousLinearMap.mul ℝ R (φ g) : R → R) ∘ φ := by
    funext h
    simp
  have hleft := mfderiv_comp (I := I) (I' := I) (I'' := 𝓘(ℝ, R)) (x := (1 : G))
    (g := (φ : G → R)) (f := fun h : G ↦ g * h) (by simpa using hφd g)
    ((contMDiffAt_mul_left (n := minSmoothness ℝ 3) (a := g)).mdifferentiableAt (by simp))
  have hright := mfderiv_comp (I := I) (I' := 𝓘(ℝ, R)) (I'' := 𝓘(ℝ, R)) (x := (1 : G))
    (g := (ContinuousLinearMap.mul ℝ R (φ g) : R → R)) (f := (φ : G → R))
    (ContinuousLinearMap.mul ℝ R (φ g)).mdifferentiableAt (hφd 1)
  have hcomp : mfderiv I 𝓘(ℝ, R) ((φ : G → R) ∘ (fun h : G ↦ g * h)) 1 =
      mfderiv I 𝓘(ℝ, R) ((ContinuousLinearMap.mul ℝ R (φ g) : R → R) ∘ φ) 1 := by
    rw [hfun]
  have h := hleft.symm.trans (hcomp.trans hright)
  rw [mul_one, ContinuousLinearMap.mfderiv_eq] at h
  -- Both sides of `h`, applied to `ξ`, are the two sides of the goal: `mulInvariantVectorField`
  -- and `mvfderiv` unfold to the differentials appearing in `h`.
  exact DFunLike.congr_fun h ξ

/-- **The bracket of a matrix Lie group is the commutator.** Let `φ : G →* R` be a `C²`
multiplicative map from a real Lie group into a complete normed algebra, such as the inclusion of a
matrix Lie group into the matrices. Its differential at the identity carries the Lie bracket of the
Lie algebra of `G` to the commutator of `R`: `dφ_1 ⁅ξ, η⁆ = ⁅dφ_1 ξ, dφ_1 η⁆`, where
`⁅A, B⁆ = A * B - B * A` (`Ring.lie_def`). -/
theorem mvfderiv_lie [CompleteSpace E] [CompleteSpace R] (φ : G →* R)
    (hφ : ContMDiff I 𝓘(ℝ, R) 2 φ) (ξ η : GroupLieAlgebra I G) :
    mvfderiv I φ 1 ⁅ξ, η⁆ = ⁅mvfderiv I φ 1 ξ, mvfderiv I φ 1 η⁆ := by
  have hφd : MDifferentiable I 𝓘(ℝ, R) φ := hφ.mdifferentiable (by norm_num)
  set A := mvfderiv I φ 1 ξ
  set B := mvfderiv I φ 1 η
  -- The linear vector fields `M ↦ M * A` and `M ↦ M * B` on `R`.
  let LA : R →L[ℝ] R := (ContinuousLinearMap.mul ℝ R).flip A
  let LB : R →L[ℝ] R := (ContinuousLinearMap.mul ℝ R).flip B
  let VA : Π M : R, TangentSpace 𝓘(ℝ, R) M := fun M ↦ LA M
  let VB : Π M : R, TangentSpace 𝓘(ℝ, R) M := fun M ↦ LB M
  have h := TauCeti.mfderiv_mlieBracket_of_eventually_related (n := 2) (y := (1 : G))
    (V' := VA) (W' := VB) hφ.contMDiffAt (by simp)
    (mdifferentiableAt_mulInvariantVectorField ξ) (mdifferentiableAt_mulInvariantVectorField η)
    (TauCeti.mdifferentiableAt_vectorSpace_iff_differentiableAt.2 LA.differentiableAt)
    (TauCeti.mdifferentiableAt_vectorSpace_iff_differentiableAt.2 LB.differentiableAt)
    (Filter.Eventually.of_forall fun g ↦ mfderiv_mulInvariantVectorField φ hφd ξ g)
    (Filter.Eventually.of_forall fun g ↦ mfderiv_mulInvariantVectorField φ hφd η g)
  -- On the vector space `R` the manifold bracket of the linear fields is the commutator.
  have hbr : mlieBracket 𝓘(ℝ, R) VA VB (φ 1) = A * B - B * A := by
    rw [mlieBracket_continuousLinearMap_model_space LA LB (φ 1)]
    simp only [LA, LB, map_one, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
      one_mul]
    -- The left side is a difference in the tangent space `TangentSpace 𝓘(ℝ, R) 1`, which is `R`.
    rfl
  rw [mvfderiv_apply_eq_mfderiv_apply, GroupLieAlgebra.bracket_def, h, hbr, Ring.lie_def]

end MonoidHom
