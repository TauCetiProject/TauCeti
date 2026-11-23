/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.Geometry.Lie.Subgroup.Unitary.TangentSpace
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# Nearest points and retractions onto a closed subgroup of the unitary group

Let `G` be a closed subgroup of `U(n)`, a compact submanifold of the real inner product space of
`n × n` complex matrices with the Frobenius inner product `⟪A, B⟫ = Re tr (Aᴴ B)`, with tangent
space `g 𝔤` at `g ∈ G` (`ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace`). This file proves
the first-order facts about nearest points of `G` and retractions onto `G`, which identify the
derivative of the nearest-point retraction `π_G` at points of `G`:

* if `g ∈ G` is, locally, a nearest point of `G` to a matrix `M`, the residual `M - g` is
  orthogonal to `g 𝔤` (`ClosedSubgroup.inner_sub_eq_zero_of_isLocalMinOn`);
* a map `r` from matrices to matrices that is the identity on `G` has derivative the identity on
  `g 𝔤` (`ClosedSubgroup.fderiv_apply_eq_self_of_mem_matrixTangentSpace`);
* if moreover `r (g + t v) = g` for every normal vector `v` and small `t`, as for the nearest-point
  retraction along short normal segments, its derivative at `g` is the orthogonal projection onto
  `g 𝔤` (`ClosedSubgroup.fderiv_eq_starProjection_matrixTangentSpace`).

These statements are about maps of matrices and the subset `G`, so they apply to any differentiable
retraction onto `G`, in particular to the smooth nearest-point retraction that the tubular
neighbourhood theorem provides on a neighbourhood of `G`.

The Frobenius inner product is a scoped instance; this file opens `Matrix.Norms.Frobenius`.

## References

* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 3 (the derivative
  of the nearest-point projection onto `G`).
-/

public section

noncomputable section

open Filter NormedSpace Set
open scoped Matrix Topology InnerProductSpace

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}

section PosTangentCone

open scoped Matrix.Norms.Operator

/-- Every vector `g X`, `X ∈ 𝔤`, of the tangent space at `g` is a velocity of a curve in `G`
starting at `g`, so it lies in the positive tangent cone of `G` at `g`. -/
theorem mem_posTangentConeAt_of_mem_matrixTangentSpace {g : G} {V : Matrix n n 𝕜}
    (hV : V ∈ G.matrixTangentSpace g) :
    V ∈ posTangentConeAt (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      (g : Matrix n n 𝕜) := by
  have hX := mem_matrixTangentSpace_iff.mp hV
  set X := star (g : Matrix n n 𝕜) * V
  have hVX : V = (g : Matrix n n 𝕜) * X := by simp [X, ← mul_assoc]
  rw [hVX]
  -- The curve `t ↦ g exp (t X)` stays in `G` and has velocity `g X` at `t = 0`.
  have hγ := (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul (g : Matrix n n 𝕜)
  simp only [zero_smul, exp_zero, one_mul] at hγ
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g : Matrix n n 𝕜) * exp (t • X) ∈
      ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G := by
    refine Eventually.of_forall fun t ↦ ?_
    obtain ⟨h, hh, hht⟩ := mem_matrixLieAlgebra_iff.mp ((LieSubalgebra.mem_toSubmodule _).mp hX) t
    exact ⟨g * h, mul_mem g.property hh, by simp [hht]⟩
  have h : (g : Matrix n n 𝕜) * X ∈ posTangentConeAt
      (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      ((g : Matrix n n 𝕜) * exp ((0 : ℝ) • X)) :=
    hγ.hasDerivWithinAt.mem_posTangentConeAt hmem.frequently
  simpa using h

end PosTangentCone

open scoped Matrix.Norms.Frobenius

/-- **First variation of the distance to `G`.** If `g ∈ G` is, locally in `G`, a nearest point of
`G` to `M`, the residual `M - g` is orthogonal (for the Frobenius inner product) to the tangent
space `g 𝔤` of `G` at `g`. -/
theorem inner_sub_eq_zero_of_isLocalMinOn {M : Matrix n n 𝕜} {g : G}
    (hmin : IsLocalMinOn (dist M) (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      (g : Matrix n n 𝕜))
    {V : Matrix n n 𝕜} (hV : V ∈ G.matrixTangentSpace g) :
    ⟪M - g, V⟫_ℝ = 0 := by
  -- The squared distance `A ↦ ‖A - M‖²` also has a local minimum at `g` on `G`.
  have hmin2 : IsLocalMinOn (fun A : Matrix n n 𝕜 ↦ ‖A - M‖ ^ 2)
      (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) (g : Matrix n n 𝕜) :=
    Filter.Eventually.mono hmin fun A (hA : dist M g ≤ dist M A) ↦ by
      simp only [← dist_eq_norm, dist_comm _ M]
      exact pow_le_pow_left₀ dist_nonneg hA 2
  have hd := ((hasFDerivAt_id (g : Matrix n n 𝕜)).sub_const M).norm_sq
  have h0 := hmin2.hasFDerivWithinAt_eq_zero hd.hasFDerivWithinAt
    (mem_posTangentConeAt_of_mem_matrixTangentSpace hV)
    (mem_posTangentConeAt_of_mem_matrixTangentSpace (neg_mem hV))
  simp only [smul_apply, id_eq, nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] at h0
  rw [← neg_sub, inner_neg_left, neg_eq_zero]
  exact h0

/-- **A retraction onto `G` is the identity on tangent vectors.** If `r` is differentiable at
`g ∈ G` and fixes every point of `G`, its derivative at `g` is the identity on `g 𝔤`. -/
theorem fderiv_apply_eq_self_of_mem_matrixTangentSpace {r : Matrix n n 𝕜 → Matrix n n 𝕜} {g : G}
    (hr : DifferentiableAt ℝ r g) (hrG : ∀ h ∈ G, r h = h) {V : Matrix n n 𝕜}
    (hV : V ∈ G.matrixTangentSpace g) :
    fderiv ℝ r g V = V := by
  set S := ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G
  have hid : HasFDerivWithinAt r (ContinuousLinearMap.id ℝ (Matrix n n 𝕜)) S g :=
    (hasFDerivWithinAt_id _ S).congr (fun _ ⟨h, hh, hA⟩ ↦ hA ▸ hrG h hh) (hrG g g.property)
  refine hr.hasFDerivAt.hasFDerivWithinAt.unique_on hid ?_
  rw [tangentConeAt_eq_matrixTangentSpace]
  exact hV

/-- A map that is constant along the line through `x` in the direction `v`, near `x`, has
derivative zero in the direction `v`. -/
private theorem fderiv_apply_eq_zero_of_eventually_add_smul {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {r : E → F} {x v : E}
    (hr : DifferentiableAt ℝ r x) (hv : ∀ᶠ t in 𝓝 (0 : ℝ), r (x + t • v) = r x) :
    fderiv ℝ r x v = 0 := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hcomp : HasDerivAt (fun t : ℝ ↦ r (x + t • v)) (fderiv ℝ r x v) 0 := by
    have hr' : HasFDerivAt r (fderiv ℝ r x) (x + (0 : ℝ) • v) := by
      simpa using hr.hasFDerivAt
    exact hr'.comp_hasDerivAt (0 : ℝ) hline
  exact hcomp.unique ((hasDerivAt_const (0 : ℝ) (r x)).congr_of_eventuallyEq hv)

/-- **The derivative of a retraction onto `G` that is constant along normal segments.** If `r` is
differentiable at `g ∈ G`, fixes every point of `G`, and satisfies `r (g + t v) = g` for every
vector `v` orthogonal to `g 𝔤` and every small `t`, then its derivative at `g` is the orthogonal
projection onto `g 𝔤`. The nearest-point retraction onto `G` has these properties. -/
theorem fderiv_eq_starProjection_matrixTangentSpace {r : Matrix n n 𝕜 → Matrix n n 𝕜} {g : G}
    (hr : DifferentiableAt ℝ r g) (hrG : ∀ h ∈ G, r h = h)
    (hnormal : ∀ v ∈ (G.matrixTangentSpace g)ᗮ,
      ∀ᶠ t in 𝓝 (0 : ℝ), r ((g : Matrix n n 𝕜) + t • v) = g) :
    fderiv ℝ r g = (G.matrixTangentSpace g).starProjection := by
  refine ContinuousLinearMap.ext fun V ↦ ?_
  -- Split `V` into its tangential and normal parts.
  set T := G.matrixTangentSpace g
  have hT : T.starProjection V ∈ T := T.starProjection_apply_mem V
  have hN : V - T.starProjection V ∈ Tᗮ := T.sub_starProjection_mem_orthogonal V
  have hrg : r g = g := hrG g g.property
  have h0 : fderiv ℝ r g (V - T.starProjection V) = 0 :=
    fderiv_apply_eq_zero_of_eventually_add_smul hr (by
      filter_upwards [hnormal _ hN] with t ht using ht.trans hrg.symm)
  rw [map_sub, sub_eq_zero, fderiv_apply_eq_self_of_mem_matrixTangentSpace hr hrG hT] at h0
  exact h0

end ClosedSubgroup
