/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Inclusion
public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.Geometry.Manifold.Complex.SquaredDistance
public import TauCeti.Topology.Algebra.MvPolynomial.ZeroLocus

import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Smooth affine complete intersections

Let `p : ι → MvPolynomial σ 𝕜` be a finite family of polynomials over a complete nontrivially
normed field, and let `TauCeti.affineZeroLocus p ⊆ 𝕜^σ` be its common zero set. Suppose the
Jacobian matrix `(∂pᵢ/∂xⱼ)` of the family is surjective at every common zero, so that the zero set
is a smooth complete intersection. Then the zero set is a closed analytic submanifold of `𝕜^σ` of
dimension `|σ| - |ι|`:

* `TauCeti.affineZeroLocusChartedSpace` and `TauCeti.isManifold_affineZeroLocus`: the zero set,
  with its subspace topology, is a `C^r` manifold modelled on `Fin (|σ| - |ι|) → 𝕜` for every
  `r : ℕ∞ω`, with the implicit-function charts of the evaluation map;
* `TauCeti.contMDiff_coe_affineZeroLocus`, `TauCeti.injective_mfderiv_coe_affineZeroLocus` and
  `TauCeti.range_mfderiv_coe_affineZeroLocus`: its inclusion into `𝕜^σ` is analytic and an
  immersion, with tangent space at `x` the kernel of the Jacobian matrix at `x`.

The zero set is closed (`TauCeti.isClosed_affineZeroLocus`). The surjectivity hypothesis forces
the zero set to have codimension `|ι|`, so a smooth affine variety is covered only through a
defining family with as many equations as its codimension; a family with more equations than the
codimension never satisfies it.

Over `ℂ` this is the input to Milnor's theorem that a smooth affine algebraic variety of complex
dimension `n` has the homotopy type of a CW complex of dimension at most `n`, for smooth complete
intersections. The Euclidean squared distance `x ↦ ‖x - a‖²` from any point `a` restricts to a
proper function on the zero set (`TauCeti.isProperMap_norm_sq_sub_toLp_affineZeroLocus`), and
every critical point of this restriction has real Morse index at most the complex dimension
`|σ| - |ι|` (`TauCeti.manifoldMorseIndex_norm_sq_sub_toLp_affineZeroLocus_le`). The latter is the
Levi-form bound `TauCeti.manifoldMorseIndex_norm_sq_sub_comp_le` for a holomorphic immersion,
applied to the inclusion of the zero set.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorem 7.2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Corollary 5.14, for regular
  level sets.
-/

public section

open MvPolynomial Set
open scoped ContDiff Manifold

namespace TauCeti

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {σ ι : Type*} [Fintype σ]
  {p : ι → MvPolynomial σ 𝕜}

private theorem surjective_fderiv_eval_family_of_mem
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    ∀ x ∈ affineZeroLocus p,
      Function.Surjective (fderiv 𝕜 (fun y ↦ fun k ↦ eval y (p k)) x) :=
  fun x hx ↦ (surjective_fderiv_eval_family_iff p x).2 (hp x hx)

variable [Fintype ι]

private theorem index_fderiv_eval_family_of_mem
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    ∀ x ∈ affineZeroLocus p,
      ContinuousLinearMap.index (fderiv 𝕜 (fun y ↦ fun k ↦ eval y (p k)) x) =
        (Fintype.card σ - Fintype.card ι : ℕ) := by
  intro x hx
  have hs := surjective_fderiv_eval_family_of_mem hp x hx
  set T := fderiv 𝕜 (fun y ↦ fun k ↦ eval y (p k)) x
  rw [← ContinuousLinearMap.finrank_ker_eq_iff_index_eq T hs]
  -- Rank-nullity for the surjective derivative `𝕜^σ → 𝕜^ι`.
  have hrn := LinearMap.finrank_range_add_finrank_ker (T : (σ → 𝕜) →ₗ[𝕜] (ι → 𝕜))
  rw [LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hrn
  omega

variable [CompleteSpace 𝕜]

/-- **The charts of a smooth affine complete intersection.** If the Jacobian matrix of a
polynomial family is surjective at every common zero, the zero set is a charted space modelled on
`Fin (|σ| - |ι|) → 𝕜`, the charts being the implicit-function charts
`TauCeti.levelSetChartAt` of the evaluation map. -/
@[instance_reducible]
noncomputable def affineZeroLocusChartedSpace
    (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec) :
    ChartedSpace (Fin (Fintype.card σ - Fintype.card ι) → 𝕜) (affineZeroLocus p) :=
  levelSetChartedSpace (fun x _ ↦ (analyticOnNhd_eval_family p x (mem_univ x)).hasStrictFDerivAt)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (surjective_fderiv_eval_family_of_mem hp) (index_fderiv_eval_family_of_mem hp)

variable (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)

/-- **A smooth affine complete intersection is an analytic manifold.** If the Jacobian matrix of a
polynomial family is surjective at every common zero, the zero set is a `C^r` manifold of
dimension `|σ| - |ι|` for every `r`, including `r = ω`. -/
theorem isManifold_affineZeroLocus (r : ℕ∞ω) :
    letI := affineZeroLocusChartedSpace hp
    IsManifold 𝓘(𝕜, Fin (Fintype.card σ - Fintype.card ι) → 𝕜) r (affineZeroLocus p) :=
  isManifold_levelSet _ _ _ _ fun _ _ ↦ (analyticOnNhd_eval_family p).contDiff.contDiffAt

/-- The inclusion of a smooth affine complete intersection into `𝕜^σ` is `C^r` for every `r`,
including `r = ω`. -/
theorem contMDiff_coe_affineZeroLocus (r : ℕ∞ω) :
    letI := affineZeroLocusChartedSpace hp
    ContMDiff 𝓘(𝕜, Fin (Fintype.card σ - Fintype.card ι) → 𝕜) 𝓘(𝕜, σ → 𝕜) r
      (Subtype.val : affineZeroLocus p → σ → 𝕜) :=
  contMDiff_coe_levelSet _ _ _ _ fun _ _ ↦ (analyticOnNhd_eval_family p).contDiff.contDiffAt

/-- The inclusion of a smooth affine complete intersection into `𝕜^σ` is an immersion. -/
theorem injective_mfderiv_coe_affineZeroLocus (x : affineZeroLocus p) :
    letI := affineZeroLocusChartedSpace hp
    Function.Injective (mfderiv 𝓘(𝕜, Fin (Fintype.card σ - Fintype.card ι) → 𝕜) 𝓘(𝕜, σ → 𝕜)
      (Subtype.val : affineZeroLocus p → σ → 𝕜) x) :=
  injective_mfderiv_coe_levelSet _ _ _ _ x

/-- **The tangent space of a smooth affine complete intersection.** At a point `x` of the zero
set, the range of the differential of the inclusion is the kernel of the Jacobian matrix at `x`. -/
theorem range_mfderiv_coe_affineZeroLocus (x : affineZeroLocus p) :
    letI := affineZeroLocusChartedSpace hp
    (mfderiv 𝓘(𝕜, Fin (Fintype.card σ - Fintype.card ι) → 𝕜) 𝓘(𝕜, σ → 𝕜)
      (Subtype.val : affineZeroLocus p → σ → 𝕜) x).range =
      LinearMap.ker (jacobiMatrixAt p x).mulVecLin := by
  let _ := affineZeroLocusChartedSpace hp
  rw [← fderiv_eval_family]
  -- `(D z).ker` in `range_mfderiv_coe_levelSet` is dot notation for `LinearMap.ker` of the
  -- underlying linear map `(D z).toLinearMap`, which is exactly the rewritten right side.
  exact range_mfderiv_coe_levelSet _ _ _ _ x

end Field

section Complex

variable {σ ι : Type*} [Fintype σ] [Fintype ι] {p : ι → MvPolynomial σ ℂ}
  (hp : ∀ x ∈ affineZeroLocus p, Function.Surjective (jacobiMatrixAt p x).mulVec)

/-- **Milnor's index bound on a smooth affine complete intersection.** On the common zero set in
`ℂ^σ` of a polynomial family with surjective Jacobian at every common zero, every critical point of
the Euclidean squared distance from a point `a` has real Morse index at most the complex dimension
`|σ| - |ι|` of the zero set. -/
theorem manifoldMorseIndex_norm_sq_sub_toLp_affineZeroLocus_le (a : EuclideanSpace ℂ σ)
    (x : affineZeroLocus p)
    (hcrit : letI := affineZeroLocusChartedSpace hp
      mvfderiv 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) x = 0) :
    letI := affineZeroLocusChartedSpace hp
    manifoldMorseIndex 𝓘(ℝ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
        (fun y : affineZeroLocus p ↦ ‖WithLp.toLp 2 (y : σ → ℂ) - a‖ ^ 2) x ≤
      Fintype.card σ - Fintype.card ι := by
  let _ := affineZeroLocusChartedSpace hp
  have := isManifold_affineZeroLocus hp 2
  -- The Euclidean inclusion is the inclusion followed by the linear identification `toLp`.
  set e := (EuclideanSpace.equiv σ ℂ).symm
  have hcomp : (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) = e ∘ Subtype.val := by
    rw [PiLp.coe_symm_continuousLinearEquiv, Function.comp_def]
  have hval := contMDiff_coe_affineZeroLocus hp 2 x
  have hi : ContMDiffAt 𝓘(ℂ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
      𝓘(ℂ, EuclideanSpace ℂ σ) 2 (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) x := by
    rw [hcomp]
    exact e.contDiff.contMDiff.contMDiffAt.comp x hval
  have hinj : Function.Injective (mvfderiv 𝓘(ℂ, Fin (Fintype.card σ - Fintype.card ι) → ℂ)
      (fun y : affineZeroLocus p ↦ WithLp.toLp 2 (y : σ → ℂ)) x) := by
    intro v w hvw
    simp only [hcomp, mvfderiv_comp_apply_of_differentiableAt e.differentiableAt
      (hval.mdifferentiableAt two_ne_zero), e.fderiv,
      mvfderiv_apply_eq_mfderiv_apply] at hvw
    exact injective_mfderiv_coe_affineZeroLocus hp x (e.injective hvw)
  have hdim : Module.finrank ℂ (Fin (Fintype.card σ - Fintype.card ι) → ℂ) =
      Fintype.card σ - Fintype.card ι := Module.finrank_fin_fun ℂ
  simpa only [hdim] using manifoldMorseIndex_norm_sq_sub_comp_le hi hinj hcrit

end Complex

end TauCeti
