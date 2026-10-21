/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.Normed.Lp.GraphDomain
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives along coordinate slices of an `L^p` product

For a function `g` on the `L^p` product `WithLp p (F × E)`, freezing one coordinate gives a
function of the other coordinate alone. Its derivative is the derivative of `g` in the
corresponding coordinate direction: along the line `s ↦ (s, y)` in the first factor `𝕜` it is
`fderiv 𝕜 g (t, y) (1, 0)`, and on the slice `z ↦ (t, z)` it is `w ↦ fderiv 𝕜 g (t, y) (0, w)`.
These are the chain rules used to compute integrals over a half-space `{x | a < x.fst}` one
normal line or one tangential slice at a time, as in Fubini-type proofs of the divergence
theorem. The file also computes the derivative of the normal graph parametrization
`y ↦ (φ y, y)`: it is the graph `x ↦ (A x, x)` of the derivative `A` of `φ`, so its
geometric Jacobian is the classical surface factor `sqrt (1 + ‖A‖²)`.

## Main declarations

* `TauCeti.hasDerivAt_comp_toLp_fst`: the derivative of `g` along a line in the first factor is
  its derivative in the direction `(1, 0)`.
* `TauCeti.fderiv_comp_toLp_snd`: the derivative of `g` on a slice of the second factor is its
  derivative in the direction `(0, w)`.
* `HasFDerivAt.normalGraphEmbedding`: the derivative of a graph parametrization is the graph of
  the derivative.
* `DifferentiableAt.fderiv_normalGraphEmbedding`: the Fréchet derivative of a graph
  parametrization at a differentiability point.
* `DifferentiableAt.injective_fderiv_normalGraphEmbedding`: that derivative is injective.
* `DifferentiableAt.range_fderiv_normalGraphEmbedding`: the range of that derivative is the
  linear tangent graph.
* `DifferentiableAt.normDet_fderiv_normalGraphEmbedding`: the geometric Jacobian of a graph
  parametrization is `sqrt (1 + ‖Dφ‖²)`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Along the line `s ↦ (s, y)` in the first factor of `WithLp p (𝕜 × E)`, the derivative of a
function differentiable at `(t, y)` is its derivative in the direction `(1, 0)`. -/
theorem hasDerivAt_comp_toLp_fst {g : WithLp p (𝕜 × E) → G} {t : 𝕜} {y : E}
    (hg : DifferentiableAt 𝕜 g (WithLp.toLp p (t, y))) :
    HasDerivAt (fun s : 𝕜 ↦ g (WithLp.toLp p (s, y)))
      (fderiv 𝕜 g (WithLp.toLp p (t, y)) (WithLp.toLp p (1, (0 : E)))) t := by
  have hl : HasDerivAt (fun s : 𝕜 ↦ WithLp.toLp p (s, y)) (WithLp.toLp p (1, (0 : E))) t :=
    ((WithLp.prodContinuousLinearEquiv p 𝕜 𝕜 E).symm.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact hg.hasFDerivAt.comp_hasDerivAt t hl

/-- On the slice `z ↦ (t, z)` of the second factor of `WithLp p (F × E)`, the derivative of a
function differentiable at `(t, y)`, applied to a direction `w` of `E`, is its derivative in the
direction `(0, w)`. -/
theorem fderiv_comp_toLp_snd {g : WithLp p (F × E) → G} {t : F} {y : E}
    (hg : DifferentiableAt 𝕜 g (WithLp.toLp p (t, y))) (w : E) :
    fderiv 𝕜 (fun z : E ↦ g (WithLp.toLp p (t, z))) y w =
      fderiv 𝕜 g (WithLp.toLp p (t, y)) (WithLp.toLp p (0, w)) := by
  have hl : HasFDerivAt (fun z : E ↦ WithLp.toLp p (t, z))
      ((WithLp.prodContinuousLinearEquiv p 𝕜 F E).symm.toContinuousLinearMap.comp
        ((0 : E →L[𝕜] F).prod (ContinuousLinearMap.id 𝕜 E))) y :=
    ((WithLp.prodContinuousLinearEquiv p 𝕜 F E).symm.hasFDerivAt).comp y
      ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have h : HasFDerivAt (fun z : E ↦ g (WithLp.toLp p (t, z))) _ y := hg.hasFDerivAt.comp y hl
  rw [h.fderiv]
  simp

section NormalGraph

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The derivative of a graph parametrization is the graph of the derivative. -/
theorem _root_.HasFDerivAt.normalGraphEmbedding {φ : V → ℝ} {φ' : V →L[ℝ] ℝ} {x : V}
    (hφ : HasFDerivAt φ φ' x) :
    HasFDerivAt (TauCeti.normalGraphEmbedding φ) φ'.normalGraphL x := by
  have h : TauCeti.normalGraphEmbedding φ =
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).symm ∘ fun y ↦ (φ y, y) :=
    funext fun y ↦ (WithLp.ext_iff 2).2 <| Prod.ext (normalGraphEmbedding_fst φ y)
      (normalGraphEmbedding_snd φ y)
  rw [h]
  refine (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).symm :
    (ℝ × V) →L[ℝ] WithLp 2 (ℝ × V)).hasFDerivAt.comp x
      (hφ.prodMk (hasFDerivAt_id x))).congr_fderiv ?_
  ext v
  simpa using (WithLp.ext_iff 2).2 <| Prod.ext (normalGraphEmbedding_fst φ' v).symm
    (normalGraphEmbedding_snd φ' v).symm

/-- At a differentiability point, the Fréchet derivative of a graph parametrization is the
continuous linear graph of the derivative. -/
theorem _root_.DifferentiableAt.fderiv_normalGraphEmbedding {φ : V → ℝ} {x : V}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (TauCeti.normalGraphEmbedding φ) x = (fderiv ℝ φ x).normalGraphL :=
  hφ.hasFDerivAt.normalGraphEmbedding.fderiv

/-- At a differentiability point, the Fréchet derivative of a graph parametrization is
injective. -/
theorem _root_.DifferentiableAt.injective_fderiv_normalGraphEmbedding {φ : V → ℝ} {x : V}
    (hφ : DifferentiableAt ℝ φ x) :
    Function.Injective (fderiv ℝ (TauCeti.normalGraphEmbedding φ) x) := by
  rw [hφ.fderiv_normalGraphEmbedding]
  exact (fderiv ℝ φ x).injective_normalGraphL

/-- At a differentiability point of `φ`, the range of the derivative of the normal graph
parametrization is the linear graph of `fderiv ℝ φ x`. This is the tangent plane to a `C¹`
normal graph at the corresponding point. -/
theorem _root_.DifferentiableAt.range_fderiv_normalGraphEmbedding {φ : V → ℝ} {x : V}
    (hφ : DifferentiableAt ℝ φ x) :
    (LinearMap.range (fderiv ℝ (TauCeti.normalGraphEmbedding φ) x).toLinearMap :
      Set (WithLp 2 (ℝ × V))) =
      {z | z.fst = fderiv ℝ φ x z.snd} := by
  rw [hφ.fderiv_normalGraphEmbedding]
  exact (fderiv ℝ φ x).range_normalGraphL

/-- At a differentiability point, the geometric Jacobian of a normal graph parametrization is
the classical surface factor `sqrt (1 + ‖Dφ‖²)`. -/
theorem _root_.DifferentiableAt.normDet_fderiv_normalGraphEmbedding {U : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] {φ : U → ℝ} {x : U}
    (hφ : DifferentiableAt ℝ φ x) :
    (fderiv ℝ (TauCeti.normalGraphEmbedding φ) x).normDet =
      Real.sqrt (1 + ‖fderiv ℝ φ x‖ ^ 2) := by
  rw [hφ.fderiv_normalGraphEmbedding, ContinuousLinearMap.normDet_normalGraphL]

end NormalGraph

end TauCeti

end
