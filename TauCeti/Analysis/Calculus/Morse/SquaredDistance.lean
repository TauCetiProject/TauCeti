/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Calculus.Morse.Generic
-- Private: used only inside proofs.
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import TauCeti.Analysis.Calculus.TangentGraphChart
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.MeasureTheory.Measure.Haar.Unique

/-!
# Squared distance from almost every point is Morse along an immersion

Let `F : E → V` be a `C²` map from an open subset `U` of a finite-dimensional real normed space
into a finite-dimensional real inner product space, whose differential is injective at every
point of `U`. For almost every point `a` of `V`, with respect to any Haar measure, every critical
point in `U` of the squared distance `u ↦ ‖F u - a‖²` is nondegenerate
(`TauCeti.ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp`). This is the genericity that
makes the squared distance from a point a Morse function on an immersed or embedded submanifold
of Euclidean space; combined with properness along closed embeddings, it gives the Morse
exhaustions used to build CW models of affine varieties and Stein manifolds.

The proof is local. Near a point `u₀`, let `R` be the image of the differential of `F` at `u₀`.
The orthogonal projection of `F` to `R` is a local diffeomorphism, so in its coordinate `w ∈ R`
the map becomes the graph `F = w + h(w)` with `h(w) ∈ Rᗮ`
(`TauCeti.ContDiffOn.exists_openPartialHomeomorph_starProjection`). Writing `a = b + c` with
`b ∈ R` and `c ∈ Rᗮ`, Pythagoras (`Submodule.norm_sub_add_sq_of_mem_of_mem_orthogonal`) gives

`‖F - a‖² = (‖w‖² + ‖h(w) - c‖²) - 2⟪b, w⟫ + ‖b‖²`.

This is a family of functions of `w`, depending smoothly on the parameter `c`, perturbed by the
linear form `2⟪b, ·⟫`; the joint genericity of such perturbations,
`TauCeti.ae_hasNondegenerateCriticalPointsOn_sub_prod`, shows that almost every `(b, c)` gives
only nondegenerate critical points. Countably many such neighbourhoods cover `U`.

## Main results

* `TauCeti.ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp`: for almost every `a`, the
  squared distance from `a` along a `C²` immersion has only nondegenerate critical points.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §6, Theorem 6.6, which proves the
  same genericity through the focal points of the normal bundle.
* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §7, for
  the reduction to linear perturbations in graph coordinates.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Set Filter Topology InnerProductSpace

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {F : E → V} {U : Set E}

/-- Change of parameters for
`TauCeti.exists_isOpen_ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp`. The splitting
`a = b + c` along `V = R ⊕ Rᗮ` and the Riesz isomorphism `b ↦ 2⟪b, e₀ ·⟫` identify `V` with
`(E →L[ℝ] ℝ) × Rᗮ` and preserve null sets. So a property of almost every pair `(L, c)` holds, for
almost every `a`, at the pair coming from the splitting of `a`. -/
private theorem ae_exists_add_eq_of_ae_prod [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {R : Submodule ℝ V} (e₀ : E ≃L[ℝ] R)
    [MeasurableSpace ((E →L[ℝ] ℝ) × Rᗮ)] [BorelSpace ((E →L[ℝ] ℝ) × Rᗮ)]
    (ν : Measure ((E →L[ℝ] ℝ) × Rᗮ)) [ν.IsAddHaarMeasure] {p : (E →L[ℝ] ℝ) × Rᗮ → Prop}
    (hp : ∀ᵐ q ∂ν, p q) :
    ∀ᵐ a ∂μ, ∃ (b : R) (c : Rᗮ) (L : E →L[ℝ] ℝ), a = (b : V) + c ∧
      (∀ w, L w = 2 * ⟪(b : V), (e₀ w : V)⟫_ℝ) ∧ p (L, c) := by
  let S : (R × Rᗮ) ≃L[ℝ] V :=
    (Submodule.prodEquivOfIsCompl R Rᗮ R.isCompl_orthogonal).toContinuousLinearEquiv
  let D : R ≃L[ℝ] (E →L[ℝ] ℝ) :=
    ((LinearEquiv.smulOfNeZero ℝ R 2 two_ne_zero).toContinuousLinearEquiv.trans
      (toDual ℝ R).toContinuousLinearEquiv).trans
      (e₀.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let T : V ≃L[ℝ] (E →L[ℝ] ℝ) × Rᗮ := S.symm.trans (D.prodCongr (ContinuousLinearEquiv.refl ℝ _))
  filter_upwards [(T.toContinuousAddEquiv.quasiMeasurePreserving_addHaar μ ν).ae hp] with a ha
  refine ⟨(S.symm a).1, (S.symm a).2, D (S.symm a).1, ?_, fun w ↦ by simp [D], ?_⟩
  · conv_lhs => rw [← S.apply_symm_apply a]
    simp [S, Submodule.coe_prodEquivOfIsCompl']
  · have hTa : T a = (D (S.symm a).1, (S.symm a).2) := by simp [T]
    simpa [hTa] using ha

/-- The local form of `TauCeti.ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp`: a point
at which the differential is injective has an open neighbourhood on which the squared distance
from almost every point has only nondegenerate critical points. -/
private theorem exists_isOpen_ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {u₀ : E} (hu₀ : u₀ ∈ U)
    (hinj : Injective (fderiv ℝ F u₀)) :
    ∃ N, IsOpen N ∧ u₀ ∈ N ∧
      ∀ᵐ a ∂μ, HasNondegenerateCriticalPointsOn (fun u ↦ ‖F u - a‖ ^ 2) N := by
  obtain ⟨e₀, Φ, hu₀Φ, hΦU, hΦe, hΦd, hsymm⟩ :=
    ContDiffOn.exists_openPartialHomeomorph_starProjection hF hU one_le_two hu₀ hinj
  let R : Submodule ℝ V := LinearMap.range (fderiv ℝ F u₀ : E →ₗ[ℝ] V)
  -- In the coordinate `w`, the squared distance from `b + c` is the family `f c` perturbed by
  -- the linear form `2⟪b, e₀ ·⟫`, up to the constant `‖b‖²`.
  let f : Rᗮ → E → ℝ := fun c w ↦ ‖(e₀ w : V)‖ ^ 2 + ‖F (Φ.symm w) - e₀ w - c‖ ^ 2
  have hf : ∀ c, ∀ w ∈ Φ.target, ContDiffAt ℝ 2 (uncurry f) (c, w) := fun c w hw ↦ by
    have hF' : ContDiffAt ℝ 2 ((F ∘ Φ.symm) ∘ Prod.snd) (c, w) :=
      ((hF.contDiffAt (hU.mem_nhds (hΦU (Φ.map_target hw)))).comp w (hsymm w hw)).comp (c, w)
        contDiffAt_snd
    have hw' : ContDiffAt ℝ 2 (fun p : Rᗮ × E ↦ (e₀ p.2 : V)) (c, w) :=
      (R.subtypeL.contDiff.comp e₀.contDiff).contDiffAt.comp _ contDiffAt_snd
    have hc' : ContDiffAt ℝ 2 (fun p : Rᗮ × E ↦ (p.1 : V)) (c, w) :=
      Rᗮ.subtypeL.contDiff.contDiffAt.comp _ contDiffAt_fst
    exact (ContDiffAt.norm_sq ℝ hw').add (ContDiffAt.norm_sq ℝ ((hF'.sub hw').sub hc'))
  borelize ((E →L[ℝ] ℝ) × Rᗮ)
  have hgood := ae_hasNondegenerateCriticalPointsOn_sub_prod
    (addHaar : Measure ((E →L[ℝ] ℝ) × Rᗮ)) Φ.open_target hf
  refine ⟨Φ.source, Φ.open_source, hu₀Φ, ?_⟩
  filter_upwards [ae_exists_add_eq_of_ae_prod μ e₀ _ hgood] with a ⟨b, c, L, hab, hL, ha⟩
  -- The squared distance agrees on the source of `Φ` with `g ∘ Φ`.
  set g : E → ℝ := fun w ↦ f c w - L w + ‖(b : V)‖ ^ 2
  have hev : ∀ u ∈ Φ.source, ‖F u - a‖ ^ 2 = g (Φ u) := fun u hu ↦ by
    simp only [g, f, Φ.left_inv hu, hL, hΦe u hu, hab,
      Submodule.norm_sub_add_sq_of_mem_of_mem_orthogonal _ _ b.2 c.2]
  refine hasNondegenerateCriticalPointsOn_iff.2 fun u hu hcrit ↦ ?_
  have hev' : (fun u ↦ ‖F u - a‖ ^ 2) =ᶠ[𝓝 u] g ∘ Φ :=
    eventually_of_mem (Φ.open_source.mem_nhds hu) hev
  obtain ⟨hΦu, Tu, hTu⟩ := hΦd u hu
  have hgu : ContDiffAt ℝ 2 g (Φ u) := by
    have h := ((hf c (Φ u) (Φ.map_source hu)).comp (Φ u)
      ((contDiffAt_const (c := c)).prodMk contDiffAt_id)).sub L.contDiff.contDiffAt
    exact h.add contDiffAt_const
  -- Criticality passes to `g` at `Φ u`, since the differential of `Φ` there is invertible.
  have hgcrit : fderiv ℝ (fun w ↦ f c w - L w) (Φ u) = 0 := by
    rw [hev'.fderiv_eq, fderiv_comp_eq_zero_iff_of_isInvertible (hgu.differentiableAt (by norm_num))
      (hΦu.differentiableAt (by norm_num)) ⟨Tu, hTu⟩] at hcrit
    simpa [g, fderiv_add_const] using hcrit
  have hnd : IsNondegenerateCriticalPoint g (Φ u) :=
    (isNondegenerateCriticalPoint_add_const_iff _).2
      (hasNondegenerateCriticalPointsOn_iff.1 ha (Φ.map_source hu) hgcrit)
  exact (hnd.comp hΦu ⟨Tu, hTu⟩).congr_of_eventuallyEq hev'.symm

/-- **The squared distance from almost every point is Morse along an immersion.** If `F` is `C²`
on the open set `U` and its differential is injective at every point of `U`, then for almost every
`a ∈ V`, with respect to any Haar measure `μ`, every critical point in `U` of `u ↦ ‖F u - a‖²` is
nondegenerate. -/
theorem ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
    (hinj : ∀ u ∈ U, Injective (fderiv ℝ F u)) :
    ∀ᵐ a ∂μ, HasNondegenerateCriticalPointsOn (fun u ↦ ‖F u - a‖ ^ 2) U := by
  choose! N hNo hmem hae using fun u (hu : u ∈ U) ↦
    exists_isOpen_ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp μ hU hF hu (hinj u hu)
  obtain ⟨T, hTU, hTc, hcover⟩ := TopologicalSpace.isOpen_biUnion_countable U N hNo
  filter_upwards [(ae_ball_iff hTc).2 fun u hu ↦ hae u (hTU hu)] with a ha
  refine hasNondegenerateCriticalPointsOn_iff.2 fun x hx hcrit ↦ ?_
  have hx' : x ∈ ⋃ u ∈ T, N u := hcover ▸ mem_biUnion hx (hmem x hx)
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 hx'
  exact hasNondegenerateCriticalPointsOn_iff.1 (ha u hu) hxu hcrit

end TauCeti
