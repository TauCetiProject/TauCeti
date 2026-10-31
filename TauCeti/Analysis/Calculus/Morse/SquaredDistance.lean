/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Analysis.Calculus.Morse.Generic
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import TauCeti.Analysis.Normed.Module.FiniteDimension
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
the map becomes the graph `F = w + h(w)` with `h(w) ∈ Rᗮ`. Writing `a = b + c` with `b ∈ R` and
`c ∈ Rᗮ`, Pythagoras gives

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

/-- Pythagoras for the squared distance from `b + c`, where `b ∈ R` and `c ∈ Rᗮ`: the
components of `v - (b + c)` along `R` and `Rᗮ` are `P v - b` and `v - P v - c`, where `P` is the
orthogonal projection to `R`. -/
private theorem norm_sub_add_sq_eq (R : Submodule ℝ V) (v : V) (b : R) (c : Rᗮ) :
    ‖v - (b + c)‖ ^ 2 = ‖R.starProjection v‖ ^ 2 + ‖v - R.starProjection v - c‖ ^ 2 -
      2 * ⟪(b : V), R.starProjection v⟫_ℝ + ‖(b : V)‖ ^ 2 := by
  have hperp : v - R.starProjection v - c ∈ Rᗮ :=
    Rᗮ.sub_mem (R.sub_starProjection_mem_orthogonal v) c.2
  have hsplit : v - (b + c) = (R.starProjection v - b) + (v - R.starProjection v - c) := by abel
  rw [hsplit, norm_add_sq_real,
    R.inner_right_of_mem_orthogonal (R.sub_mem (R.starProjection_apply_mem v) b.2) hperp,
    norm_sub_sq_real, real_inner_comm]
  ring

/-- **Graph coordinates.** Near a point `u₀` at which its differential is injective, a `C²` map
`F` into an inner product space is a graph over its tangent space `R` at `u₀`: there is a chart
`Φ` of `E` around `u₀`, `C²` with invertible differential on its source and with `C²` inverse, in
which the orthogonal projection of `F` to `R` is a fixed linear isomorphism `e₀ : E ≃ R`. -/
private theorem exists_graph_chart (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {u₀ : E}
    (hu₀ : u₀ ∈ U) (hinj : Injective (fderiv ℝ F u₀)) :
    ∃ (R : Submodule ℝ V) (e₀ : E ≃L[ℝ] R) (Φ : OpenPartialHomeomorph E E),
      u₀ ∈ Φ.source ∧ Φ.source ⊆ U ∧
      (∀ u ∈ Φ.source, (e₀ (Φ u) : V) = R.starProjection (F u)) ∧
      (∀ u ∈ Φ.source, ContDiffAt ℝ 2 Φ u ∧ (fderiv ℝ Φ u).IsInvertible) ∧
      ∀ w ∈ Φ.target, ContDiffAt ℝ 2 Φ.symm w := by
  -- The tangent space `R` at `u₀`, and the orthogonal projection `Pr` to it.
  set R : Submodule ℝ V := LinearMap.range (fderiv ℝ F u₀ : E →ₗ[ℝ] V)
  set Pr : V →L[ℝ] R := R.orthogonalProjectionOnto
  -- At `u₀` the differential of `Pr ∘ F` is an isomorphism `e₀` onto `R`.
  have hPr : ∀ v, Pr (fderiv ℝ F u₀ v) = ⟨fderiv ℝ F u₀ v, LinearMap.mem_range_self _ v⟩ :=
    fun v ↦ R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, LinearMap.mem_range_self _ v⟩
  have hbij : Bijective (Pr ∘L fderiv ℝ F u₀) := by
    refine ⟨fun v w h ↦ hinj ?_, fun ⟨r, v, hv⟩ ↦ ⟨v, ?_⟩⟩
    · simpa [hPr] using h
    · simp only [ContinuousLinearMap.coe_comp, comp_apply, hPr]
      exact Subtype.ext hv
  let e₀ : E ≃L[ℝ] R :=
    (LinearEquiv.ofBijective (Pr ∘L fderiv ℝ F u₀ : E →ₗ[ℝ] R) hbij).toContinuousLinearEquiv
  -- The coordinate `σ = e₀⁻¹ ∘ Pr ∘ F` on `E`, whose differential at `u₀` is the identity.
  set σ : E → E := fun u ↦ e₀.symm (Pr (F u))
  have hσC : ContDiffOn ℝ 2 σ U := (e₀.symm.contDiff.comp Pr.contDiff).comp_contDiffOn hF
  have hσd : ∀ u ∈ U, HasFDerivAt σ ((e₀.symm : R →L[ℝ] E) ∘L Pr ∘L fderiv ℝ F u) u :=
    fun u hu ↦ e₀.symm.hasFDerivAt.comp u (Pr.hasFDerivAt.comp u
      ((hF.differentiableOn (by norm_num) u hu).differentiableAt (hU.mem_nhds hu)).hasFDerivAt)
  have hσ₀ : HasFDerivAt σ ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) u₀ := by
    convert hσd u₀ hu₀ using 1
    ext v
    exact (e₀.symm_apply_apply v).symm
  -- The inverse function theorem makes `σ` a chart near `u₀`; restrict its source to the open
  -- set `N` where the differential of `σ` stays invertible.
  let Φ₀ := (hσC.contDiffAt (hU.mem_nhds hu₀)).toOpenPartialHomeomorph σ hσ₀ two_ne_zero
  set N := U ∩ fderiv ℝ σ ⁻¹' {T | T.IsInvertible}
  have hN : IsOpen N := (hσC.continuousOn_fderiv_of_isOpen hU (by norm_num)).isOpen_inter_preimage
    hU ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let Φ := Φ₀.restrOpen N hN
  have hΦs : Φ.source = Φ₀.source ∩ N := Φ₀.restrOpen_source N hN
  refine ⟨R, e₀, Φ, ?_, ?_, fun u _ ↦ ?_, fun u hu ↦ ?_, fun w hw ↦ ?_⟩
  · rw [hΦs]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hu₀, _, hσ₀.fderiv.symm⟩
  · rw [hΦs]
    exact fun u hu ↦ hu.2.1
  · rw [R.starProjection_apply]
    exact congrArg Subtype.val (e₀.apply_symm_apply _)
  · rw [hΦs] at hu
    exact ⟨hσC.contDiffAt (hU.mem_nhds hu.2.1), hu.2.2⟩
  · have hs : Φ.symm w ∈ Φ₀.source ∩ N := hΦs ▸ Φ.map_target hw
    obtain ⟨T, hT⟩ := hs.2.2
    refine Φ.contDiffAt_symm hw (f₀' := T) ?_ (hσC.contDiffAt (hU.mem_nhds hs.2.1))
    rw [hT]
    exact (hσd _ hs.2.1).differentiableAt.hasFDerivAt

/-- The local form of `TauCeti.ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp`: a point
at which the differential is injective has an open neighbourhood on which the squared distance
from almost every point has only nondegenerate critical points. -/
private theorem exists_isOpen_ae_hasNondegenerateCriticalPointsOn_norm_sq_sub_comp
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {u₀ : E} (hu₀ : u₀ ∈ U)
    (hinj : Injective (fderiv ℝ F u₀)) :
    ∃ N, IsOpen N ∧ u₀ ∈ N ∧
      ∀ᵐ a ∂μ, HasNondegenerateCriticalPointsOn (fun u ↦ ‖F u - a‖ ^ 2) N := by
  obtain ⟨R, e₀, Φ, hu₀Φ, hΦU, hΦe, hΦd, hsymm⟩ := exists_graph_chart hU hF hu₀ hinj
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
  -- The splitting `a = b + c` and the Riesz isomorphism `b ↦ 2⟪b, e₀ ·⟫` identify `V` with the
  -- parameter space, preserving null sets.
  let S : (R × Rᗮ) ≃L[ℝ] V :=
    (Submodule.prodEquivOfIsCompl R Rᗮ R.isCompl_orthogonal).toContinuousLinearEquiv
  let D : R ≃L[ℝ] (E →L[ℝ] ℝ) :=
    ((LinearEquiv.smulOfNeZero ℝ R 2 two_ne_zero).toContinuousLinearEquiv.trans
      (toDual ℝ R).toContinuousLinearEquiv).trans
      (e₀.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  have hD : ∀ (b : R) (w : E), D b w = 2 * ⟪(b : V), (e₀ w : V)⟫_ℝ := fun b w ↦ by
    simp [D]
  let T : V ≃L[ℝ] (E →L[ℝ] ℝ) × Rᗮ := S.symm.trans (D.prodCongr (ContinuousLinearEquiv.refl ℝ _))
  have hT : ∀ᵐ a ∂μ,
      HasNondegenerateCriticalPointsOn (fun w ↦ f (T a).2 w - (T a).1 w) Φ.target :=
    (T.toContinuousAddEquiv.quasiMeasurePreserving_addHaar μ addHaar).ae hgood
  refine ⟨Φ.source, Φ.open_source, hu₀Φ, ?_⟩
  filter_upwards [hT] with a ha
  set b := (S.symm a).1
  set c := (S.symm a).2
  have hab : a = b + c := by
    conv_lhs => rw [← S.apply_symm_apply a]
    rfl
  have ha' : HasNondegenerateCriticalPointsOn (fun w ↦ f c w - D b w) Φ.target := ha
  -- The squared distance agrees on the source of `Φ` with `g ∘ Φ`.
  set g : E → ℝ := fun w ↦ f c w - D b w + ‖(b : V)‖ ^ 2
  have hev : ∀ u ∈ Φ.source, ‖F u - a‖ ^ 2 = g (Φ u) := fun u hu ↦ by
    simp only [g, f, Φ.left_inv hu, hD, hΦe u hu, hab, norm_sub_add_sq_eq]
  refine hasNondegenerateCriticalPointsOn_iff.2 fun u hu hcrit ↦ ?_
  have hev' : (fun u ↦ ‖F u - a‖ ^ 2) =ᶠ[𝓝 u] g ∘ Φ :=
    eventually_of_mem (Φ.open_source.mem_nhds hu) hev
  obtain ⟨hΦu, Tu, hTu⟩ := hΦd u hu
  have hgu : ContDiffAt ℝ 2 g (Φ u) := by
    have h := ((hf c (Φ u) (Φ.map_source hu)).comp (Φ u)
      ((contDiffAt_const (c := c)).prodMk contDiffAt_id)).sub (D b).contDiff.contDiffAt
    exact h.add contDiffAt_const
  -- Criticality passes to `g` at `Φ u`, since the differential of `Φ` there is invertible.
  have hgcrit : fderiv ℝ (fun w ↦ f c w - D b w) (Φ u) = 0 := by
    have h := hcrit
    rw [hev'.fderiv_eq, fderiv_comp u (hgu.differentiableAt (by norm_num))
      (hΦu.differentiableAt (by norm_num)), ← hTu] at h
    ext v
    simpa [g, fderiv_add_const] using congrArg (fun L : E →L[ℝ] ℝ ↦ L (Tu.symm v)) h
  have hnd : IsNondegenerateCriticalPoint g (Φ u) :=
    (isNondegenerateCriticalPoint_add_const_iff _).2
      (hasNondegenerateCriticalPointsOn_iff.1 ha' (Φ.map_source hu) hgcrit)
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
