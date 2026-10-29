/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.EssentialConvexity

/-!
# Sets fixed by every Steiner symmetrization

A centered open ball is fixed by Steiner symmetrization in every unit direction. Conversely, a
Lebesgue-measurable set of finite volume which agrees almost everywhere with each of its Steiner
symmetrals is almost everywhere a centered open ball, necessarily of the same volume. Thus the
centered balls are exactly the common fixed points, up to null sets, of all Steiner
symmetrizations, and a set which no single symmetrization changes is a ball.

For the converse, the set has interval line sections in every direction, so its Lebesgue density
points form a convex set (`TauCeti.convex_setOf_tendsto_volume_inter_closedBall_div`). A Steiner
symmetral is symmetric about the hyperplane orthogonal to its direction, so the set is
a.e. invariant under every hyperplane reflection through the origin. Lebesgue density is
preserved by these isometries, so the set of density points contains, with each point, the whole
sphere through it, and by convexity the closed ball it bounds. A set with this property is a
centered open ball, closed ball or the whole space, and finite volume excludes the last case.
-/

public noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A centered open ball is fixed by Steiner symmetrization in every unit direction. -/
@[simp]
theorem steinerSymmetrization_ball_zero (e : E) (he : ‖e‖ = 1) (r : ℝ) :
    steinerSymmetrization e he (ball (0 : E) r) = ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, steinerSymmetrization_empty]
  -- On the line through `y ∈ e⊥`, the ball is the centered interval of radius `√(r² - ‖y‖²)`.
  have hsection (y : (ℝ ∙ e)ᗮ) :
      {t : ℝ | (y : E) + t • e ∈ ball (0 : E) r} = ball (0 : ℝ) √(r ^ 2 - ‖y‖ ^ 2) := by
    ext t
    rw [mem_ofPred_eq, mem_ball_zero_iff, mem_ball_zero_iff, Real.norm_eq_abs,
      Real.lt_sqrt (abs_nonneg t), sq_abs, lt_sub_iff_add_lt', ← norm_add_smul_sq e he,
      sq_lt_sq₀ (norm_nonneg _) hr.le]
  ext x
  obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
  rw [orthogonalLineEquiv_apply, mem_steinerSymmetrization, hsection, Real.volume_ball,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top, eball_ofReal,
    ← hsection, mem_ofPred_eq]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- If a set agrees a.e. with its Steiner symmetral in every unit direction, then Lebesgue
density of the set at a point depends only on the norm of the point: two points of equal norm
are exchanged by a hyperplane reflection through the origin, which preserves the set a.e. -/
private theorem tendsto_volume_inter_closedBall_div_of_norm_eq {s : Set E}
    (hs : NullMeasurableSet s volume)
    (h : ∀ (e : E) (he : ‖e‖ = 1), steinerSymmetrization e he s =ᵐ[volume] s) {x z : E}
    (hz : ‖z‖ = ‖x‖)
    (hx : Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
      (𝓝 1)) :
    Tendsto (fun r => volume (s ∩ closedBall z r) / volume (closedBall z r)) (𝓝[>] 0)
      (𝓝 1) := by
  rcases eq_or_ne x z with rfl | hxz
  · exact hx
  have hxz' : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  set e := ‖x - z‖⁻¹ • (x - z)
  have he : ‖e‖ = 1 := norm_smul_inv_norm (sub_ne_zero.2 hxz)
  set ρ := (ℝ ∙ e)ᗮ.reflection
  have hρx : ρ x = z := by
    simp only [ρ, e, Submodule.span_singleton_smul_eq (inv_pos.2 hxz').ne'.isUnit]
    exact Submodule.reflection_sub hz.symm
  have hρ : MeasurePreserving ρ volume volume := ρ.measurePreserving
  have hρs : ρ ⁻¹' s =ᵐ[volume] s := by
    have hpre := hρ.quasiMeasurePreserving.preimage_ae_eq (h e he)
    rw [preimage_reflection_steinerSymmetrization] at hpre
    exact hpre.symm.trans (h e he)
  refine hx.congr fun r => ?_
  rw [← hρx, Measure.addHaar_closedBall_center volume (ρ x),
    Measure.addHaar_closedBall_center volume x,
    ← hρ.measure_preimage (s := s ∩ closedBall (ρ x) r)
      (hs.inter measurableSet_closedBall.nullMeasurableSet),
    preimage_inter, ρ.preimage_closedBall, LinearIsometryEquiv.symm_apply_apply,
    measure_congr (hρs.inter (ae_eq_refl _))]

/-- **Fixed points of Steiner symmetrization.** A Lebesgue-measurable set of finite volume which
agrees almost everywhere with its Steiner symmetral in every unit direction agrees almost
everywhere with a centered open ball. -/
theorem exists_ae_eq_ball_of_forall_steinerSymmetrization_ae_eq {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (h : ∀ (e : E) (he : ‖e‖ = 1), steinerSymmetrization e he s =ᵐ[volume] s) :
    ∃ r, 0 ≤ r ∧ s =ᵐ[volume] ball (0 : E) r := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, by rw [ball_zero]⟩
    · refine ⟨1, zero_le_one, ?_⟩
      rw [Subsingleton.eq_univ_of_nonempty hne,
        Subsingleton.eq_univ_of_nonempty (nonempty_ball.2 one_pos)]
  set D := {x | Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
    (𝓝[>] 0) (𝓝 1)}
  have hsD : s =ᵐ[volume] D := hs.ae_eq_setOf_tendsto_measure_inter_div
  -- The density points form a convex set, since every line section of `s` is a.e. an interval.
  have hconv : Convex ℝ D := convex_setOf_tendsto_volume_inter_closedBall_div hs fun e he =>
    (ae_lineSection_ordConnected_iff e he (h e he)).1 <| Eventually.of_forall fun y =>
      ⟨_, ordConnected_lineSection_steinerSymmetrization e he s y, ae_eq_refl _⟩
  have hsphere {x z : E} (hx : x ∈ D) (hz : ‖z‖ = ‖x‖) : z ∈ D :=
    tendsto_volume_inter_closedBall_div_of_norm_eq hs h hz hx
  -- Hence the density points contain, with each point, the closed ball it bounds.
  have hdown {x y : E} (hx : x ∈ D) (hy : ‖y‖ ≤ ‖x‖) : y ∈ D := by
    have h0 : (0 : E) ∈ D := by
      convert hconv.add_smul_sub_mem hx (hsphere hx (norm_neg x))
        ⟨one_half_pos.le, one_half_lt_one.le⟩ using 1
      module
    rcases eq_or_ne y 0 with rfl | hy0
    · exact h0
    have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hz : (‖x‖ / ‖y‖) • y ∈ D := hsphere hx (by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hny.ne'])
    have hmem := hconv.smul_mem_of_zero_mem h0 hz
      ⟨by positivity, div_le_one_of_le₀ hy (norm_nonneg x)⟩
    rwa [smul_smul, div_mul_div_cancel₀ (hny.trans_le hy).ne', div_self hny.ne', one_smul] at hmem
  -- Finite volume makes the density points bounded, since otherwise they fill the space.
  have hbdd : BddAbove (norm '' D) := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    have hD : D = univ := eq_univ_of_forall fun y => by
      obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := hnb ‖y‖
      exact hdown hx hlt.le
    exact hfin (by rw [measure_congr hsD, hD, measure_univ_of_isAddLeftInvariant])
  rcases D.eq_empty_or_nonempty with hDe | ⟨x₀, hx₀⟩
  · exact ⟨0, le_rfl, by rwa [ball_zero, ← hDe]⟩
  -- The density points lie between the open and the closed ball of radius their maximal norm.
  set R := sSup (norm '' D)
  have hball : ball (0 : E) R ⊆ D := fun y hy => by
    rw [mem_ball_zero_iff] at hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (Nonempty.image _ ⟨x₀, hx₀⟩) hy
    exact hdown hx hlt.le
  have hclosed : D ⊆ closedBall (0 : E) R := fun x hx =>
    mem_closedBall_zero_iff.2 (le_csSup hbdd (mem_image_of_mem _ hx))
  refine ⟨R, (norm_nonneg x₀).trans (le_csSup hbdd (mem_image_of_mem _ hx₀)), ?_⟩
  refine hsD.trans (ae_eq_of_subset_of_measure_ge hball ?_ measurableSet_ball.nullMeasurableSet
    (by rwa [← measure_congr hsD])).symm
  rw [← Measure.addHaar_closedBall_eq_addHaar_ball]
  exact measure_mono hclosed

/-- **Fixed points of Steiner symmetrization.** A Lebesgue-measurable set of finite volume
agrees almost everywhere with its Steiner symmetral in every unit direction exactly when it agrees
almost everywhere with a centered open ball. -/
theorem forall_steinerSymmetrization_ae_eq_iff_exists_ae_eq_ball {s : Set E}
    (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) :
    (∀ (e : E) (he : ‖e‖ = 1), steinerSymmetrization e he s =ᵐ[volume] s) ↔
      ∃ r, 0 ≤ r ∧ s =ᵐ[volume] ball (0 : E) r := by
  refine ⟨exists_ae_eq_ball_of_forall_steinerSymmetrization_ae_eq hs hfin,
    fun ⟨r, _, hr⟩ e he => ?_⟩
  have hsym := steinerSymmetrization_ae_eq e he hr
  rw [steinerSymmetrization_ball_zero] at hsym
  exact hsym.trans hr.symm

end TauCeti
