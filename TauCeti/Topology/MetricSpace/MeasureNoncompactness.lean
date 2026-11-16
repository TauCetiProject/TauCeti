/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# The ball-cover measure of noncompactness

`Set.ballMeasureNoncompactness s` is the infimum of the radii of finite covers of `s`
by balls with centres anywhere in the ambient space. It takes values in `ℝ≥0∞`, so
unbounded sets have value `∞`. Closed balls and radius zero are allowed in the
infimum; the strict-radius characterization also identifies it with the infimum
using positive radii and open balls.

The measure vanishes precisely on totally bounded sets, hence on relatively compact
sets in a complete metric space. Lipschitz maps decrease it by at most their
Lipschitz constant. For normed groups it is subadditive under set addition and
unchanged by addition of a nonempty totally bounded set. Scalar multiplication
scales it by the norm of the scalar. These are the set-level
estimates used in essential spectral radius arguments.

The definition uses Mathlib's `Metric.externalCoveringNumber` and `Metric.IsCover`.
For the ball-cover convention see H. Hennion, *Quasi-compacité. Cas des noyaux
lipschitziens et des noyaux markoviens* (1995), §5, Définition 5.1.
-/

public section

open Metric
open scoped ENNReal NNReal Pointwise

namespace Set

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  {s t : Set X} {r : ℝ≥0} {a : ℝ≥0∞}

/-- The infimum of radii admitting a finite external ball cover. The value is `∞`
when there is no finite-radius cover. -/
noncomputable def ballMeasureNoncompactness (s : Set X) : ℝ≥0∞ :=
  ⨅ (r : ℝ≥0) (_ : externalCoveringNumber r s ≠ ⊤), (r : ℝ≥0∞)

/-- Strict upper bounds are witnessed by a finite cover of strictly smaller radius. -/
theorem ballMeasureNoncompactness_lt_iff :
    s.ballMeasureNoncompactness < a ↔
      ∃ r : ℝ≥0, (r : ℝ≥0∞) < a ∧ ∃ N : Set X, N.Finite ∧ IsCover r s N := by
  simp only [ballMeasureNoncompactness, iInf_lt_iff, externalCoveringNumber_ne_top_iff]
  tauto

/-- Every finite cover bounds the measure by its radius. -/
theorem ballMeasureNoncompactness_le_of_isCover {N : Set X} (hN : N.Finite)
    (hs : IsCover r s N) : s.ballMeasureNoncompactness ≤ r :=
  iInf₂_le r (ne_top_of_le_ne_top (encard_ne_top_iff.mpr hN) hs.externalCoveringNumber_le_encard)

/-- The measure is monotone under inclusion. -/
theorem ballMeasureNoncompactness_mono (hst : s ⊆ t) :
    s.ballMeasureNoncompactness ≤ t.ballMeasureNoncompactness := by
  unfold ballMeasureNoncompactness
  refine le_iInf fun r ↦ le_iInf fun hr ↦ ?_
  exact iInf₂_le r
    (ne_top_of_le_ne_top hr (externalCoveringNumber_mono_set hst))

/-- A finite set has zero measure of noncompactness. -/
@[simp] theorem Finite.ballMeasureNoncompactness_eq_zero (hs : s.Finite) :
    s.ballMeasureNoncompactness = 0 := by
  exact le_antisymm (ballMeasureNoncompactness_le_of_isCover (r := 0) hs (.refl 0 s))
    bot_le

/-- Totally bounded sets have zero measure of noncompactness. -/
theorem _root_.TotallyBounded.ballMeasureNoncompactness_eq_zero (hs : TotallyBounded s) :
    s.ballMeasureNoncompactness = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_forall_gt fun a ha ↦ ?_
  obtain ⟨r, hr, hra⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
  obtain ⟨N, _, hN, hcover⟩ := exists_finite_isCover_of_totallyBounded (by simpa using hr.ne') hs
  exact (ballMeasureNoncompactness_le_of_isCover hN hcover).trans_lt hra

/-- Vanishing of the measure characterizes total boundedness, without completeness. -/
@[simp] theorem ballMeasureNoncompactness_eq_zero_iff :
    s.ballMeasureNoncompactness = 0 ↔ TotallyBounded s := by
  refine ⟨fun hs ↦ EMetric.totallyBounded_iff.mpr fun ε hε ↦ ?_,
    TotallyBounded.ballMeasureNoncompactness_eq_zero⟩
  obtain ⟨r, hr, N, hN, hc⟩ := ballMeasureNoncompactness_lt_iff.mp (hs.symm ▸ hε)
  refine ⟨N, hN, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hc hx
  simp only [mem_iUnion, Metric.mem_eball, exists_prop]
  exact ⟨y, hy, hxy.trans_lt hr⟩

/-- In a complete metric space, zero measure means relative compactness. -/
theorem ballMeasureNoncompactness_eq_zero_iff_isCompact_closure [CompleteSpace X] :
    s.ballMeasureNoncompactness = 0 ↔ IsCompact (closure s) := by
  rw [ballMeasureNoncompactness_eq_zero_iff]
  exact ⟨fun hs ↦ hs.closure.isCompact_of_isClosed isClosed_closure,
    fun hs ↦ hs.totallyBounded.subset subset_closure⟩

/-- Strict bounds can also be witnessed using positive radii and open balls. -/
theorem ballMeasureNoncompactness_lt_iff_exists_eball_cover :
    s.ballMeasureNoncompactness < a ↔ ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) < a ∧
      ∃ N : Set X, N.Finite ∧ s ⊆ ⋃ y ∈ N, Metric.eball y r := by
  constructor
  · intro hs
    obtain ⟨r, hr, N, hN, hc⟩ := ballMeasureNoncompactness_lt_iff.mp hs
    obtain ⟨R, hrR, hRa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
    have hR : (0 : ℝ≥0∞) < R := bot_le.trans_lt hrR
    refine ⟨R, by exact_mod_cast hR, hRa, N, hN, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, hxy⟩ := hc hx
    exact mem_iUnion₂.mpr ⟨y, hy, hxy.trans_lt hrR⟩
  · rintro ⟨r, _, hr, N, hN, hc⟩
    apply (ballMeasureNoncompactness_le_of_isCover hN ?_).trans_lt hr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hc hx)
    exact ⟨y, hy, (Metric.mem_eball.mp hxy).le⟩

/-- Taking the closure does not change the measure. -/
@[simp] theorem ballMeasureNoncompactness_closure :
    (closure s).ballMeasureNoncompactness = s.ballMeasureNoncompactness := by
  refine le_antisymm ?_ (ballMeasureNoncompactness_mono subset_closure)
  unfold ballMeasureNoncompactness
  refine le_iInf fun r ↦ le_iInf fun hr ↦ ?_
  obtain ⟨N, hN, hc⟩ := externalCoveringNumber_ne_top_iff.mp hr
  apply ballMeasureNoncompactness_le_of_isCover hN
  rw [isCover_iff_subset_iUnion_closedEBall] at hc ⊢
  exact closure_minimal hc (hN.isClosed_biUnion fun _ _ ↦ isClosed_closedEBall)

/-- A Lipschitz map decreases the measure by at most its Lipschitz constant. -/
theorem _root_.LipschitzWith.ballMeasureNoncompactness_image_le {K : ℝ≥0} {f : X → Y}
    (hf : LipschitzWith K f) (s : Set X) :
    (f '' s).ballMeasureNoncompactness ≤ K * s.ballMeasureNoncompactness := by
  by_cases hK : K = 0
  · subst K
    simp only [ENNReal.coe_zero, zero_mul]
    rcases eq_empty_or_nonempty s with rfl | ⟨x, _⟩
    · simp
    apply ballMeasureNoncompactness_le_of_isCover (r := 0) (finite_singleton (f x))
    rintro _ ⟨y, _, rfl⟩
    exact ⟨f x, mem_singleton _, by simpa using hf y x⟩
  · unfold ballMeasureNoncompactness
    simp only [ENNReal.mul_iInf_of_ne (by exact_mod_cast hK) ENNReal.coe_ne_top,
      le_iInf_iff]
    intro r hr
    obtain ⟨N, hN, hc⟩ := externalCoveringNumber_ne_top_iff.mp hr
    simpa only [ballMeasureNoncompactness, ENNReal.coe_mul] using
      ballMeasureNoncompactness_le_of_isCover (hN.image f) (hc.image_lipschitz hf)

/-- Surjective isometries preserve the external ball-cover measure. -/
@[simp] theorem _root_.IsometryEquiv.ballMeasureNoncompactness_image (e : X ≃ᵢ Y) (s : Set X) :
    (e '' s).ballMeasureNoncompactness = s.ballMeasureNoncompactness := by
  apply le_antisymm
  · simpa using e.isometry.lipschitzWith.ballMeasureNoncompactness_image_le s
  · simpa only [image_image, e.symm_apply_apply, image_id', ENNReal.coe_one, one_mul] using
      e.symm.isometry.lipschitzWith.ballMeasureNoncompactness_image_le (e '' s)

/-- A finite measure of noncompactness is equivalent to boundedness. -/
@[simp] theorem ballMeasureNoncompactness_lt_top_iff {X : Type*} [PseudoMetricSpace X]
    {s : Set X} : s.ballMeasureNoncompactness < ⊤ ↔ Bornology.IsBounded s := by
  constructor
  · rintro hs
    obtain ⟨r, _, N, hN, hc⟩ := ballMeasureNoncompactness_lt_iff.mp hs
    exact ((Bornology.isBounded_biUnion hN).mpr fun _ _ ↦ isBounded_closedBall).subset
      hc.subset_iUnion_closedBall
  · intro hs
    rcases eq_empty_or_nonempty s with rfl | ⟨x, _⟩
    · simp
    obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball x).mp hs
    let r : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
    have hc : IsCover r s {x} := by
      intro y hy
      refine ⟨x, mem_singleton x, ?_⟩
      exact_mod_cast (hR hy).le.trans (le_max_left R 0)
    exact (ballMeasureNoncompactness_le_of_isCover (finite_singleton x) hc).trans_lt
      ENNReal.coe_lt_top

variable {E : Type*} [SeminormedAddCommGroup E] {s t : Set E}

/-- The ball-cover measure is subadditive under Minkowski addition. -/
theorem ballMeasureNoncompactness_add_le (s t : Set E) :
    (s + t).ballMeasureNoncompactness ≤
      s.ballMeasureNoncompactness + t.ballMeasureNoncompactness := by
  simp only [ballMeasureNoncompactness, ENNReal.iInf_add, ENNReal.add_iInf, le_iInf_iff]
  intro R hR r hr
  obtain ⟨N, hN, hc⟩ := externalCoveringNumber_ne_top_iff.mp hr
  obtain ⟨M, hM, hd⟩ := externalCoveringNumber_ne_top_iff.mp hR
  rw [← ENNReal.coe_add]
  apply ballMeasureNoncompactness_le_of_isCover (hN.add hM)
  rintro _ ⟨x, hx, y, hy, rfl⟩
  obtain ⟨u, hu, hxu⟩ := hc hx
  obtain ⟨v, hv, hyv⟩ := hd hy
  refine ⟨u + v, add_mem_add hu hv, ?_⟩
  exact_mod_cast (dist_add_add_le x y u v).trans
    (add_le_add (by exact_mod_cast hxu) (by exact_mod_cast hyv))

/-- Translation does not affect the measure. -/
theorem ballMeasureNoncompactness_image_add_right (s : Set E) (x : E) :
    ((fun y ↦ y + x) '' s).ballMeasureNoncompactness = s.ballMeasureNoncompactness := by
  apply le_antisymm
  · simpa using (isometry_add_right x).lipschitzWith.ballMeasureNoncompactness_image_le s
  · simpa only [image_image, add_neg_cancel_right, image_id', ENNReal.coe_one, one_mul] using
      (isometry_add_right (-x)).lipschitzWith.ballMeasureNoncompactness_image_le
        ((fun y ↦ y + x) '' s)

/-- Adding a nonempty totally bounded set leaves the measure unchanged. -/
theorem ballMeasureNoncompactness_add_eq_of_totallyBounded (s : Set E)
    (ht : TotallyBounded t) (hne : t.Nonempty) :
    (s + t).ballMeasureNoncompactness = s.ballMeasureNoncompactness := by
  refine le_antisymm ?_ ?_
  · simpa [ht.ballMeasureNoncompactness_eq_zero] using ballMeasureNoncompactness_add_le s t
  · obtain ⟨x, hx⟩ := hne
    rw [← ballMeasureNoncompactness_image_add_right s x]
    exact ballMeasureNoncompactness_mono (by rintro _ ⟨y, hy, rfl⟩; exact add_mem_add hy hx)

/-- Scalar multiplication scales the measure by the norm of the scalar, including at zero. -/
@[simp] theorem ballMeasureNoncompactness_smul {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (s : Set E) :
    (c • s).ballMeasureNoncompactness = (‖c‖₊ : ℝ≥0∞) * s.ballMeasureNoncompactness := by
  have hle := (lipschitzWith_smul c).ballMeasureNoncompactness_image_le s
  refine le_antisymm hle ?_
  by_cases hc : c = 0
  · simp [hc]
  · have hi := (lipschitzWith_smul c⁻¹).ballMeasureNoncompactness_image_le (c • s)
    have hnorm : (‖c‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hc
    have hnorm_top : (‖c‖₊ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [image_smul, inv_smul_smul₀ hc, nnNorm_inv, ENNReal.coe_inv (by simpa using hc)] at hi
    exact (ENNReal.mul_le_iff_le_inv hnorm hnorm_top).mpr hi

end Set
