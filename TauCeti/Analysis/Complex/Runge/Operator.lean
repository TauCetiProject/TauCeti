/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Quadrature
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.MeasureTheory.MeasurableSpace.Metric

/-!
# The finite-rank Runge approximation operator

A **Runge compact pair** `TauCeti.IsRungeCompactPair Ω K` consists of an open set `Ω ⊆ ℂ` and a
compact subset `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected
component of `Ω \ K` is relatively compact in `Ω`).

For any Runge compact pair `(Ω, K)` and any open neighbourhood `U ⊇ K`, this file shows that there
exists a compact neighbourhood `L` of `K` with `K ⊆ interior L ⊆ L ⊆ U ∩ Ω` such that, for every
`ε > 0`, one can choose finitely many nodes `ζ j ∈ interior L`, weights `w j`, and `Ω`-holomorphic
functions `g j` — all independent of `f` — satisfying

`sup_{z ∈ K} ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B`

for every `U`-holomorphic function `f` and every upper bound `B ≥ 0` of `‖f‖` on `L`
(`TauCeti.exists_finite_rank_runge_operator`). Choosing `ζ j`, `w j`, and `g j` independently of
`f` makes `f ↦ ∑ j, w j * f (ζ j) * g j` a finite-rank linear evaluation operator, so applying it
fiberwise preserves continuous, smooth, or holomorphic dependence on external parameters in
addition to yielding scalar uniform Runge approximation
(`TauCeti.Analysis.Complex.Runge.Approximation`).

## Main declarations and results

* `TauCeti.IsRungeCompactPair`: predicate asserting `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω`, with projection eliminators and `@[simp]` empty-set normal forms.
* `TauCeti.exists_finite_rank_runge_operator`: existence of the compact neighbourhood `L ⊆ U ∩ Ω`
  and `f`-independent finite-rank evaluation approximants with operator norm bound `ε * B`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Complex MeasureTheory Metric Set Topology
open scoped ContDiff

namespace TauCeti

/-- A **Runge compact pair**: an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω` that is filled in
`Ω` (no connected component of `Ω \ K` has compact closure contained in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

/-- Unfolding `TauCeti.IsRungeCompactPair`. -/
theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  (Iff.rfl)

/-- The ambient set of a Runge compact pair is open. -/
protected theorem IsRungeCompactPair.isOpen {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsOpen Ω :=
  h.1

/-- The compact member of a Runge compact pair is compact. -/
protected theorem IsRungeCompactPair.isCompact {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsCompact K :=
  h.2.1

/-- The compact member of a Runge compact pair is contained in the ambient set. -/
protected theorem IsRungeCompactPair.subset {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    K ⊆ Ω :=
  h.2.2.1

/-- The compact member of a Runge compact pair is filled in the ambient set. -/
protected theorem IsRungeCompactPair.isFilledIn {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsFilledIn K Ω :=
  h.2.2.2

/-- The empty set forms a Runge compact pair with `Ω` if and only if `Ω` is open. -/
@[simp]
theorem isRungeCompactPair_empty_right {Ω : Set ℂ} :
    IsRungeCompactPair Ω ∅ ↔ IsOpen Ω := by
  refine ⟨fun h => h.isOpen, fun hΩ => ⟨hΩ, isCompact_empty, empty_subset Ω, ?_⟩⟩
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    isClosed_empty hΩ (empty_subset Ω),
    filledHull_eq_self (by simpa using isPreconnected_univ)
      (by simpa using NormedSpace.unbounded_univ ℂ ℂ)]
  simp

/-- A set `K` forms a Runge compact pair with `∅` if and only if `K = ∅`. -/
@[simp]
theorem isRungeCompactPair_empty_left {K : Set ℂ} :
    IsRungeCompactPair ∅ K ↔ K = ∅ :=
  ⟨fun h => subset_empty_iff.mp h.subset,
    fun h => h ▸ isRungeCompactPair_empty_right.mpr isOpen_empty⟩

/-- **Finite-rank Runge operator.** For a Runge compact pair `(Ω, K)` and an open neighbourhood
`U ⊇ K`, there exists a compact neighbourhood `L` of `K` inside `U ∩ Ω` such that for every
`ε > 0` there are finitely many nodes `ζ j ∈ interior L`, weights `w j`, and `Ω`-holomorphic
functions `g j` (all independent of `f`) approximating every `U`-holomorphic function `f` on `K`
within `ε * B` for any upper bound `B ≥ 0` of `‖f‖` on `L`. -/
theorem exists_finite_rank_runge_operator {Ω K U : Set ℂ}
    (hRunge : IsRungeCompactPair Ω K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ,
          ∃ g : Fin N → ℂ → ℂ,
            (∀ j, ζ j ∈ interior L) ∧
            (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
            ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
              ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
                ∀ z ∈ K,
                  ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B := by
  obtain ⟨hΩ, hK, hKΩ, hfill⟩ := hRunge
  rcases K.eq_empty_or_nonempty with rfl | _
  · exact ⟨∅, isCompact_empty, by simp, empty_subset _, fun _ _ =>
      ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
        fun _ _ _ _ _ _ hz => hz.elim⟩⟩
  -- Step 1: Compact neighbourhood `L = closure W₂`, smooth cutoff `α`, and support shell `K₁`.
  obtain ⟨W₂, hW₂, hKW₂, hW₂UO, hW₂c⟩ :=
    exists_open_between_and_isCompact_closure hK (hU.inter hΩ) (subset_inter hKU hKΩ)
  let L : Set ℂ := closure W₂
  have hKL : K ⊆ interior L := hKW₂.trans (hW₂.subset_interior_iff.mpr subset_closure)
  obtain ⟨V, hV, hKV, hVW₂, hVc⟩ := exists_open_between_and_isCompact_closure hK hW₂ hKW₂
  obtain ⟨α, hα, -, hα_one, hα_cpt, hα_W₂⟩ := hVc.exists_contDiff_cutoff hW₂ hVW₂
  let K₁ : Set ℂ := tsupport α \ V
  have hK₁ : IsCompact K₁ := hα_cpt.isCompact.diff hV
  have hK₁L : K₁ ⊆ interior L :=
    sdiff_subset.trans (hα_W₂.trans (hW₂.subset_interior_iff.mpr subset_closure))
  have hK₁U : tsupport α ⊆ U := hα_W₂.trans (subset_closure.trans (hW₂UO.trans inter_subset_left))
  have hα_eq_one : EqOn α 1 V := fun y hy => by
    simpa using interior_subset (hα_one (subset_closure hy))
  have hdisj : Disjoint K K₁ := disjoint_left.mpr fun z hzK hzK₁ => hzK₁.2 (hKV hzK)
  obtain ⟨r₀, hr₀, hthick₀⟩ := hK₁.exists_thickening_subset_open isOpen_interior hK₁L
  have hball₀ : ∀ z ∈ K₁, ball z r₀ ⊆ interior L := fun z hz =>
    (ball_subset_thickening hz r₀).trans hthick₀
  -- Step 2: Uniform continuity and norm bound for the kernel `κ` on `K ×ˢ K₁`.
  let β : ℂ → ℂ := fun z => conjWirtingerDeriv (fun y => (α y : ℂ)) z 1
  let κ : ℂ → ℂ → ℂ := fun w z => (Real.pi : ℂ)⁻¹ * (w - z)⁻¹ * β z
  have hβ_cont : Continuous β :=
    ((Complex.ofRealCLM.contDiff.comp hα).of_le (by simp)).continuous_conjWirtingerDeriv_apply 1
  have hκ_cont : ContinuousOn (fun p : ℂ × ℂ => κ p.1 p.2) (K ×ˢ K₁) := by
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_)
      (hβ_cont.comp continuous_snd).continuousOn
    refine ContinuousOn.inv₀ (continuous_fst.sub continuous_snd).continuousOn ?_
    rintro ⟨w, z⟩ ⟨hw, hz⟩
    exact sub_ne_zero.mpr (hdisj.ne_of_mem hw hz)
  have hκ_uc : UniformContinuousOn (fun p : ℂ × ℂ => κ p.1 p.2) (K ×ˢ K₁) :=
    (hK.prod hK₁).uniformContinuousOn_of_continuous hκ_cont
  obtain ⟨Mκ₀, hMκ₀⟩ := (hK.prod hK₁).bddAbove_image hκ_cont.norm
  let Mκ : ℝ := max Mκ₀ 0
  have hMκ0 : 0 ≤ Mκ := le_max_right _ _
  have hMκ : ∀ w ∈ K, ∀ z ∈ K₁, ‖κ w z‖ ≤ Mκ := fun w hw z hz =>
    (hMκ₀ ⟨(w, z), ⟨hw, hz⟩, rfl⟩).trans (le_max_left _ _)
  -- Step 3: Measurable small-ball partition of `K₁` and simple-fraction approximants `g j`.
  refine ⟨L, hW₂c, hKL, hW₂UO, fun ε hε => ?_⟩
  let η : ℝ := ε / (2 * max 1 (volume.real K₁))
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, huc₁⟩ := Metric.uniformContinuousOn_iff.mp hκ_uc (η / 2) (half_pos hη)
  let δ : ℝ := min r₀ (min δ₁ (η * r₀ / (4 * (Mκ + 1))))
  have hδ : 0 < δ := lt_min hr₀ (lt_min hδ₁ (by positivity))
  obtain ⟨N, ζ, A, hζK₁, hAm, hAs, hAdisj, hAunion⟩ :=
    hK₁.totallyBounded.exists_measurable_partition_ball hK₁.isClosed.measurableSet hδ
  have hAK₁ : ∀ j, A j ⊆ K₁ := fun j => (hAs j).trans inter_subset_left
  have hAball : ∀ j, A j ⊆ ball (ζ j) δ := fun j => (hAs j).trans inter_subset_right
  let w : Fin N → ℂ := fun j => (volume.real (A j) : ℂ) * (Real.pi : ℂ)⁻¹ * β (ζ j)
  have happrox : ∀ j : Fin N, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - ζ j)⁻¹ - g z‖ < ε / (2 * (∑ i, ‖w i‖ + 1)) := fun j =>
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ
      (fun hj => hdisj.le_bot ⟨hj, hζK₁ j⟩) (by positivity)
  choose g hg_diff hg_lt using happrox
  refine ⟨N, ζ, w, g, fun j => hK₁L (hζK₁ j), hg_diff, fun f hf B hB hLf z hz => ?_⟩
  -- Step 4: Cutoff Cauchy–Pompeiu integral split across `A j` and cell quadrature bound.
  have hrep : f z = ∫ y in K₁, κ z y * f y := by
    rw [eq_pi_inv_smul_setIntegral_of_differentiableOn hV hU (hα.of_le (by simp)) hα_cpt
      hα_eq_one hK₁U hf (hKV hz), ← integral_smul]
    refine setIntegral_congr_fun ((isClosed_tsupport α).measurableSet.diff hV.measurableSet)
      fun y _ => ?_
    simp only [κ, β, smul_eq_mul]
    ring
  have hκf_int : IntegrableOn (fun y => κ z y * f y) K₁ := by
    have hz_cont : ContinuousOn (fun y => κ z y) K₁ :=
      hκ_cont.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy => ⟨hz, hy⟩
    have hf_cont : ContinuousOn f K₁ :=
      hf.continuousOn.mono (hK₁L.trans (interior_subset.trans (hW₂UO.trans inter_subset_left)))
    exact (hz_cont.mul hf_cont).integrableOn_compact hK₁
  have hsplit : ∫ y in K₁, κ z y * f y = ∑ j, ∫ y in A j, κ z y * f y := by
    rw [← hAunion, integral_iUnion_fintype hAm hAdisj fun j => hκf_int.mono_set (hAK₁ j)]
  have hsum_vol : ∑ j : Fin N, volume.real (A j) = volume.real K₁ := by
    rw [← hAunion, measureReal_iUnion_fintype hAdisj hAm
      fun j => ((measure_mono (hAK₁ j)).trans_lt hK₁.measure_lt_top).ne]
  have herr₁ : ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ (ε / 2) * B := by
    have hsum_eq : ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ =
        ∑ j, (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [w, κ]
      ring
    have hcell : ∀ j : Fin N,
        ‖(∫ y in A j, κ z y * f y) - (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j)‖ ≤
          volume.real (A j) * (η * B) := fun j => by
      have hquad := norm_setIntegral_smul_sub_measureReal_smul_le
        ((measure_mono (hAK₁ j)).trans_lt hK₁.measure_lt_top) (hAball j) (min_le_left _ _)
        (hκf_int.mono_set (hAK₁ j))
        (fun y hy => by
          have hpd : dist (z, y) (z, ζ j) < δ₁ := by
            rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
            exact (mem_ball.mp (hAball j hy)).trans_le (min_le_of_right_le (min_le_left _ _))
          rw [← dist_eq_norm]
          exact (huc₁ (z, y) ⟨hz, hAK₁ j hy⟩ (z, ζ j) ⟨hz, hζK₁ j⟩ hpd).le)
        (hf.mono ((hball₀ (ζ j) (hζK₁ j)).trans
          (interior_subset.trans (hW₂UO.trans inter_subset_left))))
        (fun u hu => hLf u (interior_subset (hball₀ (ζ j) (hζK₁ j) hu)))
      simp only [Complex.real_smul, smul_eq_mul] at hquad
      rw [← mul_assoc (volume.real (A j) : ℂ)] at hquad
      refine hquad.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hB)
        measureReal_nonneg)
      have hδ_le : δ ≤ η * r₀ / (4 * (Mκ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
      have hterm : 2 * ‖κ z (ζ j)‖ * δ / r₀ ≤ η / 2 := calc
        2 * ‖κ z (ζ j)‖ * δ / r₀
            ≤ 2 * Mκ * (η * r₀ / (4 * (Mκ + 1))) / r₀ := by
              gcongr
              exact hMκ z hz (ζ j) (hζK₁ j)
          _ = (Mκ / (Mκ + 1)) * (η / 2) := by field_simp; ring
          _ ≤ 1 * (η / 2) := by
              gcongr
              exact (div_le_one (by linarith)).mpr (by linarith)
          _ = η / 2 := one_mul _
      linarith
    rw [hrep, hsplit, hsum_eq, ← Finset.sum_sub_distrib]
    calc ‖∑ j, ((∫ y in A j, κ z y * f y) - (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j))‖
        ≤ ∑ j, ‖(∫ y in A j, κ z y * f y) - (volume.real (A j) : ℂ) * κ z (ζ j) * f (ζ j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, volume.real (A j) * (η * B) := Finset.sum_le_sum fun j _ => hcell j
      _ = volume.real K₁ * (η * B) := by rw [← Finset.sum_mul, hsum_vol]
      _ = (volume.real K₁ / max 1 (volume.real K₁)) * ((ε / 2) * B) := by simp only [η]; ring
      _ ≤ 1 * ((ε / 2) * B) := by
          gcongr
          exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_right _ _)
      _ = (ε / 2) * B := one_mul _
  -- Step 5: Replace the Cauchy kernels `(z - ζ j)⁻¹` by their `Ω`-holomorphic approximants `g j`.
  have herr₂ : ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖ ≤ (ε / 2) * B := by
    have hsum_nn : 0 ≤ ∑ i : Fin N, ‖w i‖ := Finset.sum_nonneg fun i _ => norm_nonneg (w i)
    calc ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖
        ≤ (∑ i, ‖w i‖) * (B * (ε / (2 * (∑ i, ‖w i‖ + 1)))) := by
          have hsub := norm_sum_smul_sub_smul_le (s := Finset.univ) (a := w)
            (u := fun j => f (ζ j) * (z - ζ j)⁻¹) (v := fun j => f (ζ j) * g j z) fun j _ => by
              rw [← mul_sub, norm_mul]
              exact mul_le_mul (hLf (ζ j) (interior_subset (hK₁L (hζK₁ j)))) (hg_lt j z hz).le
                (norm_nonneg _) hB
          simpa only [smul_eq_mul, mul_assoc] using hsub
      _ = ((∑ i, ‖w i‖) / (∑ i, ‖w i‖ + 1)) * ((ε / 2) * B) := by field_simp
      _ ≤ 1 * ((ε / 2) * B) := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = (ε / 2) * B := one_mul _
  calc ‖f z - ∑ j, w j * f (ζ j) * g j z‖
      = ‖(f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹) +
          (∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z)‖ := by ring_nf
    _ ≤ ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ +
        ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖ := norm_add_le _ _
    _ ≤ (ε / 2) * B + (ε / 2) * B := add_le_add herr₁ herr₂
    _ = ε * B := by ring

end TauCeti
