/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Normed.Module.DoubleDual
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
(`TauCeti.exists_finite_rank_runge_operator`). With the same nodes, weights and functions the
estimate holds for holomorphic functions with values in any complex normed space
(`TauCeti.norm_sub_sum_smul_le_of_scalar`). Choosing `ζ j`, `w j`, and `g j` independently of
`f` makes `f ↦ ∑ j, w j * f (ζ j) * g j` a finite-rank linear evaluation operator, so applying it
fiberwise preserves continuous, smooth, or holomorphic dependence on external parameters in
addition to yielding scalar uniform Runge approximation
(`TauCeti.Analysis.Complex.Runge.Approximation`).

## Main declarations and results

* `TauCeti.IsRungeCompactPair`: predicate asserting `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω`, with projection eliminators and `@[simp]` empty-set normal forms.
* `TauCeti.exists_finite_rank_runge_operator`: existence of the compact neighbourhood `L ⊆ U ∩ Ω`
  and `f`-independent finite-rank evaluation approximants with operator norm bound `ε * B`.
* `TauCeti.norm_sub_sum_smul_le_of_scalar`: the same estimate for vector-valued functions.

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
  let Mκ : ℝ := max Mκ₀ 1
  have hMκ : ∀ w ∈ K, ∀ z ∈ K₁, ‖κ w z‖ ≤ Mκ := fun w hw z hz =>
    (hMκ₀ ⟨(w, z), ⟨hw, hz⟩, rfl⟩).trans (le_max_left _ _)
  -- Step 3: Measurable small-ball partition of `K₁` and simple-fraction approximants `g j`.
  refine ⟨L, hW₂c, hKL, hW₂UO, fun ε hε => ?_⟩
  let V₁ : ℝ := max (volume.real K₁) 1
  have hV₁ : 0 < V₁ := zero_lt_one.trans_le (le_max_right _ _)
  let η : ℝ := ε / 2 / V₁
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, huc₁⟩ := Metric.uniformContinuousOn_iff.mp hκ_uc (η / 2) (half_pos hη)
  let δ : ℝ := min r₀ (min δ₁ (η / 2 * r₀ / (2 * Mκ)))
  have hδ : 0 < δ := lt_min hr₀ (lt_min hδ₁ (by positivity))
  obtain ⟨N, ζ, A, hζK₁, hAm, hAs, hAdisj, hAunion⟩ :=
    hK₁.totallyBounded.exists_measurable_partition_ball hK₁.isClosed.measurableSet hδ
  have hAK₁ : ∀ j, A j ⊆ K₁ := fun j => (hAs j).trans inter_subset_left
  have hAball : ∀ j, A j ⊆ ball (ζ j) δ := fun j => (hAs j).trans inter_subset_right
  let w : Fin N → ℂ := fun j => (volume.real (A j) : ℂ) * (Real.pi : ℂ)⁻¹ * β (ζ j)
  let W : ℝ := max (∑ i, ‖w i‖) 1
  have hW : 0 < W := zero_lt_one.trans_le (le_max_right _ _)
  have happrox : ∀ j : Fin N, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - ζ j)⁻¹ - g z‖ < ε / 2 / W := fun j =>
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ
      (fun hj => hdisj.le_bot ⟨hj, hζK₁ j⟩) (by positivity)
  choose g hg_diff hg_lt using happrox
  refine ⟨N, ζ, w, g, fun j => hK₁L (hζK₁ j), hg_diff, fun f hf B hB hLf z hz => ?_⟩
  -- Step 4: Cutoff Cauchy–Pompeiu representation and partition quadrature bound on `K₁`.
  have hrep : f z = ∫ y in K₁, κ z y • f y := by
    rw [eq_pi_inv_smul_setIntegral_of_differentiableOn hV hU (hα.of_le (by simp)) hα_cpt
      hα_eq_one hK₁U hf (hKV hz), ← integral_smul]
    refine setIntegral_congr_fun ((isClosed_tsupport α).measurableSet.diff hV.measurableSet)
      fun y _ => ?_
    simp only [κ, β, smul_eq_mul]
    ring
  have hκf_int : IntegrableOn (fun y => κ z y • f y) K₁ := by
    have hz_cont : ContinuousOn (fun y => κ z y) K₁ :=
      hκ_cont.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy => ⟨hz, hy⟩
    have hf_cont : ContinuousOn f K₁ :=
      hf.continuousOn.mono (hK₁L.trans (interior_subset.trans (hW₂UO.trans inter_subset_left)))
    exact (hz_cont.smul hf_cont).integrableOn_compact hK₁
  have herr₁ : ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ ≤ (ε / 2) * B := by
    have hsum_eq : ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ =
        ∑ j, volume.real (A j) • (κ z (ζ j) • f (ζ j)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [w, κ, Complex.real_smul, smul_eq_mul]
      ring
    have hquad := norm_setIntegral_smul_sub_sum_measureReal_smul_le
      hK₁.measure_lt_top hAm hAdisj hAunion hAball (min_le_left _ _) hκf_int
      (fun j y hy => by
        have hpd : dist (z, y) (z, ζ j) < δ₁ := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
          exact (mem_ball.mp (hAball j hy)).trans_le (min_le_of_right_le (min_le_left _ _))
        rw [← dist_eq_norm]
        exact (huc₁ (z, y) ⟨hz, hAK₁ j hy⟩ (z, ζ j) ⟨hz, hζK₁ j⟩ hpd).le)
      (fun j => hMκ z hz (ζ j) (hζK₁ j))
      (fun j => hf.mono ((hball₀ (ζ j) (hζK₁ j)).trans
        (interior_subset.trans (hW₂UO.trans inter_subset_left))))
      (fun j u hu => hLf u (interior_subset (hball₀ (ζ j) (hζK₁ j) hu)))
    have hδ_le : δ ≤ η / 2 * r₀ / (2 * Mκ) := (min_le_right _ _).trans (min_le_right _ _)
    have hterm : 2 * Mκ * δ / r₀ ≤ η / 2 := calc
      2 * Mκ * δ / r₀
          ≤ 2 * Mκ * (η / 2 * r₀ / (2 * Mκ)) / r₀ := by gcongr
        _ = η / 2 := by
            rw [mul_div_cancel₀ _ (by positivity), mul_div_cancel_right₀ _ hr₀.ne']
    rw [hrep, hsum_eq]
    refine hquad.trans ?_
    calc volume.real K₁ * ((η / 2 + 2 * Mκ * δ / r₀) * B)
        ≤ V₁ * ((η / 2 + η / 2) * B) := by
          have hKV₁ : volume.real K₁ ≤ V₁ := le_max_left _ _
          gcongr
      _ = (ε / 2) * B := by
          rw [add_halves, ← mul_assoc, mul_div_cancel₀ _ hV₁.ne']
  -- Step 5: Replace the Cauchy kernels `(z - ζ j)⁻¹` by their `Ω`-holomorphic approximants `g j`.
  have herr₂ : ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖ ≤ (ε / 2) * B := by
    calc ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖
        ≤ (∑ i, ‖w i‖) * (B * (ε / 2 / W)) := by
          have hsub := norm_sum_smul_sub_smul_le (s := Finset.univ) (a := w)
            (u := fun j => f (ζ j) * (z - ζ j)⁻¹) (v := fun j => f (ζ j) * g j z) fun j _ => by
              rw [← mul_sub, norm_mul]
              exact mul_le_mul (hLf (ζ j) (interior_subset (hK₁L (hζK₁ j)))) (hg_lt j z hz).le
                (norm_nonneg _) hB
          simpa only [smul_eq_mul, mul_assoc] using hsub
      _ ≤ W * (B * (ε / 2 / W)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = (ε / 2) * B := by rw [← mul_assoc, mul_right_comm, mul_div_cancel₀ _ hW.ne']
  calc ‖f z - ∑ j, w j * f (ζ j) * g j z‖
      ≤ ‖f z - ∑ j, w j * f (ζ j) * (z - ζ j)⁻¹‖ +
          ‖∑ j, w j * f (ζ j) * (z - ζ j)⁻¹ - ∑ j, w j * f (ζ j) * g j z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε / 2) * B + (ε / 2) * B := add_le_add herr₁ herr₂
    _ = ε * B := by ring

/-- **The finite-rank Runge estimate for vector-valued functions.** If a finite-rank evaluation
operator `f ↦ ∑ j, w j * f (ζ j) * g j` satisfies the Runge estimate on `K` for every scalar
function holomorphic on `U`, then with the same nodes, weights and output functions it satisfies
it for every function holomorphic on `U` with values in a complex normed space. -/
theorem norm_sub_sum_smul_le_of_scalar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {U L K : Set ℂ} {N : ℕ} {ζ w : Fin N → ℂ} {g : Fin N → ℂ → ℂ} {ε : ℝ}
    (hA : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
      ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B)
    {f : ℂ → W} (hf : DifferentiableOn ℂ f U) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ z ∈ L, ‖f z‖ ≤ B) {z : ℂ} (hz : z ∈ K) :
    ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B := by
  -- The estimate for the zero function shows that the bound `ε * B` is nonnegative.
  have hεB : 0 ≤ ε * B := (norm_nonneg _).trans <|
    hA 0 (differentiableOn_const 0) B hB (fun _ _ ↦ by simpa using hB) z hz
  refine NormedSpace.norm_le_dual_bound ℂ _ hεB fun φ ↦ ?_
  have hφ := hA (fun z ↦ φ (f z)) (φ.differentiable.comp_differentiableOn hf) (‖φ‖ * B)
    (by positivity) (fun z' hz' ↦ (φ.le_opNorm _).trans (by gcongr; exact hfB z' hz')) z hz
  calc ‖φ (f z - ∑ j, (w j * g j z) • f (ζ j))‖
      = ‖φ (f z) - ∑ j, w j * φ (f (ζ j)) * g j z‖ := by
        simp only [map_sub, map_sum, map_smul, smul_eq_mul, mul_right_comm]
    _ ≤ ε * (‖φ‖ * B) := hφ
    _ = ε * B * ‖φ‖ := by ring

end TauCeti
