/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Set.Finite.List

/-!
# Asymptotic summation of symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be symbols of order `mⱼ`. Borel's
construction produces a symbol `b` of order `m₀` with `b ∼ ∑ⱼ aⱼ`, that is, such that
`b - ∑_{j < N} aⱼ` is a symbol of order `m_N` for every `N`. The series `∑ⱼ aⱼ` itself need not
converge: for each `j` only the high-frequency part `χ(ξ / tⱼ) aⱼ(x, ξ)` is summed, with radii
`tⱼ → ∞` chosen so large that the tail of the series is small in every symbol seminorm.

The main results are:

* `TauCeti.Symbol.cutoff χ t a`: the high-frequency part `χ(ξ / t) a(x, ξ)` of a symbol `a` of
  order `m`, for a frequency cutoff `χ`. It vanishes for `‖ξ‖ ≤ t`, and for `t ≠ 0`,
  `cutoff χ t a - a` is smoothing (`TauCeti.Symbol.isSmoothing_cutoff_sub`).
* `TauCeti.Symbol.tendsto_inclusion_cutoff`: as `t → ∞`, the high-frequency part tends to `0` in
  the symbols of every order `m' > m`.
* `TauCeti.Symbol.exists_asymptoticSum`: **Borel's theorem**, the existence of the asymptotic sum
  `b ∼ ∑ⱼ aⱼ`, with actual remainder symbols of order `m_N` for every `N ≥ 0`.
* `TauCeti.Symbol.isSmoothing_sub_of_asymptoticSum`: the asymptotic sum is unique modulo
  smoothing symbols.

## References

* R. Melrose, *Pseudodifferential operators on Euclidean space*, Chapter 2, MIT 18.199 (2008),
  Proposition 2.3 and (2.55)–(2.57): Borel summation for uniform symbols of orders `m - j`.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3.
-/

public section

noncomputable section

open Filter Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

/-! ### High-frequency parts -/

/-- The dilated cutoff `(x, ξ) ↦ χ(ξ / t)` is smooth. -/
private theorem contDiff_cutoff_apply (χ : FrequencyCutoff (CoordinateSpace n)) (t : ℝ) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => χ (t⁻¹ • p.2) :=
  χ.contDiff.comp (contDiff_snd.const_smul t⁻¹)

/-- The high-frequency part `χ(ξ / t) a(x, ξ)` of a symbol `a` of order `m`, cut off by the
frequency cutoff `χ` dilated to the radius `t`. It vanishes for `‖ξ‖ ≤ t`, agrees with `a` for
`‖ξ‖ ≥ 2 t` when `t > 0`, and is a symbol of order `m`. -/
def cutoff (χ : FrequencyCutoff (CoordinateSpace n)) (t : ℝ) (a : Symbol n V W m) :
    Symbol n V W m where
  coefficient p := χ (t⁻¹ • p.2) • a.coefficient p
  contDiff_coefficient := (contDiff_cutoff_apply χ t).smul a.contDiff_coefficient
  exists_bound K hK α β := by
    rcases eq_or_ne t 0 with rfl | ht
    · -- For `t = 0` the cutoff `χ(ξ / t) = χ 0` vanishes identically.
      refine ⟨0, le_rfl, fun x _ ξ => ?_⟩
      have h0 : (fun p : CoordinateSpace n × CoordinateSpace n =>
          χ ((0 : ℝ)⁻¹ • p.2) • a.coefficient p) = 0 := by
        funext p
        simp
      rw [h0, mixedDeriv_zero, norm_zero, zero_mul]
    · -- Otherwise `χ(ξ / t) a = a - (1 - χ(ξ / t)) a`, the last term vanishing for
      -- `‖ξ‖ ≥ 2 |t|`.
      have hr : ∀ x ξ, 2 * |t| ≤ ‖ξ‖ → (1 - χ (t⁻¹ • ξ)) • a.coefficient (x, ξ) = 0 :=
        fun x ξ hξ => by
          rw [χ.apply_inv_smul_eq_one_of_two_mul_abs_le_norm ht hξ, sub_self, zero_smul]
      let r : Symbol n V W m := ofBoundedFrequencySupport
        (fun p => (1 - χ (t⁻¹ • p.2)) • a.coefficient p)
        ((contDiff_const.sub (contDiff_cutoff_apply χ t)).smul a.contDiff_coefficient) (2 * |t|)
        hr
      have h : (fun p : CoordinateSpace n × CoordinateSpace n =>
          χ (t⁻¹ • p.2) • a.coefficient p) = (a - r).coefficient := by
        funext p
        simp [r, sub_smul]
      rw [h]
      exact (a - r).exists_bound K hK α β

variable (χ : FrequencyCutoff (CoordinateSpace n)) (a : Symbol n V W m)

@[simp]
theorem coefficient_cutoff (t : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoff χ t a).coefficient p = χ (t⁻¹ • p.2) • a.coefficient p := (rfl)

/-- The high-frequency part vanishes for `‖ξ‖ ≤ t`. -/
theorem coefficient_cutoff_of_norm_le {t : ℝ} {x ξ : CoordinateSpace n} (hξ : ‖ξ‖ ≤ t) :
    (cutoff χ t a).coefficient (x, ξ) = 0 := by
  rw [coefficient_cutoff, χ.apply_inv_smul_eq_zero_of_norm_le hξ, zero_smul]

/-- For `t ≠ 0` the high-frequency part agrees with the symbol for `‖ξ‖ ≥ 2 |t|`. -/
theorem coefficient_cutoff_of_two_mul_abs_le_norm {t : ℝ} (ht : t ≠ 0) {x ξ : CoordinateSpace n}
    (hξ : 2 * |t| ≤ ‖ξ‖) : (cutoff χ t a).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  rw [coefficient_cutoff, χ.apply_inv_smul_eq_one_of_two_mul_abs_le_norm ht hξ, one_smul]

/-- All mixed derivatives of the high-frequency part vanish for `‖ξ‖ < t`. -/
theorem mixedDeriv_cutoff_of_norm_lt {t : ℝ} (α β : List (Fin n)) (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : ‖ξ‖ < t) :
    mixedDeriv α β (cutoff χ t a).coefficient x ξ = 0 := by
  refine (mixedDeriv_congr_of_eventually_snd (b := 0) ?_ α β x).trans (mixedDeriv_zero α β x ξ)
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hξ] with η hη y
  exact coefficient_cutoff_of_norm_le χ a (le_of_lt hη)

/-- For `t ≠ 0` the high-frequency part differs from the symbol by a smoothing symbol: the
difference vanishes for `‖ξ‖ ≥ 2 |t|`. -/
theorem isSmoothing_cutoff_sub {t : ℝ} (ht : t ≠ 0) : (cutoff χ t a - a).IsSmoothing :=
  isSmoothing_iff.2 fun _ =>
    ⟨ofBoundedFrequencySupport _ (cutoff χ t a - a).contDiff_coefficient (2 * |t|) fun x ξ hξ => by
      rw [coefficient_sub, Pi.sub_apply, coefficient_cutoff_of_two_mul_abs_le_norm χ a ht hξ,
        sub_self],
      coefficient_ofBoundedFrequencySupport _ _ _ _⟩

/-- The mixed derivatives of the dilated cutoff `(x, ξ) ↦ χ(ξ / t) • id`, `t ≥ 1`, satisfy the
symbol estimates of order `0` uniformly in `t`. -/
private theorem exists_norm_mixedDeriv_cutoff_smul_id_le :
    ∃ E : List (Fin n) → ℝ, (∀ u, 0 ≤ E u) ∧ ∀ t : ℝ, 1 ≤ t → ∀ s u (x ξ : CoordinateSpace n),
      ‖mixedDeriv s u (fun p : CoordinateSpace n × CoordinateSpace n =>
          χ (t⁻¹ • p.2) • ContinuousLinearMap.id ℂ W) x ξ‖ ≤
        E u * (1 + ‖ξ‖ ^ 2) ^ ((0 - (u.length : ℝ)) / 2) := by
  choose C hC0 hC using fun k => χ.exists_norm_iteratedFDeriv_apply_inv_smul_le k
  refine ⟨fun u => C u.length, fun u => hC0 _, fun t ht s u x ξ => ?_⟩
  have hg : ContDiff ℝ ∞ fun η : CoordinateSpace n => χ (t⁻¹ • η) :=
    χ.contDiff.comp (contDiff_const_smul t⁻¹)
  -- The cutoff does not depend on the position, and `r ↦ r • id` is a continuous linear map.
  have hinner : coordinateDeriv u (fun η : CoordinateSpace n =>
      χ (t⁻¹ • η) • ContinuousLinearMap.id ℂ W) ξ =
      coordinateDeriv u (fun η => χ (t⁻¹ • η)) ξ • ContinuousLinearMap.id ℂ W := by
    simpa [Function.comp_def] using (ContinuousLinearMap.toSpanSingleton ℝ
      (ContinuousLinearMap.id ℂ W)).coordinateDeriv_comp_left u
      (hg.of_le (by exact_mod_cast le_top)) ξ
  simp only [mixedDeriv_def, hinner]
  rcases eq_or_ne s [] with rfl | hs
  · rw [coordinateDeriv_nil]
    calc ‖coordinateDeriv u (fun η => χ (t⁻¹ • η)) ξ • ContinuousLinearMap.id ℂ W‖
        ≤ ‖coordinateDeriv u (fun η => χ (t⁻¹ • η)) ξ‖ :=
          (norm_smul_le (coordinateDeriv u (fun η => χ (t⁻¹ • η)) ξ)
            (ContinuousLinearMap.id ℂ W)).trans (mul_le_of_le_one_right (norm_nonneg _)
              ContinuousLinearMap.norm_id_le)
      _ ≤ ‖iteratedFDeriv ℝ u.length (fun η => χ (t⁻¹ • η)) ξ‖ :=
          norm_coordinateDeriv_le u (hg.of_le (by exact_mod_cast le_top)) ξ
      _ ≤ _ := by rw [zero_sub]; exact hC _ t ht ξ
  · rw [coordinateDeriv_const _ hs, Pi.zero_apply, norm_zero]
    exact mul_nonneg (hC0 _) (by positivity)

/-- The high-frequency parts `χ(ξ / t) a`, `t ≥ 1`, satisfy the symbol estimates of order `m`
uniformly in `t`. -/
private theorem exists_bound_cutoff {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ M, 0 ≤ M ∧ ∀ t : ℝ, 1 ≤ t → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (cutoff χ t a).coefficient x ξ‖ ≤
        M * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨E, hE0, hE⟩ := exists_norm_mixedDeriv_cutoff_smul_id_le (W := W) χ
  choose D hD0 hD using fun s u => a.exists_bound K hK s u
  refine ⟨(β.sublists'.revzip.map fun u =>
      (α.sublists'.revzip.map fun s => E u.1 * D s.2 u.2).sum).sum,
    List.sum_nonneg fun _ h => ?_, fun t ht x hx ξ => ?_⟩
  · obtain ⟨u, -, rfl⟩ := List.mem_map.1 h
    exact List.sum_nonneg fun _ h' => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h'
      exact mul_nonneg (hE0 _) (hD0 _ _)
  -- `χ(ξ / t) a(x, ξ)` is the composition of `χ(ξ / t) • id` with `a(x, ξ)`.
  have hc : (cutoff χ t a).coefficient = fun p =>
      (χ (t⁻¹ • p.2) • ContinuousLinearMap.id ℂ W).comp (a.coefficient p) := by
    funext p
    simp [ContinuousLinearMap.smul_comp]
  have h := norm_mixedDeriv_comp_le (m' := 0) (C := fun _ u => E u) (D := D)
    (b := fun p => χ (t⁻¹ • p.2) • ContinuousLinearMap.id ℂ W)
    ((contDiff_cutoff_apply χ t).smul contDiff_const) a.contDiff_coefficient
    (fun s u => hE t ht s u x ξ) (fun s u => hD s u x hx ξ) α β
  rw [zero_add] at h
  rw [hc]
  exact h

/-- As `t → ∞`, the high-frequency part `χ(ξ / t) a` of a symbol of order `m` tends to `0` in the
symbols of every order `m' > m`. -/
theorem tendsto_inclusion_cutoff (h : m < m') :
    Tendsto (fun t => inclusion h.le (cutoff χ t a)) atTop (𝓝 0) := by
  rw [withSeminorms.tendsto_nhds _ 0]
  rintro ⟨K, α, β⟩ ε hε
  obtain ⟨M, hM0, hM⟩ := exists_bound_cutoff χ a K.isCompact α β
  have hlim : Tendsto (fun t : ℝ => M * t ^ (m - m')) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.2 h)).const_mul M
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with t hlt ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [seminormFamily_apply, sub_zero]
  refine lt_of_le_of_lt (seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_) hlt
  rw [coefficient_inclusion]
  rcases lt_or_ge ‖ξ‖ t with hξ | hξ
  · rw [mixedDeriv_cutoff_of_norm_lt χ a α β x hξ, norm_zero]
    positivity
  · calc ‖mixedDeriv α β (cutoff χ t a).coefficient x ξ‖
        ≤ M * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := hM t ht x hx ξ
      _ ≤ M * (t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2)) :=
          mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_mul_rpow_weight ht0 hξ h.le _) hM0
      _ = _ := by ring

/-! ### Borel's theorem -/

section Borel

variable (χ : FrequencyCutoff (CoordinateSpace n)) {m : ℕ → ℝ} (a : (j : ℕ) → Symbol n V W (m j))

/-- The radii of Borel's construction: `tⱼ → ∞`, and at the radius `tⱼ` the high-frequency part
of `aⱼ` has seminorms of order `mⱼ + 1` at most `2⁻ʲ`, for the positions in the closed ball of
radius `j` and the words of length at most `j`. -/
private theorem exists_radii :
    ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧ Tendsto t atTop atTop ∧ ∀ j (α β : List (Fin n)),
      α.length ≤ j → β.length ≤ j →
        Symbol.seminorm ⟨closedBall 0 j, isCompact_closedBall 0 j⟩ α β
          (inclusion (le_add_of_nonneg_right zero_le_one) (cutoff χ (t j) (a j)) :
            Symbol n V W (m j + 1)) ≤ (1 / 2) ^ j := by
  -- Step `j`: from some radius `Tⱼ` on, these finitely many seminorms are at most `2⁻ʲ`, since
  -- the high-frequency parts tend to `0` in order `mⱼ + 1`.
  have hstep : ∀ j, ∃ T : ℝ, ∀ τ ≥ T,
      ∀ w ∈ {l : List (Fin n) | l.length ≤ j} ×ˢ {l : List (Fin n) | l.length ≤ j},
        Symbol.seminorm ⟨closedBall 0 j, isCompact_closedBall 0 j⟩ w.1 w.2
          (inclusion (le_add_of_nonneg_right zero_le_one) (cutoff χ τ (a j)) :
            Symbol n V W (m j + 1)) ≤ (1 / 2) ^ j := by
    intro j
    have h := (withSeminorms.tendsto_nhds _ 0).1
      (tendsto_inclusion_cutoff χ (a j) (lt_add_one (m j)))
    obtain ⟨T, hT⟩ := eventually_atTop.1 (((List.finite_length_le _ j).prod
      (List.finite_length_le _ j)).eventually_all.2 fun w _ => by
        simpa only [seminormFamily_apply, sub_zero] using
          h (⟨closedBall 0 j, isCompact_closedBall 0 j⟩, w.1, w.2) ((1 / 2) ^ j) (by positivity))
    exact ⟨T, fun τ hτ w hw => (hT τ hτ w hw).le⟩
  choose T hT using hstep
  -- The radii `tⱼ = j + 1 + ∑_{i ≤ j} |Tᵢ|` satisfy `tⱼ ≥ Tⱼ` and `tⱼ ≥ j + 1`.
  have hsum : ∀ j, 0 ≤ ∑ i ∈ Finset.range (j + 1), |T i| := fun j =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨fun j => j + 1 + ∑ i ∈ Finset.range (j + 1), |T i|, fun j => by positivity,
    tendsto_atTop_mono (fun j => by linarith [hsum j]) tendsto_natCast_atTop_atTop,
    fun j α β hα hβ => hT j _ ?_ (α, β) ⟨hα, hβ⟩⟩
  have hTj : |T j| ≤ ∑ i ∈ Finset.range (j + 1), |T i| :=
    Finset.single_le_sum (f := fun i => |T i|) (fun _ _ => abs_nonneg _)
      (Finset.self_mem_range_succ j)
  linarith [le_abs_self (T j), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- For orders decreasing to `-∞` and radii as in `exists_radii`, every tail
`∑_{j ≥ N} χ(ξ / tⱼ) aⱼ` of Borel's series is a symbol of order `m_N`. -/
private theorem exists_coefficient_eq_tsum_cutoff (hm : Antitone m)
    (hlim : Tendsto m atTop atBot) {t : ℕ → ℝ} (htop : Tendsto t atTop atTop)
    (ht : ∀ j (α β : List (Fin n)), α.length ≤ j → β.length ≤ j →
      Symbol.seminorm ⟨closedBall 0 j, isCompact_closedBall 0 j⟩ α β
        (inclusion (le_add_of_nonneg_right zero_le_one) (cutoff χ (t j) (a j)) :
          Symbol n V W (m j + 1)) ≤ (1 / 2) ^ j) (N : ℕ) :
    ∃ b : Symbol n V W (m N), ∀ p,
      b.coefficient p = ∑' i, (cutoff χ (t (i + N)) (a (i + N))).coefficient p := by
  have hle : ∀ i, m (i + N) ≤ m N := fun i => hm (Nat.le_add_left N i)
  refine (exists_coefficient_eq_tsum (fun i => inclusion (hle i) (cutoff χ (t (i + N)) (a (i + N))))
    (htop.comp (tendsto_add_atTop_nat N))
    (fun i x ξ hξ => by rw [coefficient_inclusion]; exact coefficient_cutoff_of_norm_le χ _ hξ.le)
    fun K α β => ?_).imp
    fun b hb p => by simpa using hb p
  -- From the index on where `K` lies in the ball of radius `j`, `|α|, |β| ≤ j` and
  -- `mⱼ + 1 ≤ m_N`, the seminorms are at most `2⁻ʲ ≤ 2⁻ⁱ`, `j = i + N`.
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hlim.eventually_le_atBot (m N - 1))
  refine Summable.of_norm_bounded_eventually_nat (g := fun i => (1 / 2 : ℝ) ^ i)
    summable_geometric_two ?_
  filter_upwards [eventually_ge_atTop J, eventually_ge_atTop ⌈R⌉₊,
    eventually_ge_atTop α.length, eventually_ge_atTop β.length] with i hiJ hiR hiα hiβ
  have hj : i ≤ i + N := Nat.le_add_right i N
  have hK : K ≤ ⟨closedBall 0 (i + N : ℕ), isCompact_closedBall 0 (i + N : ℕ)⟩ := fun x hx =>
    closedBall_subset_closedBall ((Nat.le_ceil R).trans (by exact_mod_cast hiR.trans hj)) (hR hx)
  have hmN : m (i + N) + 1 ≤ m N := by linarith [hJ (i + N) (hiJ.trans hj)]
  have hincl : (inclusion (hle i) (cutoff χ (t (i + N)) (a (i + N))) : Symbol n V W (m N)) =
      inclusion hmN (inclusion (le_add_of_nonneg_right zero_le_one)
        (cutoff χ (t (i + N)) (a (i + N)))) := by
    ext1
    simp
  rw [Real.norm_of_nonneg (apply_nonneg _ _), hincl]
  exact (seminorm_inclusion_le _ _ _ _ _).trans ((seminorm_mono hK _ _ _).trans
    ((ht (i + N) α β (hiα.trans hj) (hiβ.trans hj)).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)))

end Borel

/-- **Borel's theorem on asymptotic summation.** Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞`
and `aⱼ` symbols of order `mⱼ`. There is a symbol `b` of order `m₀` such that for every `N ≥ 0`,
`b - ∑_{j < N} aⱼ` is a symbol of order `m_N`. -/
theorem exists_asymptoticSum (m : ℕ → ℝ) (hm : Antitone m) (hlim : Tendsto m atTop atBot)
    (a : (j : ℕ) → Symbol n V W (m j)) :
    ∃ b : Symbol n V W (m 0), ∀ N, ∃ r : Symbol n V W (m N), ∀ p,
      r.coefficient p = b.coefficient p - ∑ j ∈ Finset.range N, (a j).coefficient p := by
  -- `b = ∑ⱼ χ(ξ / tⱼ) aⱼ` for suitable radii `tⱼ → ∞`.
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  obtain ⟨t, ht0, htop, ht⟩ := exists_radii χ a
  obtain ⟨b, hb⟩ := exists_coefficient_eq_tsum_cutoff χ a hm hlim htop ht 0
  -- `i + 0` reduces to `i`.
  replace hb : ∀ p, b.coefficient p = ∑' j, (cutoff χ (t j) (a j)).coefficient p := hb
  refine ⟨b, fun N => ?_⟩
  -- `b - ∑_{j < N} aⱼ = ∑_{j ≥ N} χ(ξ / tⱼ) aⱼ + ∑_{j < N} (χ(ξ / tⱼ) aⱼ - aⱼ)`, where the tail
  -- has order `m_N` and each `χ(ξ / tⱼ) aⱼ - aⱼ` is smoothing.
  obtain ⟨bN, hbN⟩ := exists_coefficient_eq_tsum_cutoff χ a hm hlim htop ht N
  choose s hs using fun j => isSmoothing_iff.1 (isSmoothing_cutoff_sub χ (a j) (ht0 j).ne') (m N)
  refine ⟨bN + ∑ j ∈ Finset.range N, s j, fun p => ?_⟩
  have hsumm : Summable fun j => (cutoff χ (t j) (a j)).coefficient p := by
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (htop.eventually_gt_atTop ‖p.2‖)
    exact summable_of_ne_finset_zero (s := Finset.range J) fun j hj =>
      coefficient_cutoff_of_norm_le χ _ (hJ j (by simpa using hj)).le
  rw [coefficient_add, coefficient_sum, Pi.add_apply, Finset.sum_apply, hbN, hb,
    ← hsumm.sum_add_tsum_nat_add N]
  simp only [hs, coefficient_sub, Pi.sub_apply, Finset.sum_sub_distrib]
  abel

/-- The asymptotic sum of `Symbol.exists_asymptoticSum` is unique modulo smoothing symbols: two
symbols `b`, `b'` of order `m₀` such that `b - ∑_{j < N} aⱼ` and `b' - ∑_{j < N} aⱼ` have order
`m_N` for every `N` differ by a smoothing symbol. -/
theorem isSmoothing_sub_of_asymptoticSum {m : ℕ → ℝ} (hlim : Tendsto m atTop atBot)
    {a : (j : ℕ) → Symbol n V W (m j)} {b b' : Symbol n V W (m 0)}
    (hb : ∀ N, ∃ r : Symbol n V W (m N), ∀ p,
      r.coefficient p = b.coefficient p - ∑ j ∈ Finset.range N, (a j).coefficient p)
    (hb' : ∀ N, ∃ r : Symbol n V W (m N), ∀ p,
      r.coefficient p = b'.coefficient p - ∑ j ∈ Finset.range N, (a j).coefficient p) :
    (b - b').IsSmoothing := isSmoothing_iff.2 fun m'' => by
  obtain ⟨N, hN⟩ := (hlim.eventually_le_atBot m'').exists
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨r', hr'⟩ := hb' N
  exact ⟨inclusion hN (r - r'), funext fun p => by simp [hr, hr']⟩

end Symbol

end TauCeti
