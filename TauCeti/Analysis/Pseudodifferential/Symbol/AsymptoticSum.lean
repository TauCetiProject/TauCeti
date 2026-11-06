/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Asymptotic sums of symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be a symbol of order `mⱼ`. A symbol
`b` is an *asymptotic sum* of the `aⱼ`, written `b ∼ ∑ⱼ aⱼ`, if for every `N` the remainder
`b - ∑_{j<N} aⱼ` is a symbol of order `m_N` (`TauCeti.Symbol.IsAsymptoticSum`). The series
`∑ⱼ aⱼ` need not converge; this is the symbol-calculus analogue of Borel's theorem that every formal
power series is the Taylor series of a smooth function. Asymptotic sums are how the symbol calculus
assembles a symbol from its terms: the classical expansions `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)`, and the
symbols of compositions, adjoints and parametrices, are produced as asymptotic sums.

## Main results

* `TauCeti.Symbol.exists_asymptoticSum` (Borel summation): every such sequence has an asymptotic
  sum of order `m₀`. The orders may repeat, and the estimates are local in the position.
* `TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`: the asymptotic sums form
  exactly one class modulo smoothing symbols.

## Implementation notes

The asymptotic sum is `b(x, ξ) = ∑ⱼ χ(ξ / tⱼ) aⱼ(x, ξ)` for a frequency cutoff `χ` and radii
`tⱼ → ∞`. The rescaled cutoffs satisfy the order-zero estimates uniformly in the radius
(`TauCeti.FrequencyCutoff.exists_norm_iteratedFDeriv_comp_smul_le`), and the `j`-th term vanishes
for `‖ξ‖ < tⱼ`, so its estimates of order `mⱼ + 1` have constants of size `O(1 / tⱼ)`. The radii
are chosen so that these constants are at most `2⁻ʲ` for the first `j` estimates in an enumeration
of all of them (a ball of positions, position derivatives, frequency derivatives). The series is
locally finite in the frequency, hence smooth with termwise derivatives. For each `N` its tail
beyond `N` has order `m_N`: once `mⱼ ≤ m_N - 1` the remaining estimates are summable, and the
finitely many terms before have order at most `m_N`. The first `N` cut-off terms differ from the
`aⱼ` by a symbol vanishing at large frequencies.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3.
* R. Melrose, *Introduction to Microlocal Analysis*, Proposition 2.3 and (2.55)–(2.57).
-/

public section

noncomputable section

open Filter Finset Metric
open scoped ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} {orders : ℕ → ℝ}

/-- A symbol `b` is an *asymptotic sum* of symbols `a j` of orders `orders j`, written
`b ∼ ∑ⱼ a j`, if for every `N` the remainder `b - ∑_{j<N} a j` is a symbol of order `orders N`. -/
def IsAsymptoticSum (a : (j : ℕ) → Symbol n V W (orders j)) (b : Symbol n V W m) : Prop :=
  ∀ N : ℕ, ∃ r : Symbol n V W (orders N), ∀ x ξ,
    b.coefficient (x, ξ) - ∑ j ∈ range N, (a j).coefficient (x, ξ) = r.coefficient (x, ξ)

theorem isAsymptoticSum_iff {a : (j : ℕ) → Symbol n V W (orders j)} {b : Symbol n V W m} :
    IsAsymptoticSum a b ↔ ∀ N : ℕ, ∃ r : Symbol n V W (orders N), ∀ x ξ,
      b.coefficient (x, ξ) - ∑ j ∈ range N, (a j).coefficient (x, ξ) = r.coefficient (x, ξ) :=
  Iff.rfl

section Uniqueness

variable {a : (j : ℕ) → Symbol n V W (orders j)} {b b' : Symbol n V W m}

/-- Adding a smoothing symbol to an asymptotic sum gives another asymptotic sum. -/
theorem IsAsymptoticSum.of_isSmoothing_sub (hb : IsAsymptoticSum a b)
    (h : (b' - b).IsSmoothing) : IsAsymptoticSum a b' := by
  refine isAsymptoticSum_iff.2 fun N => ?_
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨c, hc⟩ := isSmoothing_iff.1 h (orders N)
  refine ⟨c + r, fun x ξ => ?_⟩
  rw [coefficient_add, Pi.add_apply, ← hr, hc, coefficient_sub, Pi.sub_apply]
  abel

/-- Asymptotic sums are unique modulo smoothing symbols, since the orders tend to `-∞`. -/
theorem IsAsymptoticSum.isSmoothing_sub (hlim : Tendsto orders atTop atBot)
    (hb : IsAsymptoticSum a b) (hb' : IsAsymptoticSum a b') : (b - b').IsSmoothing := by
  refine isSmoothing_iff.2 fun m' => ?_
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_le_atBot m')).exists
  obtain ⟨r, hr⟩ := hb N
  obtain ⟨r', hr'⟩ := hb' N
  refine ⟨inclusion hN (r - r'), funext fun p => ?_⟩
  rw [coefficient_inclusion, coefficient_sub, coefficient_sub, Pi.sub_apply, Pi.sub_apply,
    ← hr p.1 p.2, ← hr' p.1 p.2]
  abel

/-- The asymptotic sums of a sequence of symbols with orders tending to `-∞` form exactly one
class modulo smoothing symbols. -/
theorem IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub (hlim : Tendsto orders atTop atBot)
    (hb : IsAsymptoticSum a b) : IsAsymptoticSum a b' ↔ (b' - b).IsSmoothing :=
  ⟨fun hb' => hb'.isSmoothing_sub hlim hb, hb.of_isSmoothing_sub⟩

end Uniqueness

/-! ### Cutting a symbol off at a large frequency radius -/

section Cutoff

variable (χ : FrequencyCutoff (CoordinateSpace n))

/-- The smooth map `(x, ξ) ↦ χ(ξ / t) a(x, ξ)`. -/
private theorem contDiff_cutoff {a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (ha : ContDiff ℝ ∞ a) (t : ℝ) : ContDiff ℝ ∞ fun p => χ (t⁻¹ • p.2) • a p :=
  (χ.contDiff.comp (contDiff_snd.const_smul t⁻¹)).smul ha

/-- The multiplier `(x, ξ) ↦ χ(ξ / t) • id`, `t ≥ 1`, satisfies the order-zero estimates uniformly
in `t`. -/
private theorem exists_norm_mixedDeriv_cutoff_id_le (u : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ s x ξ, ‖mixedDeriv s u
      (fun p : CoordinateSpace n × CoordinateSpace n => χ (t⁻¹ • p.2) • ContinuousLinearMap.id ℂ W)
      x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - u.length) / 2) := by
  obtain ⟨C, hC, hCt⟩ := χ.exists_norm_iteratedFDeriv_comp_smul_le u.length
  refine ⟨C, hC, fun t ht s x ξ => ?_⟩
  rcases eq_or_ne s [] with rfl | hs
  · have hφ : ContDiff ℝ ∞ fun η : CoordinateSpace n => χ (t⁻¹ • η) :=
      χ.contDiff.comp (contDiff_id.const_smul t⁻¹)
    rw [mixedDeriv_nil_comp_snd (fun η => χ (t⁻¹ • η) • ContinuousLinearMap.id ℂ W)]
    refine (norm_coordinateDeriv_le u (f := fun η => χ (t⁻¹ • η) • ContinuousLinearMap.id ℂ W)
      ((hφ.smul contDiff_const).of_le
      (by exact_mod_cast le_top)) ξ).trans ?_
    rw [iteratedFDeriv_smul_const_apply (hφ.of_le (by exact_mod_cast le_top)).contDiffAt]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id, one_mul, zero_sub]
    calc ‖ContinuousLinearMap.id ℂ W‖ * ‖iteratedFDeriv ℝ u.length (fun η => χ (t⁻¹ • η)) ξ‖
        ≤ 1 * ‖iteratedFDeriv ℝ u.length (fun η => χ (t⁻¹ • η)) ξ‖ := by
          gcongr
          exact ContinuousLinearMap.norm_id_le
      _ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-(u.length : ℝ) / 2) := by
          rw [one_mul]
          exact hCt t ht ξ
  · rw [mixedDeriv_comp_snd (fun η => χ (t⁻¹ • η) • ContinuousLinearMap.id ℂ W) hs, norm_zero]
    exact mul_nonneg hC (rpow_weight_pos ξ _).le

/-- Cutting a symbol of order `m` off at the radius `t ≥ 1` keeps its estimates of order `m`, with
constants independent of `t`. -/
private theorem exists_norm_mixedDeriv_cutoff_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  choose C hC0 hC using fun u : List (Fin n) => exists_norm_mixedDeriv_cutoff_id_le (W := W) χ u
  choose D hD0 hD using fun s u => a.exists_bound K hK s u
  refine ⟨max ((β.sublists'.revzip.map fun u =>
    (α.sublists'.revzip.map fun s => C u.1 * D s.2 u.2).sum).sum) 0, le_max_right _ _,
    fun t ht x hx ξ => ?_⟩
  have hcomp : (fun p => (χ (t⁻¹ • p.2) • ContinuousLinearMap.id ℂ W).comp (a.coefficient p)) =
      fun p => χ (t⁻¹ • p.2) • a.coefficient p := by
    funext p
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]
  have h := norm_mixedDeriv_comp_le (m' := 0)
    (contDiff_cutoff χ (a := fun _ => ContinuousLinearMap.id ℂ W) contDiff_const t)
    a.contDiff_coefficient
    (C := fun _ u => C u) (fun s u => hC u t ht s x ξ) (fun s u => hD s u x hx ξ) α β
  rw [hcomp, zero_add] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_weight_pos ξ _).le)

/-- The cut-off map `χ(ξ / t) a(x, ξ)` vanishes, with all its derivatives, for `‖ξ‖ < t`. -/
private theorem mixedDeriv_cutoff_eq_zero (a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    {t : ℝ} (ht : 0 < t) (α β : List (Fin n)) {x ξ : CoordinateSpace n} (hξ : ‖ξ‖ < t) :
    mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a p) x ξ = 0 := by
  have h : (fun p : CoordinateSpace n × CoordinateSpace n => χ (t⁻¹ • p.2) • a p) =ᶠ[nhds (x, ξ)]
      0 := by
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hξ] with p hp
    rw [χ.apply_eq_zero_of_norm_le_one, zero_smul, Pi.zero_apply]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]
    exact le_of_lt hp
  rw [h.mixedDeriv, mixedDeriv_zero]

/-- For large radii `t`, the cut-off symbol `χ(ξ / t) a(x, ξ)` satisfies a given estimate of order
`m + 1` with an arbitrarily small constant. -/
private theorem eventually_norm_mixedDeriv_cutoff_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        ε * (1 + ‖ξ‖ ^ 2) ^ ((m + 1 - β.length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_cutoff_le χ a hK α β
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (C / ε)] with t ht1 htC x hx ξ
  have ht0 : 0 < t := by linarith
  rcases lt_or_ge ‖ξ‖ t with hξ | hξ
  · rw [mixedDeriv_cutoff_eq_zero χ _ ht0 α β hξ, norm_zero]
    exact mul_nonneg hε.le (rpow_weight_pos ξ _).le
  · -- At frequencies `‖ξ‖ ≥ t` we have `⟨ξ⟩⁻¹ ≤ t⁻¹`.
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m + 1 - β.length) / 2) * (1 + ‖ξ‖ ^ 2) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    have hdec : (1 + ‖ξ‖ ^ 2) ^ (-(1 / 2 : ℝ)) ≤ t⁻¹ := by
      calc (1 + ‖ξ‖ ^ 2) ^ (-(1 / 2 : ℝ)) ≤ (t ^ 2) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by norm_num)
        _ = t⁻¹ := by
            rw [Real.rpow_neg (sq_nonneg t), ← Real.sqrt_eq_rpow, Real.sqrt_sq ht0.le]
    have hCε : C * t⁻¹ ≤ ε := by
      rw [← div_eq_mul_inv, div_le_iff₀ ht0]
      rw [div_le_iff₀ hε] at htC
      linarith
    calc ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖
        ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := hC t ht1 x hx ξ
      _ = C * (1 + ‖ξ‖ ^ 2) ^ (-(1 / 2 : ℝ)) * (1 + ‖ξ‖ ^ 2) ^ ((m + 1 - β.length) / 2) := by
          rw [hw]
          ring
      _ ≤ C * t⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m + 1 - β.length) / 2) := by gcongr
      _ ≤ ε * (1 + ‖ξ‖ ^ 2) ^ ((m + 1 - β.length) / 2) :=
          mul_le_mul_of_nonneg_right hCε (rpow_weight_pos ξ _).le

end Cutoff

/-! ### Series that are locally finite in the frequency -/

section LocallyFinite

variable {g : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}

/-- A series whose `j`-th term vanishes for `‖ξ‖ < j` is a finite sum at bounded frequencies. -/
private theorem tsum_eq_sum_range_of_norm_lt (hg : ∀ (j : ℕ) p, ‖p.2‖ < j → g j p = 0) {J : ℕ}
    {p : CoordinateSpace n × CoordinateSpace n} (hp : ‖p.2‖ < J) :
    ∑' j, g j p = ∑ j ∈ range J, g j p :=
  tsum_eq_sum fun j hj => hg j p (hp.trans_le (by exact_mod_cast not_lt.1 (mem_range.not.1 hj)))

private theorem tsum_eventuallyEq_sum_range (hg : ∀ (j : ℕ) p, ‖p.2‖ < j → g j p = 0) {J : ℕ}
    {p : CoordinateSpace n × CoordinateSpace n} (hp : ‖p.2‖ < J) :
    (fun q => ∑' j, g j q) =ᶠ[nhds p] fun q => ∑ j ∈ range J, g j q := by
  filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hp] with q hq
  exact tsum_eq_sum_range_of_norm_lt hg hq

private theorem contDiff_tsum_of_norm_lt (hg : ∀ (j : ℕ) p, ‖p.2‖ < j → g j p = 0)
    (hgc : ∀ j, ContDiff ℝ ∞ (g j)) : ContDiff ℝ ∞ fun q => ∑' j, g j q :=
  contDiff_iff_contDiffAt.2 fun p => by
    obtain ⟨J, hJ⟩ := exists_nat_gt ‖p.2‖
    exact (ContDiff.sum fun j _ => hgc j).contDiffAt.congr_of_eventuallyEq
      (tsum_eventuallyEq_sum_range hg hJ)

private theorem mixedDeriv_tsum_of_norm_lt (hg : ∀ (j : ℕ) p, ‖p.2‖ < j → g j p = 0)
    (hgc : ∀ j, ContDiff ℝ ∞ (g j)) (α β : List (Fin n)) {x ξ : CoordinateSpace n} {J : ℕ}
    (hJ : ‖ξ‖ < J) :
    mixedDeriv α β (fun q => ∑' j, g j q) x ξ = ∑ j ∈ range J, mixedDeriv α β (g j) x ξ := by
  rw [(tsum_eventuallyEq_sum_range hg (p := (x, ξ)) hJ).mixedDeriv, mixedDeriv_sum fun j _ => hgc j]

end LocallyFinite

/-! ### Borel summation -/

section Borel

variable (χ : FrequencyCutoff (CoordinateSpace n))

/-- The choice of the cutoff radii: `tⱼ ≥ j + 1`, and the `j`-th cut-off term satisfies each of the
first `j` estimates, in an enumeration of the triples (radius of a ball of positions, position
derivatives, frequency derivatives), in order `orders j + 1` with constant `2⁻ʲ`. -/
private theorem exists_radii (a : (j : ℕ) → Symbol n V W (orders j)) :
    ∃ t : ℕ → ℝ, (∀ j : ℕ, (j : ℝ) + 1 ≤ t j) ∧ ∀ (j k : ℕ) (α β : List (Fin n)),
      Encodable.encode (k, α, β) ≤ j → ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((orders j + 1 - β.length) / 2) := by
  have key : ∀ j : ℕ, ∀ᶠ s : ℝ in atTop, (j : ℝ) + 1 ≤ s ∧ ∀ i ∈ range (j + 1),
      ∀ q ∈ Encodable.decode (α := ℕ × List (Fin n) × List (Fin n)) i,
        ∀ x ∈ closedBall (0 : CoordinateSpace n) q.1, ∀ ξ,
          ‖mixedDeriv q.2.1 q.2.2 (fun p => χ (s⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
            (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((orders j + 1 - q.2.2.length) / 2) := by
    intro j
    refine (eventually_ge_atTop _).and ((eventually_all_finset _).2 fun i _ => ?_)
    cases Encodable.decode (α := ℕ × List (Fin n) × List (Fin n)) i with
    | none => exact Eventually.of_forall fun _ q hq => by cases hq
    | some q =>
      filter_upwards [eventually_norm_mixedDeriv_cutoff_le χ (a j) (isCompact_closedBall 0 q.1)
        q.2.1 q.2.2 (by positivity : (0 : ℝ) < (1 / 2) ^ j)] with s hs q' hq'
      cases hq'
      exact hs
  choose t ht using fun j => (key j).exists
  exact ⟨t, fun j => (ht j).1, fun j k α β hj x hx ξ =>
    (ht j).2 _ (mem_range.2 (Nat.lt_succ_of_le hj)) (k, α, β) (Encodable.encodek _) x hx ξ⟩

variable {a : (j : ℕ) → Symbol n V W (orders j)} {t : ℕ → ℝ}

/-- With radii as in `exists_radii`, the tail `∑_{j ≥ N} χ(ξ / tⱼ) aⱼ(x, ξ)` is a symbol of order
`orders N`. -/
private theorem exists_tail (hmono : Antitone orders) (hlim : Tendsto orders atTop atBot)
    (ht1 : ∀ j : ℕ, (j : ℝ) + 1 ≤ t j)
    (ht : ∀ (j k : ℕ) (α β : List (Fin n)),
      Encodable.encode (k, α, β) ≤ j → ∀ x ∈ closedBall (0 : CoordinateSpace n) k, ∀ ξ,
        ‖mixedDeriv α β (fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((orders j + 1 - β.length) / 2))
    (N : ℕ) : ∃ T : Symbol n V W (orders N), ∀ p,
      T.coefficient p = ∑' i, χ ((t (i + N))⁻¹ • p.2) • (a (i + N)).coefficient p := by
  set g : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun i p => χ ((t (i + N))⁻¹ • p.2) • (a (i + N)).coefficient p with hg
  have ht0 : ∀ j, 0 < t j := fun j => by linarith [ht1 j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hg0 : ∀ (i : ℕ) p, ‖p.2‖ < i → g i p = 0 := fun i p hp => by
    have hi : (i : ℝ) ≤ (i + N : ℕ) := by exact_mod_cast Nat.le_add_right i N
    simp only [hg]
    rw [χ.apply_eq_zero_of_norm_le_one, zero_smul]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (ht0 _).le), inv_mul_le_iff₀ (ht0 _),
      mul_one]
    linarith [ht1 (i + N)]
  have hgc : ∀ i, ContDiff ℝ ∞ (g i) := fun i =>
    contDiff_cutoff χ (a (i + N)).contDiff_coefficient _
  refine ⟨⟨fun p => ∑' i, g i p, contDiff_tsum_of_norm_lt hg0 hgc, fun K hK α β => ?_⟩,
    fun p => rfl⟩
  -- The estimates of the cut-off terms are summable from the index `J₀` on, where the enumeration
  -- has reached the estimate on `K`, `α`, `β` and the orders have dropped below `orders N - 1`.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hKk : K ⊆ closedBall 0 ⌈R⌉₊ := hR.trans (closedBall_subset_closedBall (Nat.le_ceil R))
  obtain ⟨G, hG⟩ := eventually_atTop.1 (hlim.eventually (eventually_le_atBot (orders N - 1)))
  choose D hD0 hD using fun i => exists_norm_mixedDeriv_cutoff_le χ (a i) hK α β
  set J₀ := Encodable.encode (⌈R⌉₊, α, β) + G
  refine ⟨∑ i ∈ range J₀, D (i + N) + 2,
    add_nonneg (sum_nonneg fun i _ => hD0 _) zero_le_two, fun x hx ξ => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_nat_gt ‖ξ‖
  have hJ : ‖ξ‖ < (J₀ + J₁ : ℕ) := hJ₁.trans_le (by exact_mod_cast Nat.le_add_left J₁ J₀)
  rw [mixedDeriv_tsum_of_norm_lt hg0 hgc α β hJ,
    ← sum_range_add_sum_Ico _ (Nat.le_add_right J₀ J₁)]
  set w := (1 + ‖ξ‖ ^ 2) ^ ((orders N - β.length) / 2)
  have hw : 0 ≤ w := (rpow_weight_pos ξ _).le
  -- The finitely many terms before `J₀` have order at most `orders N`.
  have h₁ : ‖∑ i ∈ range J₀, mixedDeriv α β (g i) x ξ‖ ≤ (∑ i ∈ range J₀, D (i + N)) * w := by
    rw [sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
    refine (hD (i + N) (t (i + N)) (by linarith [ht1 (i + N), (Nat.cast_nonneg (i + N) : (0 : ℝ)
      ≤ (i + N : ℕ))]) x hx ξ).trans ?_
    refine mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ ?_) (hD0 _)
    linarith [hmono (Nat.le_add_left N i)]
  -- The terms from `J₀` on are bounded by `2⁻ⁱ ⟨ξ⟩^(orders N - |β|)`.
  have h₂ : ‖∑ i ∈ Ico J₀ (J₀ + J₁), mixedDeriv α β (g i) x ξ‖ ≤ 2 * w := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Ico J₀ (J₀ + J₁), ‖mixedDeriv α β (g i) x ξ‖
        ≤ ∑ i ∈ Ico J₀ (J₀ + J₁), (1 / 2 : ℝ) ^ i * w := sum_le_sum fun i hi => by
          have hi := (mem_Ico.1 hi).1
          refine (ht (i + N) ⌈R⌉₊ α β (by omega) x (hKk hx) ξ).trans ?_
          refine mul_le_mul (pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (Nat.le_add_right i N)) (rpow_weight_le_rpow_weight ξ ?_) (rpow_weight_pos ξ _).le
            (by positivity)
          linarith [hG (i + N) (by omega)]
      _ ≤ ∑ i ∈ range (J₀ + J₁), (1 / 2 : ℝ) ^ i * w :=
          sum_le_sum_of_subset_of_nonneg (fun i hi => mem_range.2 (mem_Ico.1 hi).2)
            fun i _ _ => by positivity
      _ ≤ 2 * w := by
          rw [← sum_mul]
          exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) hw
  calc ‖∑ i ∈ range J₀, mixedDeriv α β (g i) x ξ +
        ∑ i ∈ Ico J₀ (J₀ + J₁), mixedDeriv α β (g i) x ξ‖
      ≤ (∑ i ∈ range J₀, D (i + N)) * w + 2 * w := (norm_add_le _ _).trans (add_le_add h₁ h₂)
    _ = (∑ i ∈ range J₀, D (i + N) + 2) * w := by ring

/-- **Borel summation of symbols.** For real orders `orders j` decreasing to `-∞`, every sequence
of symbols `a j` of order `orders j` has an asymptotic sum: a symbol `b` of order `orders 0` such
that for every `N` the remainder `b - ∑_{j<N} a j` is a symbol of order `orders N`. -/
theorem exists_asymptoticSum (hmono : Antitone orders) (hlim : Tendsto orders atTop atBot)
    (a : (j : ℕ) → Symbol n V W (orders j)) :
    ∃ b : Symbol n V W (orders 0), IsAsymptoticSum a b := by
  let χ : FrequencyCutoff (CoordinateSpace n) := default
  obtain ⟨t, ht1, ht⟩ := exists_radii χ a
  choose T hT using exists_tail χ hmono hlim ht1 ht
  have ht0 : ∀ j, 0 < t j := fun j => by linarith [ht1 j, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  set f : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun j p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p with hf
  refine ⟨T 0, fun N => ?_⟩
  -- The first `N` cut-off terms differ from the `a j` by a map vanishing at large frequencies.
  have hvanish : ∀ x ξ, 2 * ∑ j ∈ range N, t j ≤ ‖ξ‖ →
      ∑ j ∈ range N, (f j (x, ξ) - (a j).coefficient (x, ξ)) = 0 := fun x ξ hξ =>
    sum_eq_zero fun j hj => by
      have htj : t j ≤ ∑ i ∈ range N, t i :=
        single_le_sum (fun i _ => (ht0 i).le) hj
      simp only [hf]
      rw [χ.apply_eq_one_of_two_le_norm, one_smul, sub_self]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (ht0 j).le), le_inv_mul_iff₀ (ht0 j)]
      linarith
  let c : Symbol n V W (orders N) := ofBoundedFrequencySupport
    (fun p => ∑ j ∈ range N, (f j p - (a j).coefficient p))
    (ContDiff.sum fun j _ => (contDiff_cutoff χ (a j).contDiff_coefficient _).sub
      (a j).contDiff_coefficient)
    (2 * ∑ j ∈ range N, t j) hvanish
  refine ⟨T N + c, fun x ξ => ?_⟩
  have hsum : Summable fun j => f j (x, ξ) := by
    obtain ⟨J, hJ⟩ := exists_nat_gt ‖ξ‖
    refine summable_of_ne_finset_zero (s := range J) fun j hj => ?_
    simp only [hf]
    rw [χ.apply_eq_zero_of_norm_le_one, zero_smul]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (ht0 j).le), inv_mul_le_iff₀ (ht0 j), mul_one]
    have : (J : ℝ) ≤ j := by exact_mod_cast not_lt.1 (mem_range.not.1 hj)
    linarith [ht1 j]
  have hsplit := hsum.sum_add_tsum_nat_add N
  -- `i + 0` reduces to `i`, so `T 0` is the full cut-off series.
  have h0 : (T 0).coefficient (x, ξ) = ∑' i, f i (x, ξ) := hT 0 (x, ξ)
  rw [coefficient_add, Pi.add_apply, h0, hT, coefficient_ofBoundedFrequencySupport, sum_sub_distrib]
  simp only [hf] at hsplit ⊢
  rw [← hsplit]
  abel

end Borel

end Symbol

end TauCeti
