/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.NNRat.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Topology.MetricSpace.Holder

/-!
# The one-dimensional Kolmogorov–Chentsov continuous modification theorem

Let `X` be a stochastic process taking values in a complete metric space `E` and satisfying a
local Kolmogorov moment condition of exponents `p > 0` and `q > 1` on bounded nonnegative times:
`∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M N * edist s t ^ q` for `s, t ≤ N`.
By Borel–Cantelli on adjacent dyadic increments of mesh `2⁻ⁿ` and binary chaining, the sample
paths restricted to dyadic times are almost surely locally `γ`-Hölder continuous for every
`0 < γ < (q - 1) / p`. Extending from the dyadic grid on the explicit measurable full-measure
event where the dyadic modulus converges, and falling back to the constant path `X 0 ω` outside
that event, produces a process `Y : ℝ≥0 → Ω → E` such that:

* every sample path `t ↦ Y t ω` is continuous;
* each coordinate `Y t` is Borel measurable;
* `Y` agrees almost everywhere with `X` at each time;
* on every compact horizon `[0, T]` and for every `0 < γ < (q - 1) / p`, almost every path of `Y`
  is `γ`-Hölder continuous.

No finiteness or completeness hypothesis on the measure `P` and no separability hypothesis on `E`
is required. We expose both the extension from nonnegative rational times `ℚ≥0 → Ω → E` (used to
construct Wiener measure from a countable projective limit) and the modification theorems for
`IsKolmogorovProcess` and `IsAEKolmogorovProcess` on `ℝ≥0 → Ω → E`, together with uniqueness of
almost surely continuous modifications up to indistinguishability
(`TauCeti.indist_of_ae_continuous`) and the `dist`-moment constructors for `IsKolmogorovProcess`.

## Main results

* `TauCeti.indist_of_ae_continuous`: two modifications with almost surely continuous paths on a
  separable topological index space into a Hausdorff space are indistinguishable.
* `ProbabilityTheory.IsKolmogorovProcess.of_integral_dist_rpow_le`: builds `IsKolmogorovProcess`
  from Bochner `dist`-moment bounds on any pseudometric spaces.
* `TauCeti.exists_continuous_extension_of_nnrat`: extends a process on `ℚ≥0` satisfying local
  Kolmogorov bounds to an all-paths continuous, coordinatewise measurable process on `ℝ≥0` with
  almost sure local Hölder regularity of every order `< (q - 1) / p`.
* `TauCeti.exists_continuous_modification_of_local_isKolmogorovProcess`: local Kolmogorov–Chentsov
  modification theorem on `ℝ≥0`.
* `ProbabilityTheory.IsKolmogorovProcess.exists_continuous_modification` and
  `ProbabilityTheory.IsAEKolmogorovProcess.exists_continuous_modification`: global specializations.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, Theorem 4.23.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Theorem 2.2.8.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999,
  Theorem I.2.1.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- Two modifications on a separable index space with almost surely continuous paths into a `T₂`
space are indistinguishable. Neither finiteness of `P` nor measurability of the processes is
needed. -/
theorem indist_of_ae_continuous {ι Ω E : Type*} [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E] {_ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ι → Ω → E} (hX : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hY : ∀ᵐ ω ∂P, Continuous (Y · ω)) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ι
  have hD : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := (ae_ball_iff hDc).2 fun t _ ↦ hXY t
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω
  exact fun t ↦ congr_fun (Continuous.ext_on hDd hXω hYω hDω) t

end TauCeti

namespace ProbabilityTheory

/-- Construct `IsKolmogorovProcess` from Bochner `p`-th moment bounds on `dist`. -/
theorem IsKolmogorovProcess.of_integral_dist_rpow_le {T Ω E : Type*} [PseudoMetricSpace T]
    {_ : MeasurableSpace Ω} [PseudoMetricSpace E] {X : T → Ω → E} {P : Measure Ω}
    {p q : ℝ} {M : ℝ≥0}
    (hpair : ∀ s t : T, Measurable[_, borel (E × E)] fun ω ↦ (X s ω, X t ω))
    (hint : ∀ s t : T, Integrable (fun ω ↦ dist (X s ω) (X t ω) ^ p) P)
    (hkol : ∀ s t : T, ∫ ω, dist (X s ω) (X t ω) ^ p ∂P ≤ M * dist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M where
  measurablePair := hpair
  p_pos := hp
  q_pos := hq
  kolmogorovCondition s t := by
    have heq (ω : Ω) :
        edist (X s ω) (X t ω) ^ p = ENNReal.ofReal (dist (X s ω) (X t ω) ^ p) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp.le]
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint s t)
      (ae_of_all _ fun _ ↦ Real.rpow_nonneg dist_nonneg _)]
    calc ENNReal.ofReal (∫ ω, dist (X s ω) (X t ω) ^ p ∂P)
        ≤ ENNReal.ofReal ((M : ℝ) * dist s t ^ q) := ENNReal.ofReal_le_ofReal (hkol s t)
      _ = M * edist s t ^ q := by
        rw [ENNReal.ofReal_mul M.coe_nonneg, ENNReal.ofReal_coe_nnreal, edist_dist,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le]

/-- In a second-countable Borel space, coordinatewise measurability and Bochner `p`-th moment
bounds on `dist` imply `IsKolmogorovProcess`. -/
theorem IsKolmogorovProcess.of_secondCountableTopology_integral_dist_rpow_le {T Ω E : Type*}
    [PseudoMetricSpace T] {_ : MeasurableSpace Ω} [PseudoMetricSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X : T → Ω → E} {P : Measure Ω} {p q : ℝ} {M : ℝ≥0}
    (hmeas : ∀ t : T, Measurable (X t))
    (hint : ∀ s t : T, Integrable (fun ω ↦ dist (X s ω) (X t ω) ^ p) P)
    (hkol : ∀ s t : T, ∫ ω, dist (X s ω) (X t ω) ^ p ∂P ≤ M * dist s t ^ q)
    (hp : 0 < p) (hq : 0 < q) :
    IsKolmogorovProcess X P p q M := by
  refine IsKolmogorovProcess.of_integral_dist_rpow_le (fun s t ↦ ?_) hint hkol hp hq
  rw [← Prod.borelSpace.measurable_eq]
  exact (hmeas s).prodMk (hmeas t)

end ProbabilityTheory

namespace TauCeti

section DyadicChaining

/-- The `k`-th dyadic nonnegative rational at scale `2⁻ⁿ`. -/
private def dyadicNNRat (n k : ℕ) : ℚ≥0 := (k : ℚ≥0) / 2 ^ n

private lemma cast_dyadicNNRat_nnreal (n k : ℕ) :
    (dyadicNNRat n k : ℝ≥0) = (k : ℝ≥0) / 2 ^ n := by
  simp [dyadicNNRat]

private lemma cast_dyadicNNRat_real (n k : ℕ) :
    ((dyadicNNRat n k : ℝ≥0) : ℝ) = (k : ℝ) / 2 ^ n := by
  simp [dyadicNNRat]

private lemma cast_dyadicNNRat_mem_Iic {N n k : ℕ} (hk : k ≤ N * 2 ^ n) :
    (dyadicNNRat n k : ℝ≥0) ∈ Iic (N : ℝ≥0) := by
  rw [mem_Iic, ← NNReal.coe_le_coe, cast_dyadicNNRat_real, div_le_iff₀ (by positivity)]
  exact_mod_cast hk

private lemma floor_mul_two_pow_le {N : ℕ} {t : ℝ≥0} (ht : t ≤ N) (n : ℕ) :
    ⌊(t : ℝ) * 2 ^ n⌋₊ ≤ N * 2 ^ n := by
  refine Nat.floor_le_of_le ?_
  have ht' : (t : ℝ) ≤ N := by exact_mod_cast ht
  calc (t : ℝ) * 2 ^ n ≤ (N : ℝ) * 2 ^ n := by gcongr
    _ = ((N * 2 ^ n : ℕ) : ℝ) := by push_cast; rfl

private lemma dyadicNNRat_double (n k : ℕ) :
    dyadicNNRat (n + 1) (2 * k) = dyadicNNRat n k := by
  simp only [dyadicNNRat, Nat.cast_mul, Nat.cast_ofNat, pow_succ']
  rw [mul_div_mul_left _ _ (two_ne_zero' ℚ≥0)]

private lemma dyadicNNRat_scale (n d k : ℕ) :
    dyadicNNRat (n + d) (k * 2 ^ d) = dyadicNNRat n k := by
  simp only [dyadicNNRat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  rw [mul_div_mul_right _ _ (pow_ne_zero d (two_ne_zero' ℚ≥0))]

private lemma dist_dyadicNNRat_succ (n k : ℕ) :
    dist (dyadicNNRat n k : ℝ≥0) (dyadicNNRat n (k + 1) : ℝ≥0) = (2 : ℝ)⁻¹ ^ n := by
  rw [NNReal.dist_eq, cast_dyadicNNRat_real, cast_dyadicNNRat_real, inv_pow]
  have hle : (k : ℝ) / 2 ^ n ≤ ((k + 1 : ℕ) : ℝ) / 2 ^ n := by gcongr; exact k.le_succ
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  push_cast
  ring

private lemma edist_dyadicNNRat_succ (n k : ℕ) :
    edist (dyadicNNRat n k : ℝ≥0) (dyadicNNRat n (k + 1) : ℝ≥0) =
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) := by
  rw [edist_dist, dist_dyadicNNRat_succ]

/-- Downward floor approximation of `t : ℝ≥0` on the level-`n` dyadic grid in `ℚ≥0`. -/
private def approxDyadicNNRat (n : ℕ) (t : ℝ≥0) : ℚ≥0 :=
  dyadicNNRat n ⌊(t : ℝ) * 2 ^ n⌋₊

private lemma approxDyadicNNRat_le (n : ℕ) (t : ℝ≥0) :
    (approxDyadicNNRat n t : ℝ≥0) ≤ t := by
  rw [← NNReal.coe_le_coe, approxDyadicNNRat, cast_dyadicNNRat_real,
    div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

private lemma dist_approxDyadicNNRat_le (n : ℕ) (t : ℝ≥0) :
    dist (approxDyadicNNRat n t : ℝ≥0) t ≤ (2 : ℝ)⁻¹ ^ n := by
  rw [NNReal.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 (approxDyadicNNRat_le n t))),
    approxDyadicNNRat, cast_dyadicNNRat_real, inv_pow]
  have hlt : (t : ℝ) * 2 ^ n < (⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdiv : (t : ℝ) < ((⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n :=
    (lt_div_iff₀ (by positivity)).2 hlt
  linarith [add_div (⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) 1 ((2 : ℝ) ^ n), one_div ((2 : ℝ) ^ n)]

private lemma edist_approxDyadicNNRat_le (n : ℕ) (t : ℝ≥0) :
    edist (approxDyadicNNRat n t : ℝ≥0) t ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_approxDyadicNNRat_le n t)

private lemma tendsto_approxDyadicNNRat (t : ℝ≥0) :
    Tendsto (fun n ↦ (approxDyadicNNRat n t : ℝ≥0)) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ dist_approxDyadicNNRat_le n t) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Binary inward-rounding chaining on dyadic rationals: if adjacent increments at all levels
`j ≥ r` are bounded by `(2⁻¹) ^ (j * γ)`, then any two level-`(r + d)` grid points within
`2 * 2 ^ d` steps have values within `2 * ∑_{i ≤ d} (2⁻¹) ^ ((r + i) * γ)`. -/
private lemma dist_dyadicNNRat_le_sum {E : Type*} [PseudoMetricSpace E] {f : ℚ≥0 → E}
    {N r : ℕ} {γ : ℝ}
    (hadj : ∀ j ≥ r, ∀ k < N * 2 ^ j,
      dist (f (dyadicNNRat j k)) (f (dyadicNNRat j (k + 1))) ≤ (2 : ℝ)⁻¹ ^ ((j : ℝ) * γ)) :
    ∀ (d a b : ℕ), a ≤ b → b ≤ N * 2 ^ (r + d) → b - a ≤ 2 * 2 ^ d →
      dist (f (dyadicNNRat (r + d) a)) (f (dyadicNNRat (r + d) b)) ≤
        2 * ∑ i ∈ Finset.range (d + 1), (2 : ℝ)⁻¹ ^ (((r + i : ℕ) : ℝ) * γ) := by
  intro d
  induction d with
  | zero =>
    intro a b hab hb hba
    simp only [zero_add, add_zero, pow_zero, mul_one, Finset.range_one,
      Finset.sum_singleton] at hb hba ⊢
    have hpos : 0 ≤ (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) := by positivity
    obtain rfl | rfl | rfl : b = a ∨ b = a + 1 ∨ b = a + 2 := by omega
    · simp [hpos]
    · linarith [hadj r le_rfl a (by omega)]
    · calc dist (f (dyadicNNRat r a)) (f (dyadicNNRat r (a + 2)))
          ≤ dist (f (dyadicNNRat r a)) (f (dyadicNNRat r (a + 1))) +
              dist (f (dyadicNNRat r (a + 1))) (f (dyadicNNRat r (a + 2))) := dist_triangle ..
        _ ≤ (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) + (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) :=
          add_le_add (hadj r le_rfl a (by omega)) (hadj r le_rfl (a + 1) (by omega))
        _ = 2 * (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) := by ring
  | succ d ih =>
    intro a b hab hb hba
    rw [Finset.sum_range_succ, mul_add]
    have hsum_nonneg : 0 ≤ 2 * ∑ i ∈ Finset.range (d + 1),
        (2 : ℝ)⁻¹ ^ (((r + i : ℕ) : ℝ) * γ) :=
      mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ ↦ by positivity)
    have hterm_nonneg : 0 ≤ (2 : ℝ)⁻¹ ^ (((r + (d + 1) : ℕ) : ℝ) * γ) := by positivity
    by_cases hsmall : b ≤ a + 1
    · obtain rfl | rfl : b = a ∨ b = a + 1 := by omega
      · rw [dist_self]; linarith
      · have h1 := hadj (r + (d + 1)) (Nat.le_add_right r _) a (by omega)
        linarith
    · -- Round `a` up to `2 * a'` and `b` down to `2 * b'`, staying inside `[a, b]`.
      let a' := (a + 1) / 2
      let b' := b / 2
      have hpow : N * 2 ^ (r + (d + 1)) = 2 * (N * 2 ^ (r + d)) := by
        rw [← add_assoc, pow_succ]; ring
      have ha'b' : a' ≤ b' := by omega
      have hb'N : b' ≤ N * 2 ^ (r + d) := by omega
      have hba' : b' - a' ≤ 2 * 2 ^ d := by
        have : 2 * 2 ^ (d + 1) = 4 * 2 ^ d := by rw [pow_succ]; ring
        omega
      have hleft : dist (f (dyadicNNRat (r + (d + 1)) a))
          (f (dyadicNNRat (r + d) a')) ≤ (2 : ℝ)⁻¹ ^ (((r + (d + 1) : ℕ) : ℝ) * γ) := by
        rw [← add_assoc, ← dyadicNNRat_double (r + d) a']
        obtain ha_eq | ha_eq : 2 * a' = a ∨ 2 * a' = a + 1 := by omega
        · rw [ha_eq, dist_self]; exact hterm_nonneg
        · rw [ha_eq]
          exact hadj (r + (d + 1)) (Nat.le_add_right r _) a (by omega)
      have hright : dist (f (dyadicNNRat (r + d) b'))
          (f (dyadicNNRat (r + (d + 1)) b)) ≤ (2 : ℝ)⁻¹ ^ (((r + (d + 1) : ℕ) : ℝ) * γ) := by
        rw [← add_assoc, ← dyadicNNRat_double (r + d) b']
        obtain hb_eq | hb_eq : b = 2 * b' ∨ b = 2 * b' + 1 := by omega
        · rw [hb_eq, dist_self]; exact hterm_nonneg
        · rw [hb_eq]
          exact hadj (r + (d + 1)) (Nat.le_add_right r _) (2 * b') (by omega)
      have hmid := ih a' b' ha'b' hb'N hba'
      calc dist (f (dyadicNNRat (r + (d + 1)) a)) (f (dyadicNNRat (r + (d + 1)) b))
          ≤ dist (f (dyadicNNRat (r + (d + 1)) a)) (f (dyadicNNRat (r + d) a')) +
              dist (f (dyadicNNRat (r + d) a')) (f (dyadicNNRat (r + d) b')) +
              dist (f (dyadicNNRat (r + d) b')) (f (dyadicNNRat (r + (d + 1)) b)) :=
            dist_triangle4 ..
        _ ≤ _ := by linarith

/-- Geometric series bound for the dyadic chaining tail. -/
private lemma two_mul_sum_dyadic_rpow_le {r d : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    2 * ∑ i ∈ Finset.range (d + 1), (2 : ℝ)⁻¹ ^ (((r + i : ℕ) : ℝ) * γ) ≤
      (2 / (1 - (2 : ℝ)⁻¹ ^ γ)) * (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) := by
  set ρ : ℝ := (2 : ℝ)⁻¹ ^ γ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hrew (i : ℕ) :
      (2 : ℝ)⁻¹ ^ (((r + i : ℕ) : ℝ) * γ) = (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) * ρ ^ i := by
    rw [Nat.cast_add, add_mul, Real.rpow_add (by norm_num), ← Real.rpow_natCast ρ i,
      ← Real.rpow_mul (by norm_num), mul_comm γ (i : ℝ)]
  simp_rw [hrew, ← Finset.mul_sum]
  have hgeom : ∑ i ∈ Finset.range (d + 1), ρ ^ i ≤ (1 - ρ)⁻¹ :=
    sum_le_hasSum (Finset.range (d + 1)) (fun _ _ ↦ by positivity)
      (hasSum_geometric_of_lt_one hρ0 hρ1)
  calc 2 * ((2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) * ∑ i ∈ Finset.range (d + 1), ρ ^ i)
      ≤ 2 * ((2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) * (1 - ρ)⁻¹) := by gcongr
    _ = (2 / (1 - ρ)) * (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) := by ring

/-- Small-scale Hölder estimate on all dyadic rationals in `[0, N]` once adjacent increments at
levels `j ≥ m` are bounded by `(2⁻¹) ^ (j * γ)`. -/
private lemma dist_dyadicNNRat_le_of_dist_lt {E : Type*} [PseudoMetricSpace E] {f : ℚ≥0 → E}
    {N m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hadj : ∀ j ≥ m, ∀ k < N * 2 ^ j,
      dist (f (dyadicNNRat j k)) (f (dyadicNNRat j (k + 1))) ≤ (2 : ℝ)⁻¹ ^ ((j : ℝ) * γ))
    {n₁ k₁ n₂ k₂ : ℕ} (hk₁ : k₁ ≤ N * 2 ^ n₁) (hk₂ : k₂ ≤ N * 2 ^ n₂)
    (hdist : dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) < (2 : ℝ)⁻¹ ^ m) :
    dist (f (dyadicNNRat n₁ k₁)) (f (dyadicNNRat n₂ k₂)) ≤
      (2 / (1 - (2 : ℝ)⁻¹ ^ γ)) *
        dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) ^ γ := by
  set δ := dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0)
  have hρ1 : (2 : ℝ)⁻¹ ^ γ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have hC0 : 0 ≤ 2 / (1 - (2 : ℝ)⁻¹ ^ γ) := div_nonneg zero_le_two (sub_nonneg.2 hρ1.le)
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ δ) with hδ0 | hδ_pos
  · have hq : dyadicNNRat n₁ k₁ = dyadicNNRat n₂ k₂ :=
      NNRat.cast_injective (dist_eq_zero.mp hδ0.symm)
    rw [hq, dist_self]
    exact mul_nonneg hC0 (Real.rpow_nonneg dist_nonneg _)
  · -- Choose `r ≥ m + 1` with `2 ^ (-r) ≤ δ < 2 ^ (-r + 1)`.
    obtain ⟨z, hlo, hhi⟩ := exists_mem_Ico_zpow hδ_pos one_lt_two
    have hz_lt : z < -(m : ℤ) := by
      by_contra! hge
      have h1 : (2 : ℝ) ^ (-(m : ℤ)) ≤ (2 : ℝ) ^ z := zpow_le_zpow_right₀ one_le_two hge
      rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
      linarith
    set r : ℕ := (-z).toNat
    have hr_ge : m + 1 ≤ r := by omega
    have hz_eq : z = -(r : ℤ) := by omega
    have hr_lo : (2 : ℝ)⁻¹ ^ r ≤ δ := by
      simpa [hz_eq, zpow_neg, zpow_natCast, inv_pow] using hlo
    have hr_hi : δ < 2 * (2 : ℝ)⁻¹ ^ r := by
      have : (2 : ℝ) ^ (z + 1) = 2 * (2 : ℝ)⁻¹ ^ r := by
        rw [zpow_add₀ two_ne_zero, zpow_one, hz_eq, zpow_neg, zpow_natCast, inv_pow, mul_comm]
      linarith
    -- Express both dyadics at the common level `r + (n₁ + n₂)`.
    let d := n₁ + n₂
    let a₁ := k₁ * 2 ^ (r + n₂)
    let a₂ := k₂ * 2 ^ (r + n₁)
    have heq₁ : dyadicNNRat (r + d) a₁ = dyadicNNRat n₁ k₁ := by
      have : r + d = n₁ + (r + n₂) := by omega
      rw [this]; exact dyadicNNRat_scale n₁ (r + n₂) k₁
    have heq₂ : dyadicNNRat (r + d) a₂ = dyadicNNRat n₂ k₂ := by
      have : r + d = n₂ + (r + n₁) := by omega
      rw [this]; exact dyadicNNRat_scale n₂ (r + n₁) k₂
    have ha₁ : a₁ ≤ N * 2 ^ (r + d) := by
      have : r + d = n₁ + (r + n₂) := by omega
      rw [this, pow_add, ← mul_assoc]; exact Nat.mul_le_mul_right _ hk₁
    have ha₂ : a₂ ≤ N * 2 ^ (r + d) := by
      have : r + d = n₂ + (r + n₁) := by omega
      rw [this, pow_add, ← mul_assoc]; exact Nat.mul_le_mul_right _ hk₂
    have hdiff : |(a₁ : ℝ) - a₂| ≤ 2 * (2 : ℝ) ^ d := by
      have hδ_eq : δ = |(a₁ : ℝ) - a₂| / 2 ^ (r + d) := by
        simp only [δ, ← heq₁, ← heq₂, NNReal.dist_eq, cast_dyadicNNRat_real, ← sub_div,
          abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (r + d))]
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (r + d))).mp (hδ_eq ▸ hr_hi)
      have hcancel : 2 * (2 : ℝ)⁻¹ ^ r * 2 ^ (r + d) = 2 * (2 : ℝ) ^ d := by
        rw [pow_add, inv_pow]; field_simp
      linarith
    have hadj_r : ∀ j ≥ r, ∀ k < N * 2 ^ j,
        dist (f (dyadicNNRat j k)) (f (dyadicNNRat j (k + 1))) ≤ (2 : ℝ)⁻¹ ^ ((j : ℝ) * γ) :=
      fun j hj ↦ hadj j (by omega)
    have h2d : ((2 * 2 ^ d : ℕ) : ℝ) = 2 * (2 : ℝ) ^ d := by push_cast; rfl
    have hchain : dist (f (dyadicNNRat (r + d) a₁)) (f (dyadicNNRat (r + d) a₂)) ≤
        (2 / (1 - (2 : ℝ)⁻¹ ^ γ)) * (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ) := by
      rcases le_total a₁ a₂ with hle | hle
      · have hba : a₂ - a₁ ≤ 2 * 2 ^ d := by
          refine Nat.cast_le (α := ℝ).mp ?_
          have hsub : ((a₂ - a₁ : ℕ) : ℝ) = (a₂ : ℝ) - a₁ := Nat.cast_sub hle
          rw [hsub, h2d]
          linarith [le_abs_self ((a₂ : ℝ) - a₁), abs_sub_comm (a₁ : ℝ) a₂]
        exact (dist_dyadicNNRat_le_sum hadj_r d a₁ a₂ hle ha₂ hba).trans
          (two_mul_sum_dyadic_rpow_le hγ)
      · rw [dist_comm]
        have hba : a₁ - a₂ ≤ 2 * 2 ^ d := by
          refine Nat.cast_le (α := ℝ).mp ?_
          have hsub : ((a₁ - a₂ : ℕ) : ℝ) = (a₁ : ℝ) - a₂ := Nat.cast_sub hle
          rw [hsub, h2d]
          linarith [le_abs_self ((a₁ : ℝ) - a₂)]
        exact (dist_dyadicNNRat_le_sum hadj_r d a₂ a₁ hle ha₁ hba).trans
          (two_mul_sum_dyadic_rpow_le hγ)
    rw [← heq₁, ← heq₂]
    refine hchain.trans ?_
    gcongr
    calc (2 : ℝ)⁻¹ ^ ((r : ℝ) * γ)
        = ((2 : ℝ)⁻¹ ^ r) ^ γ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      _ ≤ δ ^ γ := Real.rpow_le_rpow (by positivity) hr_lo hγ.le

/-- Uniform bound from `f (dyadicNNRat (m + 1) 0)` to any dyadic grid point in `[0, N]`, combining
finite telescoping at coarse level `m + 1` with the short-range chaining estimate. -/
private lemma dist_dyadicNNRat_origin_le {E : Type*} [PseudoMetricSpace E]
    {f : ℚ≥0 → E} {N m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hadj : ∀ j ≥ m, ∀ k < N * 2 ^ j,
      dist (f (dyadicNNRat j k)) (f (dyadicNNRat j (k + 1))) ≤ (2 : ℝ)⁻¹ ^ ((j : ℝ) * γ))
    {n k : ℕ} (hk : k ≤ N * 2 ^ n) :
    dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat n k)) ≤
      2 / (1 - (2 : ℝ)⁻¹ ^ γ) + N * 2 ^ (m + 1) := by
  have hcoarse (l : ℕ) (hl : l ≤ N * 2 ^ (m + 1)) :
      dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat (m + 1) l)) ≤ l := by
    induction l with
    | zero => simp
    | succ l ih =>
      calc dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat (m + 1) (l + 1)))
          ≤ dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat (m + 1) l)) +
              dist (f (dyadicNNRat (m + 1) l)) (f (dyadicNNRat (m + 1) (l + 1))) :=
            dist_triangle ..
        _ ≤ (l : ℝ) + (2 : ℝ)⁻¹ ^ (((m + 1 : ℕ) : ℝ) * γ) :=
          add_le_add (ih (Nat.le_of_succ_le hl)) (hadj (m + 1) (Nat.le_succ m) l (by omega))
        _ ≤ (l : ℝ) + 1 := by
          gcongr
          exact Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
        _ = ((l + 1 : ℕ) : ℝ) := by push_cast; ring
  let j := ⌊((dyadicNNRat n k : ℝ≥0) : ℝ) * 2 ^ (m + 1)⌋₊
  have hj : j ≤ N * 2 ^ (m + 1) := floor_mul_two_pow_le (cast_dyadicNNRat_mem_Iic hk) (m + 1)
  have hdist_lt : dist (dyadicNNRat (m + 1) j : ℝ≥0) (dyadicNNRat n k : ℝ≥0) < (2 : ℝ)⁻¹ ^ m :=
    (dist_approxDyadicNNRat_le (m + 1) (dyadicNNRat n k : ℝ≥0)).trans_lt
      (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self m))
  have hnear := dist_dyadicNNRat_le_of_dist_lt hγ hadj hj hk hdist_lt
  have hrpow_le : dist (dyadicNNRat (m + 1) j : ℝ≥0) (dyadicNNRat n k : ℝ≥0) ^ γ ≤ 1 :=
    Real.rpow_le_one dist_nonneg
      (hdist_lt.le.trans (pow_le_one₀ (by norm_num) (by norm_num))) hγ.le
  have hK_nonneg : 0 ≤ 2 / (1 - (2 : ℝ)⁻¹ ^ γ) :=
    div_nonneg zero_le_two (sub_nonneg.2 (Real.rpow_lt_one (by norm_num) (by norm_num) hγ).le)
  calc dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat n k))
      ≤ dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat (m + 1) j)) +
          dist (f (dyadicNNRat (m + 1) j)) (f (dyadicNNRat n k)) := dist_triangle ..
    _ ≤ (j : ℝ) + 2 / (1 - (2 : ℝ)⁻¹ ^ γ) * 1 :=
      add_le_add (hcoarse j hj) (hnear.trans (mul_le_mul_of_nonneg_left hrpow_le hK_nonneg))
    _ ≤ (N * 2 ^ (m + 1) : ℕ) + 2 / (1 - (2 : ℝ)⁻¹ ^ γ) := by
      have hj' : (j : ℝ) ≤ ((N * 2 ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hj
      linarith
    _ = 2 / (1 - (2 : ℝ)⁻¹ ^ γ) + N * 2 ^ (m + 1) := by push_cast; ring

/-- Deterministic dyadic Hölder extension on `[0, N]`: if `f : ℚ≥0 → E` into a complete metric
space has adjacent level-`j` increments on `[0, N]` bounded by `(2⁻¹) ^ (j * γ)` for all `j ≥ m`,
then `f` extends from dyadic rationals in `[0, N]` to a `γ`-Hölder map on `Iic (N : ℝ≥0)`. -/
private lemma exists_holderWith_Iic_of_dyadic_adj {E : Type*} [MetricSpace E] [CompleteSpace E]
    {f : ℚ≥0 → E} {N m : ℕ} {γ : ℝ≥0} (hγ : 0 < γ)
    (hadj : ∀ j ≥ m, ∀ k < N * 2 ^ j,
      dist (f (dyadicNNRat j k)) (f (dyadicNNRat j (k + 1))) ≤
        (2 : ℝ)⁻¹ ^ ((j : ℝ) * (γ : ℝ))) :
    ∃ (C : ℝ≥0) (g : Iic (N : ℝ≥0) → E), HolderWith C γ g ∧
      ∀ n k (hk : k ≤ N * 2 ^ n),
        g ⟨(dyadicNNRat n k : ℝ≥0), cast_dyadicNNRat_mem_Iic hk⟩ = f (dyadicNNRat n k) := by
  classical
  have hγ' : (0 : ℝ) < γ := hγ
  let s : Set (Iic (N : ℝ≥0)) :=
    {x | ∃ q : ℚ≥0, (∃ n k : ℕ, k ≤ N * 2 ^ n ∧ q = dyadicNNRat n k) ∧ (x : ℝ≥0) = q}
  have hs_dense : Dense s := fun x ↦ mem_closure_iff_seq_limit.2
    ⟨fun n ↦ ⟨(approxDyadicNNRat n x.1 : ℝ≥0), (approxDyadicNNRat_le n x.1).trans x.2⟩,
      fun n ↦ ⟨approxDyadicNNRat n x.1,
        ⟨n, ⌊(x.1 : ℝ) * 2 ^ n⌋₊, floor_mul_two_pow_le x.2 n, rfl⟩, rfl⟩,
      tendsto_subtype_rng.2 (tendsto_approxDyadicNNRat x.1)⟩
  let F : Iic (N : ℝ≥0) → E := fun x ↦ if hx : x ∈ s then f hx.choose else f 0
  have hF_eq {x : Iic (N : ℝ≥0)} {n k : ℕ} (hk : k ≤ N * 2 ^ n)
      (hxq : (x : ℝ≥0) = dyadicNNRat n k) : F x = f (dyadicNNRat n k) := by
    have hx : x ∈ s := ⟨dyadicNNRat n k, ⟨n, k, hk, rfl⟩, hxq⟩
    simp only [F, hx, ↓reduceDIte]
    exact congrArg f (NNRat.cast_injective (hx.choose_spec.2.symm.trans hxq))
  set K : ℝ≥0 := ⟨2 / (1 - (2 : ℝ)⁻¹ ^ (γ : ℝ)),
    div_nonneg zero_le_two (sub_nonneg.2 (Real.rpow_lt_one (by norm_num) (by norm_num) hγ').le)⟩
  set D : ℝ≥0 := 2 * (K + N * 2 ^ (m + 1))
  set δ : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ m
  have hholder_s : HolderOnWith (K + D * δ ^ (-(γ : ℝ))) γ F s := by
    refine HolderOnWith.of_dist_lt_of_dist_le (pow_pos (by norm_num) m)
      (fun x hx y hy hxy ↦ ?_) (fun x hx y hy ↦ ?_)
    · rcases hx with ⟨qx, ⟨n₁, k₁, hk₁, rfl⟩, hxq⟩
      rcases hy with ⟨qy, ⟨n₂, k₂, hk₂, rfl⟩, hyq⟩
      have hdist : dist x y = dist (dyadicNNRat n₁ k₁ : ℝ≥0) (dyadicNNRat n₂ k₂ : ℝ≥0) := by
        rw [Subtype.dist_eq, hxq, hyq]
      rw [hF_eq hk₁ hxq, hF_eq hk₂ hyq, hdist]
      exact dist_dyadicNNRat_le_of_dist_lt hγ' hadj hk₁ hk₂ (by simpa [hdist, δ] using hxy)
    · rcases hx with ⟨qx, ⟨n₁, k₁, hk₁, rfl⟩, hxq⟩
      rcases hy with ⟨qy, ⟨n₂, k₂, hk₂, rfl⟩, hyq⟩
      rw [hF_eq hk₁ hxq, hF_eq hk₂ hyq]
      calc dist (f (dyadicNNRat n₁ k₁)) (f (dyadicNNRat n₂ k₂))
          ≤ dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat n₁ k₁)) +
              dist (f (dyadicNNRat (m + 1) 0)) (f (dyadicNNRat n₂ k₂)) := dist_triangle_left ..
        _ ≤ (K : ℝ) + N * 2 ^ (m + 1) + ((K : ℝ) + N * 2 ^ (m + 1)) :=
          add_le_add (dist_dyadicNNRat_origin_le hγ' hadj hk₁)
            (dist_dyadicNNRat_origin_le hγ' hadj hk₂)
        _ = (D : ℝ) := by simp [D]; ring
  obtain ⟨g, hg_holder, hg_eq⟩ := hholder_s.extend_of_dense hγ hs_dense
  refine ⟨K + D * δ ^ (-(γ : ℝ)), g, hg_holder, fun n k hk ↦ ?_⟩
  exact (hg_eq ⟨dyadicNNRat n k, ⟨n, k, hk, rfl⟩, rfl⟩).symm.trans (hF_eq hk rfl)

/-- If `g : Iic (N : ℝ≥0) → E` is continuous and agrees with `f : ℚ≥0 → E` on dyadic rationals,
then `f (approxDyadicNNRat n t)` converges to `g t`. -/
private lemma tendsto_approxDyadicNNRat_apply_of_continuous {E : Type*} [TopologicalSpace E]
    {N : ℕ} {f : ℚ≥0 → E} {g : Iic (N : ℝ≥0) → E} (hg_cont : Continuous g)
    (hg_dyad : ∀ n k (hk : k ≤ N * 2 ^ n),
      g ⟨(dyadicNNRat n k : ℝ≥0), cast_dyadicNNRat_mem_Iic hk⟩ = f (dyadicNNRat n k))
    (t : Iic (N : ℝ≥0)) :
    Tendsto (fun n ↦ f (approxDyadicNNRat n t.1)) atTop (𝓝 (g t)) := by
  have hconv : Tendsto (fun n ↦ (⟨(approxDyadicNNRat n t.1 : ℝ≥0),
      (approxDyadicNNRat_le n t.1).trans t.2⟩ : Iic (N : ℝ≥0))) atTop (𝓝 t) :=
    tendsto_subtype_rng.2 (tendsto_approxDyadicNNRat t.1)
  exact (hg_cont.tendsto t).comp hconv |>.congr fun n ↦
    hg_dyad n ⌊(t.1 : ℝ) * 2 ^ n⌋₊ (floor_mul_two_pow_le t.2 n)

end DyadicChaining

section StochasticExtension

/-- Markov's inequality for `p`-th power of an `ℝ≥0∞`-valued random variable. -/
private lemma measure_lt_le_lintegral_rpow_div {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {d : Ω → ℝ≥0∞} {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (hd : Measurable d) :
    P {ω | ENNReal.ofReal c < d ω} ≤ (∫⁻ ω, d ω ^ p ∂P) / ENNReal.ofReal (c ^ p) := by
  have hsub : {ω | ENNReal.ofReal c < d ω} ⊆ {ω | ENNReal.ofReal (c ^ p) ≤ d ω ^ p} := by
    intro ω hω
    have hlt : ENNReal.ofReal c < d ω := hω
    rw [mem_ofPred, ← ENNReal.ofReal_rpow_of_pos hc]
    exact ENNReal.rpow_le_rpow hlt.le hp.le
  have hc_ne0 : ENNReal.ofReal (c ^ p) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hc p)).ne'
  have hc_top : ENNReal.ofReal (c ^ p) ≠ ∞ := ENNReal.ofReal_ne_top
  refine (measure_mono hsub).trans ?_
  rw [ENNReal.le_div_iff_mul_le (.inl hc_ne0) (.inl hc_top), mul_comm]
  exact mul_meas_ge_le_lintegral₀ (hd.pow_const p).aemeasurable _

/-- At horizon `N`, the level-`n` event where some adjacent dyadic increment exceeds
`2 ^ (-n * γ)`. -/
private def badDyadicEvent {Ω E : Type*} [PseudoEMetricSpace E] (X : ℚ≥0 → Ω → E)
    (N : ℕ) (γ : ℝ≥0) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (N * 2 ^ n),
    {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * (γ : ℝ))) <
      edist (X (dyadicNNRat n k) ω) (X (dyadicNNRat n (k + 1)) ω)}

private lemma measurableSet_badDyadicEvent {Ω E : Type*} {_ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] {X : ℚ≥0 → Ω → E}
    (hedist : ∀ q r : ℚ≥0, Measurable fun ω ↦ edist (X q ω) (X r ω))
    (N : ℕ) (γ : ℝ≥0) (n : ℕ) :
    MeasurableSet (badDyadicEvent X N γ n) :=
  Finset.measurableSet_biUnion _ fun _ _ ↦ measurableSet_lt measurable_const (hedist _ _)

/-- Borel–Cantelli bound: for `0 < p`, `1 < q`, and `0 < γ < (q - 1) / p`, almost every sample
path eventually satisfies the dyadic increment bound at horizon `N`. -/
private lemma measure_limsup_badDyadicEvent_eq_zero {Ω E : Type*} {_ : MeasurableSpace Ω}
    [PseudoEMetricSpace E] {P : Measure Ω} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0} {N : ℕ}
    {γ : ℝ≥0} (hp : 0 < p) (hγ : (γ : ℝ) < (q - 1) / p)
    (hedist : ∀ q r : ℚ≥0, Measurable fun ω ↦ edist (X q ω) (X r ω))
    (hkol : ∀ q₁ q₂ : ℚ≥0, (q₁ : ℝ≥0) ≤ N → (q₂ : ℝ≥0) ≤ N →
      ∫⁻ ω, edist (X q₁ ω) (X q₂ ω) ^ p ∂P ≤ M * edist (q₁ : ℝ≥0) (q₂ : ℝ≥0) ^ q) :
    P (limsup (badDyadicEvent X N γ) atTop) = 0 := by
  apply measure_limsup_atTop_eq_zero
  set α : ℝ := q - 1 - p * (γ : ℝ)
  have hα : 0 < α := by
    have : (γ : ℝ) * p < q - 1 := (lt_div_iff₀ hp).mp hγ
    linarith
  have hterm (n : ℕ) :
      P (badDyadicEvent X N γ n) ≤
        (N : ℝ≥0∞) * M * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ α) ^ n) := by
    refine (measure_biUnion_finset_le (Finset.range (N * 2 ^ n)) _).trans ?_
    have hk_le (k : ℕ) (hk : k ∈ Finset.range (N * 2 ^ n)) :
        P {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * (γ : ℝ))) <
          edist (X (dyadicNNRat n k) ω) (X (dyadicNNRat n (k + 1)) ω)} ≤
          M * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * (q - p * (γ : ℝ)))) := by
      rw [Finset.mem_range] at hk
      set c : ℝ := (2 : ℝ)⁻¹ ^ ((n : ℝ) * (γ : ℝ))
      have hc_pos : 0 < c := by positivity
      have hkol_k : ∫⁻ ω, edist (X (dyadicNNRat n k) ω) (X (dyadicNNRat n (k + 1)) ω) ^ p ∂P ≤
          M * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * q)) := by
        calc ∫⁻ ω, edist (X (dyadicNNRat n k) ω) (X (dyadicNNRat n (k + 1)) ω) ^ p ∂P
            ≤ M * edist (dyadicNNRat n k : ℝ≥0) (dyadicNNRat n (k + 1) : ℝ≥0) ^ q :=
              hkol _ _ (cast_dyadicNNRat_mem_Iic hk.le)
                (cast_dyadicNNRat_mem_Iic (Nat.succ_le_of_lt hk))
          _ = M * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * q)) := by
              rw [edist_dyadicNNRat_succ, ENNReal.ofReal_rpow_of_pos (by positivity),
                ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      refine (measure_lt_le_lintegral_rpow_div hc_pos hp (hedist _ _)).trans
        ((ENNReal.div_le_div_right hkol_k _).trans_eq ?_)
      rw [mul_div_assoc, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hc_pos p)]
      congr 1
      have hcp : c ^ p = (2 : ℝ)⁻¹ ^ ((n : ℝ) * (p * (γ : ℝ))) := by
        rw [← Real.rpow_mul (by norm_num), mul_assoc, mul_comm (γ : ℝ) p]
      rw [hcp, ← Real.rpow_sub (by norm_num), ← mul_sub]
    calc ∑ k ∈ Finset.range (N * 2 ^ n), P _
        ≤ ∑ _k ∈ Finset.range (N * 2 ^ n),
            (M : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * (q - p * (γ : ℝ)))) :=
          Finset.sum_le_sum hk_le
      _ = (N * 2 ^ n : ℕ) * ((M : ℝ≥0∞) *
            ENNReal.ofReal ((2 : ℝ)⁻¹ ^ ((n : ℝ) * (q - p * (γ : ℝ))))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (N : ℝ≥0∞) * M * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ α) ^ n) := by
          have h2n : (2 : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (-(n : ℝ))) := by
            rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv,
              Real.rpow_natCast, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
          push_cast
          rw [mul_assoc (N : ℝ≥0∞), mul_left_comm ((2 : ℝ≥0∞) ^ n), h2n,
            ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num),
            ← Real.rpow_natCast ((2 : ℝ)⁻¹ ^ α), ← Real.rpow_mul (by norm_num), ← mul_assoc]
          congr 3
          simp only [α]
          ring
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hterm)
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top (by finiteness) ?_
  have hsum : Summable (fun n : ℕ ↦ ((2 : ℝ)⁻¹ ^ α) ^ n) :=
    summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one (by norm_num) (by norm_num) hα)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsum]
  exact ENNReal.ofReal_ne_top

/-- Almost sure pointwise convergence along `approxDyadicNNRat` from the Kolmogorov bound. -/
private lemma ae_tendsto_approxDyadicNNRat {Ω E : Type*} {_ : MeasurableSpace Ω}
    [MetricSpace E] {P : Measure Ω} {Z : Ω → E} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    {N : ℕ} {t : ℝ≥0} (ht : t ≤ N) (hp : 0 < p) (hq : 0 < q)
    (hedist : ∀ r : ℚ≥0, Measurable fun ω ↦ edist (X r ω) (Z ω))
    (hkol : ∀ r : ℚ≥0, (r : ℝ≥0) ≤ N →
      ∫⁻ ω, edist (X r ω) (Z ω) ^ p ∂P ≤ M * edist (r : ℝ≥0) t ^ q) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (approxDyadicNNRat n t) ω) atTop (𝓝 (Z ω)) := by
  set β : ℝ := q / (2 * p)
  have hβ : 0 < β := by positivity
  let A : ℕ → Set Ω := fun n ↦
    {ω | ENNReal.ofReal (((2 : ℝ)⁻¹ ^ β) ^ n) < edist (X (approxDyadicNNRat n t) ω) (Z ω)}
  have hsum_ne_top : ∑' n, P (A n) ≠ ∞ := by
    have hterm (n : ℕ) : P (A n) ≤ M * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (q / 2)) ^ n) := by
      set c : ℝ := ((2 : ℝ)⁻¹ ^ β) ^ n
      have hc_pos : 0 < c := by positivity
      have hkol_n : ∫⁻ ω, edist (X (approxDyadicNNRat n t) ω) (Z ω) ^ p ∂P ≤
          M * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ q) ^ n) := by
        calc ∫⁻ ω, edist (X (approxDyadicNNRat n t) ω) (Z ω) ^ p ∂P
            ≤ M * edist (approxDyadicNNRat n t : ℝ≥0) t ^ q :=
              hkol _ ((approxDyadicNNRat_le n t).trans ht)
          _ ≤ M * (ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n)) ^ q := by
              gcongr
              exact edist_approxDyadicNNRat_le n t
          _ = M * ENNReal.ofReal (((2 : ℝ)⁻¹ ^ q) ^ n) := by
              rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.rpow_natCast,
                ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ) q, Real.rpow_mul (by norm_num),
                Real.rpow_natCast]
      refine (measure_lt_le_lintegral_rpow_div hc_pos hp (hedist _)).trans
        ((ENNReal.div_le_div_right hkol_n _).trans_eq ?_)
      rw [mul_div_assoc, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hc_pos p)]
      congr 1
      have hcp : c ^ p = ((2 : ℝ)⁻¹ ^ (q / 2)) ^ n := by
        have hc_def : c = ((2 : ℝ)⁻¹ ^ (q / (2 * p))) ^ n := rfl
        rw [hc_def, ← Real.rpow_natCast ((2 : ℝ)⁻¹ ^ (q / (2 * p))) n,
          ← Real.rpow_mul (Real.rpow_nonneg (by norm_num) _), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_natCast ((2 : ℝ)⁻¹ ^ (q / 2)) n, ← Real.rpow_mul (by norm_num)]
        congr 1
        field_simp
      have hq2 : (2 : ℝ)⁻¹ ^ q = ((2 : ℝ)⁻¹ ^ (q / 2)) * ((2 : ℝ)⁻¹ ^ (q / 2)) := by
        rw [← Real.rpow_add (by norm_num), add_halves]
      rw [hcp, hq2, mul_pow,
        mul_div_cancel_right₀ _ (pow_ne_zero n (Real.rpow_pos_of_pos (by norm_num) _).ne')]
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
    have hsum : Summable (fun n : ℕ ↦ ((2 : ℝ)⁻¹ ^ (q / 2)) ^ n) :=
      summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one (by norm_num) (by norm_num) (half_pos hq))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum_ne_top] with ω hω
  rw [tendsto_iff_dist_tendsto_zero]
  obtain ⟨m, hm⟩ := eventually_atTop.mp hω
  refine squeeze_zero' (g := fun n ↦ ((2 : ℝ)⁻¹ ^ β) ^ n)
    (eventually_atTop.mpr ⟨m, fun _ _ ↦ dist_nonneg⟩)
    (eventually_atTop.mpr ⟨m, fun n hn ↦ ?_⟩)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) β)
      (Real.rpow_lt_one (by norm_num) (by norm_num) hβ))
  have hle : edist (X (approxDyadicNNRat n t) ω) (Z ω) ≤
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ β) ^ n) := not_lt.mp (hm n hn)
  rw [edist_dist] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (Real.rpow_nonneg (by norm_num) β) n)).mp hle

/-- Outside `limsup (badDyadicEvent X N γ) atTop`, the rational path `r ↦ X r ω` extends from
dyadic rationals in `[0, N]` to a `γ`-Hölder map on `Iic (N : ℝ≥0)`. -/
private lemma exists_holderWith_Iic_of_notMem_limsup_badDyadicEvent {Ω E : Type*}
    [MetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {ω : Ω} {N : ℕ} {γ : ℝ≥0}
    (hγ_pos : 0 < γ) (hω : ω ∉ limsup (badDyadicEvent X N γ) atTop) :
    ∃ (C : ℝ≥0) (g : Iic (N : ℝ≥0) → E), HolderWith C γ g ∧
      ∀ n k (hk : k ≤ N * 2 ^ n),
        g ⟨(dyadicNNRat n k : ℝ≥0), cast_dyadicNNRat_mem_Iic hk⟩ = X (dyadicNNRat n k) ω := by
  rw [mem_limsup_iff_frequently_mem, not_frequently] at hω
  obtain ⟨m, hm⟩ := eventually_atTop.mp hω
  refine exists_holderWith_Iic_of_dyadic_adj (f := fun r ↦ X r ω) (m := m) hγ_pos
    fun j hj k hk ↦ ?_
  have hnot : ω ∉ badDyadicEvent X N γ j := hm j hj
  simp only [badDyadicEvent, mem_iUnion, Finset.mem_range, mem_ofPred, not_exists, not_lt] at hnot
  have hed := hnot k hk
  rw [edist_dist] at hed
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hed

/-- Canonical pathwise dyadic limit on `G`, equal to the constant path `X 0 ω` outside `G`. -/
private def dyadicExtension {Ω E : Type*} [TopologicalSpace E] (X : ℚ≥0 → Ω → E)
    (G : Set Ω) [DecidablePred (· ∈ G)] (t : ℝ≥0) (ω : Ω) : E :=
  letI : Nonempty E := ⟨X 0 ω⟩
  limUnder atTop (fun n ↦ if ω ∈ G then X (approxDyadicNNRat n t) ω else X 0 ω)

private lemma dyadicExtension_eq_of_mem {Ω E : Type*} [TopologicalSpace E] [T2Space E]
    {X : ℚ≥0 → Ω → E} {G : Set Ω} [DecidablePred (· ∈ G)] {ω : Ω} (hω : ω ∈ G)
    {N : ℕ} {g : Iic (N : ℝ≥0) → E} (hg_cont : Continuous g)
    (hg_dyad : ∀ n k (hk : k ≤ N * 2 ^ n),
      g ⟨(dyadicNNRat n k : ℝ≥0), cast_dyadicNNRat_mem_Iic hk⟩ = X (dyadicNNRat n k) ω)
    {t : ℝ≥0} (ht : t ≤ N) :
    dyadicExtension X G t ω = g ⟨t, ht⟩ := by
  let : Nonempty E := ⟨X 0 ω⟩
  exact ((tendsto_approxDyadicNNRat_apply_of_continuous (f := fun r ↦ X r ω)
    hg_cont hg_dyad ⟨t, ht⟩) |>.congr fun _ ↦ by simp [hω]).limUnder_eq

private lemma measurable_dyadicExtension {Ω E : Type*} {_ : MeasurableSpace Ω}
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀) (hmeasX : ∀ r : ℚ≥0, Measurable (X r))
    {G : Set Ω} [DecidablePred (· ∈ G)] (hG_meas : MeasurableSet G)
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∉ limsup (badDyadicEvent X N γ₀) atTop) (t : ℝ≥0) :
    Measurable (dyadicExtension X G t) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω ↦ if ω ∈ G then X (approxDyadicNNRat n t) ω else X 0 ω)
    (fun _ ↦ Measurable.ite hG_meas (hmeasX _) (hmeasX 0)) (tendsto_pi_nhds.2 fun ω ↦ ?_)
  by_cases hω : ω ∈ G
  · let N := ⌈(t : ℝ)⌉₊
    have htN : t ≤ N := by exact_mod_cast Nat.le_ceil (t : ℝ)
    obtain ⟨_, g, hg_h, hg_d⟩ :=
      exists_holderWith_Iic_of_notMem_limsup_badDyadicEvent hγ₀_pos (hG_sub ω hω N)
    have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
    rw [dyadicExtension_eq_of_mem hω hg_cont hg_d htN]
    exact (tendsto_approxDyadicNNRat_apply_of_continuous (f := fun r ↦ X r ω)
      hg_cont hg_d ⟨t, htN⟩).congr fun _ ↦ by simp [hω]
  · let : Nonempty E := ⟨X 0 ω⟩
    have hlim : dyadicExtension X G t ω = X 0 ω :=
      (tendsto_const_nhds.congr fun _ ↦ by simp [hω]).limUnder_eq
    simp [hω, hlim]

private lemma continuous_dyadicExtension {Ω E : Type*}
    [MetricSpace E] [CompleteSpace E] {X : ℚ≥0 → Ω → E} {γ₀ : ℝ≥0} (hγ₀_pos : 0 < γ₀)
    {G : Set Ω} [DecidablePred (· ∈ G)]
    (hG_sub : ∀ ω ∈ G, ∀ N : ℕ, ω ∉ limsup (badDyadicEvent X N γ₀) atTop) (ω : Ω) :
    Continuous (dyadicExtension X G · ω) := by
  by_cases hω : ω ∈ G
  · rw [continuous_iff_continuousAt]
    intro t
    let N := ⌊(t : ℝ)⌋₊ + 1
    have ht_lt : t < (N : ℝ≥0) := by exact_mod_cast Nat.lt_floor_add_one (t : ℝ)
    obtain ⟨_, g, hg_h, hg_d⟩ :=
      exists_holderWith_Iic_of_notMem_limsup_badDyadicEvent hγ₀_pos (hG_sub ω hω N)
    have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
    have hcon : ContinuousOn (dyadicExtension X G · ω) (Iic (N : ℝ≥0)) :=
      continuousOn_iff_continuous_domRestrict.mpr
        (hg_cont.congr fun s ↦ (dyadicExtension_eq_of_mem hω hg_cont hg_d s.2).symm)
    exact hcon.continuousAt (Iic_mem_nhds ht_lt)
  · let : Nonempty E := ⟨X 0 ω⟩
    have hconst : (dyadicExtension X G · ω) = fun _ ↦ X 0 ω := funext fun _ ↦
      (tendsto_const_nhds.congr fun _ ↦ by simp [hω]).limUnder_eq
    rw [hconst]
    exact continuous_const

/-- **Kolmogorov–Chentsov extension from nonnegative rational times.** Let `X : ℚ≥0 → Ω → E` take
values in a complete metric Borel space `E`, with Borel-measurable pair evaluations and a local
Kolmogorov bound of exponents `p > 0` and `q > 1` on each bounded horizon `[0, N]`. Then `X`
extends to a process `Y : ℝ≥0 → Ω → E` such that:

1. `Y t` is Borel measurable for every `t : ℝ≥0`;
2. `t ↦ Y t ω` is continuous for *every* `ω : Ω`;
3. `Y q =ᵐ[P] X q` for every `q : ℚ≥0`;
4. for every `0 < γ < (q - 1) / p` and `T : ℝ≥0`, almost every path of `Y` is `γ`-Hölder
   continuous on `Iic T`. -/
theorem exists_continuous_extension_of_nnrat {Ω E : Type*} {_ : MeasurableSpace Ω}
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℚ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0}
    (hp : 0 < p) (hq : 1 < q)
    (hpair : ∀ r s : ℚ≥0, Measurable[_, borel (E × E)] fun ω ↦ (X r ω, X s ω))
    (hkol : ∀ (N : ℕ) (r s : ℚ≥0), (r : ℝ≥0) ≤ N → (s : ℝ≥0) ≤ N →
      ∫⁻ ω, edist (X r ω) (X s ω) ^ p ∂P ≤ M N * edist (r : ℝ≥0) (s : ℝ≥0) ^ q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ r : ℚ≥0, Y r =ᵐ[P] X r) ∧
      (∀ (γ : ℝ≥0), 0 < γ → (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∀ᵐ ω ∂P, ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  classical
  have hedist (r s : ℚ≥0) : Measurable fun ω ↦ edist (X r ω) (X s ω) := by
    borelize (E × E)
    exact continuous_edist.measurable.comp (hpair r s)
  have hmeasX (r : ℚ≥0) : Measurable (X r) :=
    (measurable_fst.mono prod_le_borel_prod le_rfl).comp (hpair r r)
  -- Pick `γ₀ = (q - 1) / (2 p)` to define the canonical full-measure event `G`.
  have hq1 : 0 < q - 1 := sub_pos.2 hq
  let γ₀ : ℝ≥0 := ⟨(q - 1) / (2 * p), by positivity⟩
  have hγ₀_val : (γ₀ : ℝ) = (q - 1) / (2 * p) := rfl
  have hγ₀_pos : 0 < γ₀ := by rw [← NNReal.coe_pos, hγ₀_val]; positivity
  have hγ₀_lt : (γ₀ : ℝ) < (q - 1) / p := by
    rw [hγ₀_val]
    have hpos : 0 < (q - 1) / p := div_pos hq1 hp
    have hhalf : (q - 1) / (2 * p) = ((q - 1) / p) / 2 := by ring
    linarith
  let G : Set Ω := ⋂ N : ℕ, (limsup (badDyadicEvent X N γ₀) atTop)ᶜ
  have hG_meas : MeasurableSet G := by
    refine MeasurableSet.iInter fun N ↦ MeasurableSet.compl ?_
    rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iUnion fun n ↦
      MeasurableSet.iUnion fun _ ↦ measurableSet_badDyadicEvent hedist N γ₀ n
  have hG_ae : ∀ᵐ ω ∂P, ω ∈ G := by
    simp only [G, mem_iInter, mem_compl_iff, ae_all_iff]
    intro N
    simpa [ae_iff] using measure_limsup_badDyadicEvent_eq_zero hp hγ₀_lt hedist (hkol N)
  have hG_sub (ω : Ω) (hω : ω ∈ G) (N : ℕ) : ω ∉ limsup (badDyadicEvent X N γ₀) atTop :=
    mem_iInter.mp hω N
  have hY_nnrat (r : ℚ≥0) : dyadicExtension X G r =ᵐ[P] X r := by
    let N := ⌈((r : ℝ≥0) : ℝ)⌉₊
    have hrN : (r : ℝ≥0) ≤ N := by exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
    have hae := ae_tendsto_approxDyadicNNRat (Z := X r) hrN hp (zero_lt_one.trans hq)
      (fun s ↦ hedist s r) (fun s hs ↦ hkol N s r hs hrN)
    filter_upwards [hG_ae, hae] with ω hω htend
    obtain ⟨_, g, hg_h, hg_d⟩ :=
      exists_holderWith_Iic_of_notMem_limsup_badDyadicEvent hγ₀_pos (hG_sub ω hω N)
    have hg_cont : Continuous g := (hg_h.uniformContinuous hγ₀_pos).continuous
    have hY_tend :
        Tendsto (fun n ↦ X (approxDyadicNNRat n (r : ℝ≥0)) ω)
          atTop (𝓝 (dyadicExtension X G r ω)) := by
      rw [dyadicExtension_eq_of_mem hω hg_cont hg_d hrN]
      exact tendsto_approxDyadicNNRat_apply_of_continuous (f := fun s ↦ X s ω) hg_cont hg_d
        ⟨(r : ℝ≥0), hrN⟩
    exact tendsto_nhds_unique hY_tend htend
  refine ⟨dyadicExtension X G, measurable_dyadicExtension hγ₀_pos hmeasX hG_meas hG_sub,
    continuous_dyadicExtension hγ₀_pos hG_sub, hY_nnrat, fun γ hγ_pos hγ_lt T ↦ ?_⟩
  let N := ⌈(T : ℝ)⌉₊
  have hTN : T ≤ N := by exact_mod_cast Nat.le_ceil (T : ℝ)
  have hbad_γ : ∀ᵐ ω ∂P, ω ∉ limsup (badDyadicEvent X N γ) atTop := by
    simpa [ae_iff] using measure_limsup_badDyadicEvent_eq_zero hp hγ_lt hedist (hkol N)
  filter_upwards [hG_ae, hbad_γ] with ω hωG hωγ
  obtain ⟨C, g, hg_holder, hg_dyad⟩ :=
    exists_holderWith_Iic_of_notMem_limsup_badDyadicEvent hγ_pos hωγ
  have hg_cont : Continuous g := (hg_holder.uniformContinuous hγ_pos).continuous
  refine ⟨C, HolderOnWith.of_dist_le fun s hs t ht ↦ ?_⟩
  have hsN : s ≤ N := hs.trans hTN
  have htN : t ≤ N := ht.trans hTN
  rw [dyadicExtension_eq_of_mem hωG hg_cont hg_dyad hsN,
    dyadicExtension_eq_of_mem hωG hg_cont hg_dyad htN]
  exact hg_holder.dist_le ⟨s, hsN⟩ ⟨t, htN⟩

/-- **Local one-dimensional Kolmogorov–Chentsov theorem on `ℝ≥0`.** If `X : ℝ≥0 → Ω → E` into a
complete metric Borel space satisfies `IsKolmogorovProcess` on each compact horizon `Iic (N : ℝ≥0)`
with exponents `p > 0` and `q > 1`, then `X` admits an all-paths continuous, coordinatewise
measurable modification `Y` whose paths are almost surely locally `γ`-Hölder for every
`0 < γ < (q - 1) / p`. -/
theorem exists_continuous_modification_of_local_isKolmogorovProcess
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℕ → ℝ≥0} (hq : 1 < q)
    (hX : ∀ N : ℕ, IsKolmogorovProcess (fun t : Iic (N : ℝ≥0) ↦ X t) P p q (M N)) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (γ : ℝ≥0), 0 < γ → (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∀ᵐ ω ∂P, ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  have hp : 0 < p := (hX 0).p_pos
  obtain ⟨Y, hY_meas, hY_cont, hY_nnrat, hY_holder⟩ :=
    exists_continuous_extension_of_nnrat (X := fun r : ℚ≥0 ↦ X r) hp hq
      (fun r s ↦ by
        let N := max ⌈((r : ℝ≥0) : ℝ)⌉₊ ⌈((s : ℝ≥0) : ℝ)⌉₊
        have hr_ceil : (r : ℝ≥0) ≤ ⌈((r : ℝ≥0) : ℝ)⌉₊ := by
          exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
        have hs_ceil : (s : ℝ≥0) ≤ ⌈((s : ℝ≥0) : ℝ)⌉₊ := by
          exact_mod_cast Nat.le_ceil ((s : ℝ≥0) : ℝ)
        have hrN : (r : ℝ≥0) ≤ N := hr_ceil.trans (Nat.cast_le.mpr (le_max_left _ _))
        have hsN : (s : ℝ≥0) ≤ N := hs_ceil.trans (Nat.cast_le.mpr (le_max_right _ _))
        exact (hX N).measurablePair ⟨r, hrN⟩ ⟨s, hsN⟩)
      (fun N r s hr hs ↦ (hX N).kolmogorovCondition ⟨r, hr⟩ ⟨s, hs⟩)
  refine ⟨Y, hY_meas, hY_cont, fun t ↦ ?_, hY_holder⟩
  let N := ⌈(t : ℝ)⌉₊
  have htN : t ≤ N := by exact_mod_cast Nat.le_ceil (t : ℝ)
  have haeX := ae_tendsto_approxDyadicNNRat (X := fun r : ℚ≥0 ↦ X r) (Z := X t)
    htN hp (zero_lt_one.trans hq)
    (fun r ↦ by
      let K := max N ⌈((r : ℝ≥0) : ℝ)⌉₊
      have htK : t ≤ K := htN.trans (Nat.cast_le.mpr (le_max_left _ _))
      have hr_ceil : (r : ℝ≥0) ≤ ⌈((r : ℝ≥0) : ℝ)⌉₊ := by
        exact_mod_cast Nat.le_ceil ((r : ℝ≥0) : ℝ)
      have hrK : (r : ℝ≥0) ≤ K := hr_ceil.trans (Nat.cast_le.mpr (le_max_right _ _))
      exact (hX K).measurable_edist (s := ⟨r, hrK⟩) (t := ⟨t, htK⟩))
    (fun r hr ↦ (hX N).kolmogorovCondition ⟨r, hr⟩ ⟨t, htN⟩)
  have hae_dyad : ∀ᵐ ω ∂P, ∀ n, Y (approxDyadicNNRat n t) ω = X (approxDyadicNNRat n t) ω :=
    ae_all_iff.mpr fun n ↦ hY_nnrat (approxDyadicNNRat n t)
  filter_upwards [haeX, hae_dyad] with ω hX_tend hYX
  have hY_tend : Tendsto (fun n ↦ X (approxDyadicNNRat n t) ω) atTop (𝓝 (Y t ω)) :=
    ((hY_cont ω).tendsto t).comp (tendsto_approxDyadicNNRat t) |>.congr hYX
  exact tendsto_nhds_unique hY_tend hX_tend

end StochasticExtension

end TauCeti

namespace ProbabilityTheory

/-- **One-dimensional Kolmogorov–Chentsov theorem** for `IsKolmogorovProcess` on `ℝ≥0`. -/
theorem IsKolmogorovProcess.exists_continuous_modification
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (γ : ℝ≥0), 0 < γ → (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∀ᵐ ω ∂P, ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) :=
  TauCeti.exists_continuous_modification_of_local_isKolmogorovProcess (M := fun _ ↦ M) hq
    fun _ ↦
      { measurablePair := fun s t ↦ hX.measurablePair s.1 t.1
        kolmogorovCondition := fun s t ↦ hX.kolmogorovCondition s.1 t.1
        p_pos := hX.p_pos
        q_pos := hX.q_pos }

/-- **One-dimensional Kolmogorov–Chentsov theorem** for `IsAEKolmogorovProcess` on `ℝ≥0`. -/
theorem IsAEKolmogorovProcess.exists_continuous_modification
    {Ω E : Type*} {_ : MeasurableSpace Ω}
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {X : ℝ≥0 → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → E,
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ ω : Ω, Continuous (Y · ω)) ∧
      (∀ t : ℝ≥0, Y t =ᵐ[P] X t) ∧
      (∀ (γ : ℝ≥0), 0 < γ → (γ : ℝ) < (q - 1) / p → ∀ T : ℝ≥0,
        ∀ᵐ ω ∂P, ∃ C : ℝ≥0, HolderOnWith C γ (Y · ω) (Iic T)) := by
  obtain ⟨Y, hYm, hYc, hYmk, hYh⟩ := hX.IsKolmogorovProcess_mk.exists_continuous_modification hq
  exact ⟨Y, hYm, hYc, fun t ↦ (hYmk t).trans (hX.ae_eq_mk t).symm, hYh⟩

end ProbabilityTheory
