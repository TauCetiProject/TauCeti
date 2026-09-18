/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.ArithmeticDirichletSeries.AbelSummation
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
public import TauCeti.NumberTheory.NumberField.DirichletDensityBounds

/-!
# Natural density of sets of prime ideals

For a number field `K`, this file defines the natural density of a set `S` of nonzero prime
ideals as the limit

```text
  primeCount K S x / primeCount K Set.univ x
```

as the inclusive real cutoff `x` tends to infinity. This normalization matches Mathlib's
ratio-normalized `NumberField.Set.HasDirichletDensity`: a density is measured relative to all
prime ideals of the same number field, rather than relative to an external approximation such as
`x / log x`.

The denominator really tends to infinity. Indeed, lying over supplies a prime of `𝓞 K` above
every rational prime, so the height-one spectrum is infinite. Its bounded-norm subsets are finite
and exhaust the spectrum, whence their cardinalities tend to infinity. This fact both makes the
whole spectrum have density one and ensures that a fixed finite error disappears in the ratio.

## Main results

* `NumberField.Set.HasNaturalDensity`: ratio-normalized natural density for a set of prime ideals.
* `NumberField.Set.hasNaturalDensity_def`: the defining ratio-convergence characterization.
* `NumberField.Set.HasNaturalDensity.union`,
  `NumberField.Set.hasNaturalDensity_biUnion_finset` and
  `NumberField.Set.HasNaturalDensity.compl`: finite Boolean calculus for natural density.
* `NumberField.Set.HasNaturalDensity.of_finite_symmDiff`: changing a prime set on finitely many
  primes preserves its natural density.
* `NumberField.Set.hasNaturalDensity_of_finite`: every finite set of prime ideals has natural
  density zero.
* `NumberField.Set.isUpperDirichletDensityBound_of_eventually_primeCount_le` and
  `NumberField.Set.isLowerDirichletDensityBound_of_eventually_le_primeCount`: an eventual
  one-sided bound on the proportion of primes of `S` below `x` is the same one-sided bound for
  Dirichlet density.
* `NumberField.Set.hasDirichletDensity_of_hasNaturalDensity`: natural density implies Dirichlet
  density, with the same value.

The comparison with Dirichlet density rests on two inputs. Abel summation against the decreasing
function `t ↦ t ^ (-s)` (`TauCeti.tsum_mul_le_of_summatory_le`) turns an eventual bound
`π_S(x) ≤ c · π(x)` into a bound `P_S(s) ≤ c · P(s) + C` with `C` independent of `s > 1`, where
`P_S` is Mathlib's `NumberField.Set.primeIdealZetaSum S`. The all-prime sum `P(s)` tends to
infinity as `s → 1⁺` (`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), so the constant `C`
disappears from the ratio `P_S(s) / P(s)`.

The definition, its elementary calculus, and the comparison with Dirichlet density are standard;
see J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4, J.-P. Serre, *Corps locaux*, Chapter
VI, or J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

namespace NumberField.Set

open Filter IsDedekindDomain
open scoped NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ ε : ℝ}

/-- A set `S` of height-one primes of a number field has natural density `δ` when the proportion
of primes of `S` below `x`, relative to all primes below `x`, tends to `δ` as `x → ∞`.

Both counts use the inclusive real cutoff fixed by `TauCeti.primeCount`. -/
def HasNaturalDensity (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
    TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ)

/-- Unfolds `HasNaturalDensity` to the convergence of the ratio of prime counts. -/
theorem hasNaturalDensity_def :
    HasNaturalDensity S δ ↔ Tendsto (fun x : ℝ => TauCeti.primeCount K S x /
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 δ) :=
  (Iff.rfl)

/-- A set of prime ideals has at most one natural density. -/
theorem HasNaturalDensity.unique (hδ : HasNaturalDensity S δ) (hε : HasNaturalDensity S ε) :
    δ = ε :=
  tendsto_nhds_unique hδ hε

/-- The empty set of prime ideals has natural density zero. -/
@[simp]
theorem hasNaturalDensity_empty :
    HasNaturalDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [hasNaturalDensity_def]

/-- The set of all prime ideals has natural density one. -/
@[simp]
theorem hasNaturalDensity_univ :
    HasNaturalDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  rw [hasNaturalDensity_def]
  have hne : ∀ᶠ x : ℝ in atTop,
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x ≠ 0 :=
    ((TauCeti.tendsto_primeCount_univ_atTop K).eventually_gt_atTop 0).mono
      fun _ hx => hx.ne'
  exact tendsto_const_nhds.congr' (hne.mono fun _ hx => (div_self hx).symm)

/-- A natural density is nonnegative. -/
theorem HasNaturalDensity.nonneg (h : HasNaturalDensity S δ) : 0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun x =>
    div_nonneg (TauCeti.primeCount_nonneg S x) (TauCeti.primeCount_nonneg Set.univ x)

/-- A natural density is at most one. -/
theorem HasNaturalDensity.le_one (h : HasNaturalDensity S δ) : δ ≤ 1 :=
  le_of_tendsto h <| Eventually.of_forall fun x =>
    div_le_one_of_le₀ (TauCeti.primeCount_mono_set (Set.subset_univ S) x)
      (TauCeti.primeCount_nonneg Set.univ x)

/-- Inclusion of prime sets orders their natural densities, when both densities exist. -/
theorem HasNaturalDensity.mono (hST : S ⊆ T) (hS : HasNaturalDensity S δ)
    (hT : HasNaturalDensity T ε) : δ ≤ ε := by
  refine le_of_tendsto_of_tendsto hS hT (Eventually.of_forall fun x => ?_)
  exact div_le_div_of_nonneg_right (TauCeti.primeCount_mono_set hST x)
    (TauCeti.primeCount_nonneg Set.univ x)

/-- Natural density is additive on disjoint unions of prime sets. -/
theorem HasNaturalDensity.union (hS : HasNaturalDensity S δ) (hT : HasNaturalDensity T ε)
    (hST : Disjoint S T) : HasNaturalDensity (S ∪ T) (δ + ε) := by
  rw [hasNaturalDensity_def] at hS hT ⊢
  simpa only [TauCeti.primeCount_union hST, add_div] using hS.add hT

/-- Natural density is additive on a finite family of pairwise disjoint prime sets. -/
theorem hasNaturalDensity_biUnion_finset {ι : Type*} {s : Finset ι}
    {f : ι → Set (HeightOneSpectrum (𝓞 K))} {d : ι → ℝ}
    (hf : ∀ i ∈ s, HasNaturalDensity (f i) (d i))
    (hdisj : (s : Set ι).PairwiseDisjoint f) :
    HasNaturalDensity (⋃ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    refine (hf a (Finset.mem_insert_self a s)).union
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (hdisj.subset (by simp))) ?_
    rw [_root_.Set.disjoint_iUnion₂_right]
    intro i hi
    exact hdisj (by simp) (by simp [hi]) fun h => ha (h ▸ hi)

/-- The complement of a set of natural density `δ` has natural density `1 - δ`. -/
theorem HasNaturalDensity.compl (hS : HasNaturalDensity S δ) :
    HasNaturalDensity Sᶜ (1 - δ) := by
  rw [hasNaturalDensity_def] at hS ⊢
  have hne : ∀ᶠ x : ℝ in atTop,
      TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x ≠ 0 :=
    ((TauCeti.tendsto_primeCount_univ_atTop K).eventually_gt_atTop 0).mono
      fun _ hx => hx.ne'
  refine (tendsto_const_nhds.sub hS).congr' (hne.mono fun x hx => ?_)
  simp only
  rw [← div_self hx, ← sub_div]
  have hdisj : Disjoint S Sᶜ := _root_.Set.disjoint_left.mpr fun _ hmem hcompl => hcompl hmem
  have hcount : TauCeti.primeCount K Set.univ x =
      TauCeti.primeCount K S x + TauCeti.primeCount K Sᶜ x := by
    rw [← TauCeti.primeCount_union hdisj, _root_.Set.union_compl_self]
  rw [hcount]
  ring

/-- Changing a set on finitely many prime ideals preserves its natural density. -/
theorem HasNaturalDensity.of_finite_symmDiff (hT : HasNaturalDensity T δ)
    (hST : (symmDiff S T).Finite) : HasNaturalDensity S δ := by
  rw [hasNaturalDensity_def] at hT ⊢
  let c : ℝ := ∑ v ∈ hST.toFinset, (S.indicator 1 v - T.indicator 1 v)
  have hzero : Tendsto (fun x : ℝ =>
      (TauCeti.primeCount K S x - TauCeti.primeCount K T x) /
        TauCeti.primeCount K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x) atTop (𝓝 0) := by
    refine ((TauCeti.tendsto_primeCount_univ_atTop K).const_div_atTop c).congr' ?_
    filter_upwards [TauCeti.eventually_primeCount_sub_eq hST] with x hx
    rw [hx]
  have hsum := hT.add hzero
  simp only [add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun x => ?_)
  ring

/-- Two prime sets with finite symmetric difference have natural density `δ` simultaneously. -/
theorem hasNaturalDensity_iff_of_finite_symmDiff (hST : (symmDiff S T).Finite) :
    HasNaturalDensity S δ ↔ HasNaturalDensity T δ := by
  refine ⟨fun h => h.of_finite_symmDiff ?_, fun h => h.of_finite_symmDiff hST⟩
  simpa [symmDiff_comm] using hST

/-- Every finite set of prime ideals has natural density zero. -/
theorem hasNaturalDensity_of_finite (hS : S.Finite) : HasNaturalDensity S 0 := by
  refine hasNaturalDensity_empty.of_finite_symmDiff ?_
  simpa [Set.symmDiff_def] using hS

/-! ### Natural density implies Dirichlet density -/

/-- If the prime summatory function of a bounded real weight `w` is eventually nonpositive, then
the prime Dirichlet series of `w` is bounded above uniformly in `s > 1`.

This is Abel summation against the decreasing function `t ↦ t ^ (-s)`: the partial sums of `w`
are bounded above by a constant independent of `s`, and so is the twisted series. -/
private theorem exists_tsum_mul_rpow_le_of_eventually_primeSummatory_nonpos
    {w : HeightOneSpectrum (𝓞 K) → ℝ} {B : ℝ} (hB : ∀ v, |w v| ≤ B)
    (hw : ∀ᶠ x in atTop, TauCeti.primeSummatory K w x ≤ 0) :
    ∃ C, ∀ s : ℝ, 1 < s → ∑' v, w v * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ C := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 hw
  have hC0 : 0 ≤ ∑ v ∈ TauCeti.primesLE K X, |w v| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  -- Beyond `X` the partial sums are nonpositive; below `X` they are bounded by the total mass
  -- of `|w|` on the primes of norm at most `X`.
  have hF : ∀ t, TauCeti.primeSummatory K w t ≤ ∑ v ∈ TauCeti.primesLE K X, |w v| := by
    intro t
    rcases le_total X t with h | h
    · exact (hX t h).trans hC0
    · rw [TauCeti.primeSummatory_apply]
      exact (Finset.sum_le_sum fun v _ ↦ le_abs_self (w v)).trans <|
        Finset.sum_le_sum_of_subset_of_nonneg (TauCeti.normLE_mono _ h)
          fun _ _ _ ↦ abs_nonneg _
  refine ⟨∑ v ∈ TauCeti.primesLE K X, |w v|, fun s hs ↦ ?_⟩
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 K) ↦
      w v * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) :=
    ((TauCeti.summable_absNorm_rpow_primes_of_one_lt hs).mul_left B).of_norm_bounded
      fun v ↦ by
        have ha : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        rw [norm_mul, Real.norm_of_nonneg ha, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hB v) ha
  have hbound := TauCeti.tsum_mul_le_of_summatory_le
    (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (fun v ↦ NumberField.HeightOneSpectrum.one_lt_absNorm v) w (g := fun t ↦ t ^ (-s))
    (fun t _ ↦ hF t)
    (fun t ht ↦ (Real.hasDerivAt_rpow_const (Or.inl (by linarith))).differentiableAt)
    (fun x ↦ by
      rw [Real.deriv_rpow_const']
      exact ContinuousOn.integrableOn_Icc <| continuousOn_const.mul <|
        continuousOn_id.rpow_const fun t ht ↦ Or.inl (by rw [id]; linarith [ht.1]))
    (fun t ht ↦ by
      rw [Real.deriv_rpow_const]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    (fun t _ ↦ by positivity) hsum
  exact hbound.trans <| mul_le_of_le_one_right hC0 <|
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

/-- For `s > 1`, the prime Dirichlet series of the weight `𝔭 ↦ 1_S(𝔭) - c` is
`P_S(s) - c · P(s)`. -/
private theorem tsum_indicator_sub_mul_rpow (S : Set (HeightOneSpectrum (𝓞 K))) (c : ℝ) {s : ℝ}
    (hs : 1 < s) :
    ∑' v, (S.indicator 1 v - c) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) =
      primeIdealZetaSum S s -
        c * primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s := by
  have hU := TauCeti.summable_absNorm_rpow_primes_of_one_lt (K := K) hs
  rw [primeIdealZetaSum_def,
    tsum_subtype S fun v : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s),
    primeIdealZetaSum_univ, ← tsum_mul_left,
    ← (hU.indicator S).tsum_sub (hU.mul_left c)]
  refine tsum_congr fun v ↦ ?_
  by_cases hv : v ∈ S <;> simp [hv, sub_mul]

/-- The prime summatory function of the weight `𝔭 ↦ 1_S(𝔭) - c` is `π_S(x) - c · π(x)`. -/
private theorem primeSummatory_indicator_sub (S : Set (HeightOneSpectrum (𝓞 K))) (c x : ℝ) :
    TauCeti.primeSummatory K (fun v ↦ S.indicator 1 v - c) x =
      TauCeti.primeCount K S x - c * TauCeti.primeCount K Set.univ x := by
  simp [TauCeti.primeSummatory_apply, TauCeti.primeCount_apply, Finset.sum_sub_distrib, mul_comm]

omit [NumberField K] in
/-- The weight `𝔭 ↦ 1_S(𝔭) - c` is bounded by `1 + |c|`. -/
private theorem abs_indicator_sub_le (S : Set (HeightOneSpectrum (𝓞 K))) (c : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) : |S.indicator 1 v - c| ≤ 1 + |c| := by
  have h1 : |S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) v| ≤ 1 := by
    by_cases hv : v ∈ S <;> simp [hv]
  linarith [abs_sub (S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ) v) c]

/-- **Upper natural bounds are upper Dirichlet bounds.** If eventually at most the proportion `c`
of the primes of norm at most `x` lie in `S`, then `c` is an upper Dirichlet-density bound for
`S`.

The proof bounds `P_S(s) - c · P(s)` uniformly in `s > 1` by Abel summation and divides by the
all-prime sum `P(s)`, which tends to infinity as `s → 1⁺`. -/
theorem isUpperDirichletDensityBound_of_eventually_primeCount_le {c : ℝ}
    (h : ∀ᶠ x in atTop, TauCeti.primeCount K S x ≤ c * TauCeti.primeCount K Set.univ x) :
    IsUpperDirichletDensityBound S c := by
  obtain ⟨C, hC⟩ := exists_tsum_mul_rpow_le_of_eventually_primeSummatory_nonpos
    (abs_indicator_sub_le S c) (h.mono fun x hx ↦ by
      rw [primeSummatory_indicator_sub]
      linarith)
  refine isUpperDirichletDensityBound_iff.2 fun ε hε ↦ ?_
  filter_upwards [self_mem_nhdsWithin,
    (TauCeti.tendsto_primeIdealZetaSum_univ_atTop (K := K)).eventually_gt_atTop (max (C / ε) 0)]
    with s (hs : 1 < s) hP
  have hP0 : 0 < primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
    (le_max_right _ _).trans_lt hP
  have hCP := (div_lt_iff₀' hε).1 ((le_max_left _ _).trans_lt hP)
  have := hC s hs
  rw [tsum_indicator_sub_mul_rpow S c hs] at this
  rw [div_lt_iff₀ hP0, add_mul]
  linarith

/-- **Lower natural bounds are lower Dirichlet bounds.** If eventually at least the proportion `c`
of the primes of norm at most `x` lie in `S`, then `c` is a lower Dirichlet-density bound for
`S`. -/
theorem isLowerDirichletDensityBound_of_eventually_le_primeCount {c : ℝ}
    (h : ∀ᶠ x in atTop, c * TauCeti.primeCount K Set.univ x ≤ TauCeti.primeCount K S x) :
    IsLowerDirichletDensityBound S c := by
  obtain ⟨C, hC⟩ := exists_tsum_mul_rpow_le_of_eventually_primeSummatory_nonpos
    (w := fun v ↦ -(S.indicator 1 v - c))
    (fun v ↦ by rw [abs_neg]; exact abs_indicator_sub_le S c v)
    (h.mono fun x hx ↦ by
      rw [TauCeti.primeSummatory_apply, Finset.sum_neg_distrib, ← TauCeti.primeSummatory_apply,
        primeSummatory_indicator_sub]
      linarith)
  refine isLowerDirichletDensityBound_iff.2 fun ε hε ↦ ?_
  filter_upwards [self_mem_nhdsWithin,
    (TauCeti.tendsto_primeIdealZetaSum_univ_atTop (K := K)).eventually_gt_atTop (max (C / ε) 0)]
    with s (hs : 1 < s) hP
  have hP0 : 0 < primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
    (le_max_right _ _).trans_lt hP
  have hCP := (div_lt_iff₀' hε).1 ((le_max_left _ _).trans_lt hP)
  have := hC s hs
  simp only [neg_mul, tsum_neg, tsum_indicator_sub_mul_rpow S c hs] at this
  rw [lt_div_iff₀ hP0, sub_mul]
  linarith

/-- **Natural density implies Dirichlet density.** A set of prime ideals with natural density `δ`
has Dirichlet density `δ`. -/
theorem hasDirichletDensity_of_hasNaturalDensity (h : HasNaturalDensity S δ) :
    HasDirichletDensity S δ := by
  have hpos := (TauCeti.tendsto_primeCount_univ_atTop K).eventually_gt_atTop 0
  refine hasDirichletDensity_of_upperBound_of_lowerBound
    (isUpperDirichletDensityBound_iff.2 fun ε hε ↦ ?_)
    (isLowerDirichletDensityBound_iff.2 fun ε hε ↦ ?_)
  · have hup : IsUpperDirichletDensityBound S (δ + ε / 2) :=
      isUpperDirichletDensityBound_of_eventually_primeCount_le <| by
        filter_upwards [(tendsto_order.1 (hasNaturalDensity_def.1 h)).2 _
          (by linarith : δ < δ + ε / 2), hpos] with x hx hx0
        exact ((div_lt_iff₀ hx0).1 hx).le
    filter_upwards [isUpperDirichletDensityBound_iff.1 hup (ε / 2) (half_pos hε)] with s hs
    linarith
  · have hlow : IsLowerDirichletDensityBound S (δ - ε / 2) :=
      isLowerDirichletDensityBound_of_eventually_le_primeCount <| by
        filter_upwards [(tendsto_order.1 (hasNaturalDensity_def.1 h)).1 _
          (by linarith : δ - ε / 2 < δ), hpos] with x hx hx0
        exact ((lt_div_iff₀ hx0).1 hx).le
    filter_upwards [isLowerDirichletDensityBound_iff.1 hlow (ε / 2) (half_pos hε)] with s hs
    linarith

end NumberField.Set
