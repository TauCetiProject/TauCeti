/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum

/-!
# Sets of primes of Dirichlet density zero

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that
`P_S(s) / P(s) → δ` as `s → 1⁺`, where `P_S(s) = ∑_{𝔭 ∈ S} N(𝔭) ^ (-s)` and `P` is the sum over
all height-one primes. Since `P(s) → ∞` as `s → 1⁺`
(`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), any set whose partial sum stays bounded near
`1` has Dirichlet density zero. This covers every finite set of primes, and every set whose
series `∑_{𝔭 ∈ S} N(𝔭)⁻¹` converges, such as the primes of residue degree greater than one.

A set of density zero is negligible: two sets whose symmetric difference has density zero have
the same Dirichlet density, or neither has one. In particular the Dirichlet density of a set of
primes does not change when finitely many primes are added or removed, or when the set is
restricted to the primes of residue degree one.

## Main results

* `NumberField.Set.hasDirichletDensity_zero_of_eventually_le`: a set whose partial sum is bounded
  as `s → 1⁺` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_zero_of_summable`: a set of primes with
  `∑_{𝔭 ∈ S} N(𝔭)⁻¹ < ∞` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_of_finite`: a finite set of primes has Dirichlet density
  zero, so a set of nonzero Dirichlet density is infinite
  (`NumberField.Set.HasDirichletDensity.infinite`).
* `NumberField.Set.hasDirichletDensity_iff_of_symmDiff`: sets whose symmetric difference has
  density zero have the same densities; `NumberField.Set.hasDirichletDensity_iff_of_finite_symmDiff`
  is the case of a finite symmetric difference.
* `TauCeti.hasDirichletDensity_higherDegreePrimes`: the primes of residue degree greater than one
  have Dirichlet density zero, and
  `TauCeti.hasDirichletDensity_inter_compl_higherDegreePrimes_iff` lets a density be computed on
  the primes of residue degree one alone.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

namespace NumberField.Set

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField symmDiff Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- **A bounded partial sum gives density zero.** If `P_S(s) ≤ C` for all `s` close enough to `1`
from the right, then `S` has Dirichlet density zero, because the all-prime denominator tends to
infinity. -/
theorem hasDirichletDensity_zero_of_eventually_le {C : ℝ}
    (h : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s ≤ C) : S.HasDirichletDensity 0 := by
  have hP := tendsto_primeIdealZetaSum_univ_atTop (K := K)
  refine hasDirichletDensity_iff.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds ((tendsto_const_nhds (x := C)).div_atTop hP) ?_ ?_
  · filter_upwards with s
    exact div_nonneg (S.primeIdealZetaSum_nonneg s) (Set.univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [h, hP.eventually_gt_atTop 0] with s hs hpos
    exact div_le_div_of_nonneg_right hs hpos.le

/-- **A convergent reciprocal-norm series gives density zero.** If `∑_{𝔭 ∈ S} N(𝔭)⁻¹` converges,
then `S` has Dirichlet density zero: for `s ≥ 1` every term `N(𝔭) ^ (-s)` is at most `N(𝔭)⁻¹`,
so the partial sums stay bounded as `s → 1⁺`. -/
theorem hasDirichletDensity_zero_of_summable
    (h : Summable fun 𝔭 : S ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-1 : ℝ)) :
    S.HasDirichletDensity 0 := by
  refine hasDirichletDensity_zero_of_eventually_le (C := S.primeIdealZetaSum 1) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hle : ∀ 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) ≤
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-1 : ℝ) := fun 𝔭 ↦
    Real.rpow_le_rpow_of_exponent_le (one_le_absNorm_real_of_nonZeroDivisors
      ⟨𝔭.1.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.1.ne_bot⟩) (by linarith)
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  exact (h.of_nonneg_of_le (fun _ ↦ by positivity) hle).tsum_le_tsum hle h

/-- **Finite sets of primes have Dirichlet density zero.** -/
theorem hasDirichletDensity_of_finite (hS : S.Finite) : S.HasDirichletDensity 0 := by
  refine hasDirichletDensity_zero_of_eventually_le (C := S.ncard) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact primeIdealZetaSum_le_card_of_finite hS (by linarith)

/-- **Sets of nonzero density are infinite.** A set of primes with a nonzero Dirichlet density
is infinite, because a finite set of primes has Dirichlet density zero. -/
theorem HasDirichletDensity.infinite (hS : S.HasDirichletDensity δ) (hδ : δ ≠ 0) : S.Infinite :=
  fun hfin ↦ hδ (hS.unique (hasDirichletDensity_of_finite hfin))

/-- **Subsets of sets of density zero have density zero.** -/
theorem HasDirichletDensity.zero_of_subset (hT : T.HasDirichletDensity 0) (hST : S ⊆ T) :
    S.HasDirichletDensity 0 :=
  hasDirichletDensity_of_subset_of_subset (Set.empty_subset S) hST hasDirichletDensity_empty hT

/-- **Sets of density zero are negligible.** If `T` has Dirichlet density `δ` and the symmetric
difference `S ∆ T` has Dirichlet density zero, then `S` has Dirichlet density `δ`. -/
theorem HasDirichletDensity.of_symmDiff (hT : T.HasDirichletDensity δ)
    (h : (S ∆ T).HasDirichletDensity 0) : S.HasDirichletDensity δ := by
  have hT' := hasDirichletDensity_iff.1 hT
  have h' := hasDirichletDensity_iff.1 h
  have hlo : Tendsto (fun s ↦ (T.primeIdealZetaSum s - (S ∆ T).primeIdealZetaSum s) /
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 δ) := by
    simpa only [sub_div, sub_zero] using hT'.sub h'
  have hhi : Tendsto (fun s ↦ (T.primeIdealZetaSum s + (S ∆ T).primeIdealZetaSum s) /
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 δ) := by
    simpa only [add_div, add_zero] using hT'.add h'
  refine hasDirichletDensity_iff.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    -- `P_T ≤ P_S + P_{S ∆ T}`, since `T ∆ S = S ∆ T`.
    have := primeIdealZetaSum_le_add_symmDiff (S := T) (T := S)
      (summable_absNorm_rpow_subtype_of_one_lt S hs)
      (summable_absNorm_rpow_subtype_of_one_lt _ hs)
    rw [symmDiff_comm] at this
    exact div_le_div_of_nonneg_right (by linarith) (Set.univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_le_add_symmDiff
      (summable_absNorm_rpow_subtype_of_one_lt T hs)
      (summable_absNorm_rpow_subtype_of_one_lt _ hs)) (Set.univ.primeIdealZetaSum_nonneg s)

/-- Two sets of primes whose symmetric difference has Dirichlet density zero have the same
Dirichlet densities. -/
theorem hasDirichletDensity_iff_of_symmDiff (h : (S ∆ T).HasDirichletDensity 0) :
    S.HasDirichletDensity δ ↔ T.HasDirichletDensity δ :=
  ⟨fun hS ↦ hS.of_symmDiff (symmDiff_comm S T ▸ h), fun hT ↦ hT.of_symmDiff h⟩

/-- Two sets of primes whose symmetric difference has Dirichlet density zero have the same value
of `NumberField.Set.dirichletDensity`, including when neither has a Dirichlet density. -/
theorem dirichletDensity_eq_of_symmDiff (h : (S ∆ T).HasDirichletDensity 0) :
    S.dirichletDensity = T.dirichletDensity := by
  by_cases hT : ∃ δ, T.HasDirichletDensity δ
  · obtain ⟨δ, hT⟩ := hT
    rw [((hasDirichletDensity_iff_of_symmDiff h).2 hT).dirichletDensity_eq, hT.dirichletDensity_eq]
  · rw [not_exists] at hT
    rw [dirichletDensity_eq_zero_of_not_hasDirichletDensity hT,
      dirichletDensity_eq_zero_of_not_hasDirichletDensity
        fun δ hS ↦ hT δ ((hasDirichletDensity_iff_of_symmDiff h).1 hS)]

/-- **Finite changes do not affect Dirichlet density.** If `T` has Dirichlet density `δ` and `S`
differs from `T` in finitely many primes, then `S` has Dirichlet density `δ`. -/
theorem HasDirichletDensity.of_finite_symmDiff (hT : T.HasDirichletDensity δ)
    (hST : (S ∆ T).Finite) : S.HasDirichletDensity δ :=
  hT.of_symmDiff (hasDirichletDensity_of_finite hST)

/-- Two sets of primes differing in finitely many primes have the same Dirichlet densities. -/
theorem hasDirichletDensity_iff_of_finite_symmDiff (hST : (S ∆ T).Finite) :
    S.HasDirichletDensity δ ↔ T.HasDirichletDensity δ :=
  hasDirichletDensity_iff_of_symmDiff (hasDirichletDensity_of_finite hST)

end NumberField.Set

open IsDedekindDomain NumberField NumberField.Set

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The primes of residue degree greater than one have Dirichlet density zero**, because their
reciprocal-norm series converges. -/
theorem hasDirichletDensity_higherDegreePrimes : (higherDegreePrimes K).HasDirichletDensity 0 :=
  hasDirichletDensity_zero_of_summable (summable_absNorm_rpow_higherDegreePrimes (by norm_num))

/-- **The primes of residue degree one have Dirichlet density one.** -/
theorem hasDirichletDensity_compl_higherDegreePrimes :
    (higherDegreePrimes K)ᶜ.HasDirichletDensity 1 := by
  simpa using hasDirichletDensity_higherDegreePrimes.compl

/-- **Dirichlet density only sees primes of residue degree one.** A set `S` of primes has
Dirichlet density `δ` if and only if its primes of residue degree one do. -/
theorem hasDirichletDensity_inter_compl_higherDegreePrimes_iff
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    (S ∩ (higherDegreePrimes K)ᶜ).HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  refine hasDirichletDensity_iff_of_symmDiff <|
    hasDirichletDensity_higherDegreePrimes.zero_of_subset fun 𝔭 h𝔭 ↦ ?_
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_compl_iff] at h𝔭
  tauto

end TauCeti
