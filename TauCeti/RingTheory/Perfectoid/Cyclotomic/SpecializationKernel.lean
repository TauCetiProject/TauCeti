/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Basic
public import TauCeti.RingTheory.Perfectoid.IsAlgClosed
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing

import TauCeti.RingTheory.Huber.ValuedField
import TauCeti.RingTheory.WittVector.Complete
import TauCeti.RingTheory.WittVector.Cyclotomic.Regular

/-!
# The infinite Witt specialization kernel

Let `V` be a `p`-adically complete ring of integers for a valuation of rank at most one (for
instance `𝒪[C]` or `C°` for a complete algebraically closed extension `C` of `ℚ_p`), with tilt
`V♭ = PreTilt V p` and `A_inf(V) = W(V♭)`.

For any `ε ∈ V♭`, the countable intersection of principal ideals `(ξ_r)`, `r ≥ 1`, equals `(μ)`:

  `⋂_{r ≥ 1} (ξ_r) = (μ)`.

For `ε = 1` this reduces to `⋂_{r ≥ 1} (p ^ r) = ⊥`; for `ε ≠ 1` the Archimedean property of the
rank-≤1 valuation forces `⋂_{r ≥ 1} ((ξ_r).coeff 0) = (ε - 1)` in `V♭`, which lifts to `W(V♭)` via
`WittVector.iInf_span_eq_span_of_coeff_zero`. Consequently, if `span {ξ(ε)} = span {ξ(ε')}` (in
particular when `V` is integral perfectoid and `(ε ^ (1 / p))♯`, `(ε' ^ (1 / p))♯` are primitive
`p`-th roots of unity or satisfy the `p`-cyclotomic equation), then `span {μ(ε)} = span {μ(ε')}` in
`W(V♭)`.

When `V = 𝒪[C]` for a complete perfectoid nonarchimedean field `C`, `(μ)` is also characterized
directly as the ideal of elements killed by `θ ∘ φʲ` for every `j ≥ 0`
(`TauCeti.WittVector.mem_span_cyclotomicMu_iff`).

## Main results

* `TauCeti.WittVector.iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub`: for a `p`-adically
  complete ring of integers `V` of a rank `≤ 1` valuation and `ε ≠ 1` in `V♭`,
  `⋂_{r ≥ 1} ((ξ_r).coeff 0) = (ε - 1)`.
* `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu`:
  `⋂_{r ≥ 1} (ξ_r) = (μ)` in `W(V♭)`.
* `TauCeti.WittVector.span_cyclotomicMu_eq_of_span_cyclotomicXi_eq`,
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_geom_sum_eq_zero`,
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_isPrimitiveRoot`,
  `TauCeti.WittVector.associated_cyclotomicMu_of_isPrimitiveRoot`: independence of `(μ)` from `ε`.
* `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu_integer`,
  `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu_powerBoundedSubring`,
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring`: specializations
  to `𝒪[C]` and `C°`.
* `TauCeti.WittVector.cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero`,
  `TauCeti.WittVector.mem_span_cyclotomicMu_iff`, and
  `TauCeti.WittVector.mem_span_frobeniusEquiv_symm_cyclotomicMu_iff`:
  characterization of `(μ)` and `(φ⁻¹(μ))` in `W(𝒪[C]♭)` via `θ ∘ φʲ`.

## Provenance

The divisibility criterion
`TauCeti.WittVector.cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero`
and the coordinate argument behind it are adapted from `New.Period.mu_dvd_of_theta_frobEnd` and
`pow_pow_dvd_constantCoeff_mu_of_eq_mul` in `src/Lib/PadicHodge/PeriodRings/Ainf.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where they are
proved for `C = ℂ_p` with a fixed compatible system of roots of unity.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.23 and §4.
-/

public section

open Ideal _root_.WittVector
open scoped nonZeroDivisors

namespace TauCeti.WittVector

section RankLeOne

variable {p : ℕ} [hp : Fact p.Prime] {K Γ₀ : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} [Valuation.RankLeOne v]
  {V : Type*} [CommRing V] [Algebra V K] (hv : v.Integers V) [Fact ¬IsUnit (p : V)]
include hv

private theorem norm_untilt_le_div_of_mul_eq [IsAdicComplete (span {(p : V)}) V]
    {w d c z : PreTilt V p} (hnormw : 0 < v.norm (algebraMap V K w.untilt))
    (hmul : w * d = c * z) :
    v.norm (algebraMap V K d.untilt) ≤
      v.norm (algebraMap V K z.untilt) / v.norm (algebraMap V K w.untilt) := by
  rw [le_div_iff₀ hnormw, mul_comm]
  have hmul' :
      v.norm (algebraMap V K w.untilt) * v.norm (algebraMap V K d.untilt) =
        v.norm (algebraMap V K c.untilt) * v.norm (algebraMap V K z.untilt) := by
    simp only [Valuation.norm_def, ← NNReal.coe_mul, ← map_mul, ← map_mul PreTilt.untilt, hmul]
  rw [hmul']
  have hc1 : v.norm (algebraMap V K c.untilt) ≤ 1 := by
    have h1 : v.restrict (algebraMap V K c.untilt) ≤ 1 :=
      v.restrict_le_one_iff.mpr (hv.map_le_one _)
    simpa [Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe] using
      (Valuation.RankLeOne.strictMono' (v := v)).le_iff_le.mpr h1
  exact mul_le_of_le_one_left (v.norm_nonneg _) hc1

/-- For a `p`-adically complete ring of integers `V` of a rank `≤ 1` valuation and `ε ≠ 1` in
`V♭`, the countable intersection `⋂_{r ≥ 1} ((ξ_r).coeff 0)` equals `(ε - 1)` in `V♭`. -/
theorem iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub
    [IsAdicComplete (span {(p : V)}) V] {ε : PreTilt V p} (hε : ε ≠ 1) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {(cyclotomicXiLevel p ε r).coeff 0}) = span {ε - 1} := by
  let : IsDomain V := Function.Injective.isDomain (algebraMap V K) hv.hom_inj
  have := hv.isIntegrallyClosed
  refine le_antisymm ?_ (le_iInf fun r ↦ le_iInf fun _ ↦ span_singleton_le_span_singleton.mpr
    ⟨_, (cyclotomicXiLevel_coeff_zero_mul p ε r).symm⟩)
  intro w hw
  rw [mem_span_singleton, ← PreTilt.untilt_dvd_untilt_iff, hv.dvd_iff_le,
    ← v.restrict_le_iff, ← (Valuation.RankLeOne.strictMono' (v := v)).le_iff_le]
  by_contra! hlt
  have hlt' : v.norm (algebraMap V K (ε - 1).untilt) < v.norm (algebraMap V K w.untilt) := by
    simpa only [Valuation.norm_def, NNReal.coe_lt_coe] using hlt
  have hz₀ : (ε - 1).untilt ≠ 0 := PreTilt.untilt_ne_zero_iff.mpr (sub_ne_zero.mpr hε)
  have hnorm0 : 0 < v.norm (algebraMap V K (ε - 1).untilt) :=
    v.norm_pos_iff_valuation_pos.mpr (hv.valuation_pos_iff_ne_zero.mpr hz₀)
  have hnormw : 0 < v.norm (algebraMap V K w.untilt) := hnorm0.trans hlt'
  set q : ℝ := v.norm (algebraMap V K (ε - 1).untilt) / v.norm (algebraMap V K w.untilt)
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hnorm0 ((div_lt_one hnormw).mpr hlt')
  obtain ⟨c, hc⟩ := mem_span_singleton.mp
    ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hw (r + 1)) (Nat.le_add_left 1 r))
  set d : PreTilt V p := ((_root_.frobeniusEquiv (PreTilt V p) p).symm^[r + 1]) ε - 1
  have hmul : w * d = c * (ε - 1) := by
    have hlevel := cyclotomicXiLevel_coeff_zero_mul p ε (r + 1)
    linear_combination d * hc + c * hlevel
  have hdnorm : v.norm (algebraMap V K d.untilt) ≤ q :=
    norm_untilt_le_div_of_mul_eq hv hnormw hmul
  have hpow : v.norm (algebraMap V K (ε - 1).untilt) =
      v.norm (algebraMap V K d.untilt) ^ p ^ (r + 1) := by
    have hd : d ^ p ^ (r + 1) = ε - 1 := by
      simpa [d, iterate_map_sub, iterate_map_one] using
        iterate_frobeniusEquiv_symm_pow_p_pow (PreTilt V p) p (ε - 1) (r + 1)
    rw [← hd]
    simp only [Valuation.norm_def, map_pow, NNReal.coe_pow]
  have hle : v.norm (algebraMap V K (ε - 1).untilt) ≤ q ^ r := by
    rw [hpow]
    calc v.norm (algebraMap V K d.untilt) ^ p ^ (r + 1)
        ≤ q ^ p ^ (r + 1) := pow_le_pow_left₀ (v.norm_nonneg _) hdnorm _
      _ ≤ q ^ r := pow_le_pow_of_le_one (div_nonneg hnorm0.le hnormw.le)
          ((div_lt_one hnormw).mpr hlt').le
          (le_trans (Nat.le_succ r) (Nat.lt_pow_self hp.out.one_lt).le)
  exact hr.not_ge hle

/-- **Infinite Witt kernel intersection** (Bhatt–Morrow–Scholze, Lemma 3.23). For a `p`-adically
complete ring of integers `V` of a rank `≤ 1` valuation (such as `𝒪[C]` or `C°`) and any
`ε : V♭`, `⋂_{r ≥ 1} (ξ_r) = (μ)` in `W(V♭)`. -/
theorem iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu
    [IsAdicComplete (span {(p : V)}) V] (ε : PreTilt V p) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {cyclotomicXiLevel p ε r}) = span {cyclotomicMu p ε} := by
  let : IsDomain V := Function.Injective.isDomain (algebraMap V K) hv.hom_inj
  rcases eq_or_ne ε 1 with rfl | hε
  · simpa [Ideal.span_singleton_zero] using
      iInf_span_natCast_pow_eq_bot (p := p) (R := PreTilt V p)
  · rw [iInf_subtype']
    refine iInf_span_eq_span_of_coeff_zero (ι := {r : ℕ // 1 ≤ r})
      (fun r ↦ mem_span_singleton.mpr (cyclotomicXiLevel_dvd_cyclotomicMu p ε r.val))
      (fun r ↦ cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p
        (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hε)) r.val) ?_
    simpa only [iInf_subtype', cyclotomicMu_coeff_zero] using
      iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub hv hε

/-- **Independence of `(μ)` from `(ξ)`.** Over a `p`-adically complete ring of integers `V` of a
rank `≤ 1` valuation, if `cyclotomicXi p ε` and `cyclotomicXi p ε'` generate the same ideal of
`W(V♭)`, then `cyclotomicMu p ε` and `cyclotomicMu p ε'` generate the same ideal of `W(V♭)`. -/
theorem span_cyclotomicMu_eq_of_span_cyclotomicXi_eq
    [IsAdicComplete (span {(p : V)}) V] {ε ε' : PreTilt V p}
    (h : span {cyclotomicXi p ε} = span {cyclotomicXi p ε'}) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} := by
  rw [← iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu hv ε,
    ← iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu hv ε']
  refine iInf_congr fun r ↦ iInf_congr fun _ ↦ ?_
  exact span_cyclotomicXiLevel_eq_of_span_cyclotomicXi_eq p h r

/-- **Independence of `(μ)` for integral perfectoid valuation rings.** If `V` is integral
perfectoid and a rank `≤ 1` ring of integers, and both `ζ = (ε ^ (1 / p))♯` and
`ζ' = (ε' ^ (1 / p))♯` satisfy `∑_{j < p} ζ ^ j = 0`, then
`(cyclotomicMu p ε) = (cyclotomicMu p ε')` in `W(V♭)`. -/
theorem span_cyclotomicMu_eq_of_geom_sum_eq_zero [TauCeti.Perfectoid.IsIntegralPerfectoid p V]
    {ε ε' : PreTilt V p}
    (hε : ∑ j ∈ Finset.range p, ((_root_.frobeniusEquiv (PreTilt V p) p).symm ε).untilt ^ j = 0)
    (hε' : ∑ j ∈ Finset.range p,
      ((_root_.frobeniusEquiv (PreTilt V p) p).symm ε').untilt ^ j = 0) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} := by
  have hker :=
    (TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_iff_isDistinguished
      (cyclotomicXi_mem_ker_fontaineTheta hε)).mpr
        (isDistinguished_cyclotomicXi_of_untilt_eq_one
          (PreTilt.untilt_eq_one_of_geom_sum_eq_zero hε))
  have hker' :=
    (TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_iff_isDistinguished
      (cyclotomicXi_mem_ker_fontaineTheta hε')).mpr
        (isDistinguished_cyclotomicXi_of_untilt_eq_one
          (PreTilt.untilt_eq_one_of_geom_sum_eq_zero hε'))
  exact span_cyclotomicMu_eq_of_span_cyclotomicXi_eq hv (hker.symm.trans hker')

/-- **Independence of `(μ)` for rank `≤ 1` integral perfectoid valuation rings.** If `V` is
integral perfectoid and a rank `≤ 1` ring of integers, and both `(ε ^ (1 / p))♯` and
`(ε' ^ (1 / p))♯` are primitive `p`-th roots of unity, then `(μ(ε)) = (μ(ε'))` in `W(V♭)`. -/
theorem span_cyclotomicMu_eq_of_isPrimitiveRoot [TauCeti.Perfectoid.IsIntegralPerfectoid p V]
    {ε ε' : PreTilt V p}
    (hζ : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε).untilt) p)
    (hζ' : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε').untilt) p) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} := by
  let : IsDomain V := Function.Injective.isDomain (algebraMap V K) hv.hom_inj
  exact span_cyclotomicMu_eq_of_geom_sum_eq_zero hv
    (hζ.geom_sum_eq_zero hp.out.one_lt) (hζ'.geom_sum_eq_zero hp.out.one_lt)

/-- Any two admissible choices of `ε` for a rank `≤ 1` integral perfectoid valuation ring give
associated elements `μ`. -/
theorem associated_cyclotomicMu_of_isPrimitiveRoot [TauCeti.Perfectoid.IsIntegralPerfectoid p V]
    {ε ε' : PreTilt V p}
    (hζ : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε).untilt) p)
    (hζ' : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε').untilt) p) :
    Associated (cyclotomicMu p ε) (cyclotomicMu p ε') := by
  let : IsDomain V := Function.Injective.isDomain (algebraMap V K) hv.hom_inj
  exact Ideal.span_singleton_eq_span_singleton.mp
    (span_cyclotomicMu_eq_of_isPrimitiveRoot hv hζ hζ')

end RankLeOne

section NormedField

open TauCeti.Huber
open scoped _root_.NormedField Valued

variable {p : ℕ} [hp : Fact p.Prime] {C : Type*} [NormedField C] [IsUltrametricDist C]

/-- **Infinite Witt kernel intersection on `𝒪[C]`:** `⋂_{r ≥ 1} (ξ_r) = (μ)` in `W(𝒪[C]♭)`. -/
theorem iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu_integer
    [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (span {(p : 𝒪[C])}) 𝒪[C]] (ε : PreTilt 𝒪[C] p) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {cyclotomicXiLevel p ε r}) = span {cyclotomicMu p ε} :=
  iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu
    (Valuation.integer.integers (NormedField.valuation (K := C))) ε

/-- **Infinite Witt kernel intersection on `C°`:** `⋂_{r ≥ 1} (ξ_r) = (μ)` in `W((C°)♭)`. -/
theorem iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu_powerBoundedSubring
    [Fact ¬IsUnit (p : powerBoundedSubring C)]
    [IsAdicComplete (span {(p : powerBoundedSubring C)}) (powerBoundedSubring C)]
    (ε : PreTilt (powerBoundedSubring C) p) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {cyclotomicXiLevel p ε r}) = span {cyclotomicMu p ε} :=
  iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu integers_powerBoundedSubring ε

/-- **Independence of `(μ)` on `C°` for complete algebraically closed `C`:** for any two
compatible systems `ε, ε' ∈ (C°)♭` whose `p`-th roots `ζ = (ε ^ (1 / p))♯` and
`ζ' = (ε' ^ (1 / p))♯` are primitive `p`-th roots of unity,
`(cyclotomicMu p ε) = (cyclotomicMu p ε')` in `A_inf(C°) = W((C°)♭)`. -/
theorem span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring {C : Type*}
    [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [hpnu : Fact ¬IsUnit (p : powerBoundedSubring C)] {ε ε' : PreTilt (powerBoundedSubring C) p}
    (hζ :
      letI : TauCeti.Perfectoid.IsPerfectoidTateRing p C :=
        TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed
          (lt_of_le_of_ne
            (isPowerBounded_iff_norm_le_one.mp
              (mem_powerBoundedSubring.mp (p : powerBoundedSubring C).prop))
            ((powerBoundedSubring.isUnit_iff_norm_eq_one).not.mp hpnu.out))
      IsPrimitiveRoot
        (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε).untilt) p)
    (hζ' :
      letI : TauCeti.Perfectoid.IsPerfectoidTateRing p C :=
        TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed
          (lt_of_le_of_ne
            (isPowerBounded_iff_norm_le_one.mp
              (mem_powerBoundedSubring.mp (p : powerBoundedSubring C).prop))
            ((powerBoundedSubring.isUnit_iff_norm_eq_one).not.mp hpnu.out))
      IsPrimitiveRoot
        (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε').untilt) p) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} := by
  let : TauCeti.Perfectoid.IsPerfectoidTateRing p C :=
    TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed
      (lt_of_le_of_ne
        (isPowerBounded_iff_norm_le_one.mp
          (mem_powerBoundedSubring.mp (p : powerBoundedSubring C).prop))
        ((powerBoundedSubring.isUnit_iff_norm_eq_one).not.mp hpnu.out))
  exact span_cyclotomicMu_eq_of_isPrimitiveRoot integers_powerBoundedSubring hζ hζ'

end NormedField

section PerfectoidField

open TauCeti.Huber TauCeti.Perfectoid
open scoped _root_.NormedField Valued

variable {p : ℕ} [hp : Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsPerfectoidTateRing p C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (span {(p : 𝒪[C])}) (𝒪[C])]

/-- The induction behind `cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero`: if `a` is
killed by every `θ ∘ φʲ` and `μ₀ = a₀ * c`, then `c ^ p ^ n` divides `μ₀` for every `n`. -/
private theorem pow_pow_dvd_coeff_zero_cyclotomicMu (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) (n : ℕ) :
    ∀ (a : _root_.WittVector p (PreTilt 𝒪[C] p)) (c : PreTilt 𝒪[C] p),
      (∀ j, fontaineTheta 𝒪[C] p (((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j]) a) = 0) →
      (cyclotomicMu p ε).coeff 0 = a.coeff 0 * c → c ^ p ^ n ∣ (cyclotomicMu p ε).coeff 0 := by
  -- Writing `a = ξ * b` gives `φ⁻¹(μ)₀ = b₀ * c`, hence `μ₀ = φ(b)₀ * c ^ p` with `φ(b)` again
  -- killed by every `θ ∘ φʲ`.
  have hp0 : (p : 𝒪[C]) ≠ 0 := hε.neZero'.out
  have hker := (isRingOfIntegralElements_integer C).ker_fontaineTheta_eq_span_cyclotomicXi
    (hε.geom_sum_eq_zero hp.out.one_lt)
  induction n with
  | zero =>
    intro a c _ h
    rw [pow_zero, pow_one, h]
    exact dvd_mul_left _ _
  | succ n ih =>
    intro a c ha h
    obtain ⟨b, rfl⟩ : cyclotomicXi p ε ∣ a := by
      rw [← Ideal.mem_span_singleton, ← hker]
      simpa only [RingHom.mem_ker, Function.iterate_zero_apply] using ha 0
    -- `θ(φʲ⁺¹(ξ)) = p ≠ 0`, so `φ(b)` is again killed by every `θ ∘ φʲ`
    have hb (j : ℕ) : fontaineTheta 𝒪[C] p
        (((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j]) (frobeniusEquiv p _ b)) = 0 := by
      have := ha (j + 1)
      rw [iterate_map_mul, map_mul, fontaineTheta_iterate_frobeniusEquiv_succ_cyclotomicXi
        (PreTilt.untilt_eq_one_of_isPrimitiveRoot ε hε)] at this
      rw [← Function.iterate_succ_apply]
      exact (mul_eq_zero.mp this).resolve_left hp0
    have hμ := cyclotomicMu_eq_cyclotomicXi_mul p ε
    -- cancelling `ξ₀` from `μ₀ = ξ₀ * b₀ * c` gives `φ⁻¹(μ)₀ = b₀ * c`
    have h1 : ((frobeniusEquiv p _).symm (cyclotomicMu p ε)).coeff 0 = b.coeff 0 * c := by
      refine mul_left_cancel₀
        (coeff_zero_cyclotomicXi_ne_zero p (PreTilt.ne_one_of_isPrimitiveRoot ε hε)) ?_
      rw [← mul_coeff_zero, ← hμ, h, mul_coeff_zero, mul_assoc]
    have h2 : (cyclotomicMu p ε).coeff 0 = (frobeniusEquiv p _ b).coeff 0 * c ^ p := by
      conv_lhs => rw [← (frobeniusEquiv p _).apply_symm_apply (cyclotomicMu p ε)]
      rw [_root_.WittVector.frobeniusEquiv_apply, coeff_frobenius_charP, h1, coeff_frobenius_charP,
        mul_pow]
    simpa only [← pow_mul, ← pow_succ'] using ih _ (c ^ p) hb h2

/-- **Divisibility by `μ`.** If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity and
`θ(φʲ(a)) = 0` for every `j ≥ 0`, then `μ` divides `a`. -/
theorem cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {a : _root_.WittVector p (PreTilt 𝒪[C] p)}
    (ha : ∀ j, fontaineTheta 𝒪[C] p (((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j]) a) = 0) :
    cyclotomicMu p ε ∣ a := by
  set φ := frobeniusEquiv p (PreTilt 𝒪[C] p)
  let I : Ideal (_root_.WittVector p (PreTilt 𝒪[C] p)) :=
    ⨅ j : ℕ, RingHom.ker ((fontaineTheta 𝒪[C] p).comp ((φ : _ →+* _) ^ j))
  have hmem (x) : x ∈ I ↔ ∀ j, fontaineTheta 𝒪[C] p ((φ^[j]) x) = 0 := by
    simp [I, RingHom.coe_pow]
  have hp0 : (p : 𝒪[C]) ≠ 0 := hε.neZero'.out
  have hI : I = span {cyclotomicMu p ε} := by
    -- `I` contains `μ`, is saturated for `p`, and `μ₀` divides the zeroth coordinates of `I`
    refine eq_span_singleton_of_coeff_zero_dvd (cyclotomicMu p ε)
      ((hmem _).mpr (fontaineTheta_iterate_frobeniusEquiv_cyclotomicMu_eq_zero
        (PreTilt.untilt_eq_one_of_isPrimitiveRoot ε hε))) (fun x hx ↦ (hmem x).mpr fun j ↦ ?_)
      (fun x hx ↦ ?_)
    · have := (hmem _).mp hx j
      rw [iterate_map_mul, Function.iterate_fixed (map_natCast φ p), map_mul,
        map_natCast] at this
      exact (mul_eq_zero.mp this).resolve_left hp0
    · by_contra hndvd
      obtain ⟨c, hc⟩ := (ValuationRing.dvd_total _ _).resolve_left hndvd
      have hcu : ¬IsUnit c := fun hu ↦ hndvd (by rw [hc, hu.mul_right_dvd])
      exact coeff_zero_cyclotomicMu_ne_zero p (PreTilt.ne_one_of_isPrimitiveRoot ε hε)
        (PreTilt.eq_zero_of_forall_pow_dvd c hcu fun n ↦
          (pow_dvd_pow c (Nat.lt_pow_self hp.out.one_lt).le).trans
            (pow_pow_dvd_coeff_zero_cyclotomicMu ε hε n x c ((hmem x).mp hx) hc))
  exact Ideal.mem_span_singleton.mp (hI ▸ (hmem a).mpr ha)

/-- An element of `A_inf` lies in `(μ)` exactly when it is killed by `θ ∘ φʲ` for every `j ≥ 0`.
-/
theorem mem_span_cyclotomicMu_iff (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {a : _root_.WittVector p (PreTilt 𝒪[C] p)} :
    a ∈ span {cyclotomicMu p ε} ↔
      ∀ j, fontaineTheta 𝒪[C] p (((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j]) a) = 0 := by
  refine ⟨fun h j ↦ ?_, fun h ↦
    Ideal.mem_span_singleton.mpr (cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero ε hε h)⟩
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp h
  rw [iterate_map_mul, map_mul,
    fontaineTheta_iterate_frobeniusEquiv_cyclotomicMu_eq_zero
      (PreTilt.untilt_eq_one_of_isPrimitiveRoot ε hε),
    zero_mul]

/-- An element of `A_inf` lies in `(φ⁻¹(μ))` exactly when it is killed by `θ ∘ φʲ` for every
`j ≥ 1`, provided the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity. -/
theorem mem_span_frobeniusEquiv_symm_cyclotomicMu_iff (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {a : _root_.WittVector p (PreTilt 𝒪[C] p)} :
    a ∈ span {(frobeniusEquiv p (PreTilt 𝒪[C] p)).symm (cyclotomicMu p ε)} ↔
      ∀ j, fontaineTheta 𝒪[C] p (((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j + 1]) a) = 0 := by
  rw [Ideal.mem_span_singleton, ← map_dvd_iff (frobeniusEquiv p (PreTilt 𝒪[C] p)),
    RingEquiv.apply_symm_apply, ← Ideal.mem_span_singleton, mem_span_cyclotomicMu_iff ε hε]
  simp only [Function.iterate_succ_apply]

/-- **Divisibility by `φ⁻¹(μ)`.** If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root
of unity and `θ(φʲ(a)) = 0` for every `j ≥ 1`, then `φ⁻¹(μ)` divides `a`. -/
theorem frobeniusEquiv_symm_cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_succ_eq_zero
    (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p)
    {a : _root_.WittVector p (PreTilt 𝒪[C] p)}
    (ha : ∀ j, fontaineTheta 𝒪[C] p (((frobeniusEquiv p (PreTilt 𝒪[C] p))^[j + 1]) a) = 0) :
    (frobeniusEquiv p (PreTilt 𝒪[C] p)).symm (cyclotomicMu p ε) ∣ a :=
  Ideal.mem_span_singleton.mp ((mem_span_frobeniusEquiv_symm_cyclotomicMu_iff ε hε).mpr ha)

end PerfectoidField

end TauCeti.WittVector
