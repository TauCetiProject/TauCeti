/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Basic
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing
public import TauCeti.RingTheory.WittVector.Cyclotomic.Level

import TauCeti.RingTheory.WittVector.Regular.Basic

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

At finite level `r` (over any `p`-adically complete ring `A` with `ker θ = (ξ)` and `A`-regular
`p`), an element `a ∈ W(A♭)` is divisible by `ξ_r` if and only if `θ(φʲ(a)) = 0` for all `j < r`.
Intersecting over `r ≥ 1` for a rank `≤ 1` valuation ring `V` with `(p : V) ≠ 0` therefore
characterizes `(μ)` directly as the ideal of elements killed by `θ ∘ φʲ` for every `j ≥ 0`
(`TauCeti.WittVector.mem_span_cyclotomicMu_iff`).

## Main results

* `TauCeti.WittVector.fontaineTheta_iterate_frobeniusEquiv_cyclotomicXiLevel_eq_zero`,
  `TauCeti.WittVector.cyclotomicXiLevel_dvd_iff_forall_fontaineTheta_iterate_eq_zero`: finite-level
  divisibility by `ξ_r` via vanishing of `θ ∘ φʲ` for `j < r`.
* `TauCeti.WittVector.iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub`: for a `p`-adically
  complete ring of integers `V` of a rank `≤ 1` valuation and `ε ≠ 1` in `V♭`,
  `⋂_{r ≥ 1} ((ξ_r).coeff 0) = (ε - 1)`.
* `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu`:
  `⋂_{r ≥ 1} (ξ_r) = (μ)` in `W(V♭)`.
* `TauCeti.WittVector.span_cyclotomicMu_eq_of_span_cyclotomicXi_eq`,
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_geom_sum_eq_zero`,
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_isPrimitiveRoot`,
  `TauCeti.WittVector.associated_cyclotomicMu_of_isPrimitiveRoot`: independence of `(μ)` from `ε`.
* `TauCeti.WittVector.cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero`,
  `TauCeti.WittVector.mem_span_cyclotomicMu_iff`,
  `TauCeti.WittVector.mem_span_frobeniusEquiv_symm_cyclotomicMu_iff`, and
  `WittVector.frobeniusEquiv_symm_cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_succ_eq_zero`:
  characterization of `(μ)` and `(φ⁻¹(μ))` in `W(V♭)` via `θ ∘ φʲ`.
* `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu_integer`,
  `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu_powerBoundedSubring`,
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring`: specializations
  to `𝒪[C]` and `C°`.

## Provenance

The divisibility criterion
`TauCeti.WittVector.cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero` follows
`New.Period.mu_dvd_of_theta_frobEnd` in `src/Lib/PadicHodge/PeriodRings/Ainf.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where it is proved
for `C = ℂ_p`; here it is derived for arbitrary rank `≤ 1` valuation rings from
`iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu` and finite-level divisibility.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.23 and §4.
-/

public section

open Ideal _root_.WittVector
open scoped nonZeroDivisors

namespace TauCeti.WittVector

section FiniteLevel

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (span {(p : A)}) A]

/-- If Fontaine's map kills `ξ`, then it kills `φʲ(ξ_r)` for every `j < r`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_cyclotomicXiLevel_eq_zero {ε : PreTilt A p}
    (hξ : fontaineTheta A p (cyclotomicXi p ε) = 0) {j r : ℕ} (hj : j < r) :
    fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) (cyclotomicXiLevel p ε r)) = 0 := by
  obtain ⟨c, hc⟩ := cyclotomicXi_dvd_iterate_frobeniusEquiv_cyclotomicXiLevel p ε hj
  rw [hc, map_mul, hξ, zero_mul]

/-- **Finite-level kernel divisibility.** If `ker θ = (ξ)` and `p` is `A`-regular, then `ξ_r`
divides `a` in `W(A♭)` if and only if `θ(φʲ(a)) = 0` for every `j < r`. -/
theorem cyclotomicXiLevel_dvd_iff_forall_fontaineTheta_iterate_eq_zero {ε : PreTilt A p}
    (hker : RingHom.ker (fontaineTheta A p) = span {cyclotomicXi p ε})
    (hp_reg : IsSMulRegular A (p : A)) {r : ℕ} {a : _root_.WittVector p (PreTilt A p)} :
    cyclotomicXiLevel p ε r ∣ a ↔
      ∀ j < r, fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) a) = 0 := by
  have hξ : fontaineTheta A p (cyclotomicXi p ε) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact mem_span_singleton_self _
  refine ⟨fun ⟨b, hb⟩ j hj ↦ ?_, fun ha ↦ ?_⟩
  · rw [hb, iterate_map_mul, map_mul,
      fontaineTheta_iterate_frobeniusEquiv_cyclotomicXiLevel_eq_zero hξ hj, zero_mul]
  · have hε : ε.untilt = 1 := by
      rw [fontaineTheta_cyclotomicXi] at hξ
      exact PreTilt.untilt_eq_one_of_geom_sum_eq_zero hξ
    induction r generalizing a with
    | zero => simp only [cyclotomicXiLevel_zero, one_dvd]
    | succ r ih =>
      obtain ⟨b, rfl⟩ : cyclotomicXi p ε ∣ a := by
        rw [← mem_span_singleton, ← hker]
        simpa only [RingHom.mem_ker, Function.iterate_zero_apply] using ha 0 (Nat.zero_lt_succ r)
      have hb : ∀ j < r,
          fontaineTheta A p
            (((frobeniusEquiv p (PreTilt A p))^[j]) (frobeniusEquiv p _ b)) = 0 := by
        intro j hj
        have h := ha (j + 1) (Nat.succ_lt_succ hj)
        rw [iterate_map_mul, map_mul,
          fontaineTheta_iterate_frobeniusEquiv_succ_cyclotomicXi hε] at h
        rw [← Function.iterate_succ_apply]
        refine hp_reg ?_
        simpa only [smul_eq_mul, mul_zero] using h
      obtain ⟨c, hc⟩ := ih hb
      have hbdvd : (frobeniusEquiv p (PreTilt A p)).symm (cyclotomicXiLevel p ε r) ∣ b := by
        refine ⟨(frobeniusEquiv p (PreTilt A p)).symm c, ?_⟩
        simpa only [map_mul, RingEquiv.symm_apply_apply] using
          congrArg (frobeniusEquiv p (PreTilt A p)).symm hc
      rw [cyclotomicXiLevel_succ']
      exact mul_dvd_mul_left _ hbdvd

end FiniteLevel

section RankLeOne

variable {p : ℕ} [hp : Fact p.Prime] {K Γ₀ : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} [Valuation.RankLeOne v]
  {V : Type*} [CommRing V] [Algebra V K] (hv : v.Integers V) [Fact ¬IsUnit (p : V)]
include hv

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
    PreTilt.norm_untilt_le_div_of_mul_eq hv hnormw hmul
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

/-- **Divisibility by `μ`.** Over a `p`-adically complete ring of integers `V` of a rank `≤ 1`
valuation with `(p : V) ≠ 0`, if `ker θ = (ξ)` and `θ(φʲ(a)) = 0` for every `j ≥ 0`, then `μ`
divides `a`. -/
theorem cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero
    [IsAdicComplete (span {(p : V)}) V] {ε : PreTilt V p}
    (hker : RingHom.ker (fontaineTheta V p) = span {cyclotomicXi p ε})
    (hp0 : (p : V) ≠ 0) {a : _root_.WittVector p (PreTilt V p)}
    (ha : ∀ j, fontaineTheta V p (((frobeniusEquiv p (PreTilt V p))^[j]) a) = 0) :
    cyclotomicMu p ε ∣ a := by
  let : IsDomain V := Function.Injective.isDomain (algebraMap V K) hv.hom_inj
  have hp_reg : IsSMulRegular V (p : V) := fun x y h ↦
    mul_left_cancel₀ hp0 (by simpa only [smul_eq_mul] using h)
  have hmem : a ∈ ⨅ (r : ℕ) (_ : 1 ≤ r), span {cyclotomicXiLevel p ε r} :=
    mem_iInf.mpr fun r ↦ mem_iInf.mpr fun _ ↦ mem_span_singleton.mpr
      ((cyclotomicXiLevel_dvd_iff_forall_fontaineTheta_iterate_eq_zero hker hp_reg).mpr
        fun j _ ↦ ha j)
  rw [iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu hv ε, mem_span_singleton] at hmem
  exact hmem

/-- An element of `W(V♭)` lies in `(μ)` exactly when it is killed by `θ ∘ φʲ` for every `j ≥ 0`,
whenever `ker θ = (ξ)` and `(p : V) ≠ 0`. -/
theorem mem_span_cyclotomicMu_iff [IsAdicComplete (span {(p : V)}) V] {ε : PreTilt V p}
    (hker : RingHom.ker (fontaineTheta V p) = span {cyclotomicXi p ε})
    (hp0 : (p : V) ≠ 0) {a : _root_.WittVector p (PreTilt V p)} :
    a ∈ span {cyclotomicMu p ε} ↔
      ∀ j, fontaineTheta V p (((frobeniusEquiv p (PreTilt V p))^[j]) a) = 0 := by
  have hε : ε.untilt = 1 := by
    have hξ : fontaineTheta V p (cyclotomicXi p ε) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact mem_span_singleton_self _
    rw [fontaineTheta_cyclotomicXi] at hξ
    exact PreTilt.untilt_eq_one_of_geom_sum_eq_zero hξ
  refine ⟨fun h j ↦ ?_, fun h ↦ mem_span_singleton.mpr
    (cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_eq_zero hv hker hp0 h)⟩
  obtain ⟨b, rfl⟩ := mem_span_singleton.mp h
  rw [iterate_map_mul, map_mul, fontaineTheta_iterate_frobeniusEquiv_cyclotomicMu_eq_zero hε,
    zero_mul]

/-- An element of `W(V♭)` lies in `(φ⁻¹(μ))` exactly when it is killed by `θ ∘ φʲ` for every
`j ≥ 1`, whenever `ker θ = (ξ)` and `(p : V) ≠ 0`. -/
theorem mem_span_frobeniusEquiv_symm_cyclotomicMu_iff [IsAdicComplete (span {(p : V)}) V]
    {ε : PreTilt V p} (hker : RingHom.ker (fontaineTheta V p) = span {cyclotomicXi p ε})
    (hp0 : (p : V) ≠ 0) {a : _root_.WittVector p (PreTilt V p)} :
    a ∈ span {(frobeniusEquiv p (PreTilt V p)).symm (cyclotomicMu p ε)} ↔
      ∀ j, fontaineTheta V p (((frobeniusEquiv p (PreTilt V p))^[j + 1]) a) = 0 := by
  rw [mem_span_singleton, ← map_dvd_iff (frobeniusEquiv p (PreTilt V p)),
    RingEquiv.apply_symm_apply, ← mem_span_singleton, mem_span_cyclotomicMu_iff hv hker hp0]
  simp only [Function.iterate_succ_apply]

/-- **Divisibility by `φ⁻¹(μ)`.** Over a `p`-adically complete ring of integers `V` of a rank `≤ 1`
valuation with `(p : V) ≠ 0`, if `ker θ = (ξ)` and `θ(φʲ(a)) = 0` for every `j ≥ 1`, then
`φ⁻¹(μ)` divides `a`. -/
theorem frobeniusEquiv_symm_cyclotomicMu_dvd_of_forall_fontaineTheta_iterate_succ_eq_zero
    [IsAdicComplete (span {(p : V)}) V] {ε : PreTilt V p}
    (hker : RingHom.ker (fontaineTheta V p) = span {cyclotomicXi p ε})
    (hp0 : (p : V) ≠ 0) {a : _root_.WittVector p (PreTilt V p)}
    (ha : ∀ j, fontaineTheta V p (((frobeniusEquiv p (PreTilt V p))^[j + 1]) a) = 0) :
    (frobeniusEquiv p (PreTilt V p)).symm (cyclotomicMu p ε) ∣ a :=
  mem_span_singleton.mp ((mem_span_frobeniusEquiv_symm_cyclotomicMu_iff hv hker hp0).mpr ha)

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

/-- **Independence of `(μ)` on `C°` for a perfectoid ultrametric field `C`:** for any two
compatible systems `ε, ε' ∈ (C°)♭` whose `p`-th roots `ζ = (ε ^ (1 / p))♯` and
`ζ' = (ε' ^ (1 / p))♯` are primitive `p`-th roots of unity,
`(cyclotomicMu p ε) = (cyclotomicMu p ε')` in `A_inf(C°) = W((C°)♭)`. -/
theorem span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring {C : Type*}
    [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [TauCeti.Perfectoid.IsPerfectoidTateRing p C]
    [Fact ¬IsUnit (p : powerBoundedSubring C)] {ε ε' : PreTilt (powerBoundedSubring C) p}
    (hζ : IsPrimitiveRoot
      (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε).untilt) p)
    (hζ' : IsPrimitiveRoot
      (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε').untilt) p) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} :=
  span_cyclotomicMu_eq_of_isPrimitiveRoot integers_powerBoundedSubring hζ hζ'

end NormedField

end TauCeti.WittVector
