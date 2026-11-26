/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.RingTheory.Perfectoid.Cyclotomic
public import TauCeti.RingTheory.Perfectoid.IsAlgClosed
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing
public import TauCeti.RingTheory.WittVector.Cyclotomic

/-!
# Infinite cyclotomic Witt kernel intersection and regularity in `A_inf`

Let `V` be a `p`-adically complete domain in which `p` is not a unit (for instance `O_C` or `C°`
for a complete algebraically closed extension `C` of `ℚ_p`), with tilt `V♭ = PreTilt V p` and
`A_inf(V) = W(V♭)`.

1. **Regularity of integral periods.** Whenever `ε : V♭` satisfies `ε♯ = 1` and `ε ≠ 1` (in
   particular whenever `ζ = (ε ^ (1 / p))♯` is a primitive `p`-th root of unity), `ε - 1` is a
   nonzerodivisor in the Jacobson radical of `V♭`. Consequently `p`, `μ = [ε] - 1`, `ξ`, `ξ'`,
   `ξ_r`, and `ξ'_r` are all nonzerodivisors in `A_inf(V)`, their quotients are `p`-torsion-free,
   and `[p, x]` and `[x, p]` are regular sequences on `A_inf(V)` for each period element `x`.

2. **Infinite Witt kernel intersection.** When `V` is a ring of integers for a valuation of rank at
   most one (e.g. `𝒪[K]` or `K°` for an ultrametric normed field `K`), the countable intersection of
   principal ideals `(ξ_r)` in `A_inf(V)` is `(μ)`:
   `⨅ (r : ℕ) (_ : 1 ≤ r), Ideal.span {cyclotomicXiLevel p ε r} = Ideal.span {cyclotomicMu p ε}`.
   For `ε = 1` this reduces to `⨅ r ≥ 1, (p ^ r) = ⊥`; for `ε ≠ 1` the Archimedean property in
   `V` forces `⨅ r ≥ 1, ((ξ_r).coeff 0) = (ε - 1)` in `V♭`, which lifts to `W(V♭)` via
   `WittVector.iInf_span_eq_span_of_coeff_zero`.

3. **Independence of `(μ)`.** If `span {cyclotomicXi p ε} = span {cyclotomicXi p ε'}` (for
   instance when `V` is integral perfectoid and `(ε ^ (1 / p))♯`, `(ε' ^ (1 / p))♯` satisfy the
   `p`-cyclotomic equation), then `span {cyclotomicXiLevel p ε r} = span {cyclotomicXiLevel p ε' r}`
   for all `r`, and hence `span {cyclotomicMu p ε} = span {cyclotomicMu p ε'}`.

## Main results

* `TauCeti.WittVector.iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub`: for a `p`-adically
  complete ring of integers `V` of a rank `≤ 1` valuation and `ε ≠ 1` in `V♭`,
  `⋂_{r ≥ 1} ((ξ_r).coeff 0) = (ε - 1)`.
* `TauCeti.WittVector.iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu`:
  `⋂_{r ≥ 1} (ξ_r) = (μ)` in `W(V♭)`.
* `TauCeti.WittVector.span_cyclotomicMu_eq_of_span_cyclotomicXi_eq` and
  `TauCeti.WittVector.span_cyclotomicMu_eq_of_geom_sum_eq_zero`: independence of `(μ)` from `ε`.
* Regularity theorems (`mem_nonZeroDivisors`, `isSMulRegular_quotient_natCast`, `isRegular_pair`)
  for `μ`, `ξ`, `ξ'`, `ξ_r`, `ξ'_r` in `W(V♭)` when `ε.untilt = 1` and `ε ≠ 1` (and from
  `IsPrimitiveRoot`).

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.23 and §4.
-/

public section

open Ideal _root_.WittVector RingTheory.Sequence
open scoped nonZeroDivisors

namespace PreTilt

section JacobsonAndPrimitive

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [CommRing V]
  [Fact ¬IsUnit (p : V)] [IsAdicComplete (span {(p : V)}) V]

/-- If `ε♯ = 1`, then `ε - 1` lies in the Jacobson radical of `V♭`. -/
theorem sub_one_mem_jacobson_of_untilt_eq_one {ε : PreTilt V p} (hε : ε.untilt = 1) :
    ε - 1 ∈ Ring.jacobson (PreTilt V p) := by
  refine RingHom.ker_le_jacobson_of_isLocalHom (PreTilt.coeff 0) ?_
  rw [RingHom.mem_ker, map_sub, map_one, ← PreTilt.mk_untilt_eq_coeff_zero, hε, map_one,
    sub_self]

/-- If `ζ = (ε ^ (1 / p))♯` is a primitive `p`-th root of unity in `V`, then `ε♯ = 1` and
`ε ≠ 1`. -/
theorem untilt_eq_one_and_ne_one_of_isPrimitiveRoot {ε : PreTilt V p}
    (hζ : IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε).untilt) p) :
    ε.untilt = 1 ∧ ε ≠ 1 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · have hpow : (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε) ^ p).untilt =
        (((_root_.frobeniusEquiv (PreTilt V p) p).symm ε).untilt) ^ p := map_pow _ _ _
    rw [frobeniusEquiv_symm_pow_p, hζ.pow_eq_one] at hpow
    exact hpow
  · have h1 : (_root_.frobeniusEquiv (PreTilt V p) p).symm ε = 1 := by simp [h]
    rw [h1, map_one] at hζ
    exact hζ.ne_one hp.out.one_lt rfl

end JacobsonAndPrimitive

end PreTilt

namespace TauCeti.WittVector

section IdealEquality

variable {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

/-- If `cyclotomicXi p ε` and `cyclotomicXi p ε'` generate the same ideal of `W(S)`, then so do
`cyclotomicXiLevel p ε r` and `cyclotomicXiLevel p ε' r` for every `r : ℕ`. -/
theorem span_cyclotomicXiLevel_eq_of_span_cyclotomicXi_eq {ε ε' : S}
    (h : span {cyclotomicXi p ε} = span {cyclotomicXi p ε'}) (r : ℕ) :
    span {cyclotomicXiLevel p ε r} = span {cyclotomicXiLevel p ε' r} := by
  have hdvd (a b : S) (hab : span {cyclotomicXi p a} ≤ span {cyclotomicXi p b}) (j : ℕ) :
      ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p b) ∣
        ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p a) := by
    have h0 : cyclotomicXi p b ∣ cyclotomicXi p a :=
      mem_span_singleton.mp (hab (mem_span_singleton_self _))
    induction j with
    | zero => exact h0
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact map_dvd _ ih
  refine le_antisymm ?_ ?_ <;> rw [span_singleton_le_span_singleton, cyclotomicXiLevel_def,
    cyclotomicXiLevel_def]
  · exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ ↦ hdvd ε ε' h.le j
  · exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ ↦ hdvd ε' ε h.ge j

private theorem iterate_frobeniusEquiv_symm_sub_one_pow (ε : S) (r : ℕ) :
    (((_root_.frobeniusEquiv S p).symm^[r]) ε - 1) ^ p ^ r = ε - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_sub_one_pow, ih]

end IdealEquality

section RankLeOne

variable {p : ℕ} [hp : Fact p.Prime] {K Γ₀ : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} [Valuation.RankLeOne v]
  {V : Type*} [CommRing V] [IsDomain V] [Algebra V K] (hv : v.Integers V)
  [Fact ¬IsUnit (p : V)] [IsAdicComplete (span {(p : V)}) V]
include hv

omit [IsDomain V] in
private theorem norm_untilt_le_div_of_mul_eq {w d c z : PreTilt V p}
    (hnormw : 0 < v.norm (algebraMap V K w.untilt)) (hmul : w * d = c * z) :
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
theorem iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub {ε : PreTilt V p} (hε : ε ≠ 1) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {(cyclotomicXiLevel p ε r).coeff 0}) = span {ε - 1} := by
  have := hv.isIntegrallyClosed
  refine le_antisymm ?_ (le_iInf fun r ↦ le_iInf fun _ ↦ span_singleton_le_span_singleton.mpr
    ⟨_, (cyclotomicXiLevel_coeff_zero_mul p ε r).symm⟩)
  intro w hw
  rw [mem_span_singleton, ← PreTilt.untilt_dvd_untilt_iff, hv.dvd_iff_le,
    ← v.restrict_le_iff, ← (Valuation.RankLeOne.strictMono' (v := v)).le_iff_le]
  by_contra! hlt
  have hlt' : v.norm (algebraMap V K (ε - 1).untilt) < v.norm (algebraMap V K w.untilt) := hlt
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
    rw [← iterate_frobeniusEquiv_symm_sub_one_pow (p := p) ε (r + 1)]
    simp only [Valuation.norm_def, map_pow, NNReal.coe_pow, d]
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
theorem iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu (ε : PreTilt V p) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), span {cyclotomicXiLevel p ε r}) = span {cyclotomicMu p ε} := by
  rcases eq_or_ne ε 1 with rfl | hε
  · simpa [Ideal.span_singleton_zero] using iInf_span_natCast_pow_eq_bot (p := p) (S := PreTilt V p)
  · refine iInf_span_eq_span_of_coeff_zero
      (fun r _ ↦ mem_span_singleton.mpr (cyclotomicXiLevel_dvd_cyclotomicMu p ε r))
      (fun r _ ↦ cyclotomicXiLevel_coeff_zero_mem_nonZeroDivisors p
        (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hε)) r) ?_
    simpa [cyclotomicMu_coeff_zero] using iInf_span_coeff_zero_cyclotomicXiLevel_eq_span_sub hv hε

/-- **Independence of `(μ)` from `(ξ)`.** Over a `p`-adically complete ring of integers `V` of a
rank `≤ 1` valuation, if `cyclotomicXi p ε` and `cyclotomicXi p ε'` generate the same ideal of
`W(V♭)`, then `cyclotomicMu p ε` and `cyclotomicMu p ε'` generate the same ideal of `W(V♭)`. -/
theorem span_cyclotomicMu_eq_of_span_cyclotomicXi_eq {ε ε' : PreTilt V p}
    (h : span {cyclotomicXi p ε} = span {cyclotomicXi p ε'}) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} := by
  rw [← iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu hv ε,
    ← iInf_span_cyclotomicXiLevel_eq_span_cyclotomicMu hv ε']
  refine iInf_congr fun r ↦ iInf_congr fun _ ↦ ?_
  exact span_cyclotomicXiLevel_eq_of_span_cyclotomicXi_eq h r

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

end RankLeOne

section DomainRegularity

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [CommRing V] [IsDomain V]
  [Fact ¬IsUnit (p : V)] [IsAdicComplete (span {(p : V)}) V]

local notation "𝕎♭" => _root_.WittVector p (PreTilt V p)

/-- If `ε : V♭` has `ε ≠ 1`, then `μ = [ε] - 1` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicMu_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) : cyclotomicMu p ε ∈ (𝕎♭)⁰ :=
  cyclotomicMu_mem_nonZeroDivisors p (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXi_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) : cyclotomicXi p ε ∈ (𝕎♭)⁰ :=
  cyclotomicXi_mem_nonZeroDivisors p (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ'` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXiTilde_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) : cyclotomicXiTilde p ε ∈ (𝕎♭)⁰ :=
  cyclotomicXiTilde_mem_nonZeroDivisors p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ_r` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXiLevel_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) : cyclotomicXiLevel p ε r ∈ (𝕎♭)⁰ :=
  cyclotomicXiLevel_mem_nonZeroDivisors p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε ≠ 1`, then `ξ'_r` is a nonzerodivisor in `W(V♭)`. -/
theorem cyclotomicXiTildeLevel_mem_nonZeroDivisors_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) : cyclotomicXiTildeLevel p ε r ∈ (𝕎♭)⁰ :=
  cyclotomicXiTildeLevel_mem_nonZeroDivisors p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (μ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicMu_of_ne_one {ε : PreTilt V p} (hne : ε ≠ 1) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicMu p ε}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicMu p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXi_of_ne_one {ε : PreTilt V p} (hne : ε ≠ 1) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXi p ε}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXi p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ')` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTilde_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXiTilde p ε}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXiTilde p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiLevel_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXiLevel p ε r}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXiLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε ≠ 1`, then `W(V♭) ⧸ (ξ'_r)` is `p`-torsion-free. -/
theorem isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel_of_ne_one {ε : PreTilt V p}
    (hne : ε ≠ 1) (r : ℕ) :
    IsSMulRegular (𝕎♭ ⧸ span {cyclotomicXiTildeLevel p ε r}) (p : 𝕎♭) :=
  isSMulRegular_quotient_natCast_cyclotomicXiTildeLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne)) r

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[p, μ]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicMu_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicMu p ε] :=
  isRegular_pair_natCast_cyclotomicMu p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1)

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[μ, p]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_cyclotomicMu_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [cyclotomicMu p ε, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicMu_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1)

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[p, ξ]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXi_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXi p ε] :=
  isRegular_pair_natCast_cyclotomicXi p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1)

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[ξ, p]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_cyclotomicXi_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [cyclotomicXi p ε, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXi_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1)

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[p, ξ']` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTilde_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXiTilde p ε] :=
  isRegular_pair_natCast_cyclotomicXiTilde p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1)

/-- If `ε : V♭` has `ε♯ = 1` and `ε ≠ 1`, then `[ξ', p]` is a regular sequence on `W(V♭)`. -/
theorem isRegular_pair_cyclotomicXiTilde_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) :
    IsRegular (𝕎♭) [cyclotomicXiTilde p ε, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXiTilde_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1)

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[p, ξ_r]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXiLevel_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXiLevel p ε r] :=
  isRegular_pair_natCast_cyclotomicXiLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1) hr

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[ξ_r, p]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_cyclotomicXiLevel_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [cyclotomicXiLevel p ε r, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXiLevel_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1) hr

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[p, ξ'_r]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_natCast_cyclotomicXiTildeLevel_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [(p : 𝕎♭), cyclotomicXiTildeLevel p ε r] :=
  isRegular_pair_natCast_cyclotomicXiTildeLevel p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1) hr

/-- If `ε : V♭` has `ε♯ = 1`, `ε ≠ 1`, and `1 ≤ r`, then `[ξ'_r, p]` is a regular sequence on
`W(V♭)`. -/
theorem isRegular_pair_cyclotomicXiTildeLevel_natCast_of_untilt_eq_one {ε : PreTilt V p}
    (hε1 : ε.untilt = 1) (hne : ε ≠ 1) {r : ℕ} (hr : 1 ≤ r) :
    IsRegular (𝕎♭) [cyclotomicXiTildeLevel p ε r, (p : 𝕎♭)] :=
  isRegular_pair_cyclotomicXiTildeLevel_natCast p
    (mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε1) hr

end DomainRegularity

section NormedField

open TauCeti.Huber
open scoped _root_.NormedField Valued

variable {p : ℕ} [hp : Fact p.Prime] {C : Type*} [NormedField C] [IsUltrametricDist C]

private theorem integers_powerBoundedSubring :
    (NormedField.valuation (K := C)).Integers (powerBoundedSubring C) where
  hom_inj := (powerBoundedSubring C).subtype_injective
  map_le_one x := by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnNorm]
    exact isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.property)
  exists_of_le_one {x} hx := by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnNorm] at hx
    exact ⟨⟨x, mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr hx)⟩, rfl⟩

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
theorem span_cyclotomicMu_eq_of_isPrimitiveRoot {C : Type*} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [hpnu : Fact ¬IsUnit (p : powerBoundedSubring C)]
    [IsAdicComplete (span {(p : powerBoundedSubring C)}) (powerBoundedSubring C)]
    {ε ε' : PreTilt (powerBoundedSubring C) p}
    (hζ : IsPrimitiveRoot
      (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε).untilt) p)
    (hζ' : IsPrimitiveRoot
      (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε').untilt) p) :
    span {cyclotomicMu p ε} = span {cyclotomicMu p ε'} := by
  have hpC : ‖(p : C)‖ < 1 := lt_of_le_of_ne
    (isPowerBounded_iff_norm_le_one.mp
      (mem_powerBoundedSubring.mp (p : powerBoundedSubring C).prop))
    ((powerBoundedSubring.isUnit_iff_norm_eq_one).not.mp hpnu.out)
  have : TauCeti.Perfectoid.IsPerfectoidTateRing p C :=
    TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed hpC
  exact span_cyclotomicMu_eq_of_geom_sum_eq_zero integers_powerBoundedSubring
    (hζ.geom_sum_eq_zero hp.out.one_lt) (hζ'.geom_sum_eq_zero hp.out.one_lt)

end NormedField

end TauCeti.WittVector
