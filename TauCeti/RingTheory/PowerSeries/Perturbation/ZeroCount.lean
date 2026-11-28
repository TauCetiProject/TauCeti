/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Perturbation.Basic
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount

/-!
# Stability of zero counts under Gauss-small perturbations

Let `f` and `g` be power series over an ultrametric normed field `K`, both restricted at a radius
`r > 0`, with `‖f - g‖_r < ‖f‖_r`. Such a perturbation preserves the Gauss norm and the first and
last indices attaining it, the lowest dominant degree `l` and the distinguished degree `d`
(`TauCeti.PowerSeries.exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt`). In a
complete normed field extension `L` over which prepared or normalised disc polynomial factors of `f`
and `g` split, the zeros of each series counted with multiplicity number `d` in the closed disc
`‖x‖ ≤ r`, `l` in the open disc `‖x‖ < r` and `d - l` on the sphere `‖x‖ = r`
(`TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_eq_of_isUnit_mul` and its companions).
Hence `f` and `g` have the same number of zeros in each of these three regions, counted with
multiplicity.

The zeros themselves move under the perturbation: `X` and `X - c` with `0 < ‖c‖ < r` each have
one zero in the open disc of radius `r`, at different points. Only the counts are stable.

Without any preparation data or completeness assumption on `K`, both series can be prepared after
mapping into `L`, so the counts agree in every algebraically closed complete extension `L`, for
instance `ℂ_p` over `ℚ_p`. The strict inequality is necessary: `1` and `1 - X / a` with
`‖a‖ = r` differ by a series of Gauss norm `1 = ‖1‖_r`, and the second has a zero on the sphere
while the first has none.

## Main results

* `TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul`,
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_isUnit_mul` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_isUnit_mul`: a
  Gauss-small perturbation preserves the numbers of zeros in the closed disc, the open disc and
  on the sphere, in any complete extension over which prepared polynomial factors split (with
  `IsDiscPreparation` versions
  `TauCeti.PowerSeries.IsDiscPreparation.card_zeroMultiset_eq_of_gaussNorm_sub_lt`,
  `TauCeti.PowerSeries.IsDiscPreparation.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt`,
  and
  `TauCeti.PowerSeries.IsDiscPreparation.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt`).
* `TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt`,
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt`: nonarchimedean
  Rouché theorems over any ultrametric normed field `K` in every algebraically closed complete
  extension `L`.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1 and 3.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {f g : PowerSeries K} {r : ℝ}

section IsUnitMul

variable {e e' : PowerSeries.IsRestricted.subring (R := K) r} {P Q : Polynomial K}

/-- A power series of the form `e * P` with `e` restricted at `r` and `P` a polynomial is
restricted at `r`. -/
private theorem isRestricted_of_coe_mul_eq (hf : (e : PowerSeries K) * P = f) :
    f.IsRestricted r := by
  rw [← hf]
  exact e.property.mul (isRestricted_polynomial P)

/-- **Closed-disc zero counts are stable, split case.** Let `f = e * P` and `g = e' * Q` over an
ultrametric normed field, with `e` and `e'` units of the ring of series restricted at `r > 0` and
`P`, `Q` polynomials splitting over a complete normed field extension `L`. If `‖f - g‖_r < ‖f‖_r`,
then `f` and `g` have the same number of zeros in the closed disc `‖x‖ ≤ r` of `L`, counted with
multiplicity. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul (hr : 0 < r)
    (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) (hsP : (P.map (algebraMap K L)).Splits)
    (he' : IsUnit e') (hg : (e' : PowerSeries K) * Q = g) (hsQ : (Q.map (algebraMap K L)).Splits)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  obtain ⟨_, _, hd, hdg, _, _⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le
      (isRestricted_of_coe_mul_eq hf)
      (hasGaussNorm_of_isRestricted (isRestricted_of_coe_mul_eq hg)) h
  rw [hd.card_zeroMultiset_eq_of_isUnit_mul hr he hf hsP,
    hdg.card_zeroMultiset_eq_of_isUnit_mul hr he' hg hsQ]

/-- **Open-disc zero counts are stable, split case.** Under the hypotheses of
`TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul`, `f` and `g` have the
same number of zeros in the open disc `‖x‖ < r` of `L`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_isUnit_mul (hr : 0 < r)
    (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) (hsP : (P.map (algebraMap K L)).Splits)
    (he' : IsUnit e') (hg : (e' : PowerSeries K) * Q = g) (hsQ : (Q.map (algebraMap K L)).Splits)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  obtain ⟨_, _, _, _, hl, hlg⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le
      (isRestricted_of_coe_mul_eq hf)
      (hasGaussNorm_of_isRestricted (isRestricted_of_coe_mul_eq hg)) h
  rw [hl.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul hr he hf hsP,
    hlg.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul hr he' hg hsQ]

/-- **Sphere zero counts are stable, split case.** Under the hypotheses of
`TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul`, `f` and `g` have the
same number of zeros on the sphere `‖x‖ = r` of `L`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_isUnit_mul (hr : 0 < r)
    (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) (hsP : (P.map (algebraMap K L)).Splits)
    (he' : IsUnit e') (hg : (e' : PowerSeries K) * Q = g) (hsQ : (Q.map (algebraMap K L)).Splits)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  obtain ⟨_, _, hd, hdg, hl, hlg⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le
      (isRestricted_of_coe_mul_eq hf)
      (hasGaussNorm_of_isRestricted (isRestricted_of_coe_mul_eq hg)) h
  rw [card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul hd hl hr he hf hsP,
    card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul hdg hlg hr he' hg hsQ]

end IsUnitMul

namespace IsDiscPreparation

variable {d dg : ℕ} {P Q : Polynomial K} {U V : PowerSeries K}

/-- A power series admitting a normalised disc preparation at `r` is restricted at `r`. -/
private theorem isRestricted_series (hfP : IsDiscPreparation r d f P U) :
    f.IsRestricted r := by
  rw [hfP.eq_mul]
  exact (isRestricted_polynomial P).mul hfP.isRestricted

/-- **Perturbation invariance of closed-disc zero counts for split disc polynomials.** If `f` and
`g` admit normalised disc preparations at `r > 0` whose polynomial factors both split over `L`, and
`‖f - g‖_r < ‖f‖_r`, then `f` and `g` have the same closed-disc zero count in `L`. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt
    (hfP : IsDiscPreparation r d f P U) (hgQ : IsDiscPreparation r dg g Q V)
    (hr : 0 < r) (hsP : (P.map (algebraMap K L)).Splits) (hsQ : (Q.map (algebraMap K L)).Splits)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  obtain ⟨_, _, hd, hdg, _, _⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le
      hfP.isRestricted_series hgQ.isDistinguished.hasGaussNorm h
  rw [hfP.card_zeroMultiset_eq_of_splits hr hsP, hgQ.card_zeroMultiset_eq_of_splits hr hsQ,
    hfP.isDistinguished.unique hd, hdg.unique hgQ.isDistinguished]

/-- **Perturbation invariance of open-disc zero counts for split disc polynomials.** Under the
hypotheses of `TauCeti.PowerSeries.IsDiscPreparation.card_zeroMultiset_eq_of_gaussNorm_sub_lt`, `f`
and `g` have the same open-disc zero count in `L`. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt
    (hfP : IsDiscPreparation r d f P U) (hgQ : IsDiscPreparation r dg g Q V)
    (hr : 0 < r) (hsP : (P.map (algebraMap K L)).Splits) (hsQ : (Q.map (algebraMap K L)).Splits)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  obtain ⟨_, _, _, _, hl, hlg⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le
      hfP.isRestricted_series hgQ.isDistinguished.hasGaussNorm h
  rw [hfP.card_filter_zeroMultiset_norm_lt_eq_of_splits hl hr hsP,
    hgQ.card_filter_zeroMultiset_norm_lt_eq_of_splits hlg hr hsQ]

/-- **Perturbation invariance of sphere zero counts for split disc polynomials.** Under the
hypotheses of `TauCeti.PowerSeries.IsDiscPreparation.card_zeroMultiset_eq_of_gaussNorm_sub_lt`, `f`
and `g` have the same sphere zero count in `L`. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt
    (hfP : IsDiscPreparation r d f P U) (hgQ : IsDiscPreparation r dg g Q V)
    (hr : 0 < r) (hsP : (P.map (algebraMap K L)).Splits) (hsQ : (Q.map (algebraMap K L)).Splits)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  obtain ⟨_, _, hd, hdg, hl, hlg⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le
      hfP.isRestricted_series hgQ.isDistinguished.hasGaussNorm h
  rw [hfP.card_filter_zeroMultiset_norm_eq_eq_of_splits hl hr hsP,
    hgQ.card_filter_zeroMultiset_norm_eq_eq_of_splits hlg hr hsQ,
    hfP.isDistinguished.unique hd, hdg.unique hgQ.isDistinguished]

end IsDiscPreparation

section IsAlgClosed

variable [IsAlgClosed L]

/-- **Nonarchimedean Rouché theorem on the closed disc.** Let `f` and `g` be power series over an
ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any algebraically
closed complete normed field extension `L`, `f` and `g` have the same number of zeros in the closed
disc `‖x‖ ≤ r`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt (hr : 0 < r) (hfr : f.IsRestricted r)
    (hgr : g.IsRestricted r) (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  obtain ⟨_, _, hd, hdg, _, _⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le hfr
      (hasGaussNorm_of_isRestricted hgr) h
  rw [hd.card_zeroMultiset_eq hr hfr, hdg.card_zeroMultiset_eq hr hgr]

/-- **Nonarchimedean Rouché theorem on the open disc.** Let `f` and `g` be power series over an
ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any algebraically
closed complete normed field extension `L`, `f` and `g` have the same number of zeros in the open
disc `‖x‖ < r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  obtain ⟨_, _, _, _, hl, hlg⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le hfr
      (hasGaussNorm_of_isRestricted hgr) h
  rw [hl.card_filter_zeroMultiset_norm_lt_eq hr hfr, hlg.card_filter_zeroMultiset_norm_lt_eq hr hgr]

/-- **Nonarchimedean Rouché theorem on the sphere.** Let `f` and `g` be power series over an
ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any algebraically
closed complete normed field extension `L`, `f` and `g` have the same number of zeros `x` with
`‖x‖ = r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  obtain ⟨_, _, hd, hdg, hl, hlg⟩ :=
    exists_isDistinguished_and_isLowestDominant_of_gaussNorm_sub_lt hr.le hfr
      (hasGaussNorm_of_isRestricted hgr) h
  rw [card_filter_zeroMultiset_norm_eq_eq hd hl hr hfr,
    card_filter_zeroMultiset_norm_eq_eq hdg hlg hr hgr]

end IsAlgClosed

end TauCeti.PowerSeries
