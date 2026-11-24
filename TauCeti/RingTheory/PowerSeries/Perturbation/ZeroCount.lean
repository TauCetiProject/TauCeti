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
(`TauCeti.PowerSeries.isLowestDominant_iff_of_gaussNorm_sub_lt` and
`TauCeti.PowerSeries.isDistinguished_iff_of_gaussNorm_sub_lt`). In a complete normed field
extension `L` over which the disc polynomials split, the zeros of a series counted with
multiplicity number `d` in the closed disc `‖x‖ ≤ r`, `l` in the open disc `‖x‖ < r` and `d - l`
on the sphere `‖x‖ = r` (`TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_eq_of_splits`
and its companions). Hence `f` and `g` have the same number of zeros in each of these three
regions, counted with multiplicity.

The zeros themselves move under the perturbation: `X` and `X - c` with `0 < ‖c‖ < r` each have
one zero in the open disc of radius `r`, at different points. Only the counts are stable.

Without a splitting hypothesis on the disc polynomials, both series are prepared over a complete
`K`, and the counts agree in every algebraically closed complete extension `L`, for instance `ℂ_p`
over `ℚ_p`. The strict inequality is necessary: `1` and `1 - X / a` with `‖a‖ = r` differ by a
series of Gauss norm `1 = ‖1‖_r`, and the second has a zero on the sphere while the first has none.

## Main results

* `TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_splits`,
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_splits` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_splits`: a
  Gauss-small perturbation preserves the numbers of zeros in the closed disc, the open disc and
  on the sphere, in an extension where both disc polynomials split.
* `TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt`,
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt`: the same over a
  complete `K`, in every algebraically closed complete extension.

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
  {f g : PowerSeries K} {r : ℝ} {d : ℕ}

section Splits

variable {e e' : PowerSeries.IsRestricted.subring (R := K) r} {P Q : Polynomial K}

/-- **Closed-disc zero counts are stable, split case.** Let `f = e * P` and `g = e' * Q` over an
ultrametric normed field, with `e` and `e'` units of the ring of series restricted at `r > 0` and
`P`, `Q` monic of the distinguished degree `d` of `f` at `r`. If `‖f - g‖_r < ‖f‖_r`, then in
any complete normed field extension over which `P` and `Q` split, `f` and `g` have the same
number of zeros in the closed disc of radius `r`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_splits (hr : 0 < r)
    (hd : IsDistinguished r d f) (h : (f - g).gaussNorm norm r < f.gaussNorm norm r)
    (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hsP : (P.map (algebraMap K L)).Splits)
    (he' : IsUnit e') (hQ : Q.IsMonicOfDegree d) (hg : (e' : PowerSeries K) * Q = g)
    (hsQ : (Q.map (algebraMap K L)).Splits) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  have hd' := (isDistinguished_iff_of_gaussNorm_sub_lt hr.le hd.hasGaussNorm
    (hasGaussNorm_of_isRestricted (hg ▸ e'.property.mul (isRestricted_polynomial Q))) h).mp hd
  rw [hd.card_zeroMultiset_eq_of_splits hr he hP hf hsP,
    hd'.card_zeroMultiset_eq_of_splits hr he' hQ hg hsQ]

/-- **Open-disc zero counts are stable, split case.** Let `f = e * P` and `g = e' * Q` over an
ultrametric normed field, with `e` and `e'` units of the ring of series restricted at `r > 0` and
`P`, `Q` monic of the distinguished degree `d` of `f` at `r`. If `‖f - g‖_r < ‖f‖_r`, then in
any complete normed field extension over which `P` and `Q` split, `f` and `g` have the same
number of zeros in the open disc of radius `r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_splits (hr : 0 < r)
    (hd : IsDistinguished r d f) (h : (f - g).gaussNorm norm r < f.gaussNorm norm r)
    (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hsP : (P.map (algebraMap K L)).Splits)
    (he' : IsUnit e') (hQ : Q.IsMonicOfDegree d) (hg : (e' : PowerSeries K) * Q = g)
    (hsQ : (Q.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  have hfn := hd.hasGaussNorm
  have hgn := hasGaussNorm_of_isRestricted (hg ▸ e'.property.mul (isRestricted_polynomial Q))
  have hd' := (isDistinguished_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hd
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr (hf ▸ e.property.mul (isRestricted_polynomial P))
    hd.ne_zero
  have hl' := (isLowestDominant_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hl
  rw [hl.card_filter_zeroMultiset_norm_lt_eq_of_splits hd hr he hP hf hsP,
    hl'.card_filter_zeroMultiset_norm_lt_eq_of_splits hd' hr he' hQ hg hsQ]

/-- **Sphere zero counts are stable, split case.** Let `f = e * P` and `g = e' * Q` over an
ultrametric normed field, with `e` and `e'` units of the ring of series restricted at `r > 0` and
`P`, `Q` monic of the distinguished degree `d` of `f` at `r`. If `‖f - g‖_r < ‖f‖_r`, then in
any complete normed field extension over which `P` and `Q` split, `f` and `g` have the same
number of zeros `x` with `‖x‖ = r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_splits (hr : 0 < r)
    (hd : IsDistinguished r d f) (h : (f - g).gaussNorm norm r < f.gaussNorm norm r)
    (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hsP : (P.map (algebraMap K L)).Splits)
    (he' : IsUnit e') (hQ : Q.IsMonicOfDegree d) (hg : (e' : PowerSeries K) * Q = g)
    (hsQ : (Q.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  have hfn := hd.hasGaussNorm
  have hgn := hasGaussNorm_of_isRestricted (hg ▸ e'.property.mul (isRestricted_polynomial Q))
  have hd' := (isDistinguished_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hd
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr (hf ▸ e.property.mul (isRestricted_polynomial P))
    hd.ne_zero
  have hl' := (isLowestDominant_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hl
  rw [card_filter_zeroMultiset_norm_eq_eq_of_splits hd hl hr he hP hf hsP,
    card_filter_zeroMultiset_norm_eq_eq_of_splits hd' hl' hr he' hQ hg hsQ]

end Splits

section IsAlgClosed

variable [CompleteSpace K] [IsAlgClosed L]

/-- **Closed-disc zero counts are stable.** Let `f` and `g` be power series over a complete
ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any algebraically
closed complete normed field extension, `f` and `g` have the same number of zeros in the closed
disc of radius `r`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt (hr : 0 < r) (hfr : f.IsRestricted r)
    (hgr : g.IsRestricted r) (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  have hfn : f.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hfr
  have hgn : g.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hgr
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr (ne_zero_of_gaussNorm_sub_lt h)
  have hd' := (isDistinguished_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hd
  rw [hd.card_zeroMultiset_eq hr hfr, hd'.card_zeroMultiset_eq hr hgr]

/-- **Open-disc zero counts are stable.** Let `f` and `g` be power series over a complete
ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any algebraically
closed complete normed field extension, `f` and `g` have the same number of zeros in the open
disc of radius `r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  have hfn : f.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hfr
  have hgn : g.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hgr
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr hfr (ne_zero_of_gaussNorm_sub_lt h)
  have hl' := (isLowestDominant_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hl
  rw [hl.card_filter_zeroMultiset_norm_lt_eq hr hfr, hl'.card_filter_zeroMultiset_norm_lt_eq hr hgr]

/-- **Sphere zero counts are stable.** Let `f` and `g` be power series over a complete ultrametric
normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any algebraically closed
complete normed field extension, `f` and `g` have the same number of zeros `x` with `‖x‖ = r`,
counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (h : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  have hf0 := ne_zero_of_gaussNorm_sub_lt h
  have hfn : f.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hfr
  have hgn : g.HasGaussNorm norm r := hasGaussNorm_of_isRestricted hgr
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr hf0
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr hfr hf0
  rw [card_filter_zeroMultiset_norm_eq_eq hd hl hr hfr,
    card_filter_zeroMultiset_norm_eq_eq ((isDistinguished_iff_of_gaussNorm_sub_lt hr.le hfn hgn
      h).mp hd) ((isLowestDominant_iff_of_gaussNorm_sub_lt hr.le hfn hgn h).mp hl) hr hgr]

end IsAlgClosed

end TauCeti.PowerSeries
