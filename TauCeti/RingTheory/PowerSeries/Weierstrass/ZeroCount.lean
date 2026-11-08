/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Polynomial.Degree.IsMonicOfDegree
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
public import TauCeti.RingTheory.PowerSeries.Map
public import TauCeti.RingTheory.PowerSeries.MulDistinguished
public import TauCeti.RingTheory.PowerSeries.Restricted.Taylor
public import TauCeti.RingTheory.PowerSeries.RootBound
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Multiplicities and numbers of zeros of restricted power series

Let `K` be a complete ultrametric normed field, `f` a nonzero power series over `K` restricted at a
radius `r > 0`, and `L` a complete normed field extension of `K`. The *multiplicity* of a zero
`x ∈ L` of `f` is the order at `0` of the translated series `f(x + T)`, the Taylor translate
`PowerSeries.taylor x f` of `f` read over `L`. Its coefficients are the values at `x` of the Hasse
derivatives of `f`, so the multiplicity is also the index of the first Hasse derivative not
vanishing at `x` (`PowerSeries.isGoodZero_iff_order_taylor_eq`). No factorial is inverted, so this
is the right notion in every characteristic, including for inseparable polynomials. The definition
involves no radius: the multiplicity at `x` is the same for every radius `r ≥ ‖x‖` at which `f` is
restricted.

Weierstrass preparation writes `f = e * P` with `e` a unit of the ring of series restricted at `r`
and `P` a polynomial. Taylor translation by a point `x` of the closed disc is multiplicative, and
the translate of `e` has the nonzero constant term `e(x)`, so the multiplicity of `f` at `x` is the
root multiplicity of `x` as a root of `P`. Hence the zeros of `f` in the closed disc of `L`,
counted with multiplicity, form a finite multiset, the zero multiset of `f` on that disc: it is
the multiset of roots of `P` in `L`. Let `d` be the
distinguished degree of `f` at `r` (the last index whose weighted coefficient norm `‖aₙ‖ rⁿ`
attains the Gauss norm) and `l` its lowest dominant degree (the first such index). Then there are
at most `d` zeros in the closed disc and at most `l` in the open disc `‖x‖ < r`. If `P` splits
over `L`, in particular if `L` is algebraically closed, these are equalities, and there are exactly
`d - l` zeros on the sphere `‖x‖ = r`. All counts include the zero `x = 0`. For `ℂ_p` these are the
exact zero counts of `p`-adic analytic functions on closed and open discs.

These counts refine Strassmann's bound
`TauCeti.PowerSeries.IsDistinguished.encard_setOf_evalAt_eq_zero_le` for the number of distinct
zeros. At a radius on the boundary of convergence they are stated through the active indices `d`
and `l` themselves, since the shape of the Newton polygon alone does not determine the number of
boundary zeros.

## Main definitions

* `PowerSeries.zeroMultiset f r L`: the zeros of `f` in the closed disc `‖x‖ ≤ r` of `L`, each
  repeated as often as its multiplicity.

## Main results

* `TauCeti.PowerSeries.order_taylor_mul_eq_rootMultiplicity`: on the closed disc, the
  multiplicity of a zero of `e * P` is its root multiplicity for `P`.
* `TauCeti.PowerSeries.order_taylor_map_eq_rootMultiplicity`: the same in a complete normed field
  extension.
* `TauCeti.PowerSeries.IsDistinguished.card_filter_roots_map_norm_le_le`,
  `TauCeti.PowerSeries.IsDistinguished.card_filter_roots_map_norm_le_eq`,
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_roots_map_norm_lt_le`,
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_roots_map_norm_lt_eq` and
  `TauCeti.PowerSeries.card_filter_roots_map_norm_eq_eq`: the roots of the preparation polynomial
  in the closed disc and in the open disc number at most, and when it splits exactly, the
  distinguished and the lowest dominant degree of the series; when it splits, the roots on the
  sphere number the difference.
* `PowerSeries.norm_le_of_mem_zeroMultiset`,
  `PowerSeries.zeroMultiset_eq_of_order_taylor_eq` and
  `PowerSeries.IsRestricted.order_taylor_eq_count_zeroMultiset`: the zero multiset lies in the
  closed disc, is the only multiset there with the multiplicities of `f`, and has them.
* `PowerSeries.IsRestricted.mem_zeroMultiset_iff`: its points are exactly the zeros of `f` in the
  closed disc.
* `TauCeti.PowerSeries.IsDistinguished.zeroMultiset_eq_roots_map`: the zero multiset is the
  multiset of roots in `L` of any monic preparation polynomial.
* `TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_le`,
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_zeroMultiset_norm_lt_le`: the zero multiset
  has at most `d` elements, of which at most `l` lie in the open disc.
* `TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_eq_of_splits`,
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq_of_splits` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_splits`: if a monic preparation
  polynomial splits over `L`, exactly `d` zeros in the closed disc, `l` in the open disc and
  `d - l` on the sphere.
* `TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_eq`,
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq`: the same counts over an
  algebraically closed `L`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1 and 3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §4.
-/

public section

namespace TauCeti.PowerSeries

section ZeroMultiset

variable {K : Type*} [NormedField K]

open Classical in
/-- The **zero multiset** of `f` on the closed disc `‖x‖ ≤ r` of a normed field extension `L`:
the multiset of points of that disc in which each `x` occurs as often as the multiplicity of `f`
at `x`, the order of the Taylor translate of `f` at `x`. It is unique when it exists
(`PowerSeries.zeroMultiset_eq_of_order_taylor_eq`), and it exists when `f` is a nonzero series
over a complete ultrametric field restricted at `r > 0` and `L` is complete
(`PowerSeries.IsRestricted.order_taylor_eq_count_zeroMultiset`); otherwise it is `0`. -/
noncomputable def _root_.PowerSeries.zeroMultiset (f : PowerSeries K) (r : ℝ) (L : Type*)
    [NormedField L] [NormedAlgebra K L] : Multiset L :=
  if h : ∃ Z : Multiset L, (∀ z ∈ Z, ‖z‖ ≤ r) ∧ ∀ x : L, ‖x‖ ≤ r →
      (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order = Z.count x
  then h.choose else 0

variable {L : Type*} [NormedField L] [NormedAlgebra K L] {f : PowerSeries K} {r : ℝ}

/-- The zero multiset of `f` on the closed disc of radius `r` lies in that disc. -/
theorem _root_.PowerSeries.norm_le_of_mem_zeroMultiset {x : L} (hx : x ∈ f.zeroMultiset r L) :
    ‖x‖ ≤ r := by
  unfold _root_.PowerSeries.zeroMultiset at hx
  split_ifs at hx with h
  · exact h.choose_spec.1 x hx
  · simp at hx

/-- A multiset of points of the closed disc of radius `r` whose multiplicities are those of the
zeros of `f` is the zero multiset of `f` on that disc. -/
theorem _root_.PowerSeries.zeroMultiset_eq_of_order_taylor_eq [DecidableEq L] {Z : Multiset L}
    (hZ : ∀ z ∈ Z, ‖z‖ ≤ r)
    (hZf : ∀ x : L, ‖x‖ ≤ r →
      (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
        Z.count x) :
    f.zeroMultiset r L = Z := by
  unfold _root_.PowerSeries.zeroMultiset
  split_ifs with h
  · have hc : ∀ x : L, ‖x‖ ≤ r →
        (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
          h.choose.count x := fun x hx ↦ by convert h.choose_spec.2 x hx
    ext x
    by_cases hx : ‖x‖ ≤ r
    · exact_mod_cast (hc x hx).symm.trans (hZf x hx)
    · rw [Multiset.count_eq_zero.mpr fun h' ↦ hx (h.choose_spec.1 x h'),
        Multiset.count_eq_zero.mpr fun h' ↦ hx (hZ x h')]
  · exact absurd ⟨Z, hZ, fun x hx ↦ by convert hZf x hx⟩ h

end ZeroMultiset

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {r : ℝ}

/-- **Multiplicities of zeros on a closed disc.** Let `e` be a unit of the ring of series over a
complete ultrametric normed field restricted at `r`, and `P` a nonzero polynomial. At every point
`x` with `‖x‖ ≤ r`, the multiplicity of `e * P` at `x`, the order of its Taylor translate at `x`,
is the multiplicity of `x` as a root of `P`. -/
theorem order_taylor_mul_eq_rootMultiplicity [CompleteSpace K]
    {e : PowerSeries.IsRestricted.subring (R := K) r} (he : IsUnit e) {P : Polynomial K}
    (hP : P ≠ 0) {x : K} (hx : ‖x‖ ≤ r) :
    (_root_.PowerSeries.taylor x ((e : PowerSeries K) * P)).order = P.rootMultiplicity x := by
  -- The translate of the unit has the nonzero constant term `e(x)`.
  have hu : (e : PowerSeries K).evalAt x ≠ 0 := by
    simpa using (he.map (_root_.PowerSeries.IsRestricted.evalAtHom K hx)).ne_zero
  have h0 : (_root_.PowerSeries.taylor x (e : PowerSeries K)).order = 0 := by
    simpa using (_root_.PowerSeries.order_eq_nat (n := 0)).mpr
      ⟨by simpa using hu, fun i hi ↦ absurd hi i.not_lt_zero⟩
  rw [_root_.PowerSeries.IsRestricted.taylor_mul e.2 (isRestricted_polynomial P) hx,
    _root_.PowerSeries.order_mul, h0, zero_add]
  exact _root_.PowerSeries.isGoodZero_iff_order_taylor_eq.mp
    (_root_.PowerSeries.isGoodZero_coe_iff_of_field.mpr ⟨hP, rfl⟩)

variable {L : Type*} [NormedField L] [NormedAlgebra K L] {d l : ℕ}
  {f : PowerSeries K} {e : PowerSeries.IsRestricted.subring (R := K) r} {P : Polynomial K}

/-- Over a normed field extension `L`, the factorization `f = e * P` becomes the factorization of
the mapped series into the mapped unit and the mapped polynomial. -/
private theorem map_eq_restrictedMap_mul [IsUltrametricDist L]
    (hf : (e : PowerSeries K) * P = f) :
    ∃ e' : PowerSeries.IsRestricted.subring (R := L) r, (IsUnit e → IsUnit e') ∧
      _root_.PowerSeries.map (algebraMap K L) f =
        (e' : PowerSeries L) * (P.map (algebraMap K L) : Polynomial L) := by
  have hφ : ∀ a : K, ‖algebraMap K L a‖ ≤ 1 * ‖a‖ := fun a ↦ by rw [norm_algebraMap', one_mul]
  refine ⟨TauCeti.MvPowerSeries.restrictedMap (algebraMap K L) hφ e, fun he ↦ he.map _, ?_⟩
  rw [← hf, map_mul, ← coe_restrictedMap_powerSeries _ hφ, Polynomial.polynomial_map_coe]

/-- The mapped polynomial factor has the lowest dominant degree of the series. -/
private theorem IsLowestDominant.map_polynomial (hl : IsLowestDominant r l f) (hr : 0 < r)
    (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) :
    IsLowestDominant r l (P.map (algebraMap K L) : PowerSeries L) := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  obtain ⟨e', he', hmap⟩ := map_eq_restrictedMap_mul (L := L) hf
  have h := hl.map (algebraMap K L) (norm_algebraMap' L)
  rw [hmap] at h
  exact h.of_isUnit_mul hr (he' he)

/-- The mapped polynomial factor has the distinguished degree of the series. -/
private theorem IsDistinguished.map_polynomial (hd : IsDistinguished r d f) (hr : 0 < r)
    (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) :
    IsDistinguished r d (P.map (algebraMap K L) : PowerSeries L) := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  obtain ⟨e', he', hmap⟩ := map_eq_restrictedMap_mul (L := L) hf
  have h := hd.map (algebraMap K L) (norm_algebraMap' L)
  rw [hmap] at h
  exact h.of_isUnit_mul hr (he' he)

/-- **Zeros in the open disc.** Let `f = e * P` over an ultrametric normed field `K`, with `e` a
unit of the ring of series restricted at `r > 0`, and let `l` be the lowest dominant degree of `f`
at `r`. In any normed field extension `L`, the polynomial `P` has at most `l` roots `x` with
`‖x‖ < r`, counted with multiplicity. -/
theorem IsLowestDominant.card_filter_roots_map_norm_lt_le (hl : IsLowestDominant r l f)
    (hr : 0 < r) (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) :
    ((P.map (algebraMap K L)).roots.filter (‖·‖ < r)).card ≤ l := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  exact (hl.map_polynomial hr he hf).card_filter_roots_norm_lt_le hr

/-- **Zeros in the open disc, split case.** Let `f = e * P` over an ultrametric normed field `K`,
with `e` a unit of the ring of series restricted at `r > 0`, and let `l` be the lowest dominant
degree of `f` at `r`. In any normed field extension `L` over which `P` splits, `P` has exactly `l`
roots `x` with `‖x‖ < r`, counted with multiplicity. -/
theorem IsLowestDominant.card_filter_roots_map_norm_lt_eq (hl : IsLowestDominant r l f)
    (hr : 0 < r) (he : IsUnit e) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((P.map (algebraMap K L)).roots.filter (‖·‖ < r)).card = l := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  exact (hl.map_polynomial hr he hf).card_filter_roots_norm_lt_eq hr hs

/-- **Zeros in the closed disc.** Let `f = e * P` over an ultrametric normed field `K`, with `e` a
unit of the ring of series restricted at `r > 0`, and let `d` be the distinguished degree of `f` at
`r`. In any normed field extension `L`, the polynomial `P` has at most `d` roots `x` with
`‖x‖ ≤ r`, counted with multiplicity. -/
theorem IsDistinguished.card_filter_roots_map_norm_le_le (hd : IsDistinguished r d f)
    (hr : 0 < r) (he : IsUnit e) (hf : (e : PowerSeries K) * P = f) :
    ((P.map (algebraMap K L)).roots.filter (‖·‖ ≤ r)).card ≤ d := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  exact (hd.map_polynomial hr he hf).card_filter_roots_norm_le_le hr

/-- **Zeros in the closed disc, split case.** Let `f = e * P` over an ultrametric normed field `K`,
with `e` a unit of the ring of series restricted at `r > 0`, and let `d` be the distinguished
degree of `f` at `r`. In any normed field extension `L` over which `P` splits, `P` has exactly `d`
roots `x` with `‖x‖ ≤ r`, counted with multiplicity. -/
theorem IsDistinguished.card_filter_roots_map_norm_le_eq (hd : IsDistinguished r d f)
    (hr : 0 < r) (he : IsUnit e) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((P.map (algebraMap K L)).roots.filter (‖·‖ ≤ r)).card = d := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  exact (hd.map_polynomial hr he hf).card_filter_roots_norm_le_eq hr hs

/-- **Zeros on the sphere, split case.** Let `f = e * P` over an ultrametric normed field `K`, with
`e` a unit of the ring of series restricted at `r > 0`, and let `d` and `l` be the distinguished
and lowest dominant degrees of `f` at `r`. In any normed field extension `L` over which `P`
splits, `P` has exactly `d - l` roots `x` with `‖x‖ = r`, counted with multiplicity. -/
theorem card_filter_roots_map_norm_eq_eq (hd : IsDistinguished r d f)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (he : IsUnit e) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((P.map (algebraMap K L)).roots.filter (‖·‖ = r)).card = d - l := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  exact card_filter_roots_norm_eq_eq (hd.map_polynomial hr he hf) (hl.map_polynomial hr he hf) hr
    hs

variable [CompleteSpace L]

/-- **Multiplicities of zeros in an extension.** Let `f = e * P` over an ultrametric normed field
`K`, with `e` a unit of the ring of series restricted at `r` and `P` a nonzero polynomial.
In any complete normed field extension `L` of `K`, at every point `x` with `‖x‖ ≤ r`, the
multiplicity of `f` at `x` is the multiplicity of `x` as a root of `P`. -/
theorem order_taylor_map_eq_rootMultiplicity (he : IsUnit e) (hP : P ≠ 0)
    (hf : (e : PowerSeries K) * P = f) {x : L} (hx : ‖x‖ ≤ r) :
    (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
      (P.map (algebraMap K L)).rootMultiplicity x := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  obtain ⟨e', he', hmap⟩ := map_eq_restrictedMap_mul (L := L) hf
  rw [hmap]
  exact order_taylor_mul_eq_rootMultiplicity (he' he)
    ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hP) hx

/-- The roots in `L` of a monic preparation polynomial of `f` lie in the closed disc, and they are
the zeros of `f` there, with their multiplicities. -/
private theorem roots_map_spec [DecidableEq L] (hd : IsDistinguished r d f) (hr : 0 < r)
    (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f) :
    (∀ z ∈ (P.map (algebraMap K L)).roots, ‖z‖ ≤ r) ∧
      ∀ x : L, ‖x‖ ≤ r →
        (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
          (P.map (algebraMap K L)).roots.count x := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  refine ⟨fun z hz ↦ (hd.map_polynomial hr he hf).norm_le_of_eval_eq_zero hr
    (hP.map (algebraMap K L)) (Polynomial.mem_roots'.mp hz).2, fun x hx ↦ ?_⟩
  rw [order_taylor_map_eq_rootMultiplicity he hP.ne_zero hf hx, Polynomial.count_roots]

/-- **The zero multiset is the root multiset.** Let `f = e * P` over an ultrametric normed field,
with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the distinguished
degree `d` of `f` at `r`. In any complete normed field extension `L`, the zero multiset of `f` on
the closed disc of radius `r` is the multiset of roots of `P` in `L`. -/
theorem IsDistinguished.zeroMultiset_eq_roots_map (hd : IsDistinguished r d f) (hr : 0 < r)
    (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f) :
    f.zeroMultiset r L = (P.map (algebraMap K L)).roots := by
  classical
  obtain ⟨hroots, hcount⟩ := roots_map_spec (L := L) hd hr he hP hf
  exact _root_.PowerSeries.zeroMultiset_eq_of_order_taylor_eq hroots hcount

/-- **Exactly `d` zeros in the closed disc, split case.** Let `f = e * P` over an ultrametric
normed field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`. In any complete normed field extension over which `P`
splits, the zeros of `f` in the closed disc of radius `r`, counted with multiplicity, number
exactly `d`. -/
theorem IsDistinguished.card_zeroMultiset_eq_of_splits (hd : IsDistinguished r d f)
    (hr : 0 < r) (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) : (f.zeroMultiset r L).card = d := by
  rw [hd.zeroMultiset_eq_roots_map hr he hP hf, Polynomial.splits_iff_card_roots.mp hs,
    (hP.map (algebraMap K L)).natDegree_eq]

/-- **Exactly `l` zeros in the open disc, split case.** Let `f = e * P` over an ultrametric normed
field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`, and let `l` be the lowest dominant degree of `f` at `r`. In
any complete normed field extension over which `P` splits, the zeros of `f` in the open disc of
radius `r`, counted with multiplicity, number exactly `l`. -/
theorem IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq_of_splits
    (hl : IsLowestDominant r l f) (hd : IsDistinguished r d f) (hr : 0 < r) (he : IsUnit e)
    (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card = l := by
  rw [hd.zeroMultiset_eq_roots_map hr he hP hf]
  exact hl.card_filter_roots_map_norm_lt_eq hr he hf hs

/-- **Exactly `d - l` zeros on the sphere, split case.** Let `f = e * P` over an ultrametric normed
field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`, and let `l` be the lowest dominant degree of `f` at `r`. In
any complete normed field extension over which `P` splits, the zeros `x` of `f` with `‖x‖ = r`,
counted with multiplicity, number exactly `d - l`. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_splits (hd : IsDistinguished r d f)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (he : IsUnit e) (hP : P.IsMonicOfDegree d)
    (hf : (e : PowerSeries K) * P = f) (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card = d - l := by
  rw [hd.zeroMultiset_eq_roots_map hr he hP hf]
  exact card_filter_roots_map_norm_eq_eq hd hl hr he hf hs

variable [CompleteSpace K]

/-- **Multiplicities in the zero multiset.** Let `f` be a nonzero power series over a complete
ultrametric normed field `K`, restricted at `r > 0`. In any complete normed field extension `L`,
the multiplicity of `f` at every point `x` of the closed disc `‖x‖ ≤ r` of `L` is the multiplicity
of `x` in the zero multiset of `f` on that disc. -/
theorem _root_.PowerSeries.IsRestricted.order_taylor_eq_count_zeroMultiset [DecidableEq L]
    (hfr : f.IsRestricted r) (hr : 0 < r) (hf0 : f ≠ 0) {x : L} (hx : ‖x‖ ≤ r) :
    (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
      (f.zeroMultiset r L).count x := by
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr hf0
  obtain ⟨e, P, he, hP, hf⟩ :=
    hd.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) hr hfr
  rw [hd.zeroMultiset_eq_roots_map hr he hP hf]
  exact (roots_map_spec hd hr he hP hf).2 x hx

/-- **Members of the zero multiset.** Let `f` be a nonzero power series over a complete ultrametric
normed field `K`, restricted at `r > 0`. In any complete normed field extension `L`, the points of
the zero multiset of `f` on the closed disc of radius `r` are exactly the zeros of `f` in that
disc. -/
theorem _root_.PowerSeries.IsRestricted.mem_zeroMultiset_iff (hfr : f.IsRestricted r) (hr : 0 < r)
    (hf0 : f ≠ 0) {x : L} :
    x ∈ f.zeroMultiset r L ↔
      ‖x‖ ≤ r ∧ (_root_.PowerSeries.map (algebraMap K L) f).evalAt x = 0 := by
  classical
  by_cases hx : ‖x‖ ≤ r
  · rw [← Multiset.count_ne_zero, ← Nat.cast_ne_zero (R := ℕ∞),
      ← hfr.order_taylor_eq_count_zeroMultiset hr hf0 hx,
      _root_.PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
      _root_.PowerSeries.constantCoeff_taylor]
    exact (and_iff_right hx).symm
  · exact iff_of_false (fun h ↦ hx (_root_.PowerSeries.norm_le_of_mem_zeroMultiset h))
      fun h ↦ hx h.1

/-- **At most `d` zeros in the closed disc.** Let `f` be a power series over a complete ultrametric
normed field, restricted at `r > 0` and distinguished of degree `d` there. In any complete normed
field extension, the zeros of `f` in the closed disc of radius `r`, counted with multiplicity,
number at most `d`. -/
theorem IsDistinguished.card_zeroMultiset_le (hd : IsDistinguished r d f) (hr : 0 < r)
    (hfr : f.IsRestricted r) : (f.zeroMultiset r L).card ≤ d := by
  obtain ⟨e, P, he, hP, hf⟩ :=
    hd.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) hr hfr
  rw [hd.zeroMultiset_eq_roots_map hr he hP hf]
  exact (Polynomial.card_roots' _).trans
    (Polynomial.natDegree_map_le.trans hP.natDegree_eq.le)

/-- **At most `l` zeros in the open disc.** Let `f` be a power series over a complete ultrametric
normed field, restricted at `r > 0` with lowest dominant degree `l` there. In any complete normed
field extension, the zeros of `f` in the open disc of radius `r`, counted with multiplicity, number
at most `l`. -/
theorem IsLowestDominant.card_filter_zeroMultiset_norm_lt_le (hl : IsLowestDominant r l f)
    (hr : 0 < r) (hfr : f.IsRestricted r) : ((f.zeroMultiset r L).filter (‖·‖ < r)).card ≤ l := by
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr hl.ne_zero
  obtain ⟨e, P, he, hP, hf⟩ :=
    hd.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) hr hfr
  rw [hd.zeroMultiset_eq_roots_map hr he hP hf]
  exact hl.card_filter_roots_map_norm_lt_le hr he hf

variable [IsAlgClosed L]

/-- **Exactly `d` zeros in the closed disc.** Let `f` be a power series over a complete ultrametric
normed field, restricted at `r > 0` and distinguished of degree `d` there. In any algebraically
closed complete normed field extension, the zeros of `f` in the closed disc of radius `r`, counted
with multiplicity, number exactly `d`. -/
theorem IsDistinguished.card_zeroMultiset_eq (hd : IsDistinguished r d f) (hr : 0 < r)
    (hfr : f.IsRestricted r) : (f.zeroMultiset r L).card = d := by
  obtain ⟨e, P, he, hP, hf⟩ :=
    hd.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) hr hfr
  exact hd.card_zeroMultiset_eq_of_splits hr he hP hf (IsAlgClosed.splits _)

/-- **Exactly `l` zeros in the open disc.** Let `f` be a power series over a complete ultrametric
normed field, restricted at `r > 0` with lowest dominant degree `l` there. In any algebraically
closed complete normed field extension, the zeros of `f` in the open disc of radius `r`, counted
with multiplicity, number exactly `l`. -/
theorem IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq (hl : IsLowestDominant r l f)
    (hr : 0 < r) (hfr : f.IsRestricted r) : ((f.zeroMultiset r L).filter (‖·‖ < r)).card = l := by
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr hl.ne_zero
  obtain ⟨e, P, he, hP, hf⟩ :=
    hd.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) hr hfr
  exact hl.card_filter_zeroMultiset_norm_lt_eq_of_splits hd hr he hP hf (IsAlgClosed.splits _)

/-- **Exactly `d - l` zeros on the sphere.** Let `f` be a power series over a complete ultrametric
normed field, restricted at `r > 0`, distinguished of degree `d` and with lowest dominant degree
`l` there. In any algebraically closed complete normed field extension, the zeros `x` of `f` with
`‖x‖ = r`, counted with multiplicity, number exactly `d - l`. -/
theorem card_filter_zeroMultiset_norm_eq_eq (hd : IsDistinguished r d f)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (hfr : f.IsRestricted r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card = d - l := by
  obtain ⟨e, P, he, hP, hf⟩ :=
    hd.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hd.coeff_ne_zero) hr hfr
  exact card_filter_zeroMultiset_norm_eq_eq_of_splits hd hl hr he hP hf (IsAlgClosed.splits _)

end TauCeti.PowerSeries
