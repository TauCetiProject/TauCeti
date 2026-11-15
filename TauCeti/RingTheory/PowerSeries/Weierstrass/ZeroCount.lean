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
public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscPreparation
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann
import TauCeti.Algebra.Polynomial.Splits
import TauCeti.RingTheory.PowerSeries.Perturbation.Basic

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
counted with multiplicity, form a finite multiset, the zero multiset of `f` on that disc: whenever
`P` has degree at most the distinguished degree `d` of `f` at `r`, it is the multiset of roots of
`P` in `L`. Let `l` be the lowest dominant degree of `f` at `r` (the first index whose weighted
coefficient norm `‖aₙ‖ rⁿ` attains the Gauss norm, while `d` is the last). Then there are at most
`d` zeros in the closed disc and at most `l` in the open disc `‖x‖ < r`. If `P` splits over `L`, in
particular if `L` is algebraically closed, these are equalities, and there are exactly `d - l`
zeros on the sphere `‖x‖ = r`. All counts include the zero `x = 0`. For `ℂ_p` these are the exact
zero counts of `p`-adic analytic functions on closed and open discs.

The underlying set of `PowerSeries.zeroMultiset f r L` is `{x : L | ‖x‖ ≤ r ∧ f.evalAt x = 0}`, so
its extended cardinality is at most `(f.zeroMultiset r L).card`, with equality if and only if all
zeros of `f` in the closed disc are simple. Together with `IsDistinguished.card_zeroMultiset_le`
this refines Strassmann's distinct-zero bound
`TauCeti.PowerSeries.IsDistinguished.encard_setOf_evalAt_eq_zero_le`, and gives the corresponding
bounds on the open disc and sphere. Because a perturbation `g` with `‖f - g‖_r < ‖f‖_r` preserves
both `d` and `l`, it preserves the closed-disc, open-disc, and sphere zero counts with multiplicity
in any complete extension over which prepared or normalised disc polynomials of `f` and `g` split,
and unconditionally over any algebraically closed complete extension. At a radius on the boundary
of convergence these counts depend on the active indices `d` and `l` rather than the shape of the
Newton polygon alone.

## Main definitions

* `PowerSeries.zeroMultiset f r L`: the zeros of `f` in the closed disc `‖x‖ ≤ r` of `L`, each
  repeated as often as its multiplicity.

## Main results

* `TauCeti.PowerSeries.order_taylor_mul_eq_rootMultiplicity` and
  `TauCeti.PowerSeries.order_taylor_map_eq_rootMultiplicity`: on the closed disc, the multiplicity
  of a zero of `e * P` is its root multiplicity for `P`.
* `TauCeti.PowerSeries.IsDistinguished.zeroMultiset_eq_roots_map_of_isUnit_mul` and
  `TauCeti.PowerSeries.IsDistinguished.zeroMultiset_eq_roots_map`: the zero multiset is the
  multiset of roots in `L` of any polynomial factor `P` of degree at most `d` in `f = e * P`.
* `TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_eq_of_isUnit_mul`,
  `TauCeti.PowerSeries.IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul`: if `P` splits over `L`,
  there are `d` zeros in the closed disc, `l` in the open disc, and `d - l` on the sphere.
* `TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul`,
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_isUnit_mul` and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_isUnit_mul`:
  perturbation invariance of all three counts when prepared polynomial factors split over `L`
  (with `IsDiscPreparation` specialisations and unconditional `IsAlgClosed` Rouché theorems
  `TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt`,
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt`, and
  `TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt`).
* `PowerSeries.IsRestricted.setOf_norm_le_and_evalAt_eq_zero`,
  `PowerSeries.IsRestricted.encard_setOf_norm_le_and_evalAt_eq_zero_le_card_zeroMultiset` and
  `PowerSeries.IsRestricted.encard_setOf_norm_le_and_evalAt_eq_zero_eq_card_zeroMultiset_iff`:
  comparison between distinct zeros and the zero multiset on closed discs, open discs, and spheres.
* `TauCeti.PowerSeries.IsDiscPreparation.zeroMultiset_eq_roots_map`,
  `TauCeti.PowerSeries.IsDiscPreparation.map_eq_prod_zeroMultiset`,
  `TauCeti.PowerSeries.IsDiscPreparation.eq_prod_zeroMultiset` and
  `PowerSeries.IsRestricted.exists_isDiscPreparation_prod_zeroMultiset`: zero multisets and root
  products for normalised disc preparations.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1 and 3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §4.
* R. Strassmann, *Über den Wertevorrat von Potenzreihen im Gebiet der p-adischen Zahlen*,
  J. Reine Angew. Math. 159 (1928), 13–28.
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
  exact (hl.map_polynomial hr he hf).card_filter_roots_norm_lt_le

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
  exact (hd.map_polynomial hr he hf).card_filter_roots_norm_le_le

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

/-- The roots in `L` of a prepared polynomial factor of `f` of degree at most `d` lie in the closed
disc, and they are the zeros of `f` there, with their multiplicities. -/
private theorem roots_map_spec [DecidableEq L] (hd : IsDistinguished r d f) (hr : 0 < r)
    (he : IsUnit e) (hPdeg : P.natDegree ≤ d) (hf : (e : PowerSeries K) * P = f) :
    (∀ z ∈ (P.map (algebraMap K L)).roots, ‖z‖ ≤ r) ∧
      ∀ x : L, ‖x‖ ≤ r →
        (_root_.PowerSeries.taylor x (_root_.PowerSeries.map (algebraMap K L) f)).order =
          (P.map (algebraMap K L)).roots.count x := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hd.ne_zero (by simpa using hf.symm)
  obtain ⟨e', he', hmap⟩ := map_eq_restrictedMap_mul (L := L) hf
  refine ⟨fun z hz ↦ (hd.map (algebraMap K L) (norm_algebraMap' L)
    ).norm_le_of_mem_roots_of_isUnit_mul hr (he' he)
      (Polynomial.natDegree_map_le.trans hPdeg) hmap.symm hz, fun x hx ↦ ?_⟩
  rw [order_taylor_map_eq_rootMultiplicity he hP0 hf hx, Polynomial.count_roots]

/-- **The zero multiset is the root multiset.** Let `f = e * P` over an ultrametric normed field,
with `e` a unit of the ring of series restricted at `r > 0` and `P` a polynomial of degree at most
the distinguished degree `d` of `f` at `r`. In any complete normed field extension `L`, the zero
multiset of `f` on the closed disc of radius `r` is the multiset of roots of `P` in `L`. -/
theorem IsDistinguished.zeroMultiset_eq_roots_map_of_isUnit_mul (hd : IsDistinguished r d f)
    (hr : 0 < r) (he : IsUnit e) (hPdeg : P.natDegree ≤ d) (hf : (e : PowerSeries K) * P = f) :
    f.zeroMultiset r L = (P.map (algebraMap K L)).roots := by
  classical
  obtain ⟨hroots, hcount⟩ := roots_map_spec (L := L) hd hr he hPdeg hf
  exact _root_.PowerSeries.zeroMultiset_eq_of_order_taylor_eq hroots hcount

/-- **The zero multiset is the root multiset, monic case.** Let `f = e * P` over an ultrametric
normed field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`. In any complete normed field extension `L`, the zero
multiset of `f` on the closed disc of radius `r` is the multiset of roots of `P` in `L`. -/
theorem IsDistinguished.zeroMultiset_eq_roots_map (hd : IsDistinguished r d f) (hr : 0 < r)
    (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f) :
    f.zeroMultiset r L = (P.map (algebraMap K L)).roots :=
  hd.zeroMultiset_eq_roots_map_of_isUnit_mul hr he hP.natDegree_eq.le hf

/-- **Exactly `d` zeros in the closed disc, split case.** Let `f = e * P` over an ultrametric
normed field, with `e` a unit of the ring of series restricted at `r > 0` and `P` a polynomial of
degree at most the distinguished degree `d` of `f` at `r`. In any complete normed field extension
over which `P` splits, the zeros of `f` in the closed disc of radius `r`, counted with
multiplicity, number exactly `d`. -/
theorem IsDistinguished.card_zeroMultiset_eq_of_isUnit_mul (hd : IsDistinguished r d f)
    (hr : 0 < r) (he : IsUnit e) (hPdeg : P.natDegree ≤ d) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) : (f.zeroMultiset r L).card = d := by
  rw [hd.zeroMultiset_eq_roots_map_of_isUnit_mul hr he hPdeg hf,
    Polynomial.splits_iff_card_roots.mp hs,
    Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective,
    natDegree_eq_of_isUnit_mul hr hd he hPdeg hf]

/-- **Exactly `d` zeros in the closed disc, monic split case.** Let `f = e * P` over an ultrametric
normed field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`. In any complete normed field extension over which `P`
splits, the zeros of `f` in the closed disc of radius `r`, counted with multiplicity, number
exactly `d`. -/
theorem IsDistinguished.card_zeroMultiset_eq_of_splits (hd : IsDistinguished r d f)
    (hr : 0 < r) (he : IsUnit e) (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) : (f.zeroMultiset r L).card = d :=
  hd.card_zeroMultiset_eq_of_isUnit_mul hr he hP.natDegree_eq.le hf hs

/-- **Exactly `l` zeros in the open disc, split case.** Let `f = e * P` over an ultrametric normed
field, with `e` a unit of the ring of series restricted at `r > 0` and `P` a polynomial of degree
at most the distinguished degree `d` of `f` at `r`, and let `l` be the lowest dominant degree of
`f` at `r`. In any complete normed field extension over which `P` splits, the zeros of `f` in the
open disc of radius `r`, counted with multiplicity, number exactly `l`. -/
theorem IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul
    (hl : IsLowestDominant r l f) (hd : IsDistinguished r d f) (hr : 0 < r) (he : IsUnit e)
    (hPdeg : P.natDegree ≤ d) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card = l := by
  rw [hd.zeroMultiset_eq_roots_map_of_isUnit_mul hr he hPdeg hf]
  exact hl.card_filter_roots_map_norm_lt_eq hr he hf hs

/-- **Exactly `l` zeros in the open disc, monic split case.** Let `f = e * P` over an ultrametric
normed field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`, and let `l` be the lowest dominant degree of `f` at `r`. In
any complete normed field extension over which `P` splits, the zeros of `f` in the open disc of
radius `r`, counted with multiplicity, number exactly `l`. -/
theorem IsLowestDominant.card_filter_zeroMultiset_norm_lt_eq_of_splits
    (hl : IsLowestDominant r l f) (hd : IsDistinguished r d f) (hr : 0 < r) (he : IsUnit e)
    (hP : P.IsMonicOfDegree d) (hf : (e : PowerSeries K) * P = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card = l :=
  hl.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul hd hr he hP.natDegree_eq.le hf hs

/-- **Exactly `d - l` zeros on the sphere, split case.** Let `f = e * P` over an ultrametric normed
field, with `e` a unit of the ring of series restricted at `r > 0` and `P` a polynomial of degree
at most the distinguished degree `d` of `f` at `r`, and let `l` be the lowest dominant degree of
`f` at `r`. In any complete normed field extension over which `P` splits, the zeros `x` of `f` with
`‖x‖ = r`, counted with multiplicity, number exactly `d - l`. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul (hd : IsDistinguished r d f)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (he : IsUnit e) (hPdeg : P.natDegree ≤ d)
    (hf : (e : PowerSeries K) * P = f) (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card = d - l := by
  rw [hd.zeroMultiset_eq_roots_map_of_isUnit_mul hr he hPdeg hf]
  exact card_filter_roots_map_norm_eq_eq hd hl hr he hf hs

/-- **Exactly `d - l` zeros on the sphere, monic split case.** Let `f = e * P` over an ultrametric
normed field, with `e` a unit of the ring of series restricted at `r > 0` and `P` monic of the
distinguished degree `d` of `f` at `r`, and let `l` be the lowest dominant degree of `f` at `r`. In
any complete normed field extension over which `P` splits, the zeros `x` of `f` with `‖x‖ = r`,
counted with multiplicity, number exactly `d - l`. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_splits (hd : IsDistinguished r d f)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (he : IsUnit e) (hP : P.IsMonicOfDegree d)
    (hf : (e : PowerSeries K) * P = f) (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card = d - l :=
  card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul hd hl hr he hP.natDegree_eq.le hf hs

/-- **Perturbation invariance of the closed-disc zero count, split case.** Suppose `f = e * P` and
`g = e' * Q` on the closed disc of radius `r > 0`, with `e` and `e'` restricted units and `P` and
`Q` polynomials of degrees at most the distinguished degrees of `f` and `g` at `r`. If both `P` and
`Q` split over a complete normed extension `L` and `‖f - g‖_r < ‖f‖_r`, then `f` and `g` have the
same number of zeros in the closed disc of radius `r`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul
    {g : PowerSeries K} {dg : ℕ} {e' : PowerSeries.IsRestricted.subring (R := K) r}
    {Q : Polynomial K} (hr : 0 < r)
    (hd : IsDistinguished r d f) (he : IsUnit e) (hPdeg : P.natDegree ≤ d)
    (hf : (e : PowerSeries K) * P = f) (hs : (P.map (algebraMap K L)).Splits)
    (hdg : IsDistinguished r dg g) (he' : IsUnit e') (hQdeg : Q.natDegree ≤ dg)
    (hg : (e' : PowerSeries K) * Q = g) (hQs : (Q.map (algebraMap K L)).Splits)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  have hd' := (isDistinguished_iff_of_gaussNorm_sub_lt hr.le hd.hasGaussNorm hdg.hasGaussNorm
    hfg).mp hd
  rw [hd.card_zeroMultiset_eq_of_isUnit_mul hr he hPdeg hf hs,
    hdg.card_zeroMultiset_eq_of_isUnit_mul hr he' hQdeg hg hQs, hd'.unique hdg]

/-- **Perturbation invariance of the open-disc zero count, split case.** Under the hypotheses of
`TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul`, `f` and `g` have the
same number of zeros in the open disc `‖x‖ < r` of `L`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_isUnit_mul
    {g : PowerSeries K} {dg : ℕ} {e' : PowerSeries.IsRestricted.subring (R := K) r}
    {Q : Polynomial K} (hr : 0 < r)
    (hd : IsDistinguished r d f) (he : IsUnit e) (hPdeg : P.natDegree ≤ d)
    (hf : (e : PowerSeries K) * P = f) (hs : (P.map (algebraMap K L)).Splits)
    (hdg : IsDistinguished r dg g) (he' : IsUnit e') (hQdeg : Q.natDegree ≤ dg)
    (hg : (e' : PowerSeries K) * Q = g) (hQs : (Q.map (algebraMap K L)).Splits)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  have hfr : f.IsRestricted r := by
    rw [← hf]
    exact (PowerSeries.IsRestricted.subring r).mul_mem e.2 (isRestricted_polynomial P)
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr hfr hd.ne_zero
  have hlg := (isLowestDominant_iff_of_gaussNorm_sub_lt hr.le hd.hasGaussNorm hdg.hasGaussNorm
    hfg).mp hl
  rw [hl.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul hd hr he hPdeg hf hs,
    hlg.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul hdg hr he' hQdeg hg hQs]

/-- **Perturbation invariance of the sphere zero count, split case.** Under the hypotheses of
`TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul`, `f` and `g` have the
same number of zeros on the sphere `‖x‖ = r` of `L`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_isUnit_mul
    {g : PowerSeries K} {dg : ℕ} {e' : PowerSeries.IsRestricted.subring (R := K) r}
    {Q : Polynomial K} (hr : 0 < r)
    (hd : IsDistinguished r d f) (he : IsUnit e) (hPdeg : P.natDegree ≤ d)
    (hf : (e : PowerSeries K) * P = f) (hs : (P.map (algebraMap K L)).Splits)
    (hdg : IsDistinguished r dg g) (he' : IsUnit e') (hQdeg : Q.natDegree ≤ dg)
    (hg : (e' : PowerSeries K) * Q = g) (hQs : (Q.map (algebraMap K L)).Splits)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  have hfr : f.IsRestricted r := by
    rw [← hf]
    exact (PowerSeries.IsRestricted.subring r).mul_mem e.2 (isRestricted_polynomial P)
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr hfr hd.ne_zero
  have hd' := (isDistinguished_iff_of_gaussNorm_sub_lt hr.le hd.hasGaussNorm hdg.hasGaussNorm
    hfg).mp hd
  have hlg := (isLowestDominant_iff_of_gaussNorm_sub_lt hr.le hd.hasGaussNorm hdg.hasGaussNorm
    hfg).mp hl
  rw [card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul hd hl hr he hPdeg hf hs,
    card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul hdg hlg hr he' hQdeg hg hQs, hd'.unique hdg]

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
  exact (roots_map_spec hd hr he hP.natDegree_eq.le hf).2 x hx

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

/-- **Distinct zeros in the closed disc.** For a nonzero series `f` restricted at `r > 0`, the set
of zeros of `f` in the closed disc `‖x‖ ≤ r` of `L` is the underlying finite set of
`f.zeroMultiset r L`. -/
theorem _root_.PowerSeries.IsRestricted.setOf_norm_le_and_evalAt_eq_zero [DecidableEq L]
    (hfr : f.IsRestricted r) (hr : 0 < r) (hf0 : f ≠ 0) :
    {x : L | ‖x‖ ≤ r ∧ f.evalAt x = 0} = (f.zeroMultiset r L).toFinset := by
  ext x
  simp [hfr.mem_zeroMultiset_iff hr hf0]

/-- **Comparison with Strassmann's distinct-zero count on the closed disc.** For a nonzero series
`f` restricted at `r > 0`, the number of distinct zeros of `f` in the closed disc `‖x‖ ≤ r` of `L`
is at most the cardinality of `f.zeroMultiset r L`. Together with
`TauCeti.PowerSeries.IsDistinguished.card_zeroMultiset_le` this refines Strassmann's bound
`TauCeti.PowerSeries.IsDistinguished.encard_setOf_evalAt_eq_zero_le`. -/
theorem _root_.PowerSeries.IsRestricted.encard_setOf_norm_le_and_evalAt_eq_zero_le_card_zeroMultiset
    (hfr : f.IsRestricted r) (hr : 0 < r) (hf0 : f ≠ 0) :
    {x : L | ‖x‖ ≤ r ∧ f.evalAt x = 0}.encard ≤ (f.zeroMultiset r L).card := by
  classical
  rw [hfr.setOf_norm_le_and_evalAt_eq_zero hr hf0, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  exact Multiset.toFinset_card_le _

/-- **Distinct-zero and multiplicity counts agree when all zeros are simple.** For a nonzero series
`f` restricted at `r > 0`, the number of distinct zeros of `f` in the closed disc `‖x‖ ≤ r` of `L`
equals `(f.zeroMultiset r L).card` if and only if `f.zeroMultiset r L` has no repeated elements. -/
theorem
    _root_.PowerSeries.IsRestricted.encard_setOf_norm_le_and_evalAt_eq_zero_eq_card_zeroMultiset_iff
    (hfr : f.IsRestricted r) (hr : 0 < r) (hf0 : f ≠ 0) :
    {x : L | ‖x‖ ≤ r ∧ f.evalAt x = 0}.encard = (f.zeroMultiset r L).card ↔
      (f.zeroMultiset r L).Nodup := by
  classical
  rw [hfr.setOf_norm_le_and_evalAt_eq_zero hr hf0, Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj,
    Multiset.toFinset_card_eq_card_iff_nodup]

/-- **Distinct zeros in the open disc.** For a nonzero series `f` restricted at `r > 0`, the number
of distinct zeros of `f` in the open disc `‖x‖ < r` of `L` is at most the open-disc multiplicity
count `((f.zeroMultiset r L).filter (‖·‖ < r)).card`. -/
theorem _root_.PowerSeries.IsRestricted.encard_setOf_norm_lt_and_evalAt_eq_zero_le
    (hfr : f.IsRestricted r) (hr : 0 < r) (hf0 : f ≠ 0) :
    {x : L | ‖x‖ < r ∧ f.evalAt x = 0}.encard ≤
      ((f.zeroMultiset r L).filter (‖·‖ < r)).card := by
  classical
  have hset : {x : L | ‖x‖ < r ∧ f.evalAt x = 0} =
      ((f.zeroMultiset r L).filter (‖·‖ < r)).toFinset := by
    ext x
    simp only [Set.mem_ofPred, Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_filter,
      hfr.mem_zeroMultiset_iff hr hf0, _root_.PowerSeries.evalAt_map_algebraMap]
    exact ⟨fun ⟨hx, h0⟩ ↦ ⟨⟨hx.le, h0⟩, hx⟩, fun ⟨⟨_, h0⟩, hx⟩ ↦ ⟨hx, h0⟩⟩
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  exact Multiset.toFinset_card_le _

/-- **Distinct zeros on the sphere.** For a nonzero series `f` restricted at `r > 0`, the number of
distinct zeros of `f` on the sphere `‖x‖ = r` of `L` is at most the sphere multiplicity count
`((f.zeroMultiset r L).filter (‖·‖ = r)).card`. -/
theorem _root_.PowerSeries.IsRestricted.encard_setOf_norm_eq_and_evalAt_eq_zero_le
    (hfr : f.IsRestricted r) (hr : 0 < r) (hf0 : f ≠ 0) :
    {x : L | ‖x‖ = r ∧ f.evalAt x = 0}.encard ≤
      ((f.zeroMultiset r L).filter (‖·‖ = r)).card := by
  classical
  have hset : {x : L | ‖x‖ = r ∧ f.evalAt x = 0} =
      ((f.zeroMultiset r L).filter (‖·‖ = r)).toFinset := by
    ext x
    simp only [Set.mem_ofPred, Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_filter,
      hfr.mem_zeroMultiset_iff hr hf0, _root_.PowerSeries.evalAt_map_algebraMap]
    exact ⟨fun ⟨hx, h0⟩ ↦ ⟨⟨hx.le, h0⟩, hx⟩, fun ⟨⟨_, h0⟩, hx⟩ ↦ ⟨hx, h0⟩⟩
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  exact Multiset.toFinset_card_le _

/-- **Nested zero multisets.** Let `f` be a nonzero power series over a complete ultrametric normed
field `K`, restricted at `s > 0`. In any complete normed field extension `L`, for `r ≤ s` the zero
multiset of `f` on the closed disc of radius `r` consists of the points of norm at most `r` of its
zero multiset on the closed disc of radius `s`. -/
theorem _root_.PowerSeries.IsRestricted.filter_zeroMultiset_eq {s : ℝ} (hfs : f.IsRestricted s)
    (hs : 0 < s) (hf0 : f ≠ 0) (hrs : r ≤ s) :
    (f.zeroMultiset s L).filter (‖·‖ ≤ r) = f.zeroMultiset r L := by
  classical
  refine (_root_.PowerSeries.zeroMultiset_eq_of_order_taylor_eq
    (fun z hz ↦ (Multiset.mem_filter.mp hz).2) fun x hx ↦ ?_).symm
  rw [Multiset.count_filter_of_pos (p := (‖·‖ ≤ r)) hx,
    hfs.order_taylor_eq_count_zeroMultiset hs hf0 (hx.trans hrs)]

namespace IsDiscPreparation

variable {U : PowerSeries K}

/-- **The zero multiset of a normalised disc preparation.** If `f = P * U` is the normalised
preparation of `f` on the closed disc of radius `r > 0` over a complete ultrametric normed field
`K`, then in any complete normed field extension `L` the zero multiset of `f` on that disc is the
multiset of roots of `P` in `L`. -/
theorem zeroMultiset_eq_roots_map (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    f.zeroMultiset r L = (P.map (algebraMap K L)).roots :=
  h.isDistinguished.zeroMultiset_eq_roots_map_of_isUnit_mul hr (h.isUnit hr) h.natDegree_eq.le
    (mul_comm (U : PowerSeries K) P ▸ h.eq_mul.symm)

/-- **Closed-disc zero count for a split disc polynomial.** If `f = P * U` is the normalised
preparation of `f` on the closed disc of radius `r > 0` and `P` splits over `L`, then `f` has
exactly `d` zeros in the closed disc of `L`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_splits (h : IsDiscPreparation r d f P U) (hr : 0 < r)
    (hs : (P.map (algebraMap K L)).Splits) : (f.zeroMultiset r L).card = d :=
  h.isDistinguished.card_zeroMultiset_eq_of_isUnit_mul hr (h.isUnit hr) h.natDegree_eq.le
    (mul_comm (U : PowerSeries K) P ▸ h.eq_mul.symm) hs

/-- **Open-disc zero count for a split disc polynomial.** If `f = P * U` is the normalised
preparation of `f` on the closed disc of radius `r > 0`, `l` is the lowest dominant degree of `f`
at `r`, and `P` splits over `L`, then `f` has exactly `l` zeros in the open disc `‖x‖ < r` of `L`,
counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_splits (h : IsDiscPreparation r d f P U)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card = l :=
  hl.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul h.isDistinguished hr (h.isUnit hr)
    h.natDegree_eq.le (mul_comm (U : PowerSeries K) P ▸ h.eq_mul.symm) hs

/-- **Sphere zero count for a split disc polynomial.** If `f = P * U` is the normalised preparation
of `f` on the closed disc of radius `r > 0`, `l` is the lowest dominant degree of `f` at `r`, and
`P` splits over `L`, then `f` has exactly `d - l` zeros on the sphere `‖x‖ = r` of `L`, counted
with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_splits (h : IsDiscPreparation r d f P U)
    (hl : IsLowestDominant r l f) (hr : 0 < r) (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card = d - l :=
  card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul h.isDistinguished hl hr (h.isUnit hr)
    h.natDegree_eq.le (mul_comm (U : PowerSeries K) P ▸ h.eq_mul.symm) hs

/-- **Perturbation invariance of closed-disc zero counts for split disc polynomials.** If `f` and
`g` admit normalised disc preparations at `r > 0` whose polynomial factors both split over `L`, and
`‖f - g‖_r < ‖f‖_r`, then `f` and `g` have the same closed-disc zero count in `L`. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt {g V : PowerSeries K} {dg : ℕ}
    {Q : Polynomial K} (hfP : IsDiscPreparation r d f P U) (hgQ : IsDiscPreparation r dg g Q V)
    (hr : 0 < r) (hs : (P.map (algebraMap K L)).Splits) (hQs : (Q.map (algebraMap K L)).Splits)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card :=
  card_zeroMultiset_eq_of_gaussNorm_sub_lt_of_isUnit_mul hr hfP.isDistinguished (hfP.isUnit hr)
    hfP.natDegree_eq.le (mul_comm (U : PowerSeries K) P ▸ hfP.eq_mul.symm) hs hgQ.isDistinguished
    (hgQ.isUnit hr) hgQ.natDegree_eq.le (mul_comm (V : PowerSeries K) Q ▸ hgQ.eq_mul.symm) hQs hfg

/-- **Perturbation invariance of open-disc zero counts for split disc polynomials.** Under the
hypotheses of `TauCeti.PowerSeries.IsDiscPreparation.card_zeroMultiset_eq_of_gaussNorm_sub_lt`, `f`
and `g` have the same open-disc zero count in `L`. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt {g V : PowerSeries K} {dg : ℕ}
    {Q : Polynomial K} (hfP : IsDiscPreparation r d f P U) (hgQ : IsDiscPreparation r dg g Q V)
    (hr : 0 < r) (hs : (P.map (algebraMap K L)).Splits) (hQs : (Q.map (algebraMap K L)).Splits)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card :=
  card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt_of_isUnit_mul hr hfP.isDistinguished
    (hfP.isUnit hr) hfP.natDegree_eq.le (mul_comm (U : PowerSeries K) P ▸ hfP.eq_mul.symm) hs
    hgQ.isDistinguished (hgQ.isUnit hr) hgQ.natDegree_eq.le
    (mul_comm (V : PowerSeries K) Q ▸ hgQ.eq_mul.symm) hQs hfg

/-- **Perturbation invariance of sphere zero counts for split disc polynomials.** Under the
hypotheses of `TauCeti.PowerSeries.IsDiscPreparation.card_zeroMultiset_eq_of_gaussNorm_sub_lt`, `f`
and `g` have the same sphere zero count in `L`. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt {g V : PowerSeries K} {dg : ℕ}
    {Q : Polynomial K} (hfP : IsDiscPreparation r d f P U) (hgQ : IsDiscPreparation r dg g Q V)
    (hr : 0 < r) (hs : (P.map (algebraMap K L)).Splits) (hQs : (Q.map (algebraMap K L)).Splits)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card :=
  card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt_of_isUnit_mul hr hfP.isDistinguished
    (hfP.isUnit hr) hfP.natDegree_eq.le (mul_comm (U : PowerSeries K) P ▸ hfP.eq_mul.symm) hs
    hgQ.isDistinguished (hgQ.isUnit hr) hgQ.natDegree_eq.le
    (mul_comm (V : PowerSeries K) Q ▸ hgQ.eq_mul.symm) hQs hfg

/-- **The disc polynomial is the product over the zeros.** If `f = P * U` is the normalised
preparation of `f` on the closed disc of radius `r > 0` over a complete ultrametric normed field
`K`, and `P` splits over a complete normed field extension `L`, then `P` is the product of the
factors `1 - α⁻¹ X` over the zeros `α` of `f` in the closed disc of `L`, counted with
multiplicity. -/
theorem map_eq_prod_zeroMultiset (h : IsDiscPreparation r d f P U) (hr : 0 < r)
    (hs : (P.map (algebraMap K L)).Splits) :
    P.map (algebraMap K L) =
      ((f.zeroMultiset r L).map fun α ↦ 1 - Polynomial.C α⁻¹ * Polynomial.X).prod := by
  rw [h.zeroMultiset_eq_roots_map hr]
  exact hs.eq_prod_roots_of_coeff_zero_eq_one
    (by rw [Polynomial.coeff_map, h.coeff_zero_eq_one, map_one])

end IsDiscPreparation

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

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem ne_zero_of_gaussNorm_sub_lt {g : PowerSeries K}
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) : f ≠ 0 := by
  intro hf0
  have h0 := (_root_.PowerSeries.gaussNorm_nonneg (R := K) norm r (f - g) norm_nonneg).trans_lt hfg
  rw [hf0, _root_.PowerSeries.gaussNorm_zero (R := K) norm r norm_zero] at h0
  exact lt_irrefl 0 h0

/-- **Nonarchimedean Rouché theorem on the closed disc.** Let `f` and `g` be power series over a
complete ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any
algebraically closed complete normed field extension `L`, `f` and `g` have the same number of zeros
in the closed disc `‖x‖ ≤ r`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_gaussNorm_sub_lt {g : PowerSeries K} (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    (f.zeroMultiset r L).card = (g.zeroMultiset r L).card := by
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr (ne_zero_of_gaussNorm_sub_lt hfg)
  have hdg := (isDistinguished_iff_of_gaussNorm_sub_lt (R := K) hr.le
    (hasGaussNorm_of_isRestricted (R := K) hfr) (hasGaussNorm_of_isRestricted (R := K) hgr)
    hfg).mp hd
  rw [hd.card_zeroMultiset_eq hr hfr, hdg.card_zeroMultiset_eq hr hgr]

/-- **Nonarchimedean Rouché theorem on the open disc.** Let `f` and `g` be power series over a
complete ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any
algebraically closed complete normed field extension `L`, `f` and `g` have the same number of zeros
in the open disc `‖x‖ < r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_gaussNorm_sub_lt {g : PowerSeries K} (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ < r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ < r)).card := by
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr hfr (ne_zero_of_gaussNorm_sub_lt hfg)
  have hlg := (isLowestDominant_iff_of_gaussNorm_sub_lt (R := K) hr.le
    (hasGaussNorm_of_isRestricted (R := K) hfr) (hasGaussNorm_of_isRestricted (R := K) hgr)
    hfg).mp hl
  rw [hl.card_filter_zeroMultiset_norm_lt_eq hr hfr, hlg.card_filter_zeroMultiset_norm_lt_eq hr hgr]

/-- **Nonarchimedean Rouché theorem on the sphere.** Let `f` and `g` be power series over a
complete ultrametric normed field, restricted at `r > 0`, with `‖f - g‖_r < ‖f‖_r`. In any
algebraically closed complete normed field extension `L`, `f` and `g` have the same number of zeros
on the sphere `‖x‖ = r`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_eq_eq_of_gaussNorm_sub_lt {g : PowerSeries K} (hr : 0 < r)
    (hfr : f.IsRestricted r) (hgr : g.IsRestricted r)
    (hfg : (f - g).gaussNorm norm r < f.gaussNorm norm r) :
    ((f.zeroMultiset r L).filter (‖·‖ = r)).card =
      ((g.zeroMultiset r L).filter (‖·‖ = r)).card := by
  have hf0 := ne_zero_of_gaussNorm_sub_lt hfg
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr hf0
  obtain ⟨l, hl⟩ := exists_isLowestDominant hr hfr hf0
  have hdg := (isDistinguished_iff_of_gaussNorm_sub_lt (R := K) hr.le
    (hasGaussNorm_of_isRestricted (R := K) hfr) (hasGaussNorm_of_isRestricted (R := K) hgr)
    hfg).mp hd
  have hlg := (isLowestDominant_iff_of_gaussNorm_sub_lt (R := K) hr.le
    (hasGaussNorm_of_isRestricted (R := K) hfr) (hasGaussNorm_of_isRestricted (R := K) hgr)
    hfg).mp hl
  rw [card_filter_zeroMultiset_norm_eq_eq hd hl hr hfr,
    card_filter_zeroMultiset_norm_eq_eq hdg hlg hr hgr]

/-- **The disc polynomial over an algebraically closed field.** If `f = P * U` is the normalised
preparation of `f` on the closed disc of radius `r > 0` over an algebraically closed complete
ultrametric normed field `K`, then `P` is the product of the factors `1 - α⁻¹ X` over the zeros
`α` of `f` in that disc, counted with multiplicity. -/
theorem IsDiscPreparation.eq_prod_zeroMultiset [IsAlgClosed K] {U : PowerSeries K}
    (h : IsDiscPreparation r d f P U) (hr : 0 < r) :
    P = ((f.zeroMultiset r K).map fun α ↦ 1 - Polynomial.C α⁻¹ * Polynomial.X).prod := by
  simpa using h.map_eq_prod_zeroMultiset (L := K) hr (IsAlgClosed.splits _)

/-- **Normalised disc preparation by the zeros.** Let `f` be a power series with constant
coefficient `1` over an algebraically closed complete ultrametric normed field `K`, restricted at
`r > 0`. Then the product of the factors `1 - α⁻¹ X` over the zeros `α` of `f` in the closed disc
of radius `r`, counted with multiplicity, is the polynomial factor of the normalised preparation
of `f` on that disc. -/
theorem _root_.PowerSeries.IsRestricted.exists_isDiscPreparation_prod_zeroMultiset [IsAlgClosed K]
    (hfr : f.IsRestricted r) (hr : 0 < r) (h0 : _root_.PowerSeries.constantCoeff f = 1) :
    ∃ (d : ℕ) (U : PowerSeries K), IsDiscPreparation r d f
      ((f.zeroMultiset r K).map fun α ↦ 1 - Polynomial.C α⁻¹ * Polynomial.X).prod U := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h0
  obtain ⟨d, hd⟩ := exists_isDistinguished hr hfr hf0
  obtain ⟨P, U, h⟩ := hd.exists_isDiscPreparation hr hfr h0
  exact ⟨d, U, h.eq_prod_zeroMultiset hr ▸ h⟩

end TauCeti.PowerSeries
