/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.Huber.Restricted.Comparison.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Restricted power series over `ℤ_[p]`

The ring `ℤ_[p]⟨T₁, …, Tₙ⟩` of restricted power series over `ℤ_[p]` — realised either as
`MvPowerSeries.IsRestricted.subring` at unit polyradius or as
`TauCeti.Huber.restrictedMvPowerSeriesCompletion n ℤ_[p]` — is the coordinate ring of formal affine
`n`-space over `Spf ℤ_[p]`. Unlike `ℚ_[p]⟨T₁, …, Tₙ⟩`, neither carrier is a Tate ring: their
topology is `(p)`-adic, so both are complete noetherian adic rings of finite ideal type, and
reducing modulo `p ^ m` gives `(ZMod (p ^ m))[T₁, …, Tₙ]` compatibly across the Gauss comparison.

## Main definitions and results

* `TauCeti.Huber.PadicInt.quotientSpanPowIsRestrictedEquivMvPolynomialZMod` and
  `TauCeti.Huber.PadicInt.quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod`: the ring
  isomorphisms `ℤ_[p]⟨T₁, …, Tₙ⟩ ⧸ (p ^ m) ≃+* (ZMod (p ^ m))[T₁, …, Tₙ]` on both carriers.
* `isAdic_span_p_isRestricted_subring`, `isAdic_span_p_restrictedMvPowerSeriesCompletion`,
  `not_isTateRing_isRestricted_subring`, and `not_isTateRing_restrictedMvPowerSeriesCompletion`.
* `coeff_quotientSpanPowIsRestrictedEquivMvPolynomialZMod_mk`,
  `quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod_mk`, and
  `quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientEquiv`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1.
* T. Wedhorn, *Adic Spaces*, §§5.6 and 6.
-/

public section

namespace TauCeti.Huber.PadicInt

open IsLocalRing TauCeti.MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The Gauss-normed restricted-series ring `ℤ_[p]⟨T₁, …, Tₙ⟩` carries the `(p)`-adic topology. -/
theorem isAdic_span_p_isRestricted_subring (n : ℕ) :
    IsAdic (Ideal.span {(p : MvPowerSeries.IsRestricted.subring (R := ℤ_[p])
      (fun _ : Fin n ↦ 1))}) := by
  rw [← _root_.PadicInt.map_maximalIdeal_eq_span_p (algebraMap ℤ_[p] _)]
  exact isAdic_map_algebraMap_isRestricted_subring (k := n) isAdic_maximalIdeal
    (maximalIdeal ℤ_[p]).fg_of_isNoetherianRing

/-- The completed Huber restricted-series ring over `ℤ_[p]` carries the `(p)`-adic topology. -/
theorem isAdic_span_p_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsAdic (Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p])}) := by
  rw [← _root_.PadicInt.map_maximalIdeal_eq_span_p (algebraMap ℤ_[p] _)]
  exact isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion n isAdic_maximalIdeal
    (maximalIdeal ℤ_[p]).fg_of_isNoetherianRing

/-- `ℤ_[p]⟨T₁, …, Tₙ⟩` is not a Tate ring: its topology is adic for the proper ideal `(p)`. -/
theorem not_isTateRing_isRestricted_subring (n : ℕ) :
    ¬ IsTateRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin n ↦ 1)) :=
  IsAdicRing.not_isTateRing

/-- The completed Huber restricted-series ring over `ℤ_[p]` is not a Tate ring. -/
theorem not_isTateRing_restrictedMvPowerSeriesCompletion (n : ℕ) :
    ¬ IsTateRing (restrictedMvPowerSeriesCompletion n ℤ_[p]) :=
  have := (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p])).toEquiv.nontrivial
  IsAdicRing.not_isTateRing

private noncomputable def quotientMaximalIdealPowEquivZMod (m : ℕ) :
    (ℤ_[p] ⧸ maximalIdeal ℤ_[p] ^ m) ≃+* ZMod (p ^ m) :=
  (Ideal.quotEquivOfEq
    (by rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow])).trans
    (_root_.PadicInt.quotientSpanPowEquivZMod m)

/-- **Reduction of `ℤ_[p]⟨T₁, …, Tₙ⟩` modulo `p ^ m` is `(ZMod (p ^ m))[T₁, …, Tₙ]`** on the
Gauss-normed carrier. -/
noncomputable def quotientSpanPowIsRestrictedEquivMvPolynomialZMod (n m : ℕ) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin n ↦ 1) ⧸
      Ideal.span {(p : MvPowerSeries.IsRestricted.subring (R := ℤ_[p])
        (fun _ : Fin n ↦ 1)) ^ m}) ≃+* MvPolynomial (Fin n) (ZMod (p ^ m)) :=
  ((Ideal.quotEquivOfEq (by
      rw [_root_.PadicInt.map_maximalIdeal_eq_span_p, Ideal.span_singleton_pow])).trans
    (quotientIsRestrictedPowEquivMvPolynomialQuotient (k := n) isAdic_maximalIdeal
      (maximalIdeal ℤ_[p]).fg_of_isNoetherianRing m).toRingEquiv).trans
    (MvPolynomial.mapEquiv (Fin n) (quotientMaximalIdealPowEquivZMod m))

/-- Reducing `f ∈ ℤ_[p]⟨T₁, …, Tₙ⟩` modulo `p ^ m` applies `PadicInt.toZModPow m` to each
coefficient. -/
@[simp]
theorem coeff_quotientSpanPowIsRestrictedEquivMvPolynomialZMod_mk (n m : ℕ)
    (f : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin n ↦ 1))
    (ν : Fin n →₀ ℕ) :
    (quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m (Ideal.Quotient.mk _ f)).coeff ν =
      _root_.PadicInt.toZModPow m (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) ℤ_[p])) := by
  simp [quotientSpanPowIsRestrictedEquivMvPolynomialZMod, quotientMaximalIdealPowEquivZMod,
    MvPolynomial.coeff_map]

/-- **Reduction of `restrictedMvPowerSeriesCompletion n ℤ_[p]` modulo `p ^ m` is
`(ZMod (p ^ m))[T₁, …, Tₙ]`.** -/
noncomputable def quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod (n m : ℕ) :
    (restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) ≃+*
      MvPolynomial (Fin n) (ZMod (p ^ m)) :=
  ((Ideal.quotEquivOfEq (by
      rw [_root_.PadicInt.map_maximalIdeal_eq_span_p, Ideal.span_singleton_pow])).trans
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := n) isAdic_maximalIdeal
      (maximalIdeal ℤ_[p]).fg_of_isNoetherianRing m).toRingEquiv).trans
    (MvPolynomial.mapEquiv (Fin n) (quotientMaximalIdealPowEquivZMod m))

/-- Reducing `x ∈ restrictedMvPowerSeriesCompletion n ℤ_[p]` modulo `p ^ m` applies
`restrictedCompletionReduction` modulo `(p ^ m)` followed by `quotientSpanPowEquivZMod m`. -/
@[simp]
theorem quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod_mk (n m : ℕ)
    (x : restrictedMvPowerSeriesCompletion n ℤ_[p]) :
    quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod n m (Ideal.Quotient.mk _ x) =
      MvPolynomial.map (_root_.PadicInt.quotientSpanPowEquivZMod m).toRingHom
        ((Ideal.span {(p : ℤ_[p]) ^ m}).restrictedCompletionReduction
          (by simpa only [← Ideal.span_singleton_pow, ← _root_.PadicInt.maximalIdeal_eq_span_p]
            using isAdic_maximalIdeal.isOpen_pow m) x) := by
  have hR : maximalIdeal ℤ_[p] ^ m = Ideal.span {(p : ℤ_[p]) ^ m} := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  have hhom : (Ideal.quotEquivOfEq hR : _ →+* _) = Ideal.Quotient.factor (le_of_eq hR) := by
    ext q; simp
  simp only [quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod,
    quotientMaximalIdealPowEquivZMod, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    AlgEquiv.coe_toRingEquiv, quotientRestrictedCompletionPowEquivMvPolynomialQuotient_mk,
    MvPolynomial.mapEquiv_apply, RingEquiv.toRingHom_trans, ← MvPolynomial.map_map, hhom,
    RingEquiv.toRingHom_eq_coe]
  exact congrArg _ (map_restrictedCompletionReduction _ _ _ _)

/-- The `ZMod (p ^ m)`-polynomial quotient equivalences agree across `Ideal.quotientMap` of
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
@[simp]
theorem quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientMap (n m : ℕ)
    (h : Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m} ≤
      Ideal.comap (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p]) : _ →+* _)
        (Ideal.span {(p : MvPowerSeries.IsRestricted.subring (R := ℤ_[p])
          (fun _ : Fin n ↦ 1)) ^ m}))
    (q : restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) :
    quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m
        (Ideal.quotientMap _
          (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p]) : _ →+* _) h q) =
      quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod n m q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [quotientSpanPowIsRestrictedEquivMvPolynomialZMod,
    quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod]

/-- The `ZMod (p ^ m)`-polynomial quotient equivalences agree across
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientEquiv (n m : ℕ)
    (q : restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) :
    quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m
        (Ideal.quotientEquiv _ _
          (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p]))
          (by rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]) q) =
      quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod n m q := by
  simp

end TauCeti.Huber.PadicInt
