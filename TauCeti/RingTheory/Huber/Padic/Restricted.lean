/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.Huber.Restricted.Comparison

/-!
# Restricted power series over `ℤ_[p]`

The ring `ℤ_[p]⟨T₁, …, Tₙ⟩` of restricted power series over the `p`-adic integers — realised
either as the Gauss-normed subring `MvPowerSeries.IsRestricted.subring` at unit polyradius or as
the completed Huber algebra `TauCeti.Huber.restrictedMvPowerSeriesCompletion n ℤ_[p]` — is the
coordinate ring of formal affine `n`-space over `Spf ℤ_[p]`.

Unlike `ℚ_[p]⟨T₁, …, Tₙ⟩` (`TauCeti.RingTheory.Huber.Padic.TateAlgebra`), neither carrier is a
Tate ring: their topology is the `(p)`-adic topology of a proper ideal, so no unit is topologically
nilpotent. Both carriers are complete noetherian adic rings of finite ideal type (hence strongly
noetherian), and reducing modulo `p ^ m` gives the polynomial ring `(ZMod (p ^ m))[T₁, …, Tₙ]`
compatibility-preservingly across the Gauss comparison.

## Main definitions and instances

* `TauCeti.Huber.PadicInt.isAdicRing`: `ℤ_[p]` is an adic ring of finite ideal type.
* `TauCeti.Huber.PadicInt.quotientSpanPowIsRestrictedEquivMvPolynomialZMod`: the ring isomorphism
  `ℤ_[p]⟨T₁, …, Tₙ⟩ ⧸ (p ^ m) ≃+* (ZMod (p ^ m))[T₁, …, Tₙ]` on the Gauss-normed carrier.
* `TauCeti.Huber.PadicInt.quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod`: the
  corresponding ring isomorphism on `restrictedMvPowerSeriesCompletion n ℤ_[p]`.

## Main results

* `isAdic_span_p_isRestricted_subring` and `isAdic_span_p_restrictedMvPowerSeriesCompletion`: both
  carriers have the `(p)`-adic topology.
* `not_isTateRing_isRestricted_subring` and `not_isTateRing_restrictedMvPowerSeriesCompletion`:
  neither carrier is a Tate ring.
* `coeff_quotientSpanPowIsRestrictedEquivMvPolynomialZMod_mk` and
  `quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientEquiv`: reduction modulo `p ^ m`
  truncates each coefficient via `PadicInt.toZModPow m` and commutes with the Gauss comparison.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.1.
* T. Wedhorn, *Adic Spaces*, §§5.6 and 6.
-/

public section

namespace TauCeti.Huber.PadicInt

open IsLocalRing TauCeti.MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- **`ℤ_[p]` is an adic ring of finite ideal type**, with `(p)` as a finitely generated ideal of
definition. -/
instance isAdicRing : IsAdicRing ℤ_[p] :=
  ⟨maximalIdeal ℤ_[p],
    by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    isAdic_maximalIdeal,
    isAdic_maximalIdeal.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩

private theorem fg_maximalIdeal : (maximalIdeal ℤ_[p]).FG := by
  rw [_root_.PadicInt.maximalIdeal_eq_span_p]
  exact Submodule.fg_span_singleton _

private theorem map_maximalIdeal_eq_span_p {S : Type*} [CommRing S] (φ : ℤ_[p] →+* S) :
    (maximalIdeal ℤ_[p]).map φ = Ideal.span {(p : S)} := by
  rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

/-- The Gauss-normed restricted-series ring `ℤ_[p]⟨T₁, …, Tₙ⟩` carries the `(p)`-adic topology. -/
theorem isAdic_span_p_isRestricted_subring (n : ℕ) :
    IsAdic (Ideal.span {(p : MvPowerSeries.IsRestricted.subring (R := ℤ_[p])
      (fun _ : Fin n ↦ 1))}) := by
  rw [← map_maximalIdeal_eq_span_p (algebraMap ℤ_[p] _)]
  exact isAdic_map_algebraMap_isRestricted_subring n isAdic_maximalIdeal fg_maximalIdeal

/-- The completed Huber restricted-series ring over `ℤ_[p]` carries the `(p)`-adic topology. -/
theorem isAdic_span_p_restrictedMvPowerSeriesCompletion (n : ℕ) :
    IsAdic (Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p])}) := by
  rw [← map_maximalIdeal_eq_span_p (algebraMap ℤ_[p] _)]
  exact isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion n isAdic_maximalIdeal
    fg_maximalIdeal

/-- `ℤ_[p]⟨T₁, …, Tₙ⟩` is not a Tate ring: its topology is adic for the proper ideal `(p)`. -/
theorem not_isTateRing_isRestricted_subring (n : ℕ) :
    ¬ IsTateRing (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin n ↦ 1)) :=
  IsAdicRing.not_isTateRing

/-- The completed Huber restricted-series ring over `ℤ_[p]` is not a Tate ring. -/
theorem not_isTateRing_restrictedMvPowerSeriesCompletion (n : ℕ) :
    ¬ IsTateRing (restrictedMvPowerSeriesCompletion n ℤ_[p]) := by
  have : Nontrivial (restrictedMvPowerSeriesCompletion n ℤ_[p]) :=
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p])).toEquiv.nontrivial
  exact IsAdicRing.not_isTateRing

/-- **Reduction of `ℤ_[p]⟨T₁, …, Tₙ⟩` modulo `p ^ m` is `(ZMod (p ^ m))[T₁, …, Tₙ]`** on the
Gauss-normed carrier, for every `n, m : ℕ`. -/
noncomputable def quotientSpanPowIsRestrictedEquivMvPolynomialZMod (n m : ℕ) :
    (MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin n ↦ 1) ⧸
      Ideal.span {(p : MvPowerSeries.IsRestricted.subring (R := ℤ_[p])
        (fun _ : Fin n ↦ 1)) ^ m}) ≃+*
      MvPolynomial (Fin n) (ZMod (p ^ m)) :=
  have hS : Ideal.span {(p : MvPowerSeries.IsRestricted.subring (R := ℤ_[p])
        (fun _ : Fin n ↦ 1)) ^ m} =
      (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] _) ^ m := by
    rw [map_maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  have hR : maximalIdeal ℤ_[p] ^ m = Ideal.span {(p : ℤ_[p]) ^ m} := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  ((Ideal.quotEquivOfEq hS).trans
    (quotientIsRestrictedPowEquivMvPolynomialQuotient (k := n) isAdic_maximalIdeal
      fg_maximalIdeal m).toRingEquiv).trans
    (MvPolynomial.mapEquiv (Fin n)
      ((Ideal.quotEquivOfEq hR).trans (_root_.PadicInt.quotientSpanPowEquivZMod m)))

/-- Reducing a restricted series `f ∈ ℤ_[p]⟨T₁, …, Tₙ⟩` modulo `p ^ m` applies
`PadicInt.toZModPow m` to each coefficient. -/
@[simp]
theorem coeff_quotientSpanPowIsRestrictedEquivMvPolynomialZMod_mk (n m : ℕ)
    (f : MvPowerSeries.IsRestricted.subring (R := ℤ_[p]) (fun _ : Fin n ↦ 1))
    (ν : Fin n →₀ ℕ) :
    (quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m (Ideal.Quotient.mk _ f)).coeff ν =
      _root_.PadicInt.toZModPow m (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) ℤ_[p])) := by
  simp [quotientSpanPowIsRestrictedEquivMvPolynomialZMod, MvPolynomial.coeff_map]

/-- **Reduction of `restrictedMvPowerSeriesCompletion n ℤ_[p]` modulo `p ^ m` is
`(ZMod (p ^ m))[T₁, …, Tₙ]`**, for every `n, m : ℕ`. -/
noncomputable def quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod (n m : ℕ) :
    (restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) ≃+*
      MvPolynomial (Fin n) (ZMod (p ^ m)) :=
  have hS : Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m} =
      (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] _) ^ m := by
    rw [map_maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  have hR : maximalIdeal ℤ_[p] ^ m = Ideal.span {(p : ℤ_[p]) ^ m} := by
    rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
  ((Ideal.quotEquivOfEq hS).trans
    (quotientRestrictedCompletionPowEquivMvPolynomialQuotient (k := n) isAdic_maximalIdeal
      fg_maximalIdeal m).toRingEquiv).trans
    (MvPolynomial.mapEquiv (Fin n)
      ((Ideal.quotEquivOfEq hR).trans (_root_.PadicInt.quotientSpanPowEquivZMod m)))

/-- The `ZMod (p ^ m)`-polynomial quotient equivalences on the completed Huber and Gauss-normed
carriers agree across `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem quotientSpanPowIsRestrictedEquivMvPolynomialZMod_quotientEquiv (n m : ℕ)
    (q : restrictedMvPowerSeriesCompletion n ℤ_[p] ⧸
      Ideal.span {(p : restrictedMvPowerSeriesCompletion n ℤ_[p]) ^ m}) :
    quotientSpanPowIsRestrictedEquivMvPolynomialZMod n m
        (Ideal.quotientEquiv _ _
          (restrictedMvPowerSeriesCompletionGaussEquiv (n := n) (R := ℤ_[p]))
          (by rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]) q) =
      quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod n m q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [quotientSpanPowIsRestrictedEquivMvPolynomialZMod,
    quotientSpanPowRestrictedCompletionEquivMvPolynomialZMod]

end TauCeti.Huber.PadicInt
