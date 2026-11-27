/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.VerticalGeneralization
import TauCeti.RingTheory.Valuation.Composite
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Points of the valuation spectrum with prescribed support and centre

A point `v` of `Spv R` that is bounded by `1` on all of `R` has two prime ideals attached to it:
its support `{r : v(r) = 0}` and its centre `{r : v(r) < 1}`, and the support lies inside the
centre. This file shows that every such pair arises: for prime ideals `𝔮 ⊆ 𝔭` of a commutative
ring `R` there is a point of `Spv R`, bounded by `1` on `R`, with support `𝔮` and centre `𝔭`
(`TauCeti.ValuationSpectrum.exists_supp_eq_and_valuation_lt_one_iff_mem`).

The centre can also be enlarged by specializing. Let `φ : R →+* A` and let `x` be a point of
`Spv A` bounded by `1` on `φ(R)`. Every prime `𝔭` of `R` containing the centre
`{r : x(φ r) < 1}` is the centre of a specialization of `x` with the same support, again bounded
by `1` on `φ(R)`
(`TauCeti.ValuationSpectrum.exists_specializes_supp_eq_and_valuation_lt_one_iff_mem`).

Both points are classical. For the first, the localisation of the domain `R ⧸ 𝔮` at the image of
`𝔭` is a local subring of the fraction field of `R ⧸ 𝔮`, and the valuation of a valuation subring
dominating it (`RingHom.exists_valuationSubring_mem_and_mem_nonunits_iff`), pulled back to `R`, is
bounded by `1`, vanishes exactly on `𝔮` and is below `1` exactly on `𝔭`. For the second, `x` is
the pullback of the valuation subring `O` of its residue field `κ(x)`. The map `R → O → κ(O)` has
the centre of `x` as kernel, so some valuation subring `U` of `κ(O)` dominates `𝔭`, and the
composite `W = O ∘ U ⊆ O` (`ValuationSubring.comapResidue`) has centre `𝔭` on `R`. A larger
valuation subring is a generization, so `x` specializes to the pullback of `W`.

These are the algebraic inputs to the specialization map of a Huber pair,
`Spa(A, A⁺) → Spec(A⁺ ⧸ A°°)`: the first to its surjectivity over a Tate ring, where `𝔭` is the
prime of `A⁺` to be hit and `𝔮` a prime below it that avoids a pseudouniformiser, and the second
to the lifting of specializations along it.

## Main results

* `TauCeti.ValuationSpectrum.exists_supp_eq_and_valuation_lt_one_iff_mem`: for primes `𝔮 ⊆ 𝔭` of
  `R`, some point of `Spv R` bounded by `1` on `R` has support `𝔮` and centre `𝔭`.
* `TauCeti.ValuationSpectrum.exists_specializes_supp_eq_and_valuation_lt_one_iff_mem`: a point
  bounded by `1` on `φ(R)` specializes, keeping its support, to one with any larger centre.

## References

* [The Stacks Project](https://stacks.math.columbia.edu/tag/00IA), Tag 00IA: every local subring
  of a field is dominated by a valuation subring.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Chapter 4, for vertical
  specializations as composites of valuation rings.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {R : Type*} [CommRing R]

/-- **Every pair of primes `𝔮 ⊆ 𝔭` is the support and centre of a valuation.** For prime ideals
`𝔮 ⊆ 𝔭` of `R`, some point `v` of `Spv R` is bounded by `1` on `R`, has support `𝔮`, and takes
values strictly below `1` exactly on `𝔭`. -/
theorem exists_supp_eq_and_valuation_lt_one_iff_mem {𝔮 𝔭 : Ideal R} [𝔮.IsPrime] [𝔭.IsPrime]
    (h : 𝔮 ≤ 𝔭) :
    ∃ v : Spv R, v.supp = 𝔮 ∧ (∀ r, v.valuation r ≤ 1) ∧ ∀ r, v.valuation r < 1 ↔ r ∈ 𝔭 := by
  -- `g : R → Frac(R ⧸ 𝔮)` has kernel `𝔮`
  let g : R →+* FractionRing (R ⧸ 𝔮) := (algebraMap (R ⧸ 𝔮) _).comp (Ideal.Quotient.mk 𝔮)
  have hkerg : RingHom.ker g = 𝔮 := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (R ⧸ 𝔮) _), Ideal.mk_ker]
  obtain ⟨V, hmem, hnon⟩ :=
    g.exists_valuationSubring_mem_and_mem_nonunits_iff 𝔭 (hkerg.trans_le h)
  let w : Valuation R V.ValueGroup := V.valuation.comap g
  refine ⟨ofValuation w, ?_, fun r ↦ ?_, fun r ↦ ?_⟩
  · ext r
    rw [supp_ofValuation, Valuation.mem_supp_iff, Valuation.comap_apply, Valuation.zero_iff,
      ← RingHom.mem_ker, hkerg]
  · exact (isEquiv_valuation_ofValuation w).le_one_iff_le_one.mpr
      ((V.valuation_le_one_iff _).mpr (hmem r))
  · exact (isEquiv_valuation_ofValuation w).lt_one_iff_lt_one.trans
      (V.mem_nonunits_iff.symm.trans (hnon r))

/-- **Enlarging the centre by a specialization.** Let `φ : R →+* A` and let `x` be a point of
`Spv A` bounded by `1` on `φ(R)`. If a prime `𝔭` of `R` contains the centre `{r : x(φ r) < 1}`,
then `x` specializes to a point `x'` with the same support, bounded by `1` on `φ(R)`, whose
values on `φ(R)` are strictly below `1` exactly on `𝔭`. -/
theorem exists_specializes_supp_eq_and_valuation_lt_one_iff_mem {A : Type*} [CommRing A]
    (φ : R →+* A) {x : Spv A} (hx : ∀ r, x.valuation (φ r) ≤ 1) (𝔭 : Ideal R) [𝔭.IsPrime]
    (h𝔭 : ∀ r, x.valuation (φ r) < 1 → r ∈ 𝔭) :
    ∃ x' : Spv A, x ⤳ x' ∧ x'.supp = x.supp ∧ (∀ r, x'.valuation (φ r) ≤ 1) ∧
      ∀ r, x'.valuation (φ r) < 1 ↔ r ∈ 𝔭 := by
  -- `x` is the pullback along `ι : A → κ(x)` of the point of a valuation subring `O` of `κ(x)`
  let ι := algebraMap A x.supp.ResidueField
  let O := (residueFieldValuation x).valuationSubring
  have hxO : comap ι (ofValuation O.valuation) = x := by
    rw [← ofValuation_eq_of_isEquiv (Valuation.isEquiv_valuation_valuationSubring _),
      comap_algebraMap_residueField_ofValuation]
  -- the pullback of the point of a valuation subring `V` reads off membership and nonunits
  have hle (V : ValuationSubring x.supp.ResidueField) (a : A) :
      (comap ι (ofValuation V.valuation)).valuation a ≤ 1 ↔ ι a ∈ V :=
    (valuation_map_le_one_iff rfl a).symm.trans
      ((isEquiv_valuation_ofValuation _).le_one_iff_le_one.trans (V.valuation_le_one_iff _))
  have hlt (V : ValuationSubring x.supp.ResidueField) (a : A) :
      (comap ι (ofValuation V.valuation)).valuation a < 1 ↔ ι a ∈ V.nonunits :=
    (valuation_map_lt_one_iff rfl a).symm.trans
      ((isEquiv_valuation_ofValuation _).lt_one_iff_lt_one.trans V.mem_nonunits_iff.symm)
  -- `φ` lands in `O`, and modulo the maximal ideal of `O` its kernel is the centre of `x`
  let ψ : R →+* O := (ι.comp φ).codRestrict O fun r ↦ (hle O (φ r)).mp (hxO.symm ▸ hx r)
  have hker : RingHom.ker ((IsLocalRing.residue O).comp ψ) ≤ 𝔭 := fun r hr ↦ h𝔭 r <| hxO ▸
    (hlt O (φ r)).mpr (ValuationSubring.coe_mem_nonunits_iff.mpr
      ((IsLocalRing.residue_eq_zero_iff _).mp (RingHom.mem_ker.mp hr)))
  -- a valuation subring `U` of `κ(O)` dominating `𝔭`, and the composite `W ⊆ O` of `O` with `U`
  obtain ⟨U, hU, hUnon⟩ :=
    ((IsLocalRing.residue O).comp ψ).exists_valuationSubring_mem_and_mem_nonunits_iff 𝔭 hker
  refine ⟨comap ι (ofValuation (O.comapResidue U).valuation), ?_, ?_, fun r ↦ ?_, fun r ↦ ?_⟩
  · have := (ofValuation_valuation_specializes_of_le
      (ValuationSubring.comapResidue_le (U := U))).map (continuous_comap ι)
    rwa [hxO] at this
  · refine (?_ : _ = (comap ι (ofValuation O.valuation)).supp).trans (congrArg supp hxO)
    rw [supp_comap, supp_comap,
      Ideal.eq_bot_of_prime (ofValuation (O.comapResidue U).valuation).supp,
      Ideal.eq_bot_of_prime (ofValuation O.valuation).supp]
  · exact (hle _ (φ r)).mpr (ValuationSubring.coe_mem_comapResidue_iff (a := ψ r) |>.mpr (hU r))
  · exact (hlt _ (φ r)).trans
      ((ValuationSubring.coe_mem_nonunits_comapResidue_iff (a := ψ r)).trans (hUnon r))

end TauCeti.ValuationSpectrum
