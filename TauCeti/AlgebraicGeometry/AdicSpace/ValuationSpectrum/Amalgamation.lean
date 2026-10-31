/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.RingTheory.Valuation.Amalgamation

/-!
# Amalgamation of points of valuation spectra

Let `A → B` and `A → C` be ring homomorphisms, and let `y ∈ Spv B` and `x ∈ Spv C` be points with
the same pullback to `Spv A`. Then some point of `Spv (B ⊗[A] C)` pulls back to `y` and to `x`
along the two inclusions (`TauCeti.ValuationSpectrum.exists_amalgamation`). The amalgam is not
unique in general: for a quadratic extension `L` of `ℚ_p`, the ring `L ⊗[ℚ_p] L` is a product of
two copies of `L`, and both factors carry an amalgam of the `p`-adic valuation with itself. This is
the statement behind the description of the points of a fibre product of adic spaces.

The proof passes to residue fields. Points of `Spv` of a field are its valuation subrings
(`ofValuation_valuationSubring_valuation`, `comap_ofValuation_valuation`). The points `y` and `x`
are the residue-field valuations on `κ(y)` and `κ(x)` pulled back to `B` and `C`, and these
restrict to the residue-field valuation of their common pullback `z` on `κ(z)`, because pulling
back along `A → κ(z)` is injective. The amalgamation of valuation subrings
(`ValuationSubring.exists_comap_eq_of_comap_eq`) on `κ(y) ⊗[κ(z)] κ(x)` then gives the amalgam,
pulled back along `B ⊗[A] C → κ(y) ⊗[κ(z)] κ(x)`.

## Main results

* `TauCeti.ValuationSpectrum.comap_algebraMap_ofValuation_residueFieldValuation`: a point is the
  pullback of its residue-field valuation.
* `TauCeti.ValuationSpectrum.comap_algebraMap_residueField_injective`: pulling back along
  `A → κ(𝔭)` is injective on valuation spectra.
* `TauCeti.ValuationSpectrum.exists_amalgamation`: points agreeing on `A` amalgamate on
  `B ⊗[A] C`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), proof of Lemma 3.9(i).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), proof of Proposition 8.63.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace ValuationSpectrum

section Field

variable {K L : Type*} [Field K] [Field L]

/-- A point of the valuation spectrum of a field is the point of its valuation subring. -/
@[simp]
theorem ofValuation_valuationSubring_valuation (w : Spv K) :
    ofValuation w.valuation.valuationSubring.valuation = w :=
  (ofValuation_eq_of_isEquiv
    (Valuation.isEquiv_valuation_valuationSubring w.valuation).symm).trans (ofValuation_valuation w)

/-- Pulling back the point of a valuation subring along a field homomorphism gives the point of
the pulled-back valuation subring. -/
theorem comap_ofValuation_valuation (g : K →+* L) (W : ValuationSubring L) :
    comap g (ofValuation W.valuation) = ofValuation (W.comap g).valuation := by
  rw [comap_ofValuation]
  refine ofValuation_eq_of_isEquiv ?_
  rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation]
  ext x
  simp [Valuation.mem_valuationSubring_iff, ValuationSubring.valuation_le_one_iff]

/-- The valuation subring of a pulled-back point of the valuation spectrum of a field is the
pullback of its valuation subring. -/
theorem valuationSubring_valuation_comap (g : K →+* L) (w : Spv L) :
    (comap g w).valuation.valuationSubring = w.valuation.valuationSubring.comap g := by
  ext x
  have := valuation_le_iff (comap g w) x 1
  rw [map_one, comap_vle, ← valuation_le_iff, map_one] at this
  simpa [Valuation.mem_valuationSubring_iff] using this

end Field

section ResidueField

variable {A : Type*} [CommRing A]

/-- A point of `Spv A` is the pullback of its residue-field valuation along `A → κ(v)`. -/
theorem comap_algebraMap_ofValuation_residueFieldValuation (v : Spv A) :
    comap (algebraMap A v.supp.ResidueField) (ofValuation (residueFieldValuation v)) = v := by
  rw [comap_ofValuation, IsScalarTower.algebraMap_eq A (residueRing v), Valuation.comap_comp]
  convert ofValuation_valuation v using 2
  rw [← quotientValuation_comap_quotientMk]
  congr 1
  ext x
  simp

/-- Pulling back along `A → κ(𝔭)` is injective on valuation spectra, since `A → κ(𝔭)` is a
surjection followed by a localization. -/
theorem comap_algebraMap_residueField_injective (p : Ideal A) [p.IsPrime] :
    Function.Injective (comap (algebraMap A p.ResidueField)) := by
  rw [IsScalarTower.algebraMap_eq A (A ⧸ p), comap_comp]
  exact (comap_injective Ideal.Quotient.mk_surjective).comp
    (localization_comap_injective (nonZeroDivisors (A ⧸ p)) p.ResidueField)

end ResidueField

section TensorProduct

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

open Algebra.TensorProduct in
/-- **Valuations agreeing on `A` amalgamate on `B ⊗[A] C`.** If points `y ∈ Spv B` and
`x ∈ Spv C` pull back to the same point of `Spv A`, then some point of `Spv (B ⊗[A] C)` pulls back
to `y` along `b ↦ b ⊗ 1` and to `x` along `c ↦ 1 ⊗ c`. The amalgam need not be unique. -/
theorem exists_amalgamation (y : Spv B) (x : Spv C)
    (h : comap (algebraMap A B) y = comap (algebraMap A C) x) :
    ∃ v : Spv (B ⊗[A] C), comap includeLeftRingHom v = y ∧
      comap (includeRight (R := A) (A := B)).toRingHom v = x := by
  set z := comap (algebraMap A B) y
  -- the residue fields `κ(y)` and `κ(x)` are extensions of `κ(z)`
  have hzy : z.supp = y.supp.comap (algebraMap A B) := supp_comap _ _
  have hzx : z.supp = x.supp.comap (algebraMap A C) := h ▸ supp_comap _ _
  let : Algebra z.supp.ResidueField y.supp.ResidueField :=
    (Ideal.ResidueField.map z.supp y.supp (algebraMap A B) hzy).toAlgebra
  let : Algebra z.supp.ResidueField x.supp.ResidueField :=
    (Ideal.ResidueField.map z.supp x.supp (algebraMap A C) hzx).toAlgebra
  have hB : (algebraMap B y.supp.ResidueField).comp (algebraMap A B) =
      (algebraMap z.supp.ResidueField _).comp (algebraMap A _) :=
    RingHom.ext fun a ↦ (Ideal.ResidueField.map_algebraMap _ _ _ hzy a).symm
  have hC : (algebraMap C x.supp.ResidueField).comp (algebraMap A C) =
      (algebraMap z.supp.ResidueField _).comp (algebraMap A _) :=
    RingHom.ext fun a ↦ (Ideal.ResidueField.map_algebraMap _ _ _ hzx a).symm
  -- `y`, `x` and `z` are the residue-field valuations, and those of `y` and `x` restrict to that
  -- of `z`, so their valuation subrings meet `κ(z)` in the same valuation subring
  set y' := ofValuation (residueFieldValuation y)
  set x' := ofValuation (residueFieldValuation x)
  have hy' : comap (algebraMap A z.supp.ResidueField)
      (comap (algebraMap z.supp.ResidueField _) y') = z := by
    rw [← Function.comp_apply (f := comap _), ← comap_comp, ← hB, comap_comp, Function.comp_apply,
      comap_algebraMap_ofValuation_residueFieldValuation]
  have hx' : comap (algebraMap A z.supp.ResidueField)
      (comap (algebraMap z.supp.ResidueField _) x') = z := by
    rw [← Function.comp_apply (f := comap _), ← comap_comp, ← hC, comap_comp, Function.comp_apply,
      comap_algebraMap_ofValuation_residueFieldValuation, h]
  have hV := congrArg (fun w ↦ w.valuation.valuationSubring)
    (comap_algebraMap_residueField_injective z.supp (hy'.trans hx'.symm))
  simp only [valuationSubring_valuation_comap] at hV
  -- amalgamate the valuation subrings on a residue field of `κ(y) ⊗[κ(z)] κ(x)`
  obtain ⟨P, _, W, hW₁, hW₂⟩ := ValuationSubring.exists_comap_eq_of_comap_eq _ _ hV
  refine ⟨comap (mapRingHom (algebraMap A z.supp.ResidueField) (algebraMap B y.supp.ResidueField)
    (algebraMap C x.supp.ResidueField) hB hC)
      (comap (algebraMap _ P.ResidueField) (ofValuation W.valuation)), ?_, ?_⟩
  · rw [← Function.comp_apply (f := comap _), ← comap_comp, ← Function.comp_apply (f := comap _),
      ← comap_comp, mapRingHom_comp_includeLeftRingHom, ← RingHom.comp_assoc,
      comap_comp, Function.comp_apply, comap_ofValuation_valuation, hW₁,
      ofValuation_valuationSubring_valuation, comap_algebraMap_ofValuation_residueFieldValuation]
  · rw [AlgHom.toRingHom_eq_coe] at hW₂ ⊢
    rw [← Function.comp_apply (f := comap _), ← comap_comp, ← Function.comp_apply (f := comap _),
      ← comap_comp, mapRingHom_comp_includeRight, ← RingHom.comp_assoc,
      comap_comp, Function.comp_apply, comap_ofValuation_valuation, hW₂,
      ofValuation_valuationSubring_valuation, comap_algebraMap_ofValuation_residueFieldValuation]

end TensorProduct

end ValuationSpectrum

end TauCeti
