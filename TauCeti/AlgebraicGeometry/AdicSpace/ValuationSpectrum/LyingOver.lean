/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# Lifting points of the valuation spectrum along a ring map

Let `φ : A →+* B` be a ring map, `v` a point of `Spv A` with support `𝔭`, and `𝔮` a prime of `B`
lying over `𝔭`. Then `v` is the pullback of a point `w` of `Spv B` with support `𝔮`. No
finiteness or integrality hypothesis on `φ` is needed: valuations extend along every field
extension.

The proof passes to residue fields. The point `v` is a valuation on `κ(𝔭)`
(`TauCeti.ValuationSpectrum.residueFieldValuation`), with valuation ring `O`. The local ring `O`
maps to the field `κ(𝔮)`, and Chevalley's theorem gives a valuation ring `O'` of `κ(𝔮)`
dominating its image (`IsLocalRing.exists_factor_valuationRing`). Domination forces
`O' ∩ κ(𝔭) = O`, because a valuation ring is integrally closed against every ring dominating it
(`TauCeti.ValuationRing.isInteger_of_isInteger_algebraMap`). The valuation of `O'`, pulled back
to `B`, is the point `w`.

Consequently `Spv B → Spv A` is surjective exactly when `Spec B → Spec A` is.

## Main results

* `TauCeti.ValuationSpectrum.exists_supp_eq_comap_eq`: a point of `Spv A` lifts to a point of
  `Spv B` with any prescribed support lying over its own.
* `TauCeti.ValuationSpectrum.comap_surjective_iff`: `Spv B → Spv A` is surjective iff
  `Spec B → Spec A` is.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §2.4 and Remark 4.6.
* [Stacks Project, Lemma 00IA](https://stacks.math.columbia.edu/tag/00IA) for the domination
  step.
-/

public section

namespace TauCeti

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **Lifting a point of the valuation spectrum along a prime lying over its support.** If
`φ : A →+* B` is a ring map, `v ∈ Spv A`, and `𝔮` is a prime of `B` with `φ⁻¹(𝔮) = supp v`, there
is `w ∈ Spv B` with support `𝔮` and pullback `v`. -/
theorem exists_supp_eq_comap_eq (φ : A →+* B) (v : Spv A) (q : Ideal B) [q.IsPrime]
    (hq : q.comap φ = v.supp) : ∃ w : Spv B, w.supp = q ∧ comap φ w = v := by
  set ψ := Ideal.ResidueField.map v.supp q φ hq.symm
  set O := (residueFieldValuation v).valuationSubring
  obtain ⟨O', h, hloc⟩ := IsLocalRing.exists_factor_valuationRing (ψ.comp O.subtype)
  -- domination forces `O' ∩ κ(supp v) = O`
  have hO : O'.comap ψ = O := by
    refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ h ⟨x, hx⟩
    let : Algebra O O' := ((ψ.comp O.subtype).codRestrict O'.toSubring h).toAlgebra
    let : Algebra v.supp.ResidueField q.ResidueField := ψ.toAlgebra
    have : IsLocalHom (algebraMap O O') := hloc
    obtain ⟨y, hy⟩ := ValuationRing.isInteger_of_isInteger_algebraMap (R := O) (S := O')
      Subtype.val_injective (RingHom.ext fun _ ↦ rfl) (x := x) ⟨⟨ψ x, hx⟩, rfl⟩
    exact hy ▸ y.2
  refine ⟨ofValuation (O'.valuation.comap (algebraMap B q.ResidueField)), ?_, ?_⟩
  · ext b
    simp [supp_ofValuation, Valuation.mem_supp_iff, Ideal.algebraMap_residueField_eq_zero]
  · -- the pullback of `O'` to `κ(supp v)` has valuation ring `O`
    have hequiv : (O'.valuation.comap ψ).IsEquiv (residueFieldValuation v) := by
      rw [Valuation.isEquiv_iff_valuationSubring]
      refine Eq.trans ?_ hO
      ext x
      simp [ValuationSubring.mem_comap]
    have hcomp : (algebraMap B q.ResidueField).comp φ =
        ψ.comp ((algebraMap (residueRing v) v.supp.ResidueField).comp
          (Ideal.Quotient.mk v.supp)) := by
      ext a
      simp [ψ, Ideal.ResidueField.map_algebraMap]
    -- `v` is the residue-field valuation pulled back along `A → A ⧸ supp v → κ(supp v)`
    have hv : v.valuation = ((residueFieldValuation v).comap
        (algebraMap (residueRing v) v.supp.ResidueField)).comap (Ideal.Quotient.mk v.supp) := by
      rw [← quotientValuation_comap_quotientMk]
      congr 1
      ext x
      simp
    rw [comap_ofValuation, ← Valuation.comap_comp, hcomp, Valuation.comap_comp,
      Valuation.comap_comp]
    refine (ofValuation_eq_of_isEquiv ?_).trans (ofValuation_valuation v)
    rw [hv]
    exact (hequiv.comap _).comap _

/-- **`Spv B → Spv A` is surjective exactly when `Spec B → Spec A` is.** Taking supports turns a
lift on valuation spectra into one on prime spectra, and conversely a prime lying over the
support of a point carries a lift of that point (`exists_supp_eq_comap_eq`). -/
theorem comap_surjective_iff (φ : A →+* B) :
    Function.Surjective (comap φ) ↔ Function.Surjective (PrimeSpectrum.comap φ) := by
  refine ⟨fun h p ↦ ?_, fun h v ↦ ?_⟩
  · obtain ⟨w, hw⟩ := h (trivialSection p)
    exact ⟨suppFun w, by rw [← suppFun_comap, hw, suppFun_trivialSection]⟩
  · obtain ⟨q, hq⟩ := h (suppFun v)
    obtain ⟨w, -, hw⟩ := exists_supp_eq_comap_eq φ v q.asIdeal
      (by simpa [← suppFun_asIdeal] using congrArg PrimeSpectrum.asIdeal hq)
    exact ⟨w, hw⟩

end ValuationSpectrum

end TauCeti
