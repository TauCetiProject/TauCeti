/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryIdeles
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.AuxiliaryPlaces
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Tower
import TauCeti.NumberTheory.NumberField.Kummer.Unramified

/-!
# Auxiliary Kummer ideles as norms

Let `K` contain the `p`-th roots of unity, let `S` contain the places above `p`, and put
`M = K(U_S^{1/p})`. For an intermediate field `L` of `M/K`, the auxiliary-place construction
chooses a finite set `T`, disjoint from `S`, whose places have local degree one in `L`. The
extension `L/K` has exponent dividing `p` and is unramified outside `S`, so the auxiliary Kummer
idele subgroup `E_{S,T}` consists of norms from `L`.

This combines the Frobenius choice of `T` with the placewise norm criterion. It is the norm-side
input in the Kummer proof of the second fundamental inequality: the remaining index calculation
compares the image of `E_{S,T}` in the idele classes with the principal `S`-units.

## Main result

* `TauCeti.ClassFieldTheory.exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap`:
  the auxiliary set `T`, its counting and local-power-class properties, and the inclusion of its
  idele-class subgroup in the norm subgroup from `L`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6, especially Lemmas 6.4, 6.6 and 6.9.
-/

public noncomputable section

open IsDedekindDomain NumberField IntermediateField
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

variable {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E]

/-- **The auxiliary Kummer idele classes are norms from an intermediate Kummer field.**
Let `M = K(U_S^{1/p})`, where `S` contains the places above the prime `p`, and let `L/K` be an
intermediate field of `M/K`. There is a finite set `T`, disjoint from `S`, such that
`p ^ #T = [M : L]`, the `S`-units surject onto the local unit `p`-th power classes at `T`, and
the image in `C_K` of the auxiliary Kummer subgroup `E_{S,T}` is contained in
`N_{L/K}(C_L)`. -/
theorem exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap
    {p : ℕ} (hp : p.Prime) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ∃ x : E, x ^ p = algebraMap K E (a : K))
    (L : IntermediateField K
      (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) [NumberField L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∃ hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _),
        p ^ T.card = Module.finrank L
            (kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) ∧
          Function.Surjective
            (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p) ∧
          auxiliaryKummerIdeleClassSubgroup (K := K) S T p ≤
            (GlobalNumberFields.ideleClassNormMap K L :
              IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  classical
  let _ : Algebra K L := L.algebra'
  let M := kummerField E p ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hζK : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
    hζ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  let _ : HasEnoughRootsOfUnity K p := .of_card_le hζK.card_rootsOfUnity.ge
  let _ : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex
      ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
    ⟨by rw [relIndex_range_powMonoidHom_sUnits_numberField]; exact pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨T, hST, hcard, hsurj, hsplit⟩ :=
    exists_auxiliaryPlaces_unitLocalPowerClassMap_surjective hp S hpS hζ hroots L
  have hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S := fun _ hv ↦
    TauCeti.NumberField.ramifiedSupport_kummerField_sUnits_subset S hpS
      (NumberField.ramifiedSupport_mono K (L := L) (M := M) hv)
  refine ⟨T, hST, hcard, hsurj, ?_⟩
  apply auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap K L
  · have hMexp : Monoid.exponent (M ≃ₐ[K] M) ∣ p :=
      exponent_algEquiv_kummerField_dvd
    exact (MonoidHom.exponent_dvd (AlgEquiv.restrictNormalHom_surjective M)).trans hMexp
  · intro v hvT _
    obtain ⟨w, hw⟩ := hsplit v hvT
    refine ⟨w, ?_⟩
    let _ : w.1.asIdeal.LiesOver v.asIdeal := w.2
    rw [HeightOneSpectrum.finrank_adicCompletion (R := 𝓞 K) (K := K) (B := 𝓞 L)
      (L := L) v w.1]
    exact hw
  · intro v hvS _
    obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
    exact ⟨⟨w, inferInstance⟩, NumberField.isUnramifiedAway_ramifiedSupport _
      (fun hv ↦ hvS (hram hv)) w.asIdeal⟩

end TauCeti.ClassFieldTheory
