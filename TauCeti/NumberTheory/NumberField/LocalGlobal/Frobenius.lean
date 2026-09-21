/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

/-!
# Frobenius under the decomposition-group equivalence

Let `L/K` be a Galois extension of number fields, and let `w` be a finite place of `L` above a
finite place `v` of `K`. The decomposition-group equivalence identifies the stabilizer of `w`
with the Galois group of the completed extension `L_w/K_v`. This file proves that the
identification respects reduction to residue fields. Consequently it carries an arithmetic
Frobenius at `w` to the Frobenius automorphism of an unramified local extension.

The residue compatibility is stated pointwise through the canonical equivalences
`R ⧸ v ≃ 𝓀[K_v]` and `S ⧸ w ≃ 𝓀[L_w]`. This avoids choosing a second algebra structure on either
residue extension.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.residueFieldEquivAdicCompletion_stabilizerHom`: reduction
  intertwines the global decomposition action with the action on the completed residue field.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_eq_frobeniusAlgEquiv`: a global
  arithmetic Frobenius maps to the local Frobenius.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §9.
-/

public section
noncomputable section

open IsDedekindDomain Module NumberField
open scoped NumberField Pointwise AdicCompletionExtension ValuativeRel

namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝒪 K)} {w : HeightOneSpectrum (𝒪 L)}
  [w.asIdeal.LiesOver v.asIdeal]

/-- **The global and local residue actions agree.** Under the canonical identification of the
residue field of `w` with the residue field of `L_w`, the action of an element of the global
decomposition group is the residue action of its continuous extension to `L_w`. -/
theorem residueFieldEquivAdicCompletion_stabilizerHom
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : (𝒪 L) ⧸ w.asIdeal) :
    w.residueFieldEquivAdicCompletion (K := L)
        (Ideal.Quotient.stabilizerHom w.asIdeal (w.asIdeal.under (𝒪 K)) (L ≃ₐ[K] L) σ x) =
      MulSemiringAction.toAlgAut
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
          𝓀[v.adicCompletion K] 𝓀[w.adicCompletion L] (decompositionHom v w σ)
        (w.residueFieldEquivAdicCompletion (K := L) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.stabilizerHom_apply,
    residueFieldEquivAdicCompletion_apply_mk,
    TauCeti.residueField_toAlgAut_apply,
    AlgEquiv.residueFieldEquiv_apply,
    residueFieldEquivAdicCompletion_apply_mk]
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply congrArg (IsLocalRing.residue _)
  apply Subtype.ext
  -- The residue construction hides the completed field map under two integer-ring subtypes;
  -- expose that map before using the defining property of `decompositionHom`.
  change algebraMap (𝒪 L) (w.adicCompletion L) (σ • x) =
    decompositionHom v w σ (algebraMap (𝒪 L) (w.adicCompletion L) x)
  rw [IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L)]
  rw [IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L)]
  rw [decompositionHom_algebraMap]
  rfl

/-- **The decomposition-group map carries global arithmetic Frobenius to local Frobenius.**
If `w` is unramified over `v`, the continuous extension to `L_w` of an arithmetic Frobenius at
`w` is the canonical Frobenius automorphism of the unramified local extension `L_w/K_v`. -/
theorem decompositionHom_eq_frobeniusAlgEquiv [IsGalois K L]
    [Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝒪 K) σ w.asIdeal) :
    decompositionHom v w ⟨σ, hσ.mem_stabilizer⟩ =
      TauCeti.frobeniusAlgEquiv (K := v.adicCompletion K) (L := w.adicCompletion L) := by
  let _ : Fintype ((𝒪 K) ⧸ w.asIdeal.under (𝒪 K)) := Fintype.ofFinite _
  let _ : Fintype 𝓀[v.adicCompletion K] := Fintype.ofFinite _
  apply (TauCeti.residueFieldAutEquiv
    (K := v.adicCompletion K) (L := w.adicCompletion L)).injective
  ext x
  rw [TauCeti.residueFieldAutEquiv_apply,
    TauCeti.residueFieldAutEquiv_apply]
  obtain ⟨x, rfl⟩ := w.residueFieldEquivAdicCompletion (K := L).surjective x
  rw [← residueFieldEquivAdicCompletion_stabilizerHom,
    Ideal.stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic w.asIdeal w.ne_bot hσ,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    MulSemiringAction.toAlgAut_apply,
    TauCeti.residueField_toAlgEquiv_frobeniusAlgEquiv,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  simp only
  rw [map_pow]
  congr 1
  exact Fintype.card_congr
    (((Ideal.quotEquivOfEq Ideal.LiesOver.over.symm).trans
      (v.residueFieldEquivAdicCompletion (K := K))).toEquiv)

end IsDedekindDomain.HeightOneSpectrum
