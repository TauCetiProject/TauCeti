/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# The residue degree of a completion is the inertia degree

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, and let `w` be a height-one prime of
`B` lying over the height-one prime `v` of `R`. The completions `K_v` and `L_w` carry valuative
relations, and the canonical map `K_v → L_w` is a valuative extension, so the residue field
`𝓀[L_w]` is an extension of the residue field `𝓀[K_v]`. Its degree is the residue degree of the
local extension.

This file proves that this local residue degree is the global inertia degree `f(w ∣ v)`: the
residue-field identifications `R ⧸ v ≃+* 𝓀[K_v]` and `B ⧸ w ≃+* 𝓀[L_w]` intertwine the two residue
extensions, so the two degrees agree. Together with
`IsDedekindDomain.HeightOneSpectrum.ramificationIndex_adicCompletion`, which matches the local
ramification index with `w.asIdeal.ramificationIdx R`, this says that passing to the completions
loses neither of the two invariants attached to `w` over `v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.algebraMap_residueFieldEquivAdicCompletion`: the
  residue-field identifications intertwine the residue extension of `w` over `v` with the residue
  extension of the completions.
* `IsDedekindDomain.HeightOneSpectrum.finrank_residueField_adicCompletion`: the residue degree of
  `L_w / K_v` is `w.asIdeal.inertiaDeg R`.
* `IsDedekindDomain.HeightOneSpectrum.natCard_residueField_adicCompletion_eq_pow_inertiaDeg`: for
  finite residue fields, `#𝓀[L_w] = #𝓀[K_v] ^ f(w ∣ v)`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §6 and §8.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension ValuativeRel

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- **The residue-field identifications are natural.** The identifications `R ⧸ v ≃+* 𝓀[K_v]` and
`B ⧸ w ≃+* 𝓀[L_w]` intertwine the residue extension of `w` over `v` with the residue extension of
the completions. -/
@[simp]
theorem algebraMap_residueFieldEquivAdicCompletion (x : R ⧸ v.asIdeal) :
    algebraMap 𝓀[v.adicCompletion K] 𝓀[w.adicCompletion L]
        (v.residueFieldEquivAdicCompletion (K := K) x) =
      w.residueFieldEquivAdicCompletion (K := L)
        (algebraMap (R ⧸ v.asIdeal) (B ⧸ w.asIdeal) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, residueFieldEquivAdicCompletion_apply_mk,
    residueFieldEquivAdicCompletion_apply_mk, IsLocalRing.ResidueField.algebraMap_residue]
  refine congrArg (IsLocalRing.residue _) (Subtype.ext ?_)
  rw [TauCeti.coe_algebraMap_integerRing, algebraMap_adicCompletionExtensionAlgebra]
  exact adicCompletionExtension_algebraMap K L v w a

/-- **The local residue degree is the global inertia degree.** For `w` a height-one prime of `B`
over the height-one prime `v` of `R`, the residue field of the completion `L_w` has degree
`w.asIdeal.inertiaDeg R` over the residue field of `K_v`. -/
@[simp]
theorem finrank_residueField_adicCompletion :
    Module.finrank 𝓀[v.adicCompletion K] 𝓀[w.adicCompletion L] =
      w.asIdeal.inertiaDeg R := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv (v.residueFieldEquivAdicCompletion (K := K))
    (w.residueFieldEquivAdicCompletion (K := L)) (RingHom.ext fun x ↦ ?_)).symm
  exact algebraMap_residueFieldEquivAdicCompletion v w x

/-- **The residue cardinality of a completion.** When the residue field of `w` is finite, the
residue field of `L_w` has `#𝓀[K_v] ^ f(w ∣ v)` elements. -/
theorem natCard_residueField_adicCompletion_eq_pow_inertiaDeg [Finite (B ⧸ w.asIdeal)] :
    Nat.card 𝓀[w.adicCompletion L] =
      Nat.card 𝓀[v.adicCompletion K] ^ w.asIdeal.inertiaDeg R := by
  -- the residue field of `v` embeds in the residue field of `w`, so it is finite too
  have : Finite (R ⧸ v.asIdeal) :=
    .of_injective _ (FaithfulSMul.algebraMap_injective (R ⧸ v.asIdeal) (B ⧸ w.asIdeal))
  have hK : Finite 𝓀[v.adicCompletion K] :=
    .of_equiv _ (v.residueFieldEquivAdicCompletion (K := K)).toEquiv
  have hL : Finite 𝓀[w.adicCompletion L] :=
    .of_equiv _ (w.residueFieldEquivAdicCompletion (K := L)).toEquiv
  have _ : Fintype 𝓀[v.adicCompletion K] := .ofFinite _
  have _ : Fintype 𝓀[w.adicCompletion L] := .ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← finrank_residueField_adicCompletion (K := K) (L := L) v w]
  exact Module.card_eq_pow_finrank

end IsDedekindDomain.HeightOneSpectrum
