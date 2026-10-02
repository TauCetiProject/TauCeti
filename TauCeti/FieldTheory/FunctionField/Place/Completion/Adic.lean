/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Adic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Intrinsic and affine-model completions

The intrinsic completion at the place attached to a height-one prime of a Dedekind
`k`-algebra is canonically the prime's adic completion. The comparison is a continuous
`k`-algebra equivalence preserving the normalized valuation. It restricts to the valuation
rings, identifies their maximal ideals and residue fields, and commutes with the original
field embeddings and reduction maps. Thus local calculations made with places can be used
in the adic completions appearing in finite adeles.

The field comparison uses Mathlib's `HeightOneSpectrum.adicCompletion.equiv` and
`adicCompletion.uniformEquiv`; the residue comparison uses
`IsLocalRing.ResidueField.mapAlgEquiv`. No finiteness assumption on the residue fields is needed.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.7.
-/

public section

noncomputable section

open IsDedekindDomain
open scoped WithZero
open UniformSpace WithZeroTopology
open HeightOneSpectrum.adicCompletion

namespace TauCeti.Place

variable (k F : Type*) {R : Type*} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F] (p : HeightOneSpectrum R)

private def completionAdicRingEquiv (v : Valuation F ℤᵐ⁰) (hv : v = p.valuation F) :
    v.Completion ≃+* p.adicCompletion F := by
  subst v
  exact (HeightOneSpectrum.adicCompletion.equiv F p).symm

private theorem completionAdicRingEquiv_embedding (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) (x : F) :
    completionAdicRingEquiv F p v hv
        ((WithVal.toVal v x : WithVal v) : v.Completion) =
      algebraMap F (p.adicCompletion F) x := by
  subst v
  rw [completionAdicRingEquiv, RingEquiv.symm_apply_eq]
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

private theorem continuous_completionAdicRingEquiv (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) : Continuous (completionAdicRingEquiv F p v hv) := by
  subst v
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv F p).symm.continuous

private theorem continuous_completionAdicRingEquiv_symm (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) : Continuous (completionAdicRingEquiv F p v hv).symm := by
  subst v
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv F p).continuous

/-- The completion of the adic place is the affine-model adic completion, over the constants. -/
def completionAdicEquiv : (adic k F p).Completion ≃A[k] p.adicCompletion F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := completionAdicRingEquiv F p _ (valuation_adic k F p)) fun c ↦ by
      rw [← (adic k F p).completionEmbedding.commutes, completionEmbedding_apply,
        completionAdicRingEquiv_embedding, ← IsScalarTower.algebraMap_apply k F _]
  continuous_toFun := continuous_completionAdicRingEquiv F p _ (valuation_adic k F p)
  continuous_invFun := continuous_completionAdicRingEquiv_symm F p _ (valuation_adic k F p)

/-- The comparison carries the intrinsic field embedding to the adic field embedding. -/
@[simp]
theorem completionAdicEquiv_completionEmbedding (x : F) :
    completionAdicEquiv k F p ((adic k F p).completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x := by
  rw [completionEmbedding_apply]
  -- Reduce the bundled algebra equivalence to its underlying ring equivalence.
  convert completionAdicRingEquiv_embedding F p _ (valuation_adic k F p) x using 1
  rfl

/-- The comparison preserves the normalized valuation on completed functions. -/
@[simp]
theorem valuation_completionAdicEquiv (x : (adic k F p).Completion) :
    Valued.v (completionAdicEquiv k F p x) = (adic k F p).completionPlace.valuation x := by
  rw [completionPlace_valuation]
  have h (v : Valuation F ℤᵐ⁰) (hv : v = p.valuation F) (y : v.Completion) :
      Valued.v (completionAdicRingEquiv F p v hv y) = Valued.v y := by
    subst v
    exact HeightOneSpectrum.adicCompletion.valued_ofCompletion F p y
  exact h _ (valuation_adic k F p) x

/-- The comparison preserves uniformizers for the normalized completed valuations. -/
@[simp]
theorem isUniformizer_completionAdicEquiv_iff (x : (adic k F p).Completion) :
    (Valued.v : Valuation (p.adicCompletion F) ℤᵐ⁰).IsUniformizer
        (completionAdicEquiv k F p x) ↔
      (adic k F p).completionPlace.valuation.IsUniformizer x := by
  simp only [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (p.valuedAdicCompletion_surjective F),
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (adic k F p).completionPlace.valuation_surjective,
    valuation_completionAdicEquiv]

/-- The field comparison identifies the two rings of integers. -/
@[simp]
theorem completionAdicEquiv_mem_integers_iff (x : (adic k F p).Completion) :
    completionAdicEquiv k F p x ∈ p.adicCompletionIntegers F ↔
      x ∈ (adic k F p).completionPlace.integers := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valuation_completionAdicEquiv,
    mem_integers_iff]

/-- The continuous restriction of the completion comparison to the two valuation rings,
over the constants. -/
def completionIntegersAdicEquiv :
    (adic k F p).completionPlace.integers ≃A[k] p.adicCompletionIntegers F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := (completionAdicEquiv k F p).toAlgEquiv.toRingEquiv.restrict
      (adic k F p).completionPlace.integers (p.adicCompletionIntegers F)
      fun x ↦ (completionAdicEquiv_mem_integers_iff k F p x).symm) fun c ↦ by
    apply Subtype.ext
    simp only [RingEquiv.restrict_apply_coe, AlgEquiv.coe_toRingEquiv,
      coe_algebraMap_constants]
    rw [(completionAdicEquiv k F p).toAlgEquiv.commutes,
      IsScalarTower.algebraMap_apply k R (p.adicCompletionIntegers F),
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      ← IsScalarTower.algebraMap_apply k R F]
  continuous_toFun :=
    ((completionAdicEquiv k F p).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((completionAdicEquiv k F p).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The valuation-ring comparison is the restriction of the field comparison. -/
@[simp]
theorem completionIntegersAdicEquiv_apply
    (x : (adic k F p).completionPlace.integers) :
    (completionIntegersAdicEquiv k F p x : p.adicCompletion F) =
      completionAdicEquiv k F p x := (rfl)

/-- The valuation-ring comparison carries completed model elements to their adic images. -/
@[simp]
theorem completionIntegersAdicEquiv_completionIntegersEmbedding (r : R) :
    completionIntegersAdicEquiv k F p
        ((adic k F p).completionIntegersEmbedding (algebraMap R (adic k F p).integers r)) =
      algebraMap R (p.adicCompletionIntegers F) r := by
  apply Subtype.ext
  rw [completionIntegersAdicEquiv_apply, completionIntegersEmbedding_apply,
    ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply R _ F,
    completionAdicEquiv_completionEmbedding]
  exact p.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (K := F) r

/-- The completed residue fields agree under the valuation-ring comparison. -/
def completionResidueFieldAdicEquiv :
    (adic k F p).completionPlace.ResidueField ≃ₐ[k]
      IsLocalRing.ResidueField (p.adicCompletionIntegers F) :=
  IsLocalRing.ResidueField.mapAlgEquiv (completionIntegersAdicEquiv k F p).toAlgEquiv

/-- The residue-field comparison commutes with reduction from the completed valuation rings. -/
@[simp]
theorem completionResidueFieldAdicEquiv_apply_residue
    (x : (adic k F p).completionPlace.integers) :
    completionResidueFieldAdicEquiv k F p
        (IsLocalRing.residue (adic k F p).completionPlace.integers x) =
      IsLocalRing.residue (p.adicCompletionIntegers F) (completionIntegersAdicEquiv k F p x) :=
  IsLocalRing.ResidueField.mapAlgEquiv_residue (completionIntegersAdicEquiv k F p).toAlgEquiv x

/-- Composing `adicResidueFieldEquiv`, `residueFieldEquivCompletion`, and
`completionResidueFieldAdicEquiv` gives `residueFieldEquivAdicCompletionIntegers`,
viewed as an equivalence over the constants. -/
theorem adicResidueFieldEquiv_trans_trans_eq_residueFieldEquivAdicCompletionIntegers :
    ((adicResidueFieldEquiv k F p).trans
      ((adic k F p).residueFieldEquivCompletion.trans
        (completionResidueFieldAdicEquiv k F p))) =
      AlgEquiv.ofRingEquiv (f := p.residueFieldEquivAdicCompletionIntegers (K := F))
        (fun c ↦ p.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F)
          (algebraMap k R c)) := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgEquiv.trans_apply,
    adicResidueFieldEquiv_mk, adicResidueHom_apply,
    residueFieldEquivCompletion_apply_residue, completionResidueFieldAdicEquiv_apply_residue,
    completionIntegersAdicEquiv_completionIntegersEmbedding]
  exact (p.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r).symm

end TauCeti.Place
