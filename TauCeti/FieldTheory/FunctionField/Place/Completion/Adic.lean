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
field embeddings and reduction maps. Maximal-ideal compatibility follows from Mathlib's
`IsLocalRing.map_ringEquiv_maximalIdeal` applied to the valuation-ring equivalence.
Thus local calculations made with places can be used
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
open scoped WithZero AdicCompletionIntegers
open UniformSpace WithZeroTopology
open HeightOneSpectrum.adicCompletion

namespace TauCeti.Place

variable (k F : Type*) {R : Type*} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F] (p : HeightOneSpectrum R)

-- The equality parameter transports the valued and uniform structures from the adic valuation
-- to an equal place valuation, without unfolding the dependent place-completion carrier.
private def completionAdicRingEquiv (v : Valuation F ℤᵐ⁰) (hv : v = p.valuation F) :
    v.Completion ≃+* p.adicCompletion F :=
  hv.symm ▸ (HeightOneSpectrum.adicCompletion.equiv F p).symm

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

private theorem valuation_completionAdicRingEquiv (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) (y : v.Completion) :
    Valued.v (completionAdicRingEquiv F p v hv y) = Valued.v y := by
  subst v
  exact HeightOneSpectrum.adicCompletion.valued_ofCompletion F p y

/-- The completion of a place with the affine model's valuation is its adic completion,
over the constants. The equality transports the dependent completion structures. -/
def completionEquivAdicCompletionOfValuationEq (P : Place k F)
    (hP : P.valuation = p.valuation F) : P.Completion ≃A[k] p.adicCompletion F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := completionAdicRingEquiv F p _ hP) fun c ↦ by
      rw [← P.completionEmbedding.commutes, completionEmbedding_apply,
        completionAdicRingEquiv_embedding, ← IsScalarTower.algebraMap_apply k F _]
  continuous_toFun := continuous_completionAdicRingEquiv F p _ hP
  continuous_invFun := continuous_completionAdicRingEquiv_symm F p _ hP

/-- The completion of the adic place is the affine-model adic completion, over the constants. -/
def completionEquivAdicCompletion : (adic k F p).Completion ≃A[k] p.adicCompletion F :=
  completionEquivAdicCompletionOfValuationEq k F p (adic k F p) (valuation_adic k F p)

private theorem completionEquivAdicCompletion_apply (x : (adic k F p).Completion) :
    completionEquivAdicCompletion k F p x =
      completionAdicRingEquiv F p _ (valuation_adic k F p) x := rfl

/-- The comparison carries the intrinsic field embedding to the adic field embedding. -/
@[simp]
theorem completionEquivAdicCompletion_completionEmbedding (x : F) :
    completionEquivAdicCompletion k F p ((adic k F p).completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x := by
  rw [completionEquivAdicCompletion_apply, completionEmbedding_apply,
    completionAdicRingEquiv_embedding]

/-- The comparison preserves the normalized valuation on completed functions. -/
@[simp]
theorem valuation_completionEquivAdicCompletion (x : (adic k F p).Completion) :
    Valued.v (completionEquivAdicCompletion k F p x) =
      (adic k F p).completionPlace.valuation x := by
  rw [completionEquivAdicCompletion_apply, completionPlace_valuation]
  exact valuation_completionAdicRingEquiv F p _ (valuation_adic k F p) x

/-- The comparison preserves uniformizers for the normalized completed valuations. -/
@[simp]
theorem isUniformizer_completionEquivAdicCompletion_iff (x : (adic k F p).Completion) :
    (Valued.v : Valuation (p.adicCompletion F) ℤᵐ⁰).IsUniformizer
        (completionEquivAdicCompletion k F p x) ↔
      (adic k F p).completionPlace.valuation.IsUniformizer x := by
  rw [TauCeti.isUniformizer_adicCompletion_iff, Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (adic k F p).completionPlace.valuation_surjective,
    valuation_completionEquivAdicCompletion]
  rfl

/-- The field comparison identifies the two rings of integers. -/
@[simp]
theorem completionEquivAdicCompletion_mem_integers_iff (x : (adic k F p).Completion) :
    completionEquivAdicCompletion k F p x ∈ p.adicCompletionIntegers F ↔
      x ∈ (adic k F p).completionPlace.integers := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valuation_completionEquivAdicCompletion,
    mem_integers_iff]

/-- The continuous restriction of the completion comparison to the two valuation rings,
over the constants. -/
def completionIntegersEquivAdicCompletionIntegers :
    (adic k F p).completionPlace.integers ≃A[k] p.adicCompletionIntegers F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := (completionEquivAdicCompletion k F p).toAlgEquiv.toRingEquiv.restrict
      (adic k F p).completionPlace.integers (p.adicCompletionIntegers F)
      fun x ↦ (completionEquivAdicCompletion_mem_integers_iff k F p x).symm) fun c ↦ by
    apply Subtype.ext
    simp only [RingEquiv.restrict_apply_coe, AlgEquiv.coe_toRingEquiv,
      coe_algebraMap_constants]
    rw [(completionEquivAdicCompletion k F p).toAlgEquiv.commutes,
      IsScalarTower.algebraMap_apply k R (p.adicCompletionIntegers F),
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      ← IsScalarTower.algebraMap_apply k R F]
  continuous_toFun :=
    ((completionEquivAdicCompletion k F p).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((completionEquivAdicCompletion k F p).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The valuation-ring comparison is the restriction of the field comparison. -/
@[simp]
theorem completionIntegersEquivAdicCompletionIntegers_apply
    (x : (adic k F p).completionPlace.integers) :
    (completionIntegersEquivAdicCompletionIntegers k F p x : p.adicCompletion F) =
      completionEquivAdicCompletion k F p x := (rfl)

/-- The valuation-ring comparison carries completed model elements to their adic images. -/
@[simp]
theorem completionIntegersEquivAdicCompletionIntegers_completionIntegersEmbedding_algebraMap
    (r : R) :
    completionIntegersEquivAdicCompletionIntegers k F p
        ((adic k F p).completionIntegersEmbedding (algebraMap R (adic k F p).integers r)) =
      algebraMap R (p.adicCompletionIntegers F) r := by
  apply Subtype.ext
  rw [completionIntegersEquivAdicCompletionIntegers_apply, completionIntegersEmbedding_apply,
    ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply R _ F,
    completionEquivAdicCompletion_completionEmbedding]
  exact p.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (K := F) r

/-- The completed residue fields agree under the valuation-ring comparison. -/
def completionResidueFieldEquivAdicCompletionIntegers :
    (adic k F p).completionPlace.ResidueField ≃ₐ[k]
      IsLocalRing.ResidueField (p.adicCompletionIntegers F) :=
  IsLocalRing.ResidueField.mapAlgEquiv
    (completionIntegersEquivAdicCompletionIntegers k F p).toAlgEquiv

/-- Both residue comparison routes agree on each affine-model representative. -/
theorem completionResidueFieldEquivAdicCompletionIntegers_apply_adicResidueHom
    (r : R) :
    completionResidueFieldEquivAdicCompletionIntegers k F p
        ((adic k F p).residueFieldEquivCompletion (adicResidueHom k F p r)) =
      residueFieldAlgEquivAdicCompletionIntegers (K := F) k (v := p)
        (Ideal.Quotient.mk p.asIdeal r) := by
  rw [adicResidueHom_apply, residueFieldEquivCompletion_apply_residue]
  simp only [completionResidueFieldEquivAdicCompletionIntegers,
    IsLocalRing.ResidueField.mapAlgEquiv_residue, ContinuousAlgEquiv.coe_toAlgEquiv,
    completionIntegersEquivAdicCompletionIntegers_completionIntegersEmbedding_algebraMap]
  rw [residueFieldAlgEquivAdicCompletionIntegers_apply]
  exact (p.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r).symm

/-- The affine-model residue equivalence equals the composite of `adicResidueFieldEquiv`,
`residueFieldEquivCompletion`, and `completionResidueFieldEquivAdicCompletionIntegers`. -/
theorem residueFieldAlgEquivAdicCompletionIntegers_eq_trans :
    residueFieldAlgEquivAdicCompletionIntegers (K := F) k (v := p) =
      (adicResidueFieldEquiv k F p).trans
        ((adic k F p).residueFieldEquivCompletion.trans
          (completionResidueFieldEquivAdicCompletionIntegers k F p)) := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa only [AlgEquiv.trans_apply, adicResidueFieldEquiv_mk] using
    (completionResidueFieldEquivAdicCompletionIntegers_apply_adicResidueHom k F p r).symm

end TauCeti.Place
