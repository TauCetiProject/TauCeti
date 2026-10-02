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
`IsLocalRing.ResidueField.mapEquiv`. No finiteness assumption on the residue fields is needed.

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

private theorem adicValuation_isEquiv :
    (adic k F p).valuation.IsEquiv (p.valuation F) := by
  rw [valuation_adic]

private def withValAdicEquiv :
    WithVal (adic k F p).valuation ≃+* WithVal (p.valuation F) :=
  WithVal.congr _ _ (RingEquiv.refl F)

private theorem uniformContinuous_withValAdicEquiv :
    UniformContinuous (withValAdicEquiv k F p) :=
  (adicValuation_isEquiv k F p).uniformContinuous_congr

private theorem uniformContinuous_withValAdicEquiv_symm :
    UniformContinuous (withValAdicEquiv k F p).symm :=
  (adicValuation_isEquiv k F p).symm.uniformContinuous_congr

private def completionAdicRingEquiv :
    (adic k F p).Completion ≃+* p.adicCompletion F :=
  (Completion.mapRingEquiv (withValAdicEquiv k F p)
    (uniformContinuous_withValAdicEquiv k F p).continuous
    (uniformContinuous_withValAdicEquiv_symm k F p).continuous).trans
    (HeightOneSpectrum.adicCompletion.equiv F p).symm

private theorem completionAdicRingEquiv_embedding (x : F) :
    completionAdicRingEquiv k F p ((adic k F p).completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x := by
  rw [completionAdicRingEquiv, RingEquiv.trans_apply, completionEmbedding_apply,
    RingEquiv.symm_apply_eq, Completion.mapRingEquiv_apply,
    Completion.map_coe (uniformContinuous_withValAdicEquiv k F p)]
  simp [withValAdicEquiv, HeightOneSpectrum.algebraMap_adicCompletion]

/-- The completion of the adic place is the affine-model adic completion, over the constants. -/
def completionAdicEquiv : (adic k F p).Completion ≃ₐ[k] p.adicCompletion F :=
  AlgEquiv.ofRingEquiv (f := completionAdicRingEquiv k F p) fun c ↦ by
    rw [← (adic k F p).completionEmbedding.commutes,
      completionAdicRingEquiv_embedding, ← IsScalarTower.algebraMap_apply k F _]

/-- The comparison carries the intrinsic field embedding to the adic field embedding. -/
@[simp]
theorem completionAdicEquiv_completionEmbedding (x : F) :
    completionAdicEquiv k F p ((adic k F p).completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x :=
  completionAdicRingEquiv_embedding k F p x

/-- The comparison is uniformly continuous for the valuation uniformities. -/
theorem uniformContinuous_completionAdicEquiv :
    UniformContinuous (completionAdicEquiv k F p) :=
  (HeightOneSpectrum.adicCompletion.uniformEquiv F p).symm.uniformContinuous.comp
    Completion.uniformContinuous_map

/-- The inverse comparison is uniformly continuous for the valuation uniformities. -/
theorem uniformContinuous_completionAdicEquiv_symm :
    UniformContinuous (completionAdicEquiv k F p).symm :=
  Completion.uniformContinuous_map.comp
    (HeightOneSpectrum.adicCompletion.uniformEquiv F p).uniformContinuous

/-- The comparison preserves the normalized valuation on completed functions. -/
@[simp]
theorem valuation_completionAdicEquiv (x : (adic k F p).Completion) :
    Valued.v (completionAdicEquiv k F p x) = (adic k F p).completionPlace.valuation x := by
  have h₁ := Valued.continuous_valuation_of_surjective
    (p.valuedAdicCompletion_surjective F)
  have h₂ := Valued.continuous_valuation_of_surjective
    (by simpa only [Function.Surjective, completionPlace_valuation] using
      (adic k F p).completionPlace.valuation_surjective)
  rw [completionPlace_valuation]
  exact congrFun ((adic k F p).denseRange_completionEmbedding.equalizer
    (h₁.comp (uniformContinuous_completionAdicEquiv k F p).continuous) h₂
    (funext fun y ↦ by
      simp [HeightOneSpectrum.algebraMap_adicCompletion])) x

/-- The comparison identifies a filtration step with its valuation bound in the adic field.
The multiplicative bound also handles zero and negative filtration indices. -/
theorem completionAdicEquiv_mem_filtration_iff (a : ℤ) (x : (adic k F p).Completion) :
    Valued.v (completionAdicEquiv k F p x) ≤ WithZero.exp (-a) ↔
      x ∈ (adic k F p).completionPlace.filtration a := by
  rw [valuation_completionAdicEquiv, mem_filtration_iff]

/-- The field comparison identifies the two rings of integers. -/
theorem completionAdicEquiv_mem_integers_iff (x : (adic k F p).Completion) :
    completionAdicEquiv k F p x ∈ p.adicCompletionIntegers F ↔
      x ∈ (adic k F p).completionPlace.integers := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valuation_completionAdicEquiv,
    mem_integers_iff]

/-- The restriction of the completion comparison to the two valuation rings. -/
def completionIntegersAdicEquiv :
    (adic k F p).completionPlace.integers ≃+* p.adicCompletionIntegers F where
  toFun x := ⟨completionAdicEquiv k F p x,
    (completionAdicEquiv_mem_integers_iff k F p x).mpr x.2⟩
  invFun y := ⟨(completionAdicEquiv k F p).symm y, by
    apply (completionAdicEquiv_mem_integers_iff k F p _).mp
    simp⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul (completionAdicEquiv k F p) _ _)
  map_add' x y := Subtype.ext (map_add (completionAdicEquiv k F p) _ _)

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
    completionAdicEquiv_completionEmbedding,
    ← IsScalarTower.algebraMap_apply R F (p.adicCompletion F),
    HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.algebraMap_adicCompletion]
  rfl

/-- The comparison identifies the maximal ideals of the completed valuation rings. -/
theorem completionIntegersAdicEquiv_mem_maximalIdeal_iff
    (x : (adic k F p).completionPlace.integers) :
    completionIntegersAdicEquiv k F p x ∈ IsLocalRing.maximalIdeal (p.adicCompletionIntegers F) ↔
      x ∈ IsLocalRing.maximalIdeal (adic k F p).completionPlace.integers := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

/-- The completed residue fields agree under the valuation-ring comparison. -/
def completionResidueFieldAdicEquiv :
    (adic k F p).completionPlace.ResidueField ≃+*
      IsLocalRing.ResidueField (p.adicCompletionIntegers F) :=
  IsLocalRing.ResidueField.mapEquiv (completionIntegersAdicEquiv k F p)

/-- The residue-field comparison commutes with reduction in the completed valuation rings. -/
@[simp]
theorem completionResidueFieldAdicEquiv_apply_residue
    (x : (adic k F p).completionPlace.integers) :
    completionResidueFieldAdicEquiv k F p
        (IsLocalRing.residue (adic k F p).completionPlace.integers x) =
      IsLocalRing.residue (p.adicCompletionIntegers F)
        (completionIntegersAdicEquiv k F p x) :=
  IsLocalRing.ResidueField.map_residue _ _

/-- The intrinsic residue comparisons agree with the affine-model residue comparison.
In particular the comparison preserves the constants coming from `R ⧸ p`. -/
theorem completionResidueFieldAdicEquiv_comp_adicResidueFieldEquiv :
    ((adicResidueFieldEquiv k F p).toRingEquiv.trans
      ((adic k F p).residueFieldEquivCompletion.toRingEquiv.trans
        (completionResidueFieldAdicEquiv k F p))) =
      p.residueFieldEquivAdicCompletionIntegers (K := F) := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    adicResidueFieldEquiv_mk, adicResidueHom_apply,
    residueFieldEquivCompletion_apply_residue, completionResidueFieldAdicEquiv_apply_residue,
    completionIntegersAdicEquiv_completionIntegersEmbedding]
  exact (p.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r).symm

end TauCeti.Place
