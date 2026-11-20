/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Extension
public import TauCeti.FieldTheory.FunctionField.Place.Adic
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Intrinsic and affine-model completions

The intrinsic completion at a place whose valuation agrees with that of a height-one prime `p` of a
Dedekind domain `R` with fraction field `F` is canonically `p.adicCompletion F`
(`TauCeti.Place.completionEquivAdicCompletionOfValuationEq`, requiring no `k`-algebra structure on
`R`). The continuous `k`-algebra equivalence preserves the valuation, restricts to a continuous
ring equivalence of completed valuation rings
(`TauCeti.Place.completionIntegersRingEquivAdicCompletionIntegersOfValuationEq`), upgrades to a
`k`-algebra equivalence when `R` is a `k`-algebra, identifies maximal ideals and residue fields,
and commutes with completed field extensions
(`TauCeti.Place.completionEquivAdicCompletionOfValuationEq_completionExtension`).

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

section SinglePlace

variable (k F : Type*) {R : Type*} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] [Algebra k F] (p : HeightOneSpectrum R)

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
  exact HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply F p y

section ValuationEq

variable (P : Place k F) (hP : P.valuation = p.valuation F)

/-- The completion of a place with the Dedekind model's valuation is its adic completion, over the
constants `k` (with no `k`-algebra assumption on `R`). -/
def completionEquivAdicCompletionOfValuationEq : P.Completion ≃A[k] p.adicCompletion F where
  toAlgEquiv := AlgEquiv.ofRingEquiv (f := completionAdicRingEquiv F p _ hP) fun c ↦ by
    rw [← P.completionEmbedding.commutes, completionEmbedding_apply,
      completionAdicRingEquiv_embedding, ← IsScalarTower.algebraMap_apply k F _]
  continuous_toFun := continuous_completionAdicRingEquiv F p _ hP
  continuous_invFun := continuous_completionAdicRingEquiv_symm F p _ hP

private theorem completionEquivAdicCompletionOfValuationEq_apply (x : P.Completion) :
    completionEquivAdicCompletionOfValuationEq k F p P hP x =
      completionAdicRingEquiv F p _ hP x := rfl

/-- The comparison carries the intrinsic field embedding to the adic field embedding. -/
@[simp]
theorem completionEquivAdicCompletionOfValuationEq_completionEmbedding (x : F) :
    completionEquivAdicCompletionOfValuationEq k F p P hP (P.completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x := by
  rw [completionEquivAdicCompletionOfValuationEq_apply, completionEmbedding_apply,
    completionAdicRingEquiv_embedding]

/-- The comparison preserves the normalized valuation on completed functions. -/
@[simp]
theorem valuation_completionEquivAdicCompletionOfValuationEq (x : P.Completion) :
    Valued.v (completionEquivAdicCompletionOfValuationEq k F p P hP x) =
      P.completionPlace.valuation x := by
  rw [completionEquivAdicCompletionOfValuationEq_apply, completionPlace_valuation]
  exact valuation_completionAdicRingEquiv F p _ hP x

/-- The comparison preserves uniformizers for the normalized completed valuations. -/
@[simp]
theorem isUniformizer_completionEquivAdicCompletionOfValuationEq_iff (x : P.Completion) :
    (Valued.v : Valuation (p.adicCompletion F) ℤᵐ⁰).IsUniformizer
        (completionEquivAdicCompletionOfValuationEq k F p P hP x) ↔
      P.completionPlace.valuation.IsUniformizer x := by
  rw [TauCeti.isUniformizer_adicCompletion_iff, Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      P.completionPlace.valuation_surjective,
    valuation_completionEquivAdicCompletionOfValuationEq]; rfl

/-- The field comparison identifies the two rings of integers. -/
@[simp]
theorem completionEquivAdicCompletionOfValuationEq_mem_integers_iff (x : P.Completion) :
    completionEquivAdicCompletionOfValuationEq k F p P hP x ∈ p.adicCompletionIntegers F ↔
      x ∈ P.completionPlace.integers := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    valuation_completionEquivAdicCompletionOfValuationEq, mem_integers_iff]

/-- The ring equivalence of completed valuation rings induced by
`completionEquivAdicCompletionOfValuationEq`, requiring no `k`-algebra structure on `R`. -/
def completionIntegersRingEquivAdicCompletionIntegersOfValuationEq :
    P.completionPlace.integers ≃+* p.adicCompletionIntegers F :=
  (completionEquivAdicCompletionOfValuationEq k F p P hP).toAlgEquiv.toRingEquiv.restrict
    P.completionPlace.integers (p.adicCompletionIntegers F)
    fun x ↦ (completionEquivAdicCompletionOfValuationEq_mem_integers_iff k F p P hP x).symm

/-- `completionIntegersRingEquivAdicCompletionIntegersOfValuationEq` is the restriction of
`completionEquivAdicCompletionOfValuationEq`. -/
@[simp]
theorem completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply
    (x : P.completionPlace.integers) :
    (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F p P hP x :
        p.adicCompletion F) = completionEquivAdicCompletionOfValuationEq k F p P hP x := (rfl)

/-- `completionIntegersRingEquivAdicCompletionIntegersOfValuationEq` is continuous. -/
theorem continuous_completionIntegersRingEquivAdicCompletionIntegersOfValuationEq :
    Continuous (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F p P hP) :=
  ((completionEquivAdicCompletionOfValuationEq k F p P hP).continuous.comp
    continuous_subtypeVal).subtype_mk _

/-- The inverse of `completionIntegersRingEquivAdicCompletionIntegersOfValuationEq` is
continuous. -/
theorem continuous_completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_symm :
    Continuous (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F p P hP).symm :=
  ((completionEquivAdicCompletionOfValuationEq k F p P hP).symm.continuous.comp
    continuous_subtypeVal).subtype_mk _

end ValuationEq

variable [Algebra k R] [IsScalarTower k R F]

/-- The completion of the adic place is the affine-model adic completion, over the constants. -/
def completionEquivAdicCompletion : (ofPrime k F p).Completion ≃A[k] p.adicCompletion F :=
  completionEquivAdicCompletionOfValuationEq k F p (ofPrime k F p) (valuation_ofPrime k F p)

/-- The comparison carries the intrinsic field embedding to the adic field embedding. -/
@[simp]
theorem completionEquivAdicCompletion_completionEmbedding (x : F) :
    completionEquivAdicCompletion k F p ((ofPrime k F p).completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x :=
  completionEquivAdicCompletionOfValuationEq_completionEmbedding k F p (ofPrime k F p)
    (valuation_ofPrime k F p) x

/-- The comparison preserves the normalized valuation on completed functions. -/
@[simp]
theorem valuation_completionEquivAdicCompletion (x : (ofPrime k F p).Completion) :
    Valued.v (completionEquivAdicCompletion k F p x) =
      (ofPrime k F p).completionPlace.valuation x :=
  valuation_completionEquivAdicCompletionOfValuationEq k F p (ofPrime k F p)
    (valuation_ofPrime k F p) x

/-- The comparison preserves uniformizers for the normalized completed valuations. -/
@[simp]
theorem isUniformizer_completionEquivAdicCompletion_iff (x : (ofPrime k F p).Completion) :
    (Valued.v : Valuation (p.adicCompletion F) ℤᵐ⁰).IsUniformizer
        (completionEquivAdicCompletion k F p x) ↔
      (ofPrime k F p).completionPlace.valuation.IsUniformizer x :=
  isUniformizer_completionEquivAdicCompletionOfValuationEq_iff k F p (ofPrime k F p)
    (valuation_ofPrime k F p) x

/-- The field comparison identifies the two rings of integers. -/
@[simp]
theorem completionEquivAdicCompletion_mem_integers_iff (x : (ofPrime k F p).Completion) :
    completionEquivAdicCompletion k F p x ∈ p.adicCompletionIntegers F ↔
      x ∈ (ofPrime k F p).completionPlace.integers :=
  completionEquivAdicCompletionOfValuationEq_mem_integers_iff k F p (ofPrime k F p)
    (valuation_ofPrime k F p) x

/-- The continuous restriction of the completion comparison to the two valuation rings,
over the constants. -/
def completionIntegersEquivAdicCompletionIntegers :
    (ofPrime k F p).completionPlace.integers ≃A[k] p.adicCompletionIntegers F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F p (ofPrime k F p)
      (valuation_ofPrime k F p)) fun c ↦ by
    apply Subtype.ext
    simp only [completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply,
      coe_algebraMap_constants]
    rw [← ContinuousAlgEquiv.coe_toAlgEquiv,
      (completionEquivAdicCompletionOfValuationEq k F p (ofPrime k F p)
        (valuation_ofPrime k F p)).toAlgEquiv.commutes,
      IsScalarTower.algebraMap_apply k R (p.adicCompletionIntegers F),
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      ← IsScalarTower.algebraMap_apply k R F]
  continuous_toFun :=
    continuous_completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F p (ofPrime k F p)
      (valuation_ofPrime k F p)
  continuous_invFun :=
    continuous_completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_symm k F p
      (ofPrime k F p) (valuation_ofPrime k F p)

/-- The valuation-ring comparison is the restriction of the field comparison. -/
@[simp]
theorem completionIntegersEquivAdicCompletionIntegers_apply
    (x : (ofPrime k F p).completionPlace.integers) :
    (completionIntegersEquivAdicCompletionIntegers k F p x : p.adicCompletion F) =
      completionEquivAdicCompletion k F p x := (rfl)

/-- The valuation-ring comparison carries completed model elements to their adic images. -/
@[simp]
theorem completionIntegersEquivAdicCompletionIntegers_completionIntegersEmbedding_algebraMap
    (r : R) :
    completionIntegersEquivAdicCompletionIntegers k F p
        ((ofPrime k F p).completionIntegersEmbedding (algebraMap R (ofPrime k F p).integers r)) =
      algebraMap R (p.adicCompletionIntegers F) r := by
  apply Subtype.ext
  rw [completionIntegersEquivAdicCompletionIntegers_apply, completionIntegersEmbedding_apply,
    ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply R _ F,
    completionEquivAdicCompletion_completionEmbedding]
  exact p.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (K := F) r

/-- The completed residue fields agree under the valuation-ring comparison. -/
def completionResidueFieldEquivAdicCompletionIntegers :
    (ofPrime k F p).completionPlace.ResidueField ≃ₐ[k]
      IsLocalRing.ResidueField (p.adicCompletionIntegers F) :=
  IsLocalRing.ResidueField.mapAlgEquiv
    (completionIntegersEquivAdicCompletionIntegers k F p).toAlgEquiv

/-- Both residue comparison routes agree on each affine-model representative. -/
theorem completionResidueFieldEquivAdicCompletionIntegers_apply_algebraMap
    (r : R) :
    completionResidueFieldEquivAdicCompletionIntegers k F p
        ((ofPrime k F p).residueFieldEquivCompletion
          (algebraMap R (ofPrime k F p).ResidueField r)) =
      residueFieldAlgEquivAdicCompletionIntegers (K := F) k (v := p)
        (Ideal.Quotient.mk p.asIdeal r) := by
  rw [algebraMap_residueField, residueFieldEquivCompletion_apply_residue]
  simp only [completionResidueFieldEquivAdicCompletionIntegers,
    IsLocalRing.ResidueField.mapAlgEquiv_residue, ContinuousAlgEquiv.coe_toAlgEquiv,
    completionIntegersEquivAdicCompletionIntegers_completionIntegersEmbedding_algebraMap]
  rw [residueFieldAlgEquivAdicCompletionIntegers_apply]
  exact (p.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r).symm

/-- The affine-model residue equivalence is the composite of `quotientAlgEquivResidueFieldOfPrime`,
`residueFieldEquivCompletion`, and `completionResidueFieldEquivAdicCompletionIntegers`. -/
theorem residueFieldAlgEquivAdicCompletionIntegers_eq_trans :
    residueFieldAlgEquivAdicCompletionIntegers (K := F) k (v := p) =
      (quotientAlgEquivResidueFieldOfPrime k F p).trans
        ((ofPrime k F p).residueFieldEquivCompletion.trans
          (completionResidueFieldEquivAdicCompletionIntegers k F p)) := by
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa only [AlgEquiv.trans_apply, quotientAlgEquivResidueFieldOfPrime_mk] using
    (completionResidueFieldEquivAdicCompletionIntegers_apply_algebraMap k F p r).symm

end SinglePlace

section Extension

variable {k k' F F' R B : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
  [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra R F'] [IsScalarTower R F F']
  [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra B F'] [IsFractionRing B F']
  [IsScalarTower R B F']
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
  (hv : P.valuation = v.valuation F) (hw : P'.valuation = w.valuation F')

/-- `completionEquivAdicCompletionOfValuationEq` intertwines `Place.completionExtension` with
`HeightOneSpectrum.adicCompletionExtension`, even when the constant field grows. -/
theorem completionEquivAdicCompletionOfValuationEq_completionExtension (x : P.Completion) :
    completionEquivAdicCompletionOfValuationEq k' F' w P' hw (P.completionExtension P' hP x) =
      v.adicCompletionExtension F F' w
        (completionEquivAdicCompletionOfValuationEq k F v P hv x) := by
  let eK := completionEquivAdicCompletionOfValuationEq k F v P hv
  let eL := completionEquivAdicCompletionOfValuationEq k' F' w P' hw
  have hf : eL.symm.toRingEquiv.toRingHom.comp
      ((v.adicCompletionExtension F F' w).comp eK.toRingEquiv.toRingHom) =
      P.completionExtension P' hP :=
    P.eq_completionExtension_of_continuous P' hP
      (eL.symm.continuous.comp ((v.continuous_adicCompletionExtension F F' w).comp eK.continuous))
      fun y ↦ by
        simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
          ContinuousAlgEquiv.coe_toAlgEquiv, RingHom.coe_coe, Function.comp_apply, eK, eL,
          completionEquivAdicCompletionOfValuationEq_completionEmbedding]
        rw [eL.symm_apply_eq]
        simp [eL, HeightOneSpectrum.algebraMap_adicCompletion,
          HeightOneSpectrum.adicCompletionExtension_coe]
  exact ((RingEquiv.symm_apply_eq eL.toRingEquiv).mp (congrArg (fun g : _ →+* _ ↦ g x) hf)).symm

open scoped AdicCompletionExtension in
/-- Naturality of `completionEquivAdicCompletionOfValuationEq` with `completionExtensionAlgebra`
and `adicCompletionExtensionAlgebra`. -/
theorem algebraMap_comp_completionEquivAdicCompletionOfValuationEq :
    letI := P.completionExtensionAlgebra P' hP
    (algebraMap (v.adicCompletion F) (w.adicCompletion F')).comp
        (completionEquivAdicCompletionOfValuationEq k F v P hv).toAlgEquiv.toRingEquiv.toRingHom =
      (completionEquivAdicCompletionOfValuationEq
        k' F' w P' hw).toAlgEquiv.toRingEquiv.toRingHom.comp
        (algebraMap P.Completion P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  refine RingHom.ext fun x ↦ ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
    ContinuousAlgEquiv.coe_toAlgEquiv, RingHom.coe_coe, P.algebraMap_completionExtensionAlgebra,
    v.algebraMap_adicCompletionExtensionAlgebra (K := F) (L := F')]
  exact (completionEquivAdicCompletionOfValuationEq_completionExtension v w P P' hP hv hw x).symm

end Extension

end TauCeti.Place

end
