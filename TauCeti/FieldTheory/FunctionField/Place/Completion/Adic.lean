/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Extension
public import TauCeti.FieldTheory.FunctionField.Place.Adic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension

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

More generally, whenever a place `P` of `F / k` has the same normalized valuation as a
height-one prime `p` of a Dedekind model `R` of `F` (with no `k`-algebra structure assumed on
`R`), `TauCeti.Place.completionRingEquivAdicCompletion` and
`TauCeti.Place.completionIntegersRingEquivAdicCompletionIntegers` identify `P.Completion` and
`P.completionPlace.integers` with `p.adicCompletion F` and `p.adicCompletionIntegers F`,
compatibly with field extensions (`TauCeti.Place.completionExtension` and
`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`).

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

section RingEquiv

variable {k F R : Type*} [Field k] [Field F] [CommRing R] [IsDedekindDomain R]
  [Algebra k F] [Algebra R F] [IsFractionRing R F]

-- The equality parameter transports the valued and uniform structures from the adic valuation
-- to an equal place valuation, without unfolding the dependent place-completion carrier.
private def completionAdicRingEquiv (p : HeightOneSpectrum R) (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) : v.Completion ≃+* p.adicCompletion F :=
  hv.symm ▸ (HeightOneSpectrum.adicCompletion.equiv F p).symm

private theorem completionAdicRingEquiv_embedding (p : HeightOneSpectrum R) (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) (x : F) :
    completionAdicRingEquiv p v hv
        ((WithVal.toVal v x : WithVal v) : v.Completion) =
      algebraMap F (p.adicCompletion F) x := by
  subst v
  rw [completionAdicRingEquiv, RingEquiv.symm_apply_eq]
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

private theorem continuous_completionAdicRingEquiv (p : HeightOneSpectrum R) (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) : Continuous (completionAdicRingEquiv p v hv) := by
  subst v
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv F p).symm.continuous

private theorem continuous_completionAdicRingEquiv_symm (p : HeightOneSpectrum R)
    (v : Valuation F ℤᵐ⁰) (hv : v = p.valuation F) :
    Continuous (completionAdicRingEquiv p v hv).symm := by
  subst v
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv F p).continuous

private theorem valuation_completionAdicRingEquiv (p : HeightOneSpectrum R) (v : Valuation F ℤᵐ⁰)
    (hv : v = p.valuation F) (y : v.Completion) :
    Valued.v (completionAdicRingEquiv p v hv y) = Valued.v y := by
  subst v
  exact HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply F p y

/-- **Comparison of a place completion with an affine-model adic completion** when their
normalized valuations agree, requiring no `k`-algebra structure on the Dedekind model `R`. -/
def completionRingEquivAdicCompletion (P : Place k F) (p : HeightOneSpectrum R)
    (hP : P.valuation = p.valuation F) : P.Completion ≃+* p.adicCompletion F :=
  completionAdicRingEquiv p P.valuation hP

/-- `completionRingEquivAdicCompletion` is continuous. -/
theorem continuous_completionRingEquivAdicCompletion (P : Place k F) (p : HeightOneSpectrum R)
    (hP : P.valuation = p.valuation F) :
    Continuous (P.completionRingEquivAdicCompletion p hP) :=
  continuous_completionAdicRingEquiv p P.valuation hP

/-- The inverse of `completionRingEquivAdicCompletion` is continuous. -/
theorem continuous_completionRingEquivAdicCompletion_symm (P : Place k F) (p : HeightOneSpectrum R)
    (hP : P.valuation = p.valuation F) :
    Continuous (P.completionRingEquivAdicCompletion p hP).symm :=
  continuous_completionAdicRingEquiv_symm p P.valuation hP

/-- `completionRingEquivAdicCompletion` carries the intrinsic field embedding to `algebraMap`. -/
@[simp]
theorem completionRingEquivAdicCompletion_completionEmbedding (P : Place k F)
    (p : HeightOneSpectrum R) (hP : P.valuation = p.valuation F) (x : F) :
    P.completionRingEquivAdicCompletion p hP (P.completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x := by
  rw [completionRingEquivAdicCompletion, completionEmbedding_apply,
    completionAdicRingEquiv_embedding]

/-- `completionRingEquivAdicCompletion` preserves the normalized completed valuation. -/
@[simp]
theorem valuation_completionRingEquivAdicCompletion (P : Place k F) (p : HeightOneSpectrum R)
    (hP : P.valuation = p.valuation F) (x : P.Completion) :
    Valued.v (P.completionRingEquivAdicCompletion p hP x) = P.completionPlace.valuation x := by
  rw [completionRingEquivAdicCompletion, completionPlace_valuation]
  exact valuation_completionAdicRingEquiv p P.valuation hP x

/-- `completionRingEquivAdicCompletion` identifies the completed valuation rings. -/
@[simp]
theorem completionRingEquivAdicCompletion_mem_integers_iff (P : Place k F)
    (p : HeightOneSpectrum R) (hP : P.valuation = p.valuation F) (x : P.Completion) :
    P.completionRingEquivAdicCompletion p hP x ∈ p.adicCompletionIntegers F ↔
      x ∈ P.completionPlace.integers := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valuation_completionRingEquivAdicCompletion,
    mem_integers_iff]

/-- **Comparison of completed valuation rings** when the place valuation equals `p.valuation F`,
requiring no `k`-algebra structure on `R`. -/
def completionIntegersRingEquivAdicCompletionIntegers (P : Place k F) (p : HeightOneSpectrum R)
    (hP : P.valuation = p.valuation F) :
    P.completionPlace.integers ≃+* p.adicCompletionIntegers F :=
  (P.completionRingEquivAdicCompletion p hP).restrict
    P.completionPlace.integers (p.adicCompletionIntegers F)
    fun x ↦ (P.completionRingEquivAdicCompletion_mem_integers_iff p hP x).symm

/-- `completionIntegersRingEquivAdicCompletionIntegers` restricts the field equivalence. -/
@[simp]
theorem coe_completionIntegersRingEquivAdicCompletionIntegers (P : Place k F)
    (p : HeightOneSpectrum R) (hP : P.valuation = p.valuation F)
    (x : P.completionPlace.integers) :
    (P.completionIntegersRingEquivAdicCompletionIntegers p hP x : p.adicCompletion F) =
      P.completionRingEquivAdicCompletion p hP x := (rfl)

/-- `completionIntegersRingEquivAdicCompletionIntegers` sends completed model elements to their
adic images. -/
theorem completionIntegersRingEquivAdicCompletionIntegers_completionIntegersEmbedding
    (P : Place k F) (p : HeightOneSpectrum R) (hP : P.valuation = p.valuation F)
    {r : R} (hr : algebraMap R F r ∈ P.integers) :
    P.completionIntegersRingEquivAdicCompletionIntegers p hP
        (P.completionIntegersEmbedding ⟨algebraMap R F r, hr⟩) =
      algebraMap R (p.adicCompletionIntegers F) r := by
  apply Subtype.ext
  rw [coe_completionIntegersRingEquivAdicCompletionIntegers, completionIntegersEmbedding_apply,
    completionRingEquivAdicCompletion_completionEmbedding]
  exact p.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (K := F) r

end RingEquiv

section AlgEquiv

variable (k F : Type*) {R : Type*} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F] (p : HeightOneSpectrum R)

/-- The completion of a place with the affine model's valuation is its adic completion,
over the constants. The equality transports the dependent completion structures. -/
def completionEquivAdicCompletionOfValuationEq (P : Place k F)
    (hP : P.valuation = p.valuation F) : P.Completion ≃A[k] p.adicCompletion F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := P.completionRingEquivAdicCompletion p hP) fun c ↦ by
      rw [← P.completionEmbedding.commutes,
        P.completionRingEquivAdicCompletion_completionEmbedding p hP,
        ← IsScalarTower.algebraMap_apply k F _]
  continuous_toFun := P.continuous_completionRingEquivAdicCompletion p hP
  continuous_invFun := P.continuous_completionRingEquivAdicCompletion_symm p hP

/-- The completion of the adic place is the affine-model adic completion, over the constants. -/
def completionEquivAdicCompletion : (ofPrime k F p).Completion ≃A[k] p.adicCompletion F :=
  completionEquivAdicCompletionOfValuationEq k F p (ofPrime k F p) (valuation_ofPrime k F p)

private theorem completionEquivAdicCompletion_apply (x : (ofPrime k F p).Completion) :
    completionEquivAdicCompletion k F p x =
      (ofPrime k F p).completionRingEquivAdicCompletion p (valuation_ofPrime k F p) x := (rfl)

/-- The comparison carries the intrinsic field embedding to the adic field embedding. -/
@[simp]
theorem completionEquivAdicCompletion_completionEmbedding (x : F) :
    completionEquivAdicCompletion k F p ((ofPrime k F p).completionEmbedding x) =
      algebraMap F (p.adicCompletion F) x :=
  (ofPrime k F p).completionRingEquivAdicCompletion_completionEmbedding p
    (valuation_ofPrime k F p) x

/-- The comparison preserves the normalized valuation on completed functions. -/
@[simp]
theorem valuation_completionEquivAdicCompletion (x : (ofPrime k F p).Completion) :
    Valued.v (completionEquivAdicCompletion k F p x) =
      (ofPrime k F p).completionPlace.valuation x :=
  (ofPrime k F p).valuation_completionRingEquivAdicCompletion p (valuation_ofPrime k F p) x

/-- The comparison preserves uniformizers for the normalized completed valuations. -/
@[simp]
theorem isUniformizer_completionEquivAdicCompletion_iff (x : (ofPrime k F p).Completion) :
    (Valued.v : Valuation (p.adicCompletion F) ℤᵐ⁰).IsUniformizer
        (completionEquivAdicCompletion k F p x) ↔
      (ofPrime k F p).completionPlace.valuation.IsUniformizer x := by
  rw [TauCeti.isUniformizer_adicCompletion_iff, Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (ofPrime k F p).completionPlace.valuation_surjective,
    valuation_completionEquivAdicCompletion]
  rfl

/-- The field comparison identifies the two rings of integers. -/
@[simp]
theorem completionEquivAdicCompletion_mem_integers_iff (x : (ofPrime k F p).Completion) :
    completionEquivAdicCompletion k F p x ∈ p.adicCompletionIntegers F ↔
      x ∈ (ofPrime k F p).completionPlace.integers :=
  (ofPrime k F p).completionRingEquivAdicCompletion_mem_integers_iff p
    (valuation_ofPrime k F p) x

/-- The continuous restriction of the completion comparison to the two valuation rings,
over the constants. -/
def completionIntegersEquivAdicCompletionIntegers :
    (ofPrime k F p).completionPlace.integers ≃A[k] p.adicCompletionIntegers F where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := (ofPrime k F p).completionIntegersRingEquivAdicCompletionIntegers p
      (valuation_ofPrime k F p)) fun c ↦ by
    apply Subtype.ext
    simp only [coe_completionIntegersRingEquivAdicCompletionIntegers, coe_algebraMap_constants]
    rw [← completionEquivAdicCompletion_apply,
      AlgEquivClass.commutes (completionEquivAdicCompletion k F p),
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
    (x : (ofPrime k F p).completionPlace.integers) :
    (completionIntegersEquivAdicCompletionIntegers k F p x : p.adicCompletion F) =
      completionEquivAdicCompletion k F p x := (rfl)

/-- The valuation-ring comparison carries completed model elements to their adic images. -/
@[simp]
theorem completionIntegersEquivAdicCompletionIntegers_completionIntegersEmbedding_algebraMap
    (r : R) :
    completionIntegersEquivAdicCompletionIntegers k F p
        ((ofPrime k F p).completionIntegersEmbedding (algebraMap R (ofPrime k F p).integers r)) =
      algebraMap R (p.adicCompletionIntegers F) r :=
  (ofPrime k F p).completionIntegersRingEquivAdicCompletionIntegers_completionIntegersEmbedding p
    (valuation_ofPrime k F p) (algebraMap_mem_integers_ofPrime k F p r)

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

end AlgEquiv

section Extension

variable {k k' F F' R B : Type*} [Field k] [Field k'] [Field F] [Field F']
  [CommRing R] [CommRing B] [IsDedekindDomain R] [IsDedekindDomain B]
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra R B] [Algebra R F] [IsFractionRing R F]
  [Algebra B F'] [IsFractionRing B F'] [Algebra R F']
  [IsScalarTower R F F'] [IsScalarTower R B F']
  [Algebra.IsIntegral F F']

/-- **The intrinsic and adic field-completion extensions commute** under the valuation-ring
comparisons at `v` and `w`. -/
theorem completionRingEquivAdicCompletion_completionExtension
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (hv : P.valuation = v.valuation F) (hw : P'.valuation = w.valuation F')
    (x : P.Completion) :
    P'.completionRingEquivAdicCompletion w hw (P.completionExtension P' hP x) =
      v.adicCompletionExtension F F' w (P.completionRingEquivAdicCompletion v hv x) := by
  let f : P.Completion →+* P'.Completion :=
    ((P'.completionRingEquivAdicCompletion w hw).symm : w.adicCompletion F' →+* P'.Completion).comp
      ((v.adicCompletionExtension F F' w).comp
        (P.completionRingEquivAdicCompletion v hv : P.Completion →+* v.adicCompletion F))
  have hf : f = P.completionExtension P' hP := by
    refine P.eq_completionExtension_of_continuous P' hP
      ((P'.continuous_completionRingEquivAdicCompletion_symm w hw).comp
        ((v.continuous_adicCompletionExtension F F' w).comp
          (P.continuous_completionRingEquivAdicCompletion v hv))) fun y ↦ ?_
    apply (P'.completionRingEquivAdicCompletion w hw).injective
    simp only [f, RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply,
      completionRingEquivAdicCompletion_completionEmbedding]
    exact v.adicCompletionExtension_coe F F' w y
  simpa only [f, RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] using
    congrArg (P'.completionRingEquivAdicCompletion w hw) (RingHom.congr_fun hf.symm x)

/-- **The intrinsic and adic valuation-ring completion extensions commute** under the
valuation-ring comparisons at `v` and `w`. -/
theorem completionIntegersRingEquivAdicCompletionIntegers_completionIntegersExtension
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (hv : P.valuation = v.valuation F) (hw : P'.valuation = w.valuation F')
    (x : P.completionPlace.integers) :
    P'.completionIntegersRingEquivAdicCompletionIntegers w hw
        (P.completionIntegersExtension P' hP x) =
      v.adicCompletionIntegersExtension F F' w
        (P.completionIntegersRingEquivAdicCompletionIntegers v hv x) := by
  apply Subtype.ext
  simp only [coe_completionIntegersRingEquivAdicCompletionIntegers, coe_completionIntegersExtension,
    HeightOneSpectrum.coe_adicCompletionIntegersExtension]
  exact P.completionRingEquivAdicCompletion_completionExtension P' hP v w hv hw x

end Extension

end TauCeti.Place
