/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Different.Localization
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Adic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
public import TauCeti.RingTheory.DedekindDomain.Different.Completion

/-!
# The different and its length formula under completion at a place

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is finite and
separable, and let `P'` be a place of `F' / k'` lying over `P = P'.restrict k F` in `F / k`, with
completed extension `F̂_P → F̂'_{P'}` and completed valuation rings `𝒪̂_P ⊆ 𝒪̂_{P'}`. Neither `k`
nor the residue fields are assumed perfect or finite: an inseparable residue extension is allowed
and contributes its full degree `f(P' ∣ P) = relativeDegree k F P'`.

Even when the residue extension `F'_{P'} / F_P` is inseparable — so `𝒪̂_{P'}` need not be monogenic
over `𝒪̂_P` and need not admit a `k`-linear coefficient field — passing to the completion preserves
every local different invariant. The proof transports the adic completion theorems of
`TauCeti.RingTheory.DedekindDomain.Different.Completion` from the local Dedekind model
`𝒪_P ⊆ integralClosure 𝒪_P F'` at `centerIntegralClosure k F P'` along the monogenicity-free
comparison `TauCeti.Place.completionRingEquivAdicCompletion`.

## Main definitions

* `TauCeti.Place.integralClosureToCompletionIntegers`: the canonical ring homomorphism from the
  local model `integralClosure 𝒪_P F'` into the completed valuation ring `𝒪̂_{P'}`.

## Main results

* `TauCeti.Place.isIntegralClosure_completionIntegers` and `TauCeti.Place.isSeparable_completion`:
  `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂'_{P'}`, and `F̂'_{P'} / F̂_P` is separable.
* `TauCeti.Place.traceDual_one_completionIntegers_eq_span` and
  `TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`: the completed complementary
  module `Ĉ_{P'} = Submodule.traceDual 𝒪̂_P F̂_P 1` is spanned over `𝒪̂_{P'}` by the image of the
  local-model complementary module `C_P`, and consists of the completed elements of valuation at
  most `exp d(P' ∣ P)` with no global function-field hypothesis.
* `TauCeti.Place.differentIdeal_completionIntegers_eq_map`,
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers`, and
  `TauCeti.Place.differentIdeal_completionIntegers_eq_maximalIdeal_pow`: the local-model different
  ideal extends to `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`.
* `TauCeti.Place.length_traceDual_quotient_completionIntegers`,
  `TauCeti.Place.ord_discr_completionIntegers`, and
  `TauCeti.Place.length_traceDual_quotient_completionIntegers_eq_length`: the `𝒪̂_P`-length of
  `Ĉ_{P'} / 𝒪̂_{P'}` and the `𝒪̂_P`-order of the discriminant of any `𝒪̂_P`-basis of `𝒪̂_{P'}` both
  equal `d(P' ∣ P) · f(P' ∣ P)`, agreeing with the uncompleted length when `integralClosure 𝒪_P F'`
  is local.
* `TauCeti.Place.restrict_completionPlace`, `TauCeti.Place.ramificationIdx_completionPlace`,
  `TauCeti.Place.relativeDegree_completionPlace`, and
  `TauCeti.Place.differentExponent_completionPlace`: when `F` and `F'` share the constant field `k`,
  `P'.completionPlace` lies over `P.completionPlace` with the same ramification index, relative
  degree, and `differentExponent`.

## References

* [J.-P. Serre, *Local Fields*][serre1968], Chapter III, §§3–4.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], Section III.4.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing Module
open scoped WithZero AdicCompletionExtension nonZeroDivisors

namespace TauCeti.Place

section IntegralExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)

/-- The map of completed valuation rings is injective. -/
theorem completionIntegersExtension_injective :
    Function.Injective (P.completionIntegersExtension P' hP) := by
  intro x y h
  apply Subtype.ext
  apply (P.completionExtension P' hP).injective
  simpa only [coe_completionIntegersExtension] using congrArg Subtype.val h

/-- `𝒪̂_{P'}` is torsion-free over `𝒪̂_P`. -/
theorem isTorsionFree_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let := P.completionIntegersExtensionAlgebra P' hP
  have : FaithfulSMul P.completionPlace.integers P'.completionPlace.integers := by
    rw [faithfulSMul_iff_algebraMap_injective,
      P.algebraMap_completionIntegersExtensionAlgebra P' hP]
    exact P.completionIntegersExtension_injective P' hP
  infer_instance

/-- The completed valuation rings and upper completed field form a scalar tower. -/
theorem isScalarTower_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    ValuationSubring.algebraMap_apply, P.algebraMap_completionExtensionAlgebra P' hP,
    ValuationSubring.algebraMap_apply, P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP]

/-- **The completed valuation ring `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂'_{P'}`**
whenever the residue extension is finite (in particular whenever `F' / F` is finite), with no
separability assumption on `F' / F` or on the residue fields. -/
theorem isIntegralClosure_completionIntegers
    [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField] :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := moduleFinite_completionIntegers P P' hP
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

end IntegralExtension

section FiniteSeparable

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- The centre of `P'.restrict k F` on the local model `𝒪_P`. -/
private def centerRestrict (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra.IsIntegral F F'] (P' : Place k' F') :
    HeightOneSpectrum (P'.restrict k F).integers :=
  (P'.restrict k F).center (algebraMap_mem_integers_restrict k F P'
    (algebraMap_mem_integers_of_mem_integralClosure k F P'))

private instance centerIntegralClosure_liesOver_centerRestrict (P' : Place k' F') :
    (centerIntegralClosure k F P').asIdeal.LiesOver (centerRestrict k F P').asIdeal := by
  rw [centerIntegralClosure_def, centerRestrict]
  exact center_liesOver k F P' (algebraMap_mem_integers_of_mem_integralClosure k F P')

private theorem valuation_eq_centerRestrict (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra.IsIntegral F F'] (P' : Place k' F') :
    (P'.restrict k F).valuation = (centerRestrict k F P').valuation F :=
  ((P'.restrict k F).valuation_center _).symm

private theorem valuation_eq_centerIntegralClosure (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P' : Place k' F') :
    P'.valuation = (centerIntegralClosure k F P').valuation F' := by
  rw [centerIntegralClosure_def]
  exact (P'.valuation_center (algebraMap_mem_integers_of_mem_integralClosure k F P')).symm

private theorem completionComparison_hAK (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra.IsIntegral F F'] (P' : Place k' F') :
    (algebraMap ((centerRestrict k F P').adicCompletionIntegers F)
        ((centerRestrict k F P').adicCompletion F)).comp
      ((P'.restrict k F).completionIntegersRingEquivAdicCompletionIntegers (centerRestrict k F P')
        (valuation_eq_centerRestrict k F P') :
        (P'.restrict k F).completionPlace.integers →+* _) =
    ((P'.restrict k F).completionRingEquivAdicCompletion (centerRestrict k F P')
        (valuation_eq_centerRestrict k F P') :
        (P'.restrict k F).Completion →+* _).comp
      (algebraMap (P'.restrict k F).completionPlace.integers (P'.restrict k F).Completion) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe, ValuationSubring.algebraMap_apply,
    coe_completionIntegersRingEquivAdicCompletionIntegers]

private theorem completionComparison_hKL (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P' : Place k' F') :
    letI := (P'.restrict k F).completionExtensionAlgebra P' rfl
    (algebraMap ((centerRestrict k F P').adicCompletion F)
        ((centerIntegralClosure k F P').adicCompletion F')).comp
      ((P'.restrict k F).completionRingEquivAdicCompletion (centerRestrict k F P')
        (valuation_eq_centerRestrict k F P') :
        (P'.restrict k F).Completion →+* _) =
    (P'.completionRingEquivAdicCompletion (centerIntegralClosure k F P')
        (valuation_eq_centerIntegralClosure k F P') :
        P'.Completion →+* _).comp
      (algebraMap (P'.restrict k F).Completion P'.Completion) := by
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, RingHom.coe_coe, algebraMap_completionExtensionAlgebra,
    HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
  exact ((P'.restrict k F).completionRingEquivAdicCompletion_completionExtension P' rfl
    (centerRestrict k F P') (centerIntegralClosure k F P')
    (valuation_eq_centerRestrict k F P') (valuation_eq_centerIntegralClosure k F P') x).symm

private theorem completionComparison_hBL (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P' : Place k' F') :
    (algebraMap ((centerIntegralClosure k F P').adicCompletionIntegers F')
        ((centerIntegralClosure k F P').adicCompletion F')).comp
      (P'.completionIntegersRingEquivAdicCompletionIntegers (centerIntegralClosure k F P')
        (valuation_eq_centerIntegralClosure k F P') :
        P'.completionPlace.integers →+* _) =
    (P'.completionRingEquivAdicCompletion (centerIntegralClosure k F P')
        (valuation_eq_centerIntegralClosure k F P') :
        P'.Completion →+* _).comp
      (algebraMap P'.completionPlace.integers P'.Completion) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe, ValuationSubring.algebraMap_apply,
    coe_completionIntegersRingEquivAdicCompletionIntegers]

/-- **Completion preserves separability of the field extension** at any place `P' ∣ P`, with no
assumption on the residue fields. -/
theorem isSeparable_completion (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  have := (centerRestrict k F P').adicCompletion_isSeparable F
    (integralClosure (P'.restrict k F).integers F') F' (centerIntegralClosure k F P')
  exact (Algebra.IsSeparable.iff_of_equiv_equiv
    ((P'.restrict k F).completionRingEquivAdicCompletion (centerRestrict k F P')
      (valuation_eq_centerRestrict k F P'))
    (P'.completionRingEquivAdicCompletion (centerIntegralClosure k F P')
      (valuation_eq_centerIntegralClosure k F P'))
    (completionComparison_hKL k F P')).mpr this

/-- **The completed complementary module is spanned over `𝒪̂_{P'}` by the local-model complementary
module**, even when the residue field at `P'` is inseparable. -/
theorem traceDual_one_completionIntegers_eq_span (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) =
      Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F')) := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  set v := centerRestrict k F P'
  set w := centerIntegralClosure k F P'
  let eL := P'.completionRingEquivAdicCompletion w (valuation_eq_centerIntegralClosure k F P')
  let eB := P'.completionIntegersRingEquivAdicCompletionIntegers w
    (valuation_eq_centerIntegralClosure k F P')
  let S := Submodule.traceDual (P'.restrict k F).integers F
    (1 : Submodule (integralClosure (P'.restrict k F).integers F') F')
  ext z
  rw [← TauCeti.mem_traceDual_one_iff_of_equiv (completionComparison_hAK k F P')
      (completionComparison_hKL k F P') (completionComparison_hBL k F P'),
    v.traceDual_one_adicCompletionIntegers_eq_span F F' w]
  constructor
  · intro hz
    have key : ∀ y ∈ Submodule.span (w.adicCompletionIntegers F')
        (algebraMap F' (w.adicCompletion F') '' (S : Set F')),
        eL.symm y ∈ Submodule.span P'.completionPlace.integers (P'.completionEmbedding '' S) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨d, hd, rfl⟩
        refine Submodule.subset_span ⟨d, hd, ?_⟩
        rw [RingEquiv.eq_symm_apply]
        exact P'.completionRingEquivAdicCompletion_completionEmbedding w
          (valuation_eq_centerIntegralClosure k F P') d
      · simp
      · intro x₁ x₂ _ _ hx₁ hx₂
        rw [map_add]
        exact add_mem hx₁ hx₂
      · intro c x _ hx
        have hcb : eL (eB.symm c : P'.Completion) = (c : w.adicCompletion F') := by
          simpa only [eL, eB, RingEquiv.apply_symm_apply] using
            (P'.coe_completionIntegersRingEquivAdicCompletionIntegers w
              (valuation_eq_centerIntegralClosure k F P') (eB.symm c)).symm
        have hc : eL.symm (c • x) = eB.symm c • eL.symm x := by
          apply eL.injective
          simp only [eL, RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul,
            ValuationSubring.algebraMap_apply, hcb]
        rw [hc]
        exact Submodule.smul_mem _ _ hx
    simpa only [eL, RingEquiv.symm_apply_apply] using key (eL z) hz
  · intro hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨d, hd, rfl⟩
      refine Submodule.subset_span ⟨d, hd, ?_⟩
      exact (P'.completionRingEquivAdicCompletion_completionEmbedding w
        (valuation_eq_centerIntegralClosure k F P') d).symm
    · simp
    · intro x₁ x₂ _ _ hx₁ hx₂
      rw [map_add]
      exact add_mem hx₁ hx₂
    · intro c x _ hx
      have hc : eL (c • x) = eB c • eL x := by
        simp only [eL, eB, Algebra.smul_def, map_mul, ValuationSubring.algebraMap_apply,
          coe_completionIntegersRingEquivAdicCompletionIntegers]
      rw [hc]
      exact Submodule.smul_mem _ _ hx

/-- Canonical ring homomorphism sending the local model `integralClosure 𝒪_P F'` into the
completed valuation ring `𝒪̂_{P'}` via `F' → F̂'_{P'}`. -/
def integralClosureToCompletionIntegers (k F : Type*) [Field k] [Field F]
    [Algebra k F] [Algebra k k'] [Algebra k F'] [Algebra F F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra.IsIntegral F F'] (P' : Place k' F') :
    integralClosure (P'.restrict k F).integers F' →+* P'.completionPlace.integers :=
  (P'.completionIntegersEmbedding : P'.integers →+* P'.completionPlace.integers).comp
    ((algebraMap (integralClosure (P'.restrict k F).integers F') F').codRestrict P'.integers
      (algebraMap_mem_integers_of_mem_integralClosure k F P'))

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
variable [Algebra.IsIntegral F F'] in
/-- Coercion of `integralClosureToCompletionIntegers` to the completed field. -/
@[simp]
theorem coe_integralClosureToCompletionIntegers (P' : Place k' F')
    (b : integralClosure (P'.restrict k F).integers F') :
    (integralClosureToCompletionIntegers k F P' b : P'.Completion) =
      P'.completionEmbedding (algebraMap _ F' b) := by
  simp [integralClosureToCompletionIntegers]

/-- **The different ideal of the local model extends to the completed different ideal**, with no
assumption of residue-field separability or monogenicity. -/
theorem differentIdeal_completionIntegers_eq_map (P' : Place k' F') :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    haveI := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
    differentIdeal (P'.restrict k F).completionPlace.integers P'.completionPlace.integers =
      (differentIdeal (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F')).map
          (integralClosureToCompletionIntegers k F P') := by
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  have := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have := finiteDimensional_completion (P'.restrict k F) P' rfl
  have := isSeparable_completion (P'.restrict k F) P' rfl
  set v := centerRestrict k F P'
  set w := centerIntegralClosure k F P'
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite F F' w
  let eB := P'.completionIntegersRingEquivAdicCompletionIntegers w
    (valuation_eq_centerIntegralClosure k F P')
  have hcomp : (eB : P'.completionPlace.integers →+* w.adicCompletionIntegers F').comp
      (integralClosureToCompletionIntegers k F P') =
      algebraMap (integralClosure (P'.restrict k F).integers F') (w.adicCompletionIntegers F') := by
    apply RingHom.ext
    intro b
    exact P'.completionIntegersRingEquivAdicCompletionIntegers_completionIntegersEmbedding w
      (valuation_eq_centerIntegralClosure k F P')
      (algebraMap_mem_integers_of_mem_integralClosure k F P' b)
  have heq : (differentIdeal (P'.restrict k F).completionPlace.integers
        P'.completionPlace.integers).map
          (eB : P'.completionPlace.integers →+* w.adicCompletionIntegers F') =
      ((differentIdeal (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F')).map
          (integralClosureToCompletionIntegers k F P')).map
            (eB : P'.completionPlace.integers →+* w.adicCompletionIntegers F') := by
    rw [TauCeti.map_differentIdeal_eq_of_equiv (completionComparison_hAK k F P')
        (completionComparison_hKL k F P') (completionComparison_hBL k F P'),
      Ideal.map_map, hcomp, v.differentIdeal_adicCompletionIntegers_eq_map F F' w]
  simpa only [Ideal.map_of_equiv] using
    congrArg (Ideal.map (eB.symm : w.adicCompletionIntegers F' →+* P'.completionPlace.integers)) heq

private theorem multiplicity_ideal_map_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I J : Ideal R) :
    multiplicity (I.map (e : R →+* S)) (J.map (e : R →+* S)) = multiplicity I J :=
  multiplicity_map_eq (f := ({
    toFun := Ideal.map (e : R →+* S)
    invFun := Ideal.map (e.symm : S →+* R)
    left_inv := fun _ ↦ Ideal.map_of_equiv e
    right_inv := fun _ ↦ Ideal.map_of_equiv e.symm
    map_mul' := Ideal.map_mul (e : R →+* S) } : Ideal R ≃* Ideal S))

/-- **The multiplicity of `𝔪̂_{P'}` in the completed different ideal is `differentExponent k F P'`**
even when the residue extension is inseparable. -/
@[simp]
theorem multiplicity_differentIdeal_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    multiplicity (IsLocalRing.maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  have := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have := finiteDimensional_completion (P'.restrict k F) P' rfl
  have := isSeparable_completion (P'.restrict k F) P' rfl
  set v := centerRestrict k F P'
  set w := centerIntegralClosure k F P'
  have := v.adicCompletionIntegers_isIntegralClosure_of_finite F F' w
  let eB := P'.completionIntegersRingEquivAdicCompletionIntegers w
    (valuation_eq_centerIntegralClosure k F P')
  have hmax : (IsLocalRing.maximalIdeal P'.completionPlace.integers).map
      (eB : P'.completionPlace.integers →+* w.adicCompletionIntegers F') =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers F') :=
    IsLocalRing.map_ringEquiv_maximalIdeal eB
  have hdiff : (differentIdeal (P'.restrict k F).completionPlace.integers
      P'.completionPlace.integers).map
      (eB : P'.completionPlace.integers →+* w.adicCompletionIntegers F') =
      differentIdeal (v.adicCompletionIntegers F) (w.adicCompletionIntegers F') :=
    TauCeti.map_differentIdeal_eq_of_equiv (completionComparison_hAK k F P')
      (completionComparison_hKL k F P') (completionComparison_hBL k F P')
  rw [differentExponent_def, ← v.multiplicity_differentIdeal_adicCompletionIntegers F F' w,
    ← hmax, ← hdiff, multiplicity_ideal_map_equiv eB]

/-- **The completed different ideal is `𝔪̂_{P'} ^ differentExponent k F P'`.** -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      IsLocalRing.maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  have h0 : differentIdeal P.completionPlace.integers P'.completionPlace.integers ≠ ⊥ :=
    differentIdeal_ne_bot_of_isSeparable (K := P.Completion) (L := P'.Completion)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P'.completionPlace.integers
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  have hpow : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      IsLocalRing.maximalIdeal P'.completionPlace.integers ^ n := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have hmult : multiplicity (IsLocalRing.maximalIdeal P'.completionPlace.integers)
      (differentIdeal P.completionPlace.integers P'.completionPlace.integers) = n := by
    rw [hpow, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance)]
  rw [← multiplicity_differentIdeal_completionIntegers P P' hP, hmult, hpow]

/-- **Valuation criterion for the completed complementary module**: an element of `F̂'_{P'}` lies in
`Submodule.traceDual 𝒪̂_P F̂_P 1` if and only if its completed valuation is at most
`exp (differentExponent k F P')`. Unlike the global criterion
`TauCeti.Place.mem_traceDual_iff_forall_valuation_le`, no `IsFunctionField` or constant-field
integrality hypothesis is needed. -/
theorem mem_traceDual_completionIntegers_iff_valuation_le (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  obtain ⟨π, hπ0, hπ⟩ := P'.completionPlace.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P'.completionPlace.integers := by
    rw [mem_integers_iff_ord_nonneg, hπ]
    norm_num
  let ϖ : P'.completionPlace.integers := ⟨π, hπint⟩
  have hϖv : P'.completionPlace.valuation π = WithZero.exp (-1) := by
    rw [P'.completionPlace.valuation_eq_exp_neg_ord hπ0, hπ]
  have hmax : IsLocalRing.maximalIdeal P'.completionPlace.integers = Ideal.span {ϖ} := by
    refine le_antisymm (fun x hx ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · rcases eq_or_ne x 0 with rfl | hx0
      · simp
      have hx0' : (x : P'.Completion) ≠ 0 := by simpa using hx0
      have hord : 1 ≤ P'.completionPlace.ord x :=
        (P'.completionPlace.mem_maximalIdeal_iff_ord_pos hx0').mp hx
      have hdiv : (x : P'.Completion) / π ∈ P'.completionPlace.integers := by
        rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div hx0' hπ0, hπ]
        omega
      refine Ideal.mem_span_singleton.mpr ⟨⟨(x : P'.Completion) / π, hdiv⟩, ?_⟩
      apply Subtype.ext
      exact (mul_div_cancel₀ _ hπ0).symm
    · rw [P'.completionPlace.mem_maximalIdeal_iff_ord_pos hπ0, hπ]
      exact zero_lt_one
  have hdiff : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {ϖ ^ differentExponent k F P'} := by
    rw [differentIdeal_completionIntegers_eq_maximalIdeal_pow P P' hP, hmax,
      Ideal.span_singleton_pow]
  rw [TauCeti.mem_traceDual_one_iff_forall_mem_differentIdeal, hdiff]
  set d := differentExponent k F P'
  have hπd : P'.completionPlace.valuation (π ^ d) = WithZero.exp (-(d : ℤ)) := by
    rw [map_pow, hϖv, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp
      (hz (ϖ ^ d) (Ideal.mem_span_singleton_self (ϖ ^ d)))
    have hle : P'.completionPlace.valuation (z * π ^ d) ≤ 1 := by
      have hb' : z * π ^ d = (b : P'.Completion) := by simpa [ϖ] using hb.symm
      rw [hb']
      exact P'.completionPlace.mem_integers_iff.mp b.2
    rw [map_mul, hπd] at hle
    calc P'.completionPlace.valuation z
        = P'.completionPlace.valuation z * WithZero.exp (-(d : ℤ)) * WithZero.exp (d : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (d : ℤ) := by gcongr
      _ = WithZero.exp (d : ℤ) := one_mul _
  · intro hz y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hy
    suffices z * (π ^ d * (c : P'.Completion)) ∈ P'.completionPlace.integers from
      Submodule.mem_one.mpr ⟨⟨_, this⟩, by simp [ϖ]⟩
    rw [mem_integers_iff, map_mul, map_mul, hπd]
    calc P'.completionPlace.valuation z *
          (WithZero.exp (-(d : ℤ)) * P'.completionPlace.valuation (c : P'.Completion))
        ≤ WithZero.exp (d : ℤ) * (WithZero.exp (-(d : ℤ)) * 1) := by
          gcongr
          exact P'.completionPlace.mem_integers_iff.mp c.2
      _ = 1 := by rw [mul_one, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-- **The complementary-module length formula on the completion at a place**: the `𝒪̂_P`-length of
`Ĉ_{P'} / 𝒪̂_{P'}` equals `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P) = relativeDegree k F P'`
includes any inseparable residue factor. -/
theorem length_traceDual_quotient_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    Module.length P.completionPlace.integers
        ((Submodule.traceDual P.completionPlace.integers P.Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual P.completionPlace.integers P.Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  have := moduleFinite_completionIntegers (P'.restrict k F) P' rfl
  have := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have := finiteDimensional_completion (P'.restrict k F) P' rfl
  have := isSeparable_completion (P'.restrict k F) P' rfl
  rw [TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl]
  exact congrArg _ (congrArg Nat.cast (P'.finrank_residueField_completion (k := k) (F := F)))

/-- **The discriminant valuation formula on the completion at a place**: for any `𝒪̂_P`-basis `b`
of `𝒪̂_{P'}`, `ord_{𝒪̂_P}(discr_{𝒪̂_P}(b)) = d(P' ∣ P) · f(P' ∣ P)`, including any inseparable
residue factor. -/
theorem ord_discr_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : letI := P.completionIntegersExtensionAlgebra P' hP
      Module.Basis ι P.completionPlace.integers P'.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  have := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have := isSeparable_completion (P'.restrict k F) P' rfl
  rw [TauCeti.ord_discr_eq_multiplicity_mul_finrank
      (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl]
  exact congrArg _ (congrArg Nat.cast (P'.finrank_residueField_completion (k := k) (F := F)))

/-- **Invariance of the complementary-module quotient length under completion** when the integral
closure of `𝒪_P` in `F'` is a discrete valuation ring (for example when `P'` is the unique place
of `F'` lying over `P`), with no assumption of residue-field separability. -/
theorem length_traceDual_quotient_completionIntegers_eq_length (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) [IsDiscreteValuationRing (integralClosure P.integers F')] :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    Module.length P.completionPlace.integers
        ((Submodule.traceDual P.completionPlace.integers P.Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual P.completionPlace.integers P.Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      Module.length P.integers
        ((Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F')) ⧸
          (1 : Submodule (integralClosure P.integers F') F').comap
            (Submodule.traceDual P.integers F
              (1 : Submodule (integralClosure P.integers F') F')).subtype) := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  have hover := (centerIntegralClosure_liesOver_maximalIdeal k F P').over
  have hw : (centerIntegralClosure k F P').asIdeal =
      IsLocalRing.maximalIdeal (integralClosure (P'.restrict k F).integers F') :=
    (centerIntegralClosure k F P').isMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (IsLocalRing.le_maximalIdeal (centerIntegralClosure k F P').isMaximal.ne_top)
  have : IsLocalHom
      (algebraMap (P'.restrict k F).integers (integralClosure (P'.restrict k F).integers F')) :=
    ⟨fun a ha ↦ by
      by_contra h
      have ha' : a ∈ IsLocalRing.maximalIdeal (P'.restrict k F).integers := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [hw, Ideal.under_def] at hover
      rw [hover, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha'
      exact ha' ha⟩
  have hfin : Module.finrank (IsLocalRing.ResidueField (P'.restrict k F).integers)
      (IsLocalRing.ResidueField (integralClosure (P'.restrict k F).integers F')) =
      relativeDegree k F P' := by
    rw [P'.relativeDegree_eq_inertiaDeg_center (R := (P'.restrict k F).integers) k F
        (P'.algebraMap_mem_integers_of_mem_integralClosure k F),
      ← P'.centerIntegralClosure_def k F,
      Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal (P'.restrict k F).integers)
        (centerIntegralClosure k F P').asIdeal]
    exact Algebra.finrank_eq_of_equiv_equiv
      (Ideal.quotEquivOfEq (rfl : IsLocalRing.maximalIdeal (P'.restrict k F).integers = _))
      (Ideal.quotEquivOfEq hw.symm)
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))
  rw [length_traceDual_quotient_completionIntegers (P'.restrict k F) P' rfl,
    TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank, ← hw, ← differentExponent_def,
    hfin]

end FiniteSeparable

section SameConstants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section Integral

variable [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k F')
  (hP : P'.restrict k F = P)
  [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

/-- **The completed upper place restricts to the completed lower place.** -/
@[simp]
theorem restrict_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI := finiteDimensional_completion P P' hP
    P'.completionPlace.restrict k P.Completion = P.completionPlace := by
  let := P.completionExtensionAlgebra P' hP
  have := P.isScalarTower_completionExtensionAlgebra P' hP
  have := finiteDimensional_completion P P' hP
  rw [restrict_eq_iff_integers_le]
  intro x hx
  rw [P.algebraMap_completionExtensionAlgebra P' hP]
  exact P.completionExtension_mem_integers P' hP hx

/-- **Completion preserves the ramification index**, read intrinsically on `completionPlace`. -/
@[simp]
theorem ramificationIdx_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    ramificationIdx P.Completion P'.completionPlace = ramificationIdx F P' := by
  let := P.completionExtensionAlgebra P' hP
  have := P.isScalarTower_completionExtensionAlgebra P' hP
  have := finiteDimensional_completion P P' hP
  refine ramificationIdx_eq_of_forall_ord_eq k P.Completion P'.completionPlace fun x ↦ ?_
  rw [restrict_completionPlace P P' hP, P.algebraMap_completionExtensionAlgebra P' hP,
    P.ord_completionExtension P' hP x]

/-- **Completion preserves the full relative residue degree**, read intrinsically on
`completionPlace` and including any inseparable factor. -/
@[simp]
theorem relativeDegree_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI := finiteDimensional_completion P P' hP
    relativeDegree k P.Completion P'.completionPlace = relativeDegree k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegers P' rfl
  have := finiteDimensional_completion (P'.restrict k F) P' rfl
  have hS : ∀ s : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion s ∈ P'.completionPlace.integers :=
    fun s ↦ s.2
  have hmax : (P'.completionPlace.center hS).asIdeal =
      IsLocalRing.maximalIdeal P'.completionPlace.integers := by
    ext s
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  have hlies : (IsLocalRing.maximalIdeal P'.completionPlace.integers).LiesOver
      (IsLocalRing.maximalIdeal (P'.restrict k F).completionPlace.integers) := by
    have h := center_liesOver (R := (P'.restrict k F).completionPlace.integers)
      k (P'.restrict k F).Completion P'.completionPlace hS
    have hR : ((P'.completionPlace.restrict k (P'.restrict k F).Completion).center
        (algebraMap_mem_integers_restrict k (P'.restrict k F).Completion
          P'.completionPlace hS)).asIdeal =
        IsLocalRing.maximalIdeal (P'.restrict k F).completionPlace.integers := by
      ext r
      rw [mem_center_asIdeal, restrict_completionPlace (P'.restrict k F) P' rfl,
        mem_maximalIdeal_iff_valuation_lt_one]
      exact Iff.rfl
    rwa [hmax, hR] at h
  have hfin : Module.finrank (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField =
      Module.finrank
        ((P'.restrict k F).completionPlace.integers ⧸
          IsLocalRing.maximalIdeal (P'.restrict k F).completionPlace.integers)
        (P'.completionPlace.integers ⧸
          IsLocalRing.maximalIdeal P'.completionPlace.integers) :=
    Algebra.finrank_eq_of_equiv_equiv
      (Ideal.quotEquivOfEq
        (rfl : IsLocalRing.maximalIdeal (P'.restrict k F).completionPlace.integers = _))
      (Ideal.quotEquivOfEq
        (rfl : IsLocalRing.maximalIdeal P'.completionPlace.integers = _))
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl))
  rw [relativeDegree_eq_inertiaDeg_center (R := (P'.restrict k F).completionPlace.integers)
      k (P'.restrict k F).Completion P'.completionPlace hS,
    hmax, Ideal.inertiaDeg_eq_of_isMaximal
      (IsLocalRing.maximalIdeal (P'.restrict k F).completionPlace.integers)
      (IsLocalRing.maximalIdeal P'.completionPlace.integers),
    ← hfin, P'.finrank_residueField_completion (k := k) (F := F)]

end Integral

/-- **Invariance of `differentExponent` under completion**: the intrinsic different exponent of
`P'.completionPlace` over `P.completionPlace` equals `differentExponent k F P'`, with no
assumption of residue-field separability. -/
@[simp]
theorem differentExponent_completionPlace [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (P : Place k F) (P' : Place k F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI := finiteDimensional_completion P P' hP
    haveI := isSeparable_completion P P' hP
    differentExponent k P.Completion P'.completionPlace = differentExponent k F P' := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  have hmax : (P'.completionPlace.center hC).asIdeal =
      IsLocalRing.maximalIdeal P'.completionPlace.integers := by
    ext c
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  rw [differentExponent_eq_multiplicity_center
      (B := P.completionPlace.integers) (C := P'.completionPlace.integers) P'.completionPlace hC,
    hmax, multiplicity_differentIdeal_completionIntegers P P' hP]

end SameConstants

end TauCeti.Place

end
end
