/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Nakayama
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Separable
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# The semilocal decomposition of an extension of function fields at a place

Let `F' / F` be a finite separable extension of fields equipped with constant fields `k' / k` such
that `k' / k` is integral, and let `P` be a place of `F / k`. The places `P'` of `F' / k'` lying
over `P` form a finite set, and scalar extension from `F` (respectively `𝒪_P`) to the completion
`F̂_P` (respectively `𝒪̂_P`) decomposes as the product over the fibre above `P`:

* `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}` (`TauCeti.Place.semilocalEquiv`);
* `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}` (`TauCeti.Place.integralSemilocalEquiv`), where
  `𝒪'_P` is the integral closure of `𝒪_P` in `F'`.

No assumption is made on the characteristic, on `IsFunctionField`, or on the finiteness or
separability of the residue fields: an inseparable or infinite residue extension is handled
directly. Rather than appealing to local compactness (which would require finite residue fields),
surjectivity of `integralSemilocalHom` is proved from weak approximation
(`TauCeti.Place.exists_forall_ord_sub_eq`), module-finiteness of each completed valuation ring over
`𝒪̂_P` (`TauCeti.Place.moduleFinite_completionIntegers`), and Nakayama's lemma
(`Submodule.le_of_le_smul_of_le_jacobson`); surjectivity of `semilocalHom` follows by clearing
denominators by a power of a uniformizer of `P`, and injectivity follows from the local degree
formula (`TauCeti.Place.finrank_completion`) and the fundamental identity
(`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`).

The semilocal decomposition then decomposes `Algebra.trace` and `Algebra.norm` into the sum and
product of the completed local traces and norms above `P`. The overall algebraic interface and the
integral-to-field compatibility lemmas parallel
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Basic.lean`,
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Integers.lean`, and
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Norm/Trace.lean`.

## Main definitions

* `TauCeti.Place.integralClosureToCompletionIntegers`: the canonical ring homomorphism
  `𝒪'_P →+* 𝒪̂_{P'}` for a place `P'` over `P`.
* `TauCeti.Place.semilocalEquiv`: the field semilocal algebra isomorphism
  `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}`.
* `TauCeti.Place.integralSemilocalEquiv`: the integral semilocal algebra isomorphism
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}`.
* `TauCeti.Place.integralSemilocalToField`: the injective `𝒪_P`-algebra homomorphism from
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` to `F̂_P ⊗[F] F'`.

## Main results

* `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable`: an element of a
  finite separable extension `F' / F` is integral over `𝒪_P` iff it is regular at every place of
  `F' / k'` lying over `P`.
* `TauCeti.Place.trace_eq_sum_trace_semilocalEquiv`,
  `TauCeti.Place.completionEmbedding_trace_eq_sum_trace`,
  `TauCeti.Place.trace_semilocalEquiv_symm_single_mul`,
  `TauCeti.Place.trace_integralSemilocalToField_tmul_mul`: local-global trace decomposition.
* `TauCeti.Place.norm_eq_prod_norm_semilocalEquiv`,
  `TauCeti.Place.completionEmbedding_norm_eq_prod_norm`: local-global norm decomposition.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.3 and III.1–III.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3.
-/

public section

open IsDedekindDomain IsLocalRing
open scoped TensorProduct BigOperators

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- Scalar multiplication on `WithVal P.valuation` through any `F`-algebra base `S` is uniformly
continuous. Kept private as a theorem rather than a polymorphic instance so `S = k` does not create
a second `Algebra k P.Completion` alongside `Place.instAlgebraCompletion`. -/
private theorem uniformContinuousConstSMul_of_algebra {k F S : Type*} [Field k] [Field F]
    [Algebra k F] [CommSemiring S] [Algebra S F] (P : Place k F) :
    UniformContinuousConstSMul S (WithVal P.valuation) := by
  refine ⟨fun s ↦ ?_⟩
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal P.valuation)).uniformContinuous_const_smul _

/-- Uniform continuity of `F`-scalar multiplication on `WithVal P.valuation`, unlocking
`UniformSpace.Completion.algebra` (`Algebra F P.Completion`). -/
instance uniformContinuousConstSMul_self_withVal {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) : UniformContinuousConstSMul F (WithVal P.valuation) :=
  uniformContinuousConstSMul_of_algebra P

/-- Uniform continuity of `𝒪_P`-scalar multiplication on `WithVal P.valuation`, unlocking
`UniformSpace.Completion.algebra` (`Algebra P.integers P.Completion`). -/
instance uniformContinuousConstSMul_integers_withVal {k F : Type*} [Field k] [Field F]
    [Algebra k F] (P : Place k F) : UniformContinuousConstSMul P.integers (WithVal P.valuation) :=
  uniformContinuousConstSMul_of_algebra P

/-- The canonical `F`-algebra map into `P.Completion` (coming from `UniformSpace.Completion` of
`WithVal P.valuation`) agrees with `P.completionEmbedding`. -/
@[simp]
theorem algebraMap_completion_eq_completionEmbedding {k F : Type*} [Field k] [Field F]
    [Algebra k F] (P : Place k F) (x : F) :
    algebraMap F P.Completion x = P.completionEmbedding x := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, ← P.completionEmbedding_apply]

/-- The canonical `𝒪_P`-algebra map into `P.Completion` agrees with `P.completionEmbedding`. -/
@[simp]
theorem algebraMap_integers_completion_eq_completionEmbedding {k F : Type*} [Field k] [Field F]
    [Algebra k F] (P : Place k F) (r : P.integers) :
    algebraMap P.integers P.Completion r = P.completionEmbedding r := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    ValuationSubring.algebraMap_apply, ← P.completionEmbedding_apply]

/-- The action of `𝒪_P` on `P.Completion` factors through `F`. -/
instance isScalarTower_integers_completion {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) : IsScalarTower P.integers F P.Completion :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [algebraMap_integers_completion_eq_completionEmbedding,
      algebraMap_completion_eq_completionEmbedding, ValuationSubring.algebraMap_apply]

/-- The uniform-completion `k`-action on `P.Completion` agrees with multiplication by
`algebraMap k P.Completion`. -/
theorem completion_smul_constants {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (c : k) (x : P.Completion) :
    c • x = algebraMap k P.Completion c * x := by
  have := uniformContinuousConstSMul_of_algebra (S := k) P
  exact (congrFun (UniformSpace.Completion.map_smul_eq_mul_coe (WithVal P.valuation) k c) x).trans
    (by rw [WithVal.algebraMap_right_apply, ← P.completionEmbedding_apply,
      P.completionEmbedding.commutes])

/-- When the constant fields agree, the uniform-completion `k`-actions form a scalar tower across
`P.completionExtensionAlgebra P' hP` (without needing explicit `SMul` overrides). -/
theorem isScalarTower_constants_completionExtension {k F F' : Type*} [Field k] [Field F]
    [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
    [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    IsScalarTower k P.Completion P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  refine ⟨fun c a x ↦ ?_⟩
  rw [P.completion_smul_constants, P'.completion_smul_constants, Algebra.smul_def,
    Algebra.smul_def, P.algebraMap_completionExtensionAlgebra P' hP, map_mul,
    P.completionExtension_algebraMap P' hP, Algebra.algebraMap_self_apply, mul_assoc]

/-- The completed valuation ring `𝒪̂_P` as an `𝒪_P`-algebra via `completionIntegersEmbedding`. -/
@[expose, instance_reducible]
noncomputable def completionIntegersAlgebra {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) : Algebra P.integers P.completionPlace.integers :=
  P.completionIntegersEmbedding.toRingHom.toAlgebra

/-- For a place `Q` in the fibre over `P`, the completed field `F̂'_Q` as an `F̂_P`-algebra. -/
@[expose, instance_reducible]
noncomputable def fibreCompletionAlgebra {k k' F F' : Type*} [Field k] [Field k']
    [Field F] [Field F'] [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F']
    [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    {P : Place k F} (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.Completion Q.1.Completion :=
  P.completionExtensionAlgebra Q.1 Q.2

/-- For a place `Q` in the fibre over `P`, the completed valuation ring `𝒪̂_Q` as an
`𝒪̂_P`-algebra. -/
@[expose, instance_reducible]
noncomputable def fibreCompletionIntegersAlgebra {k k' F F' : Type*} [Field k] [Field k']
    [Field F] [Field F'] [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F']
    [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    {P : Place k F} (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.completionPlace.integers Q.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra Q.1 Q.2

scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.completionIntegersAlgebra
  TauCeti.Place.fibreCompletionAlgebra
  TauCeti.Place.fibreCompletionIntegersAlgebra

open scoped PlaceCompletion

@[simp]
theorem coe_algebraMap_completionIntegers {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (r : P.integers) :
    ((algebraMap P.integers P.completionPlace.integers r : P.completionPlace.integers) :
      P.Completion) = P.completionEmbedding r :=
  P.completionIntegersEmbedding_apply r

section IntegralClosureMap

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F']

/-- Every element of the local integral closure `𝒪'_P` maps into the completed valuation ring
`𝒪̂_{P'}` at any place `P'` over `P`. -/
theorem completionEmbedding_mem_integers_of_mem_integralClosure
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (x : integralClosure P.integers F') :
    P'.completionEmbedding (x : F') ∈ P'.completionPlace.integers := by
  subst hP
  have hx : (x : F') ∈ P'.integers :=
    algebraMap_mem_integers_of_mem_integralClosure k F P' x
  simpa only [mem_integers_iff, completionPlace_valuation, valuation_completionEmbedding]
    using P'.mem_integers_iff.mp hx

/-- The canonical ring homomorphism `𝒪'_P →+* 𝒪̂_{P'}` from the integral closure of `𝒪_P` in `F'`
to the completed valuation ring at a place `P'` lying over `P`. -/
noncomputable def integralClosureToCompletionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    integralClosure P.integers F' →+* P'.completionPlace.integers where
  toFun x := ⟨P'.completionEmbedding (x : F'),
    completionEmbedding_mem_integers_of_mem_integralClosure P P' hP x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add P'.completionEmbedding (x : F') (y : F'))
  map_mul' x y := Subtype.ext (map_mul P'.completionEmbedding (x : F') (y : F'))

@[simp]
theorem coe_integralClosureToCompletionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (x : integralClosure P.integers F') :
    (integralClosureToCompletionIntegers P P' hP x : P'.Completion) =
      P'.completionEmbedding (x : F') :=
  (rfl)

@[simp]
theorem integralClosureToCompletionIntegers_algebraMap
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) (r : P.integers) :
    integralClosureToCompletionIntegers P P' hP
        (algebraMap P.integers (integralClosure P.integers F') r) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding r) := by
  apply Subtype.ext
  rw [coe_integralClosureToCompletionIntegers, Subalgebra.coe_algebraMap,
    IsScalarTower.algebraMap_apply P.integers F F', coe_completionIntegersExtension,
    completionIntegersEmbedding_apply, P.completionExtension_completionEmbedding P' hP]
  rfl

end IntegralClosureMap

section Semilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

section Intersection

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- **The integral closure `𝒪'_P` is the intersection of the valuation rings above `P`** for any
finite separable extension `F' / F` and integral constant extension `k' / k` (without assuming
`IsFunctionField`): `𝒪'_P` is a Dedekind domain with fraction field `F'`, and every height-one
prime of `𝒪'_P` contracts to the unique maximal ideal of `𝒪_P`, hence defines a place of `F' / k'`
lying over `P`. -/
theorem isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable
    (P : Place k F) {x : F'} :
    IsIntegral P.integers x ↔ ∀ P' : Place k' F', P'.restrict k F = P → x ∈ P'.integers := by
  refine ⟨fun hx P' hP' ↦ P'.mem_integers_of_isIntegral (fun a ↦ ?_) hx, fun h ↦ ?_⟩
  · subst hP'
    exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2
  let S := integralClosure P.integers F'
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ by
    rw [ValuationSubring.algebraMap_apply]
    exact r.2
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  have hk' : ∀ c : k', algebraMap k' F' c ∈ S := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' S := ((algebraMap k' F').codRestrict S hk').toAlgebra
  have : IsScalarTower k' S F' := .of_algebraMap_eq fun _ ↦ rfl
  have : FaithfulSMul P.integers S := FaithfulSMul.of_field_isFractionRing P.integers S F F'
  have : Algebra.IsIntegral P.integers S := Algebra.IsIntegral.of_finite P.integers S
  obtain ⟨s, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := S) F' x fun 𝔓 ↦ by
    have hne : 𝔓.asIdeal.under P.integers ≠ ⊥ :=
      Ideal.IsIntegral.under_ne_bot P.integers 𝔓.ne_bot
    have hmax₁ : (𝔓.asIdeal.under P.integers).IsMaximal :=
      (𝔓.isPrime.under P.integers).isMaximal hne
    have hmax₂ : (P.center hR).asIdeal.IsMaximal :=
      (P.center hR).isPrime.isMaximal (P.center hR).ne_bot
    have hlies : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal :=
      ⟨(eq_maximalIdeal hmax₂).trans (eq_maximalIdeal hmax₁).symm⟩
    have hres : (ofPrime k' F' 𝔓).restrict k F = P := by
      rw [restrict_ofPrime k F (P.center hR) 𝔓, ofPrime_center]
    simpa only [mem_integers_iff, valuation_ofPrime] using h (ofPrime k' F' 𝔓) hres
  exact s.2

end Intersection

section Maps

variable [Algebra.IsIntegral F F'] (k' F') (P : Place k F)

/-- The canonical `𝒪̂_P`-algebra homomorphism from `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` to the product of the
completed valuation rings above `P`. -/
noncomputable def integralSemilocalHom :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[
      P.completionPlace.integers]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Algebra P.integers Q.1.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers Q.1.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers Q.1.completionPlace.integers :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { integralClosureToCompletionIntegers P Q.1 Q.2 with
        commutes' := fun r ↦ by
          -- Unfold the composite `𝒪_P`-algebra structure on `𝒪̂_Q` installed above so
          -- `integralClosureToCompletionIntegers_algebraMap` applies.
          change integralClosureToCompletionIntegers P Q.1 Q.2
              (algebraMap P.integers (integralClosure P.integers F') r) =
            algebraMap P.completionPlace.integers Q.1.completionPlace.integers
              (algebraMap P.integers P.completionPlace.integers r)
          rw [P.algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2]
          exact integralClosureToCompletionIntegers_algebraMap P Q.1 Q.2 r })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
@[simp]
theorem integralSemilocalHom_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralSemilocalHom k' F' P (a ⊗ₜ x) Q =
      P.completionIntegersExtension Q.1 Q.2 a *
        integralClosureToCompletionIntegers P Q.1 Q.2 x := by
  simp [integralSemilocalHom, algebraMap_completionIntegersExtensionAlgebra]

/-- The canonical `F̂_P`-algebra homomorphism from `F̂_P ⊗[F] F'` to the product of the completed
fields above `P`. -/
noncomputable def semilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      UniformContinuousConstSMul F (WithVal Q.1.valuation) :=
    uniformContinuousConstSMul_of_algebra Q.1
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower F P.Completion Q.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
        ← Q.1.completionEmbedding_apply, P.algebraMap_completionExtensionAlgebra Q.1 Q.2,
        P.algebraMap_completion_eq_completionEmbedding,
        P.completionExtension_completionEmbedding Q.1 Q.2]
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { Q.1.completionEmbedding.toRingHom with
        commutes' := fun x ↦ by
          rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
            ← Q.1.completionEmbedding_apply]
          rfl })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
@[simp]
theorem semilocalHom_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalHom k' F' P (a ⊗ₜ x) Q =
      P.completionExtension Q.1 Q.2 a * Q.1.completionEmbedding x := by
  simp [semilocalHom, algebraMap_completionExtensionAlgebra]

end Maps

section Equivalence

variable [FiniteDimensional F F']

private noncomputable def completionIntegersToCompletion (P : Place k F) :
    P.completionPlace.integers →ₐ[P.integers] P.Completion where
  toRingHom := P.completionPlace.integers.subtype
  commutes' r := by
    rw [algebraMap_integers_completion_eq_completionEmbedding]
    exact P.completionIntegersEmbedding_apply r

variable (F') in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [FiniteDimensional F F'] in
private noncomputable def integralTensorToBaseChange (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[P.integers] integralClosure P.integers F' :=
  Algebra.TensorProduct.map (completionIntegersToCompletion P)
    (AlgHom.id P.integers (integralClosure P.integers F'))

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [FiniteDimensional F F'] in
private theorem integralTensorToBaseChange_injective (P : Place k F) :
    Function.Injective (integralTensorToBaseChange F' P) := by
  have : Module.IsTorsionFree P.integers (integralClosure P.integers F') :=
    .of_smul_eq_zero fun r m h ↦ by
      have h' : algebraMap P.integers F' r * (m : F') = 0 := by
        simpa only [Algebra.smul_def, MulMemClass.coe_mul, ZeroMemClass.coe_zero,
          Subalgebra.coe_algebraMap] using
          congrArg (fun z : integralClosure P.integers F' ↦ (z : F')) h
      exact (mul_eq_zero.mp h').imp
        (fun hr ↦ algebraMap_integersExtension_injective F' P (by rw [hr, map_zero]))
        (fun hm ↦ Subtype.ext hm)
  have : Module.IsTorsionFree P.integers P.completionPlace.integers :=
    .of_smul_eq_zero fun r m h ↦ by
      have h' : P.completionEmbedding r * (m : P.Completion) = 0 := by
        simpa only [Algebra.smul_def, MulMemClass.coe_mul, ZeroMemClass.coe_zero,
          coe_algebraMap_completionIntegers] using
          congrArg (fun z : P.completionPlace.integers ↦ (z : P.Completion)) h
      exact (mul_eq_zero.mp h').imp
        (fun hr ↦ Subtype.ext ((map_eq_zero_iff _ P.completionEmbedding.injective).mp hr))
        (fun hm ↦ Subtype.ext hm)
  -- Expose the underlying linear tensor map so `TensorProduct.map_injective_of_flat_flat` applies.
  change Function.Injective (TensorProduct.map
    (completionIntegersToCompletion P).toLinearMap
    (AlgHom.id P.integers (integralClosure P.integers F')).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private theorem isPushout_integers_integralClosure (P : Place k F) :
    Algebra.IsPushout P.integers F (integralClosure P.integers F') F' := by
  have := isLocalization_integralClosure F' P
  exact (Algebra.isPushout_of_isLocalization (nonZeroDivisors P.integers) F
    (integralClosure P.integers F') F').symm

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private noncomputable def integralFieldBaseChangeEquiv (P : Place k F) :
    P.Completion ⊗[P.integers] integralClosure P.integers F' ≃ₐ[P.Completion]
      P.Completion ⊗[F] F' := by
  have := isPushout_integers_integralClosure (F' := F') P
  exact (Algebra.TensorProduct.cancelBaseChange P.integers F P.Completion P.Completion
      (integralClosure P.integers F')).symm.trans
    (Algebra.TensorProduct.congr (.refl : P.Completion ≃ₐ[P.Completion] P.Completion)
      (Algebra.IsPushout.equiv P.integers F (integralClosure P.integers F') F'))

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private theorem integralFieldBaseChangeEquiv_tmul (P : Place k F)
    (a : P.Completion) (x : integralClosure P.integers F') :
    integralFieldBaseChangeEquiv (F' := F') P (a ⊗ₜ x) = a ⊗ₜ (x : F') := by
  have := isPushout_integers_integralClosure (F' := F') P
  simp [integralFieldBaseChangeEquiv, Algebra.IsPushout.equiv_tmul]

variable (F') in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- The canonical `𝒪_P`-algebra homomorphism from `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` to `F̂_P ⊗[F] F'`. -/
noncomputable def integralSemilocalToField (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
  let e : P.Completion ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
    { (integralFieldBaseChangeEquiv (F' := F') P).toRingEquiv.toRingHom with
      commutes' := fun r ↦ by
        -- Expose both `𝒪_P`-algebra maps as pure tensors so `integralFieldBaseChangeEquiv_tmul`
        -- bridges the `𝒪_P`- and `F`-tensor products.
        change integralFieldBaseChangeEquiv (F' := F') P
            (algebraMap P.integers P.Completion r ⊗ₜ[P.integers]
              (1 : integralClosure P.integers F')) =
          algebraMap P.integers P.Completion r ⊗ₜ[F] (1 : F')
        exact integralFieldBaseChangeEquiv_tmul P (algebraMap P.integers P.Completion r) 1 }
  e.comp (integralTensorToBaseChange F' P)

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
@[simp]
theorem integralSemilocalToField_tmul (P : Place k F) (a : P.completionPlace.integers)
    (x : integralClosure P.integers F') :
    integralSemilocalToField F' P (a ⊗ₜ x) = (a : P.Completion) ⊗ₜ (x : F') :=
  integralFieldBaseChangeEquiv_tmul P (a : P.Completion) x

variable (F') in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- The canonical map `𝒪̂_P ⊗[𝒪_P] 𝒪'_P → F̂_P ⊗[F] F'` is injective. -/
theorem integralSemilocalToField_injective (P : Place k F) :
    Function.Injective (integralSemilocalToField F' P) :=
  (integralFieldBaseChangeEquiv (F' := F') P).injective.comp
    (integralTensorToBaseChange_injective P)

/-- After inclusion into the completions, `integralSemilocalHom` agrees with `semilocalHom`. -/
theorem integralSemilocalHom_fieldCompatibility (P : Place k F)
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    semilocalHom k' F' P (integralSemilocalToField F' P z) =
      fun Q ↦ (integralSemilocalHom k' F' P z Q : Q.1.Completion) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      funext Q
      simp [coe_completionIntegersExtension]
  | add x y hx hy =>
      funext Q
      simp only [map_add, Pi.add_apply, AddMemClass.coe_add]
      exact congrArg₂ (· + ·) (congrFun hx Q) (congrFun hy Q)

variable [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

omit [Algebra.IsSeparable F F'] in
/-- The fibre of places of `F' / k'` lying over `P` is finite. -/
instance finite_subtype_restrict_eq (P : Place k F) :
    Finite {P' : Place k' F' // P'.restrict k F = P} :=
  (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).to_subtype

variable (k' F')

/-- Weak approximation modulo `𝔪̂_P`: every family of completed integral elements above `P` is
simultaneously approximated to order `e(P' ∣ P)` at every `P' ∣ P` by a single element of the
integral closure `𝒪'_P`. -/
theorem exists_integralClosure_completionEmbedding_sub_mem_filtration (P : Place k F)
    (y : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :
    ∃ w : integralClosure P.integers F',
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P},
        Q.1.completionEmbedding (w : F') - (y Q : Q.1.Completion) ∈
          Q.1.completionPlace.filtration (ramificationIdx F Q.1) := by
  choose y₀ hy₀ using fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
    Q.1.exists_filtration_sub_completionEmbedding_mem (ramificationIdx F Q.1)
      ⟨y Q, Q.1.completionPlace.mem_filtration_zero_iff.mpr (y Q).2⟩
  obtain ⟨w, hw⟩ := exists_forall_ord_sub_eq
    (P := fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦ Q.1)
    Subtype.val_injective (fun Q ↦ (y₀ Q : F')) (fun Q ↦ (ramificationIdx F Q.1 : ℤ))
  have hw_fil (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      w - (y₀ Q : F') ∈ Q.1.filtration (ramificationIdx F Q.1) := by
    have hne : w - (y₀ Q : F') ≠ 0 := by
      intro h0
      have hord := hw Q
      rw [h0, ord_zero] at hord
      exact (ramificationIdx_pos F Q.1).ne' (Int.ofNat_inj.mp hord.symm)
    exact (Q.1.mem_filtration_iff_le_ord hne).mpr (hw Q).ge
  have hw_int : w ∈ integralClosure P.integers F' := by
    rw [mem_integralClosure_iff,
      isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable (k' := k') P]
    intro P' hP'
    let Q : {P' : Place k' F' // P'.restrict k F = P} := ⟨P', hP'⟩
    have hmem : w ∈ Q.1.filtration 0 := by
      have h1 := Q.1.filtration_antitone (Nat.cast_nonneg _) (hw_fil Q)
      rw [← sub_add_cancel w (y₀ Q : F')]
      exact (Q.1.filtration 0).add_mem h1 (y₀ Q).2
    exact Q.1.mem_filtration_zero_iff.mp hmem
  refine ⟨⟨w, hw_int⟩, fun Q ↦ ?_⟩
  have hsub : Q.1.completionEmbedding w - (y Q : Q.1.Completion) =
      Q.1.completionEmbedding (w - (y₀ Q : F')) -
        ((y Q : Q.1.Completion) - Q.1.completionEmbedding (y₀ Q)) := by
    rw [map_sub, sub_sub_sub_cancel_right]
  rw [hsub]
  exact (Q.1.completionPlace.filtration (ramificationIdx F Q.1)).sub_mem
    (Q.1.completionEmbedding_mem_filtration_iff.mpr (hw_fil Q)) (hy₀ Q)

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k'] in
private theorem pi_mem_maximalIdeal_smul_top_of_forall_mem_filtration
    [Algebra.IsIntegral F F'] (P : Place k F)
    {d : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers}
    (hd : ∀ Q : {P' : Place k' F' // P'.restrict k F = P},
      (d Q : Q.1.Completion) ∈ Q.1.completionPlace.filtration (ramificationIdx F Q.1)) :
    d ∈ (maximalIdeal P.completionPlace.integers • ⊤ :
      Submodule P.completionPlace.integers
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers)) := by
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P.integers := by rw [mem_integers_iff_ord_nonneg, hπ]; exact zero_le_one
  let πc := P.completionIntegersEmbedding ⟨π, hπint⟩
  have hπc0 : (πc : P.Completion) ≠ 0 := by
    rw [completionIntegersEmbedding_apply]
    exact (map_ne_zero _).mpr hπ0
  have hπm : πc ∈ maximalIdeal P.completionPlace.integers := by
    rw [P.completionPlace.mem_maximalIdeal_iff_ord_pos hπc0,
      completionIntegersEmbedding_apply, ord_completionEmbedding, hπ]
    exact zero_lt_one
  have hdiv (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      ∃ zQ : Q.1.completionPlace.integers, d Q = πc • zQ := by
    let E := P.completionExtension Q.1 Q.2 πc
    have hE0 : E ≠ 0 := (map_ne_zero _).mpr hπc0
    have hE : Q.1.completionPlace.ord E = ramificationIdx F Q.1 := by
      rw [P.ord_completionExtension Q.1 Q.2, completionIntegersEmbedding_apply,
        ord_completionEmbedding, hπ, mul_one]
    have hq_int : (d Q : Q.1.Completion) / E ∈ Q.1.completionPlace.integers := by
      rcases eq_or_ne (d Q : Q.1.Completion) 0 with h0 | h0
      · rw [h0, zero_div]
        exact zero_mem _
      · rw [mem_integers_iff_ord_nonneg, Q.1.completionPlace.ord_div h0 hE0, hE]
        exact sub_nonneg.mpr ((Q.1.completionPlace.mem_filtration_iff_le_ord h0).mp (hd Q))
    refine ⟨⟨(d Q : Q.1.Completion) / E, hq_int⟩, Subtype.ext ?_⟩
    rw [Algebra.smul_def, MulMemClass.coe_mul,
      P.coe_algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2, mul_div_cancel₀ _ hE0]
  choose z hz using hdiv
  have hzed : d = πc • z := funext hz
  rw [hzed]
  exact Submodule.smul_mem_smul hπm Submodule.mem_top

/-- **Surjectivity of the integral semilocal map**: every family of completed integral elements
at the places over `P` is approximated modulo `𝔪̂_P` by a single global element `w ∈ 𝒪'_P` via
weak approximation, and Nakayama's lemma over the local ring `𝒪̂_P` upgrades this to surjectivity
since each `𝒪̂_{P'}` is finite over `𝒪̂_P`. -/
theorem integralSemilocalHom_surjective (P : Place k F) :
    Function.Surjective (integralSemilocalHom k' F' P) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Finite P.completionPlace.integers Q.1.completionPlace.integers :=
    P.moduleFinite_completionIntegers Q.1 Q.2
  suffices htop : (⊤ : Submodule P.completionPlace.integers
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers)) ≤
      (integralSemilocalHom k' F' P).range.toSubmodule by
    intro y
    exact htop Submodule.mem_top
  refine Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top
    (ringJacobson_eq_maximalIdeal _).ge fun y _ ↦ ?_
  obtain ⟨w, hw⟩ := exists_integralClosure_completionEmbedding_sub_mem_filtration k' F' P y
  have hmem := pi_mem_maximalIdeal_smul_top_of_forall_mem_filtration k' F' P
      (d := integralSemilocalHom k' F' P (1 ⊗ₜ w) - y) fun Q ↦ by
    have hd : ((integralSemilocalHom k' F' P (1 ⊗ₜ w) - y) Q : Q.1.Completion) =
        Q.1.completionEmbedding (w : F') - (y Q : Q.1.Completion) := by
      rw [Pi.sub_apply, AddSubgroupClass.coe_sub, integralSemilocalHom_tmul, map_one, one_mul,
        coe_integralClosureToCompletionIntegers]
    rw [hd]
    exact hw Q
  have hy : y = integralSemilocalHom k' F' P (1 ⊗ₜ w) -
      (integralSemilocalHom k' F' P (1 ⊗ₜ w) - y) := (sub_sub_cancel _ _).symm
  rw [hy]
  exact Submodule.sub_mem_sup ⟨1 ⊗ₜ w, rfl⟩ hmem

/-- **Surjectivity of the field semilocal map**, obtained by clearing denominators of a tuple of
completed elements using a power of a uniformizer at `P` and lifting the resulting integral tuple
along `integralSemilocalHom_surjective`. -/
theorem semilocalHom_surjective (P : Place k F) :
    Function.Surjective (semilocalHom k' F' P) := by
  classical
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  intro y
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  set πc : P.Completion := P.completionEmbedding π
  have hπc0 : πc ≠ 0 := by simpa [πc] using hπ0
  let N : ℕ := Finset.univ.sup fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
    (Q.1.completionPlace.ord (y Q)).natAbs
  have hyN (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      P.completionExtension Q.1 Q.2 (πc ^ N) * y Q ∈ Q.1.completionPlace.integers := by
    rcases eq_or_ne (y Q) 0 with h0 | h0
    · simp [h0]
    have hE0 : P.completionExtension Q.1 Q.2 (πc ^ N) ≠ 0 :=
      (map_ne_zero _).mpr (pow_ne_zero N hπc0)
    rw [mem_integers_iff_ord_nonneg, Q.1.completionPlace.ord_mul hE0 h0,
      P.ord_completionExtension Q.1 Q.2, P.completionPlace.ord_pow,
      ord_completionEmbedding, hπ, mul_one]
    have hle : (Q.1.completionPlace.ord (y Q)).natAbs ≤ N :=
      Finset.le_sup (f := fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
        (Q.1.completionPlace.ord (y Q)).natAbs) (Finset.mem_univ Q)
    have he : (1 : ℤ) ≤ ramificationIdx F Q.1 := by exact_mod_cast ramificationIdx_pos F Q.1
    have hN : -(N : ℤ) ≤ Q.1.completionPlace.ord (y Q) := by
      have : ((Q.1.completionPlace.ord (y Q)).natAbs : ℤ) ≤ N := by exact_mod_cast hle
      linarith [neg_abs_le (Q.1.completionPlace.ord (y Q)),
        Int.natCast_natAbs (Q.1.completionPlace.ord (y Q))]
    nlinarith
  obtain ⟨z, hz⟩ := integralSemilocalHom_surjective k' F' P
    fun Q ↦ ⟨P.completionExtension Q.1 Q.2 (πc ^ N) * y Q, hyN Q⟩
  refine ⟨(πc ^ N)⁻¹ • integralSemilocalToField F' P z, funext fun Q ↦ ?_⟩
  rw [map_smul, integralSemilocalHom_fieldCompatibility, Pi.smul_apply, Algebra.smul_def,
    P.algebraMap_completionExtensionAlgebra Q.1 Q.2, hz, map_inv₀,
    inv_mul_cancel_left₀ ((map_ne_zero _).mpr (pow_ne_zero N hπc0))]

attribute [local instance] Fintype.ofFinite in
/-- The sum of the completed local degrees above `P` equals `[F' : F]`. -/
theorem sum_finrank_completion_eq_finrank (P : Place k F) :
    (∑ Q : {P' : Place k' F' // P'.restrict k F = P},
      Module.finrank P.Completion Q.1.Completion) = Module.finrank F F' := by
  classical
  let s : Finset (Place k' F') := (finite_setOf_restrict_eq k F P).toFinset
  have hs (P' : Place k' F') : P' ∈ s ↔ P'.restrict k F = P := Set.Finite.mem_toFinset _
  calc (∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Module.finrank P.Completion Q.1.Completion)
      = ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
          ramificationIdx F Q.1 * relativeDegree k F Q.1 :=
        Finset.sum_congr rfl fun Q _ ↦ P.finrank_completion Q.1 Q.2
    _ = ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' := by
        rw [← Finset.sum_coe_sort s]
        exact Fintype.sum_equiv (Equiv.subtypeEquivRight hs).symm _ _ fun _ ↦ rfl
    _ = Module.finrank F F' :=
        sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P hs

attribute [local instance] Fintype.ofFinite in
/-- The field semilocal map is injective: it is a surjective `F̂_P`-linear map between vector
spaces of equal finite dimension `[F' : F]`. -/
theorem semilocalHom_injective (P : Place k F) :
    Function.Injective (semilocalHom k' F' P) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    P.finiteDimensional_completion Q.1 Q.2
  have hdim : Module.finrank P.Completion (P.Completion ⊗[F] F') =
      Module.finrank P.Completion
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype,
      sum_finrank_completion_eq_finrank k' F' P]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (semilocalHom k' F' P).toLinearMap) hdim).mpr (semilocalHom_surjective k' F' P)

/-- **The field semilocal decomposition**: `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}`. -/
noncomputable def semilocalEquiv (P : Place k F) :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) :=
  AlgEquiv.ofBijective (semilocalHom k' F' P)
    -- `Function.Bijective` is semireducible; `show` keeps the proof typed at `Function.Bijective`
    -- rather than its unfolded conjunction so `AlgEquiv.ofBijective_apply` rewrites cleanly.
    (show Function.Bijective (semilocalHom k' F' P) from
      ⟨semilocalHom_injective k' F' P, semilocalHom_surjective k' F' P⟩)

variable {k' F'} in
@[simp]
theorem semilocalEquiv_tmul (P : Place k F) (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalEquiv k' F' P (a ⊗ₜ x) Q =
      P.completionExtension Q.1 Q.2 a * Q.1.completionEmbedding x := by
  rw [semilocalEquiv, AlgEquiv.ofBijective_apply, semilocalHom_tmul]

/-- The integral semilocal map is injective because it embeds into `semilocalEquiv`. -/
theorem integralSemilocalHom_injective (P : Place k F) :
    Function.Injective (integralSemilocalHom k' F' P) := by
  intro x y hxy
  apply integralSemilocalToField_injective F' P
  apply (semilocalEquiv k' F' P).injective
  rw [semilocalEquiv, AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply,
    integralSemilocalHom_fieldCompatibility, integralSemilocalHom_fieldCompatibility, hxy]

/-- **The integral semilocal decomposition**: `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}`. -/
noncomputable def integralSemilocalEquiv (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' ≃ₐ[
      P.completionPlace.integers]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :=
  AlgEquiv.ofBijective (integralSemilocalHom k' F' P)
    -- Keep the proof typed at `Function.Bijective` so `AlgEquiv.ofBijective_apply` rewrites it.
    (show Function.Bijective (integralSemilocalHom k' F' P) from
      ⟨integralSemilocalHom_injective k' F' P, integralSemilocalHom_surjective k' F' P⟩)

variable {k' F'} in
@[simp]
theorem integralSemilocalEquiv_tmul (P : Place k F) (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralSemilocalEquiv k' F' P (a ⊗ₜ x) Q =
      P.completionIntegersExtension Q.1 Q.2 a *
        integralClosureToCompletionIntegers P Q.1 Q.2 x := by
  rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply, integralSemilocalHom_tmul]

variable {k' F'} in
/-- After inclusion into the completions, `integralSemilocalEquiv` agrees with `semilocalEquiv`. -/
theorem integralSemilocalEquiv_fieldCompatibility (P : Place k F)
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    semilocalEquiv k' F' P (integralSemilocalToField F' P z) =
      fun Q ↦ (integralSemilocalEquiv k' F' P z Q : Q.1.Completion) := by
  rw [semilocalEquiv, integralSemilocalEquiv, AlgEquiv.ofBijective_apply]
  funext Q
  rw [AlgEquiv.ofBijective_apply]
  exact congrFun (integralSemilocalHom_fieldCompatibility P z) Q

/-! ### Norm and trace in the semilocal decomposition -/

variable {k' F'} in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k'] in
/-- The trace of a pure integral tensor paired with an element of `F'` is the scalar extension of
the trace pairing of `F' / F`. -/
theorem trace_integralSemilocalToField_tmul_mul (P : Place k F)
    (a : P.completionPlace.integers) (x : integralClosure P.integers F') (d : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (integralSemilocalToField F' P (a ⊗ₜ x) * (1 ⊗ₜ d)) =
      (a : P.Completion) * P.completionEmbedding (Algebra.trace F F' ((x : F') * d)) := by
  have ha : (a : P.Completion) ⊗ₜ[F] ((x : F') * d) =
      (a : P.Completion) • ((1 : P.Completion) ⊗ₜ[F] ((x : F') * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [integralSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul,
    algebraMap_completion_eq_completionEmbedding]

attribute [local instance] Fintype.ofFinite in
/-- The trace of `F̂_P ⊗[F] F'` over `F̂_P` is the sum of the traces of its completed components. -/
theorem trace_eq_sum_trace_semilocalEquiv (P : Place k F) (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (semilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    P.finiteDimensional_completion Q.1 Q.2
  rw [← Algebra.trace_eq_of_algEquiv (semilocalEquiv k' F' P)]
  exact Algebra.trace_pi _

variable {k' F'} in
attribute [local instance] Fintype.ofFinite in
/-- An element of `F̂'_Q`, placed in the `Q`-component of `F̂_P ⊗[F] F'`, has the same trace
pairing with an element of `F'` as inside `F̂'_Q`. -/
theorem trace_semilocalEquiv_symm_single_mul (P : Place k F)
    [DecidableEq {P' : Place k' F' // P'.restrict k F = P}]
    (Q : {P' : Place k' F' // P'.restrict k F = P})
    (z : Q.1.Completion) (x : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((semilocalEquiv k' F' P).symm (Pi.single Q z) * (1 ⊗ₜ x)) =
      Algebra.trace P.Completion Q.1.Completion (z * Q.1.completionEmbedding x) := by
  rw [trace_eq_sum_trace_semilocalEquiv k' F' P, Finset.sum_eq_single Q]
  · simp [semilocalEquiv_tmul]
  · intro Q' _ hQ'
    simp [Pi.single_eq_of_ne hQ']
  · simp

variable {F'} in
attribute [local instance] Fintype.ofFinite in
/-- **Local-global trace formula**: the trace of an element of `F'` is the sum of its completed
local traces at the places above `P`. -/
theorem completionEmbedding_trace_eq_sum_trace (P : Place k F) (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (Q.1.completionEmbedding x) := by
  rw [← algebraMap_completion_eq_completionEmbedding,
    ← Algebra.trace_baseChange_tmul (A := P.Completion) (B := F') x,
    trace_eq_sum_trace_semilocalEquiv k' F' P]
  refine Finset.sum_congr rfl fun Q _ ↦ ?_
  simp [semilocalEquiv_tmul]

attribute [local instance] Fintype.ofFinite in
/-- The norm of `F̂_P ⊗[F] F'` over `F̂_P` is the product of the norms of its completed
components. -/
theorem norm_eq_prod_norm_semilocalEquiv (P : Place k F) (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (semilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    P.finiteDimensional_completion Q.1 Q.2
  rw [← Algebra.norm_eq_of_algEquiv (semilocalEquiv k' F' P)]
  exact Algebra.norm_pi _

variable {F'} in
attribute [local instance] Fintype.ofFinite in
/-- **Local-global norm formula**: the norm of an element of `F'` is the product of its completed
local norms at the places above `P`. -/
theorem completionEmbedding_norm_eq_prod_norm (P : Place k F) (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (Q.1.completionEmbedding x) := by
  rw [← algebraMap_completion_eq_completionEmbedding,
    ← Algebra.norm_baseChange_tmul (A := P.Completion) (B := F') x,
    norm_eq_prod_norm_semilocalEquiv k' F' P]
  refine Finset.prod_congr rfl fun Q _ ↦ ?_
  simp [semilocalEquiv_tmul]

end Equivalence

end Semilocal

end TauCeti.Place
