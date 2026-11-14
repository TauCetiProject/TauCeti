/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Nakayama
public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# The semilocal decomposition of an extension of function fields at a place

Let `F' / F` be a finite separable extension of fields equipped with constant fields `k' / k` such
that `k' / k` is integral, and let `P` be a place of `F / k`. The places `P'` of `F' / k'` lying
over `P` form a finite set, and scalar extension from `F` (respectively `𝒪_P`) to the completion
`F̂_P` (respectively `𝒪̂_P`) decomposes as the product over the fiber above `P`:

* `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}` (`TauCeti.Place.semilocalEquiv`);
* `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}` (`TauCeti.Place.integralSemilocalEquiv`), where
  `𝒪'_P` is the integral closure of `𝒪_P` in `F'`.

No assumption is made on the characteristic, on `IsFunctionField`, or on the finiteness or
separability of the residue fields: an inseparable residue extension or infinite residue fields are
handled directly (under `[FiniteDimensional F F']` each residue extension `[F'_{P'} : F_P]` is
automatically finite-dimensional). Rather than appealing to local compactness (which would require
finite residue fields), surjectivity of `integralSemilocalHom` is proved from weak approximation
(`TauCeti.Place.exists_forall_ord_sub_eq`), module-finiteness of each completed valuation ring over
`𝒪̂_P` (`TauCeti.Place.moduleFinite_completionIntegers`), and Nakayama's lemma
(`Submodule.le_of_le_smul_of_le_jacobson`); surjectivity of `semilocalHom` follows by clearing
denominators by a power of a uniformizer of `P`, and injectivity follows from the local degree
formula (`TauCeti.Place.finrank_completion`) and the fundamental identity
(`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`).

The semilocal decomposition then decomposes `Algebra.trace` and `Algebra.norm` into the sum and
product of the completed local traces and norms above `P`, and transfers global trace-dual
expansions to a single completed place without assuming `k' / k` is integral
(`TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`).

Semilocal declarations indexed by the fiber `{P' : Place k' F' // P'.restrict k F = P}` use the
scoped instance bundle `PlaceCompletion` (`open scoped PlaceCompletion`), which activates
`TauCeti.Place.completionIntegersAlgebra`, `TauCeti.Place.fiberCompletionAlgebra`,
`TauCeti.Place.fiberCompletionIntegersAlgebra`, and their companion scalar-tower, torsion-freeness,
locality, finiteness, and integral-closure instances on fiber places. By contrast, single-place
completion declarations bind `completionExtensionAlgebra` and `completionIntegersExtensionAlgebra`
locally via `letI` so they never compete with `Algebra.id`.

The overall algebraic interface and the integral-to-field compatibility lemmas parallel
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Basic.lean`,
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Integers.lean`, and
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Norm/Trace.lean`.

## Main definitions

* `TauCeti.Place.fiberCompletionAlgebra`, `TauCeti.Place.fiberCompletionIntegersAlgebra`: scoped
  `PlaceCompletion` algebra structures on `Q.1.Completion` and `Q.1.completionPlace.integers` for a
  place `Q` in the fiber over `P`.
* `TauCeti.Place.semilocalEquiv`: the field semilocal algebra isomorphism
  `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{P' ∣ P} F̂'_{P'}`.
* `TauCeti.Place.integralSemilocalEquiv`: the integral semilocal algebra isomorphism
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{P' ∣ P} 𝒪̂_{P'}`.
* `TauCeti.Place.integralSemilocalToField`: the injective `𝒪_P`-algebra homomorphism from
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` to `F̂_P ⊗[F] F'`.

## Main results

* `TauCeti.Place.integralSemilocalHom_surjective`, `TauCeti.Place.semilocalHom_surjective`:
  surjectivity of the integral and field semilocal maps for any finite extension `F' / F` and
  integral constant extension `k' / k` (without separability of `F' / F`).
* `TauCeti.Place.trace_eq_sum_trace_semilocalEquiv`,
  `TauCeti.Place.completionEmbedding_trace_eq_sum_trace`,
  `TauCeti.Place.trace_semilocalEquiv_symm_single_mul`,
  `TauCeti.Place.trace_integralSemilocalToField_tmul_mul`,
  `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`: local-global trace decomposition and
  transfer of trace-dual expansions to completions.
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

section FiberInstances

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

section Integral

variable [Algebra.IsIntegral F F'] {P : Place k F}

/-- For a place `Q` in the fiber over `P`, the completed field `F̂'_Q` as an `F̂_P`-algebra.
Registered as a scoped instance in `PlaceCompletion`. -/
@[expose, instance_reducible]
noncomputable def fiberCompletionAlgebra (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.Completion Q.1.Completion :=
  P.completionExtensionAlgebra Q.1 Q.2

/-- For a place `Q` in the fiber over `P`, the completed valuation ring `𝒪̂_Q` as an
`𝒪̂_P`-algebra. Registered as a scoped instance in `PlaceCompletion`. -/
@[expose, instance_reducible]
noncomputable def fiberCompletionIntegersAlgebra
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.completionPlace.integers Q.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra Q.1 Q.2

-- Activate the fiber completion algebra structures in `PlaceCompletion` alongside
-- `Place.completionIntegersAlgebra` from `Place/Completion/Basic.lean`.
scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.fiberCompletionAlgebra
  TauCeti.Place.fiberCompletionIntegersAlgebra

open scoped PlaceCompletion

/-- On a place `Q` in the fiber over `P`, `algebraMap P.Completion Q.1.Completion` is
`P.completionExtension Q.1 Q.2`. -/
theorem algebraMap_fiberCompletionAlgebra (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    algebraMap P.Completion Q.1.Completion = P.completionExtension Q.1 Q.2 :=
  P.algebraMap_completionExtensionAlgebra Q.1 Q.2

/-- On a place `Q` in the fiber over `P`,
`algebraMap P.completionPlace.integers Q.1.completionPlace.integers` is
`P.completionIntegersExtension Q.1 Q.2`. -/
theorem algebraMap_fiberCompletionIntegersAlgebra
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    algebraMap P.completionPlace.integers Q.1.completionPlace.integers =
      P.completionIntegersExtension Q.1 Q.2 :=
  P.algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2

@[simp]
theorem coe_algebraMap_fiberCompletionIntegersAlgebra
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : P.completionPlace.integers) :
    (algebraMap P.completionPlace.integers Q.1.completionPlace.integers x : Q.1.Completion) =
      P.completionExtension Q.1 Q.2 x :=
  P.coe_algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2 x

/-- Scalar-tower compatibility `𝒪̂_P → 𝒪̂_Q → F̂'_Q` on a place `Q` in the fiber over `P`. -/
theorem fiberCompletionIntegers_isScalarTower (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsScalarTower P.completionPlace.integers Q.1.completionPlace.integers Q.1.Completion :=
  P.isScalarTower_completionIntegersExtension Q.1 Q.2

/-- Torsion-freeness of `𝒪̂_Q` over `𝒪̂_P` for a place `Q` in the fiber over `P`. -/
theorem fiberCompletionIntegers_isTorsionFree (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.IsTorsionFree P.completionPlace.integers Q.1.completionPlace.integers :=
  P.isTorsionFree_completionIntegersExtension Q.1 Q.2

/-- Locality of `𝒪̂_P →+* 𝒪̂_Q` for a place `Q` in the fiber over `P`. -/
theorem fiberCompletionIntegers_isLocalHom (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsLocalHom (algebraMap P.completionPlace.integers Q.1.completionPlace.integers) :=
  P.isLocalHom_algebraMap_completionIntegersExtensionAlgebra Q.1 Q.2

-- Companion `Prop` instances on fiber places under `[Algebra.IsIntegral F F']`.
scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.fiberCompletionIntegers_isScalarTower
  TauCeti.Place.fiberCompletionIntegers_isTorsionFree
  TauCeti.Place.fiberCompletionIntegers_isLocalHom

end Integral

section Finite

open scoped PlaceCompletion

variable [FiniteDimensional F F'] {P : Place k F}

/-- Finite-dimensionality of `F̂'_Q` over `F̂_P` for a place `Q` in the fiber over `P`. -/
theorem fiberCompletion_finiteDimensional (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    FiniteDimensional P.Completion Q.1.Completion :=
  P.finiteDimensional_completion Q.1 Q.2

/-- Module-finiteness of `𝒪̂_Q` over `𝒪̂_P` for a place `Q` in the fiber over `P`. -/
theorem fiberCompletionIntegers_moduleFinite (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.Finite P.completionPlace.integers Q.1.completionPlace.integers :=
  P.moduleFinite_completionIntegers Q.1 Q.2

/-- Module-freeness of `𝒪̂_Q` over `𝒪̂_P` for a place `Q` in the fiber over `P`. -/
theorem fiberCompletionIntegers_moduleFree (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.Free P.completionPlace.integers Q.1.completionPlace.integers :=
  P.moduleFree_completionIntegers Q.1 Q.2

/-- Integral-closure property of `𝒪̂_Q` over `𝒪̂_P` in `F̂'_Q` for a place `Q` in the fiber over
`P`. -/
theorem fiberCompletionIntegers_isIntegralClosure
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsIntegralClosure Q.1.completionPlace.integers P.completionPlace.integers Q.1.Completion :=
  P.isIntegralClosure_completionIntegers Q.1 Q.2

-- Companion `Prop` instances on fiber places under `[FiniteDimensional F F']`.
scoped[PlaceCompletion] attribute [instance]
  TauCeti.Place.fiberCompletion_finiteDimensional
  TauCeti.Place.fiberCompletionIntegers_moduleFinite
  TauCeti.Place.fiberCompletionIntegers_moduleFree
  TauCeti.Place.fiberCompletionIntegers_isIntegralClosure

end Finite

end FiberInstances

open scoped PlaceCompletion

section Semilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

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
      { P.integralClosureToCompletionIntegers Q.1 Q.2 with
        commutes' := fun r ↦ by
          rw [RingHom.toFun_eq_coe, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
            algebraMap_fiberCompletionIntegersAlgebra, P.algebraMap_completionIntegers,
            AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            P.integralClosureToCompletionIntegers_algebraMap Q.1 Q.2 r] })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
@[simp]
theorem integralSemilocalHom_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralSemilocalHom k' F' P (a ⊗ₜ x) Q =
      P.completionIntegersExtension Q.1 Q.2 a *
        P.integralClosureToCompletionIntegers Q.1 Q.2 x := by
  simp [integralSemilocalHom, algebraMap_fiberCompletionIntegersAlgebra]

/-- The canonical `F̂_P`-algebra homomorphism from `F̂_P ⊗[F] F'` to the product of the completed
fields above `P`. -/
noncomputable def semilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      UniformContinuousConstSMul F (WithVal Q.1.valuation) :=
    WithVal.uniformContinuousConstSMul_of_algebra F Q.1.valuation
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower F P.Completion Q.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
        ← Q.1.completionEmbedding_apply, algebraMap_fiberCompletionAlgebra,
        P.algebraMap_completion_eq_completionEmbedding,
        P.completionExtension_completionEmbedding Q.1 Q.2]
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { Q.1.completionEmbedding.toRingHom with
        commutes' := fun x ↦ by
          rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
            ← Q.1.completionEmbedding_apply] })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
@[simp]
theorem semilocalHom_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalHom k' F' P (a ⊗ₜ x) Q =
      P.completionExtension Q.1 Q.2 a * Q.1.completionEmbedding x := by
  simp [semilocalHom, algebraMap_fiberCompletionAlgebra]

end Maps

section IntegralToField

private noncomputable def completionIntegersToCompletion (P : Place k F) :
    P.completionPlace.integers →ₐ[P.integers] P.Completion where
  toRingHom := P.completionPlace.integers.subtype
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass, ValuationSubring.subtype_apply,
      P.algebraMap_integers_completion_eq_completionEmbedding, P.coe_algebraMap_completionIntegers]

variable (F') in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private noncomputable def integralTensorToBaseChange (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[P.integers] integralClosure P.integers F' :=
  Algebra.TensorProduct.map (completionIntegersToCompletion P)
    (AlgHom.id P.integers (integralClosure P.integers F'))

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private theorem integralTensorToBaseChange_injective (P : Place k F) :
    Function.Injective (integralTensorToBaseChange F' P) := by
  have : Module.IsTorsionFree P.integers (integralClosure P.integers F') :=
    IsIntegralClosure.isTorsionFree P.integers F'
  rw [← AlgHom.coe_toLinearMap, integralTensorToBaseChange, Algebra.TensorProduct.toLinearMap_map,
    AlgHom.toLinearMap_id, TensorProduct.AlgebraTensorModule.map_eq, ← LinearMap.rTensor_def]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private theorem isPushout_integers_integralClosure [Algebra.IsIntegral F F'] (P : Place k F) :
    Algebra.IsPushout P.integers F (integralClosure P.integers F') F' := by
  have := IsIntegralClosure.isLocalization P.integers F F' (integralClosure P.integers F')
  exact (Algebra.isPushout_of_isLocalization (nonZeroDivisors P.integers) F
    (integralClosure P.integers F') F').symm

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private noncomputable def integralFieldBaseChangeEquiv [Algebra.IsIntegral F F'] (P : Place k F) :
    P.Completion ⊗[P.integers] integralClosure P.integers F' ≃ₐ[P.Completion]
      P.Completion ⊗[F] F' := by
  have := isPushout_integers_integralClosure (F' := F') P
  exact (Algebra.TensorProduct.cancelBaseChange P.integers F P.Completion P.Completion
      (integralClosure P.integers F')).symm.trans
    (Algebra.TensorProduct.congr (.refl : P.Completion ≃ₐ[P.Completion] P.Completion)
      (Algebra.IsPushout.equiv P.integers F (integralClosure P.integers F') F'))

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
private theorem integralFieldBaseChangeEquiv_tmul [Algebra.IsIntegral F F'] (P : Place k F)
    (a : P.Completion) (x : integralClosure P.integers F') :
    integralFieldBaseChangeEquiv (F' := F') P (a ⊗ₜ x) = a ⊗ₜ (x : F') := by
  have := isPushout_integers_integralClosure (F' := F') P
  simp [integralFieldBaseChangeEquiv, Algebra.IsPushout.equiv_tmul]

variable [Algebra.IsIntegral F F']

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
        rw [RingHom.toFun_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.algebraMap_apply, integralFieldBaseChangeEquiv_tmul,
          OneMemClass.coe_one] }
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

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
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

end IntegralToField

section Surjective

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k'] (k' F')

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
      isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional (k' := k') P]
    intro P' hP'
    let Q : {P' : Place k' F' // P'.restrict k F = P} := ⟨P', hP'⟩
    exact Q.1.mem_integers_of_sub_mem_filtration
      (Q.1.mem_filtration_zero_iff.mp (y₀ Q).2) (hw_fil Q)
  refine ⟨⟨w, hw_int⟩, fun Q ↦ ?_⟩
  have hsub : Q.1.completionEmbedding w - (y Q : Q.1.Completion) =
      Q.1.completionEmbedding (w - (y₀ Q : F')) -
        ((y Q : Q.1.Completion) - Q.1.completionEmbedding (y₀ Q)) := by
    rw [map_sub, sub_sub_sub_cancel_right]
  rw [hsub]
  exact (Q.1.completionPlace.filtration (ramificationIdx F Q.1)).sub_mem
    (Q.1.completionEmbedding_mem_filtration_iff.mpr (hw_fil Q)) (hy₀ Q)

omit [FiniteDimensional F F'] [Algebra.IsIntegral k k'] in
private theorem pi_mem_maximalIdeal_smul_top_of_forall_mem_filtration
    [Algebra.IsIntegral F F'] (P : Place k F)
    {d : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers}
    (hd : ∀ Q : {P' : Place k' F' // P'.restrict k F = P},
      (d Q : Q.1.Completion) ∈ Q.1.completionPlace.filtration (ramificationIdx F Q.1)) :
    d ∈ (maximalIdeal P.completionPlace.integers • ⊤ :
      Submodule P.completionPlace.integers
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers)) := by
  let π := Submodule.IsPrincipal.generator (maximalIdeal P.completionPlace.integers)
  have hπ : Ideal.span {π} = maximalIdeal P.completionPlace.integers :=
    Ideal.span_singleton_generator _
  have hdiv (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      ∃ zQ : Q.1.completionPlace.integers, π • zQ = d Q := by
    have hQ : d Q ∈ (maximalIdeal P.completionPlace.integers • ⊤ :
        Submodule P.completionPlace.integers Q.1.completionPlace.integers) :=
      P.mem_maximalIdeal_smul_top_of_mem_filtration Q.1 Q.2 (hd Q)
    rw [← hπ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hQ
    obtain ⟨zQ, -, hzQ⟩ := hQ
    exact ⟨zQ, hzQ⟩
  choose z hz using hdiv
  rw [← hπ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨z, Submodule.mem_top, funext hz⟩

/-- **Surjectivity of the integral semilocal map**: for a finite extension `F' / F` and an integral
constant extension `k' / k`, `integralSemilocalHom k' F' P` is surjective. -/
theorem integralSemilocalHom_surjective (P : Place k F) :
    Function.Surjective (integralSemilocalHom k' F' P) := by
  -- Approximate any tuple modulo `𝔪̂_P` by a single global element via weak approximation, then
  -- upgrade to surjectivity by Nakayama's lemma over the local ring `𝒪̂_P`.
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

/-- **Surjectivity of the field semilocal map**: for a finite extension `F' / F` and an integral
constant extension `k' / k`, `semilocalHom k' F' P` is surjective. -/
theorem semilocalHom_surjective (P : Place k F) :
    Function.Surjective (semilocalHom k' F' P) := by
  -- Clear denominators across the finite fiber by a power of a uniformizer of `P` and lift along
  -- `integralSemilocalHom_surjective`.
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
    algebraMap_fiberCompletionAlgebra, hz, map_inv₀,
    inv_mul_cancel_left₀ ((map_ne_zero _).mpr (pow_ne_zero N hπc0))]

end Surjective

section Equivalence

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k'] (k' F')

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
/-- For a finite separable extension `F' / F` and an integral constant extension `k' / k`,
`semilocalHom k' F' P` is injective. -/
theorem semilocalHom_injective (P : Place k F) :
    Function.Injective (semilocalHom k' F' P) := by
  -- A surjective `F̂_P`-linear map between vector spaces of equal finite dimension `[F' : F]` is
  -- injective.
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

/-- As a function, `semilocalEquiv` agrees with `semilocalHom`. -/
theorem coe_semilocalEquiv (P : Place k F) :
    (semilocalEquiv k' F' P :
        (P.Completion ⊗[F] F') →
          ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) =
      semilocalHom k' F' P :=
  funext fun z ↦ by rw [semilocalEquiv, AlgEquiv.ofBijective_apply]

variable {k' F'} in
@[simp]
theorem semilocalEquiv_tmul (P : Place k F) (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalEquiv k' F' P (a ⊗ₜ x) Q =
      P.completionExtension Q.1 Q.2 a * Q.1.completionEmbedding x := by
  rw [semilocalEquiv, AlgEquiv.ofBijective_apply, semilocalHom_tmul]

variable {k' F'} in
@[simp]
theorem semilocalEquiv_symm_completionEmbedding (P : Place k F) (x : F') :
    (semilocalEquiv k' F' P).symm (fun Q ↦ Q.1.completionEmbedding x) = 1 ⊗ₜ x := by
  rw [AlgEquiv.symm_apply_eq]
  funext Q
  simp

/-- For a finite separable extension `F' / F` and an integral constant extension `k' / k`,
`integralSemilocalHom k' F' P` is injective. -/
theorem integralSemilocalHom_injective (P : Place k F) :
    Function.Injective (integralSemilocalHom k' F' P) := by
  -- Embed into `semilocalEquiv` via `integralSemilocalToField_injective`.
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

/-- As a function, `integralSemilocalEquiv` agrees with `integralSemilocalHom`. -/
theorem coe_integralSemilocalEquiv (P : Place k F) :
    (integralSemilocalEquiv k' F' P :
        (P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') →
          ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) =
      integralSemilocalHom k' F' P :=
  funext fun z ↦ by rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply]

variable {k' F'} in
@[simp]
theorem integralSemilocalEquiv_tmul (P : Place k F) (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralSemilocalEquiv k' F' P (a ⊗ₜ x) Q =
      P.completionIntegersExtension Q.1 Q.2 a *
        P.integralClosureToCompletionIntegers Q.1 Q.2 x := by
  rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply, integralSemilocalHom_tmul]

variable {k' F'} in
@[simp]
theorem integralSemilocalEquiv_symm_integralClosureToCompletionIntegers
    (P : Place k F) (x : integralClosure P.integers F') :
    (integralSemilocalEquiv k' F' P).symm
        (fun Q ↦ P.integralClosureToCompletionIntegers Q.1 Q.2 x) = 1 ⊗ₜ x := by
  rw [AlgEquiv.symm_apply_eq]
  funext Q
  simp

variable {k' F'} in
/-- After inclusion into the completions, `integralSemilocalEquiv` agrees with `semilocalEquiv`. -/
theorem integralSemilocalEquiv_fieldCompatibility (P : Place k F)
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    semilocalEquiv k' F' P (integralSemilocalToField F' P z) =
      fun Q ↦ (integralSemilocalEquiv k' F' P z Q : Q.1.Completion) := by
  rw [coe_semilocalEquiv, coe_integralSemilocalEquiv]
  exact integralSemilocalHom_fieldCompatibility P z

variable {k' F'} in
/-- Transporting an integral tuple along `(integralSemilocalEquiv k' F' P).symm` and including into
`F̂_P ⊗[F] F'` agrees with `(semilocalEquiv k' F' P).symm` of the coerced tuple. -/
@[simp]
theorem integralSemilocalToField_integralSemilocalEquiv_symm (P : Place k F)
    (y : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :
    integralSemilocalToField F' P ((integralSemilocalEquiv k' F' P).symm y) =
      (semilocalEquiv k' F' P).symm (fun Q ↦ (y Q : Q.1.Completion)) := by
  rw [AlgEquiv.eq_symm_apply, integralSemilocalEquiv_fieldCompatibility,
    AlgEquiv.apply_symm_apply]

/-! ### Norm and trace in the semilocal decomposition -/

attribute [local instance] Fintype.ofFinite in
/-- The trace of `F̂_P ⊗[F] F'` over `F̂_P` is the sum of the traces of its completed components. -/
theorem trace_eq_sum_trace_semilocalEquiv (P : Place k F) (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (semilocalEquiv k' F' P ξ Q) := by
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

section SinglePlaceTrace

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) • yᵢ` for every
`x ∈ F'`, then the same expansion holds in `F̂'_{P'}` over `F̂_P` after applying
`P'.completionEmbedding`, without assuming `k' / k` is integral. -/
theorem sum_trace_mul_smul_completionEmbedding_eq
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) •
        P'.completionEmbedding (y i) = z := by
  classical
  set Q₀ : {Q : Place k F' // Q.restrict k F = P} :=
    ⟨P'.restrictConstants k, (restrict_restrictConstants k F P').trans hP⟩
  have h' := congrArg (fun ξ ↦ semilocalEquiv k F' P ξ Q₀)
    (TauCeti.Algebra.sum_trace_mul_smul_baseChange_eq (A := P.Completion) b y h
      ((semilocalEquiv k F' P).symm (Pi.single Q₀ z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, semilocalEquiv_tmul, map_one, one_mul,
    trace_semilocalEquiv_symm_single_mul] at h'
  rw [← P.completionExtensionAlgebra_restrictConstants P' hP]
  simpa only [Q₀, fiberCompletionAlgebra, completionEmbedding_restrictConstants] using h'

end SinglePlaceTrace

end Semilocal

end TauCeti.Place
