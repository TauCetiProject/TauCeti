/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.IntegralClosure
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.Localization.Integral

/-!
# Semilocal decomposition, norm, and trace at a completed place

Let `F' / F` be a finite extension of fields over a constant-field extension `k' / k` with `k' / k`
integral, and let `P` be a place of `F / k`. Whenever the local integral closure
`𝒪'_P = integralClosure P.integers F'` is a finite `𝒪_P`-module — which holds automatically when
`F' / F` is separable (`TauCeti.Place.moduleFinite_integralClosure`), and also for any finite
extension of an algebraic function field
(`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`) — completing along `P` decomposes
both the integral and field extensions into the finite product of completions at the places `Q` of
`F' / k'` lying over `P`:

```text
𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q,
F̂_P ⊗[F] F'     ≃ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q.
```

Unlike the number-field proof in `TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/`, the
residue fields here may be arbitrary (infinite or imperfect), so `𝒪̂_P` need not be compact.
Instead, `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` is finite over the complete discrete valuation ring `𝒪̂_P`, hence
`𝔪̂_P`-adically precomplete (`IsPrecomplete.of_finite`), while `∏_{Q ∣ P} 𝒪̂_Q` is `𝔪̂_P`-adically
Hausdorff. Chinese remainder approximation on the Dedekind domain `𝒪'_P` makes the integral
semilocal map surjective modulo `𝔪̂_P`, successive approximation
(`surjective_of_mkQ_comp_surjective`) lifts this to surjectivity on `𝒪̂_P ⊗[𝒪_P] 𝒪'_P`, and
comparing ranks via the fundamental identity `∑_{Q ∣ P} e(Q ∣ P) f(Q ∣ P) = [F' : F]` upgrades
surjectivity to an isomorphism by Orzech's theorem
(`OrzechProperty.bijective_of_surjective_of_finrank_le`). Clearing poles at `P` then yields
the field-level decomposition, from which the local–global trace and norm formulas follow via
`TauCeti.RingTheory.NormTrace.BaseChange` and `TauCeti.RingTheory.NormTrace.Pi`.

The algebra structures `F → F̂_P`, `𝒪_P → 𝒪̂_P`, and the factorwise extension algebras over
`{P' : Place k' F' // P'.restrict k F = P}` are registered in the `PlaceCompletionExtension` scope,
avoiding any overlap with the global `k`-algebra structure on `F̂_P`.

## Main definitions

* `TauCeti.Place.completionIntegersIntegralClosureHom`: the canonical ring map `𝒪'_P →+* 𝒪̂_{P'}`
  for `P' ∣ P`.
* `TauCeti.Place.integralCompletionSemilocalHom` and
  `TauCeti.Place.integralCompletionSemilocalEquiv`: the integral semilocal map and isomorphism
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∀ Q : {P' // P'.restrict k F = P}, 𝒪̂_Q`.
* `TauCeti.Place.completionSemilocalHom` and `TauCeti.Place.completionSemilocalEquiv`: the field
  semilocal map and isomorphism `F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∀ Q : {P' // P'.restrict k F = P}, F̂_Q`.
* `TauCeti.Place.integralCompletionSemilocalToField`: the canonical injection
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪_P] F̂_P ⊗[F] F'`.

## Main results

* `TauCeti.Place.completionIntegersIntegralClosureHom_injective`: the canonical map
  `𝒪'_P →+* 𝒪̂_{P'}` is injective.
* `TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`: `𝒪'_P` is module-finite over
  `𝒪_P` for any finite extension of a function field, without separability.
* `TauCeti.Place.integralCompletionSemilocalEquiv_fieldCompatibility` and
  `TauCeti.Place.integralCompletionSemilocalToField_injective`: compatibility of the integral and
  field semilocal equivalences.
* `TauCeti.Place.completionEmbedding_trace` and `TauCeti.Place.completionEmbedding_norm`: trace and
  norm decompose as the sum and product of local traces and norms over `Q ∣ P`.
* `TauCeti.Place.trace_completionSemilocalEquiv_symm_single_mul` and
  `TauCeti.Place.trace_integralCompletionSemilocalToField_tmul_mul`: componentwise and integral
  trace-pairing formulas used to localize the complementary module at a completion.

## References

* [J.-P. Serre, *Local Fields*][serre1968], Chapter II, §3, Theorem 1 and Corollary 4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.1 and III.4.
* Adapted from the number-field semilocal API in
  `TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/`.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing Module WithZero
open scoped TensorProduct

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section ScopedInstances

section Base

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Scalar multiplication on `WithVal P.valuation` by any `F`-algebra base `S` is uniformly
continuous. Kept as an explicit theorem rather than a global instance so it cannot compete with
`TauCeti.Place.instAlgebraCompletion` at `S = k`. -/
theorem uniformContinuousConstSMul_withVal (P : Place k F) {S : Type*} [CommSemiring S]
    [Algebra S F] :
    UniformContinuousConstSMul S (WithVal P.valuation) := ⟨fun s ↦ by
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal P.valuation)).uniformContinuous_const_smul _⟩

/-- The `F`-algebra structure on `F̂_P` whose scalar multiplication matches
`UniformSpace.Completion.instSMul`. Installed in the `PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionAlgebra (P : Place k F) : Algebra F P.Completion :=
  haveI := P.uniformContinuousConstSMul_withVal (S := F)
  UniformSpace.Completion.algebra (WithVal P.valuation) F

/-- The `𝒪_P`-algebra structure on `F̂_P` whose scalar multiplication matches
`UniformSpace.Completion.instSMul`. Installed in the `PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionIntegersFieldAlgebra (P : Place k F) : Algebra P.integers P.Completion :=
  haveI := P.uniformContinuousConstSMul_withVal (S := P.integers)
  UniformSpace.Completion.algebra (WithVal P.valuation) P.integers

/-- The valuation ring `𝒪_P` acts on its completion `𝒪̂_P` through
`TauCeti.Place.completionIntegersEmbedding`. Installed in the `PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionIntegersAlgebra (P : Place k F) :
    Algebra P.integers P.completionPlace.integers :=
  P.completionIntegersEmbedding.toRingHom.toAlgebra

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionAlgebra
  TauCeti.Place.completionIntegersFieldAlgebra
  TauCeti.Place.completionIntegersAlgebra

open scoped PlaceCompletionExtension

/-- The scoped `F`-algebra structure on `F̂_P` acts via `TauCeti.Place.completionEmbedding`. -/
@[simp]
theorem algebraMap_completion (P : Place k F) (x : F) :
    algebraMap F P.Completion x = P.completionEmbedding x := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, P.completionEmbedding_apply]

/-- The scoped `𝒪_P`-algebra structure on `F̂_P` acts via `TauCeti.Place.completionEmbedding`. -/
@[simp]
theorem algebraMap_completionIntegersFieldAlgebra (P : Place k F) (r : P.integers) :
    algebraMap P.integers P.Completion r = P.completionEmbedding r := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    P.completionEmbedding_apply]
  rfl

/-- The scoped `𝒪_P`-algebra structure on `𝒪̂_P` acts via
`TauCeti.Place.completionIntegersEmbedding`. -/
@[simp]
theorem algebraMap_completionIntegersAlgebra (P : Place k F) (x : P.integers) :
    algebraMap P.integers P.completionPlace.integers x = P.completionIntegersEmbedding x :=
  (rfl)

/-- The scalar tower `𝒪_P → F → F̂_P`. Installed in the `PlaceCompletionExtension` scope. -/
theorem completionIntegersFieldIsScalarTower (P : Place k F) :
    IsScalarTower P.integers F P.Completion :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [algebraMap_completionIntegersFieldAlgebra, algebraMap_completion]
    rfl

/-- The scalar tower `𝒪_P → 𝒪̂_P → F̂_P`. Installed in the `PlaceCompletionExtension` scope. -/
theorem completionIntegersIsScalarTower (P : Place k F) :
    IsScalarTower P.integers P.completionPlace.integers P.Completion :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [algebraMap_completionIntegersFieldAlgebra, ValuationSubring.algebraMap_apply,
      algebraMap_completionIntegersAlgebra, P.completionIntegersEmbedding_apply]

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionIntegersFieldIsScalarTower
  TauCeti.Place.completionIntegersIsScalarTower

end Base

open scoped PlaceCompletionExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- For each place `Q` in the fibre above `P`, the `F`-algebra structure on `F̂_Q` whose scalar
multiplication matches `UniformSpace.Completion.instSMul`. Installed in the
`PlaceCompletionExtension` scope. -/
@[instance_reducible]
def completionFibreBaseAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra F Q.1.Completion :=
  haveI := Q.1.uniformContinuousConstSMul_withVal (S := F)
  UniformSpace.Completion.algebra (WithVal Q.1.valuation) F

/-- For each place `Q` in the fibre above `P`, the local field extension algebra `F̂_P → F̂_Q`.
Installed in the `PlaceCompletionExtension` scope so dependent products over the fibre inherit the
factorwise `F̂_P`-algebra structure without introducing a global self-algebra diamond. -/
@[expose, instance_reducible]
def completionFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.Completion Q.1.Completion :=
  P.completionExtensionAlgebra Q.1 Q.2

/-- For each place `Q` in the fibre above `P`, the local valuation-ring algebra `𝒪̂_P → 𝒪̂_Q`.
Installed in the `PlaceCompletionExtension` scope. -/
@[expose, instance_reducible]
def completionIntegersFibreAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra P.completionPlace.integers Q.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra Q.1 Q.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionFibreBaseAlgebra
  TauCeti.Place.completionFibreAlgebra
  TauCeti.Place.completionIntegersFibreAlgebra

/-- The scoped `F`-algebra map into `F̂_Q` embeds `F` into `F'` and then into `F̂_Q`. -/
theorem algebraMap_completionFibreBaseAlgebra [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) (x : F) :
    algebraMap F Q.1.Completion x = Q.1.completionEmbedding (algebraMap F F' x) := by
  rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
    Q.1.completionEmbedding_apply]

/-- For each place `Q` in the fibre above `P`, `F → F̂_P → F̂_Q` is a scalar tower. Installed in the
`PlaceCompletionExtension` scope. -/
theorem completionFibreIsScalarTower [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    IsScalarTower F P.Completion Q.1.Completion :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [algebraMap_completionFibreBaseAlgebra, algebraMap_completion,
      algebraMap_completionExtensionAlgebra P Q.1 Q.2,
      P.completionExtension_completionEmbedding Q.1 Q.2 x]

/-- For each place `Q` in the fibre above `P`, `𝒪̂_Q` is torsion-free over `𝒪̂_P`. Installed in the
`PlaceCompletionExtension` scope. -/
theorem completionFibreIsTorsionFree [Algebra.IsIntegral F F'] (P : Place k F)
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Module.IsTorsionFree P.completionPlace.integers Q.1.completionPlace.integers :=
  P.isTorsionFree_completionIntegers Q.1 Q.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.completionFibreIsScalarTower
  TauCeti.Place.completionFibreIsTorsionFree

/-- The canonical ring homomorphism from the local integral closure `𝒪'_P` to the completed
valuation ring `𝒪̂_{P'}` at a place `P'` lying over `P`. -/
def completionIntegersIntegralClosureHom [Algebra.IsIntegral F F'] (P : Place k F)
    (P' : Place k' F') (hP : P'.restrict k F = P) :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  P'.completionIntegersEmbedding.toRingHom.comp
    ((algebraMap (integralClosure P.integers F') F').codRestrict P'.integers fun b ↦ by
      subst hP
      exact algebraMap_mem_integers_of_mem_integralClosure k F P' b)

/-- Coercing `completionIntegersIntegralClosureHom` to `F̂_{P'}` is `P'.completionEmbedding`. -/
@[simp]
theorem coe_completionIntegersIntegralClosureHom [Algebra.IsIntegral F F'] (P : Place k F)
    (P' : Place k' F') (hP : P'.restrict k F = P) (b : integralClosure P.integers F') :
    (P.completionIntegersIntegralClosureHom P' hP b : P'.Completion) =
      P'.completionEmbedding (b : F') := by
  simp [completionIntegersIntegralClosureHom]

/-- On `𝒪_P`, `completionIntegersIntegralClosureHom` agrees with `completionIntegersExtension`. -/
@[simp]
theorem completionIntegersIntegralClosureHom_algebraMap [Algebra.IsIntegral F F'] (P : Place k F)
    (P' : Place k' F') (hP : P'.restrict k F = P) (r : P.integers) :
    P.completionIntegersIntegralClosureHom P' hP
        (algebraMap P.integers (integralClosure P.integers F') r) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding r) := by
  apply Subtype.ext
  simp [coe_completionIntegersIntegralClosureHom, IsScalarTower.algebraMap_apply P.integers F F']

/-- The canonical homomorphism `𝒪'_P →+* 𝒪̂_{P'}` is injective. -/
theorem completionIntegersIntegralClosureHom_injective [Algebra.IsIntegral F F'] (P : Place k F)
    (P' : Place k' F') (hP : P'.restrict k F = P) :
    Function.Injective (P.completionIntegersIntegralClosureHom P' hP) := fun a b h ↦ by
  apply Subtype.ext
  exact P'.completionEmbedding.toRingHom.injective (by
    simpa only [coe_completionIntegersIntegralClosureHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using congrArg Subtype.val h)

end ScopedInstances

open scoped PlaceCompletionExtension

section FunctionFieldFinite

open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin

/-- Over an algebraic function field `F / k`, the integral closure `𝒪'_P` of `𝒪_P` in any finite
extension `F' / F` is a finite `𝒪_P`-module, with no separability hypothesis on `F' / F`: it is the
localization at the centre of `P` of the integral closure of `k[t]` in `F'` for a uniformizer `t` at
`P`. -/
theorem moduleFinite_integralClosure_of_isFunctionField {k F F' : Type*} [Field k] [Field F]
    [Field F'] [Algebra k F] [Algebra F F'] [FiniteDimensional F F'] (P : Place k F)
    (hF : IsFunctionField k F) :
    Module.Finite P.integers (integralClosure P.integers F') := by
  let _ : Algebra k F' := Algebra.compHom F' (algebraMap k F)
  have : IsScalarTower k F F' := .of_compHom k F F'
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have htP : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by omega)
  have hti : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin htr
  have : FiniteDimensional k⟮t⟯ F' := Module.Finite.trans F F'
  let R := integralClosure (Algebra.adjoin k {t}) F
  have : IsDedekindDomain R := isDedekindDomain_integralClosure_adjoin hF t
  have : IsFractionRing R F := isFractionRing_integralClosure_adjoin hF htr
  have : Module.Finite R (integralClosure R F') :=
    IsIntegralClosure.finite_integralClosure_integralClosure_adjoin k t F'
  have hR : ∀ r : R, algebraMap R F r ∈ P.integers := fun r ↦
    P.mem_integers_iff.mpr
      (P.forall_algebraMap_mem_integers_integralClosure_adjoin_iff.mpr hti r r.2)
  let p : HeightOneSpectrum R := P.center hR
  let _ : Algebra R P.integers := ((algebraMap R F).codRestrict P.integers hR).toAlgebra
  have : IsScalarTower R P.integers F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R P.integers F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply R F F' x
  let eR : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[R] P.integers :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P.valuationSubringAtPrime_eq_integers hR)))
      fun _ ↦ rfl
  have : IsLocalization p.asIdeal.primeCompl P.integers :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eR
  exact TauCeti.finite_integralClosure_of_isLocalization p.asIdeal.primeCompl P.integers F'

end FunctionFieldFinite

section ToField

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The canonical `𝒪_P`-algebra homomorphism `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪_P] F̂_P ⊗[F] F'`. -/
def integralCompletionSemilocalToField (F' : Type*) [Field F'] [Algebra F F'] (P : Place k F) :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
  Algebra.TensorProduct.lift
    { (Algebra.TensorProduct.includeLeftRingHom : P.Completion →+* P.Completion ⊗[F] F').comp
        (algebraMap P.completionPlace.integers P.Completion) with
      commutes' := fun r ↦ by
        rw [RingHom.toFun_eq_coe, RingHom.comp_apply,
          Algebra.TensorProduct.includeLeftRingHom_apply,
          ← IsScalarTower.algebraMap_apply P.integers P.completionPlace.integers P.Completion,
          Algebra.TensorProduct.algebraMap_apply] }
    { (Algebra.TensorProduct.includeRight : F' →ₐ[F] P.Completion ⊗[F] F').toRingHom.comp
        (algebraMap (integralClosure P.integers F') F') with
      commutes' := fun r ↦ by
        simp only [RingHom.toFun_eq_coe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
        rw [← IsScalarTower.algebraMap_apply P.integers (integralClosure P.integers F') F',
          IsScalarTower.algebraMap_apply P.integers F F',
          ← Algebra.TensorProduct.algebraMap_apply',
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply P.integers F P.Completion] }
    fun _ _ ↦ .all _ _

variable {F' : Type*} [Field F'] [Algebra F F']

/-- `integralCompletionSemilocalToField` acts on pure tensors by coercion in both factors. -/
@[simp]
theorem integralCompletionSemilocalToField_tmul {P : Place k F} (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') :
    integralCompletionSemilocalToField F' P (a ⊗ₜ[P.integers] b) =
      (a : P.Completion) ⊗ₜ[F] (b : F') := by
  simp [integralCompletionSemilocalToField]

/-- The trace of a pure integral tensor paired with `d ∈ F'` is the scalar extension of the global
trace pairing. -/
theorem trace_integralCompletionSemilocalToField_tmul_mul {P : Place k F}
    (a : P.completionPlace.integers) (b : integralClosure P.integers F') (d : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (integralCompletionSemilocalToField F' P (a ⊗ₜ[P.integers] b) * (1 ⊗ₜ[F] d)) =
      (a : P.Completion) * P.completionEmbedding (Algebra.trace F F' ((b : F') * d)) := by
  have ha : (a : P.Completion) ⊗ₜ[F] ((b : F') * d) =
      (a : P.Completion) • ((1 : P.Completion) ⊗ₜ[F] ((b : F') * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [integralCompletionSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, TauCeti.Algebra.trace_baseChange_tmul, smul_eq_mul, algebraMap_completion]

end ToField

section Semilocal

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

section Hom

variable [Algebra.IsIntegral F F'] (k' F') (P : Place k F)

/-- The integral semilocal algebra map `𝒪̂_P ⊗[𝒪_P] 𝒪'_P →ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q` sending `a ⊗ b`
to `(a · b)_Q`. -/
def integralCompletionSemilocalHom :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[
        P.completionPlace.integers]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers :=
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Algebra P.integers Q.1.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers Q.1.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers Q.1.completionPlace.integers :=
    .of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { P.completionIntegersIntegralClosureHom Q.1 Q.2 with
        commutes' := fun r ↦ by
          -- Expose the composite `P.integers`-algebra installed above so the compatibility lemma
          -- for `completionIntegersIntegralClosureHom` applies.
          change P.completionIntegersIntegralClosureHom Q.1 Q.2
              (algebraMap P.integers (integralClosure P.integers F') r) =
            algebraMap P.completionPlace.integers Q.1.completionPlace.integers
              (algebraMap P.integers P.completionPlace.integers r)
          rw [completionIntegersIntegralClosureHom_algebraMap,
            algebraMap_completionIntegersAlgebra,
            algebraMap_completionIntegersExtensionAlgebra] })
    fun _ _ ↦ .all _ _

/-- The field semilocal algebra map `F̂_P ⊗[F] F' →ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q` sending `a ⊗ x` to
`(a · x)_Q`. -/
def completionSemilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun Q ↦
      { Q.1.completionEmbedding.toRingHom with
        commutes' := fun x ↦ (algebraMap_completionFibreBaseAlgebra P Q x).symm })
    fun _ _ ↦ .all _ _

variable {k' F' P}

/-- `integralCompletionSemilocalHom` acts componentwise on pure tensors. -/
@[simp]
theorem integralCompletionSemilocalHom_tmul (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralCompletionSemilocalHom k' F' P (a ⊗ₜ b) Q =
      algebraMap P.completionPlace.integers Q.1.completionPlace.integers a *
        P.completionIntegersIntegralClosureHom Q.1 Q.2 b := by
  simp [integralCompletionSemilocalHom]

/-- `completionSemilocalHom` acts componentwise on pure tensors. -/
@[simp]
theorem completionSemilocalHom_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    completionSemilocalHom k' F' P (a ⊗ₜ x) Q =
      algebraMap P.Completion Q.1.Completion a * Q.1.completionEmbedding x := by
  simp [completionSemilocalHom]

/-- A tuple of completed functions at `Q ∣ P` vanishing to order `e(Q ∣ P)` at every `Q` lies in
`𝔪̂_P • ⊤`. -/
private theorem mem_maximalIdeal_smul_top_of_forall_mem_filtration
    {w : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers}
    (hw : ∀ Q, (w Q : Q.1.Completion) ∈ Q.1.completionPlace.filtration (ramificationIdx F Q.1)) :
    w ∈ (maximalIdeal P.completionPlace.integers • ⊤ :
      Submodule P.completionPlace.integers
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers)) := by
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  let πc := P.completionIntegersEmbedding ⟨π, hπint⟩
  have hπc0 : (πc : P.Completion) ≠ 0 := by simpa [πc] using hπ0
  have hπm : πc ∈ maximalIdeal P.completionPlace.integers := by
    rw [P.completionPlace.mem_maximalIdeal_iff_ord_pos hπc0]
    simp [πc, hπ]
  have hE0 (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      P.completionExtension Q.1 Q.2 πc ≠ 0 := (map_ne_zero _).mpr hπc0
  have hdiv (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      (w Q : Q.1.Completion) / P.completionExtension Q.1 Q.2 πc ∈ Q.1.completionPlace.integers := by
    have hE : Q.1.completionPlace.ord (P.completionExtension Q.1 Q.2 πc) =
        ramificationIdx F Q.1 := by
      simp [πc, ord_algebraMap_restrict k F Q.1, Q.2, hπ]
    rcases eq_or_ne (w Q : Q.1.Completion) 0 with h | h
    · simp [h]
    · rw [mem_integers_iff_ord_nonneg, Q.1.completionPlace.ord_div h (hE0 Q), hE]
      have := (Q.1.completionPlace.mem_filtration_iff_le_ord h).mp (hw Q)
      omega
  have hweq : w = πc • fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
      (⟨_, hdiv Q⟩ : Q.1.completionPlace.integers) := by
    funext Q
    apply Subtype.ext
    rw [Pi.smul_apply, Algebra.smul_def, Subring.coe_mul,
      coe_algebraMap_completionIntegersExtensionAlgebra, mul_div_cancel₀ _ (hE0 Q)]
  rw [hweq]
  exact Submodule.smul_mem_smul hπm Submodule.mem_top

end Hom

section Equiv

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']
variable (k' F') (P : Place k F) [Module.Finite P.integers (integralClosure P.integers F')]

/-- Simultaneous approximation in the completed valuation rings above `P` by an element of the
local integral closure `𝒪'_P`, to precision `e(Q ∣ P)` at each `Q ∣ P`. -/
private theorem exists_forall_sub_completionIntegersIntegralClosureHom_mem_filtration
    (y : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :
    ∃ b : integralClosure P.integers F',
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P},
        ((y Q - P.completionIntegersIntegralClosureHom Q.1 Q.2 b :
            Q.1.completionPlace.integers) : Q.1.Completion) ∈
          Q.1.completionPlace.filtration (ramificationIdx F Q.1) := by
  classical
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  let B := integralClosure P.integers F'
  have : IsDedekindDomain B := integralClosure.isDedekindDomain P.integers F F'
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  have hk' : ∀ c : k', algebraMap k' F' c ∈ B := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' B := ((algebraMap k' F').codRestrict B hk').toAlgebra
  have : IsScalarTower k' B F' := .of_algebraMap_eq fun _ ↦ rfl
  have hB (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      ∀ b : B, algebraMap B F' b ∈ Q.1.integers := fun b ↦ by
    obtain ⟨Q', hQ'⟩ := Q
    subst hQ'
    exact algebraMap_mem_integers_of_mem_integralClosure k F Q' b
  let q (Q : {P' : Place k' F' // P'.restrict k F = P}) : HeightOneSpectrum B := Q.1.center (hB Q)
  have hqinj : Function.Injective q := fun Q₁ Q₂ h ↦ Subtype.ext <|
    (ofPrime_center k' F' Q₁.1 (hB Q₁)).symm.trans
      ((congrArg (ofPrime k' F') h).trans (ofPrime_center k' F' Q₂.1 (hB Q₂)))
  have hval (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Q.1.valuation = (q Q).valuation F' := by
    rw [← ofPrime_center k' F' Q.1 (hB Q), valuation_ofPrime]
  -- Step 1: approximate `y Q` in `F'` by `z Q ∈ 𝒪_Q` to order `e(Q ∣ P)`.
  choose z hz using fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
    Q.1.exists_filtration_sub_completionEmbedding_mem (ramificationIdx F Q.1)
      ⟨y Q, Q.1.completionPlace.mem_filtration_zero_iff.mpr (y Q).2⟩
  -- Step 2: approximate `z Q ∈ 𝒪_Q` by `a Q ∈ B` to order `e(Q ∣ P)` at `q Q`.
  have hzint (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      (q Q).valuation F' (z Q : F') ≤ 1 := by
    rw [← hval Q, ← Q.1.mem_integers_iff]
    exact Q.1.mem_filtration_zero_iff.mp (z Q).2
  choose a ha using fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
    (q Q).exists_valuation_sub_lt_of_integer (hzint Q)
      (Units.mk0 (exp (-(ramificationIdx F Q.1 : ℤ))) exp_ne_zero)
  -- Step 3: glue the local elements `a Q` modulo `(q Q) ^ e(Q ∣ P)` via CRT in `B`.
  obtain ⟨b, hb⟩ := exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦ (q Q).asIdeal)
    (fun Q ↦ ramificationIdx F Q.1) (fun Q _ ↦ (q Q).prime)
    (fun _ _ _ _ hQW h ↦ hQW (hqinj (HeightOneSpectrum.ext h))) (fun Q ↦ a Q.1)
  refine ⟨b, fun Q ↦ ?_⟩
  have hbQ : a Q - b ∈ (q Q).asIdeal ^ ramificationIdx F Q.1 := by
    rw [← neg_sub]
    exact neg_mem (hb Q (Finset.mem_univ Q))
  have h1 : Q.1.completionEmbedding ((z Q : F') - algebraMap B F' (a Q)) ∈
      Q.1.completionPlace.filtration (ramificationIdx F Q.1) := by
    rw [Q.1.completionEmbedding_mem_filtration_iff, Q.1.mem_filtration_iff, hval Q,
      Valuation.map_sub_swap]
    simpa only [Units.val_mk0] using (ha Q).le
  have h2 : Q.1.completionEmbedding (algebraMap B F' (a Q - b)) ∈
      Q.1.completionPlace.filtration (ramificationIdx F Q.1) := by
    rw [Q.1.completionEmbedding_mem_filtration_iff, Q.1.mem_filtration_iff, hval Q,
      (q Q).valuation_of_algebraMap, (q Q).intValuation_le_pow_iff_mem]
    exact hbQ
  have htel : (y Q : Q.1.Completion) -
      (P.completionIntegersIntegralClosureHom Q.1 Q.2 b : Q.1.Completion) =
      ((y Q : Q.1.Completion) - Q.1.completionEmbedding (z Q : F')) +
        Q.1.completionEmbedding ((z Q : F') - algebraMap B F' (a Q)) +
        Q.1.completionEmbedding (algebraMap B F' (a Q - b)) := by
    rw [coe_completionIntegersIntegralClosureHom, map_sub, RingHom.map_sub, map_sub]
    change (y Q : Q.1.Completion) - Q.1.completionEmbedding (algebraMap B F' b) = _
    ring
  rw [AddSubgroupClass.coe_sub, htel]
  exact (Q.1.completionPlace.filtration (ramificationIdx F Q.1)).add_mem
    ((Q.1.completionPlace.filtration (ramificationIdx F Q.1)).add_mem (hz Q) h1) h2

private theorem sub_integralCompletionSemilocalHom_tmul_mem_maximalIdeal_smul_top
    (y : ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers) :
    ∃ b : integralClosure P.integers F',
      integralCompletionSemilocalHom k' F' P (1 ⊗ₜ b) - y ∈
        (maximalIdeal P.completionPlace.integers • ⊤ :
          Submodule P.completionPlace.integers
            (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers)) := by
  obtain ⟨b, hb⟩ :=
    exists_forall_sub_completionIntegersIntegralClosureHom_mem_filtration k' F' P y
  refine ⟨b, ?_⟩
  rw [← Submodule.neg_mem_iff, neg_sub]
  refine mem_maximalIdeal_smul_top_of_forall_mem_filtration fun Q ↦ ?_
  rw [Pi.sub_apply, integralCompletionSemilocalHom_tmul, map_one, one_mul]
  exact hb Q

private theorem mkQ_comp_integralCompletionSemilocalHom_surjective :
    Function.Surjective
      ((Submodule.mkQ (maximalIdeal P.completionPlace.integers • ⊤)).comp
        (integralCompletionSemilocalHom k' F' P).toLinearMap) := by
  intro ybar
  refine Quotient.inductionOn' ybar fun y ↦ ?_
  obtain ⟨b, hb⟩ :=
    sub_integralCompletionSemilocalHom_tmul_mem_maximalIdeal_smul_top k' F' P y
  refine ⟨1 ⊗ₜ b, ?_⟩
  change Submodule.mkQ _ (integralCompletionSemilocalHom k' F' P (1 ⊗ₜ b)) = Submodule.mkQ _ y
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact hb

/-- **The integral semilocal map is surjective** for arbitrary residue fields: `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` is
`𝔪̂_P`-adically precomplete, `∏_{Q ∣ P} 𝒪̂_Q` is Hausdorff, and `𝒪'_P` hits every residue class
modulo `𝔪̂_P`. -/
theorem integralCompletionSemilocalHom_surjective :
    Function.Surjective (integralCompletionSemilocalHom k' F' P) := by
  have : IsPrecomplete (maximalIdeal P.completionPlace.integers)
      (P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :=
    .of_finite _ _
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      IsHausdorff (maximalIdeal P.completionPlace.integers) Q.1.completionPlace.integers :=
    .of_map (map_maximalIdeal_le (algebraMap _ Q.1.completionPlace.integers))
  exact surjective_of_mkQ_comp_surjective (I := maximalIdeal P.completionPlace.integers)
    (f := (integralCompletionSemilocalHom k' F' P).toLinearMap)
    (mkQ_comp_integralCompletionSemilocalHom_surjective k' F' P)

attribute [local instance] Fintype.ofFinite in
/-- Under `[Module.Finite P.integers (integralClosure P.integers F')]`, the local degrees above `P`
sum to `[F' : F]`. -/
theorem sum_finrank_completion_eq_finrank :
    ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
      Module.finrank P.Completion Q.1.Completion = Module.finrank F F' := by
  have : IsDedekindDomain (integralClosure P.integers F') :=
    integralClosure.isDedekindDomain P.integers F F'
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  have hk' : ∀ c : k', algebraMap k' F' c ∈ integralClosure P.integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict (integralClosure P.integers F') hk').toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  let s := (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset
  calc ∑ Q : {P' : Place k' F' // P'.restrict k F = P}, Module.finrank P.Completion Q.1.Completion
      = ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
          ramificationIdx F Q.1 * relativeDegree k F Q.1 :=
        Finset.sum_congr rfl fun Q _ ↦ finrank_completion P Q.1 Q.2
    _ = ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' :=
        Finset.sum_bij (fun Q _ ↦ Q.1)
          (fun Q _ ↦ (finite_setOf_restrict_eq k F P).mem_toFinset.mpr Q.2)
          (fun _ _ _ _ h ↦ Subtype.ext h)
          (fun P' hP' ↦ ⟨⟨P', (finite_setOf_restrict_eq k F P).mem_toFinset.mp hP'⟩,
            Finset.mem_univ _, rfl⟩)
          (fun _ _ ↦ rfl)
    _ = Module.finrank F F' :=
        sum_ramificationIdx_mul_relativeDegree_eq_finrank
          (S := integralClosure P.integers F') k F (P.center hR) fun P' ↦ by
            rw [(finite_setOf_restrict_eq k F P).mem_toFinset, Set.mem_ofPred, ofPrime_center]

attribute [local instance] Fintype.ofFinite in
/-- The integral semilocal map is bijective. -/
theorem integralCompletionSemilocalHom_bijective :
    Function.Bijective (integralCompletionSemilocalHom k' F' P) := by
  have : Module.Free P.integers (integralClosure P.integers F') :=
    Module.free_of_finite_type_torsion_free'
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Finite P.completionPlace.integers Q.1.completionPlace.integers :=
    moduleFinite_completionIntegers P Q.1 Q.2
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.Free P.completionPlace.integers Q.1.completionPlace.integers :=
    moduleFree_completionIntegers P Q.1 Q.2
  refine OrzechProperty.bijective_of_surjective_of_finrank_le
    (integralCompletionSemilocalHom k' F' P).toLinearMap
    (integralCompletionSemilocalHom_surjective k' F' P) ?_
  rw [Module.finrank_baseChange, finrank_integralClosure F' P,
    Module.finrank_pi_fintype, ← sum_finrank_completion_eq_finrank k' F' P]
  refine le_of_eq (Finset.sum_congr rfl fun Q _ ↦ ?_)
  rw [finrank_completion P Q.1 Q.2, finrank_completionIntegers P Q.1 Q.2]

/-- **The integral semilocal decomposition**
`𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ₐ[𝒪̂_P] ∏_{Q ∣ P} 𝒪̂_Q`, valid for arbitrary residue fields. -/
def integralCompletionSemilocalEquiv :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' ≃ₐ[
        P.completionPlace.integers]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.completionPlace.integers :=
  AlgEquiv.ofBijective (integralCompletionSemilocalHom k' F' P)
    (integralCompletionSemilocalHom_bijective k' F' P)

variable {k' F' P} in
/-- `integralCompletionSemilocalEquiv` acts componentwise on pure tensors. -/
@[simp]
theorem integralCompletionSemilocalEquiv_tmul (a : P.completionPlace.integers)
    (b : integralClosure P.integers F') (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    integralCompletionSemilocalEquiv k' F' P (a ⊗ₜ b) Q =
      algebraMap P.completionPlace.integers Q.1.completionPlace.integers a *
        P.completionIntegersIntegralClosureHom Q.1 Q.2 b :=
  integralCompletionSemilocalHom_tmul a b Q

/-- Compatibility of the integral and field semilocal homomorphisms. -/
theorem integralCompletionSemilocalHom_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalHom k' F' P (integralCompletionSemilocalToField F' P z) =
      fun Q ↦ (integralCompletionSemilocalEquiv k' F' P z Q : Q.1.Completion) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext Q
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, AddMemClass.coe_add]
  | tmul a b =>
    funext Q
    rw [integralCompletionSemilocalToField_tmul, completionSemilocalHom_tmul,
      integralCompletionSemilocalEquiv_tmul, MulMemClass.coe_mul,
      coe_algebraMap_completionIntegersExtensionAlgebra, algebraMap_completionExtensionAlgebra,
      coe_completionIntegersIntegralClosureHom]

/-- **The field semilocal map is surjective**: clearing poles at `P` with a uniformizer of `P`
reduces every tuple in `∏_{Q ∣ P} F̂_Q` to the integral semilocal map. -/
theorem completionSemilocalHom_surjective :
    Function.Surjective (completionSemilocalHom k' F' P) := by
  classical
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  intro y
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  have hπc0 : P.completionEmbedding π ≠ 0 := (map_ne_zero _).mpr hπ0
  let N : ℕ := Finset.univ.sup fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
    (Q.1.completionPlace.ord (y Q)).natAbs
  have hyint (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      algebraMap P.Completion Q.1.Completion (P.completionEmbedding π ^ N) * y Q ∈
        Q.1.completionPlace.integers := by
    rcases eq_or_ne (y Q) 0 with h0 | h0
    · simp [h0]
    have hE0 : algebraMap P.Completion Q.1.Completion (P.completionEmbedding π ^ N) ≠ 0 :=
      (map_ne_zero _).mpr (pow_ne_zero N hπc0)
    rw [mem_integers_iff_ord_nonneg, Q.1.completionPlace.ord_mul hE0 h0,
      algebraMap_completionExtensionAlgebra, P.ord_completionExtension Q.1 Q.2,
      P.completionPlace.ord_pow, P.ord_completionEmbedding, hπ, mul_one]
    have he : (1 : ℤ) ≤ ramificationIdx F Q.1 := mod_cast ramificationIdx_pos F Q.1
    have hle : (Q.1.completionPlace.ord (y Q)).natAbs ≤ N :=
      Finset.le_sup (f := fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
        (Q.1.completionPlace.ord (y Q)).natAbs) (Finset.mem_univ Q)
    have hle' : ((Q.1.completionPlace.ord (y Q)).natAbs : ℤ) ≤ N := mod_cast hle
    have habs : -((Q.1.completionPlace.ord (y Q)).natAbs : ℤ) ≤ Q.1.completionPlace.ord (y Q) := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le _
    nlinarith
  obtain ⟨t, ht⟩ := (integralCompletionSemilocalEquiv k' F' P).surjective fun Q ↦ ⟨_, hyint Q⟩
  refine ⟨(P.completionEmbedding π ^ N)⁻¹ • integralCompletionSemilocalToField F' P t, ?_⟩
  funext Q
  rw [map_smul, integralCompletionSemilocalHom_fieldCompatibility, ht, Pi.smul_apply,
    Algebra.smul_def, map_inv₀]
  have hE0 : algebraMap P.Completion Q.1.Completion (P.completionEmbedding π ^ N) ≠ 0 :=
    (map_ne_zero _).mpr (pow_ne_zero N hπc0)
  exact inv_mul_cancel_left₀ hE0 (y Q)

attribute [local instance] Fintype.ofFinite in
/-- The field semilocal map is bijective. -/
theorem completionSemilocalHom_bijective :
    Function.Bijective (completionSemilocalHom k' F' P) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  have hdim : Module.finrank P.Completion (P.Completion ⊗[F] F') =
      Module.finrank P.Completion
        (∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype,
      ← sum_finrank_completion_eq_finrank k' F' P]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (completionSemilocalHom k' F' P).toLinearMap)).mpr
        (completionSemilocalHom_surjective k' F' P),
    completionSemilocalHom_surjective k' F' P⟩

/-- **The field semilocal decomposition**
`F̂_P ⊗[F] F' ≃ₐ[F̂_P] ∏_{Q ∣ P} F̂_Q`, valid for arbitrary residue fields. -/
def completionSemilocalEquiv :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.1.Completion :=
  AlgEquiv.ofBijective (completionSemilocalHom k' F' P) (completionSemilocalHom_bijective k' F' P)

variable {k' F' P} in
/-- `completionSemilocalEquiv` acts componentwise on pure tensors. -/
@[simp]
theorem completionSemilocalEquiv_tmul (a : P.Completion) (x : F')
    (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    completionSemilocalEquiv k' F' P (a ⊗ₜ x) Q =
      algebraMap P.Completion Q.1.Completion a * Q.1.completionEmbedding x :=
  completionSemilocalHom_tmul a x Q

/-- After inclusion into the completions, `integralCompletionSemilocalEquiv` agrees with
`completionSemilocalEquiv`. -/
theorem integralCompletionSemilocalEquiv_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalEquiv k' F' P (integralCompletionSemilocalToField F' P z) =
      fun Q ↦ (integralCompletionSemilocalEquiv k' F' P z Q : Q.1.Completion) :=
  integralCompletionSemilocalHom_fieldCompatibility k' F' P z

/-! ### Norm and trace in the semilocal decomposition -/

attribute [local instance] Fintype.ofFinite in
/-- The norm of `F̂_P ⊗[F] F'` over `F̂_P` is the product of the norms of its semilocal
components. -/
theorem norm_eq_prod_norm_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (completionSemilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  rw [← Algebra.norm_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact TauCeti.Algebra.norm_pi _

attribute [local instance] Fintype.ofFinite in
variable {F'} in
/-- **Local–global norm decomposition**: the norm of `x ∈ F'` in `F̂_P` is the product of its local
norms across the places `Q` of `F' / k'` lying over `P`. -/
theorem completionEmbedding_norm (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.norm P.Completion (Q.1.completionEmbedding x) := by
  rw [← algebraMap_completion,
    ← TauCeti.Algebra.norm_baseChange_tmul (A := P.Completion) (B := F') x,
    norm_eq_prod_norm_completionSemilocalEquiv k' F' P]
  exact Finset.prod_congr rfl fun Q _ ↦ by simp

attribute [local instance] Fintype.ofFinite in
/-- The trace of `F̂_P ⊗[F] F'` over `F̂_P` is the sum of the traces of its semilocal components. -/
theorem trace_eq_sum_trace_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (completionSemilocalEquiv k' F' P ξ Q) := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      FiniteDimensional P.Completion Q.1.Completion :=
    finiteDimensional_completion P Q.1 Q.2
  rw [← Algebra.trace_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact TauCeti.Algebra.trace_pi _

attribute [local instance] Fintype.ofFinite in
variable {F'} in
/-- **Local–global trace decomposition**: the trace of `x ∈ F'` in `F̂_P` is the sum of its local
traces across the places `Q` of `F' / k'` lying over `P`. -/
theorem completionEmbedding_trace (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ Q : {P' : Place k' F' // P'.restrict k F = P},
        Algebra.trace P.Completion Q.1.Completion (Q.1.completionEmbedding x) := by
  rw [← algebraMap_completion,
    ← TauCeti.Algebra.trace_baseChange_tmul (A := P.Completion) (B := F') x,
    trace_eq_sum_trace_completionSemilocalEquiv k' F' P]
  exact Finset.sum_congr rfl fun Q _ ↦ by simp

variable {k' F' P} in
attribute [local instance] Fintype.ofFinite in
/-- An element of `F̂_{P'}`, placed in the `P'`-component of `F̂_P ⊗[F] F'`, has the same trace
pairing with `x ∈ F'` as in `F̂_{P'}`. -/
theorem trace_completionSemilocalEquiv_symm_single_mul
    [DecidableEq {Q : Place k' F' // Q.restrict k F = P}]
    (P' : Place k' F') (hP : P'.restrict k F = P) (z : P'.Completion) (x : F') :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((completionSemilocalEquiv k' F' P).symm
          (Pi.single (⟨P', hP⟩ : {Q : Place k' F' // Q.restrict k F = P}) z) * (1 ⊗ₜ x)) =
      Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding x) := by
  rw [trace_eq_sum_trace_completionSemilocalEquiv k' F' P, Finset.sum_eq_single
    (⟨P', hP⟩ : {Q : Place k' F' // Q.restrict k F = P})]
  · simp
  · intro Q _ hQ
    rw [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_of_ne hQ, zero_mul,
      map_zero]
  · simp

end Equiv

end Semilocal

section ToFieldInjective

/-- The canonical map `𝒪̂_P ⊗[𝒪_P] 𝒪'_P → F̂_P ⊗[F] F'` is injective. -/
theorem integralCompletionSemilocalToField_injective {k F F' : Type*} [Field k] [Field F]
    [Field F'] [Algebra k F] [Algebra F F'] [FiniteDimensional F F'] (P : Place k F)
    [Module.Finite P.integers (integralClosure P.integers F')] :
    Function.Injective (integralCompletionSemilocalToField F' P) := fun x y h ↦ by
  let _ : Algebra k F' := Algebra.compHom F' (algebraMap k F)
  have : IsScalarTower k F F' := .of_compHom k F F'
  apply (integralCompletionSemilocalEquiv k F' P).injective
  funext Q
  apply Subtype.ext
  exact congrFun ((integralCompletionSemilocalEquiv_fieldCompatibility k F' P x).symm.trans
    ((congrArg (completionSemilocalEquiv k F' P) h).trans
      (integralCompletionSemilocalEquiv_fieldCompatibility k F' P y))) Q

end ToFieldInjective

end TauCeti.Place
