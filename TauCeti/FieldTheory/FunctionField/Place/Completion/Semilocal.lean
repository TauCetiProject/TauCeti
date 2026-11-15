/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.FieldTheory.FunctionField.Place.Approximation
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.NormTrace.Pi

/-!
# The semilocal decomposition at a place

Let `F' / k'` be a finite separable extension of a field `F / k` with an integral constant-field
extension `k' / k`, and let `P` be a place of `F / k`. Every place `w` of `F' / k'` lying over `P`
gives a completed field `w.Completion` over `P.Completion` and a completed valuation ring
`w.completionPlace.integers` over `P.completionPlace.integers`. Assembling these completions over
the finite fibre `{Q' : Place k' F' // Q'.restrict k F = P}` yields the field and integral
**semilocal decompositions**

```text
P.Completion ⊗[F] F' ≃ₐ[P.Completion] ∏_{w ∣ P} w.Completion,
P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
  ≃ₐ[P.completionPlace.integers] ∏_{w ∣ P} w.completionPlace.integers.
```

Neither `IsFunctionField` nor finiteness or separability of the residue fields is assumed. Because
the residue fields may be infinite, the completed valuation ring `P.completionPlace.integers` need
not be compact, so surjectivity of the integral semilocal map cannot be deduced from compactness of
finitely generated submodules. Instead, weak approximation
(`TauCeti.Place.exists_forall_ord_sub_eq`) and the characterization of
`integralClosure P.integers F'` as the intersection of the valuation rings above `P` show that the
integral semilocal map is surjective modulo the maximal ideal of `P.completionPlace.integers`;
Nakayama's lemma over the adically complete ring `P.completionPlace.integers`
(`AdicCompletion.surjective_of_mkQ_comp_surjective`) lifts this to surjectivity on the nose.
Clearing denominators by powers of a uniformizer of `P` gives surjectivity on the completed fields,
and the local degree formula `[w.Completion : P.Completion] = e(w ∣ P) · f(w ∣ P)` together with
the fundamental identity `∑_{w ∣ P} e(w ∣ P) · f(w ∣ P) = [F' : F]` supplies injectivity. Over a
general discretely valued field `(F, P)` without a function-field hypothesis, separability of
`F' / F` is genuinely needed: over a non-excellent valuation ring `𝒪_P`, the scalar extension
`P.Completion ⊗[F] F'` of an inseparable extension can acquire nilpotent elements whereas
`∏_{w ∣ P} w.Completion` is reduced.

Restricting constants from `k'` to `k` makes the semilocal decomposition available with no
hypothesis on `k' / k` at all, and transferring formal étaleness across it shows that each
completed extension `P.Completion → w.Completion` is separable
(`TauCeti.Place.isSeparable_completion`), even when the residue extension is inseparable.

## Main definitions

* `TauCeti.Place.completionSemilocalHom` and `TauCeti.Place.completionSemilocalEquiv`: the
  semilocal `P.Completion`-algebra isomorphism `P.Completion ⊗[F] F' ≃ₐ[P.Completion]
  ∏_{w ∣ P} w.1.Completion`.
* `TauCeti.Place.integralClosureToCompletionIntegers`: the canonical injective ring homomorphism
  `integralClosure P.integers F' →+* P'.completionPlace.integers` for `P'` lying over `P`.
* `TauCeti.Place.completionIntegersSemilocalHom` and
  `TauCeti.Place.completionIntegersSemilocalEquiv`: the integral semilocal isomorphism
  `P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
  ≃ₐ[P.completionPlace.integers] ∏_{w ∣ P} w.1.completionPlace.integers`.
* `TauCeti.Place.completionIntegersSemilocalToField`: the canonical injective map from the
  integral tensor product to the field tensor product.

## Main results

* `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable`: an element of a
  finite separable extension `F' / F` is integral over `P.integers` if and only if it belongs to
  `P'.integers` for every place `P'` above `P`, with no function-field hypothesis.
* `TauCeti.Place.sum_finrank_completion_eq_finrank`: `∑_{w ∣ P} [w.1.Completion : P.Completion] =
  [F' : F]`.
* `TauCeti.Place.norm_eq_prod_norm_completionSemilocalEquiv`,
  `TauCeti.Place.completionEmbedding_norm_eq_prod_norm`,
  `TauCeti.Place.trace_eq_sum_trace_completionSemilocalEquiv`, and
  `TauCeti.Place.completionEmbedding_trace_eq_sum_trace`: global norm and trace decompose into the
  product and sum of local norms and traces above `P`.
* `TauCeti.Place.isSeparable_completion` and
  `TauCeti.Place.isSeparable_fractionRing_completionIntegers`: completion preserves separability
  of the field extension, with no assumption on the constant fields or residue fields.

## Implementation notes

The algebra structures `Algebra F P.Completion`, `Algebra P.integers P.completionPlace.integers`,
and the extension algebras on `w.1.Completion` and `w.1.completionPlace.integers` for
`w : {Q' : Place k' F' // Q'.restrict k F = P}` are registered in the `PlaceCompletionExtension`
scope, mirroring `AdicCompletionExtension` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Completion.lean`. On `P.Completion`, the algebras
use `UniformSpace.Completion.algebra` so their scalar actions agree definitionally with the
inherited uniform-completion scalar actions. The semilocal maps, integral base-change
compatibility, and norm/trace identities adapt
`TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/` from compact number-field completions to
arbitrary discretely valued place completions.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §8, nos. 2 and 5.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.3 and III.1.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing Module UniformSpace
open scoped TensorProduct nonZeroDivisors

namespace TauCeti.Place

section Instances

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Constant scalar multiplication by any `F`-algebra base `S` on `WithVal P.valuation` is
uniformly continuous, since it acts by ring multiplication in `WithVal P.valuation`. -/
instance uniformContinuousConstSMul_withVal {S : Type*} [CommSemiring S] [Algebra S F]
    (P : Place k F) : UniformContinuousConstSMul S (WithVal P.valuation) := ⟨fun l ↦ by
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal P.valuation)).uniformContinuous_const_smul _⟩

/-- The canonical `F`-algebra structure on `P.Completion`, whose scalar action agrees
definitionally with `UniformSpace.Completion.instSMul`. Installed at low priority in the
`PlaceCompletionExtension` scope so that for `F = k` it never competes with
`P.instAlgebraCompletion`. -/
@[instance_reducible]
def completionFieldAlgebra (P : Place k F) : Algebra F P.Completion :=
  UniformSpace.Completion.algebra (WithVal P.valuation) F

scoped[PlaceCompletionExtension] attribute [instance 10]
  TauCeti.Place.completionFieldAlgebra

/-- The canonical `P.integers`-algebra structure on `P.Completion`, whose scalar action agrees
definitionally with `UniformSpace.Completion.instSMul`. -/
@[instance_reducible]
def completionIntegersToCompletionAlgebra (P : Place k F) :
    Algebra P.integers P.Completion :=
  UniformSpace.Completion.algebra (WithVal P.valuation) P.integers

scoped[PlaceCompletionExtension] attribute [instance 100]
  TauCeti.Place.completionIntegersToCompletionAlgebra

/-- The canonical `P.integers`-algebra structure on `P.completionPlace.integers` given by
`P.completionIntegersEmbedding`, compatible with `completionIntegersToCompletionAlgebra`. -/
@[instance_reducible]
def completionIntegersAlgebra (P : Place k F) :
    Algebra P.integers P.completionPlace.integers :=
  P.completionIntegersEmbedding.toRingHom.toAlgebra

scoped[PlaceCompletionExtension] attribute [instance 10]
  TauCeti.Place.completionIntegersAlgebra

open scoped PlaceCompletionExtension in
@[simp]
theorem algebraMap_completionFieldAlgebra (P : Place k F) (x : F) :
    algebraMap F P.Completion x = P.completionEmbedding x :=
  (P.completionEmbedding_apply x).symm

open scoped PlaceCompletionExtension in
@[simp]
theorem algebraMap_completionIntegersAlgebra (P : Place k F) (x : P.integers) :
    algebraMap P.integers P.completionPlace.integers x = P.completionIntegersEmbedding x :=
  (rfl)

open scoped PlaceCompletionExtension in
theorem isScalarTower_integers_completionFieldAlgebra (P : Place k F) :
    IsScalarTower P.integers F P.Completion :=
  .of_algebraMap_eq fun _ ↦ rfl

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isScalarTower_integers_completionFieldAlgebra

open scoped PlaceCompletionExtension in
theorem isScalarTower_completionIntegersAlgebra (P : Place k F) :
    IsScalarTower P.integers P.completionPlace.integers P.Completion :=
  .of_algebraMap_eq fun r ↦
    (P.completionEmbedding_apply (r : F)).symm.trans (P.completionIntegersEmbedding_apply r).symm

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isScalarTower_completionIntegersAlgebra

open scoped PlaceCompletionExtension in
/-- The completed valuation ring `P.completionPlace.integers` is torsion-free over `P.integers`. -/
theorem isTorsionFree_completionIntegersAlgebra (P : Place k F) :
    Module.IsTorsionFree P.integers P.completionPlace.integers := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro x y h
  apply Subtype.ext
  apply (algebraMap F P.Completion).injective
  simpa only [algebraMap_completionFieldAlgebra, algebraMap_completionIntegersAlgebra,
    completionIntegersEmbedding_apply] using congrArg Subtype.val h

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isTorsionFree_completionIntegersAlgebra

section FibreInstances

variable [Algebra.IsIntegral F F'] {P : Place k F}
  (w : {Q' : Place k' F' // Q'.restrict k F = P})

/-- For a place `w` in the fibre over `P`, `w.1.Completion` is a `P.Completion`-algebra in the
`PlaceCompletionExtension` scope. -/
@[expose, instance_reducible]
def instCompletionExtensionAlgebraSubtype : Algebra P.Completion w.1.Completion :=
  P.completionExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.instCompletionExtensionAlgebraSubtype

/-- For a place `w` in the fibre over `P`, `w.1.completionPlace.integers` is a
`P.completionPlace.integers`-algebra in the `PlaceCompletionExtension` scope. -/
@[expose, instance_reducible]
def instCompletionIntegersExtensionAlgebraSubtype :
    Algebra P.completionPlace.integers w.1.completionPlace.integers :=
  P.completionIntegersExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.instCompletionIntegersExtensionAlgebraSubtype

open scoped PlaceCompletionExtension in
theorem algebraMap_completionExtensionAlgebra_subtype :
    algebraMap P.Completion w.1.Completion = P.completionExtension w.1 w.2 :=
  P.algebraMap_completionExtensionAlgebra w.1 w.2

open scoped PlaceCompletionExtension in
theorem algebraMap_completionIntegersExtensionAlgebra_subtype :
    algebraMap P.completionPlace.integers w.1.completionPlace.integers =
      P.completionIntegersExtension w.1 w.2 :=
  P.algebraMap_completionIntegersExtensionAlgebra w.1 w.2

open scoped PlaceCompletionExtension in
theorem isTorsionFree_completionIntegers_subtype :
    Module.IsTorsionFree P.completionPlace.integers w.1.completionPlace.integers :=
  P.isTorsionFree_completionIntegersExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isTorsionFree_completionIntegers_subtype

open scoped PlaceCompletionExtension in
theorem isScalarTower_completionIntegers_subtype :
    IsScalarTower P.completionPlace.integers w.1.completionPlace.integers w.1.Completion :=
  P.isScalarTower_completionIntegersExtensionAlgebra w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isScalarTower_completionIntegers_subtype

variable [FiniteDimensional F F']

open scoped PlaceCompletionExtension in
theorem finiteDimensional_completion_subtype :
    FiniteDimensional P.Completion w.1.Completion :=
  P.finiteDimensional_completion w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.finiteDimensional_completion_subtype

open scoped PlaceCompletionExtension in
theorem moduleFinite_completionIntegers_subtype :
    Module.Finite P.completionPlace.integers w.1.completionPlace.integers :=
  P.moduleFinite_completionIntegers w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.moduleFinite_completionIntegers_subtype

open scoped PlaceCompletionExtension in
theorem moduleFree_completionIntegers_subtype :
    Module.Free P.completionPlace.integers w.1.completionPlace.integers :=
  P.moduleFree_completionIntegers w.1 w.2

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.moduleFree_completionIntegers_subtype

end FibreInstances

end Instances

open scoped PlaceCompletionExtension

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section IntegralClosureIntersection

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- **The integral closure of `P.integers` in a finite separable extension is the intersection of
the valuation rings above `P`.** Unlike
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`, no `IsFunctionField` hypothesis is
required: `integralClosure P.integers F'` is a Dedekind domain with fraction field `F'`, and every
height-one prime of it contracts to the maximal ideal of `P.integers` and therefore comes from a
place of `F' / k'` lying over `P`. -/
theorem isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable (P : Place k F) {x : F'} :
    IsIntegral P.integers x ↔ ∀ P' : Place k' F', P'.restrict k F = P → x ∈ P'.integers := by
  refine ⟨fun hx P' hP' ↦ P'.mem_integers_of_isIntegral (fun a ↦ ?_) hx, fun h ↦ ?_⟩
  · subst hP'
    exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  have hk' : ∀ c : k', algebraMap k' F' c ∈ integralClosure P.integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict (integralClosure P.integers F') hk').toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  have hpmax : (P.center hR).asIdeal = maximalIdeal P.integers :=
    IsLocalRing.eq_maximalIdeal (P.center hR).isMaximal
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := integralClosure P.integers F') F' x fun 𝔓 ↦ by
      have : 𝔓.asIdeal.IsMaximal := 𝔓.isMaximal
      have hunder : 𝔓.asIdeal.under P.integers = (P.center hR).asIdeal :=
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under P.integers 𝔓.asIdeal)).trans
          hpmax.symm
      have : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal := ⟨hunder.symm⟩
      have hres : (ofPrime k' F' 𝔓).restrict k F = P :=
        (restrict_ofPrime k F (P.center hR) 𝔓).trans (ofPrime_center k F P hR)
      simpa only [mem_integers_iff, valuation_ofPrime] using h (ofPrime k' F' 𝔓) hres
  exact hy ▸ y.2

end IntegralClosureIntersection

section Semilocal

variable {k : Type*} (k' : Type*) {F : Type*} (F' : Type*)
  [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  (P : Place k F)

section Maps

variable [Algebra.IsIntegral F F']

/-- The canonical semilocal map `P.Completion ⊗[F] F' →ₐ[P.Completion] ∏_{w ∣ P} w.1.Completion`
sending `a ⊗ x` to `(a · x)_w`. -/
def completionSemilocalHom :
    P.Completion ⊗[F] F' →ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) :=
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) : Algebra F w.1.Completion :=
    UniformSpace.Completion.algebra (WithVal w.1.valuation) F
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsScalarTower F F' w.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      congrArg (UniformSpace.Completion.coeRingHom (α := WithVal w.1.valuation))
        (IsScalarTower.algebraMap_apply F F' (WithVal w.1.valuation) x)
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsScalarTower F P.Completion w.1.Completion :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply F F' w.1.Completion, algebraMap_completionFieldAlgebra,
        algebraMap_completionExtensionAlgebra_subtype, algebraMap_completionFieldAlgebra,
        P.completionExtension_completionEmbedding w.1 w.2]
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦ IsScalarTower.toAlgHom F F' w.1.Completion)
    fun _ _ ↦ .all _ _

variable {k' F' P} in
/-- The semilocal map on a pure tensor. -/
@[simp]
theorem completionSemilocalHom_tmul (a : P.Completion) (x : F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionSemilocalHom k' F' P (a ⊗ₜ x) w =
      P.completionExtension w.1 w.2 a * w.1.completionEmbedding x := by
  simp [completionSemilocalHom, algebraMap_completionExtensionAlgebra_subtype]

variable {k' F'} in
/-- An element of `integralClosure P.integers F'` is regular at every place `P'` lying over `P`. -/
private theorem coe_mem_integers_of_restrict_eq (P' : Place k' F') (hP : P'.restrict k F = P)
    (x : integralClosure P.integers F') :
    algebraMap (integralClosure P.integers F') F' x ∈ P'.integers :=
  P'.mem_integers_of_isIntegral (R := P.integers)
    (fun a ↦ (mem_integers_restrict_iff k F P' (a : F)).mp (hP.symm ▸ a.2))
    x.2

variable {k' F'} in
/-- The canonical embedding of `integralClosure P.integers F'` into the completed valuation ring
at a place `P'` lying over `P`. -/
def integralClosureToCompletionIntegers (P' : Place k' F') (hP : P'.restrict k F = P) :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  P'.completionIntegersEmbedding.toRingHom.comp
    ((algebraMap (integralClosure P.integers F') F').codRestrict P'.integers
      fun x ↦ P.coe_mem_integers_of_restrict_eq P' hP x)

variable {k' F' P} in
@[simp]
theorem coe_integralClosureToCompletionIntegers (P' : Place k' F') (hP : P'.restrict k F = P)
    (x : integralClosure P.integers F') :
    (P.integralClosureToCompletionIntegers P' hP x : P'.Completion) =
      P'.completionEmbedding (x : F') :=
  (P'.completionIntegersEmbedding_apply _).trans
    (congrArg P'.completionEmbedding (RingHom.codRestrict_apply _ _ _ x))

variable {k' F'} in
/-- The embedding `integralClosure P.integers F' →+* P'.completionPlace.integers` is injective. -/
theorem integralClosureToCompletionIntegers_injective (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    Function.Injective (P.integralClosureToCompletionIntegers P' hP) := fun x y h ↦ by
  apply Subtype.ext
  apply (algebraMap F' P'.Completion).injective
  simpa only [algebraMap_completionFieldAlgebra, coe_integralClosureToCompletionIntegers]
    using congrArg Subtype.val h

/-- The canonical integral semilocal map from
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'` to
`∏_{w ∣ P} w.1.completionPlace.integers`. -/
def completionIntegersSemilocalHom :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
      →ₐ[P.completionPlace.integers]
        ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :=
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      Algebra P.integers w.1.completionPlace.integers :=
    ((algebraMap P.completionPlace.integers w.1.completionPlace.integers).comp
      (algebraMap P.integers P.completionPlace.integers)).toAlgebra
  letI (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsScalarTower P.integers P.completionPlace.integers w.1.completionPlace.integers :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦
      { P.integralClosureToCompletionIntegers w.1 w.2 with
        commutes' := fun r ↦ by
          -- Expose the composite `P.integers`-algebra on `w.1.completionPlace.integers` installed
          -- above and compare both sides inside `w.1.Completion`.
          change P.integralClosureToCompletionIntegers w.1 w.2
              (algebraMap P.integers (integralClosure P.integers F') r) =
            algebraMap P.completionPlace.integers w.1.completionPlace.integers
              (algebraMap P.integers P.completionPlace.integers r)
          apply Subtype.ext
          rw [coe_integralClosureToCompletionIntegers,
            algebraMap_completionIntegersExtensionAlgebra_subtype,
            algebraMap_completionIntegersAlgebra, coe_completionIntegersExtension,
            completionIntegersEmbedding_apply, completionExtension_completionEmbedding]
          rfl })
    fun _ _ ↦ .all _ _

variable {k' F' P} in
/-- The integral semilocal map on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalHom_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionIntegersSemilocalHom k' F' P (a ⊗ₜ x) w =
      P.completionIntegersExtension w.1 w.2 a *
        P.integralClosureToCompletionIntegers w.1 w.2 x := by
  simp [completionIntegersSemilocalHom, algebraMap_completionIntegersExtensionAlgebra_subtype]

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
/-- The canonical `P.integers`-algebra homomorphism from the integral tensor product
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'` to the field tensor
product `P.Completion ⊗[F] F'`. -/
def completionIntegersSemilocalToField :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' →ₐ[P.integers]
      P.Completion ⊗[F] F' :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : P.Completion →ₐ[F] P.Completion ⊗[F] F').restrictScalars
      P.integers |>.comp (IsScalarTower.toAlgHom P.integers P.completionPlace.integers
        P.Completion))
    ((Algebra.TensorProduct.includeRight : F' →ₐ[F] P.Completion ⊗[F] F').restrictScalars
      P.integers |>.comp (IsScalarTower.toAlgHom P.integers (integralClosure P.integers F') F'))
    fun _ _ ↦ .all _ _

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
variable {F' P} in
/-- The map to the field tensor product on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalToField_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F') :
    completionIntegersSemilocalToField F' P (a ⊗ₜ x) = (a : P.Completion) ⊗ₜ[F] (x : F') := by
  simp [completionIntegersSemilocalToField]

variable {k' F' P} in
/-- After inclusion into the completions, the integral and field semilocal maps agree. -/
theorem completionIntegersSemilocalHom_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalHom k' F' P (completionIntegersSemilocalToField F' P z) =
      fun w ↦ (completionIntegersSemilocalHom k' F' P z w : w.1.Completion) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    funext w
    simp [congrFun hx w, congrFun hy w]
  | tmul a x =>
    funext w
    simp

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
/-- The canonical map from the integral tensor product to the field tensor product is injective:
`F` is the fraction field of `P.integers`, so tensoring over `F` agrees with tensoring over
`P.integers`, and both `P.Completion` and `F'` are torsion-free hence flat over the Dedekind domain
`P.integers`. -/
theorem completionIntegersSemilocalToField_injective :
    Function.Injective (completionIntegersSemilocalToField F' P) := by
  have := IsLocalization.tensorProduct_compatibleSMul P.integers⁰ F P.Completion F'
  let e : (P.Completion ⊗[F] F') →ₗ[P.integers] (P.Completion ⊗[P.integers] F') :=
    TensorProduct.mapOfCompatibleSMul P.integers F P.integers P.Completion F'
  let f₁ : P.completionPlace.integers →ₗ[P.integers] P.Completion :=
    (IsScalarTower.toAlgHom P.integers P.completionPlace.integers P.Completion).toLinearMap
  let f₂ : integralClosure P.integers F' →ₗ[P.integers] F' :=
    (IsScalarTower.toAlgHom P.integers (integralClosure P.integers F') F').toLinearMap
  have hcomp : e.comp (completionIntegersSemilocalToField F' P).toLinearMap =
      TensorProduct.map f₁ f₂ :=
    TensorProduct.ext' fun a x ↦ by simp [e, f₁, f₂]
  have hinj : Function.Injective (TensorProduct.map f₁ f₂) :=
    TensorProduct.map_injective_of_flat_flat f₁ f₂ Subtype.val_injective Subtype.val_injective
  intro x y hxy
  exact hinj <| DFunLike.congr_fun hcomp x ▸ DFunLike.congr_fun hcomp y ▸ congrArg e hxy

end Maps

section Equiv

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- Simultaneous approximation in the product of completed valuation rings above `P`, modulo the
maximal ideal of `P.completionPlace.integers`: every tuple `y` agrees modulo
`maximalIdeal P.completionPlace.integers • ⊤` with the image of some
`x ∈ integralClosure P.integers F'`. -/
private theorem exists_integralClosure_sub_mem_maximalIdeal_smul
    (y : (w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :
    ∃ x : integralClosure P.integers F',
      y - completionIntegersSemilocalHom k' F' P (1 ⊗ₜ x) ∈
        (maximalIdeal P.completionPlace.integers • ⊤ :
          Submodule P.completionPlace.integers
            ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers)) := by
  -- Approximate each `y w` in `F'` to order `e(w ∣ P)`, then combine the approximations by weak
  -- approximation on the finite fibre above `P`.
  choose y₀ hy₀ using fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦
    w.1.exists_sub_completionEmbedding_mem_filtration (y w) (ramificationIdx F w.1)
  obtain ⟨x, hx⟩ := exists_forall_ord_sub_eq
    (P := fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦ w.1)
    Subtype.val_injective y₀ (fun w ↦ ramificationIdx F w.1)
  have hxmem : ∀ w : {Q' : Place k' F' // Q'.restrict k F = P},
      (y w : w.1.Completion) - w.1.completionEmbedding x ∈
        w.1.completionPlace.filtration (ramificationIdx F w.1) := fun w ↦ by
    have hne : x - y₀ w ≠ 0 := fun h ↦ by
      have := hx w
      rw [h, ord_zero] at this
      exact (ramificationIdx_pos F w.1).ne' (Int.natCast_inj.mp this.symm)
    have hxy₀ : w.1.completionEmbedding (y₀ w) - w.1.completionEmbedding x ∈
        w.1.completionPlace.filtration (ramificationIdx F w.1) := by
      have h' : w.1.completionEmbedding x - w.1.completionEmbedding (y₀ w) ∈
          w.1.completionPlace.filtration (ramificationIdx F w.1) := by
        rw [← map_sub, completionEmbedding_mem_filtration_iff, w.1.mem_filtration_iff_le_ord hne,
          hx w]
      simpa only [neg_sub] using (w.1.completionPlace.filtration _).neg_mem h'
    simpa only [sub_add_sub_cancel] using (w.1.completionPlace.filtration _).add_mem (hy₀ w) hxy₀
  have hxint : IsIntegral P.integers x :=
    (isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable (k' := k') P).mpr
      fun P' hP' ↦ by
        have h0 := P'.completionPlace.filtration_antitone
          (Nat.cast_nonneg (ramificationIdx F P')) (hxmem ⟨P', hP'⟩)
        have hmem := (P'.completionPlace.filtration 0).sub_mem
          (P'.completionPlace.mem_filtration_zero_iff.mpr (y ⟨P', hP'⟩).2) h0
        rw [sub_sub_cancel, P'.completionPlace.mem_filtration_zero_iff] at hmem
        simpa only [mem_integers_iff, completionPlace_valuation, valuation_completionEmbedding]
          using hmem
  refine ⟨⟨x, hxint⟩, ?_⟩
  let πc := Submodule.IsPrincipal.generator (maximalIdeal P.completionPlace.integers)
  have hπc : maximalIdeal P.completionPlace.integers = Ideal.span {πc} :=
    (Ideal.span_singleton_generator _).symm
  have hcomp : ∀ w : {Q' : Place k' F' // Q'.restrict k F = P},
      ∃ z : w.1.completionPlace.integers,
        y w - completionIntegersSemilocalHom k' F' P (1 ⊗ₜ ⟨x, hxint⟩) w = πc • z := fun w ↦ by
    have hm := mem_maximalIdeal_smul_top_of_mem_filtration P w.1 w.2
      (z := y w - completionIntegersSemilocalHom k' F' P (1 ⊗ₜ ⟨x, hxint⟩) w)
      (by simpa using hxmem w)
    rw [hπc, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hm
    obtain ⟨z, -, hz⟩ := hm
    exact ⟨z, hz.symm⟩
  choose z hz using hcomp
  rw [hπc, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨z, Submodule.mem_top, funext fun w ↦ (hz w).symm⟩

/-- **The integral semilocal map is surjective.** It is surjective modulo the maximal ideal of
`P.completionPlace.integers` by weak approximation, and `P.completionPlace.integers` is adically
complete while the target is a finite product of Hausdorff modules. -/
theorem completionIntegersSemilocalHom_surjective :
    Function.Surjective (completionIntegersSemilocalHom k' F' P) := by
  refine (Module.Finite.exists_fin' P.completionPlace.integers
    (P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).elim
    fun n h ↦ h.elim fun g hg ↦ ?_
  have (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
      IsHausdorff (maximalIdeal P.completionPlace.integers) w.1.completionPlace.integers :=
    .of_map (map_maximalIdeal_le (algebraMap P.completionPlace.integers
      w.1.completionPlace.integers))
  let M : Submodule P.completionPlace.integers
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :=
    maximalIdeal P.completionPlace.integers • ⊤
  refine Function.Surjective.of_comp (g := g) <|
    surjective_of_mkQ_comp_surjective (I := maximalIdeal P.completionPlace.integers)
      (f := (completionIntegersSemilocalHom k' F' P).toLinearMap.comp g) fun q ↦ ?_
  refine (Submodule.mkQ_surjective M q).elim fun y hy ↦ ?_
  refine (exists_integralClosure_sub_mem_maximalIdeal_smul k' F' P y).elim fun x hx ↦ ?_
  refine (hg (1 ⊗ₜ x)).elim fun v hv ↦ ⟨v, ?_⟩
  exact ((congrArg (fun t ↦ M.mkQ (completionIntegersSemilocalHom k' F' P t)) hv).trans
    ((Submodule.Quotient.eq M).mpr (neg_sub y _ ▸ M.neg_mem hx))).trans hy

/-- **The field semilocal map is surjective**: multiplying a tuple of completed elements by a
sufficiently high power of a uniformizer of `P` clears all poles simultaneously, reducing to
`TauCeti.Place.completionIntegersSemilocalHom_surjective`. -/
theorem completionSemilocalHom_surjective :
    Function.Surjective (completionSemilocalHom k' F' P) := by
  have := Fintype.ofFinite {Q' : Place k' F' // Q'.restrict k F = P}
  intro y
  obtain ⟨π, hπ0, hπ⟩ := P.exists_ne_zero_ord_eq 1
  set πc : P.Completion := P.completionEmbedding π
  have hπc0 : πc ≠ 0 := by simpa [πc] using hπ0
  let N : ℕ := Finset.univ.sup fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦
    (w.1.completionPlace.ord (y w)).natAbs
  have hreg : ∀ w : {Q' : Place k' F' // Q'.restrict k F = P},
      (πc ^ N) • y w ∈ w.1.completionPlace.integers := fun w ↦ by
    rw [Algebra.smul_def, algebraMap_completionExtensionAlgebra_subtype, map_pow]
    rcases eq_or_ne (y w) 0 with hy0 | hy0
    · simp [hy0]
    have hE0 : P.completionExtension w.1 w.2 πc ≠ 0 := (map_ne_zero _).mpr hπc0
    rw [mem_integers_iff_ord_nonneg, w.1.completionPlace.ord_mul (pow_ne_zero N hE0) hy0,
      w.1.completionPlace.ord_pow, ord_completionExtension, ord_completionEmbedding, hπ, mul_one]
    have he : (1 : ℤ) ≤ ramificationIdx F w.1 := by exact_mod_cast ramificationIdx_pos F w.1
    have hle : (w.1.completionPlace.ord (y w)).natAbs ≤ N :=
      Finset.le_sup (f := fun w : {Q' : Place k' F' // Q'.restrict k F = P} ↦
        (w.1.completionPlace.ord (y w)).natAbs) (Finset.mem_univ w)
    have hle' : ((w.1.completionPlace.ord (y w)).natAbs : ℤ) ≤ N := by exact_mod_cast hle
    rw [Int.natCast_natAbs] at hle'
    nlinarith [neg_abs_le (w.1.completionPlace.ord (y w))]
  obtain ⟨z, hz⟩ := completionIntegersSemilocalHom_surjective k' F' P fun w ↦ ⟨_, hreg w⟩
  refine ⟨(πc ^ N)⁻¹ • completionIntegersSemilocalToField F' P z, funext fun w ↦ ?_⟩
  have hzw : (completionIntegersSemilocalHom k' F' P z w : w.1.Completion) = (πc ^ N) • y w :=
    congrArg Subtype.val (congrFun hz w)
  rw [map_smul, Pi.smul_apply,
    congrFun (completionIntegersSemilocalHom_fieldCompatibility z) w, hzw,
    inv_smul_smul₀ (pow_ne_zero N hπc0)]

attribute [local instance] Fintype.ofFinite in
/-- **The local degrees above `P` sum to the global degree**:
`∑_{w ∣ P} [w.1.Completion : P.Completion] = [F' : F]`. -/
theorem sum_finrank_completion_eq_finrank :
    ∑ w : {Q' : Place k' F' // Q'.restrict k F = P},
        finrank P.Completion w.1.Completion = finrank F F' := by
  classical
  let s := (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset
  have hs : ∀ Q' : Place k' F', Q' ∈ s ↔ Q'.restrict k F = P := fun _ ↦ Set.Finite.mem_toFinset _
  calc ∑ w : {Q' : Place k' F' // Q'.restrict k F = P}, finrank P.Completion w.1.Completion
      = ∑ w : {Q' : Place k' F' // Q'.restrict k F = P},
          ramificationIdx F w.1 * relativeDegree k F w.1 :=
        Finset.sum_congr rfl fun w _ ↦ P.finrank_completion w.1 w.2
    _ = ∑ Q' ∈ s, ramificationIdx F Q' * relativeDegree k F Q' := by
        rw [← Finset.sum_attach s]
        exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun Q' ↦ (hs Q').symm) _ _ fun _ ↦ rfl
    _ = finrank F F' := sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P hs

attribute [local instance] Fintype.ofFinite in
/-- **The field semilocal map is injective**: domain and codomain have the same finite dimension
over `P.Completion`, and the map is surjective. -/
theorem completionSemilocalHom_injective :
    Function.Injective (completionSemilocalHom k' F' P) := by
  have hdim : finrank P.Completion (P.Completion ⊗[F] F') =
      finrank P.Completion ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange, sum_finrank_completion_eq_finrank]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (completionSemilocalHom k' F' P).toLinearMap)).mpr
    (completionSemilocalHom_surjective k' F' P)

/-- **The semilocal decomposition at a place**: `P.Completion ⊗[F] F' ≃ₐ[P.Completion]
∏_{w ∣ P} w.1.Completion`. -/
def completionSemilocalEquiv :
    P.Completion ⊗[F] F' ≃ₐ[P.Completion]
      ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.Completion) :=
  -- Keep `Function.Bijective` explicit so `AlgEquiv.ofBijective_apply` rewrites cleanly at
  -- `instances` transparency without unfolding a raw conjunction.
  AlgEquiv.ofBijective (completionSemilocalHom k' F' P)
    (show Function.Bijective (completionSemilocalHom k' F' P) from
      ⟨completionSemilocalHom_injective k' F' P, completionSemilocalHom_surjective k' F' P⟩)

theorem coe_completionSemilocalEquiv :
    ⇑(completionSemilocalEquiv k' F' P) = completionSemilocalHom k' F' P := by
  rw [completionSemilocalEquiv, AlgEquiv.coe_ofBijective]

variable {k' F' P} in
/-- The semilocal equivalence on a pure tensor. -/
@[simp]
theorem completionSemilocalEquiv_tmul (a : P.Completion) (x : F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionSemilocalEquiv k' F' P (a ⊗ₜ x) w =
      P.completionExtension w.1 w.2 a * w.1.completionEmbedding x := by
  rw [completionSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact completionSemilocalHom_tmul a x w

/-- The integral semilocal map is injective, since it embeds into the field semilocal equivalence
by `TauCeti.Place.completionIntegersSemilocalToField_injective`. -/
theorem completionIntegersSemilocalHom_injective :
    Function.Injective (completionIntegersSemilocalHom k' F' P) := by
  intro x y hxy
  apply completionIntegersSemilocalToField_injective F' P
  apply completionSemilocalHom_injective k' F' P
  rw [completionIntegersSemilocalHom_fieldCompatibility,
    completionIntegersSemilocalHom_fieldCompatibility, hxy]

/-- **The integral semilocal decomposition at a place**:
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
≃ₐ[P.completionPlace.integers] ∏_{w ∣ P} w.1.completionPlace.integers`. -/
def completionIntegersSemilocalEquiv :
    P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'
      ≃ₐ[P.completionPlace.integers]
        ((w : {Q' : Place k' F' // Q'.restrict k F = P}) → w.1.completionPlace.integers) :=
  -- Keep `Function.Bijective` explicit so `AlgEquiv.ofBijective_apply` rewrites cleanly.
  AlgEquiv.ofBijective (completionIntegersSemilocalHom k' F' P)
    (show Function.Bijective (completionIntegersSemilocalHom k' F' P) from
      ⟨completionIntegersSemilocalHom_injective k' F' P,
        completionIntegersSemilocalHom_surjective k' F' P⟩)

theorem coe_completionIntegersSemilocalEquiv :
    ⇑(completionIntegersSemilocalEquiv k' F' P) = completionIntegersSemilocalHom k' F' P := by
  rw [completionIntegersSemilocalEquiv, AlgEquiv.coe_ofBijective]

variable {k' F' P} in
/-- The integral semilocal equivalence on a pure tensor. -/
@[simp]
theorem completionIntegersSemilocalEquiv_tmul (a : P.completionPlace.integers)
    (x : integralClosure P.integers F')
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    completionIntegersSemilocalEquiv k' F' P (a ⊗ₜ x) w =
      P.completionIntegersExtension w.1 w.2 a *
        P.integralClosureToCompletionIntegers w.1 w.2 x := by
  rw [completionIntegersSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact completionIntegersSemilocalHom_tmul a x w

variable {k' F' P} in
/-- After inclusion into the completions, the integral semilocal equivalence agrees with the field
semilocal equivalence. -/
theorem completionIntegersSemilocalEquiv_fieldCompatibility
    (z : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    completionSemilocalEquiv k' F' P (completionIntegersSemilocalToField F' P z) =
      fun w ↦ (completionIntegersSemilocalEquiv k' F' P z w : w.1.Completion) := by
  rw [coe_completionSemilocalEquiv, coe_completionIntegersSemilocalEquiv]
  exact completionIntegersSemilocalHom_fieldCompatibility z

/-! ### Norm and trace in the semilocal decomposition -/

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k'] in
/-- The trace of a pure integral tensor paired with a global element is a scalar extension of the
global trace pairing. -/
theorem trace_completionIntegersSemilocalToField_tmul_mul
    (a : P.completionPlace.integers) (x : integralClosure P.integers F') (d : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (completionIntegersSemilocalToField F' P (a ⊗ₜ x) * (1 ⊗ₜ d)) =
      (a : P.Completion) * P.completionEmbedding (Algebra.trace F F' ((x : F') * d)) := by
  have ha : (a : P.Completion) ⊗ₜ[F] ((x : F') * d) =
      (a : P.Completion) • ((1 : P.Completion) ⊗ₜ[F] ((x : F') * d)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [completionIntegersSemilocalToField_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha,
    map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul, algebraMap_completionFieldAlgebra]

attribute [local instance] Fintype.ofFinite in
/-- The norm of `P.Completion ⊗[F] F'` over `P.Completion` is the product of the norms of its
semilocal components. -/
theorem norm_eq_prod_norm_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.norm P.Completion ξ =
      ∏ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (completionSemilocalEquiv k' F' P ξ w) := by
  rw [← Algebra.norm_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact Algebra.norm_pi _

attribute [local instance] Fintype.ofFinite in
/-- **Global norm equals the product of local norms** above `P`. -/
theorem completionEmbedding_norm_eq_prod_norm (x : F') :
    P.completionEmbedding (Algebra.norm F x) =
      ∏ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.norm P.Completion (w.1.completionEmbedding x) := by
  calc P.completionEmbedding (Algebra.norm F x)
      = Algebra.norm P.Completion ((1 : P.Completion) ⊗ₜ[F] x) := by
        rw [← algebraMap_completionFieldAlgebra, Algebra.norm_baseChange_tmul]
    _ = ∏ w : {Q' : Place k' F' // Q'.restrict k F = P},
          Algebra.norm P.Completion
            (completionSemilocalEquiv k' F' P ((1 : P.Completion) ⊗ₜ[F] x) w) :=
        norm_eq_prod_norm_completionSemilocalEquiv k' F' P _
    _ = _ := Finset.prod_congr rfl fun w _ ↦ by simp

attribute [local instance] Fintype.ofFinite in
/-- The trace of `P.Completion ⊗[F] F'` over `P.Completion` is the sum of the traces of its
semilocal components. -/
theorem trace_eq_sum_trace_completionSemilocalEquiv (ξ : P.Completion ⊗[F] F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ξ =
      ∑ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.trace P.Completion w.1.Completion (completionSemilocalEquiv k' F' P ξ w) := by
  rw [← Algebra.trace_eq_of_algEquiv (completionSemilocalEquiv k' F' P)]
  exact Algebra.trace_pi _

attribute [local instance] Fintype.ofFinite in
/-- **Global trace equals the sum of local traces** above `P`. -/
theorem completionEmbedding_trace_eq_sum_trace (x : F') :
    P.completionEmbedding (Algebra.trace F F' x) =
      ∑ w : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.trace P.Completion w.1.Completion (w.1.completionEmbedding x) := by
  rw [← algebraMap_completionFieldAlgebra,
    ← Algebra.trace_baseChange_tmul (A := P.Completion) (B := F') x,
    trace_eq_sum_trace_completionSemilocalEquiv k' F' P]
  exact Finset.sum_congr rfl fun w _ ↦ by simp

open scoped Classical in
attribute [local instance] Fintype.ofFinite in
/-- An element of `w.1.Completion`, placed in the `w`-component of `P.Completion ⊗[F] F'`, has the
same trace pairing with a global element as in `w.1.Completion`. -/
theorem trace_completionSemilocalEquiv_symm_single_mul
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) (z : w.1.Completion) (x : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((completionSemilocalEquiv k' F' P).symm (Pi.single w z) * (1 ⊗ₜ x)) =
      Algebra.trace P.Completion w.1.Completion (z * w.1.completionEmbedding x) := by
  classical
  rw [trace_eq_sum_trace_completionSemilocalEquiv k' F' P, Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp [Pi.single_eq_of_ne hw']
  · simp

variable {k' F' P} in
/-- Each completed factor in the semilocal decomposition of a finite separable extension is
separable over `P.Completion`. -/
theorem isSeparable_completion_subtype
    (w : {Q' : Place k' F' // Q'.restrict k F = P}) :
    Algebra.IsSeparable P.Completion w.1.Completion := by
  have := Fintype.ofFinite {Q' : Place k' F' // Q'.restrict k F = P}
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  have hpi : Algebra.FormallyEtale P.Completion
      ((u : {Q' : Place k' F' // Q'.restrict k F = P}) → u.1.Completion) :=
    Algebra.FormallyEtale.of_equiv (completionSemilocalEquiv k' F' P)
  exact (Algebra.FormallyEtale.iff_isSeparable P.Completion w.1.Completion).mp
    ((Algebra.FormallyEtale.pi_iff (R := P.Completion)
      (A := fun u : {Q' : Place k' F' // Q'.restrict k F = P} ↦ u.1.Completion)).mp hpi w)

scoped[PlaceCompletionExtension] attribute [instance]
  TauCeti.Place.isSeparable_completion_subtype

end Equiv

end Semilocal

section SeparableCompletion

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **Completion preserves separability of the field extension.** If `F' / F` is finite and
separable and `P'` lies over `P`, then `P'.Completion` is separable over `P.Completion` — with no
integrality hypothesis on `k' / k` and no separability hypothesis on the residue extension.

Restricting constants of `P'` to `k` via `TauCeti.Place.restrictScalars` places `P'.Completion` as
a factor of the formally étale `P.Completion`-algebra
`P.Completion ⊗[F] F' ≃ ∏_{w ∣ P} w.Completion`. -/
theorem isSeparable_completion :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion :=
  Eq.mp
    (congrArg (@Algebra.IsSeparable P.Completion P'.Completion _ _)
      (P.completionExtensionAlgebra_restrictScalars P' hP))
    (isSeparable_completion_subtype (k' := k) (F' := F') (P := P)
      ⟨P'.restrictScalars k, (P'.restrict_restrictScalars (k := k) (F := F)).trans hP⟩)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- Separability of `P'.Completion / P.Completion`, transported to the canonical fraction fields
`FractionRing P.completionPlace.integers` and `FractionRing P'.completionPlace.integers` consumed
by Mathlib's `differentIdeal` API. -/
theorem isSeparable_fractionRing_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Algebra.IsSeparable (FractionRing P.completionPlace.integers)
      (FractionRing P'.completionPlace.integers) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have : Algebra.IsSeparable P.Completion P'.Completion := isSeparable_completion P P' hP
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv P.completionPlace.integers P.Completion).symm.toRingEquiv
    (FractionRing.algEquiv P'.completionPlace.integers P'.Completion).symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext P.completionPlace.integers⁰
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P'.completionPlace.integers
    P'.Completion, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

end SeparableCompletion

end TauCeti.Place

end
end
