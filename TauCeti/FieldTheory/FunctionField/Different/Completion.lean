/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant

import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Different.Localization
import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily
import TauCeti.RingTheory.DedekindDomain.Different.Localization

/-!
# The trace-dual different under completion

Let `F' / k'` be an extension of the field extension `F / k` such that `F' / F` is finite and
separable and `k' / k` is integral, and let `P'` be a place of `F' / k'` lying over the place `P`
of `F / k`.  Completion sends the local model `𝒪_P ⊆ 𝒪'_P` to the extension of complete discrete
valuation rings `𝒪̂_P ⊆ 𝒪̂_{P'}` inside the finite separable extension `F̂'_{P'} / F̂_P`.  This file
proves that the trace-dual different survives completion without any hypothesis on the residue
extension:

* the trace dual of `𝒪̂_{P'}` over `𝒪̂_P` is spanned over `𝒪̂_{P'}` by the image of the trace dual
  of `𝒪'_P` over `𝒪_P`;
* the different ideal of `𝒪'_P / 𝒪_P` generates in `𝒪̂_{P'}` the different ideal of
  `𝒪̂_{P'} / 𝒪̂_P`, and the same holds for any affine model `B ⊆ C` on which `P'` is finite;
* the completed different ideal is `𝔪̂_{P'} ^ d(P' ∣ P)`, so its multiplicity at `𝔪̂_{P'}` equals
  the different exponent `d(P' ∣ P)`;
* an element `z ∈ F̂'_{P'}` lies in the completed complementary module `Ĉ_{P'}` if and only if
  `v_{P'}(z) ≤ exp d(P' ∣ P)`;
* the `𝒪̂_P`-length of `Ĉ_{P'} / 𝒪̂_{P'}` and the order of the discriminant of any `𝒪̂_P`-basis of
  `𝒪̂_{P'}` both equal `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full relative residue
  degree, including any inseparable factor.

No separability of the residue extension, no perfectness of the constants, and no function-field
hypothesis are assumed.  In particular, fierce extensions with inseparable residue fields are
covered on the same footing as separable-residue extensions.

The proof follows the trace-dual family pattern of
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`, replacing the tensor-product
semilocal isomorphism with the spanning theorems
`TauCeti.Place.span_completionIntegers_pi_eq_top` and `TauCeti.Place.span_completion_pi_eq_top` and
the trace formula `TauCeti.Place.completionEmbedding_trace_of_isSeparable`.  As elsewhere in the
local-model and completion API, the action `TauCeti.Place.algebraIntegersExtension` is installed
locally at low priority, and `TauCeti.Place.completionExtensionAlgebra` and
`TauCeti.Place.completionIntegersExtensionAlgebra` are installed explicitly in each statement.  The
comparison equations are not `@[simp]` lemmas because their left-hand sides do not determine the
base place `P`.

## Main definitions

* `TauCeti.Place.completionIntegersOfIntegralClosure`: the canonical ring homomorphism
  `𝒪'_P →+* 𝒪̂_{P'}` from the local integral closure to the completed valuation ring at `P'`.

## Main results

* `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`: a trace-dual expansion of `F' / F`
  remains one of `F̂'_{P'} / F̂_P`.
* `TauCeti.Place.span_traceDual_one_eq_traceDual_one_completionIntegers`: the completed trace dual
  is spanned by the local trace dual.
* `TauCeti.Place.extended_dual_one_eq_dual_one_completionIntegers`: the same statement for
  fractional ideals.
* `TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers`: the different ideal of
  the local model commutes with completion.
* `TauCeti.Place.differentIdeal_completionIntegers_eq_maximalIdeal_pow` and
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers`: the completed different ideal is
  `𝔪̂_{P'} ^ d(P' ∣ P)`, of multiplicity `d(P' ∣ P)`.
* `TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`: the valuation criterion for
  the completed complementary module.
* `TauCeti.Place.length_traceDual_quotient_completionIntegers`: the length of `Ĉ_{P'} / 𝒪̂_{P'}`
  over `𝒪̂_P` is `d(P' ∣ P) · f(P' ∣ P)`.
* `TauCeti.Place.ord_discr_completionIntegers` and
  `TauCeti.Place.ord_completionPlace_discr_completionIntegers`: the discriminant order of any
  `𝒪̂_P`-basis of `𝒪̂_{P'}` is `d(P' ∣ P) · f(P' ∣ P)`.
* `TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers_of_mem_integers` and
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers_eq_multiplicity_center`: the
  different ideal of an arbitrary affine model `B ⊆ C` extends to the completed different ideal,
  preserving its multiplicity at the centre of `P'`.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter III, §§2–4 (Proposition 10).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.4 and IV.2.
-/

public section

open IsDedekindDomain IsLocalRing Module

open scoped nonZeroDivisors

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section Embedding

variable [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)

/-- The canonical ring homomorphism from the local integral closure `𝒪'_P` to the completed
valuation ring `𝒪̂_{P'}` at a place `P'` lying over `P`. -/
noncomputable def completionIntegersOfIntegralClosure :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  (P'.completionEmbedding.toRingHom.comp
    (algebraMap (integralClosure P.integers F') F')).codRestrict
    P'.completionPlace.integers.toSubring fun b ↦ by
      subst hP
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ValuationSubring.mem_toSubring]
      simpa only [completionIntegersEmbedding_apply] using
        (P'.completionIntegersEmbedding
          ⟨algebraMap _ F' b, algebraMap_mem_integers_of_mem_integralClosure k F P' b⟩).2

@[simp]
theorem coe_completionIntegersOfIntegralClosure (b : integralClosure P.integers F') :
    (P.completionIntegersOfIntegralClosure P' hP b : P'.Completion) =
      P'.completionEmbedding (algebraMap (integralClosure P.integers F') F' b) := by
  simp [completionIntegersOfIntegralClosure]

/-- The canonical embedding `𝒪'_P →+* 𝒪̂_{P'}` is injective. -/
theorem completionIntegersOfIntegralClosure_injective :
    Function.Injective (P.completionIntegersOfIntegralClosure P' hP) := fun _ _ h ↦
  Subtype.ext <| P'.completionEmbedding.injective <| by
    simpa only [coe_completionIntegersOfIntegralClosure, Subalgebra.algebraMap_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using congrArg Subtype.val h

end Embedding

section TraceDual

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) yᵢ` for every
`x ∈ F'`, then `z = ∑ᵢ Tr_{F̂'_{P'}/F̂_P}(z bᵢ) yᵢ` for every `z ∈ F̂'_{P'}`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  classical
  let τ := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := fun Q' : τ ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  have _ := Fintype.ofFinite τ
  -- Consider the `F̂_P`-linear endomorphism of `∏_{Q' ∣ P} F̂'_{Q'}` built from the trace-dual sum.
  let Φ : (∀ Q' : τ, Q'.1.Completion) →ₗ[P.Completion] (∀ Q' : τ, Q'.1.Completion) :=
    { toFun w Q' := ∑ i,
        (∑ R' : τ, Algebra.trace P.Completion R'.1.Completion
          (w R' * R'.1.completionEmbedding (b i))) • Q'.1.completionEmbedding (y i)
      map_add' w₁ w₂ := funext fun Q' ↦ by
        simp only [Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib, add_smul]
      map_smul' c w := funext fun Q' ↦ by
        simp only [Pi.smul_apply, smul_mul_assoc, map_smul, ← Finset.smul_sum, smul_assoc,
          RingHom.id_apply] }
  -- On diagonal elements from `F'`, the trace formula turns `Φ` into the identity.
  have hΦ : Φ = LinearMap.id := by
    refine LinearMap.ext_on_range (span_completion_pi_eq_top k' F' P) fun x ↦ funext fun Q' ↦ ?_
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
    have htr (i : ι) :
        ∑ R' : τ, Algebra.trace P.Completion R'.1.Completion
            (R'.1.completionEmbedding x * R'.1.completionEmbedding (b i)) =
          P.completionEmbedding (Algebra.trace F F' (x * b i)) := by
      simp_rw [← map_mul, ← finsum_eq_sum_of_fintype]
      exact (completionEmbedding_trace_of_isSeparable k' P (x * b i)).symm
    calc
      ∑ i, (∑ R' : τ, Algebra.trace P.Completion R'.1.Completion
          (R'.1.completionEmbedding x * R'.1.completionEmbedding (b i))) •
            Q'.1.completionEmbedding (y i)
        = ∑ i, P.completionEmbedding (Algebra.trace F F' (x * b i)) •
            Q'.1.completionEmbedding (y i) := Finset.sum_congr rfl fun i _ ↦ by rw [htr i]
      _ = ∑ i, Q'.1.completionEmbedding (Algebra.trace F F' (x * b i) • y i) :=
          Finset.sum_congr rfl fun i _ ↦ (completionEmbedding_smul P Q'.1 Q'.2 _ _).symm
      _ = Q'.1.completionEmbedding (∑ i, Algebra.trace F F' (x * b i) • y i) := (map_sum ..).symm
      _ = Q'.1.completionEmbedding x := by rw [h x]
  -- Evaluate `Φ = id` on `z` placed in the `P'`-component.
  have hsingle := congrFun (LinearMap.congr_fun hΦ (Pi.single ⟨P', hP⟩ z)) ⟨P', hP⟩
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply, Pi.single_eq_same] at hsingle
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hsingle
  congr 1
  rw [Finset.sum_eq_single_of_mem (⟨P', hP⟩ : τ) (Finset.mem_univ _)
    fun R' _ hR' ↦ by simp [Pi.single_eq_of_ne hR'], Pi.single_eq_same]

/-- The image in `F̂'_{P'}` of an element of the trace dual of `𝒪'_P` over `𝒪_P` lies in the trace
dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem completionEmbedding_mem_traceDual_completionIntegers {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  classical
  let τ := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := fun Q' : τ ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let _ := fun Q' : τ ↦ P.completionIntegersExtensionAlgebra Q'.1 Q'.2
  have _ := Fintype.ofFinite τ
  -- The sum of local traces paired with `d` is `𝒪̂_P`-linear on `∏_{Q' ∣ P} 𝒪̂_{Q'}` and takes
  -- values in `𝒪̂_P` on the diagonal image of functions regular above `P`, hence everywhere.
  let ψ : (∀ Q' : τ, Q'.1.completionPlace.integers) →ₗ[P.completionPlace.integers] P.Completion :=
    { toFun m := ∑ Q' : τ, Algebra.trace P.Completion Q'.1.Completion
        (Q'.1.completionEmbedding d * (m Q' : Q'.1.Completion))
      map_add' m₁ m₂ := by
        simp only [Pi.add_apply, AddMemClass.coe_add, mul_add, map_add, Finset.sum_add_distrib]
      map_smul' c m := by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun Q' _ ↦ ?_
        have hcm : ((c • m Q' : Q'.1.completionPlace.integers) : Q'.1.Completion) =
            (c : P.Completion) • (m Q' : Q'.1.Completion) := by
          rw [Algebra.smul_def, MulMemClass.coe_mul,
            coe_algebraMap_completionIntegersExtensionAlgebra,
            ← algebraMap_completionExtensionAlgebra, ← Algebra.smul_def]
        rw [Pi.smul_apply, hcm, mul_smul_comm, map_smul, smul_eq_mul, Algebra.smul_def,
          ValuationSubring.algebraMap_apply] }
  have hψ (m : ∀ Q' : τ, Q'.1.completionPlace.integers) :
      ψ m ∈ (1 : Submodule P.completionPlace.integers P.Completion) := by
    have hle :
        (⊤ : Submodule P.completionPlace.integers (∀ Q' : τ, Q'.1.completionPlace.integers)) ≤
          Submodule.comap ψ (1 : Submodule P.completionPlace.integers P.Completion) := by
      rw [← span_completionIntegers_pi_eq_top k' F' P, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      have hy : IsIntegral P.integers y.1 :=
        (isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable k' P).mpr
          fun Q' hQ' ↦ y.2 ⟨Q', hQ'⟩
      obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨⟨y.1, hy⟩, rfl⟩)
      refine Submodule.mem_one.mpr ⟨P.completionIntegersEmbedding r, ?_⟩
      rw [ValuationSubring.algebraMap_apply, completionIntegersEmbedding_apply]
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, completionIntegersEmbedding_apply]
      simp_rw [← map_mul, ← finsum_eq_sum_of_fintype]
      rw [← completionEmbedding_trace_of_isSeparable k' P (d * y.1)]
      exact congrArg P.completionEmbedding hr
    exact hle Submodule.mem_top
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  have hz' := hψ (Pi.single ⟨P', hP⟩ z)
  rw [Submodule.mem_one] at hz'
  rw [Algebra.traceForm_apply, RingHom.mem_range]
  refine hz'.imp fun y hy ↦ hy.trans ?_
  simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, ValuationSubring.algebraMap_apply]
  rw [Finset.sum_eq_single_of_mem (⟨P', hP⟩ : τ) (Finset.mem_univ _)
    fun Q' _ hQ' ↦ by simp [Pi.single_eq_of_ne hQ'], Pi.single_eq_same]

/-- **The completed trace dual is spanned by the local trace dual.** The trace dual of `𝒪̂_{P'}`
over `𝒪̂_P` is the `𝒪̂_{P'}`-span of the image in `F̂'_{P'}` of the trace dual of `𝒪'_P` over
`𝒪_P`. -/
theorem span_traceDual_one_eq_traceDual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact completionEmbedding_mem_traceDual_completionIntegers P P' hP hd
  -- `𝒪'_P` is finite free over the DVR `𝒪_P`, hence projective; expand `z` along a trace-dual
  -- family of `𝒪'_P / 𝒪_P`.
  have : Module.Free P.integers (integralClosure P.integers F') :=
    Module.free_of_finite_type_torsion_free'
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← sum_trace_mul_smul_completionEmbedding_eq P P' hP
    (fun i ↦ algebraMap (integralClosure P.integers F') F' (b i)) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
    ⟨P.completionIntegersOfIntegralClosure P' hP (b i), rfl⟩)
  simp only [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply,
    coe_completionIntegersOfIntegralClosure] at hc
  rw [← hc, ← ValuationSubring.algebraMap_apply, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace dual of
`𝒪'_P` over `𝒪_P` along `𝒪'_P →+* 𝒪̂_{P'}` gives the trace dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem extended_dual_one_eq_dual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := finiteDimensional_completion P P' hP
    haveI := isSeparable_completion P P' hP
    haveI := isIntegralClosure_completionIntegers P P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P.completionIntegersOfIntegralClosure_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal P'.completionPlace.integers⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := finiteDimensional_completion P P' hP
  have _ := isSeparable_completion P P' hP
  have _ := isIntegralClosure_completionIntegers P P' hP
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.completionIntegersOfIntegralClosure P' hP)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.completionIntegersOfIntegralClosure_injective P' hP)) =
      (P'.completionEmbedding : F' →+* P'.Completion) := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun x ↦ ?_
    rw [IsLocalization.map_eq, ValuationSubring.algebraMap_apply,
      coe_completionIntegersOfIntegralClosure, AlgHom.coe_toRingHom]
  have hdual : ((FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')) : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, hdual, FractionalIdeal.coeToSubmodule_dual_one]
  exact span_traceDual_one_eq_traceDual_one_completionIntegers P P' hP

/-- **The different ideal commutes with completion.** The different ideal of the local model
`𝒪'_P / 𝒪_P` generates in `𝒪̂_{P'}` the different ideal of the completed valuation rings
`𝒪̂_{P'} / 𝒪̂_P`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.completionIntegersOfIntegralClosure P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := finiteDimensional_completion P P' hP
  have _ := isSeparable_completion P P' hP
  have _ := isIntegralClosure_completionIntegers P P' hP
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.completionIntegersOfIntegralClosure_injective P' hP)),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one_completionIntegers P P' hP]

end TraceDual

section DifferentExponent

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **The completed different ideal is the `d(P' ∣ P)`-th power of the maximal ideal of `𝒪̂_{P'}`**,
with no separability assumption on the residue extension. -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow :
    letI := P.completionIntegersExtensionAlgebra P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  let P := P'.restrict k F
  let _ := P.completionIntegersExtensionAlgebra P' rfl
  rw [← map_differentIdeal_eq_differentIdeal_completionIntegers P P' rfl]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) fun w hw ↦ ?_
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [Ideal.mem_comap, P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration,
      coe_completionIntegersOfIntegralClosure, completionEmbedding_mem_filtration_iff,
      P'.mem_filtration_iff_le_ord (by simpa using hy0)]
    exact differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    rcases eq_or_ne w 0 with rfl | hw0
    · exact zero_mem _
    set z : P'.completionPlace.integers := P.completionIntegersOfIntegralClosure P' rfl y
    have hz0 : (z : P'.Completion) ≠ 0 := by
      rw [coe_completionIntegersOfIntegralClosure]
      simpa using hy0
    have hzord : P'.completionPlace.ord (z : P'.Completion) = differentExponent k F P' := by
      rw [coe_completionIntegersOfIntegralClosure, ord_completionEmbedding, hord]
    have hword : (differentExponent k F P' : ℤ) ≤ P'.completionPlace.ord (w : P'.Completion) :=
      (P'.completionPlace.mem_filtration_iff_le_ord (by simpa using hw0)).mp
        ((P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration _ _).mp hw)
    have hdiv : (w : P'.Completion) / (z : P'.Completion) ∈ P'.completionPlace.integers := by
      rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div (by simpa using hw0) hz0, hzord]
      omega
    have hmul : w = ⟨(w : P'.Completion) / (z : P'.Completion), hdiv⟩ * z :=
      Subtype.ext (by simp [div_mul_cancel₀ _ hz0])
    rw [hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hy)

/-- **The different exponent survives completion**: the multiplicity of the maximal ideal of
`𝒪̂_{P'}` in the different ideal of `𝒪̂_{P'} / 𝒪̂_P` is `d(P' ∣ P)`. -/
theorem multiplicity_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [differentIdeal_completionIntegers_eq_maximalIdeal_pow P P' hP]
  exact multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance) _

/-- **The valuation criterion for the completed complementary module**: a completed function
`z ∈ F̂'_{P'}` lies in the trace dual of `𝒪̂_{P'}` over `𝒪̂_P` if and only if
`v_{P'}(z) ≤ exp d(P' ∣ P)`. -/
theorem mem_traceDual_completionIntegers_iff_valuation_le {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := finiteDimensional_completion P P' hP
  have _ := isSeparable_completion P P' hP
  have _ := isIntegralClosure_completionIntegers P P' hP
  obtain ⟨t, ht⟩ := P'.completionPlace.exists_isUniformizer
  have hπord : P'.completionPlace.ord t = 1 :=
    P'.completionPlace.isUniformizer_iff_ord_eq_one.mp ht
  let π : P'.completionPlace.integers :=
    ⟨t, P'.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  have hπ : Irreducible π := P'.completionPlace.irreducible_of_isUniformizer ht
  have hmax : maximalIdeal P'.completionPlace.integers = Ideal.span {π} := hπ.maximalIdeal_eq
  have hdiff : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {π ^ differentExponent k F P'} := by
    rw [differentIdeal_completionIntegers_eq_maximalIdeal_pow P P' hP, hmax,
      Ideal.span_singleton_pow]
  have hπ0 : (π : P'.Completion) ≠ 0 := by simpa using hπ.ne_zero
  have hpowval : P'.completionPlace.valuation ((π : P'.Completion) ^ differentExponent k F P') =
      WithZero.exp (-(differentExponent k F P' : ℤ)) := by
    rw [P'.completionPlace.valuation_eq_exp_neg_ord (pow_ne_zero _ hπ0),
      P'.completionPlace.ord_pow, hπord, mul_one]
  rw [mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hdiff]
  have hmem : z * algebraMap P'.completionPlace.integers P'.Completion
        (π ^ differentExponent k F P') ∈
      (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation (z * (π : P'.Completion) ^ differentExponent k F P') ≤ 1 := by
    rw [Submodule.mem_one, ← P'.completionPlace.mem_integers_iff,
      ValuationSubring.algebraMap_apply, SubmonoidClass.coe_pow]
    simp_rw [ValuationSubring.algebraMap_apply]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  rw [hmem, map_mul, hpowval]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc
      P'.completionPlace.valuation z
        = P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ)) *
            WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
      _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _
  · calc
      P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ))
        ≤ WithZero.exp (differentExponent k F P' : ℤ) *
            WithZero.exp (-(differentExponent k F P' : ℤ)) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-- **The length of the completed complementary-module quotient** over `𝒪̂_P` is
`d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full relative residue degree, including any
inseparable factor. -/
theorem length_traceDual_quotient_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
        ((Submodule.traceDual P.completionPlace.integers P.Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual P.completionPlace.integers P.Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have _ := finiteDimensional_completion (P'.restrict k F) P' rfl
  have _ := isSeparable_completion (P'.restrict k F) P' rfl
  have _ := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have _ := finiteDimensional_residueField_completion (k := k) (F := F) P'
  rw [length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers, finrank_residueField_completion]

/-- **The discriminant of an integral basis of the completed valuation rings**: for every
`𝒪̂_P`-basis `b` of `𝒪̂_{P'}`, `ord_{𝒪̂_P}(discr b) = d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is
the full relative residue degree, including any inseparable factor. -/
theorem ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : letI := P.completionIntegersExtensionAlgebra P' hP
      Basis ι P.completionPlace.integers P'.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have _ := isSeparable_completion (P'.restrict k F) P' rfl
  have _ := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  rw [ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers, finrank_residueField_completion]

/-- On a nonzero regular element of a place, the DVR `Ring.ord` agrees with the place order. -/
private theorem ringOrd_eq_ord {Q : Place k F} {y : Q.integers} (hy : y ≠ 0) :
    Ring.ord Q.integers y = ((Q.ord (y : F)).toNat : ℕ∞) := by
  rw [Ring.ord_eq_addVal]
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
    Q.mem_maximalIdeal_pow_iff_coe_mem_filtration,
    Q.mem_filtration_iff_le_ord (by simpa using hy), Nat.cast_le]
  have := Q.mem_integers_iff_ord_nonneg.mp y.2
  omega

/-- **The completed place order of the discriminant** of any `𝒪̂_P`-basis `b` of `𝒪̂_{P'}` is
`d(P' ∣ P) · f(P' ∣ P)`. -/
theorem ord_completionPlace_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : letI := P.completionIntegersExtensionAlgebra P' hP
      Basis ι P.completionPlace.integers P'.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    P.completionPlace.ord (Algebra.discr P.completionPlace.integers b : P.Completion) =
      (differentExponent k F P' : ℤ) * relativeDegree k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have hord := ord_discr_completionIntegers P P' hP b
  have hne : Algebra.discr P.completionPlace.integers b ≠ 0 := by
    intro h
    rw [h, Ring.ord_eq_addVal, AddValuation.map_zero, ← Nat.cast_mul] at hord
    exact ENat.top_ne_natCast _ hord
  rw [ringOrd_eq_ord hne, ← Nat.cast_mul, Nat.cast_inj] at hord
  have hnonneg : 0 ≤ P.completionPlace.ord
      (Algebra.discr P.completionPlace.integers b : P.Completion) :=
    P.completionPlace.mem_integers_iff_ord_nonneg.mp (Algebra.discr P.completionPlace.integers b).2
  exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm.trans (congrArg Nat.cast hord)

end DifferentExponent

section AffineModel

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']
  {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
  [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
  [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
  [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]

/-- **The different ideal of an affine model commutes with completion**: if `P'` lies over `P` and
is finite on the integral closure `C` in `F'` of an affine model `B` of `F`, then the different
ideal of `C / B` generates in `𝒪̂_{P'}` the different ideal of `𝒪̂_{P'} / 𝒪̂_P`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers_of_mem_integers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal B C).map
        (P'.completionIntegersEmbedding.toRingHom.comp
          ((algebraMap C F').codRestrict P'.integers.toSubring hC)) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  subst hP
  let P := P'.restrict k F
  let _ := P.completionIntegersExtensionAlgebra P' rfl
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  have _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P.center hB
  let Bₘ := P.integers
  let Cₘ := integralClosure Bₘ F'
  let _ : Algebra B Bₘ := ((algebraMap B F).codRestrict Bₘ hB).toAlgebra
  have _ : IsScalarTower B Bₘ F := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[B] Bₘ :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P.valuationSubringAtPrime_eq_integers hB)))
      fun _ ↦ rfl
  have _ : IsLocalization p.asIdeal.primeCompl Bₘ :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eB
  have _ : IsScalarTower B Bₘ F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply B F F' x
  let _ : Algebra C Cₘ :=
    ((algebraMap C F').codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := Bₘ)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  have _ : IsScalarTower C Cₘ F' := .of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B C F' x
  have _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply B F F' x
  have _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F') (M := p.asIdeal.primeCompl)
  have hcomp : P'.completionIntegersEmbedding.toRingHom.comp
        ((algebraMap C F').codRestrict P'.integers.toSubring hC) =
      (P.completionIntegersOfIntegralClosure P' rfl).comp (algebraMap C Cₘ) :=
    RingHom.ext fun c ↦ Subtype.ext <| by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.codRestrict_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, completionIntegersEmbedding_apply,
        coe_completionIntegersOfIntegralClosure]
      exact congrArg P'.completionEmbedding (IsScalarTower.algebraMap_apply C Cₘ F' c)
  rw [hcomp, ← Ideal.map_map,
    map_differentIdeal_eq_differentIdeal (R := B) (Rₘ := Bₘ) (S := C) (Sₘ := Cₘ) (K := F)
      (L := F') (M := p.asIdeal.primeCompl),
    map_differentIdeal_eq_differentIdeal_completionIntegers P P' rfl]

/-- **The multiplicity of the completed different equals that on any affine model**: if `P'` lies
over `P` and is finite on the integral closure `C` in `F'` of an affine model `B` of `F`, then the
multiplicity of `𝔪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals the multiplicity of the centre of
`P'` on `C` in `differentIdeal B C`. -/
theorem multiplicity_differentIdeal_completionIntegers_eq_multiplicity_center
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      multiplicity (P'.center hC).asIdeal (differentIdeal B C) := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [multiplicity_differentIdeal_completionIntegers P P' hP,
    differentExponent_eq_multiplicity_center (B := B) (C := C) P' hC]

end AffineModel

end TauCeti.Place
