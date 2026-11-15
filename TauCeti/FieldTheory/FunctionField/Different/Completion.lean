/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant

import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Different.Localization
import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily
import TauCeti.RingTheory.DedekindDomain.Different.Localization
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# The trace-dual different and length formula under place completion

Let `F' / F` be a finite separable extension of fields, let `P` be a place of `F / k`, and let `P'`
be a place of `F' / k'` lying over `P`. No function-field hypothesis, no integrality hypothesis on
`k' / k`, and no finiteness or separability hypothesis on the residue fields `κ(P)` and `κ(P')` are
imposed in the single-place theorems; in particular, fierce places whose residue extension
`κ(P') / κ(P)` is inseparable are covered on equal footing with tame and wildly ramified places.

Denote by `𝒪_P = P.integers` the valuation ring of `P`, by `𝒪'_P = integralClosure 𝒪_P F'` its
integral closure in `F'`, and by `𝒪̂_P = P.completionPlace.integers` and
`𝒪̂_{P'} = P'.completionPlace.integers` the valuation rings of the completed fields `P.Completion`
and `P'.Completion`. This file relates the complementary module, different ideal, different
exponent, complementary-module quotient length, and trace Gram discriminant valuation of the
completed extension `𝒪̂_{P'} / 𝒪̂_P` to those of `F' / F` at `P'`:

* **Trace-dual expansions and complementary modules**: any global trace-dual expansion over `F`
  remains valid over `P'.Completion / P.Completion`
  (`TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`), and the completed complementary
  module `Ĉ_{P'/P}` is the `𝒪̂_{P'}`-span of the image of the local-model complementary module
  `C_P` (`TauCeti.Place.span_traceDual_one_eq_traceDual_one_completionIntegers`,
  `TauCeti.Place.extended_dual_one_eq_dual_one_completionIntegers`).
* **The different ideal commutes with completion**: extending `𝔇(𝒪'_P / 𝒪_P)` along
  `𝒪'_P → 𝒪̂_{P'}` yields `𝔇(𝒪̂_{P'} / 𝒪̂_P)`
  (`TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers`), as does extending the
  different ideal `𝔇(C / B)` of any affine Dedekind model `B ⊆ C` on which `P'` is finite
  (`TauCeti.Place.map_differentIdeal_affineModel_eq_differentIdeal_completionIntegers`); across the
  integral semilocal decomposition, the extended different decomposes into the product of the
  completed differents above `P` (`TauCeti.Place.differentIdeal_completionIntegersSemilocal`).
* **Invariance of the different exponent and completed valuation criterion**: the multiplicity of
  the maximal ideal `𝔪̂_{P'}` in `𝔇(𝒪̂_{P'} / 𝒪̂_P)` is `d(P' ∣ P)`
  (`TauCeti.Place.multiplicity_differentIdeal_completionIntegers`), the place-level different
  exponent of `P'.completionPlace` over `P.Completion` equals `d(P' ∣ P)`
  (`TauCeti.Place.differentExponent_completionPlace`), and an element `z ∈ P'.Completion` belongs
  to `Ĉ_{P'/P}` if and only if `v_{P̂'}(z) ≤ exp d(P' ∣ P)`
  (`TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`).
* **Completed length and discriminant formulas (including fierce residue extensions)**: combining
  `TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank` and
  `TauCeti.ord_discr_eq_multiplicity_mul_finrank` with
  `TauCeti.Place.finrank_residueField_completion` gives
  `length_{𝒪̂_P}(𝒪̂_{P'} / 𝔇(𝒪̂_{P'} / 𝒪̂_P)) = length_{𝒪̂_P}(Ĉ_{P'/P} / 𝒪̂_{P'})`
  `= d(P' ∣ P) · f(P' ∣ P)`
  (`TauCeti.Place.length_quotient_differentIdeal_completionIntegers`,
  `TauCeti.Place.length_traceDual_quotient_completionIntegers`) and
  `ord_{𝒪̂_P}(discr_{𝒪̂_P} b) = d(P' ∣ P) · f(P' ∣ P)` for every `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`
  (`TauCeti.Place.ord_discr_completionIntegers`), where `f(P' ∣ P) = [κ(P') : κ(P)]` is the full
  relative residue degree including its inseparable factor.

## Implementation notes

The semilocal trace-dual argument adapts
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean` from number-field completions to
place completions `TauCeti.Place.completionSemilocalEquiv` and
`TauCeti.Place.completionIntegersSemilocalEquiv`. To avoid imposing `[Algebra.IsIntegral k k']` in
single-place theorems, the internal semilocal steps restrict the constant field of `P'` to `k` via
`TauCeti.Place.restrictScalars`, where `Algebra.IsIntegral k k` holds tautologically and the
completion `P'.Completion` and extension homomorphism from `P.Completion` are unchanged. As in
`TauCeti.Place`'s global different API, statements involving `Submodule.traceDual` or
`FractionalIdeal.dual` over `P.completionPlace` use `TauCeti.Place.algebraIntegersExtension` and
`TauCeti.Place.isScalarTowerIntegersExtension` installed with `attribute [local instance 10]`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §8, nos. 2 and 5.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter III, §§2–4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.4 and III.5.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing Module
open scoped PlaceCompletionExtension TensorProduct nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section OnePlace

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-! ### Trace-dual expansions and the completed complementary module -/

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
private theorem trace_tmul_mul_smul (a : P.Completion) (x b y : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F') ((a ⊗ₜ[F] x) * (1 ⊗ₜ[F] b)) •
        ((1 : P.Completion) ⊗ₜ[F] y) =
      a ⊗ₜ[F] (Algebra.trace F F' (x * b) • y) := by
  have ha : a ⊗ₜ[F] (x * b) = a • ((1 : P.Completion) ⊗ₜ[F] (x * b)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul, Algebra.trace_baseChange_tmul]
  simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
    ← Algebra.smul_def, TensorProduct.smul_tmul]

private theorem sum_trace_mul_smul_completionEmbedding_eq_of_isIntegral
    [Algebra.IsIntegral k k'] {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  classical
  have hF (ξ : P.Completion ⊗[F] F') :
      ∑ i, Algebra.trace P.Completion (P.Completion ⊗[F] F') (ξ * (1 ⊗ₜ b i)) •
        ((1 : P.Completion) ⊗ₜ[F] y i) = ξ := by
    induction ξ using TensorProduct.inductionOn with
    | add ξ η hξ hη =>
      conv_rhs => rw [← hξ, ← hη]
      simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
    | tmul a x =>
      conv_rhs => rw [← h x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ trace_tmul_mul_smul P a x (b i) (y i)
  let w : {Q' : Place k' F' // Q'.restrict k F = P} := ⟨P', hP⟩
  have h' := congrArg (fun ξ ↦ completionSemilocalEquiv k' F' P ξ w)
    (hF ((completionSemilocalEquiv k' F' P).symm (Pi.single w z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, completionSemilocalEquiv_tmul, map_one, one_mul,
    trace_completionSemilocalEquiv_symm_single_mul] at h'
  exact h'

/-- **Trace-dual expansions pass to place completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) yᵢ` for every
`x ∈ F'`, then `z = ∑ᵢ Tr_{F̂'_{P'}/F̂_P}(z bᵢ) yᵢ` for every `z ∈ P'.Completion`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  have hP₀ : (P'.restrictScalars k).restrict k F = P :=
    (P'.restrict_restrictScalars (k := k) (F := F)).trans hP
  have h₀ := sum_trace_mul_smul_completionEmbedding_eq_of_isIntegral P (P'.restrictScalars k) hP₀
    b y h z
  simp only [completionEmbedding_restrictScalars] at h₀
  exact Eq.mp (congrArg (fun alg : Algebra P.Completion P'.Completion ↦
    letI := alg
    ∑ i, Algebra.trace P.Completion P'.Completion
      (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z)
    (P.completionExtensionAlgebra_restrictScalars P' hP)) h₀

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
/-- On the image of `P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'`, the
trace pairing with an element of the local-model complementary module takes values in
`P.completionPlace.integers`. -/
private theorem trace_completionIntegersSemilocalToField_mul_mem {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F'))
    (t : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (completionIntegersSemilocalToField F' P t * (1 ⊗ₜ d)) ∈
      (algebraMap P.completionPlace.integers P.Completion).range := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    rw [map_add, add_mul, map_add]
    exact add_mem ht hu
  | tmul a x =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
    rw [ValuationSubring.algebraMap_apply] at hr
    refine ⟨a * algebraMap P.integers P.completionPlace.integers r, ?_⟩
    rw [map_mul, ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply,
      P.algebraMap_completionIntegersAlgebra, P.completionIntegersEmbedding_apply, hr,
      Algebra.traceForm_apply, mul_comm d, trace_completionIntegersSemilocalToField_tmul_mul]
    rfl

private theorem completionEmbedding_mem_traceDual_of_isIntegral [Algebra.IsIntegral k k'] {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  classical
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  let w : {Q' : Place k' F' // Q'.restrict k F = P} := ⟨P', hP⟩
  obtain ⟨t, ht⟩ := (completionIntegersSemilocalEquiv k' F' P).surjective (Pi.single w z)
  have hξ : completionIntegersSemilocalToField F' P t =
      (completionSemilocalEquiv k' F' P).symm (Pi.single w (z : P'.Completion)) := by
    rw [AlgEquiv.eq_symm_apply, completionIntegersSemilocalEquiv_fieldCompatibility, ht]
    funext w'
    obtain rfl | hw' := eq_or_ne w' w
    · simp
    · simp [Pi.single_eq_of_ne hw']
  have htr := trace_completionSemilocalEquiv_symm_single_mul k' F' P w (z : P'.Completion) d
  rw [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply, mul_comm, ← htr, ← hξ]
  exact trace_completionIntegersSemilocalToField_mul_mem P hd t

private theorem completionEmbedding_mem_traceDual {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let P₀' : Place k F' := P'.restrictScalars k
  have hP₀ : P₀'.restrict k F = P := (P'.restrict_restrictScalars (k := k) (F := F)).trans hP
  have h₀ := completionEmbedding_mem_traceDual_of_isIntegral P P₀' hP₀ hd
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  rw [Submodule.mem_traceDual]
  intro a ha
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp ha
  have hz₀ : (z : P'.Completion) ∈ P₀'.completionPlace.integers := by
    have hz' := P'.completionPlace.mem_integers_iff.mp z.2
    rwa [P'.completionPlace_valuation, ← P₀'.completionPlace_valuation,
      ← P₀'.completionPlace.mem_integers_iff] at hz'
  have hmem₀ := (letI := P.completionExtensionAlgebra P₀' hP₀
    letI := P.completionIntegersExtensionAlgebra P₀' hP₀
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P₀' hP₀
    Submodule.mem_traceDual.mp h₀ (z : P'.Completion) (Submodule.mem_one.mpr ⟨⟨z, hz₀⟩, rfl⟩))
  rw [Algebra.traceForm_apply, P'.completionEmbedding_restrictScalars d] at hmem₀
  rw [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply]
  exact Eq.mp (congrArg (fun alg : Algebra P.Completion P'.Completion ↦
    letI := alg
    Algebra.trace P.Completion P'.Completion
      (P'.completionEmbedding d * (z : P'.Completion)) ∈
        (algebraMap P.completionPlace.integers P.Completion).range)
    (P.completionExtensionAlgebra_restrictScalars P' hP)) hmem₀

/-- **The completed complementary module is spanned by the local-model complementary module.**
The trace dual of `P'.completionPlace.integers` over `P.completionPlace.integers` is the
`P'.completionPlace.integers`-span of the image in `P'.Completion` of the trace dual of
`integralClosure P.integers F'` over `P.integers`. -/
theorem span_traceDual_one_eq_traceDual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact completionEmbedding_mem_traceDual P P' hP hd
  have : Module.Free P.integers (integralClosure P.integers F') :=
    .of_basis (integralClosureFinBasis F' P)
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← P.sum_trace_mul_smul_completionEmbedding_eq P' hP (fun i ↦ (b i : F')) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _
    (Submodule.mem_one.mpr ⟨P.integralClosureToCompletionIntegers P' hP (b i),
      P.coe_integralClosureToCompletionIntegers P' hP (b i)⟩)
  rw [Algebra.traceForm_apply] at hc
  have hsmul : Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i : F')) • P'.completionEmbedding (y i) =
      P.completionIntegersExtension P' hP c • P'.completionEmbedding (y i) := by
    rw [← hc, Algebra.smul_def, Algebra.smul_def, P.algebraMap_completionExtensionAlgebra P' hP,
      ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply,
      P.coe_completionIntegersExtension P' hP]
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with place completion**, as fractional ideals: extending the trace dual
of `integralClosure P.integers F'` over `P.integers` along `integralClosureToCompletionIntegers`
gives the trace dual of `P'.completionPlace.integers` over `P.completionPlace.integers`. -/
theorem extended_dual_one_eq_dual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    letI := P.finiteDimensional_completion P' hP
    letI := P.isIntegralClosure_completionIntegers P' hP
    letI := P.isSeparable_completion P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P.integralClosureToCompletionIntegers_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal (P'.completionPlace.integers)⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  let hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    (P.integralClosureToCompletionIntegers P' hP)
    (P.integralClosureToCompletionIntegers_injective P' hP)
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.integralClosureToCompletionIntegers P' hP) hf =
      P'.completionEmbedding.toRingHom := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun x ↦ ?_
    rw [IsLocalization.map_eq, ValuationSubring.algebraMap_apply,
      P.coe_integralClosureToCompletionIntegers P' hP, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rfl
  have hdual : ((FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')) : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hdual,
    FractionalIdeal.coeToSubmodule_dual_one]
  exact P.span_traceDual_one_eq_traceDual_one_completionIntegers P' hP

/-! ### Compatibility of the different ideal with completion -/

/-- **The different ideal commutes with place completion.** Extending the different ideal of the
local model `integralClosure P.integers F'` over `P.integers` along
`integralClosureToCompletionIntegers` gives the different ideal of `P'.completionPlace.integers`
over `P.completionPlace.integers`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.integralClosureToCompletionIntegers P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.moduleFinite_completionIntegers P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  have := P.isSeparable_fractionRing_completionIntegers P' hP
  let hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    (P.integralClosureToCompletionIntegers P' hP)
    (P.integralClosureToCompletionIntegers_injective P' hP)
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion hf,
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    P.extended_dual_one_eq_dual_one_completionIntegers P' hP]

/-- **Extending the different ideal of any affine model to the completion.** If `C` is the integral
closure in `F'` of a Dedekind `F`-model `B` and `P'` is finite on `C`, then extending
`differentIdeal B C` to `P'.completionPlace.integers` yields
`differentIdeal P.completionPlace.integers P'.completionPlace.integers`. -/
theorem map_differentIdeal_affineModel_eq_differentIdeal_completionIntegers
    {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
    [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
    [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal B C).map
        (P'.completionIntegersEmbedding.toRingHom.comp
          ((algebraMap C F').codRestrict P'.integers hC)) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  subst hP
  let P₀ := P'.restrict k F
  have hB : ∀ b : B, algebraMap B F b ∈ P₀.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P₀.center hB
  let Bₘ := P₀.integers
  let Cₘ := integralClosure Bₘ F'
  let _ : Algebra B Bₘ := ((algebraMap B F).codRestrict Bₘ hB).toAlgebra
  let _ : IsScalarTower B Bₘ F := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[B] Bₘ :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P₀.valuationSubringAtPrime_eq_integers hB)))
      fun _ ↦ rfl
  let _ : IsLocalization p.asIdeal.primeCompl Bₘ :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eB
  let _ : IsScalarTower B Bₘ F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply B F F' x
  let _ : Algebra C Cₘ :=
    ((algebraMap C F').codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := Bₘ)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  let _ : IsScalarTower C Cₘ F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦
    Subtype.ext <| IsScalarTower.algebraMap_apply B C F' x
  let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦
    Subtype.ext <| IsScalarTower.algebraMap_apply B F F' x
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F') (M := p.asIdeal.primeCompl)
  let _ := P₀.completionIntegersExtensionAlgebra P' rfl
  have hloc : (differentIdeal B C).map (algebraMap C Cₘ) = differentIdeal Bₘ Cₘ :=
    TauCeti.map_differentIdeal_eq_differentIdeal (R := B) (Rₘ := Bₘ) (S := C) (Sₘ := Cₘ)
      (K := F) (L := F') (M := p.asIdeal.primeCompl)
  have hcomp : P'.completionIntegersEmbedding.toRingHom.comp
      ((algebraMap C F').codRestrict P'.integers hC) =
        (P₀.integralClosureToCompletionIntegers P' rfl).comp (algebraMap C Cₘ) := by
    refine RingHom.ext fun c ↦ Subtype.ext ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, P₀.coe_integralClosureToCompletionIntegers P' rfl]
    exact (P'.completionIntegersEmbedding_apply _).trans
      (congrArg P'.completionEmbedding (RingHom.codRestrict_apply _ _ _ c))
  rw [hcomp, ← Ideal.map_map, hloc]
  exact P₀.map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl

/-! ### Invariance of the different exponent and completed valuation criterion -/

/-- **Completion preserves the different exponent, as a valuation-ring multiplicity.** The
multiplicity of the maximal ideal of `P'.completionPlace.integers` in the completed different ideal
`differentIdeal P.completionPlace.integers P'.completionPlace.integers` equals
`differentExponent k F P'`. -/
theorem multiplicity_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
      (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
    differentExponent k F P' := by
  subst hP
  let P₀ := P'.restrict k F
  let _ := P₀.completionExtensionAlgebra P' rfl
  let _ := P₀.completionIntegersExtensionAlgebra P' rfl
  have := P₀.isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := P₀.isTorsionFree_completionIntegersExtensionAlgebra P' rfl
  have := P₀.finiteDimensional_completion P' rfl
  have := P₀.moduleFinite_completionIntegers P' rfl
  have := P₀.isIntegralClosure_completionIntegers P' rfl
  have := P₀.isSeparable_completion P' rfl
  have := P₀.isSeparable_fractionRing_completionIntegers P' rfl
  set d := differentExponent k F P'
  refine le_antisymm ?_ ?_
  · by_contra! hlt
    have hdvd : maximalIdeal P'.completionPlace.integers ^ (d + 1) ∣
        differentIdeal P₀.completionPlace.integers P'.completionPlace.integers :=
      (pow_dvd_differentIdeal_iff_le_multiplicity _
        (maximalIdeal.isMaximal P'.completionPlace.integers).ne_top).mpr hlt
    obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    have hymem : P₀.integralClosureToCompletionIntegers P' rfl y ∈
        maximalIdeal P'.completionPlace.integers ^ (d + 1) := by
      refine Ideal.dvd_iff_le.mp hdvd ?_
      rw [← P₀.map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl]
      exact Ideal.mem_map_of_mem _ hy
    rw [mem_maximalIdeal_pow_iff_coe_mem_filtration,
      P₀.coe_integralClosureToCompletionIntegers P' rfl,
      P'.completionEmbedding_mem_filtration_iff,
      P'.mem_filtration_iff_le_ord (by simpa using hy0)] at hymem
    have hord' : P'.ord (y : F') = d := hord
    omega
  · rw [← pow_dvd_differentIdeal_iff_le_multiplicity _
      (maximalIdeal.isMaximal P'.completionPlace.integers).ne_top, Ideal.dvd_iff_le,
      ← P₀.map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl,
      Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff_coe_mem_filtration,
      P₀.coe_integralClosureToCompletionIntegers P' rfl,
      P'.completionEmbedding_mem_filtration_iff]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    · rw [P'.mem_filtration_iff_le_ord (by simpa using hy0)]
      exact differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0

/-- **Completion preserves the place-level different exponent**: `d(P̂' ∣ P̂) = d(P' ∣ P)`. -/
theorem differentExponent_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    letI := completionAlgebraBase (k := k) P'
    letI := isScalarTower_completionAlgebraBase (k := k) P'
    letI := P.isScalarTower_completionAlgebraBase_completionExtension P' hP
    letI := P.finiteDimensional_completion P' hP
    letI := P.isSeparable_completion P' hP
    differentExponent k P.Completion P'.completionPlace = differentExponent k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  let _ := completionAlgebraBase (k := k) P'
  have : @IsScalarTower k k' P'.Completion _
      (P'.instAlgebraCompletion).toSMul (completionAlgebraBase (k := k) P').toSMul :=
    isScalarTower_completionAlgebraBase (k := k) P'
  have : @IsScalarTower k P.Completion P'.Completion
      (P.instAlgebraCompletion).toSMul (P.completionExtensionAlgebra P' hP).toSMul
      (completionAlgebraBase (k := k) P').toSMul :=
    P.isScalarTower_completionAlgebraBase_completionExtension P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.moduleFinite_completionIntegers P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  rw [differentExponent_eq_multiplicity_center (B := P.completionPlace.integers)
      (C := P'.completionPlace.integers) P'.completionPlace hC,
    IsLocalRing.eq_maximalIdeal (P'.completionPlace.center hC).isMaximal,
    P.multiplicity_differentIdeal_completionIntegers P' hP]

/-- **The valuation criterion for the completed complementary module**: an element
`z ∈ P'.Completion` belongs to the trace dual of `P'.completionPlace.integers` over
`P.completionPlace.integers` if and only if `v_{P̂'}(z) ≤ exp d(P' ∣ P)`. Unlike the global
criterion `TauCeti.Place.mem_traceDual_iff_forall_valuation_le`, no `IsFunctionField` or
constant-field integrality hypothesis is needed. -/
theorem mem_traceDual_completionIntegers_iff_valuation_le {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.moduleFinite_completionIntegers P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  have := P.isSeparable_fractionRing_completionIntegers P' hP
  let δ := Submodule.IsPrincipal.generator
    (differentIdeal P.completionPlace.integers P'.completionPlace.integers)
  have hδ : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {δ} := (Ideal.span_singleton_generator _).symm
  have hδL : algebraMap P'.completionPlace.integers P'.Completion δ ≠ 0 :=
    algebraMap_ne_zero_of_differentIdeal_eq_span (K := P.Completion) (L := P'.Completion) hδ
  have hδ0 : δ ≠ 0 := fun h ↦ hδL (by simp [h])
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  have hord : P'.completionPlace.ord (algebraMap P'.completionPlace.integers P'.Completion δ) =
      differentExponent k F P' := by
    rw [P'.completionPlace.ord_algebraMap_eq_multiplicity_center hC hδ0,
      IsLocalRing.eq_maximalIdeal (P'.completionPlace.center hC).isMaximal, ← hδ,
      P.multiplicity_differentIdeal_completionIntegers P' hP]
  have hvδ : P'.completionPlace.valuation
      (algebraMap P'.completionPlace.integers P'.Completion δ) =
        WithZero.exp (-(differentExponent k F P' : ℤ)) := by
    rw [P'.completionPlace.valuation_eq_exp_neg_ord hδL, hord]
  rw [mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ]
  have hmem : z * algebraMap P'.completionPlace.integers P'.Completion δ ∈
      (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
        P'.completionPlace.valuation
          (z * algebraMap P'.completionPlace.integers P'.Completion δ) ≤ 1 := by
    rw [Submodule.mem_one, ← P'.completionPlace.mem_integers_iff]
    exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.2, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  rw [hmem, map_mul, hvδ]
  constructor
  · intro hle
    calc P'.completionPlace.valuation z
        = P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ)) *
            WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
      _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _
  · intro hle
    calc P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ))
        ≤ WithZero.exp (differentExponent k F P' : ℤ) *
            WithZero.exp (-(differentExponent k F P' : ℤ)) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-! ### Completed length and discriminant formulas (including fierce residue extensions) -/

/-- **Length of the completed complementary-module quotient.** The `𝒪̂_P`-length of
`Ĉ_{P'/P} / 𝒪̂_{P'}` equals `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P) = [κ(P') : κ(P)]` is the full
relative residue degree including its inseparable factor. -/
theorem length_traceDual_quotient_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
      ((Submodule.traceDual P.completionPlace.integers P.Completion
          (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
        (1 : Submodule P'.completionPlace.integers P'.Completion).comap
          (Submodule.traceDual P.completionPlace.integers P.Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let P₀ := P'.restrict k F
  let _ := P₀.completionExtensionAlgebra P' rfl
  let _ := P₀.completionIntegersExtensionAlgebra P' rfl
  have := P₀.isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := P₀.isTorsionFree_completionIntegersExtensionAlgebra P' rfl
  have := P₀.finiteDimensional_completion P' rfl
  have := P₀.moduleFinite_completionIntegers P' rfl
  have := P₀.isIntegralClosure_completionIntegers P' rfl
  have := P₀.isSeparable_completion P' rfl
  rw [TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    P₀.multiplicity_differentIdeal_completionIntegers P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **Length of the quotient by the completed different ideal.** The `𝒪̂_P`-length of
`𝒪̂_{P'} / 𝔇(𝒪̂_{P'} / 𝒪̂_P)` equals `d(P' ∣ P) · f(P' ∣ P)`, including any inseparable residue
factor. -/
theorem length_quotient_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
      (P'.completionPlace.integers ⧸
        differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.moduleFinite_completionIntegers P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  rw [← TauCeti.length_traceDual_quotient_eq_length_quotient_differentIdeal
    (K := P.Completion) (L := P'.Completion),
    P.length_traceDual_quotient_completionIntegers P' hP]

/-- **Completed discriminant-different-degree formula.** For any `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`, the
order of vanishing of the trace Gram discriminant `Algebra.discr 𝒪̂_P b` in `𝒪̂_P` is
`d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full relative residue degree including its
inseparable factor. -/
theorem ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  intro b
  let P₀ := P'.restrict k F
  let _ := P₀.completionExtensionAlgebra P' rfl
  let _ := P₀.completionIntegersExtensionAlgebra P' rfl
  have := P₀.isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := P₀.isTorsionFree_completionIntegersExtensionAlgebra P' rfl
  have := P₀.isIntegralClosure_completionIntegers P' rfl
  have := P₀.isSeparable_completion P' rfl
  rw [TauCeti.ord_discr_eq_multiplicity_mul_finrank P₀.Completion P'.Completion b,
    P₀.multiplicity_differentIdeal_completionIntegers P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

end OnePlace

section Semilocal

variable {k : Type*} (k' : Type*) {F : Type*} (F' : Type*)
  [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']
  (P : Place k F)

/-- **The different ideal across the integral semilocal decomposition.** Extending the different
ideal of `integralClosure P.integers F'` over `P.integers` to the integral semilocal algebra
`P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F'` and transporting it along
`TauCeti.Place.completionIntegersSemilocalEquiv` gives the product of the completed different ideals
above `P`. -/
theorem differentIdeal_completionIntegersSemilocal :
    ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (completionIntegersSemilocalEquiv k' F' P) =
      Ideal.pi fun w ↦
        differentIdeal P.completionPlace.integers w.1.completionPlace.integers := by
  have hmap : ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (completionIntegersSemilocalEquiv k' F' P) =
      (differentIdeal P.integers (integralClosure P.integers F')).map
        ((completionIntegersSemilocalEquiv k' F' P).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            integralClosure P.integers F' →ₐ[P.integers] _).toRingHom) :=
    Ideal.map_map (Algebra.TensorProduct.includeRight :
      integralClosure P.integers F' →ₐ[P.integers] _).toRingHom
      (completionIntegersSemilocalEquiv k' F' P).toRingEquiv.toRingHom
  rw [hmap]
  apply Ideal.piOrderIso.injective
  funext w
  simp only [Ideal.piOrderIso, OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk,
    RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, AlgHom.toRingHom_eq_coe]
  rw [Ideal.map_evalRingHom_pi, Ideal.map_map,
    ← P.map_differentIdeal_eq_differentIdeal_completionIntegers w.1 w.2]
  congr 1
  ext x
  simp

end Semilocal

end TauCeti.Place

end
end
