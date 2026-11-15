/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.FieldTheory.FunctionField.Different.Localization
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# Completion invariance of the complementary module and the different

Let `F' / F` be a finite separable extension of fields over an integral constant-field extension
`k' / k`, and let `P'` be a place of `F' / k'` lying over `P = P'.restrict k F`. Denote by
`𝒪_P ⊆ 𝒪'_P` the local integral closure model at `P` and by `𝒪̂_P ⊆ 𝒪̂_{P'}` the completed valuation
rings inside `F̂_P ⊆ F̂_{P'}`.

This file proves that passing to completions commutes with forming the complementary module
(trace dual), the different ideal, and the different exponent, with no finiteness or separability
assumption on the residue fields and no monogenic generator assumption:

* the completed complementary module `C(𝒪̂_{P'} / 𝒪̂_P)` is the `𝒪̂_{P'}`-span of the image of the
  complementary module `C_P = Submodule.traceDual 𝒪_P F 1` under `P'.completionEmbedding`;
* extending the different ideal `differentIdeal 𝒪_P 𝒪'_P` along `𝒪'_P → 𝒪̂_{P'}` gives
  `differentIdeal 𝒪̂_P 𝒪̂_{P'}`, and across the integral semilocal decomposition
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P ≃ ∏_{Q ∣ P} 𝒪̂_Q` the extended different decomposes into the product of the
  completed differents;
* in the discrete valuation ring `𝒪̂_{P'}`, `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`, so
  the multiplicity of `𝔪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` — and, over a common constant
  field, the place different exponent `d(P'.completionPlace ∣ P.completionPlace)` — equals
  `d(P' ∣ P)`;
* consequently, the length of `C(𝒪̂_{P'} / 𝒪̂_P) / 𝒪̂_{P'}` over `𝒪̂_P` and the `𝒪̂_P`-order of the
  discriminant of any `𝒪̂_P`-basis of `𝒪̂_{P'}` both equal `d(P' ∣ P) · f(P' ∣ P)`, where
  `f(P' ∣ P)` is the full relative residue degree including any inseparable factor.

The trace-dual and fractional-ideal comparison arguments adapt
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean` from number-field adic
completions to the intrinsic place completions of
`TauCeti/FieldTheory/FunctionField/Place/Completion/Semilocal.lean`.

## Main results

All declarations live in `TauCeti.Place`:

* `sum_trace_mul_smul_completionEmbedding_eq`: a trace-dual expansion of `F' / F` transfers to
  `F̂_{P'} / F̂_P`.
* `span_traceDual_one_eq_traceDual_one_completion`: the completed trace dual is spanned over
  `𝒪̂_{P'}` by the image of the trace dual of `𝒪'_P / 𝒪_P`.
* `extended_dual_one_eq_dual_one_completion`: fractional-ideal form of trace-dual completion
  invariance along `𝒪'_P →+* 𝒪̂_{P'}`.
* `map_differentIdeal_eq_differentIdeal_completion`: the different ideal of `𝒪'_P / 𝒪_P` generates
  the different ideal of `𝒪̂_{P'} / 𝒪̂_P`.
* `differentIdeal_integralCompletionSemilocal`: under `integralCompletionSemilocalEquiv`, the
  extended different ideal is the product of the completed different ideals above `P`.
* `differentIdeal_completionIntegers_eq_maximalIdeal_pow` and
  `multiplicity_differentIdeal_completionIntegers`: `differentIdeal 𝒪̂_P 𝒪̂_{P'} =
  𝔪̂_{P'} ^ d(P' ∣ P)` and its multiplicity at `𝔪̂_{P'}` is `d(P' ∣ P)`.
* `differentExponent_completionPlace`: over a common constant field, completion preserves the
  different exponent `d(P' ∣ P)`.
* `length_traceDual_quotient_completion` and `ord_discr_completionIntegers`: the completed
  complementary-module length and discriminant valuation equal `d(P' ∣ P) · f(P' ∣ P)` without
  residue-field separability.

## References

* [J.-P. Serre, *Local Fields*][serre1968], Chapter III, §§2–4.
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, Proposition (2.2).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.4–III.5.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing
open scoped TensorProduct PlaceCompletionExtension nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section General

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- Scalar multiplication and the trace pairing commute with base change from `F` to `F̂_P`. -/
private theorem trace_tmul_mul_smul (P : Place k F) (a : P.Completion) (x b y : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((a ⊗ₜ x) * (1 ⊗ₜ b)) • ((1 : P.Completion) ⊗ₜ[F] y) =
      a ⊗ₜ[F] (Algebra.trace F F' (x * b) • y) := by
  have ha : a ⊗ₜ[F] (x * b) = a • ((1 : P.Completion) ⊗ₜ[F] (x * b)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul,
    TauCeti.Algebra.trace_baseChange_tmul]
  simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
    ← Algebra.smul_def, TensorProduct.smul_tmul]

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] in
/-- On the image of `𝒪̂_P ⊗[𝒪_P] 𝒪'_P`, pairing under the trace with an element of the complementary
module `C_P` takes values in `𝒪̂_P`. -/
private theorem trace_integralCompletionSemilocalToField_mul_mem (P : Place k F) {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F'))
    (t : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (integralCompletionSemilocalToField F' P t * (1 ⊗ₜ d)) ∈
      (algebraMap P.completionPlace.integers P.Completion).range := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    rw [map_add, add_mul, map_add]
    exact add_mem ht hu
  | tmul a x =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
    change algebraMap P.integers F r = (Algebra.traceForm F F') d (x : F') at hr
    refine ⟨a * algebraMap P.integers P.completionPlace.integers r, ?_⟩
    rw [trace_integralCompletionSemilocalToField_tmul_mul, mul_comm (x : F'),
      ← Algebra.traceForm_apply, ← hr]
    simp only [map_mul, ValuationSubring.algebraMap_apply, algebraMap_completionIntegersAlgebra,
      completionIntegersEmbedding_apply]

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) yᵢ` for every
`x ∈ F'`, then `z = ∑ᵢ Tr_{F̂_{P'}/F̂_P}(z bᵢ) yᵢ` for every `z ∈ F̂_{P'}`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  classical
  let _ := P.completionExtensionAlgebra P' hP
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
  let Q₀ : {Q : Place k' F' // Q.restrict k F = P} := ⟨P', hP⟩
  have h' := congrArg (fun ξ ↦ completionSemilocalEquiv k' F' P ξ Q₀)
    (hF ((completionSemilocalEquiv k' F' P).symm (Pi.single Q₀ z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, completionSemilocalEquiv_tmul, map_one, one_mul,
    Q₀, trace_completionSemilocalEquiv_symm_single_mul] at h'
  exact h'

/-- The image in `F̂_{P'}` of an element of the complementary module of `𝒪'_P / 𝒪_P` lies in the
complementary module of `𝒪̂_{P'} / 𝒪̂_P`. -/
private theorem completionEmbedding_mem_traceDual (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  classical
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  let Q₀ : {Q : Place k' F' // Q.restrict k F = P} := ⟨P', hP⟩
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  obtain ⟨t, ht⟩ := (integralCompletionSemilocalEquiv k' F' P).surjective (Pi.single Q₀ z)
  have hξ : integralCompletionSemilocalToField F' P t =
      (completionSemilocalEquiv k' F' P).symm
        (Pi.single Q₀ (algebraMap P'.completionPlace.integers P'.Completion z)) := by
    rw [AlgEquiv.eq_symm_apply, integralCompletionSemilocalEquiv_fieldCompatibility k' F' P, ht]
    funext Q
    obtain rfl | hQ := eq_or_ne Q Q₀
    · simp
    · simp [Pi.single_eq_of_ne hQ]
  rw [Algebra.traceForm_apply, mul_comm,
    ← trace_completionSemilocalEquiv_symm_single_mul P' hP, ← hξ]
  exact trace_integralCompletionSemilocalToField_mul_mem P hd t

/-- **The completed complementary module is spanned by the local complementary module.** For `P'`
lying over `P`, the trace dual of `𝒪̂_{P'}` over `𝒪̂_P` is the `𝒪̂_{P'}`-span of the image of the
trace dual of `𝒪'_P` over `𝒪_P`. -/
theorem span_traceDual_one_eq_traceDual_one_completion (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          (Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F') : Set F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact completionEmbedding_mem_traceDual P P' hP hd
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← sum_trace_mul_smul_completionEmbedding_eq P P' hP (fun i ↦ (b i : F')) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
    ⟨P.completionIntegersIntegralClosureHom P' hP (b i),
      coe_completionIntegersIntegralClosureHom P P' hP (b i)⟩)
  rw [Algebra.traceForm_apply] at hc
  rw [← hc, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace dual of
`𝒪'_P` over `𝒪_P` along `𝒪'_P →+* 𝒪̂_{P'}` yields the trace dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem extended_dual_one_eq_dual_one_completion (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers P' hP
    haveI := finiteDimensional_completion P P' hP
    haveI := isSeparable_completion P P' hP
    haveI := isIntegralClosure_completionIntegers P P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (completionIntegersIntegralClosureHom_injective P P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal P'.completionPlace.integers⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.completionIntegersIntegralClosureHom P' hP)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (completionIntegersIntegralClosureHom_injective P P' hP)) =
      P'.completionEmbedding.toRingHom := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun x ↦ ?_
    rw [IsLocalization.map_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ValuationSubring.algebraMap_apply, coe_completionIntegersIntegralClosureHom]
    rfl
  have hdual : ((FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')) : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hdual, FractionalIdeal.coeToSubmodule_dual_one]
  exact span_traceDual_one_eq_traceDual_one_completion P P' hP

/-- **The different ideal commutes with completion.** Extending the different ideal of `𝒪'_P` over
`𝒪_P` along `𝒪'_P →+* 𝒪̂_{P'}` produces the different ideal of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem map_differentIdeal_eq_differentIdeal_completion (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.completionIntegersIntegralClosureHom P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (completionIntegersIntegralClosureHom_injective P P' hP)),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one_completion P P' hP]

variable (k' F') in
/-- **Componentwise decomposition of the different in the integral semilocal algebra.** Extending
`differentIdeal 𝒪_P 𝒪'_P` to `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` and transporting along
`integralCompletionSemilocalEquiv` gives the product of the completed different ideals above `P`. -/
theorem differentIdeal_integralCompletionSemilocal (P : Place k F) :
    ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (integralCompletionSemilocalEquiv k' F' P) =
      Ideal.pi fun Q ↦
        differentIdeal P.completionPlace.integers Q.1.completionPlace.integers := by
  have hmap : ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (integralCompletionSemilocalEquiv k' F' P) =
      (differentIdeal P.integers (integralClosure P.integers F')).map
        ((integralCompletionSemilocalEquiv k' F' P).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            integralClosure P.integers F' →ₐ[P.integers] _).toRingHom) :=
    Ideal.map_map (Algebra.TensorProduct.includeRight :
      integralClosure P.integers F' →ₐ[P.integers] _).toRingHom
      (integralCompletionSemilocalEquiv k' F' P).toRingEquiv.toRingHom
  rw [hmap]
  apply Ideal.piOrderIso.injective
  funext Q
  simp only [Ideal.piOrderIso, OrderIso.symm_mk, RelIso.coe_fn_mk,
    Equiv.coe_fn_symm_mk, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    AlgHom.toRingHom_eq_coe]
  rw [Ideal.map_evalRingHom_pi, Ideal.map_map,
    ← map_differentIdeal_eq_differentIdeal_completion P Q.1 Q.2]
  congr 1
  ext x
  simp

/-- **In the completed valuation ring, the different ideal is `𝔪̂_{P'} ^ d(P' ∣ P)`.** No
separability or finiteness assumption on the residue fields is needed. -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  let P := P'.restrict k F
  let _ := P.completionIntegersExtensionAlgebra P' rfl
  have := P.isTorsionFree_completionIntegers P' rfl
  rw [← map_differentIdeal_eq_differentIdeal_completion P P' rfl]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) fun w hw ↦ ?_
  · rw [Ideal.mem_comap, P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration,
      coe_completionIntegersIntegralClosureHom, completionEmbedding_mem_filtration_iff]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [P'.mem_filtration_iff_le_ord (by simpa using hy0)]
    exact differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    let y' := P.completionIntegersIntegralClosureHom P' rfl y
    have hy'0 : (y' : P'.Completion) ≠ 0 := by
      rw [coe_completionIntegersIntegralClosureHom]
      exact (map_ne_zero _).mpr (by simpa using hy0)
    have hy'ord : P'.completionPlace.ord (y' : P'.Completion) = differentExponent k F P' := by
      rw [coe_completionIntegersIntegralClosureHom, P'.ord_completionEmbedding]
      exact hord
    have hdiv : (w : P'.Completion) / (y' : P'.Completion) ∈ P'.completionPlace.integers := by
      rcases eq_or_ne (w : P'.Completion) 0 with hw0 | hw0
      · simp [hw0]
      rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div hw0 hy'0, hy'ord]
      have hwfilt := (P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration _ w).mp hw
      have hle := (P'.completionPlace.mem_filtration_iff_le_ord hw0).mp hwfilt
      omega
    have hweq : w = (⟨(w : P'.Completion) / (y' : P'.Completion), hdiv⟩ :
        P'.completionPlace.integers) * y' := by
      apply Subtype.ext
      exact (div_mul_cancel₀ (w : P'.Completion) hy'0).symm
    rw [hweq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hy)

/-- **The multiplicity of `𝔪̂_{P'}` in the completed different ideal equals `d(P' ∣ P)`.** -/
theorem multiplicity_differentIdeal_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  rw [differentIdeal_completionIntegers_eq_maximalIdeal_pow P P' hP,
    multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance)]

/-- **Length of the completed complementary-module quotient.** The `𝒪̂_P`-length of
`C(𝒪̂_{P'} / 𝒪̂_P) / 𝒪̂_{P'}` is `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full relative
residue degree including any inseparable factor. -/
theorem length_traceDual_quotient_completion (P : Place k F) (P' : Place k' F')
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
  let P := P'.restrict k F
  let _ := P.completionExtensionAlgebra P' rfl
  let _ := P.completionIntegersExtensionAlgebra P' rfl
  have := P.isScalarTower_completionIntegers P' rfl
  have := P.isTorsionFree_completionIntegers P' rfl
  have := finiteDimensional_completion P P' rfl
  have := isSeparable_completion P P' rfl
  have := isIntegralClosure_completionIntegers P P' rfl
  have hfin : Module.Finite P.completionPlace.ResidueField P'.completionPlace.ResidueField := by
    apply Module.finite_of_finrank_pos
    rw [P'.finrank_residueField_completion (k := k) (F := F)]
    exact one_le_relativeDegree k F P'
  rw [TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers P P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **Valuation of the completed discriminant.** For any `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`, the
`𝒪̂_P`-order of `Algebra.discr 𝒪̂_P b` equals `d(P' ∣ P) · f(P' ∣ P)`, including the inseparable
factor of the residue extension. -/
theorem ord_discr_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let P := P'.restrict k F
  let _ := P.completionExtensionAlgebra P' rfl
  let _ := P.completionIntegersExtensionAlgebra P' rfl
  have := P.isScalarTower_completionIntegers P' rfl
  have := P.isTorsionFree_completionIntegers P' rfl
  have := isSeparable_completion P P' rfl
  have := isIntegralClosure_completionIntegers P P' rfl
  intro b
  rw [TauCeti.ord_discr_eq_multiplicity_mul_finrank P.Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers P P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

end General

section SameConstants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  (P : Place k F) (P' : Place k F') (hP : P'.restrict k F = P)

/-- **Completion preserves the place different exponent.** Over a common constant field `k`, the
different exponent of `P'.completionPlace` over `P.completionPlace` equals `d(P' ∣ P)`. -/
theorem differentExponent_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI : FiniteDimensional P.Completion P'.Completion := finiteDimensional_completion P P' hP
    haveI : Algebra.IsSeparable P.Completion P'.Completion := isSeparable_completion P P' hP
    differentExponent k P.Completion P'.completionPlace = differentExponent k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.isScalarTower_completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have : FiniteDimensional P.Completion P'.Completion := finiteDimensional_completion P P' hP
  have : Algebra.IsSeparable P.Completion P'.Completion := isSeparable_completion P P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  have hcenter : (P'.completionPlace.center hC).asIdeal =
      maximalIdeal P'.completionPlace.integers := by
    ext f
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  rw [differentExponent_eq_multiplicity_center (B := P.completionPlace.integers)
      (C := P'.completionPlace.integers) P'.completionPlace hC,
    hcenter, multiplicity_differentIdeal_completionIntegers P P' hP]

end SameConstants

end TauCeti.Place

end
