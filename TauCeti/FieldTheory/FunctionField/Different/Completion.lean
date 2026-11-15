/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.RingTheory.DedekindDomain.Different.Localization
public import TauCeti.RingTheory.Trace.Length
import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily
import TauCeti.RingTheory.Localization.Integral

/-!
# The complementary module and the different under completion

Let `F' / F` be a finite separable extension of fields, `k' / k` an integral extension of base
fields with `F` over `k` and `F'` over `k'`, `P` a place of `F / k`, and `P'` a place of `F' / k'`
lying over `P`. Write `𝒪_P` for the valuation ring of `P`, `𝒪'_P` for its integral closure in `F'`,
and `𝒪̂_P ⊆ 𝒪̂_{P'}` for the completed valuation rings inside the completed fields
`F̂_P ⊆ F̂'_{P'}`.

This file proves that passing to the completion at `P'` preserves the trace-dual complementary
module, the different ideal, the different exponent `d(P' ∣ P)`, and the local length and
discriminant formulas, with **no separability hypothesis on the residue extension** and no
function-field hypothesis on `F / k`:

* the completed complementary module `Submodule.traceDual 𝒪̂_P F̂_P 1` is the `𝒪̂_{P'}`-span of the
  image of the complementary module `Submodule.traceDual 𝒪_P F 1` of the local model (and more
  generally of `Submodule.traceDual B F 1` for any Dedekind affine model `B ⊆ C` on which `P'` is
  finite);
* the different ideal `differentIdeal 𝒪_P 𝒪'_P` (and `differentIdeal B C` for any such affine
  model) generates `differentIdeal 𝒪̂_P 𝒪̂_{P'}` in `𝒪̂_{P'}`, and diagonally generates
  `∏_{Q' ∣ P} differentIdeal 𝒪̂_P 𝒪̂_{Q'}` in `∏_{Q' ∣ P} 𝒪̂_{Q'}`;
* `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`, so the multiplicity of `𝔪̂_{P'}` in the
  completed different ideal equals `d(P' ∣ P)` and membership in the completed complementary module
  is governed by `v_{P̂'}(z) ≤ exp d(P' ∣ P)`;
* the `𝒪̂_P`-length of `Ĉ_{P'} / 𝒪̂_{P'}` and the valuation `ord_P (discr 𝒪̂_P b)` of any
  `𝒪̂_P`-basis `b` of `𝒪̂_{P'}` equal `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the **full**
  relative residue degree, including its inseparable factor.

## Proof strategy

Unlike the number-field completion comparison
`IsDedekindDomain.HeightOneSpectrum.span_traceDual_one_eq_traceDual_one_adicCompletionIntegers` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`, which passes through the
tensor products `K_v ⊗[K] L` and `𝒪_v ⊗[𝒪 K] 𝒪 L`, the comparison here works directly on the
semilocal products `∏_{Q' ∣ P} F̂'_{Q'}` and `∏_{Q' ∣ P} 𝒪̂_{Q'}` (`F̂_P` is not given an
`F`-algebra structure). By `TauCeti.Place.span_completionIntegers_pi_eq_top`, a single-coordinate
completed integer `Pi.single ⟨P', hP⟩ z` is an `𝒪̂_P`-linear combination of diagonal images of
elements of `F'` regular at every place above `P` — hence integral over `𝒪_P` by
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional`. Applying the
trace formula `TauCeti.Place.completionEmbedding_trace_of_isSeparable` shows that the global
complementary module maps into the completed one; conversely,
`TauCeti.Place.span_completion_pi_eq_top` transports a projective trace-dual expansion
(`TauCeti.exists_sum_trace_mul_smul_eq`) from `F' / F` to `F̂'_{P'} / F̂_P`.

## Main definitions

* `TauCeti.Place.integralClosureToCompletionIntegers`: the canonical embedding `𝒪'_P →+* 𝒪̂_{P'}` at
  a place `P'` above `P`.

## Main results

* `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`: a trace-dual expansion of `F' / F`
  remains one of `F̂'_{P'} / F̂_P`.
* `TauCeti.Place.completionEmbedding_mem_traceDual_completionIntegers`,
  `TauCeti.Place.span_traceDual_one_eq_traceDual_one_completionIntegers`, and
  `TauCeti.Place.extended_dual_one_eq_dual_one_completionIntegers`: the completed trace dual is
  spanned by (and is the fractional-ideal extension of) the trace dual of the local model.
* `TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers` and
  `TauCeti.Place.map_differentIdeal_pi_eq_pi_differentIdeal_completionIntegers`: the different ideal
  commutes with completion, at a single place and across the semilocal product above `P`.
* `TauCeti.Place.span_traceDual_one_eq_traceDual_one_completionIntegers_of_forall_mem_integers` and
  `TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers_of_forall_mem_integers`:
  the same comparisons read directly from any Dedekind affine model `B ⊆ C` on which `P'` is
  finite.
* `TauCeti.Place.differentIdeal_completionIntegers_eq_maximalIdeal_pow`,
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers`, and
  `TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`: the completed different ideal
  is `𝔪̂_{P'} ^ d(P' ∣ P)`, its multiplicity is `d(P' ∣ P)`, and the completed complementary module
  is `{z ∈ F̂'_{P'} | v_{P̂'}(z) ≤ exp d(P' ∣ P)}`.
* `TauCeti.Place.length_traceDual_quotient_completionIntegers`,
  `TauCeti.Place.length_quotient_differentIdeal_completionIntegers`,
  `TauCeti.Place.ringOrd_discr_completionIntegers`, and
  `TauCeti.Place.ord_discr_completionIntegers`: the lengths of `Ĉ_{P'} / 𝒪̂_{P'}` and
  `𝒪̂_{P'} / 𝔡(𝒪̂_{P'} / 𝒪̂_P)` and the valuation of the discriminant of an `𝒪̂_P`-basis of
  `𝒪̂_{P'}` equal `d(P' ∣ P) · f(P' ∣ P)` with the full residue degree.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3 and Chapter III, §§3–4,
  Proposition 10.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.4 and IV.2.
* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter III,
  Proposition (2.2).
-/

public section

open IsDedekindDomain IsLocalRing Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section Embedding

variable [Algebra.IsIntegral F F']

/-- **The canonical embedding `𝒪'_P →+* 𝒪̂_{P'}`** from the integral closure of `𝒪_P` in `F'` into
the completed valuation ring at a place `P'` lying over `P`. -/
noncomputable def integralClosureToCompletionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  P'.completionIntegersEmbedding.toRingHom.comp
    ((algebraMap (integralClosure P.integers F') F').codRestrict P'.integers fun y ↦ by
      subst hP
      exact algebraMap_mem_integers_of_mem_integralClosure k F P' y)

@[simp]
theorem coe_integralClosureToCompletionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) (y : integralClosure P.integers F') :
    (P.integralClosureToCompletionIntegers P' hP y : P'.Completion) =
      P'.completionEmbedding (algebraMap (integralClosure P.integers F') F' y) := by
  simp [integralClosureToCompletionIntegers]

/-- The canonical embedding `𝒪'_P →+* 𝒪̂_{P'}` is injective. -/
theorem integralClosureToCompletionIntegers_injective (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    Function.Injective (P.integralClosureToCompletionIntegers P' hP) := by
  intro x y h
  apply IsIntegralClosure.algebraMap_injective (integralClosure P.integers F') P.integers F'
  apply P'.completionEmbedding.injective
  simpa [← coe_integralClosureToCompletionIntegers P P' hP] using congrArg Subtype.val h

/-- On `𝒪_P`, the canonical embedding `𝒪'_P →+* 𝒪̂_{P'}` agrees with completing at `P` and
applying the completed valuation-ring extension. -/
@[simp]
theorem integralClosureToCompletionIntegers_algebraMap (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) (x : P.integers) :
    P.integralClosureToCompletionIntegers P' hP
        (algebraMap P.integers (integralClosure P.integers F') x) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding x) := by
  apply Subtype.ext
  rw [coe_integralClosureToCompletionIntegers, coe_completionIntegersExtension,
    completionIntegersEmbedding_apply, ← IsScalarTower.algebraMap_apply P.integers
      (integralClosure P.integers F') F',
    IsScalarTower.algebraMap_apply P.integers F F',
    ← P.completionExtension_completionEmbedding P' hP]
  rfl

end Embedding

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

section TraceDual

variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- On the semilocal product `∏_{Q' ∣ P} F̂'_{Q'}`, a global trace-dual expansion holds
coordinatewise: both sides are `F̂_P`-linear and agree on the diagonal image of `F'`, which spans
the product over `F̂_P`. -/
private theorem sum_trace_mul_smul_completion_pi_eq
    [Fintype {Q' : Place k' F' // Q'.restrict k F = P}] {ι : Type*} [Fintype ι] (b y : ι → F')
    (hb : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x)
    (ξ : ∀ Q' : {Q' : Place k' F' // Q'.restrict k F = P}, Q'.1.Completion) :
    letI := fun Q' : {Q' : Place k' F' // Q'.restrict k F = P} ↦
      P.completionExtensionAlgebra Q'.1 Q'.2
    ∑ i, (∑ Q' : {Q' : Place k' F' // Q'.restrict k F = P},
        Algebra.trace P.Completion Q'.1.Completion (ξ Q' * Q'.1.completionEmbedding (b i))) •
      (fun Q' : {Q' : Place k' F' // Q'.restrict k F = P} ↦
        Q'.1.completionEmbedding (y i)) = ξ := by
  let J := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := fun Q' : J ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let Φ : (∀ Q' : J, Q'.1.Completion) →ₗ[P.Completion] (∀ Q' : J, Q'.1.Completion) :=
    ∑ i : ι, LinearMap.smulRight
      (∑ Q' : J, (Algebra.trace P.Completion Q'.1.Completion).comp
        ((LinearMap.mulRight P.Completion (Q'.1.completionEmbedding (b i))).comp
          (LinearMap.proj Q')))
      (fun Q' : J ↦ Q'.1.completionEmbedding (y i))
  suffices hΦ : Φ = LinearMap.id by
    simpa [Φ, LinearMap.sum_apply, LinearMap.smulRight_apply] using LinearMap.congr_fun hΦ ξ
  refine LinearMap.ext_on (span_completion_pi_eq_top k' F' P) ?_
  rintro _ ⟨x, rfl⟩
  simp only [Φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, LinearMap.mulRight_apply, LinearMap.id_coe, id_eq]
  ext Q'
  simp only [Finset.sum_apply, Pi.smul_apply]
  have htr (i : ι) :
      ∑ R' : J, Algebra.trace P.Completion R'.1.Completion
          (R'.1.completionEmbedding x * R'.1.completionEmbedding (b i)) =
        P.completionEmbedding (Algebra.trace F F' (x * b i)) := by
    simp_rw [← map_mul]
    rw [← finsum_eq_sum_of_fintype]
    exact (completionEmbedding_trace_of_isSeparable k' P (x * b i)).symm
  simp_rw [htr, ← P.completionEmbedding_smul Q'.1 Q'.2, ← map_sum, hb x]

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) • yᵢ` for every
`x ∈ F'`, then `z = ∑ᵢ Tr_{F̂'_{P'}/F̂_P}(z bᵢ) • yᵢ` for every `z ∈ F̂'_{P'}`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {ι : Type*} [Fintype ι] (b y : ι → F')
    (hb : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  classical
  let J := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := P.completionExtensionAlgebra P' hP
  let _ := fun Q' : J ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let _ := Fintype.ofFinite J
  let P₀ : J := ⟨P', hP⟩
  let ξ₀ : ∀ Q' : J, Q'.1.Completion := Pi.single (M := fun Q' : J ↦ Q'.1.Completion) P₀ z
  have h := congrFun (sum_trace_mul_smul_completion_pi_eq P b y hb ξ₀) P₀
  simp only [Finset.sum_apply, Pi.smul_apply] at h
  have h0 : ξ₀ P₀ = z := Pi.single_eq_same (M := fun Q' : J ↦ Q'.1.Completion) P₀ z
  rw [h0] at h
  have hsum (i : ι) :
      ∑ Q' : J, Algebra.trace P.Completion Q'.1.Completion
          (ξ₀ Q' * Q'.1.completionEmbedding (b i)) =
        Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) := by
    rw [Finset.sum_eq_single P₀ (fun Q' _ hQ' ↦ ?_) fun habs ↦ absurd (Finset.mem_univ P₀) habs]
    · rw [h0]
    · have hne : ξ₀ Q' = 0 := Pi.single_eq_of_ne (M := fun Q' : J ↦ Q'.1.Completion) hQ' z
      rw [hne, zero_mul, map_zero]
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans h
  rw [hsum i]

/-- Pairing any family in `∏_{Q' ∣ P} 𝒪̂_{Q'}` against an element of the complementary module of
`𝒪'_P / 𝒪_P` yields an element of `𝒪̂_P`. -/
private theorem semilocal_sum_trace_mem_one
    [Fintype {Q' : Place k' F' // Q'.restrict k F = P}] {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F'))
    (m : ∀ Q' : {Q' : Place k' F' // Q'.restrict k F = P}, Q'.1.completionPlace.integers) :
    letI := fun Q' : {Q' : Place k' F' // Q'.restrict k F = P} ↦
      P.completionExtensionAlgebra Q'.1 Q'.2
    ∑ Q' : {Q' : Place k' F' // Q'.restrict k F = P},
      Algebra.trace P.Completion Q'.1.Completion
        (Q'.1.completionEmbedding d * (m Q' : Q'.1.Completion)) ∈
      (1 : Submodule P.completionPlace.integers P.Completion) := by
  let J := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := fun Q' : J ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let _ := fun Q' : J ↦ P.completionIntegersExtensionAlgebra Q'.1 Q'.2
  let T : (∀ Q' : J, Q'.1.completionPlace.integers) →ₗ[P.completionPlace.integers] P.Completion :=
    { toFun m' := ∑ Q' : J, Algebra.trace P.Completion Q'.1.Completion
        (Q'.1.completionEmbedding d * (m' Q' : Q'.1.Completion))
      map_add' m₁ m₂ := by
        simp only [Pi.add_apply, AddMemClass.coe_add, mul_add, map_add, Finset.sum_add_distrib]
      map_smul' a m' := by
        simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun Q' _ ↦ ?_
        have hsmul : ((a • m' Q' : Q'.1.completionPlace.integers) : Q'.1.Completion) =
            (a : P.Completion) • (m' Q' : Q'.1.Completion) := by
          rw [Algebra.smul_def, Algebra.smul_def, Subring.coe_mul,
            coe_algebraMap_completionIntegersExtensionAlgebra,
            algebraMap_completionExtensionAlgebra]
        rw [hsmul, mul_smul_comm, LinearMap.map_smul, smul_eq_mul, Algebra.smul_def,
          ValuationSubring.algebraMap_apply] }
  have hsp : (⊤ : Submodule P.completionPlace.integers
      (∀ Q' : J, Q'.1.completionPlace.integers)) ≤
      (1 : Submodule P.completionPlace.integers P.Completion).comap T := by
    rw [← span_completionIntegers_pi_eq_top k' F' P, Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hyInt : IsIntegral P.integers y :=
      (isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional k' P).mpr
        fun Q' hQ' ↦ hy ⟨Q', hQ'⟩
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd y
      (Submodule.mem_one.mpr ⟨⟨y, hyInt⟩, rfl⟩)
    refine Submodule.mem_one.mpr ⟨P.completionIntegersEmbedding r, ?_⟩
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, ValuationSubring.algebraMap_apply,
      completionIntegersEmbedding_apply]
    simp_rw [← map_mul]
    rw [← finsum_eq_sum_of_fintype, ← completionEmbedding_trace_of_isSeparable k' P (d * y),
      ← Algebra.traceForm_apply, ← hr]
    rfl
  exact hsp Submodule.mem_top

/-- **The complementary module of the local model maps into the completed complementary module**:
if `Tr_{F'/F}(d · 𝒪'_P) ⊆ 𝒪_P`, then `Tr_{F̂'_{P'}/F̂_P}(d · 𝒪̂_{P'}) ⊆ 𝒪̂_P`. -/
theorem completionEmbedding_mem_traceDual_completionIntegers {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers_completion P' hP
    P'.completionEmbedding d ∈ Submodule.traceDual P.completionPlace.integers P.Completion
      (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  classical
  let J := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  let _ := fun Q' : J ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let _ := Fintype.ofFinite J
  rw [Submodule.mem_traceDual]
  rintro _ ⟨z, rfl⟩
  let P₀ : J := ⟨P', hP⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp
    (semilocal_sum_trace_mem_one P hd (Pi.single P₀ z))
  refine ⟨c, hc.trans ?_⟩
  rw [Finset.sum_eq_single P₀ (fun Q' _ hQ' ↦ ?_) fun habs ↦ absurd (Finset.mem_univ P₀) habs]
  · simp [P₀, Algebra.traceForm_apply, Algebra.smul_def]
  · rw [Pi.single_eq_of_ne hQ', ZeroMemClass.coe_zero, mul_zero, map_zero]

/-- **The completed complementary module is spanned by the global local-model complementary
module**: the trace dual of `𝒪̂_{P'}` over `𝒪̂_P` is the `𝒪̂_{P'}`-span of the image in `F̂'_{P'}`
of the trace dual of `𝒪'_P` over `𝒪_P`. No separability of residue fields is required. -/
theorem span_traceDual_one_eq_traceDual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers_completion P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          (Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F') : Set F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact P.completionEmbedding_mem_traceDual_completionIntegers P' hP hd
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← P.sum_trace_mul_smul_completionEmbedding_eq P' hP
    (fun i ↦ algebraMap (integralClosure P.integers F') F' (b i)) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _
    (Submodule.mem_one.mpr ⟨P.integralClosureToCompletionIntegers P' hP (b i), rfl⟩)
  rw [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply,
    coe_integralClosureToCompletionIntegers] at hc
  have hsmul : Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (algebraMap (integralClosure P.integers F') F' (b i))) •
      P'.completionEmbedding (y i) =
      (algebraMap P.completionPlace.integers P'.completionPlace.integers c) •
        P'.completionEmbedding (y i) := by
    rw [← hc, Algebra.smul_def, Algebra.smul_def, algebraMap_completionExtensionAlgebra,
      ValuationSubring.algebraMap_apply, ← coe_algebraMap_completionIntegersExtensionAlgebra]
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace dual of
`𝒪'_P` over `𝒪_P` along `𝒪'_P →+* 𝒪̂_{P'}` yields the trace dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem extended_dual_one_eq_dual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers_completion P' hP
    haveI := P.finiteDimensional_completion P' hP
    haveI := P.isSeparable_completion P' hP
    haveI := P.isIntegralClosure_completionIntegers P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P.integralClosureToCompletionIntegers_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal P'.completionPlace.integers⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  have _ := P.finiteDimensional_completion P' hP
  have _ := P.isSeparable_completion P' hP
  have _ := P.isIntegralClosure_completionIntegers P' hP
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.integralClosureToCompletionIntegers P' hP)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.integralClosureToCompletionIntegers_injective P' hP)) =
      (P'.completionEmbedding : F' →+* P'.Completion) := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun y ↦ ?_
    rw [IsLocalization.map_eq, ValuationSubring.algebraMap_apply,
      coe_integralClosureToCompletionIntegers]
    rfl
  have hdual : ((FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')) : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, hdual, FractionalIdeal.coeToSubmodule_dual_one]
  exact P.span_traceDual_one_eq_traceDual_one_completionIntegers P' hP

/-- **The different ideal commutes with completion.** Extending `differentIdeal 𝒪_P 𝒪'_P` along
`𝒪'_P →+* 𝒪̂_{P'}` yields `differentIdeal 𝒪̂_P 𝒪̂_{P'}` with no separability hypothesis on the
residue extension. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.integralClosureToCompletionIntegers P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  have _ := P.finiteDimensional_completion P' hP
  have _ := P.isSeparable_completion P' hP
  have _ := P.isIntegralClosure_completionIntegers P' hP
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.integralClosureToCompletionIntegers_injective P' hP)),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    P.extended_dual_one_eq_dual_one_completionIntegers P' hP]

variable (k' F') in
/-- **The different ideal across the semilocal product above `P`.** Extending
`differentIdeal 𝒪_P 𝒪'_P` diagonally to `∏_{Q' ∣ P} 𝒪̂_{Q'}` yields the product of the completed
different ideals `differentIdeal 𝒪̂_P 𝒪̂_{Q'}`. -/
theorem map_differentIdeal_pi_eq_pi_differentIdeal_completionIntegers :
    letI := fun Q' : {Q' : Place k' F' // Q'.restrict k F = P} ↦
      P.completionIntegersExtensionAlgebra Q'.1 Q'.2
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (RingHom.pi fun Q' : {Q' : Place k' F' // Q'.restrict k F = P} ↦
          P.integralClosureToCompletionIntegers Q'.1 Q'.2) =
      Ideal.pi fun Q' : {Q' : Place k' F' // Q'.restrict k F = P} ↦
        differentIdeal P.completionPlace.integers Q'.1.completionPlace.integers := by
  let J := {Q' : Place k' F' // Q'.restrict k F = P}
  let _ := fun Q' : J ↦ P.completionIntegersExtensionAlgebra Q'.1 Q'.2
  let _ := Fintype.ofFinite J
  apply Ideal.piOrderIso.injective
  funext Q'
  have hcomp : (Pi.evalRingHom (fun i : J ↦ i.1.completionPlace.integers) Q').comp
      (RingHom.pi fun R' : J ↦ P.integralClosureToCompletionIntegers R'.1 R'.2) =
      P.integralClosureToCompletionIntegers Q'.1 Q'.2 :=
    RingHom.ext fun _ ↦ rfl
  simp only [Ideal.piOrderIso, OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]
  rw [Ideal.map_evalRingHom_pi, Ideal.map_map, hcomp,
    P.map_differentIdeal_eq_differentIdeal_completionIntegers Q'.1 Q'.2]

end TraceDual

section AffineModel

omit [Algebra.IsIntegral k k'] in
/-- Localizing an affine model `B ⊆ C` finite at `P'` at the centre of `P` identifies its trace
dual and different ideal with those of the local model `𝒪_P ⊆ 𝒪'_P`. -/
private theorem span_traceDual_one_and_map_differentIdeal_of_forall_mem_integers (B C : Type*)
    [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
    [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
    [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    Submodule.span (integralClosure P.integers F')
        (Submodule.traceDual B F (1 : Submodule C F') : Set F') =
      Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') ∧
    ∃ f : C →+* integralClosure P.integers F',
      (∀ c : C, algebraMap (integralClosure P.integers F') F' (f c) = algebraMap C F' c) ∧
      (differentIdeal B C).map f =
        differentIdeal P.integers (integralClosure P.integers F') := by
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    hP ▸ algebraMap_mem_integers_restrict k F P' hC
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P.center hB
  let Bₘ := P.integers
  let Cₘ := integralClosure Bₘ F'
  let _ : Algebra B Bₘ := ((algebraMap B F).codRestrict Bₘ hB).toAlgebra
  let _ : IsScalarTower B Bₘ F := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[B] Bₘ :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P.valuationSubringAtPrime_eq_integers hB)))
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
    Subtype.ext (IsScalarTower.algebraMap_apply B C F' x)
  let _ : IsScalarTower B Bₘ Cₘ := .of_algebraMap_eq fun x ↦
    Subtype.ext (IsScalarTower.algebraMap_apply B F F' x)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := Bₘ) (S := C)
      (Sₘ := Cₘ) (L := F') (M := p.asIdeal.primeCompl)
  exact ⟨TauCeti.span_traceDual_one_eq_traceDual_one
      (R := B) (Rₘ := Bₘ) (S := C) (Sₘ := Cₘ) (K := F) (L := F') (M := p.asIdeal.primeCompl),
    algebraMap C Cₘ, fun _ ↦ rfl,
    TauCeti.map_differentIdeal_eq_differentIdeal
      (R := B) (Rₘ := Bₘ) (S := C) (Sₘ := Cₘ) (K := F) (L := F') (M := p.asIdeal.primeCompl)⟩

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
  [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
  [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
  [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]

/-- **The completed complementary module is spanned by the complementary module of any affine
model** `B ⊆ C` on which `P'` is finite: elements of `B` outside the centre of `P` become units in
`𝒪̂_{P'}`, so localizing at `P` and completing at `P'` compose cleanly. -/
theorem span_traceDual_one_eq_traceDual_one_completionIntegers_of_forall_mem_integers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers_completion P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding '' (Submodule.traceDual B F (1 : Submodule C F') : Set F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  have hloc := (span_traceDual_one_and_map_differentIdeal_of_forall_mem_integers B C P P' hP hC).1
  rw [← P.span_traceDual_one_eq_traceDual_one_completionIntegers P' hP, ← hloc]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, Submodule.subset_span hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction (fun y hy ↦ Submodule.subset_span ⟨y, hy, rfl⟩) (by simp)
      (fun y₁ y₂ _ _ hy₁ hy₂ ↦ by rw [map_add]; exact add_mem hy₁ hy₂) (fun s y _ hy ↦ ?_) hx
    rw [Algebra.smul_def, map_mul, ← coe_integralClosureToCompletionIntegers P P' hP s,
      ← ValuationSubring.algebraMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem _ (P.integralClosureToCompletionIntegers P' hP s) hy

/-- **The different ideal of any affine model `B ⊆ C` finite at `P'` generates the completed
different ideal**: localizing at `P` and completing at `P'` both commute with `differentIdeal`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers_of_forall_mem_integers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal B C).map
        (P'.completionIntegersEmbedding.toRingHom.comp
          ((algebraMap C F').codRestrict P'.integers hC)) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  obtain ⟨f, hf, hmap⟩ :=
    (span_traceDual_one_and_map_differentIdeal_of_forall_mem_integers B C P P' hP hC).2
  have hcomp : P'.completionIntegersEmbedding.toRingHom.comp
      ((algebraMap C F').codRestrict P'.integers hC) =
      (P.integralClosureToCompletionIntegers P' hP).comp f := by
    ext c
    simp [hf]
  rw [hcomp, ← Ideal.map_map, hmap,
    P.map_differentIdeal_eq_differentIdeal_completionIntegers P' hP]

end AffineModel

section ExponentAndLength

variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **The completed different ideal is `𝔪̂_{P'} ^ d(P' ∣ P)`.** Passing to the completion at `P'`
realizes the different exponent `d(P' ∣ P)` as the exact power of the maximal ideal of `𝒪̂_{P'}`,
with no assumption on the residue extension. -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow :
    letI := P.completionIntegersExtensionAlgebra P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      IsLocalRing.maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  rw [← (P'.restrict k F).map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) ?_
  · rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff_coe_mem_filtration,
      coe_integralClosureToCompletionIntegers, completionEmbedding_mem_filtration_iff]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    exact (P'.mem_filtration_iff_le_ord (by simpa using hy0)).mpr
      (differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0)
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    set z := (P'.restrict k F).integralClosureToCompletionIntegers P' rfl y
    have hzmem : z ∈ (differentIdeal (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F')).map
        ((P'.restrict k F).integralClosureToCompletionIntegers P' rfl) :=
      Ideal.mem_map_of_mem _ hy
    have hz0 : (z : P'.Completion) ≠ 0 := by
      simpa [z, coe_integralClosureToCompletionIntegers] using hy0
    have hzord : P'.completionPlace.ord (z : P'.Completion) = differentExponent k F P' := by
      simpa [z, coe_integralClosureToCompletionIntegers] using hord
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · exact zero_mem _
    have hw0' : (w : P'.Completion) ≠ 0 := ZeroMemClass.coe_eq_zero.not.mpr hw0
    have hword : (differentExponent k F P' : ℤ) ≤ P'.completionPlace.ord (w : P'.Completion) :=
      (P'.completionPlace.mem_filtration_iff_le_ord hw0').mp
        ((P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration _ w).mp hw)
    have hq : (w : P'.Completion) / (z : P'.Completion) ∈ P'.completionPlace.integers := by
      rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div hw0' hz0, hzord]
      omega
    have hwz : w = z * ⟨(w : P'.Completion) / (z : P'.Completion), hq⟩ :=
      Subtype.ext (mul_div_cancel₀ _ hz0).symm
    exact hwz ▸ Ideal.mul_mem_right _ _ hzmem

/-- **Completion preserves the different exponent**: the multiplicity of the maximal ideal of
`𝒪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals `d(P' ∣ P)`. -/
theorem multiplicity_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (IsLocalRing.maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP]
  exact multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance) _

/-- **The valuation criterion for the completed complementary module**: an element `z ∈ F̂'_{P'}`
satisfies `Tr_{F̂'_{P'}/F̂_P}(z · 𝒪̂_{P'}) ⊆ 𝒪̂_P` if and only if
`v_{P̂'}(z) ≤ exp d(P' ∣ P)`. -/
theorem mem_traceDual_completionIntegers_iff_valuation_le {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers_completion P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  have _ := P.finiteDimensional_completion P' hP
  have _ := P.isSeparable_completion P' hP
  have _ := P.isIntegralClosure_completionIntegers P' hP
  obtain ⟨π, hπ0, hπ⟩ := P'.completionPlace.exists_ne_zero_ord_eq 1
  let π₀ : P'.completionPlace.integers :=
    ⟨π, P'.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  have hπd : (π₀ ^ differentExponent k F P' : P'.completionPlace.integers) ∈
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
    rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP,
      mem_maximalIdeal_pow_iff_coe_mem_filtration]
    refine (P'.completionPlace.mem_filtration_iff_le_ord (pow_ne_zero _ hπ0)).mpr ?_
    simp [P'.completionPlace.ord_pow, hπ]
  rw [TauCeti.mem_traceDual_one_iff_forall_mem_differentIdeal]
  refine ⟨fun hz ↦ ?_, fun hz y hy ↦ ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hz _ hπd)
    have hle : P'.completionPlace.valuation (z * π ^ differentExponent k F P') ≤ 1 :=
      hb ▸ P'.completionPlace.mem_integers_iff.mp b.2
    rw [map_mul, P'.completionPlace.valuation_eq_exp_neg_ord (pow_ne_zero _ hπ0),
      P'.completionPlace.ord_pow, hπ, mul_one] at hle
    calc P'.completionPlace.valuation z
        = P'.completionPlace.valuation z *
            WithZero.exp (-(differentExponent k F P' : ℤ)) *
            WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
      _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _
  · rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP,
      mem_maximalIdeal_pow_iff_coe_mem_filtration] at hy
    refine Submodule.mem_one.mpr ⟨⟨z * (y : P'.Completion), ?_⟩, rfl⟩
    rw [mem_integers_iff, map_mul]
    have hyval : P'.completionPlace.valuation (y : P'.Completion) ≤
        WithZero.exp (-(differentExponent k F P' : ℤ)) :=
      P'.completionPlace.mem_filtration_iff.mp hy
    calc P'.completionPlace.valuation z * P'.completionPlace.valuation (y : P'.Completion)
        ≤ WithZero.exp (differentExponent k F P' : ℤ) *
            WithZero.exp (-(differentExponent k F P' : ℤ)) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-- **The completed complementary-module length formula**: the `𝒪̂_P`-length of `Ĉ_{P'} / 𝒪̂_{P'}`
equals `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full relative residue degree, including
its inseparable factor. -/
theorem length_traceDual_quotient_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegers_completion P' hP
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
  have _ := (P'.restrict k F).isScalarTower_completionIntegers_completion P' rfl
  have _ := (P'.restrict k F).finiteDimensional_completion P' rfl
  have _ := (P'.restrict k F).isSeparable_completion P' rfl
  have _ := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have : Module.Finite (P'.restrict k F).completionPlace.integers P'.completionPlace.integers :=
    IsIntegralClosure.finite (P'.restrict k F).completionPlace.integers
      (P'.restrict k F).Completion P'.Completion P'.completionPlace.integers
  rw [TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    (P'.restrict k F).multiplicity_differentIdeal_completionIntegers P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **The length of `𝒪̂_{P'} / 𝔡(𝒪̂_{P'} / 𝒪̂_P)` over `𝒪̂_P` is `d(P' ∣ P) · f(P' ∣ P)`**, with
`f(P' ∣ P)` the full relative residue degree, including its inseparable factor. -/
theorem length_quotient_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
        (P'.completionPlace.integers ⧸
          differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  have _ := P.finiteDimensional_completion P' hP
  have _ := P.isSeparable_completion P' hP
  have _ := P.isIntegralClosure_completionIntegers P' hP
  rw [← TauCeti.length_traceDual_quotient_eq_length_quotient_differentIdeal
      (K := P.Completion) (L := P'.Completion),
    P.length_traceDual_quotient_completionIntegers P' hP]

/-- **The completed discriminant length formula (`Ring.ord` form)**: for any `𝒪̂_P`-basis `b` of
`𝒪̂_{P'}`, `Ring.ord 𝒪̂_P (discr 𝒪̂_P b) = d(P' ∣ P) · f(P' ∣ P)`, with `f(P' ∣ P)` the full
relative residue degree, including its inseparable factor. -/
theorem ringOrd_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  intro b
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have _ := (P'.restrict k F).isScalarTower_completionIntegers_completion P' rfl
  have _ := (P'.restrict k F).isSeparable_completion P' rfl
  have _ := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  rw [TauCeti.ord_discr_eq_multiplicity_mul_finrank
      (K := (P'.restrict k F).Completion) (L := P'.Completion) b,
    (P'.restrict k F).multiplicity_differentIdeal_completionIntegers P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **The completed discriminant valuation formula (`Place.ord` form)**: for any `𝒪̂_P`-basis `b`
of `𝒪̂_{P'}`, `ord_P (discr 𝒪̂_P b) = d(P' ∣ P) · f(P' ∣ P)`, with `f(P' ∣ P)` the full relative
residue degree, including its inseparable factor. -/
theorem ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      P.completionPlace.ord (Algebra.discr P.completionPlace.integers b : P.Completion) =
        differentExponent k F P' * relativeDegree k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  have _ := P.finiteDimensional_completion P' hP
  have _ := P.isSeparable_completion P' hP
  have _ := P.isIntegralClosure_completionIntegers P' hP
  have _ := IsIntegralClosure.isLocalization
    P.completionPlace.integers P.Completion P'.Completion P'.completionPlace.integers
  intro b
  have hd0 : Algebra.discr P.completionPlace.integers b ≠ 0 := by
    intro h
    have hz := Algebra.discr_localizationLocalization
      P.completionPlace.integers P.completionPlace.integers⁰ P'.Completion
      (Rₘ := P.Completion) b
    rw [h, map_zero] at hz
    exact Algebra.discr_not_zero_of_basis P.Completion
      (b.localizationLocalization P.Completion P.completionPlace.integers⁰ P'.Completion) hz
  set d := Algebra.discr P.completionPlace.integers b
  have hR : ∀ r : P.completionPlace.integers,
      algebraMap P.completionPlace.integers P.Completion r ∈ P.completionPlace.integers :=
    fun r ↦ r.2
  have hcenter : (P.completionPlace.center hR).asIdeal =
      IsLocalRing.maximalIdeal P.completionPlace.integers := by
    ext r
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  have hmult : (multiplicity (IsLocalRing.maximalIdeal P.completionPlace.integers)
      (Ideal.span {d}) : ℕ∞) = (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
    rw [← TauCeti.IsDiscreteValuationRing.addVal_eq_multiplicity_span_singleton hd0,
      ← Ring.ord_eq_addVal, P.ringOrd_discr_completionIntegers P' hP b]
  have hmult_nat : multiplicity (IsLocalRing.maximalIdeal P.completionPlace.integers)
      (Ideal.span {d}) = differentExponent k F P' * relativeDegree k F P' := by
    exact_mod_cast hmult
  calc P.completionPlace.ord (d : P.Completion)
      = P.completionPlace.ord (algebraMap P.completionPlace.integers P.Completion d) := rfl
    _ = multiplicity (P.completionPlace.center hR).asIdeal (Ideal.span {d}) :=
        P.completionPlace.ord_algebraMap_eq_multiplicity_center hR hd0
    _ = multiplicity (IsLocalRing.maximalIdeal P.completionPlace.integers) (Ideal.span {d}) := by
        rw [hcenter]
    _ = differentExponent k F P' * relativeDegree k F P' := by exact_mod_cast hmult_nat

end ExponentAndLength

end TauCeti.Place
