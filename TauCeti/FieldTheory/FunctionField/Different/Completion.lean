/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Different.Localization
import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
import TauCeti.LinearAlgebra.Span.Basic
import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# The complementary module and the different under completion

Let `F' / F` be a finite separable extension of fields, `k' / k` an extension of base fields with
`F` over `k` and `F'` over `k'`, `P` a place of `F / k`, and `P'` a place of `F' / k'` lying over
`P`. Write `𝒪_P` for the valuation ring of `P`, `𝒪'_P` for its integral closure in `F'`, and
`𝒪̂_P ⊆ 𝒪̂_{P'}` for the completed valuation rings inside the completed fields `F̂_P ⊆ F̂'_{P'}`.

This file proves that passing to the completion at `P'` preserves the trace-dual complementary
module, the different ideal, the different exponent `d(P' ∣ P)`, and the local length and
discriminant formulas, with **no separability hypothesis on the residue extension**, no integrality
hypothesis on `k' / k`, and no function-field hypothesis on `F / k`:

* the completed complementary module `Submodule.traceDual 𝒪̂_P F̂_P 1` is the `𝒪̂_{P'}`-span of the
  image of the complementary module `Submodule.traceDual 𝒪_P F 1` of the local model (and more
  generally of `Submodule.traceDual B F 1` when `C` is the integral closure in `F'` of a Dedekind
  affine model `B` of `F` on which `P'` is finite);
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
semilocal products `∏_{Q' ∣ P} F̂'_{Q'}` and `∏_{Q' ∣ P} 𝒪̂_{Q'}` over `Place k F'` (`F̂_P` is not
given an `F`-algebra structure, and forgetting `k'` to `k` on `P'` removes any integrality
assumption on `k' / k`). By `TauCeti.Place.span_completionIntegers_pi_eq_top`, a single-coordinate
completed integer `Pi.single ⟨Q', hQ⟩ z` is an `𝒪̂_P`-linear combination of diagonal images of
elements of `F'` regular at every place above `P` — hence integral over `𝒪_P` by
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional`. Applying the
trace formula `TauCeti.Place.completionEmbedding_trace_of_isSeparable` shows that the global
complementary module maps into the completed one; conversely,
`TauCeti.Place.span_completion_pi_eq_top` transports a projective trace-dual expansion
(`TauCeti.exists_sum_trace_mul_smul_eq`) from `F' / F` to `F̂'_{P'} / F̂_P`.

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
  the same comparisons read directly when `C` is the integral closure in `F'` of a Dedekind affine
  model `B` of `F` on which `P'` is finite.
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

section ForgetConstants

/-- Restrict a place of `F' / k'` to a place of `F' / k` with the same valuation, without assuming
`k' / k` is integral. -/
private abbrev forgetConstants {k k' F' : Type*} [Field k] [Field k'] [Field F']
    [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
    (Q' : Place k' F') : Place k F' where
  valuation := Q'.valuation
  valuation_surjective := Q'.valuation_surjective
  isTrivialOn := ⟨fun c hc ↦ by
    rw [IsScalarTower.algebraMap_apply k k' F']
    exact Q'.isTrivialOn.eq_one _ ((map_ne_zero_iff _ (algebraMap k k').injective).mpr hc)⟩

private theorem completionEmbedding_forgetConstants {k k' F' : Type*} [Field k] [Field k']
    [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
    (Q' : Place k' F') (x : F') :
    (forgetConstants (k := k) Q').completionEmbedding x = Q'.completionEmbedding x := by
  rw [completionEmbedding_apply, completionEmbedding_apply]

variable [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')

private theorem forgetConstants_restrict (hP : P'.restrict k F = P) :
    (forgetConstants (k := k) P').restrict k F = P := by
  rw [restrict_eq_iff_isEquiv_comap]
  exact (restrict_eq_iff_isEquiv_comap k F P' P).mp hP

private theorem completionExtensionAlgebra_forgetConstants (hP : P'.restrict k F = P) :
    P.completionExtensionAlgebra (forgetConstants (k := k) P')
        (forgetConstants_restrict P P' hP) =
      P.completionExtensionAlgebra P' hP := by
  have hext : P.completionExtension (forgetConstants (k := k) P')
      (forgetConstants_restrict P P' hP) = P.completionExtension P' hP :=
    P.eq_completionExtension_of_continuous P' hP
      (P.continuous_completionExtension (forgetConstants (k := k) P')
        (forgetConstants_restrict P P' hP)) fun x ↦ by
      rw [completionExtension_completionEmbedding, completionEmbedding_forgetConstants]
  apply Algebra.algebra_ext
  intro x
  exact DFunLike.congr_fun
    ((P.algebraMap_completionExtensionAlgebra _ (forgetConstants_restrict P P' hP)).trans
      (hext.trans (P.algebraMap_completionExtensionAlgebra P' hP).symm)) x

end ForgetConstants

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section TraceDual

variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

omit [Field k'] [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F'] in
/-- For `ξ ∈ ∏_{Q' ∣ P} F̂'_{Q'}` and a trace-dual expansion `b, y` of `F' / F`,
`ξ = ∑ᵢ (∑_{Q' ∣ P} Tr_{F̂'_{Q'}/F̂_P}(ξ_{Q'} bᵢ)) • (yᵢ)_{Q'}`. -/
private theorem sum_trace_mul_smul_completion_pi_eq
    [Fintype {Q' : Place k F' // Q'.restrict k F = P}] {ι : Type*} [Fintype ι] (b y : ι → F')
    (hb : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x)
    (ξ : ∀ Q' : {Q' : Place k F' // Q'.restrict k F = P}, Q'.1.Completion) :
    letI := fun Q' : {Q' : Place k F' // Q'.restrict k F = P} ↦
      P.completionExtensionAlgebra Q'.1 Q'.2
    ∑ i, (∑ Q' : {Q' : Place k F' // Q'.restrict k F = P},
        Algebra.trace P.Completion Q'.1.Completion (ξ Q' * Q'.1.completionEmbedding (b i))) •
      (fun Q' : {Q' : Place k F' // Q'.restrict k F = P} ↦
        Q'.1.completionEmbedding (y i)) = ξ := by
  let J := {Q' : Place k F' // Q'.restrict k F = P}
  let _ := fun Q' : J ↦ P.completionExtensionAlgebra Q'.1 Q'.2
  let Φ : (∀ Q' : J, Q'.1.Completion) →ₗ[P.Completion] (∀ Q' : J, Q'.1.Completion) :=
    ∑ i : ι, LinearMap.smulRight
      (∑ Q' : J, (Algebra.trace P.Completion Q'.1.Completion).comp
        ((LinearMap.mulRight P.Completion (Q'.1.completionEmbedding (b i))).comp
          (LinearMap.proj Q')))
      (fun Q' : J ↦ Q'.1.completionEmbedding (y i))
  suffices hΦ : Φ = LinearMap.id by
    simpa [Φ, LinearMap.sum_apply, LinearMap.smulRight_apply] using LinearMap.congr_fun hΦ ξ
  refine LinearMap.ext_on (span_completion_pi_eq_top k F' P) ?_
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
    exact (completionEmbedding_trace_of_isSeparable k P (x * b i)).symm
  simp_rw [htr, ← P.completionEmbedding_smul Q'.1 Q'.2, ← map_sum, hb x]

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) • yᵢ` for every
`x ∈ F'`, then `z = ∑ᵢ Tr_{F̂'_{P'}/F̂_P}(z bᵢ) • yᵢ` for every `z ∈ F̂'_{P'}`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {ι : Type*} [Fintype ι] (b y : ι → F')
    (hb : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  classical
  let Q' : Place k F' := forgetConstants (k := k) P'
  have hQ : Q'.restrict k F = P := forgetConstants_restrict P P' hP
  have hemb (x : F') : Q'.completionEmbedding x = P'.completionEmbedding x :=
    completionEmbedding_forgetConstants P' x
  have halg : P.completionExtensionAlgebra Q' hQ = P.completionExtensionAlgebra P' hP :=
    completionExtensionAlgebra_forgetConstants P P' hP
  let J := {R' : Place k F' // R'.restrict k F = P}
  let _ := fun R' : J ↦ P.completionExtensionAlgebra R'.1 R'.2
  let _ := Fintype.ofFinite J
  let P₀ : J := ⟨Q', hQ⟩
  let ξ₀ : ∀ R' : J, R'.1.Completion := Pi.single (M := fun R' : J ↦ R'.1.Completion) P₀ z
  have h := congrFun (sum_trace_mul_smul_completion_pi_eq P b y hb ξ₀) P₀
  simp only [Finset.sum_apply, Pi.smul_apply] at h
  have h0 : ξ₀ P₀ = z := Pi.single_eq_same (M := fun R' : J ↦ R'.1.Completion) P₀ z
  rw [h0] at h
  have hsum (i : ι) :
      ∑ R' : J, Algebra.trace P.Completion R'.1.Completion
          (ξ₀ R' * R'.1.completionEmbedding (b i)) =
        @Algebra.trace P.Completion Q'.Completion _ _ (P.completionExtensionAlgebra Q' hQ)
          (z * Q'.completionEmbedding (b i)) := by
    rw [Finset.sum_eq_single P₀ (fun R' _ hR' ↦ ?_) fun habs ↦ absurd (Finset.mem_univ P₀) habs]
    · rw [h0]
    · have hne : ξ₀ R' = 0 := Pi.single_eq_of_ne (M := fun R' : J ↦ R'.1.Completion) hR' z
      rw [hne, zero_mul, map_zero]
  have hQeq :
      letI := P.completionExtensionAlgebra Q' hQ
      ∑ i, Algebra.trace P.Completion Q'.Completion
          (z * Q'.completionEmbedding (b i)) • Q'.completionEmbedding (y i) = z := by
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans h
    rw [hsum i]
  have htr : ∀ (alg : Algebra P.Completion P'.Completion),
      alg = P.completionExtensionAlgebra Q' hQ →
      ∑ i, Algebra.trace P.Completion P'.Completion
          (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
    rintro _ rfl
    simpa only [hemb] using hQeq
  exact htr (P.completionExtensionAlgebra P' hP) halg.symm

omit [Field k'] [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F'] in
/-- Pairing any family in `∏_{Q' ∣ P} 𝒪̂_{Q'}` against an element of the complementary module of
`𝒪'_P / 𝒪_P` yields an element of `𝒪̂_P`. -/
private theorem semilocal_sum_trace_mem_one
    [Fintype {Q' : Place k F' // Q'.restrict k F = P}] {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F'))
    (m : ∀ Q' : {Q' : Place k F' // Q'.restrict k F = P}, Q'.1.completionPlace.integers) :
    letI := fun Q' : {Q' : Place k F' // Q'.restrict k F = P} ↦
      P.completionExtensionAlgebra Q'.1 Q'.2
    ∑ Q' : {Q' : Place k F' // Q'.restrict k F = P},
      Algebra.trace P.Completion Q'.1.Completion
        (Q'.1.completionEmbedding d * (m Q' : Q'.1.Completion)) ∈
      (1 : Submodule P.completionPlace.integers P.Completion) := by
  let J := {Q' : Place k F' // Q'.restrict k F = P}
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
    rw [← span_completionIntegers_pi_eq_top k F' P, Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hyInt : IsIntegral P.integers y :=
      (isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional k P).mpr
        fun Q' hQ' ↦ hy ⟨Q', hQ'⟩
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd y
      (Submodule.mem_one.mpr ⟨⟨y, hyInt⟩, Subalgebra.algebraMap_apply _ _⟩)
    refine Submodule.mem_one.mpr ⟨P.completionIntegersEmbedding r, ?_⟩
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, ValuationSubring.algebraMap_apply,
      completionIntegersEmbedding_apply]
    simp_rw [← map_mul]
    rw [← finsum_eq_sum_of_fintype, ← completionEmbedding_trace_of_isSeparable k P (d * y),
      ← Algebra.traceForm_apply, ← hr, ValuationSubring.algebraMap_apply]
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
  let Q' : Place k F' := forgetConstants (k := k) P'
  have hQ : Q'.restrict k F = P := forgetConstants_restrict P P' hP
  have hemb (x : F') : Q'.completionEmbedding x = P'.completionEmbedding x :=
    completionEmbedding_forgetConstants P' x
  have halg : P.completionExtensionAlgebra Q' hQ = P.completionExtensionAlgebra P' hP :=
    completionExtensionAlgebra_forgetConstants P P' hP
  let J := {R' : Place k F' // R'.restrict k F = P}
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have _ := P.isScalarTower_completionIntegers_completion P' hP
  let _ := Fintype.ofFinite J
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  let P₀ : J := ⟨Q', hQ⟩
  have hzmem : (z : P'.Completion) ∈ Q'.completionPlace.integers := by
    rw [Q'.completionPlace.mem_integers_iff, Q'.completionPlace_valuation]
    have hz' := P'.completionPlace.mem_integers_iff.mp z.2
    rwa [P'.completionPlace_valuation] at hz'
  let z' : Q'.completionPlace.integers := ⟨(z : P'.Completion), hzmem⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp
    (semilocal_sum_trace_mem_one P hd (Pi.single P₀ z'))
  refine RingHom.mem_range.mpr ⟨c, hc.trans ?_⟩
  rw [Finset.sum_eq_single P₀ (fun R' _ hR' ↦ ?_) fun habs ↦ absurd (Finset.mem_univ P₀) habs]
  · simp only [P₀, Pi.single_eq_same, z', hemb, Algebra.traceForm_apply,
      ValuationSubring.algebraMap_apply]
    exact congrArg (fun inst ↦ @Algebra.trace P.Completion P'.Completion _ _ inst _) halg
  · rw [Pi.single_eq_of_ne hR', ZeroMemClass.coe_zero, mul_zero, map_zero]

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
  exact TauCeti.extended_dual_one_eq_dual_one_of_span_traceDual_one
    (P'.completionEmbedding : F' →+* P'.Completion)
    (fun y ↦ by
      rw [AlgHom.coe_toRingHom, ValuationSubring.algebraMap_apply,
        coe_integralClosureToCompletionIntegers])
    (P.span_traceDual_one_eq_traceDual_one_completionIntegers P' hP)

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
  exact TauCeti.map_differentIdeal_eq_differentIdeal_of_extended_dual_one
    (P.extended_dual_one_eq_dual_one_completionIntegers P' hP)

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
    RingHom.ext fun x ↦ by rw [RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.pi_apply]
  simp only [Ideal.piOrderIso, OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]
  rw [Ideal.map_evalRingHom_pi, Ideal.map_map, hcomp,
    P.map_differentIdeal_eq_differentIdeal_completionIntegers Q'.1 Q'.2]

end TraceDual

section AffineModel

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
  [CommRing C] [Algebra C F'] [Algebra B C] [Algebra B F']
  [IsScalarTower B C F'] [IsScalarTower B F F'] [IsIntegralClosure C B F']

/-- **The completed complementary module is spanned by the complementary module of an affine
model**: if `B` is a Dedekind affine model of `F`, `C` is its integral closure in `F'`, and `P'`
is finite on `C`, then `Submodule.traceDual 𝒪̂_P F̂_P 1` is the `𝒪̂_{P'}`-span of the image of
`Submodule.traceDual B F 1` in `F̂'_{P'}`. -/
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
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    hP ▸ algebraMap_mem_integers_restrict k F P' hC
  have hloc := P.span_traceDual_one_eq_traceDual_one_integralClosure (F' := F') (C := C) hB
  rw [← P.span_traceDual_one_eq_traceDual_one_completionIntegers P' hP, ← hloc]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, Submodule.subset_span hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Submodule.map_mem_span_of_forall_exists (P'.completionEmbedding : F' →+* P'.Completion)
      _ _ (fun s ↦ ⟨P.integralClosureToCompletionIntegers P' hP s, by
        rw [AlgHom.coe_toRingHom, ValuationSubring.algebraMap_apply,
          coe_integralClosureToCompletionIntegers]⟩)
      (fun y hy ↦ Submodule.subset_span (Set.mem_image_of_mem _ hy)) hx

/-- **The different ideal of an affine model generates the completed different ideal**: if `B` is
a Dedekind affine model of `F`, `C` is its integral closure in `F'`, and `P'` is finite on `C`,
then extending `differentIdeal B C` along `C →+* 𝒪̂_{P'}` yields
`differentIdeal 𝒪̂_P 𝒪̂_{P'}`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers_of_forall_mem_integers
    [IsDedekindDomain C] [Module.IsTorsionFree B C]
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal B C).map
        (P'.completionIntegersEmbedding.toRingHom.comp
          ((algebraMap C F').codRestrict P'.integers hC)) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have hB : ∀ b : B, algebraMap B F b ∈ P.integers :=
    hP ▸ algebraMap_mem_integers_restrict k F P' hC
  let _ : Algebra B P.integers := ((algebraMap B F).codRestrict P.integers hB).toAlgebra
  have : IsScalarTower B P.integers F' := .of_algebraMap_eq fun b ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F', ValuationSubring.algebraMap_apply,
      RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply,
      ← IsScalarTower.algebraMap_apply B F F']
  let f : C →+* integralClosure P.integers F' :=
    (algebraMap C F').codRestrict (integralClosure P.integers F').toSubring fun c ↦
      Subalgebra.mem_toSubring.mpr ((mem_integralClosure_iff _ _).mpr
        (IsIntegral.tower_top (R := B) (A := P.integers)
          ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)))
  have hf (c : C) : algebraMap (integralClosure P.integers F') F' (f c) = algebraMap C F' c := by
    rw [Subalgebra.algebraMap_apply, RingHom.codRestrict_apply]
  have hcomp : P'.completionIntegersEmbedding.toRingHom.comp
      ((algebraMap C F').codRestrict P'.integers hC) =
      (P.integralClosureToCompletionIntegers P' hP).comp f := by
    ext c
    simp [hf]
  rw [hcomp, ← Ideal.map_map,
    P.map_differentIdeal_eq_differentIdeal_integralClosure hB f hf,
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
  obtain ⟨π, hπ⟩ := P'.completionPlace.exists_isUniformizer
  have hπ1 : P'.completionPlace.ord π = 1 :=
    P'.completionPlace.isUniformizer_iff_ord_eq_one.mp hπ
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ1
  let π₀ : P'.completionPlace.integers :=
    ⟨π, P'.completionPlace.mem_integers_iff_ord_nonneg.mpr (by omega)⟩
  have hdiff : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {π₀ ^ differentExponent k F P'} := by
    rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP,
      (P'.completionPlace.irreducible_of_isUniformizer (t := π₀) hπ).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  rw [TauCeti.mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hdiff,
    ValuationSubring.algebraMap_apply, SubmonoidClass.coe_pow, Submodule.mem_one]
  refine ⟨fun ⟨b, hb⟩ ↦ ?_, fun hz ↦ ?_⟩
  · have hmem : π ^ differentExponent k F P' * z ∈ P'.completionPlace.integers := by
      rw [mul_comm, ← hb, ValuationSubring.algebraMap_apply]
      exact b.2
    exact (TauCeti.Place.mul_mem_integers_iff (pow_ne_zero _ hπ0)
      (by rw [P'.completionPlace.ord_pow, hπ1, mul_one])).mp hmem
  · have hmem : z * π ^ differentExponent k F P' ∈ P'.completionPlace.integers := by
      rw [mul_comm]
      exact (TauCeti.Place.mul_mem_integers_iff (pow_ne_zero _ hπ0)
        (by rw [P'.completionPlace.ord_pow, hπ1, mul_one])).mpr hz
    exact ⟨⟨z * π ^ differentExponent k F P', hmem⟩, ValuationSubring.algebraMap_apply _ _⟩

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
  let _ := P.completionIntegersExtensionAlgebra P' hP
  intro b
  have hord := P.ringOrd_discr_completionIntegers P' hP b
  set d := Algebra.discr P.completionPlace.integers b
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, Ring.ord_eq_addVal, AddValuation.map_zero, ← Nat.cast_mul] at hord
    exact ENat.top_ne_natCast _ hord
  rw [Ring.ord_eq_addVal, P.completionPlace.addVal_integers hd0, ← Nat.cast_mul,
    Nat.cast_inj] at hord
  rw [← Int.toNat_of_nonneg (P.completionPlace.mem_integers_iff_ord_nonneg.mp d.2), hord,
    Nat.cast_mul]

end ExponentAndLength

end TauCeti.Place
