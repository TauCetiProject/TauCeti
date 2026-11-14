/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Different.Localization
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
public import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# Compatibility of the trace-dual different with completion at a place

Let `F' / F` be a finite separable extension of fields equipped with constant fields `k' / k`,
let `P` be a place of `F / k`, and let `P'` be a place of `F' / k'` lying over `P`, with local
integral closure `𝒪'_P = integralClosure 𝒪_P F'` and completed valuation rings `𝒪̂_P ⊆ 𝒪̂_{P'}`.

This file proves that the trace-dual complementary module, the different ideal, and the different
exponent commute with completion at `P'`:

* the `𝒪̂_{P'}`-span of the image of the complementary module `C_P = Submodule.traceDual 𝒪_P F 1`
  inside `F̂'_{P'}` is the completed trace dual `Submodule.traceDual 𝒪̂_P F̂_P 1`
  (`TauCeti.Place.span_traceDual_one_eq_traceDual_one_completionIntegers`), and the same holds for
  fractional ideals (`TauCeti.Place.extended_dual_one_eq_dual_one_completionIntegers`);
* the different ideal of `𝒪'_P / 𝒪_P` generates in `𝒪̂_{P'}` the different ideal of `𝒪̂_{P'} / 𝒪̂_P`
  (`TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers`);
* the different ideal of `𝒪̂_{P'} / 𝒪̂_P` is `𝔪̂_{P'} ^ d(P' ∣ P)`
  (`TauCeti.Place.differentIdeal_completionIntegers_eq_pow`), so its multiplicity at `𝔪̂_{P'}` and
  the different exponent of the completed places equal `d(P' ∣ P)`
  (`TauCeti.Place.multiplicity_differentIdeal_completionIntegers`,
  `TauCeti.Place.differentExponent_completionPlace`);
* the lengths over `𝒪̂_P` of `𝒪̂_{P'} ⧸ 𝔇(𝒪̂_{P'} / 𝒪̂_P)` and of the completed complementary-module
  quotient, as well as the `𝒪̂_P`-order of the discriminant of any `𝒪̂_P`-basis of `𝒪̂_{P'}`, equal
  `d(P' ∣ P) · f(P' ∣ P)` (`TauCeti.Place.length_quotient_differentIdeal_completionIntegers`,
  `TauCeti.Place.length_traceDual_quotient_completionIntegers`,
  `TauCeti.Place.ord_discr_completionIntegers`), where `f(P' ∣ P)` is the full relative residue
  degree including its inseparable factor;
* when `k' / k` is integral, the extended different in the integral semilocal algebra
  `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` decomposes through `TauCeti.Place.integralSemilocalEquiv` as the product of the
  completed differents above `P` (`TauCeti.Place.differentIdeal_integralSemilocal`).

No assumption is made on the characteristic, on `IsFunctionField`, or on the finiteness or
separability of the residue fields. Single-place statements also dispense with
`[Algebra.IsIntegral k k']` by viewing `P'` over `k` internally before applying the semilocal
decomposition of `TauCeti/FieldTheory/FunctionField/Place/Completion/Semilocal.lean`. The
trace-dual comparison adapts `IsDedekindDomain.HeightOneSpectrum` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean` to intrinsic place completions.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter III, §§2–4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.4–III.5.
-/

public section

open IsDedekindDomain IsLocalRing
open scoped TensorProduct nonZeroDivisors

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section Preliminaries

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

/-- The canonical ring homomorphism `𝒪'_P →+* 𝒪̂_{P'}` is injective. -/
theorem integralClosureToCompletionIntegers_injective
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    Function.Injective (integralClosureToCompletionIntegers P P' hP) := by
  intro x y hxy
  apply Subtype.ext
  apply P'.completionEmbedding.injective
  -- Unfold `P'.completionEmbedding.toRingHom` to `P'.completionEmbedding` so `coe` rewrites it.
  change P'.completionEmbedding (x : F') = P'.completionEmbedding (y : F')
  simpa only [coe_integralClosureToCompletionIntegers] using
    congrArg (fun z : P'.completionPlace.integers ↦ (z : P'.Completion)) hxy

/-- Restricting the constant field of `P' : Place k' F'` along `k → k'` produces a place of
`F' / k` with the exact same normalized valuation, allowing single-place completion arguments to
invoke the semilocal decomposition over `k` without assuming `Algebra.IsIntegral k k'`. Marked as
an `abbrev` so `(restrictConstants k P').Completion` is reducible to `P'.Completion`. -/
private abbrev restrictConstants (k : Type*) [Field k] [Algebra k k'] [Algebra k F']
    [IsScalarTower k k' F'] (P' : Place k' F') : Place k F' where
  valuation := P'.valuation
  valuation_surjective := P'.valuation_surjective
  isTrivialOn := ⟨fun c hc ↦ by
    rw [IsScalarTower.algebraMap_apply k k' F']
    exact P'.isTrivialOn.eq_one _ ((map_ne_zero _).mpr hc)⟩

private theorem restrict_restrictConstants (P' : Place k' F') :
    (restrictConstants k P').restrict k F = P'.restrict k F := by
  refine (restrict_eq_iff_integers_le k F (restrictConstants k P') (P'.restrict k F)).mpr
    fun f hf ↦ ?_
  have hf' : algebraMap F F' f ∈ P'.integers := (mem_integers_restrict_iff k F P' f).mp hf
  rw [mem_integers_iff] at hf' ⊢
  exact hf'

omit [Field F] [Algebra k F] [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
private theorem completionEmbedding_restrictConstants (P' : Place k' F') (x : F') :
    (restrictConstants k P').completionEmbedding x = P'.completionEmbedding x := by
  rw [completionEmbedding_apply, completionEmbedding_apply]

private theorem completionExtension_restrictConstants
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    P.completionExtension (restrictConstants k P') ((restrict_restrictConstants P').trans hP) =
      P.completionExtension P' hP :=
  P.eq_completionExtension_of_continuous P' hP
    (P.continuous_completionExtension (restrictConstants k P') _) fun x ↦ by
      rw [P.completionExtension_completionEmbedding (restrictConstants k P') _,
        completionEmbedding_restrictConstants]

private theorem completionExtensionAlgebra_restrictConstants
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    P.completionExtensionAlgebra (restrictConstants k P')
        ((restrict_restrictConstants P').trans hP) =
      P.completionExtensionAlgebra P' hP :=
  Algebra.algebra_ext _ _ fun r ↦ by
    -- Express both `algebraMap`s at `P'.Completion` so `algebraMap_completionExtensionAlgebra`
    -- rewrites both sides.
    change @algebraMap P.Completion P'.Completion _ _
        (P.completionExtensionAlgebra (restrictConstants k P')
          ((restrict_restrictConstants P').trans hP)) r =
      @algebraMap P.Completion P'.Completion _ _ (P.completionExtensionAlgebra P' hP) r
    rw [P.algebraMap_completionExtensionAlgebra (restrictConstants k P') _,
      P.algebraMap_completionExtensionAlgebra P' hP, completionExtension_restrictConstants]

omit [Field F] [Algebra k F] [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
private theorem mem_completionPlace_integers_restrictConstants
    (P' : Place k' F') {z : P'.Completion} :
    z ∈ (restrictConstants k P').completionPlace.integers ↔ z ∈ P'.completionPlace.integers := by
  rw [(restrictConstants k P').completionPlace.mem_integers_iff,
    P'.completionPlace.mem_integers_iff,
    (restrictConstants k P').completionPlace_valuation,
    P'.completionPlace_valuation]

end Preliminaries

section SinglePlace

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [Algebra.IsSeparable F F'] in
/-- The trace pairing and scalar multiplication commute with scalar extension from `F` to `F̂_P`. -/
private theorem trace_tmul_mul_smul (P : Place k F) (a : P.Completion) (x b y : F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        ((a ⊗ₜ x) * (1 ⊗ₜ b)) • ((1 : P.Completion) ⊗ₜ[F] y) =
      a ⊗ₜ[F] (Algebra.trace F F' (x * b) • y) := by
  have ha : a ⊗ₜ[F] (x * b) = a • ((1 : P.Completion) ⊗ₜ[F] (x * b)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul,
    Algebra.trace_baseChange_tmul]
  simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
    ← Algebra.smul_def, TensorProduct.smul_tmul]

open scoped PlaceCompletion in
/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) • yᵢ` for every
`x ∈ F'`, then the same expansion holds in `F̂'_{P'}` over `F̂_P` after applying
`P'.completionEmbedding`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) •
        P'.completionEmbedding (y i) = z := by
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
  set Q₀ : {Q : Place k F' // Q.restrict k F = P} :=
    ⟨restrictConstants k P', (restrict_restrictConstants P').trans hP⟩
  have h' := congrArg (fun ξ ↦ semilocalEquiv k F' P ξ Q₀)
    (hF ((semilocalEquiv k F' P).symm (Pi.single Q₀ z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, semilocalEquiv_tmul, map_one, one_mul,
    trace_semilocalEquiv_symm_single_mul] at h'
  rw [← completionExtensionAlgebra_restrictConstants P P' hP]
  simpa only [Q₀, fibreCompletionAlgebra, completionEmbedding_restrictConstants] using h'

open scoped PlaceCompletion in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [Algebra.IsSeparable F F'] in
/-- On the image of `𝒪̂_P ⊗[𝒪_P] 𝒪'_P`, the trace pairing with an element of the local
complementary module takes values in `𝒪̂_P`. -/
private theorem trace_integralSemilocalToField_mul_mem (P : Place k F) {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F'))
    (t : P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F') :
    Algebra.trace P.Completion (P.Completion ⊗[F] F')
        (integralSemilocalToField F' P t * (1 ⊗ₜ d)) ∈
      (algebraMap P.completionPlace.integers P.Completion).range := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    rw [map_add, add_mul, map_add]
    exact add_mem ht hu
  | tmul a x =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
    have hr' : algebraMap P.integers F r = Algebra.traceForm F F' d (x : F') := hr
    refine ⟨a * algebraMap P.integers P.completionPlace.integers r, ?_⟩
    rw [trace_integralSemilocalToField_tmul_mul, mul_comm (x : F'), ← Algebra.traceForm_apply,
      ← hr']
    simp only [ValuationSubring.algebraMap_apply, MulMemClass.coe_mul,
      coe_algebraMap_completionIntegers]

open scoped PlaceCompletion in
/-- An element of the complementary module of `𝒪'_P` over `𝒪_P` maps into the trace dual of
`𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem completionEmbedding_mem_traceDual_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
      P.isScalarTower_completionIntegersExtension P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  classical
  have hmem (z : P'.completionPlace.integers) :
      (@Algebra.trace P.Completion P'.Completion _ _ (P.completionExtensionAlgebra P' hP))
          ((z : P'.Completion) * P'.completionEmbedding d) ∈
        (algebraMap P.completionPlace.integers P.Completion).range := by
    let P'₀ : Place k F' := restrictConstants k P'
    have hP₀ : P'₀.restrict k F = P := (restrict_restrictConstants P').trans hP
    set Q₀ : {Q : Place k F' // Q.restrict k F = P} := ⟨P'₀, hP₀⟩
    let z₀ : Q₀.1.completionPlace.integers :=
      ⟨(z : P'.Completion), (mem_completionPlace_integers_restrictConstants P').mpr z.2⟩
    obtain ⟨t, ht⟩ := (integralSemilocalEquiv k F' P).surjective (Pi.single Q₀ z₀)
    have hξ : integralSemilocalToField F' P t =
        (semilocalEquiv k F' P).symm (Pi.single Q₀ (z₀ : Q₀.1.Completion)) := by
      rw [AlgEquiv.eq_symm_apply, integralSemilocalEquiv_fieldCompatibility, ht]
      funext Q'
      obtain rfl | hQ' := eq_or_ne Q' Q₀
      · simp
      · simp [Pi.single_eq_of_ne hQ']
    have htr := trace_semilocalEquiv_symm_single_mul P Q₀ (z₀ : Q₀.1.Completion) d
    rw [← hξ] at htr
    have htr' : (@Algebra.trace P.Completion P'.Completion _ _
          (P.completionExtensionAlgebra P' hP))
          ((z : P'.Completion) * P'.completionEmbedding d) =
        (@Algebra.trace P.Completion Q₀.1.Completion _ _ (fibreCompletionAlgebra Q₀))
          ((z₀ : Q₀.1.Completion) * Q₀.1.completionEmbedding d) := by
      rw [← completionExtensionAlgebra_restrictConstants P P' hP]
      simp only [Q₀, P'₀, completionEmbedding_restrictConstants, z₀]
    rw [htr', ← htr]
    exact trace_integralSemilocalToField_mul_mem P hd t
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtension P' hP
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  rw [Algebra.traceForm_apply, mul_comm, ValuationSubring.algebraMap_apply]
  exact hmem z

/-- **The completed trace dual is spanned by the complementary module.** The trace dual of `𝒪̂_{P'}`
over `𝒪̂_P` is the `𝒪̂_{P'}`-span of the image under `P'.completionEmbedding` of the complementary
module of `𝒪'_P` over `𝒪_P`. -/
theorem span_traceDual_one_eq_traceDual_one_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
      P.isScalarTower_completionIntegersExtension P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtension P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact completionEmbedding_mem_traceDual_completionIntegers P P' hP hd
  have := Module.finitePresentation_of_finite P.integers (integralClosure P.integers F')
  have : Module.Projective P.integers (integralClosure P.integers F') :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← sum_trace_mul_smul_completionEmbedding_eq P P' hP (fun i ↦ (b i : F')) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have hb_mem : P'.completionEmbedding (b i : F') ∈
      (1 : Submodule P'.completionPlace.integers P'.Completion) :=
    Submodule.mem_one.mpr ⟨integralClosureToCompletionIntegers P P' hP (b i), by
      rw [ValuationSubring.algebraMap_apply, coe_integralClosureToCompletionIntegers]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ hb_mem
  rw [Algebra.traceForm_apply] at hc
  rw [← hc, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace-dual
fractional ideal of `𝒪'_P` over `𝒪_P` along `integralClosureToCompletionIntegers P P' hP` yields
the trace-dual fractional ideal of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem extended_dual_one_eq_dual_one_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
      P.isScalarTower_completionIntegersExtension P' hP
    haveI : FiniteDimensional P.Completion P'.Completion := P.finiteDimensional_completion P' hP
    haveI : Algebra.IsSeparable P.Completion P'.Completion := P.isSeparable_completion P' hP
    haveI : IsIntegralClosure P'.completionPlace.integers
        P.completionPlace.integers P'.Completion :=
      P.isIntegralClosure_completionIntegers P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (integralClosureToCompletionIntegers_injective P P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal (P'.completionPlace.integers)⁰ P'.Completion) := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtension P' hP
  have : FiniteDimensional P.Completion P'.Completion := P.finiteDimensional_completion P' hP
  have : Algebra.IsSeparable P.Completion P'.Completion := P.isSeparable_completion P' hP
  have : IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion :=
    P.isIntegralClosure_completionIntegers P' hP
  have hmap : IsLocalization.map (S := F') P'.Completion
      (integralClosureToCompletionIntegers P P' hP)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (integralClosureToCompletionIntegers_injective P P' hP)) =
      P'.completionEmbedding.toRingHom := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun x ↦ ?_
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
  exact span_traceDual_one_eq_traceDual_one_completionIntegers P P' hP

/-- **The different ideal commutes with completion.** Extending the different ideal of `𝒪'_P` over
`𝒪_P` along `integralClosureToCompletionIntegers P P' hP` gives the different ideal of `𝒪̂_{P'}`
over `𝒪̂_P`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
      P.isTorsionFree_completionIntegersExtension P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (integralClosureToCompletionIntegers P P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtension P' hP
  have : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
    P.isTorsionFree_completionIntegersExtension P' hP
  have : FiniteDimensional P.Completion P'.Completion := P.finiteDimensional_completion P' hP
  have : Algebra.IsSeparable P.Completion P'.Completion := P.isSeparable_completion P' hP
  have : IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion :=
    P.isIntegralClosure_completionIntegers P' hP
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (integralClosureToCompletionIntegers_injective P P' hP)),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one_completionIntegers P P' hP]

/-- **The centre of `P'` on `𝒪'_P` generates the completed maximal ideal `𝔪̂_{P'}`.** -/
theorem map_centerIntegralClosure_completionIntegers (P' : Place k' F') :
    (centerIntegralClosure k F P').asIdeal.map
        (integralClosureToCompletionIntegers (P'.restrict k F) P' rfl) =
      maximalIdeal P'.completionPlace.integers := by
  let P := P'.restrict k F
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) fun z hz ↦ ?_
  · rw [Ideal.mem_comap, P'.completionPlace.mem_maximalIdeal_iff_valuation_lt_one,
      coe_integralClosureToCompletionIntegers, completionPlace_valuation,
      valuation_completionEmbedding]
    rw [centerIntegralClosure_def] at hy
    exact (mem_center_asIdeal _ _).mp hy
  · have hnot : ¬ (centerIntegralClosure k F P').asIdeal ^ 1 ≤
        (centerIntegralClosure k F P').asIdeal ^ 2 := by
      intro hle
      have hmul := multiplicity_pow_self_of_prime
        (Ideal.prime_of_isPrime (centerIntegralClosure k F P').ne_bot
          (centerIntegralClosure k F P').isPrime) 1
      have hdvd : (centerIntegralClosure k F P').asIdeal ^ 2 ∣
          (centerIntegralClosure k F P').asIdeal ^ 1 := Ideal.dvd_iff_le.mpr hle
      have hfin : FiniteMultiplicity (centerIntegralClosure k F P').asIdeal
          ((centerIntegralClosure k F P').asIdeal ^ 1) :=
        .of_not_isUnit (mt Ideal.isUnit_iff.mp (centerIntegralClosure k F P').isPrime.ne_top)
          (pow_ne_zero 1 (centerIntegralClosure k F P').ne_bot)
      have := hfin.pow_dvd_iff_le_multiplicity.mp hdvd
      omega
    obtain ⟨π, hπ1, hπ2⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    rw [pow_one] at hπ1
    have hπ0 : π ≠ 0 := by rintro rfl; exact hπ2 (zero_mem _)
    have hπ0' : (π : F') ≠ 0 := by simpa using hπ0
    have hord_le : P'.ord (π : F') ≤ 1 := by
      by_contra hgt
      have hfin : FiniteMultiplicity (centerIntegralClosure k F P').asIdeal (Ideal.span {π}) :=
        .of_prime_left (Ideal.prime_of_isPrime (centerIntegralClosure k F P').ne_bot
          (centerIntegralClosure k F P').isPrime) (by simpa using hπ0)
      have hmul : 2 ≤ multiplicity (centerIntegralClosure k F P').asIdeal (Ideal.span {π}) := by
        have h := P'.ord_algebraMap_eq_multiplicity_center
          (algebraMap_mem_integers_of_mem_integralClosure k F P') hπ0
        rw [← centerIntegralClosure_def] at h
        have : (2 : ℤ) ≤ P'.ord (algebraMap _ F' π) := by
          -- Coercion of `π` from the subalgebra `𝒪'_P` to `F'` is its `algebraMap`.
          change (2 : ℤ) ≤ P'.ord (π : F')
          omega
        omega
      exact hπ2 ((Ideal.span_singleton_le_iff_mem _).mp
        (Ideal.dvd_iff_le.mp (hfin.pow_dvd_iff_le_multiplicity.mpr hmul)))
    have hπ1' := hπ1
    rw [centerIntegralClosure_def] at hπ1'
    have hord_pos : 0 < P'.ord (π : F') :=
      (P'.valuation_lt_one_iff_ord_pos hπ0').mp ((mem_center_asIdeal _ _).mp hπ1')
    have hord1 : P'.ord (π : F') = 1 := by omega
    let πc := integralClosureToCompletionIntegers P P' rfl π
    have hπc0 : (πc : P'.Completion) ≠ 0 := by
      rw [coe_integralClosureToCompletionIntegers]
      exact (map_ne_zero _).mpr hπ0'
    have hq_int : (z : P'.Completion) / (πc : P'.Completion) ∈ P'.completionPlace.integers := by
      rcases eq_or_ne (z : P'.Completion) 0 with hz0 | hz0
      · simp [hz0]
      · rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div hz0 hπc0,
          coe_integralClosureToCompletionIntegers, ord_completionEmbedding, hord1]
        have hz_pos := (P'.completionPlace.mem_maximalIdeal_iff_ord_pos hz0).mp hz
        omega
    have hz_eq : z = ⟨(z : P'.Completion) / (πc : P'.Completion), hq_int⟩ * πc :=
      Subtype.ext (div_mul_cancel₀ (z : P'.Completion) hπc0).symm
    rw [hz_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hπ1)

/-- **The completed different ideal is `𝔪̂_{P'} ^ d(P' ∣ P)`.** -/
theorem differentIdeal_completionIntegers_eq_pow
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
      P.isTorsionFree_completionIntegersExtension P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have : Module.IsTorsionFree (P'.restrict k F).completionPlace.integers
      P'.completionPlace.integers :=
    (P'.restrict k F).isTorsionFree_completionIntegersExtension P' rfl
  rw [← map_differentIdeal_eq_differentIdeal_completionIntegers (P'.restrict k F) P' rfl]
  set d := differentExponent k F P'
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) fun z hz ↦ ?_
  · rw [Ideal.mem_comap, P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration,
      coe_integralClosureToCompletionIntegers, P'.completionEmbedding_mem_filtration_iff]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hy0' : (y : F') ≠ 0 := by simpa using hy0
    exact (P'.mem_filtration_iff_le_ord hy0').mpr
      (differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0)
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    have hy0' : (y : F') ≠ 0 := by simpa using hy0
    let yc := integralClosureToCompletionIntegers (P'.restrict k F) P' rfl y
    have hyc0 : (yc : P'.Completion) ≠ 0 := by
      rw [coe_integralClosureToCompletionIntegers]
      exact (map_ne_zero _).mpr hy0'
    have hq_int : (z : P'.Completion) / (yc : P'.Completion) ∈ P'.completionPlace.integers := by
      rcases eq_or_ne (z : P'.Completion) 0 with hz0 | hz0
      · simp [hz0]
      · rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div hz0 hyc0,
          coe_integralClosureToCompletionIntegers, ord_completionEmbedding]
        have hz_fil := (P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration d z).mp hz
        have hz_ord := (P'.completionPlace.mem_filtration_iff_le_ord hz0).mp hz_fil
        have hy_ord : P'.ord (y : F') = d := hord
        omega
    have hz_eq : z = ⟨(z : P'.Completion) / (yc : P'.Completion), hq_int⟩ * yc :=
      Subtype.ext (div_mul_cancel₀ (z : P'.Completion) hyc0).symm
    rw [hz_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hy)

/-- **Completion preserves the different exponent**, read as the multiplicity of `𝔪̂_{P'}` in the
completed different ideal `𝔇(𝒪̂_{P'} / 𝒪̂_P)`. -/
@[simp]
theorem multiplicity_differentIdeal_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
      P.isTorsionFree_completionIntegersExtension P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let := P.completionIntegersExtensionAlgebra P' hP
  have : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
    P.isTorsionFree_completionIntegersExtension P' hP
  rw [differentIdeal_completionIntegers_eq_pow P P' hP]
  exact multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance) _

/-- **Length of the completed different quotient.** Over `𝒪̂_P`, the quotient
`𝒪̂_{P'} ⧸ 𝔇(𝒪̂_{P'} / 𝒪̂_P)` has length `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full
relative residue degree including any inseparable factor. -/
theorem length_quotient_differentIdeal_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
      P.isTorsionFree_completionIntegersExtension P' hP
    Module.length P.completionPlace.integers
        (P'.completionPlace.integers ⧸
          differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have : Module.IsTorsionFree (P'.restrict k F).completionPlace.integers
      P'.completionPlace.integers :=
    (P'.restrict k F).isTorsionFree_completionIntegersExtension P' rfl
  have : IsScalarTower (P'.restrict k F).completionPlace.integers P'.completionPlace.integers
      P'.Completion :=
    (P'.restrict k F).isScalarTower_completionIntegersExtension P' rfl
  have : FiniteDimensional (P'.restrict k F).Completion P'.Completion :=
    (P'.restrict k F).finiteDimensional_completion P' rfl
  have : Algebra.IsSeparable (P'.restrict k F).Completion P'.Completion :=
    (P'.restrict k F).isSeparable_completion P' rfl
  have : IsIntegralClosure P'.completionPlace.integers
      (P'.restrict k F).completionPlace.integers P'.Completion :=
    (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have : Module.Finite (P'.restrict k F).completionPlace.integers P'.completionPlace.integers :=
    (P'.restrict k F).moduleFinite_completionIntegers P' rfl
  rw [IsLocalRing.length_restrictScalars
        (P'.restrict k F).completionPlace.integers P'.completionPlace.integers,
      Ideal.length_quotient_eq_multiplicity _
        (differentIdeal_ne_bot_of_isSeparable
          (K := (P'.restrict k F).Completion) (L := P'.Completion)),
      multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
      Module.length_eq_finrank,
      P'.finrank_residueField_completion (k := k) (F := F)]

/-- **Length of the completed complementary-module quotient.** Over `𝒪̂_P`, the quotient of the
completed complementary module `Submodule.traceDual 𝒪̂_P F̂_P 1` by `𝒪̂_{P'}` has length
`d(P' ∣ P) · f(P' ∣ P)`, with no separability hypothesis on the residue extension. -/
theorem length_traceDual_quotient_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
      P.isScalarTower_completionIntegersExtension P' hP
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
  have : Module.IsTorsionFree (P'.restrict k F).completionPlace.integers
      P'.completionPlace.integers :=
    (P'.restrict k F).isTorsionFree_completionIntegersExtension P' rfl
  have : IsScalarTower (P'.restrict k F).completionPlace.integers P'.completionPlace.integers
      P'.Completion :=
    (P'.restrict k F).isScalarTower_completionIntegersExtension P' rfl
  have : FiniteDimensional (P'.restrict k F).Completion P'.Completion :=
    (P'.restrict k F).finiteDimensional_completion P' rfl
  have : Algebra.IsSeparable (P'.restrict k F).Completion P'.Completion :=
    (P'.restrict k F).isSeparable_completion P' rfl
  have : IsIntegralClosure P'.completionPlace.integers
      (P'.restrict k F).completionPlace.integers P'.Completion :=
    (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have : Module.Finite (P'.restrict k F).completionPlace.integers P'.completionPlace.integers :=
    (P'.restrict k F).moduleFinite_completionIntegers P' rfl
  rw [length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **Valuation of the completed discriminant.** For any `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`, the order of
vanishing of `Algebra.discr 𝒪̂_P b` in `𝒪̂_P` is `d(P' ∣ P) · f(P' ∣ P)`, including any inseparable
factor of the residue degree. -/
theorem ord_discr_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have : Module.IsTorsionFree (P'.restrict k F).completionPlace.integers
      P'.completionPlace.integers :=
    (P'.restrict k F).isTorsionFree_completionIntegersExtension P' rfl
  have : IsScalarTower (P'.restrict k F).completionPlace.integers P'.completionPlace.integers
      P'.Completion :=
    (P'.restrict k F).isScalarTower_completionIntegersExtension P' rfl
  have : Algebra.IsSeparable (P'.restrict k F).Completion P'.Completion :=
    (P'.restrict k F).isSeparable_completion P' rfl
  have : IsIntegralClosure P'.completionPlace.integers
      (P'.restrict k F).completionPlace.integers P'.Completion :=
    (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  intro b
  rw [ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

end SinglePlace

section Constants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- **Completion preserves `Place.differentExponent`** when the constant fields agree. -/
@[simp]
theorem differentExponent_completionPlace
    (P : Place k F) (P' : Place k F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    haveI : @IsScalarTower k P.Completion P'.Completion
        P.instAlgebraCompletion.toSMul (P.completionExtensionAlgebra P' hP).toSMul
        P'.instAlgebraCompletion.toSMul :=
      P.isScalarTower_completionExtensionAlgebra P' hP
    haveI : FiniteDimensional P.Completion P'.Completion := P.finiteDimensional_completion P' hP
    haveI : Algebra.IsSeparable P.Completion P'.Completion := P.isSeparable_completion P' hP
    differentExponent k P.Completion P'.completionPlace = differentExponent k F P' := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have : @IsScalarTower k P.Completion P'.Completion
      P.instAlgebraCompletion.toSMul (P.completionExtensionAlgebra P' hP).toSMul
      P'.instAlgebraCompletion.toSMul :=
    P.isScalarTower_completionExtensionAlgebra P' hP
  have : @IsScalarTower k k P'.Completion
      Algebra.toSMul P'.instAlgebraCompletion.toSMul P'.instAlgebraCompletion.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion :=
    P.isScalarTower_completionIntegersExtension P' hP
  have : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
    P.isTorsionFree_completionIntegersExtension P' hP
  have : FiniteDimensional P.Completion P'.Completion := P.finiteDimensional_completion P' hP
  have : Algebra.IsSeparable P.Completion P'.Completion := P.isSeparable_completion P' hP
  have : IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion :=
    P.isIntegralClosure_completionIntegers P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  have hcenter : (P'.completionPlace.center hC).asIdeal =
      maximalIdeal P'.completionPlace.integers := by
    ext x
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  rw [differentExponent_eq_multiplicity_center (B := P.completionPlace.integers)
      (C := P'.completionPlace.integers) P'.completionPlace hC,
    hcenter, multiplicity_differentIdeal_completionIntegers P P' hP]

end Constants

section Semilocal

open scoped PlaceCompletion

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- **The different ideal in the integral semilocal decomposition.** Extending the different ideal
of `𝒪'_P` over `𝒪_P` to `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` and transporting along
`TauCeti.Place.integralSemilocalEquiv` yields the product of the completed different ideals at the
places of `F' / k'` lying over `P`. -/
theorem differentIdeal_integralSemilocal (P : Place k F) :
    haveI (Q : {P' : Place k' F' // P'.restrict k F = P}) :
        Module.IsTorsionFree P.completionPlace.integers Q.1.completionPlace.integers :=
      P.isTorsionFree_completionIntegersExtension Q.1 Q.2
    ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (integralSemilocalEquiv k' F' P) =
      Ideal.pi fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
        differentIdeal P.completionPlace.integers Q.1.completionPlace.integers := by
  have (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Module.IsTorsionFree P.completionPlace.integers Q.1.completionPlace.integers :=
    P.isTorsionFree_completionIntegersExtension Q.1 Q.2
  let incR : integralClosure P.integers F' →ₐ[P.integers]
      P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' :=
    Algebra.TensorProduct.includeRight
  have hmap : ((differentIdeal P.integers (integralClosure P.integers F')).map incR).map
        (integralSemilocalEquiv k' F' P) =
      (differentIdeal P.integers (integralClosure P.integers F')).map
        ((integralSemilocalEquiv k' F' P).toRingEquiv.toRingHom.comp incR.toRingHom) :=
    Ideal.map_map incR.toRingHom (integralSemilocalEquiv k' F' P).toRingEquiv.toRingHom
  rw [hmap]
  apply Ideal.piOrderIso.injective
  funext Q
  simp only [Ideal.piOrderIso, OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk,
    RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, AlgHom.toRingHom_eq_coe]
  rw [Ideal.map_evalRingHom_pi, Ideal.map_map,
    ← map_differentIdeal_eq_differentIdeal_completionIntegers P Q.1 Q.2]
  congr 1
  ext x
  simp [incR]

end Semilocal

end TauCeti.Place
