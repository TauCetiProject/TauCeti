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
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Separable
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
  (`TauCeti.Place.differentIdeal_completionIntegers_eq_pow`), so its multiplicity at `𝔪̂_{P'}` —
  and, when the constant fields agree, the different exponent of the completed places — equals
  `d(P' ∣ P)` (`TauCeti.Place.multiplicity_differentIdeal_completionIntegers`,
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

Completion invariance allows `d(P' ∣ P)`, complementary-module quotient lengths, and local
discriminant valuations to be computed purely locally in the completed extension `𝒪̂_{P'} / 𝒪̂_P`
without residue-separability or residue-finiteness hypotheses, and transports global differential
and cotrace data to completions.

No assumption is made on the characteristic, on `IsFunctionField`, or on the finiteness or
separability of the residue fields. Single-place statements over `k' / k` dispense with
`[Algebra.IsIntegral k k']` by restricting the constant field of `P'` to `k` via
`TauCeti.Place.restrictConstants` before invoking the semilocal decomposition of
`TauCeti/FieldTheory/FunctionField/Place/Completion/Semilocal.lean` (while
`TauCeti.Place.differentExponent_completionPlace` assumes matching constant fields `k' = k` so
`P'.completionPlace` is a place over the same constant field `k` as `P.Completion`). Semilocal
statements (`TauCeti.Place.differentIdeal_integralSemilocal`) require `open scoped PlaceCompletion`,
whereas single-place statements bind `completionExtensionAlgebra` and
`completionIntegersExtensionAlgebra` locally via `letI`.

The trace-dual comparison adapts `IsDedekindDomain.HeightOneSpectrum` in
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

section FiberSeparable

open scoped PlaceCompletion

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {P : Place k F}

/-- Separability of `F̂'_Q` over `F̂_P` for a place `Q` in the fiber over `P`. -/
theorem fiberCompletion_isSeparable (Q : {P' : Place k' F' // P'.restrict k F = P}) :
    Algebra.IsSeparable P.Completion Q.1.Completion :=
  P.isSeparable_completion Q.1 Q.2

-- Register `fiberCompletion_isSeparable` alongside the `PlaceCompletion` fiber instances from
-- `Place/Completion/Semilocal.lean`.
scoped[PlaceCompletion] attribute [instance] TauCeti.Place.fiberCompletion_isSeparable

end FiberSeparable

section SinglePlace

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- Supplies the standard single-place completed extension instances (`IsScalarTower`,
`Module.IsTorsionFree`, `FiniteDimensional`, `Algebra.IsSeparable`, `IsIntegralClosure`, and
`Module.Finite`) in one step once `completionExtensionAlgebra` and
`completionIntegersExtensionAlgebra` are bound. -/
private theorem withCompletionExtension {P : Place k F} {P' : Place k' F'}
    (hP : P'.restrict k F = P)
    {Goal :
      letI := P.completionExtensionAlgebra P' hP
      letI := P.completionIntegersExtensionAlgebra P' hP
      Prop}
    (h :
      letI := P.completionExtensionAlgebra P' hP
      letI := P.completionIntegersExtensionAlgebra P' hP
      ∀ [IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion]
        [Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers]
        [FiniteDimensional P.Completion P'.Completion]
        [Algebra.IsSeparable P.Completion P'.Completion]
        [IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion]
        [Module.Finite P.completionPlace.integers P'.completionPlace.integers],
        Goal) :
    Goal := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtension P' hP
  have := P.isTorsionFree_completionIntegersExtension P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isSeparable_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.moduleFinite_completionIntegers P' hP
  exact h

open scoped PlaceCompletion in
omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
/-- On the image of `𝒪̂_P ⊗[𝒪_P] 𝒪'_P`, the trace pairing with an element of the local
complementary module takes values in `𝒪̂_P`. -/
private theorem trace_integralSemilocalToField_mul_mem [Algebra.IsIntegral F F']
    (P : Place k F) {d : F'}
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
    rw [Subalgebra.algebraMap_apply, Algebra.traceForm_apply, mul_comm] at hr
    refine ⟨a * algebraMap P.integers P.completionPlace.integers r, ?_⟩
    rw [trace_integralSemilocalToField_tmul_mul, ← hr]
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
    let P'₀ : Place k F' := P'.restrictConstants k
    have hP₀ : P'₀.restrict k F = P := (restrict_restrictConstants k F P').trans hP
    set Q₀ : {Q : Place k F' // Q.restrict k F = P} := ⟨P'₀, hP₀⟩
    let z₀ : Q₀.1.completionPlace.integers :=
      ⟨(z : P'.Completion), (mem_completionPlace_integers_restrictConstants P').mpr z.2⟩
    let f : ∀ Q : {Q : Place k F' // Q.restrict k F = P}, Q.1.completionPlace.integers :=
      Pi.single Q₀ z₀
    let t := (integralSemilocalEquiv k F' P).symm f
    have hcoe : (fun Q ↦ (f Q : Q.1.Completion)) = Pi.single Q₀ (z₀ : Q₀.1.Completion) := by
      funext Q'
      obtain rfl | hQ' := eq_or_ne Q' Q₀
      · simp [f]
      · simp [f, Pi.single_eq_of_ne hQ']
    have htr := trace_semilocalEquiv_symm_single_mul P Q₀ (z₀ : Q₀.1.Completion) d
    rw [← hcoe, ← integralSemilocalToField_integralSemilocalEquiv_symm P f] at htr
    have htr' : (@Algebra.trace P.Completion P'.Completion _ _
          (P.completionExtensionAlgebra P' hP))
          ((z : P'.Completion) * P'.completionEmbedding d) =
        (@Algebra.trace P.Completion Q₀.1.Completion _ _ (fiberCompletionAlgebra Q₀))
          ((z₀ : Q₀.1.Completion) * Q₀.1.completionEmbedding d) := by
      rw [← P.completionExtensionAlgebra_restrictConstants P' hP]
      simp only [Q₀, P'₀, completionEmbedding_restrictConstants, z₀]
    rw [htr', ← htr]
    exact trace_integralSemilocalToField_mul_mem P hd t
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtension P' hP
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
  have := P.isScalarTower_completionIntegersExtension P' hP
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
    Submodule.mem_one.mpr ⟨P.integralClosureToCompletionIntegers P' hP (b i), by
      rw [ValuationSubring.algebraMap_apply, coe_integralClosureToCompletionIntegers]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ hb_mem
  rw [Algebra.traceForm_apply] at hc
  rw [← hc, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace-dual
fractional ideal of `𝒪'_P` over `𝒪_P` along `P.integralClosureToCompletionIntegers P' hP` yields
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
          (P.integralClosureToCompletionIntegers_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal (P'.completionPlace.integers)⁰ P'.Completion) := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  apply withCompletionExtension (k := k) hP
  intro _ _ _ _ _ _
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.integralClosureToCompletionIntegers P' hP)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.integralClosureToCompletionIntegers_injective P' hP)) =
      P'.completionEmbedding.toRingHom := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun x ↦ ?_
    rw [IsLocalization.map_eq, ValuationSubring.algebraMap_apply,
      coe_integralClosureToCompletionIntegers, Subalgebra.algebraMap_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
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
`𝒪_P` along `P.integralClosureToCompletionIntegers P' hP` gives the different ideal of `𝒪̂_{P'}`
over `𝒪̂_P`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI : Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers :=
      P.isTorsionFree_completionIntegersExtension P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.integralClosureToCompletionIntegers P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  apply withCompletionExtension (k := k) hP
  intro _ _ _ _ _ _
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (P.integralClosureToCompletionIntegers_injective P' hP)),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one_completionIntegers P P' hP]

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
/-- An ideal `I` of `𝒪'_P` whose nonzero elements have `P'`-order at least `n`, and which contains
a nonzero element of `P'`-order `n`, generates `𝔪̂_{P'} ^ n` in `𝒪̂_{P'}`. -/
private theorem map_integralClosureToCompletionIntegers_eq_maximalIdeal_pow
    [Algebra.IsIntegral F F'] (P' : Place k' F')
    {I : Ideal (integralClosure (P'.restrict k F).integers F')} {n : ℕ}
    (hle : ∀ y ∈ I, y ≠ 0 → (n : ℤ) ≤ P'.ord (y : F'))
    (hex : ∃ y ∈ I, y ≠ 0 ∧ P'.ord (y : F') = n) :
    I.map ((P'.restrict k F).integralClosureToCompletionIntegers P' rfl) =
      maximalIdeal P'.completionPlace.integers ^ n := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) fun z hz ↦ ?_
  · rw [Ideal.mem_comap, P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration,
      coe_integralClosureToCompletionIntegers, P'.completionEmbedding_mem_filtration_iff]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    exact (P'.mem_filtration_iff_le_ord (by simpa using hy0)).mpr (hle y hy hy0)
  · obtain ⟨y, hy, hy0, hord⟩ := hex
    let yc := (P'.restrict k F).integralClosureToCompletionIntegers P' rfl y
    have hyc0 : (yc : P'.Completion) ≠ 0 := by
      rw [coe_integralClosureToCompletionIntegers]
      exact (map_ne_zero _).mpr (by simpa using hy0)
    have hinv_ord : P'.completionPlace.ord (yc : P'.Completion)⁻¹ = -(n : ℤ) := by
      rw [P'.completionPlace.ord_inv, coe_integralClosureToCompletionIntegers,
        ord_completionEmbedding, hord]
    have hfil : (z : P'.Completion) ∈ P'.completionPlace.filtration n :=
      (P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration n z).mp hz
    have hq_int : (yc : P'.Completion)⁻¹ * (z : P'.Completion) ∈ P'.completionPlace.integers :=
      P'.completionPlace.mul_mem_integers_of_mem_filtration hinv_ord hfil
    have hz_eq : z = ⟨(yc : P'.Completion)⁻¹ * (z : P'.Completion), hq_int⟩ * yc :=
      Subtype.ext (by rw [MulMemClass.coe_mul, mul_comm, mul_inv_cancel_left₀ hyc0])
    rw [hz_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hy)

/-- The centre of `P'` on `𝒪'_P` contains a nonzero element of `P'`-order `1`. -/
theorem exists_mem_centerIntegralClosure_ord_eq_one (P' : Place k' F') :
    ∃ π ∈ (centerIntegralClosure k F P').asIdeal,
      π ≠ 0 ∧ P'.ord (π : F') = 1 := by
  obtain ⟨π, hπ⟩ := (centerIntegralClosure k F P').intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.coe_ne_zero hπ.symm
  have hπ0' : (π : F') ≠ 0 := by simpa using hπ0
  have hval : P'.valuation (π : F') = WithZero.exp (-1 : ℤ) := by
    rw [← Subalgebra.algebraMap_apply,
      ← P'.valuation_center (algebraMap_mem_integers_of_mem_integralClosure k F P'),
      ← centerIntegralClosure_def, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hmem : π ∈ (centerIntegralClosure k F P').asIdeal := by
    rw [centerIntegralClosure_def, mem_center_asIdeal, Subalgebra.algebraMap_apply, hval,
      ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  exact ⟨π, hmem, hπ0, (P'.ord_eq_iff_valuation_eq_exp_neg hπ0').mpr hval⟩

/-- **The centre of `P'` on `𝒪'_P` generates the completed maximal ideal `𝔪̂_{P'}`.** -/
theorem map_centerIntegralClosure_completionIntegers (P' : Place k' F') :
    (centerIntegralClosure k F P').asIdeal.map
        ((P'.restrict k F).integralClosureToCompletionIntegers P' rfl) =
      maximalIdeal P'.completionPlace.integers := by
  rw [← pow_one (maximalIdeal P'.completionPlace.integers)]
  refine map_integralClosureToCompletionIntegers_eq_maximalIdeal_pow P'
    (fun y hy hy0 ↦ ?_) (exists_mem_centerIntegralClosure_ord_eq_one P')
  rw [centerIntegralClosure_def,
    P'.mem_center_asIdeal_iff_ord_pos (algebraMap_mem_integers_of_mem_integralClosure k F P') hy0,
    Subalgebra.algebraMap_apply] at hy
  omega

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
  have := (P'.restrict k F).isTorsionFree_completionIntegersExtension P' rfl
  rw [← map_differentIdeal_eq_differentIdeal_completionIntegers (P'.restrict k F) P' rfl]
  refine map_integralClosureToCompletionIntegers_eq_maximalIdeal_pow P'
    (fun y hy hy0 ↦ ?_) ?_
  · simpa only [Subalgebra.algebraMap_apply] using
      differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    rw [Subalgebra.algebraMap_apply] at hord
    exact ⟨y, hy, hy0, hord⟩

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
  have := P.isTorsionFree_completionIntegersExtension P' hP
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
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegersExtension P' rfl
  have := (P'.restrict k F).moduleFinite_completionIntegers P' rfl
  rw [IsLocalRing.length_restrictScalars
        (P'.restrict k F).completionPlace.integers P'.completionPlace.integers,
      differentIdeal_completionIntegers_eq_pow (P'.restrict k F) P' rfl,
      Ideal.length_quotient_eq_multiplicity _
        (pow_ne_zero _ (IsDiscreteValuationRing.not_a_field _)),
      multiplicity_pow_self_of_prime
        (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance),
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
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  apply withCompletionExtension (k := k) hP
  intro _ _ _ _ _ _
  rw [length_traceDual_quotient_eq_length_quotient_differentIdeal,
    length_quotient_differentIdeal_completionIntegers P P' hP]

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
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  apply withCompletionExtension (k := k) hP
  intro _ _ _ _ _ _ b
  subst hP
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
  apply withCompletionExtension (k := k) hP
  intro _ _ _ _ _ _
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  have hcenter : (P'.completionPlace.center hC).asIdeal =
      maximalIdeal P'.completionPlace.integers := by
    ext x
    rw [mem_center_asIdeal, ValuationSubring.algebraMap_apply,
      P'.completionPlace.mem_maximalIdeal_iff_valuation_lt_one]
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
    ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (integralSemilocalEquiv k' F' P) =
      Ideal.pi fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
        differentIdeal P.completionPlace.integers Q.1.completionPlace.integers := by
  let incR : integralClosure P.integers F' →ₐ[P.integers]
      P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' :=
    Algebra.TensorProduct.includeRight
  have hmap : ((differentIdeal P.integers (integralClosure P.integers F')).map incR).map
        (integralSemilocalEquiv k' F' P) =
      (differentIdeal P.integers (integralClosure P.integers F')).map
        ((integralSemilocalEquiv k' F' P).toRingEquiv.toRingHom.comp incR.toRingHom) :=
    Ideal.map_map incR.toRingHom (integralSemilocalEquiv k' F' P).toRingEquiv.toRingHom
  have hpi (K : Ideal (∀ Q : {P' : Place k' F' // P'.restrict k F = P},
      Q.1.completionPlace.integers)) (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      Ideal.piOrderIso K Q = K.map (Pi.evalRingHom _ Q) := by
    ext x
    rw [← SetLike.mem_coe, Ideal.coe_piOrderIso_apply, Ideal.map, Submodule.mem_span]
    simp [Set.image_subset_iff]
  rw [hmap]
  apply Ideal.piOrderIso.injective
  funext Q
  rw [hpi, hpi, Ideal.map_evalRingHom_pi, Ideal.map_map,
    ← map_differentIdeal_eq_differentIdeal_completionIntegers P Q.1 Q.2]
  congr 1
  ext x
  simp [incR]

end Semilocal

end TauCeti.Place
