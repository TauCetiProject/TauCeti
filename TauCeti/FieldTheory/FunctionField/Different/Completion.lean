/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant

import TauCeti.FieldTheory.FunctionField.Different.Localization
import TauCeti.FieldTheory.FunctionField.Place.Completion.Adic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Multiplicity
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily
import TauCeti.RingTheory.DedekindDomain.Different.Semilocal
import TauCeti.RingTheory.NormTrace.Pi

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
exponent, complementary-module and different-ideal quotient lengths, and trace Gram discriminant
valuation of the completed extension `𝒪̂_{P'} / 𝒪̂_P` to those of `F' / F` at `P'`:

* **Trace-dual expansions and complementary modules**: any global trace-dual expansion over `F`
  remains valid over `P'.Completion / P.Completion`
  (`TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`), and the completed complementary
  module `Ĉ_{P'/P}` is the `𝒪̂_{P'}`-span of the image of the local-model complementary module
  `C_P` (`TauCeti.Place.traceDual_one_completionIntegers_eq_span`,
  `TauCeti.Place.extended_dual_one_eq_dual_one_completionIntegers`).
* **The different ideal commutes with completion**: extending `𝔇(𝒪'_P / 𝒪_P)` along
  `completionIntegersIntegralClosureHom : 𝒪'_P →+* 𝒪̂_{P'}` yields `𝔇(𝒪̂_{P'} / 𝒪̂_P)`
  (`TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers`), as does extending the
  different ideal `𝔇(C / B)` where `C` is the integral closure in `F'` of an affine Dedekind model
  `B` of `F` on which `P'` is finite
  (`TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers_of_isIntegralClosure`);
  across the integral semilocal decomposition, the extended different decomposes into the product
  of the completed differents above `P`
  (`TauCeti.Place.differentIdeal_integralCompletionSemilocal`).
* **Invariance of the different exponent and completed valuation criterion**:
  extending any nonzero ideal of `𝒪'_P` along `completionIntegersIntegralClosureHom` preserves its
  multiplicity at the centre of `P'`
  (`TauCeti.Place.multiplicity_map_completionIntegersIntegralClosureHom`), so the multiplicity of
  `𝔪̂_{P'}` in `𝔇(𝒪̂_{P'} / 𝒪̂_P)` is `d(P' ∣ P)`
  (`TauCeti.Place.multiplicity_differentIdeal_completionIntegers`),
  `𝔇(𝒪̂_{P'} / 𝒪̂_P) = 𝔪̂_{P'} ^ d(P' ∣ P)`
  (`TauCeti.Place.differentIdeal_completionIntegers_eq_maximalIdeal_pow`), the place-level different
  exponent of `P'.completionPlace` over `P.Completion` equals `d(P' ∣ P)`
  (`TauCeti.Place.differentExponent_completionPlace`), and `z ∈ P'.Completion` belongs to
  `Ĉ_{P'/P}` if and only if `v_{P̂'}(z) ≤ exp d(P' ∣ P)`
  (`TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`).
* **Completed length and discriminant formulas (including fierce residue extensions)**:
  `length_{𝒪̂_P}(𝒪̂_{P'} / 𝔇(𝒪̂_{P'} / 𝒪̂_P)) = length_{𝒪̂_P}(Ĉ_{P'/P} / 𝒪̂_{P'})`
  `= d(P' ∣ P) · f(P' ∣ P)`
  (`TauCeti.Place.length_quotient_differentIdeal_completionIntegers`,
  `TauCeti.Place.length_traceDual_completionIntegers_quotient`,
  `TauCeti.Place.length_traceDual_completionIntegers_quotient_eq`) and
  `ord_{𝒪̂_P}(discr_{𝒪̂_P} b) = d(P' ∣ P) · f(P' ∣ P)` for every `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`
  (`TauCeti.Place.ord_discr_completionIntegers`, `TauCeti.Place.ord_discr_completionIntegers_eq`),
  where `f(P' ∣ P) = [κ(P') : κ(P)]` is the full relative residue degree including its inseparable
  factor.

## Implementation notes

The semilocal trace-dual argument instantiates the abstract Dedekind-domain comparison in
`TauCeti/RingTheory/DedekindDomain/Different/Semilocal.lean` (shared with
`TauCeti/RingTheory/DedekindDomain/Different/Completion.lean`) at the place-completion
decompositions `TauCeti.Place.completionSemilocalEquiv` and
`TauCeti.Place.integralCompletionSemilocalEquiv`. To avoid imposing `[Algebra.IsIntegral k k']` in
single-place theorems, the internal semilocal steps restrict the constant field of `P'` to `k` via
`TauCeti.Place.restrictScalars` and transport across
`TauCeti.Place.completionExtensionRestrictScalarsEquiv`. As in `TauCeti.Place`'s global different
API, single-place statements install `TauCeti.Place.completionExtensionAlgebra` and
`TauCeti.Place.completionIntegersExtensionAlgebra` locally via `letI`, together with
`TauCeti.Place.algebraIntegersExtension` and `TauCeti.Place.isScalarTowerIntegersExtension` at
priority `10`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §8, nos. 2 and 5.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3 and Chapter III, §§2–4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.7, III.4, and III.5.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing Module
open scoped PlaceCompletionExtension TensorProduct WithZero nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section FibreInstances

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] {P : Place k F}

-- Typeclass synthesis does not look through the subtype projection `w.val` when solving
-- family-level `Field` and `Module.Free` goals on `{Q' : Place k F' // Q'.restrict k F = P}`,
-- and `TauCeti.Place.finiteDimensional_completion` takes an explicit `P'.restrict k F = P` proof
-- because `completionExtensionAlgebra` is not a global instance on `P'.Completion` (only on the
-- fibre subtype in the `PlaceCompletionExtension` scope). These local instances supply the
-- resulting family-level `Field`, `FiniteDimensional`, and `Module.Free` instances.
@[instance_reducible]
private noncomputable def fieldCompletionAbove :
    ∀ w : {Q' : Place k F' // Q'.restrict k F = P}, Field w.val.Completion :=
  fun _ ↦ inferInstance

private theorem finiteDimensional_completion_above
    (w : {Q' : Place k F' // Q'.restrict k F = P}) :
    FiniteDimensional P.Completion w.val.Completion :=
  finiteDimensional_completion P w.val w.property

private theorem moduleFree_completion_above
    (w : {Q' : Place k F' // Q'.restrict k F = P}) :
    Module.Free P.Completion w.val.Completion :=
  inferInstance

end FibreInstances

section OnePlace

attribute [local instance] fieldCompletionAbove finiteDimensional_completion_above
  moduleFree_completion_above

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
private theorem isTorsionFree_integers [Algebra.IsIntegral F F'] (Q' : Place k' F') :
    Module.IsTorsionFree (Q'.restrict k F).integers Q'.integers :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr fun _ _ hab ↦ Subtype.ext <|
    (algebraMap F F').injective <| by simpa [coe_algebraMap_integers] using congrArg Subtype.val hab

/-! ### Trace-dual expansions and the completed complementary module -/

omit [FiniteDimensional F F'] in
private theorem trace_mul_completionEmbedding_restrictScalars (z : P'.Completion) (x : F') :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionExtensionAlgebra (P'.restrictScalars k)
      (P'.restrictScalarsAbove k hP).property
    Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding x) =
      Algebra.trace P.Completion (P'.restrictScalars k).Completion
        ((P'.completionRestrictScalarsRingEquiv k).symm z *
          (P'.restrictScalars k).completionEmbedding x) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionExtensionAlgebra (P'.restrictScalars k)
    (P'.restrictScalarsAbove k hP).property
  let e := P.completionExtensionRestrictScalarsEquiv P' hP
  have hmul : e.symm (z * P'.completionEmbedding x) =
      (P'.completionRestrictScalarsRingEquiv k).symm z *
        (P'.restrictScalars k).completionEmbedding x := by
    rw [map_mul, completionExtensionRestrictScalarsEquiv_symm_apply,
      completionExtensionRestrictScalarsEquiv_symm_apply,
      completionRestrictScalarsRingEquiv_symm_completionEmbedding]
  exact (Algebra.trace_eq_of_algEquiv e.symm (z * P'.completionEmbedding x)).symm.trans
    (congrArg (Algebra.trace P.Completion (P'.restrictScalars k).Completion) hmul)

/-- **Trace-dual expansions pass to place completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) yᵢ` for every
`x ∈ F'`, then `z = ∑ᵢ Tr_{F̂'_{P'}/F̂_P}(z bᵢ) yᵢ` for every `z ∈ P'.Completion`. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {ι : Type*} [Fintype ι] (b y : ι → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionExtensionAlgebra (P'.restrictScalars k)
    (P'.restrictScalarsAbove k hP).property
  let e := P.completionExtensionRestrictScalarsEquiv P' hP
  have h₀ := (completionSemilocalEquiv k F' P).sum_trace_mul_smul_eq
    b y h (P'.restrictScalarsAbove k hP) ((P'.completionRestrictScalarsRingEquiv k).symm z)
  simp only [completionSemilocalEquiv_tmul, map_one, one_mul] at h₀
  have he := (congrArg e h₀).trans (by
    rw [completionExtensionRestrictScalarsEquiv_apply, RingEquiv.apply_symm_apply])
  rw [map_sum] at he
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) he
  rw [trace_mul_completionEmbedding_restrictScalars P P' hP, map_smul,
    completionExtensionRestrictScalarsEquiv_apply,
    completionRestrictScalarsRingEquiv_completionEmbedding]

private theorem completionEmbedding_mem_traceDual {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  let _ := P.completionExtensionAlgebra (P'.restrictScalars k)
    (P'.restrictScalarsAbove k hP).property
  let _ := P.completionIntegersExtensionAlgebra (P'.restrictScalars k)
    (P'.restrictScalarsAbove k hP).property
  have h₀ := (completionSemilocalEquiv k F' P).mem_traceDual_one_of_semilocal
    (integralCompletionSemilocalEquiv k F' P)
    (fun w ↦ w.val.completionEmbedding.toRingHom)
    (fun w ↦ P.completionIntegersIntegralClosureHom w.val w.property)
    (fun a x w ↦ completionSemilocalEquiv_tmul a x w)
    (fun a x w ↦ integralCompletionSemilocalEquiv_tmul a x w)
    (fun _ _ ↦ by simp) (P'.restrictScalarsAbove k hP) hd
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  have hz₀ : (P'.completionRestrictScalarsRingEquiv k).symm (z : P'.Completion) ∈
      (P'.restrictScalars k).completionPlace.integers :=
    (P'.completionRestrictScalarsRingEquiv_symm_mem_integers_iff (k₀ := k)).mpr z.property
  have hmem₀ := Submodule.mem_traceDual.mp h₀ _ (Submodule.mem_one.mpr ⟨⟨_, hz₀⟩, rfl⟩)
  rw [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply,
    mul_comm (P'.completionEmbedding d) (z : P'.Completion),
    trace_mul_completionEmbedding_restrictScalars P P' hP,
    mul_comm _ ((P'.restrictScalars k).completionEmbedding d)]
  rwa [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply] at hmem₀

/-- **The completed complementary module is generated by the local-model complementary module**,
with no hypothesis on the residue fields. -/
theorem traceDual_one_completionIntegers_eq_span :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) =
      Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F')) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  exact (P'.completionEmbedding.toRingHom.span_traceDual_one_eq_traceDual_one_of_forall
    (P.completionIntegersIntegralClosureHom P' hP) (fun _ ↦ by simp)
    (fun _ hd ↦ completionEmbedding_mem_traceDual P P' hP hd)
    (fun b y hb ↦ P.sum_trace_mul_smul_completionEmbedding_eq P' hP b y hb)).symm

/-- **Trace duals commute with place completion**, as fractional ideals: extending the trace dual
of `integralClosure P.integers F'` over `P.integers` along `completionIntegersIntegralClosureHom`
gives the trace dual of `P'.completionPlace.integers` over `P.completionPlace.integers`. -/
theorem extended_dual_one_eq_dual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := P.finiteDimensional_completion P' hP
    letI := P.isIntegralClosure_completionIntegers P' hP
    letI := P.isSeparable_completion P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P.completionIntegersIntegralClosureHom_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal (P'.completionPlace.integers)⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  exact P'.completionEmbedding.toRingHom.extended_dual_one_eq_dual_one_of_span_eq
    (P.completionIntegersIntegralClosureHom P' hP)
    (P.completionIntegersIntegralClosureHom_injective P' hP) (fun _ ↦ by simp)
    (P.traceDual_one_completionIntegers_eq_span P' hP).symm

/-! ### Compatibility of the different ideal with completion -/

/-- **The different ideal commutes with place completion.** Extending the different ideal of the
local model `integralClosure P.integers F'` over `P.integers` along
`completionIntegersIntegralClosureHom` gives the different ideal of `P'.completionPlace.integers`
over `P.completionPlace.integers`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.completionIntegersIntegralClosureHom P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  exact (P.completionIntegersIntegralClosureHom P' hP)
    |>.map_differentIdeal_eq_differentIdeal_of_extended_eq
      (P.completionIntegersIntegralClosureHom_injective P' hP)
      (P.extended_dual_one_eq_dual_one_completionIntegers P' hP)

/-- **Extending the different ideal of an integral closure to the completion.** If `C` is the
integral closure in `F'` of a Dedekind `F`-model `B` and `P'` is finite on `C`, then extending
`differentIdeal B C` to `P'.completionPlace.integers` yields
`differentIdeal P.completionPlace.integers P'.completionPlace.integers`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers_of_isIntegralClosure
    {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    [CommRing C] [IsDedekindDomain C] [Algebra C F']
    [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
    [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal B C).map
        (P'.completionIntegersEmbedding.toRingHom.comp
          ((algebraMap C F').codRestrict P'.integers hC)) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  subst hP
  have hB : ∀ b : B, algebraMap B F b ∈ (P'.restrict k F).integers :=
    algebraMap_mem_integers_restrict k F P' hC
  let fC : C →+* integralClosure (P'.restrict k F).integers F' :=
    (algebraMap C F').codRestrict (integralClosure (P'.restrict k F).integers F')
      (algebraMap_mem_integralClosure_of_forall_mem_integers (P'.restrict k F) hB)
  have hcomp : P'.completionIntegersEmbedding.toRingHom.comp
      ((algebraMap C F').codRestrict P'.integers hC) =
        ((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl).comp fC :=
    RingHom.ext fun _ ↦ Subtype.ext (by simp [fC])
  rw [hcomp, ← Ideal.map_map,
    map_differentIdeal_eq_differentIdeal_of_isIntegralClosure (P'.restrict k F) hB]
  exact (P'.restrict k F).map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl

/-! ### Invariance of the different exponent and completed valuation criterion -/

/-- Extending a nonzero ideal of the local model `𝒪'_P` along
`completionIntegersIntegralClosureHom` preserves its multiplicity at the centre of `P'`. -/
@[simp]
theorem multiplicity_map_completionIntegersIntegralClosureHom
    (I : Ideal (integralClosure (P'.restrict k F).integers F')) (hI : I ≠ ⊥) :
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (I.map ((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl)) =
      multiplicity (centerIntegralClosure k F P').asIdeal I := by
  have hv : P'.valuation = (centerIntegralClosure k F P').valuation F' := by
    rw [centerIntegralClosure_def]
    exact (P'.valuation_center _).symm
  let p := centerIntegralClosure k F P'
  let e := completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k' F' p P' hv
  have hcomp : (e : P'.completionPlace.integers →+* p.adicCompletionIntegers F').comp
      ((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl) =
      algebraMap _ (p.adicCompletionIntegers F') :=
    RingHom.ext fun x ↦ Subtype.ext <| by
      simp only [RingHom.comp_apply, RingHom.coe_coe, e,
        completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply,
        coe_completionIntegersIntegralClosureHom,
        completionEquivAdicCompletionOfValuationEq_completionEmbedding,
        ← Subalgebra.algebraMap_apply]
      exact p.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (K := F') x
  have hem : emultiplicity (maximalIdeal P'.completionPlace.integers)
      (I.map ((P'.restrict k F).completionIntegersIntegralClosureHom P' rfl)) =
      emultiplicity (maximalIdeal (p.adicCompletionIntegers F'))
        (I.map (algebraMap _ (p.adicCompletionIntegers F'))) :=
    emultiplicity_eq_emultiplicity_iff.mpr fun n ↦ by
      simp only [Ideal.dvd_iff_le]
      rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, ← hcomp, ← Ideal.map_map, Ideal.map_coe]
      exact (Ideal.relIsoOfBijective e e.bijective).symm.le_iff_le.symm
  exact (multiplicity_eq_of_emultiplicity_eq hem).trans
    (p.multiplicity_map_adicCompletionIntegers I hI)

/-- **Completion preserves the different exponent**: the multiplicity of `𝔪̂_{P'}` in
`differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals `d(P' ∣ P)` (with arbitrary residue fields). -/
@[simp]
theorem multiplicity_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  subst hP
  rw [← (P'.restrict k F).map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl,
    P'.multiplicity_map_completionIntegersIntegralClosureHom _
      (differentIdeal_ne_bot_of_isSeparable (K := F) (L := F')),
    differentExponent_def]

/-- **The completed different ideal as a power of the maximal ideal**: with no hypothesis on the
residue fields, `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`. -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow :
    letI := P.completionIntegersExtensionAlgebra P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  rw [← P.multiplicity_differentIdeal_completionIntegers P' hP]
  exact (differentIdeal _ _).eq_maximalIdeal_pow_multiplicity
    (differentIdeal_ne_bot_of_isSeparable (R := P.completionPlace.integers)
      (K := P.Completion) (L := P'.Completion))

/-- **Completion preserves the place-level different exponent**: `d(P̂' ∣ P̂) = d(P' ∣ P)`. -/
@[simp]
theorem differentExponent_completionPlace [alg : Algebra k P'.Completion]
    [@IsScalarTower k k' P'.Completion _ (P'.instAlgebraCompletion).toSMul alg.toSMul]
    [@IsScalarTower k P.Completion P'.Completion
      (P.instAlgebraCompletion).toSMul (P.completionExtensionAlgebra P' hP).toSMul alg.toSMul] :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.finiteDimensional_completion P' hP
    haveI := P.isSeparable_completion P' hP
    differentExponent k P.Completion P'.completionPlace = differentExponent k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.property
  rw [differentExponent_eq_multiplicity_center (B := P.completionPlace.integers)
      (C := P'.completionPlace.integers) P'.completionPlace hC,
    P'.completionPlace.center_integers_asIdeal hC,
    P.multiplicity_differentIdeal_completionIntegers P' hP]

/-- **The valuation criterion for the completed complementary module**: `z ∈ F̂'_{P'}` has
`𝒪̂_P`-integral traces against `𝒪̂_{P'}` if and only if `v_{P̂'}(z) ≤ exp d(P' ∣ P)`. -/
theorem mem_traceDual_completionIntegers_iff_valuation_le {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  obtain ⟨π, hπ0, hπ⟩ := P'.completionPlace.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P'.completionPlace.integers :=
    P'.completionPlace.mem_integers_iff_ord_nonneg.mpr (by rw [hπ]; norm_num)
  have hδ : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {⟨π, hπint⟩ ^ differentExponent k F P'} := by
    rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP,
      (P'.completionPlace.irreducible_of_isUniformizer (t := ⟨π, hπint⟩)
        (P'.completionPlace.isUniformizer_iff_ord_eq_one.mpr hπ)).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have hvalπ : P'.completionPlace.valuation (π ^ differentExponent k F P') =
      WithZero.exp (-(differentExponent k F P' : ℤ)) := by
    rw [P'.completionPlace.valuation_eq_exp_neg_ord (pow_ne_zero _ hπ0),
      P'.completionPlace.ord_pow, hπ, mul_one]
  rw [mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ, ValuationSubring.algebraMap_apply,
    Submodule.mem_one, Subring.coe_pow]
  have hmem1 : (∃ b : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion b = z * π ^ differentExponent k F P') ↔
      P'.completionPlace.valuation (z * π ^ differentExponent k F P') ≤ 1 :=
    ⟨fun ⟨b, hb⟩ ↦ hb ▸ (P'.completionPlace.mem_integers_iff).mp b.property,
      fun h ↦ ⟨⟨_, (P'.completionPlace.mem_integers_iff).mpr h⟩, rfl⟩⟩
  rw [hmem1, map_mul, hvalπ]
  exact ⟨fun h ↦ by simpa [mul_assoc, ← WithZero.exp_add] using
      mul_le_mul_left h (WithZero.exp (differentExponent k F P' : ℤ)),
    fun h ↦ by simpa [← WithZero.exp_add] using
      mul_le_mul_left h (WithZero.exp (-(differentExponent k F P' : ℤ)))⟩

/-! ### Completed length and discriminant formulas (including fierce residue extensions) -/

/-- **Completed complementary-module length formula**: `length 𝒪̂_P (Ĉ_{P'} / 𝒪̂_{P'}) = d · f`,
where `f(P' ∣ P) = [κ(P') : κ(P)]` is the full relative residue degree including its inseparable
factor. -/
theorem length_traceDual_completionIntegers_quotient :
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
  have := (P'.restrict k F).finiteDimensional_completion P' rfl
  have := (P'.restrict k F).moduleFinite_completionIntegers P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  rw [TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- When `𝒪_{P'}` is the integral closure of `𝒪_P`, completion preserves the length of `C / 𝒪`. -/
theorem length_traceDual_completionIntegers_quotient_eq
    [IsIntegralClosure P'.integers (P'.restrict k F).integers F'] :
    letI := (P'.restrict k F).completionExtensionAlgebra P' rfl
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    Module.length (P'.restrict k F).completionPlace.integers
        ((Submodule.traceDual (P'.restrict k F).completionPlace.integers
            (P'.restrict k F).Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual (P'.restrict k F).completionPlace.integers
              (P'.restrict k F).Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      Module.length (P'.restrict k F).integers
        ((Submodule.traceDual (P'.restrict k F).integers F (1 : Submodule P'.integers F')) ⧸
          (1 : Submodule P'.integers F').comap
            (Submodule.traceDual (P'.restrict k F).integers F
              (1 : Submodule P'.integers F')).subtype) := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := isTorsionFree_integers (k := k) (F := F) P'
  have hC : ∀ c : P'.integers, algebraMap P'.integers F' c ∈ P'.integers := fun c ↦ c.property
  rw [(P'.restrict k F).length_traceDual_completionIntegers_quotient P' rfl,
    TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank,
    differentExponent_eq_multiplicity_center (B := (P'.restrict k F).integers) (C := P'.integers)
      P' hC, P'.center_integers_asIdeal hC, relativeDegree_def]

/-- **Length of the quotient by the completed different ideal**: the `𝒪̂_P`-length of
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
  have := P.finiteDimensional_completion P' hP
  have := P.moduleFinite_completionIntegers P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  rw [← TauCeti.length_traceDual_quotient_eq_length_quotient_differentIdeal
      (K := P.Completion) (L := P'.Completion),
    P.length_traceDual_completionIntegers_quotient P' hP]

/-- **Completed discriminant valuation formula**: `Ring.ord 𝒪̂_P (discr 𝒪̂_P b) = d · f`. -/
theorem ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  intro b
  rw [TauCeti.ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

omit [FiniteDimensional F F'] in
/-- When `𝒪_{P'}` is the integral closure of `𝒪_P`, completion preserves the discriminant ord. -/
theorem ord_discr_completionIntegers_eq
    [IsIntegralClosure P'.integers (P'.restrict k F).integers F']
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι (P'.restrict k F).integers P'.integers) :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    ∀ b' : Module.Basis ι' (P'.restrict k F).completionPlace.integers P'.completionPlace.integers,
      Ring.ord (P'.restrict k F).completionPlace.integers
          (Algebra.discr (P'.restrict k F).completionPlace.integers b') =
        Ring.ord (P'.restrict k F).integers (Algebra.discr (P'.restrict k F).integers b) := by
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have : Module.Finite (P'.restrict k F).integers P'.integers := .of_basis b
  have := IsIntegralClosure.isLocalization (P'.restrict k F).integers F F' P'.integers
  have : FiniteDimensional F F' :=
    .of_basis (b.localizationLocalization F (P'.restrict k F).integers⁰ F')
  have := isTorsionFree_integers (k := k) (F := F) P'
  have hC : ∀ c : P'.integers, algebraMap P'.integers F' c ∈ P'.integers := fun c ↦ c.property
  intro b'
  rw [(P'.restrict k F).ord_discr_completionIntegers P' rfl b',
    TauCeti.ord_discr_eq_multiplicity_mul_finrank F F' b,
    differentExponent_eq_multiplicity_center (B := (P'.restrict k F).integers) (C := P'.integers)
      P' hC, P'.center_integers_asIdeal hC, relativeDegree_def]

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
`TauCeti.Place.integralCompletionSemilocalEquiv` gives the product of the completed different ideals
above `P`. -/
theorem differentIdeal_integralCompletionSemilocal :
    ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (integralCompletionSemilocalEquiv k' F' P) =
      Ideal.pi fun w ↦
        differentIdeal P.completionPlace.integers w.val.completionPlace.integers :=
  (integralCompletionSemilocalEquiv k' F' P).map_differentIdeal_semilocal
    (fun w ↦ P.completionIntegersIntegralClosureHom w.val w.property)
    (fun a x w ↦ integralCompletionSemilocalEquiv_tmul a x w)
    fun w ↦ P.map_differentIdeal_eq_differentIdeal_completionIntegers w.val w.property

end Semilocal

end TauCeti.Place

end
