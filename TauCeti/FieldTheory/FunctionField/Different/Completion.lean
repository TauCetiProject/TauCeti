/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Localization
public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
import TauCeti.RingTheory.DedekindDomain.Different.Completion

/-!
# The trace-dual different of a place under completion

Let `P'` be a place of `F' / k'` lying over the place `P = P'.restrict k F` of `F / k`, with
`F' / F` finite and separable. No perfectness is assumed of `k` or `k'`, and no finiteness or
separability is assumed of the residue extension `F'_{P'} / F_P`. Passing to the completed
extension `F̂_P → F̂'_{P'}` (`TauCeti.Place.completionExtension`) with completed valuation rings
`𝒪̂_P ⊆ 𝒪̂_{P'}` preserves the trace-dual different and its complementary-module length formula:

* `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂'_{P'}`
  (`TauCeti.Place.isIntegralClosure_completionIntegers`), and `F̂'_{P'} / F̂_P` is separable
  (`TauCeti.Place.isSeparable_completion`);
* the completed complementary module `Submodule.traceDual 𝒪̂_P F̂_P 1` is spanned over `𝒪̂_{P'}` by
  the canonical image of the local-model complementary module `Submodule.traceDual 𝒪_P F 1`
  (`TauCeti.Place.traceDual_one_completionIntegers_eq_span`), and is characterized by the
  valuation bound `v_{P̂'}(z) ≤ exp d(P' ∣ P)`
  (`TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`);
* the completed different ideal `differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals `𝔪̂_{P'} ^ d(P' ∣ P)`, so its
  exponent at `𝔪̂_{P'}` is `d(P' ∣ P)`
  (`TauCeti.Place.differentIdeal_completionIntegers_eq_maximalIdeal_pow`,
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers`), and when the constant fields
  agree, `differentExponent k F̂_P P̂' = differentExponent k F P'`
  (`TauCeti.Place.differentExponent_completionPlace`);
* the `𝒪̂_P`-length of `Ĉ_{P'} ⧸ 𝒪̂_{P'}`, and `Ring.ord 𝒪̂_P` of the discriminant of any
  `𝒪̂_P`-basis of `𝒪̂_{P'}`, equal `d(P' ∣ P) · f(P' ∣ P)` with `f(P' ∣ P)` the full relative
  residue degree including its inseparable factor
  (`TauCeti.Place.length_traceDual_completionIntegers_quotient`,
  `TauCeti.Place.ord_discr_completionIntegers`); when `𝒪_{P'}` is already the integral closure of
  `𝒪_P` in `F'`, this length agrees literally with the uncompleted length of `C_P ⧸ 𝒪_{P'}` over
  `𝒪_P` (`TauCeti.Place.length_traceDual_completionIntegers_quotient_eq`).

## Proof strategy

We identify the intrinsic place completions at `P` and `P'` with the adic completions of `F` and
`F'` at the centres of `P` and `P'` on the local model `𝒪_P ⊆ 𝒪'_P` (following the valuation
transport pattern of `TauCeti.FieldTheory.FunctionField.Place.Completion.Adic`, without requiring a
`k'`-algebra structure on `𝒪'_P` when `k' ≠ k`), and transport the adic completion theorems of
`TauCeti.RingTheory.DedekindDomain.Different.Completion` across that continuous ring isomorphism.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3 and Chapter III, §§2–4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.7 and III.4–III.5.
-/

public section
noncomputable section

open IsDedekindDomain IsLocalRing
open scoped WithZero nonZeroDivisors

namespace TauCeti.Place

section Equiv

private theorem mem_traceDual_one_iff_of_equiv {A₁ K₁ B₁ L₁ A₂ K₂ B₂ L₂ : Type*}
    [CommRing A₁] [Field K₁] [CommRing B₁] [Field L₁]
    [Algebra A₁ K₁] [Algebra B₁ L₁] [Algebra A₁ B₁] [Algebra K₁ L₁] [Algebra A₁ L₁]
    [IsScalarTower A₁ K₁ L₁] [IsScalarTower A₁ B₁ L₁]
    [CommRing A₂] [Field K₂] [CommRing B₂] [Field L₂]
    [Algebra A₂ K₂] [Algebra B₂ L₂] [Algebra A₂ B₂] [Algebra K₂ L₂] [Algebra A₂ L₂]
    [IsScalarTower A₂ K₂ L₂] [IsScalarTower A₂ B₂ L₂]
    (eA : A₁ ≃+* A₂) (eK : K₁ ≃+* K₂) (eB : B₁ ≃+* B₂) (eL : L₁ ≃+* L₂)
    (hAK : ∀ a, eK (algebraMap A₁ K₁ a) = algebraMap A₂ K₂ (eA a))
    (hBL : ∀ b, eL (algebraMap B₁ L₁ b) = algebraMap B₂ L₂ (eB b))
    (hKL : (algebraMap K₂ L₂).comp eK.toRingHom = eL.toRingHom.comp (algebraMap K₁ L₁))
    (z : L₁) :
    z ∈ Submodule.traceDual A₁ K₁ (1 : Submodule B₁ L₁) ↔
      eL z ∈ Submodule.traceDual A₂ K₂ (1 : Submodule B₂ L₂) := by
  have htr (u : L₁) : eK (Algebra.trace K₁ L₁ u) = Algebra.trace K₂ L₂ (eL u) := by
    rw [Algebra.trace_eq_of_equiv_equiv eK eL hKL, RingEquiv.apply_symm_apply]
  have hrange (t : K₁) : t ∈ (algebraMap A₁ K₁).range ↔ eK t ∈ (algebraMap A₂ K₂).range :=
    ⟨fun ⟨a, ha⟩ ↦ ⟨eA a, by rw [← ha, hAK]⟩,
      fun ⟨a, ha⟩ ↦ ⟨eA.symm a, eK.injective (by rw [hAK, eA.apply_symm_apply, ha])⟩⟩
  simp only [Submodule.mem_traceDual, Submodule.mem_one, forall_exists_index,
    forall_apply_eq_imp_iff, Algebra.traceForm_apply]
  refine ⟨fun h b ↦ ?_, fun h b ↦ ?_⟩
  · have hb := (hrange _).mp (h (eB.symm b))
    rwa [htr, map_mul, hBL, eB.apply_symm_apply] at hb
  · exact (hrange _).mpr (by rw [htr, map_mul, hBL]; exact h (eB b))

private theorem mem_differentIdeal_iff_of_equiv {A₁ K₁ B₁ L₁ A₂ K₂ B₂ L₂ : Type*}
    [CommRing A₁] [IsDomain A₁] [IsIntegrallyClosed A₁] [Field K₁]
    [CommRing B₁] [IsDedekindDomain B₁] [Field L₁]
    [Algebra A₁ K₁] [IsFractionRing A₁ K₁] [Algebra B₁ L₁]
    [Algebra A₁ B₁] [Module.IsTorsionFree A₁ B₁] [Algebra K₁ L₁] [Algebra A₁ L₁]
    [IsScalarTower A₁ K₁ L₁] [IsScalarTower A₁ B₁ L₁]
    [IsIntegralClosure B₁ A₁ L₁] [FiniteDimensional K₁ L₁] [Algebra.IsSeparable K₁ L₁]
    [CommRing A₂] [IsDomain A₂] [IsIntegrallyClosed A₂] [Field K₂]
    [CommRing B₂] [IsDedekindDomain B₂] [Field L₂]
    [Algebra A₂ K₂] [IsFractionRing A₂ K₂] [Algebra B₂ L₂]
    [Algebra A₂ B₂] [Module.IsTorsionFree A₂ B₂] [Algebra K₂ L₂] [Algebra A₂ L₂]
    [IsScalarTower A₂ K₂ L₂] [IsScalarTower A₂ B₂ L₂]
    [IsIntegralClosure B₂ A₂ L₂] [FiniteDimensional K₂ L₂] [Algebra.IsSeparable K₂ L₂]
    (eA : A₁ ≃+* A₂) (eK : K₁ ≃+* K₂) (eB : B₁ ≃+* B₂) (eL : L₁ ≃+* L₂)
    (hAK : ∀ a, eK (algebraMap A₁ K₁ a) = algebraMap A₂ K₂ (eA a))
    (hBL : ∀ b, eL (algebraMap B₁ L₁ b) = algebraMap B₂ L₂ (eB b))
    (hKL : (algebraMap K₂ L₂).comp eK.toRingHom = eL.toRingHom.comp (algebraMap K₁ L₁))
    (y : B₁) :
    y ∈ differentIdeal A₁ B₁ ↔ eB y ∈ differentIdeal A₂ B₂ := by
  rw [mem_differentIdeal_iff_forall_mem_traceDual (K := K₁) (L := L₁),
    mem_differentIdeal_iff_forall_mem_traceDual (K := K₂) (L := L₂)]
  refine ⟨fun hy z' hz' ↦ ?_, fun hy z hz ↦ ?_⟩
  · have hz₁ : eL.symm z' ∈ Submodule.traceDual A₁ K₁ (1 : Submodule B₁ L₁) :=
      (mem_traceDual_one_iff_of_equiv eA eK eB eL hAK hBL hKL (eL.symm z')).mpr
        (by rwa [eL.apply_symm_apply])
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hy (eL.symm z') hz₁)
    refine Submodule.mem_one.mpr ⟨eB b, ?_⟩
    have hb' := congrArg eL hb
    rwa [hBL, map_mul, eL.apply_symm_apply, hBL] at hb'
  · have hz₂ : eL z ∈ Submodule.traceDual A₂ K₂ (1 : Submodule B₂ L₂) :=
      (mem_traceDual_one_iff_of_equiv eA eK eB eL hAK hBL hKL z).mp hz
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hy (eL z) hz₂)
    refine Submodule.mem_one.mpr ⟨eB.symm b, eL.injective ?_⟩
    rw [hBL, eB.apply_symm_apply, hb, map_mul, hBL]

private theorem symm_mem_span_image_of_mem_span_image {B₁ L₁ B₂ L₂ E : Type*}
    [CommRing B₁] [Field L₁] [Algebra B₁ L₁] [CommRing B₂] [Field L₂] [Algebra B₂ L₂]
    (eB : B₁ ≃+* B₂) (eL : L₁ ≃+* L₂) (f₁ : E → L₁) (f₂ : E → L₂) (S : Set E)
    (hBL : ∀ c : B₂, eL.symm (algebraMap B₂ L₂ c) = algebraMap B₁ L₁ (eB.symm c))
    (hf : ∀ d ∈ S, eL.symm (f₂ d) = f₁ d) {u : L₂}
    (hu : u ∈ Submodule.span B₂ (f₂ '' S)) :
    eL.symm u ∈ Submodule.span B₁ (f₁ '' S) := by
  refine Submodule.span_induction ?_ (by simp)
    (fun a b _ _ ha hb ↦ by rw [map_add]; exact add_mem ha hb)
    (fun c a _ ha ↦ ?_) hu
  · rintro _ ⟨d, hd, rfl⟩
    rw [hf d hd]
    exact Submodule.subset_span ⟨d, hd, rfl⟩
  · rw [Algebra.smul_def, map_mul, hBL, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ha

end Equiv

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section IntegralClosure

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- The valuation-ring extension `𝒪_P ⊆ 𝒪_{P'}` forms a scalar tower inside `F'`. -/
theorem isScalarTower_restrict_integers_field (P' : Place k' F') :
    IsScalarTower (P'.restrict k F).integers P'.integers F' :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (P'.restrict k F).integers F F',
      ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply, coe_algebraMap_integers]

/-- The completed valuation-ring extension forms a scalar tower inside the completed upper field. -/
theorem isScalarTower_completionIntegersExtensionAlgebra (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    P.algebraMap_completionExtensionAlgebra P' hP, ValuationSubring.algebraMap_apply,
    ValuationSubring.algebraMap_apply, P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP]

/-- The completed valuation ring `𝒪̂_{P'}` is torsion-free over `𝒪̂_P`. -/
theorem isTorsionFree_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b hab ↦ Subtype.ext ?_
  have hab' := congrArg Subtype.val hab
  rw [P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP,
    P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP] at hab'
  exact (P.completionExtension P' hP).injective hab'

/-- **The completed valuation ring `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂'_{P'}`**,
without any separability hypothesis on `F' / F` or on the residue extension. -/
theorem isIntegralClosure_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P)
    [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField] :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.moduleFinite_completionIntegers P' hP
  infer_instance

end IntegralClosure

section AdicBridge

-- Unlike `TauCeti.Place.completionEquivAdicCompletionOfValuationEq`, the upper Dedekind model
-- `integralClosure (P'.restrict k F).integers F'` need not be a `k'`-algebra when `k' ≠ k`, so we
-- transport along bare ring equivalences following `Place.Completion.Adic`.
private def completionRingEquivAdic {E A : Type*} [Field E] [CommRing A]
    [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (u : Valuation E ℤᵐ⁰) (p : HeightOneSpectrum A) (hu : u = p.valuation E) :
    u.Completion ≃+* p.adicCompletion E :=
  hu.symm ▸ (HeightOneSpectrum.adicCompletion.equiv E p).symm

private theorem completionRingEquivAdic_completionEmbedding {κ E A : Type*} [Field κ] [Field E]
    [Algebra κ E] [CommRing A] [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (Q : Place κ E) (p : HeightOneSpectrum A) (hQ : Q.valuation = p.valuation E) (x : E) :
    completionRingEquivAdic Q.valuation p hQ (Q.completionEmbedding x) =
      algebraMap E (p.adicCompletion E) x := by
  rw [Q.completionEmbedding_apply]
  generalize Q.valuation = u at hQ ⊢
  subst hQ
  rw [completionRingEquivAdic, RingEquiv.symm_apply_eq]
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

private theorem continuous_completionRingEquivAdic {E A : Type*} [Field E] [CommRing A]
    [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (u : Valuation E ℤᵐ⁰) (p : HeightOneSpectrum A) (hu : u = p.valuation E) :
    Continuous (completionRingEquivAdic u p hu) := by
  subst hu
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv E p).symm.continuous

private theorem continuous_completionRingEquivAdic_symm {E A : Type*} [Field E] [CommRing A]
    [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (u : Valuation E ℤᵐ⁰) (p : HeightOneSpectrum A) (hu : u = p.valuation E) :
    Continuous (completionRingEquivAdic u p hu).symm := by
  subst hu
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv E p).continuous

private theorem valued_completionRingEquivAdic {E A : Type*} [Field E] [CommRing A]
    [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (u : Valuation E ℤᵐ⁰) (p : HeightOneSpectrum A) (hu : u = p.valuation E) (z : u.Completion) :
    Valued.v (completionRingEquivAdic u p hu z) = Valued.v z := by
  subst hu
  exact HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply E p z

private def completionIntegersRingEquivAdic {κ E A : Type*} [Field κ] [Field E] [Algebra κ E]
    [CommRing A] [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (Q : Place κ E) (p : HeightOneSpectrum A) (hQ : Q.valuation = p.valuation E) :
    Q.completionPlace.integers ≃+* p.adicCompletionIntegers E :=
  (completionRingEquivAdic Q.valuation p hQ).restrict Q.completionPlace.integers
    (p.adicCompletionIntegers E) fun z ↦ by
      simp [HeightOneSpectrum.mem_adicCompletionIntegers, mem_integers_iff,
        valued_completionRingEquivAdic]

@[simp]
private theorem coe_completionIntegersRingEquivAdic {κ E A : Type*} [Field κ] [Field E]
    [Algebra κ E] [CommRing A] [IsDedekindDomain A] [Algebra A E] [IsFractionRing A E]
    (Q : Place κ E) (p : HeightOneSpectrum A) (hQ : Q.valuation = p.valuation E)
    (z : Q.completionPlace.integers) :
    (completionIntegersRingEquivAdic Q p hQ z : p.adicCompletion E) =
      completionRingEquivAdic Q.valuation p hQ z :=
  rfl

private theorem center_integers_asIdeal {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    (Q : Place κ E)
    (hC : ∀ c : Q.integers, algebraMap Q.integers E c ∈ Q.integers) :
    (Q.center hC).asIdeal = maximalIdeal Q.integers := by
  ext x
  rw [mem_center_asIdeal, ValuationSubring.algebraMap_apply, mem_maximalIdeal_iff_valuation_lt_one]

private theorem maximalIdeal_eq_span_of_ord_eq_one {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    (Q : Place κ E) {π : E} (hπ0 : π ≠ 0) (hπ : Q.ord π = 1) (hπint : π ∈ Q.integers) :
    maximalIdeal Q.integers = Ideal.span {⟨π, hπint⟩} := by
  refine le_antisymm (fun y hy ↦ Ideal.mem_span_singleton.mpr ?_)
    ((Ideal.span_singleton_le_iff_mem _).mpr
      ((Q.mem_maximalIdeal_iff_ord_pos hπ0).mpr (by rw [hπ]; exact zero_lt_one)))
  rcases eq_or_ne (y : E) 0 with hy0 | hy0
  · exact ⟨0, Subtype.ext (by simp [hy0])⟩
  · have hord := (Q.mem_maximalIdeal_iff_ord_pos hy0).mp hy
    have hdiv : (y : E) / π ∈ Q.integers := by
      rw [Q.mem_integers_iff_ord_nonneg, Q.ord_div hy0 hπ0, hπ]
      omega
    exact ⟨⟨_, hdiv⟩, Subtype.ext (by simp [mul_div_cancel₀ _ hπ0])⟩

end AdicBridge

section Different

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

private abbrev centerBase (P' : Place k' F') : HeightOneSpectrum (P'.restrict k F).integers :=
  (P'.restrict k F).center
    (algebraMap_mem_integers_restrict (R := (P'.restrict k F).integers) k F P'
      (algebraMap_mem_integers_of_mem_integralClosure k F P'))

private theorem centerIntegralClosure_liesOver_centerBase (P' : Place k' F') :
    (centerIntegralClosure k F P').asIdeal.LiesOver (centerBase (k := k) (F := F) P').asIdeal := by
  rw [centerIntegralClosure_def]
  exact center_liesOver k F P' (algebraMap_mem_integers_of_mem_integralClosure k F P')

omit [FiniteDimensional F F'] in
private theorem valuation_eq_centerBase (P' : Place k' F') :
    (P'.restrict k F).valuation = (centerBase (k := k) (F := F) P').valuation F :=
  ((P'.restrict k F).valuation_center _).symm

private theorem valuation_eq_centerIntegralClosure (P' : Place k' F') :
    P'.valuation = (centerIntegralClosure k F P').valuation F' := by
  rw [centerIntegralClosure_def]
  exact (P'.valuation_center _).symm

open scoped AdicCompletionExtension in
private theorem completionRingEquivAdic_completionExtension (P' : Place k' F')
    (x : (P'.restrict k F).Completion) :
    haveI := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
    completionRingEquivAdic P'.valuation (centerIntegralClosure k F P')
        (valuation_eq_centerIntegralClosure (k := k) (F := F) P')
        ((P'.restrict k F).completionExtension P' rfl x) =
      (centerBase (k := k) (F := F) P').adicCompletionExtension F F'
        (centerIntegralClosure k F P')
        (completionRingEquivAdic (P'.restrict k F).valuation (centerBase (k := k) (F := F) P')
          (valuation_eq_centerBase (k := k) (F := F) P') x) := by
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  let v := centerBase (k := k) (F := F) P'
  let w := centerIntegralClosure k F P'
  let hv := valuation_eq_centerBase (k := k) (F := F) P'
  let hw := valuation_eq_centerIntegralClosure (k := k) (F := F) P'
  let eK := completionRingEquivAdic (P'.restrict k F).valuation v hv
  let eL := completionRingEquivAdic P'.valuation w hw
  have hf : eL.symm.toRingHom.comp ((v.adicCompletionExtension F F' w).comp eK.toRingHom) =
      (P'.restrict k F).completionExtension P' rfl := by
    refine (P'.restrict k F).eq_completionExtension_of_continuous P' rfl
      ((continuous_completionRingEquivAdic_symm P'.valuation w hw).comp
        ((v.continuous_adicCompletionExtension F F' w).comp
          (continuous_completionRingEquivAdic (P'.restrict k F).valuation v hv))) fun y ↦ ?_
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply,
      eK, eL, completionRingEquivAdic_completionEmbedding]
    rw [RingEquiv.symm_apply_eq, completionRingEquivAdic_completionEmbedding]
    simp [HeightOneSpectrum.algebraMap_adicCompletion,
      HeightOneSpectrum.adicCompletionExtension_coe]
  exact ((RingEquiv.symm_apply_eq eL).mp (congrArg (fun g : _ →+* _ ↦ g x) hf)).symm

open scoped AdicCompletionExtension in
private theorem algebraMap_comp_completionRingEquivAdic (P' : Place k' F') :
    letI := (P'.restrict k F).completionExtensionAlgebra P' rfl
    haveI := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
    (algebraMap ((centerBase (k := k) (F := F) P').adicCompletion F)
        ((centerIntegralClosure k F P').adicCompletion F')).comp
      (completionRingEquivAdic (P'.restrict k F).valuation (centerBase (k := k) (F := F) P')
        (valuation_eq_centerBase (k := k) (F := F) P')).toRingHom =
      (completionRingEquivAdic P'.valuation (centerIntegralClosure k F P')
        (valuation_eq_centerIntegralClosure (k := k) (F := F) P')).toRingHom.comp
        (algebraMap (P'.restrict k F).Completion P'.Completion) := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  refine RingHom.ext fun x ↦ ?_
  dsimp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [(P'.restrict k F).algebraMap_completionExtensionAlgebra P' rfl,
    (centerBase (k := k) (F := F) P').algebraMap_adicCompletionExtensionAlgebra F F'
      (centerIntegralClosure k F P')]
  exact (completionRingEquivAdic_completionExtension P' x).symm

/-- **Completion preserves separability of the field extension**, with no separability or
finiteness hypothesis on the residue fields. -/
theorem isSeparable_completion (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion := by
  subst hP
  open scoped AdicCompletionExtension in
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let v := centerBase (k := k) (F := F) P'
  let w := centerIntegralClosure k F P'
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  have : Module.Finite (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F') :=
    IsIntegralClosure.finite (P'.restrict k F).integers F F' _
  have := v.isSeparable_adicCompletion_of_isSeparable (K := F)
    (B := integralClosure (P'.restrict k F).integers F') (L := F') w
  let eK := completionRingEquivAdic (P'.restrict k F).valuation v
    (valuation_eq_centerBase (k := k) (F := F) P')
  let eL := completionRingEquivAdic P'.valuation w
    (valuation_eq_centerIntegralClosure (k := k) (F := F) P')
  refine (Algebra.IsSeparable.iff_of_equiv_equiv eK eL
    (algebraMap_comp_completionRingEquivAdic P')).mpr inferInstance

open scoped AdicCompletionExtension in
private theorem mem_traceDual_completionIntegers_iff_adic (P' : Place k' F') (z : P'.Completion) :
    letI := (P'.restrict k F).completionExtensionAlgebra P' rfl
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    haveI := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
    haveI := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
    z ∈ Submodule.traceDual (P'.restrict k F).completionPlace.integers
        (P'.restrict k F).Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      completionRingEquivAdic P'.valuation (centerIntegralClosure k F P')
          (valuation_eq_centerIntegralClosure (k := k) (F := F) P') z ∈
        Submodule.traceDual ((centerBase (k := k) (F := F) P').adicCompletionIntegers F)
          ((centerBase (k := k) (F := F) P').adicCompletion F)
          (1 : Submodule ((centerIntegralClosure k F P').adicCompletionIntegers F')
            ((centerIntegralClosure k F P').adicCompletion F')) := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  exact mem_traceDual_one_iff_of_equiv
    (completionIntegersRingEquivAdic (P'.restrict k F) _ (valuation_eq_centerBase P'))
    (completionRingEquivAdic (P'.restrict k F).valuation _ (valuation_eq_centerBase P'))
    (completionIntegersRingEquivAdic P' _ (valuation_eq_centerIntegralClosure P'))
    (completionRingEquivAdic P'.valuation _ (valuation_eq_centerIntegralClosure P'))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (algebraMap_comp_completionRingEquivAdic P') z

/-- **The completed complementary module is generated by the local-model complementary module**,
with no hypothesis on the residue fields. -/
theorem traceDual_one_completionIntegers_eq_span (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) =
      Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F')) := by
  subst hP
  open scoped AdicCompletionExtension in
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  let v := centerBase (k := k) (F := F) P'
  let w := centerIntegralClosure k F P'
  let hw := valuation_eq_centerIntegralClosure (k := k) (F := F) P'
  let eB := completionIntegersRingEquivAdic P' w hw
  let eL := completionRingEquivAdic P'.valuation w hw
  have hspan := v.traceDual_one_adicCompletionIntegers_eq_span (K := F)
    (B := integralClosure (P'.restrict k F).integers F') (L := F') w
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.mpr ?_)
  · have hz' : eL z ∈ Submodule.span (w.adicCompletionIntegers F')
        (algebraMap F' (w.adicCompletion F') ''
          Submodule.traceDual (P'.restrict k F).integers F
            (1 : Submodule (integralClosure (P'.restrict k F).integers F') F')) :=
      hspan ▸ (mem_traceDual_completionIntegers_iff_adic P' z).mp hz
    simpa only [eL.symm_apply_apply] using symm_mem_span_image_of_mem_span_image eB eL
      P'.completionEmbedding (algebraMap F' (w.adicCompletion F')) _ (fun _ ↦ rfl)
      (fun d _ ↦ (RingEquiv.symm_apply_eq eL).mpr
        (completionRingEquivAdic_completionEmbedding P' w hw d).symm) hz'
  · rintro _ ⟨d, hd, rfl⟩
    rw [SetLike.mem_coe, mem_traceDual_completionIntegers_iff_adic P',
      completionRingEquivAdic_completionEmbedding P' w hw, hspan]
    exact Submodule.subset_span ⟨d, hd, rfl⟩

/-- **The completed different ideal as a power of the maximal ideal**: with no hypothesis on the
residue fields, `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`. -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  open scoped AdicCompletionExtension in
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).finiteDimensional_completion P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  let v := centerBase (k := k) (F := F) P'
  let w := centerIntegralClosure k F P'
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  have : Module.Finite (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F') :=
    IsIntegralClosure.finite (P'.restrict k F).integers F F' _
  have := v.finiteDimensional_adicCompletion_of_finite (K := F)
    (B := integralClosure (P'.restrict k F).integers F') (L := F') w
  have := v.isIntegralClosure_adicCompletionIntegers_of_finite (K := F)
    (B := integralClosure (P'.restrict k F).integers F') (L := F') w
  have := v.isSeparable_adicCompletion_of_isSeparable (K := F)
    (B := integralClosure (P'.restrict k F).integers F') (L := F') w
  let eB := completionIntegersRingEquivAdic P' w (valuation_eq_centerIntegralClosure P')
  ext y
  rw [mem_differentIdeal_iff_of_equiv
      (completionIntegersRingEquivAdic (P'.restrict k F) v (valuation_eq_centerBase P'))
      (completionRingEquivAdic (P'.restrict k F).valuation v (valuation_eq_centerBase P'))
      eB (completionRingEquivAdic P'.valuation w (valuation_eq_centerIntegralClosure P'))
      (fun _ ↦ rfl) (fun _ ↦ rfl) (algebraMap_comp_completionRingEquivAdic P') y,
    v.differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow (K := F)
      (B := integralClosure (P'.restrict k F).integers F') (L := F') w, ← differentExponent_def,
    ← IsLocalRing.map_ringEquiv_maximalIdeal eB, ← Ideal.map_pow]
  exact ⟨fun hy ↦ by
      obtain ⟨a, ha, hay⟩ := (Ideal.mem_map_iff_of_surjective _ eB.surjective).mp hy
      exact eB.injective hay ▸ ha,
    fun hy ↦ Ideal.mem_map_of_mem _ hy⟩

/-- **Completion preserves the different exponent**: the multiplicity of `𝔪̂_{P'}` in
`differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals `d(P' ∣ P)`, with no separability hypothesis on the residue
fields. -/
@[simp]
theorem multiplicity_differentIdeal_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isTorsionFree_completionIntegers P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP]
  exact multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field P'.completionPlace.integers)
      inferInstance) _

/-- **The valuation criterion for the completed complementary module**: `z ∈ F̂'_{P'}` has
`𝒪̂_P`-integral traces against `𝒪̂_{P'}` if and only if `v_{P̂'}(z) ≤ exp d(P' ∣ P)`. -/
theorem mem_traceDual_completionIntegers_iff_valuation_le (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  obtain ⟨π, hπ0, hπ⟩ := P'.completionPlace.exists_ne_zero_ord_eq 1
  have hπint : π ∈ P'.completionPlace.integers :=
    P'.completionPlace.mem_integers_iff_ord_nonneg.mpr (by rw [hπ]; norm_num)
  have hδ : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {⟨π, hπint⟩ ^ differentExponent k F P'} := by
    rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP,
      maximalIdeal_eq_span_of_ord_eq_one P'.completionPlace hπ0 hπ hπint, Ideal.span_singleton_pow]
  have hvalπ : P'.completionPlace.valuation (π ^ differentExponent k F P') =
      WithZero.exp (-(differentExponent k F P' : ℤ)) := by
    rw [P'.completionPlace.valuation_eq_exp_neg_ord (pow_ne_zero _ hπ0),
      P'.completionPlace.ord_pow, hπ, mul_one]
  rw [mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ, ValuationSubring.algebraMap_apply,
    Submodule.mem_one, Subring.coe_pow]
  have hmem1 : (∃ b : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion b = z * π ^ differentExponent k F P') ↔
      P'.completionPlace.valuation (z * π ^ differentExponent k F P') ≤ 1 := by
    rw [← P'.completionPlace.mem_integers_iff]
    exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.2, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  rw [hmem1, map_mul, hvalπ]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc P'.completionPlace.valuation z
        = P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ)) *
            WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
      _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _
  · calc P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ))
        ≤ WithZero.exp (differentExponent k F P' : ℤ) *
            WithZero.exp (-(differentExponent k F P' : ℤ)) := by gcongr
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-- **The completed complementary-module length formula**, with no separability hypothesis on the
residue fields: the `𝒪̂_P`-length of `Ĉ_{P'} ⧸ 𝒪̂_{P'}` equals `d(P' ∣ P) · f(P' ∣ P)`, where
`f(P' ∣ P)` is the full relative residue degree including its inseparable factor. -/
theorem length_traceDual_completionIntegers_quotient (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
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
  have := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).finiteDimensional_completion P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  have : Module.Finite (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField :=
    Module.Finite.of_equiv_equiv (P'.restrict k F).residueFieldEquivCompletion.toRingEquiv
      P'.residueFieldEquivCompletion.toRingEquiv
      (P'.algebraMap_comp_residueFieldEquivCompletion (k := k) (F := F))
  rw [length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

/-- **When `𝒪_{P'}` is already the integral closure of `𝒪_P` in `F'`, completion preserves the
complementary-module length**, even when the residue extension is inseparable. -/
theorem length_traceDual_completionIntegers_quotient_eq (P' : Place k' F')
    [IsIntegralClosure P'.integers (P'.restrict k F).integers F'] :
    letI := (P'.restrict k F).completionExtensionAlgebra P' rfl
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    haveI := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
    haveI := isScalarTower_restrict_integers_field (k := k) (F := F) P'
    Module.length (P'.restrict k F).completionPlace.integers
        ((Submodule.traceDual (P'.restrict k F).completionPlace.integers
            (P'.restrict k F).Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual (P'.restrict k F).completionPlace.integers
              (P'.restrict k F).Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      Module.length (P'.restrict k F).integers
        ((Submodule.traceDual (P'.restrict k F).integers F
            (1 : Submodule P'.integers F')) ⧸
          (1 : Submodule P'.integers F').comap
            (Submodule.traceDual (P'.restrict k F).integers F
              (1 : Submodule P'.integers F')).subtype) := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := isScalarTower_restrict_integers_field (k := k) (F := F) P'
  have : Module.IsTorsionFree (P'.restrict k F).integers P'.integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b hab ↦ Subtype.ext <|
      (algebraMap F F').injective <| by
        simpa [coe_algebraMap_integers] using congrArg Subtype.val hab
  have hC : ∀ c : P'.integers, algebraMap P'.integers F' c ∈ P'.integers := fun c ↦ c.2
  rw [(P'.restrict k F).length_traceDual_completionIntegers_quotient P' rfl,
    length_traceDual_quotient_eq_multiplicity_mul_finrank,
    differentExponent_eq_multiplicity_center (B := (P'.restrict k F).integers) (C := P'.integers)
      P' hC, center_integers_asIdeal P' hC, relativeDegree_def]

/-- **The completed discriminant valuation formula**, with no separability hypothesis on the
residue fields: for any `𝒪̂_P`-basis `b` of `𝒪̂_{P'}`, `Ring.ord 𝒪̂_P (discr 𝒪̂_P b)` equals
`d(P' ∣ P) · f(P' ∣ P)`. -/
theorem ord_discr_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Module.Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isTorsionFree_completionIntegers P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  intro b
  rw [ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

end Different

section Constants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- For extensions over the same constant field `k`, the completed upper place restricts to the
completed lower place. -/
@[simp]
theorem restrict_completionPlace [FiniteDimensional F F'] (P : Place k F) (P' : Place k F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI : Algebra.IsIntegral P.Completion P'.Completion :=
      letI := P.completionExtensionAlgebra P' hP
      haveI := P.finiteDimensional_completion P' hP
      Algebra.IsIntegral.of_finite P.Completion P'.Completion
    P'.completionPlace.restrict k P.Completion = P.completionPlace := by
  let _ := P.completionExtensionAlgebra P' hP
  have := P.isScalarTower_completionExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  have : Algebra.IsIntegral P.Completion P'.Completion :=
    Algebra.IsIntegral.of_finite P.Completion P'.Completion
  refine (restrict_eq_iff_integers_le k P.Completion P'.completionPlace P.completionPlace).mpr
    fun x hx ↦ ?_
  rw [P.algebraMap_completionExtensionAlgebra P' hP]
  exact P.completionExtension_mem_integers P' hP hx

/-- **Completing an extension over `k` preserves `TauCeti.Place.differentExponent`**, with no
perfectness hypothesis on `k` and no separability hypothesis on the residue fields. -/
@[simp]
theorem differentExponent_completionPlace [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (P : Place k F) (P' : Place k F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI := P.finiteDimensional_completion P' hP
    haveI := P.isSeparable_completion P' hP
    differentExponent k P.Completion P'.completionPlace = differentExponent k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtensionAlgebra P' hP
  have := P.isTorsionFree_completionIntegers P' hP
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  rw [differentExponent_eq_multiplicity_center (B := P.completionPlace.integers)
      (C := P'.completionPlace.integers) P'.completionPlace hC,
    center_integers_asIdeal P'.completionPlace hC,
    P.multiplicity_differentIdeal_completionIntegers P' hP]

end Constants

end TauCeti.Place

end
