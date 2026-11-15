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
import TauCeti.FieldTheory.FunctionField.Place.Completion.Adic
import TauCeti.RingTheory.DedekindDomain.Different.Completion

/-!
# The trace-dual different of a place under completion

Let `P'` be a place of `F' / k'` lying over the place `P = P'.restrict k F` of `F / k`, with
`F' / F` finite and separable. No perfectness is assumed of `k` or `k'`, no finiteness is assumed
of the residue fields `F_P` and `F'_{P'}`, and no separability is assumed of the residue extension
`F'_{P'} / F_P`. Passing to the completed extension `F̂_P → F̂'_{P'}`
(`TauCeti.Place.completionExtension`) with completed valuation rings `𝒪̂_P ⊆ 𝒪̂_{P'}` reduces local
ramification, complementary-module, and discriminant calculations on function fields (including
wild or residue-inseparable extensions where `𝒪_{P'}` need not be monogenic over `𝒪_P` and the
completed valuation rings need not be compact) to complete discrete valuation rings, where explicit
uniformizer expansions and local Galois theory apply.

Because different places above `P` induce distinct completed extensions and valuation-ring actions,
callers working with the theorems below install the local algebra structures
`TauCeti.Place.completionExtensionAlgebra` and `TauCeti.Place.completionIntegersExtensionAlgebra`
(as `letI` / `let _`), and install `TauCeti.Place.algebraIntegersExtension` and
`TauCeti.Place.isScalarTowerIntegersExtension` with `attribute [local instance 10]` when referring
to the uncompleted local model `𝒪_P ⊆ 𝒪'_P`. The compatible scalar-tower and torsion-freeness
instances (`TauCeti.Place.isScalarTower_completionIntegersExtensionAlgebra`,
`TauCeti.Place.isTorsionFree_completionIntegers`, and
`TauCeti.Place.isScalarTower_restrict_integers_field`) are then synthesized automatically.

## Main results

* `TauCeti.Place.traceDual_one_completionIntegers_eq_span` and
  `TauCeti.Place.mem_traceDual_completionIntegers_iff_valuation_le`: the completed complementary
  module `Submodule.traceDual 𝒪̂_P F̂_P 1` is spanned over `𝒪̂_{P'}` by the canonical image of the
  local-model complementary module `Submodule.traceDual 𝒪_P F 1`, and is characterized by the
  valuation bound `v_{P̂'}(z) ≤ exp d(P' ∣ P)`.
* `TauCeti.Place.differentIdeal_completionIntegers_eq_maximalIdeal_pow`,
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers`, and
  `TauCeti.Place.differentExponent_completionPlace`:
  `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`,
  its multiplicity at `𝔪̂_{P'}` is `d(P' ∣ P)`, and when the constant fields agree,
  `differentExponent k F̂_P P̂' = differentExponent k F P'`.
* `TauCeti.Place.length_traceDual_completionIntegers_quotient` and
  `TauCeti.Place.ord_discr_completionIntegers`: the `𝒪̂_P`-length of `Ĉ_{P'} ⧸ 𝒪̂_{P'}` and
  `Ring.ord 𝒪̂_P` of the discriminant of any `𝒪̂_P`-basis of `𝒪̂_{P'}` equal
  `d(P' ∣ P) · f(P' ∣ P)` with `f(P' ∣ P)` the full relative residue degree (including its
  inseparable factor).
* `TauCeti.Place.length_traceDual_completionIntegers_quotient_eq` and
  `TauCeti.Place.ord_discr_completionIntegers_eq`: when `𝒪_{P'}` is already the integral closure of
  `𝒪_P` in `F'`, both invariants agree literally with their uncompleted counterparts over `𝒪_P`.

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
private theorem mem_traceDual_completionIntegers_iff_adic (P' : Place k' F') (z : P'.Completion) :
    letI := (P'.restrict k F).completionExtensionAlgebra P' rfl
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    haveI := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
    z ∈ Submodule.traceDual (P'.restrict k F).completionPlace.integers
        (P'.restrict k F).Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      completionEquivAdicCompletionOfValuationEq k' F' (centerIntegralClosure k F P') P'
          (valuation_eq_centerIntegralClosure (k := k) (F := F) P') z ∈
        Submodule.traceDual ((centerBase (k := k) (F := F) P').adicCompletionIntegers F)
          ((centerBase (k := k) (F := F) P').adicCompletion F)
          (1 : Submodule ((centerIntegralClosure k F P').adicCompletionIntegers F')
            ((centerIntegralClosure k F P').adicCompletion F')) := by
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  exact TauCeti.mem_traceDual_one_iff_of_equiv
    (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F _ (P'.restrict k F)
      (valuation_eq_centerBase P'))
    (completionEquivAdicCompletionOfValuationEq k F _ (P'.restrict k F)
      (valuation_eq_centerBase P')).toAlgEquiv.toRingEquiv
    (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k' F' _ P'
      (valuation_eq_centerIntegralClosure P'))
    (completionEquivAdicCompletionOfValuationEq k' F' _ P'
      (valuation_eq_centerIntegralClosure P')).toAlgEquiv.toRingEquiv
    (fun a ↦ (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply k F _
      (P'.restrict k F) (valuation_eq_centerBase P') a).symm)
    (fun b ↦ (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply k' F' _ P'
      (valuation_eq_centerIntegralClosure P') b).symm)
    (algebraMap_comp_completionEquivAdicCompletionOfValuationEq (centerBase P')
      (centerIntegralClosure k F P') (P'.restrict k F) P' rfl
      (valuation_eq_centerBase P') (valuation_eq_centerIntegralClosure P')) z

/-- **The completed complementary module is generated by the local-model complementary module**,
with no hypothesis on the residue fields. -/
theorem traceDual_one_completionIntegers_eq_span (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
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
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  let v := centerBase (k := k) (F := F) P'
  let w := centerIntegralClosure k F P'
  let hw := valuation_eq_centerIntegralClosure (k := k) (F := F) P'
  let eB := completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k' F' w P' hw
  let eL := (completionEquivAdicCompletionOfValuationEq k' F' w P' hw).toAlgEquiv.toRingEquiv
  have hspan := v.traceDual_one_adicCompletionIntegers_eq_span (K := F)
    (B := integralClosure (P'.restrict k F).integers F') (L := F') w
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.mpr ?_)
  · have hz' : eL z ∈ Submodule.span (w.adicCompletionIntegers F')
        (algebraMap F' (w.adicCompletion F') ''
          Submodule.traceDual (P'.restrict k F).integers F
            (1 : Submodule (integralClosure (P'.restrict k F).integers F') F')) :=
      hspan ▸ (mem_traceDual_completionIntegers_iff_adic P' z).mp hz
    suffices ∀ u ∈ Submodule.span (w.adicCompletionIntegers F')
        (algebraMap F' (w.adicCompletion F') ''
          Submodule.traceDual (P'.restrict k F).integers F
            (1 : Submodule (integralClosure (P'.restrict k F).integers F') F')),
        eL.symm u ∈ Submodule.span P'.completionPlace.integers
          (P'.completionEmbedding ''
            Submodule.traceDual (P'.restrict k F).integers F
              (1 : Submodule (integralClosure (P'.restrict k F).integers F') F')) by
      simpa only [eL.symm_apply_apply] using this (eL z) hz'
    intro u hu
    refine Submodule.span_induction (fun _ hx ↦ ?_)
      (by rw [map_zero]; exact zero_mem _)
      (fun x y _ _ hx hy ↦ by rw [map_add]; exact add_mem hx hy)
      (fun c x _ hx ↦ ?_) hu
    · rcases hx with ⟨d, hd, rfl⟩
      have hd' : eL.symm (algebraMap F' (w.adicCompletion F') d) = P'.completionEmbedding d :=
        (eL.symm_apply_eq).mpr
          (completionEquivAdicCompletionOfValuationEq_completionEmbedding k' F' w P' hw d).symm
      rw [hd']
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · have hc : (eB.symm c : P'.Completion) = eL.symm (c : w.adicCompletion F') := by
        apply eL.injective
        rw [eL.apply_symm_apply]
        exact (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply k' F' w P'
          hw (eB.symm c)).symm.trans (congrArg Subtype.val (eB.apply_symm_apply c))
      have hsmul : eL.symm (c • x) = eB.symm c • eL.symm x := by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def,
          ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply, hc]
      rw [hsmul]
      exact Submodule.smul_mem _ (eB.symm c) hx
  · rintro _ ⟨d, hd, rfl⟩
    refine (mem_traceDual_completionIntegers_iff_adic P' (P'.completionEmbedding d)).mpr ?_
    rw [completionEquivAdicCompletionOfValuationEq_completionEmbedding k' F' w P' hw d, hspan]
    exact Submodule.subset_span ⟨d, hd, rfl⟩

/-- **The completed different ideal as a power of the maximal ideal**: with no hypothesis on the
residue fields, `differentIdeal 𝒪̂_P 𝒪̂_{P'} = 𝔪̂_{P'} ^ d(P' ∣ P)`. -/
theorem differentIdeal_completionIntegers_eq_maximalIdeal_pow (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  open scoped AdicCompletionExtension in
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).finiteDimensional_completion P' rfl
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  let v := centerBase (k := k) (F := F) P'
  let w := centerIntegralClosure k F P'
  have := centerIntegralClosure_liesOver_centerBase (k := k) (F := F) P'
  have : Module.Finite (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F') :=
    IsIntegralClosure.finite (P'.restrict k F).integers F F' _
  let hv := valuation_eq_centerBase (k := k) (F := F) P'
  let hw := valuation_eq_centerIntegralClosure (k := k) (F := F) P'
  let eA := completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k F v
    (P'.restrict k F) hv
  let eK := (completionEquivAdicCompletionOfValuationEq k F v
    (P'.restrict k F) hv).toAlgEquiv.toRingEquiv
  let eB := completionIntegersRingEquivAdicCompletionIntegersOfValuationEq k' F' w P' hw
  let eL := (completionEquivAdicCompletionOfValuationEq k' F' w P' hw).toAlgEquiv.toRingEquiv
  have hAK (a : v.adicCompletionIntegers F) :
      eK.symm (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) a) =
        algebraMap (P'.restrict k F).completionPlace.integers (P'.restrict k F).Completion
          (eA.symm a) := by
    apply eK.injective
    rw [eK.apply_symm_apply, ValuationSubring.algebraMap_apply]
    exact (congrArg Subtype.val (eA.apply_symm_apply a)).symm.trans
      (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply k F v
        (P'.restrict k F) hv (eA.symm a))
  have hBL (b : w.adicCompletionIntegers F') :
      eL.symm (algebraMap (w.adicCompletionIntegers F') (w.adicCompletion F') b) =
        algebraMap P'.completionPlace.integers P'.Completion (eB.symm b) := by
    apply eL.injective
    rw [eL.apply_symm_apply, ValuationSubring.algebraMap_apply]
    exact (congrArg Subtype.val (eB.apply_symm_apply b)).symm.trans
      (completionIntegersRingEquivAdicCompletionIntegersOfValuationEq_apply k' F' w P' hw
        (eB.symm b))
  have hKL : (algebraMap (P'.restrict k F).Completion P'.Completion).comp eK.symm.toRingHom =
      eL.symm.toRingHom.comp (algebraMap (v.adicCompletion F) (w.adicCompletion F')) := by
    refine RingHom.ext fun x ↦ eL.injective ?_
    have hnat := RingHom.congr_fun
      (algebraMap_comp_completionEquivAdicCompletionOfValuationEq v w (P'.restrict k F) P' rfl
        hv hw) (eK.symm x)
    dsimp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
      ContinuousAlgEquiv.coe_toAlgEquiv, RingHom.coe_coe] at hnat ⊢
    rw [eL.apply_symm_apply]
    exact hnat.symm.trans (congrArg _ (eK.apply_symm_apply x))
  have hmax : (maximalIdeal (w.adicCompletionIntegers F')).map (eB.symm : _ →+* _) =
      maximalIdeal P'.completionPlace.integers :=
    IsLocalRing.map_maximalIdeal_of_surjective eB.symm.toRingHom (by simpa using eB.symm.surjective)
  rw [← TauCeti.map_differentIdeal_of_equiv eA.symm eK.symm eB.symm eL.symm hAK hBL hKL,
    v.differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow (K := F)
      (B := integralClosure (P'.restrict k F).integers F') (L := F') w,
    Ideal.map_pow, hmax, ← differentExponent_def]

/-- **Completion preserves the different exponent**: the multiplicity of `𝔪̂_{P'}` in
`differentIdeal 𝒪̂_P 𝒪̂_{P'}` equals `d(P' ∣ P)`, with no separability hypothesis on the residue
fields. -/
@[simp]
theorem multiplicity_differentIdeal_completionIntegers (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
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
  have hπ_irr : Irreducible (⟨π, hπint⟩ : P'.completionPlace.integers) :=
    P'.completionPlace.irreducible_of_isUniformizer
      (P'.completionPlace.isUniformizer_iff_ord_eq_one.mpr hπ)
  have hδ : differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      Ideal.span {⟨π, hπint⟩ ^ differentExponent k F P'} := by
    rw [P.differentIdeal_completionIntegers_eq_maximalIdeal_pow P' hP, hπ_irr.maximalIdeal_eq,
      Ideal.span_singleton_pow]
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
  have : Module.IsTorsionFree (P'.restrict k F).integers P'.integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b hab ↦ Subtype.ext <|
      (algebraMap F F').injective <| by
        simpa [coe_algebraMap_integers] using congrArg Subtype.val hab
  have hC : ∀ c : P'.integers, algebraMap P'.integers F' c ∈ P'.integers := fun c ↦ c.2
  rw [(P'.restrict k F).length_traceDual_completionIntegers_quotient P' rfl,
    length_traceDual_quotient_eq_multiplicity_mul_finrank,
    differentExponent_eq_multiplicity_center (B := (P'.restrict k F).integers) (C := P'.integers)
      P' hC, P'.center_integers_asIdeal hC, relativeDegree_def]

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
  have := (P'.restrict k F).isIntegralClosure_completionIntegers P' rfl
  have := (P'.restrict k F).isSeparable_completion P' rfl
  intro b
  rw [ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl,
    P'.finrank_residueField_completion (k := k) (F := F)]

omit [FiniteDimensional F F'] in
/-- **When `𝒪_{P'}` is already the integral closure of `𝒪_P` in `F'`, completion preserves the
discriminant valuation**, with no separability hypothesis on the residue fields. -/
theorem ord_discr_completionIntegers_eq (P' : Place k' F')
    [IsIntegralClosure P'.integers (P'.restrict k F).integers F']
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι (P'.restrict k F).integers P'.integers) :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    ∀ b' : Module.Basis ι' (P'.restrict k F).completionPlace.integers P'.completionPlace.integers,
      Ring.ord (P'.restrict k F).completionPlace.integers
          (Algebra.discr (P'.restrict k F).completionPlace.integers b') =
        Ring.ord (P'.restrict k F).integers (Algebra.discr (P'.restrict k F).integers b) := by
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have : Module.IsTorsionFree (P'.restrict k F).integers P'.integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b hab ↦ Subtype.ext <|
      (algebraMap F F').injective <| by
        simpa [coe_algebraMap_integers] using congrArg Subtype.val hab
  have : Module.Finite (P'.restrict k F).integers P'.integers := .of_basis b
  have := IsIntegralClosure.isLocalization (P'.restrict k F).integers F F' P'.integers
  have : FiniteDimensional F F' :=
    .of_basis (b.localizationLocalization F (P'.restrict k F).integers⁰ F')
  have hC : ∀ c : P'.integers, algebraMap P'.integers F' c ∈ P'.integers := fun c ↦ c.2
  intro b'
  rw [(P'.restrict k F).ord_discr_completionIntegers P' rfl b',
    ord_discr_eq_multiplicity_mul_finrank F F' b,
    differentExponent_eq_multiplicity_center (B := (P'.restrict k F).integers) (C := P'.integers)
      P' hC, P'.center_integers_asIdeal hC, relativeDegree_def]

end Different

section Constants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

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
  have := P.finiteDimensional_completion P' hP
  have := P.isIntegralClosure_completionIntegers P' hP
  have := P.isSeparable_completion P' hP
  have hC : ∀ c : P'.completionPlace.integers,
      algebraMap P'.completionPlace.integers P'.Completion c ∈ P'.completionPlace.integers :=
    fun c ↦ c.2
  rw [differentExponent_eq_multiplicity_center (B := P.completionPlace.integers)
      (C := P'.completionPlace.integers) P'.completionPlace hC,
    P'.completionPlace.center_integers_asIdeal hC,
    P.multiplicity_differentIdeal_completionIntegers P' hP]

end Constants

end TauCeti.Place

end
