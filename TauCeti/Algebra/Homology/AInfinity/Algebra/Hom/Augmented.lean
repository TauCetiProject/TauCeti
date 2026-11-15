/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict

/-!
# Augmented morphisms of `A∞` algebras and restriction to augmentation ideals

An `A∞` morphism `f : A ⟶ B` between augmented `A∞` algebras `(A, ε_A)` and `(B, ε_B)` is
**augmented** (`TauCeti.AInfinityHom.IsAugmented`) when its linear component intertwines the
augmentations (`ε_B (f₁ a) = ε_A a`) and every higher component lands in the target augmentation
ideal `ker ε_B`.  On the reduced bar construction this says that `ε_B ∘ f.taylor` agrees with
`ε_A ∘ letter` (`TauCeti.AInfinityHom.isAugmented_iff_taylor`), so augmented morphisms contain
the identity and are closed under composition.

This file also packages the strict `A∞` inclusion `ker ε ↪ A`, the universal factorization of
ideal-valued `A∞` morphisms through `ker ε`, and the functorial restriction
`TauCeti.AInfinityHom.IsAugmented.reducedHom : ker ε_A ⟶ ker ε_B` of an augmented `A∞` morphism
to the reduced augmentation ideals.  The inverse extension `liftHom` to a strictly unital
augmented morphism is established in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented.Lift`.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.inclusionStrictHom`: the strict `A∞` inclusion of the
  reduced augmentation ideal `ker ε ⟶ A`.
* `TauCeti.AInfinityAlgebra.Augmentation.liftToReduced` and
  `TauCeti.AInfinityAlgebra.Augmentation.idealValuedHomEquiv`: factoring an `A∞` morphism into `B`
  through `ker ε_B` when its suspended Taylor map takes values in `ker ε_B`.
* `TauCeti.AInfinityHom.IsAugmented`: the augmentation-compatibility predicate on an `A∞`
  morphism.
* `TauCeti.AInfinityHom.IsAugmented.reducedHom`: the induced `A∞` morphism
  `ker ε_A ⟶ ker ε_B`.

## Main results

* `TauCeti.AInfinityHom.isAugmented_iff_taylor`: characterization of `IsAugmented` via the
  suspended Taylor map.
* `TauCeti.AInfinityHom.IsAugmented.comp`, `reducedHom_id`, and `reducedHom_comp`: functoriality
  of augmented `A∞` morphisms and restriction to reduced augmentation ideals.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
-/

public section

namespace TauCeti

universe uR uA uB uC

section InclusionAndReducedPart

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 : AInfinityAlgebra R A}

namespace AInfinityAlgebra.Augmentation

/-- The inclusion `ker ε ↪ A` of the reduced augmentation ideal as a strict `A∞` morphism. -/
noncomputable def inclusionStrictHom (ε : 𝒜.Augmentation) :
    AInfinityStrictHom ε.reducedAlgebra 𝒜 where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' ha := by
    rw [reducedAlgebra_grading, reducedGrading_piece, Submodule.mem_comap] at ha
    exact ha
  map_m' n := MultilinearMap.ext fun x ↦ by
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      reducedAlgebra_m, Submodule.subtype_apply, coe_reducedOperation]
    rfl

/-- The underlying linear map of `ε.inclusionStrictHom` is the submodule inclusion of `ker ε`. -/
@[simp]
theorem inclusionStrictHom_toLinearMap (ε : 𝒜.Augmentation) :
    ε.inclusionStrictHom.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

/-- Evaluating `ε.inclusionStrictHom` coerces an element of `ker ε` into `A`. -/
@[simp]
theorem inclusionStrictHom_apply (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.inclusionStrictHom x = (x : A) := (rfl)

section Target

variable {B : Type uB} [AddCommGroup B] [Module R B] {ℬ : AInfinityAlgebra R B}

private theorem subtype_comp_reducedPart_comp_taylor (ε : ℬ.Augmentation)
    {f : AInfinityHom 𝒜 ℬ} (hf : ∀ z, f.taylor z ∈ ε.augmentationIdeal) :
    ε.augmentationIdeal.subtype ∘ₗ (ε.reducedPart ∘ₗ f.taylor) = f.taylor := by
  refine LinearMap.ext fun z ↦ ?_
  dsimp only [LinearMap.comp_apply, Submodule.subtype_apply]
  exact congrArg Subtype.val (ε.reducedPart_coe ⟨f.taylor z, hf z⟩)

private theorem taylor_comp_coalgHom_reducedPart_comp_taylor (ε : ℬ.Augmentation)
    {f : AInfinityHom 𝒜 ℬ} (hf : ∀ z, f.taylor z ∈ ε.augmentationIdeal) :
    ε.reducedAlgebra.taylor ∘ₗ ReducedTensorWords.coalgHom R (ε.reducedPart ∘ₗ f.taylor) =
      (ε.reducedPart ∘ₗ f.taylor) ∘ₗ 𝒜.barDifferential := by
  refine LinearMap.ext fun z ↦ ε.augmentationIdeal.injective_subtype ?_
  have hB := LinearMap.congr_fun ε.inclusionStrictHom.taylor_comp_barMap
    (ReducedTensorWords.coalgHom R (ε.reducedPart ∘ₗ f.taylor) z)
  have hm := LinearMap.congr_fun
    (ReducedTensorWords.map_comp_coalgHom (R := R)
      ε.augmentationIdeal.subtype (ε.reducedPart ∘ₗ f.taylor)) z
  have hf' := LinearMap.congr_fun f.taylor_comp_barMap z
  rw [f.barMap_eq_coalgHom] at hf'
  simp only [AInfinityStrictHom.barMap_def, inclusionStrictHom_toLinearMap,
    LinearMap.comp_apply, ε.subtype_comp_reducedPart_comp_taylor hf] at hB hm hf' ⊢
  rw [← hB, hm, hf']
  exact (congrArg Subtype.val (ε.reducedPart_coe ⟨_, hf _⟩)).symm

/-- Factor an `A∞` morphism `f : A ⟶ B` whose suspended Taylor map takes values in `ker ε`
through the reduced augmentation ideal `ker ε`. -/
noncomputable def liftToReduced (ε : ℬ.Augmentation) (f : AInfinityHom 𝒜 ℬ)
    (hf : ∀ z, f.taylor z ∈ ε.augmentationIdeal) :
    AInfinityHom 𝒜 ε.reducedAlgebra :=
  AInfinityHom.ofTaylor (ε.reducedPart ∘ₗ f.taylor)
    (by simpa using ε.isHomogeneous_reducedPart_shift_one.comp f.isHomogeneous_taylor)
    (ε.taylor_comp_coalgHom_reducedPart_comp_taylor hf)

/-- The suspended Taylor map of `ε.liftToReduced f` postcomposes `f.taylor` with `ε.reducedPart`. -/
@[simp]
theorem taylor_liftToReduced (ε : ℬ.Augmentation) (f : AInfinityHom 𝒜 ℬ)
    (hf : ∀ z, f.taylor z ∈ ε.augmentationIdeal) :
    (ε.liftToReduced f hf).taylor = ε.reducedPart ∘ₗ f.taylor :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- In `B`, the linear part of `ε.liftToReduced f` agrees pointwise with `f.linearPart`. -/
theorem coe_linearPart_liftToReduced (ε : ℬ.Augmentation) (f : AInfinityHom 𝒜 ℬ)
    (hf : ∀ z, f.taylor z ∈ ε.augmentationIdeal) (a : A) :
    ((ε.liftToReduced f hf).linearPart a : B) = f.linearPart a := by
  rw [AInfinityHom.linearPart_apply, AInfinityHom.linearPart_apply, ε.taylor_liftToReduced,
    LinearMap.comp_apply]
  exact congrArg Subtype.val (ε.reducedPart_coe ⟨_, hf _⟩)

/-- Postcomposing `ε.liftToReduced f` with the inclusion of `ker ε` recovers `f`. -/
@[simp]
theorem inclusionStrictHom_comp_liftToReduced (ε : ℬ.Augmentation) (f : AInfinityHom 𝒜 ℬ)
    (hf : ∀ z, f.taylor z ∈ ε.augmentationIdeal) :
    ε.inclusionStrictHom.toAInfinityHom.comp (ε.liftToReduced f hf) = f := by
  apply AInfinityHom.ext
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, inclusionStrictHom_toLinearMap,
    ε.taylor_liftToReduced]
  exact ε.subtype_comp_reducedPart_comp_taylor hf

/-- Factoring `ε.inclusionStrictHom ∘ g` through `ker ε` recovers `g`. -/
@[simp]
theorem liftToReduced_inclusionStrictHom_comp (ε : ℬ.Augmentation)
    (g : AInfinityHom 𝒜 ε.reducedAlgebra)
    (hg : ∀ z, (ε.inclusionStrictHom.toAInfinityHom.comp g).taylor z ∈ ε.augmentationIdeal) :
    ε.liftToReduced (ε.inclusionStrictHom.toAInfinityHom.comp g) hg = g := by
  apply AInfinityHom.ext
  rw [ε.taylor_liftToReduced, AInfinityStrictHom.taylor_toAInfinityHom_comp,
    inclusionStrictHom_toLinearMap, ← LinearMap.comp_assoc, ε.reducedPart_comp_subtype,
    LinearMap.id_comp]

/-- Universal property of the reduced augmentation ideal `ker ε`: `A∞` morphisms `A ⟶ ker ε`
correspond bijectively, via postcomposition with `ε.inclusionStrictHom`, to `A∞` morphisms
`A ⟶ B` whose suspended Taylor map lands in `ker ε`. -/
noncomputable def idealValuedHomEquiv (𝒜 : AInfinityAlgebra R A) (ε : ℬ.Augmentation) :
    AInfinityHom 𝒜 ε.reducedAlgebra ≃
      {f : AInfinityHom 𝒜 ℬ // ∀ z, f.taylor z ∈ ε.augmentationIdeal} where
  toFun g := ⟨ε.inclusionStrictHom.toAInfinityHom.comp g, fun z ↦ by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, inclusionStrictHom_toLinearMap,
      LinearMap.comp_apply, Submodule.subtype_apply]
    exact (g.taylor z).property⟩
  invFun f := ε.liftToReduced f.val f.property
  left_inv g := ε.liftToReduced_inclusionStrictHom_comp g _
  right_inv f := Subtype.ext (ε.inclusionStrictHom_comp_liftToReduced f.val f.property)

/-- Forward evaluation of `idealValuedHomEquiv` postcomposes with `ε.inclusionStrictHom`. -/
@[simp]
theorem idealValuedHomEquiv_apply (𝒜 : AInfinityAlgebra R A) (ε : ℬ.Augmentation)
    (g : AInfinityHom 𝒜 ε.reducedAlgebra) :
    (ε.idealValuedHomEquiv 𝒜 g).val = ε.inclusionStrictHom.toAInfinityHom.comp g := (rfl)

/-- Inverse evaluation of `idealValuedHomEquiv` applies `ε.liftToReduced`. -/
@[simp]
theorem idealValuedHomEquiv_symm_apply (𝒜 : AInfinityAlgebra R A) (ε : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ // ∀ z, f.taylor z ∈ ε.augmentationIdeal}) :
    (ε.idealValuedHomEquiv 𝒜).symm f = ε.liftToReduced f.val f.property := (rfl)

end Target

end AInfinityAlgebra.Augmentation

end InclusionAndReducedPart

section IsAugmented

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

namespace AInfinityHom

/-- An `A∞` morphism between augmented `A∞` algebras is **augmented** when its linear component
intertwines the augmentations and every higher component takes values in the target augmentation
ideal. -/
structure IsAugmented (f : AInfinityHom AA BB) (εA : AA.Augmentation)
    (εB : BB.Augmentation) : Prop where
  /-- The linear component intertwines the augmentations. -/
  map_linearPart : ∀ a, εB (f.linearPart a) = εA a
  /-- Every component away from arity one lands in the target augmentation ideal. -/
  component_mem_augmentationIdeal : ∀ {n : ℕ}, n ≠ 1 → ∀ x : Fin n → A,
    f.component n x ∈ εB.augmentationIdeal

/-- On the suspended bar coalgebra, `f` is augmented precisely when `ε_B ∘ f.taylor` agrees with
`ε_A ∘ letter`. -/
theorem isAugmented_iff_taylor {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} :
    f.IsAugmented εA εB ↔
      εB.toLinearMap ∘ₗ f.taylor = εA.toLinearMap ∘ₗ ReducedTensorWords.letter R A := by
  constructor
  · intro hf
    refine ReducedTensorWords.linearMap_ext R A fun ⟨n, hn⟩ x ↦ ?_
    by_cases hn1 : n = 1
    · subst hn1
      have hw : ReducedTensorWords.of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) =
          ReducedTensorWords.ofLetter R A (x ⟨0, hn⟩) := by
        rw [ReducedTensorWords.of_tprod_eq_subword R hn, ReducedTensorWords.subword_one R A x hn]
      rw [hw, LinearMap.comp_apply, LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter,
        ← linearPart_apply]
      exact hf.map_linearPart _
    · have hne1 : (⟨n, hn⟩ : {k : ℕ // 0 < k}) ≠ 1 :=
        fun h ↦ hn1 (congrArg Subtype.val h)
      have htw : f.component n (fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)) =
          f.taylor (ReducedTensorWords.of R A ⟨n, hn⟩ (PiTensorProduct.tprod R x)) := by
        rw [component_apply f n hn]
        simp only [InternalGrading.koszulTwist_koszulTwist]
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        ReducedTensorWords.letter_of_of_ne_one R A hne1, map_zero, ← htw]
      exact (εB.mem_augmentationIdeal).1 (hf.component_mem_augmentationIdeal hn1 _)
  · intro ht
    refine ⟨fun a ↦ ?_, fun {n} hn x ↦ ?_⟩
    · simpa [linearPart_apply] using LinearMap.congr_fun ht (ReducedTensorWords.ofLetter R A a)
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · have hne1 : (⟨n, hn0⟩ : {k : ℕ // 0 < k}) ≠ 1 :=
          fun h ↦ hn (congrArg Subtype.val h)
        rw [εB.mem_augmentationIdeal, component_apply f n hn0]
        have hz := LinearMap.congr_fun ht (ReducedTensorWords.of R A ⟨n, hn0⟩
          (PiTensorProduct.tprod R fun i ↦ AA.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))
        simpa [ReducedTensorWords.letter_of_of_ne_one R A hne1] using hz

/-- A strict `A∞` morphism is augmented precisely when its linear part intertwines the
augmentations. -/
theorem IsStrict.isAugmented_iff {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsStrict) :
    f.IsAugmented εA εB ↔ ∀ a, εB (f.linearPart a) = εA a := by
  refine ⟨IsAugmented.map_linearPart, fun hlin ↦ ⟨hlin, fun {n} hn x ↦ ?_⟩⟩
  rw [← hf.toAInfinityHom_toStrictHom,
    MultilinearMap.congr_fun (hf.toStrictHom.component_toAInfinityHom_eq_zero hn) x]
  exact zero_mem _

/-- The identity `A∞` morphism is augmented for every augmentation. -/
@[simp]
theorem isAugmented_id (εA : AA.Augmentation) : (AInfinityHom.id AA).IsAugmented εA εA := by
  rw [isAugmented_iff_taylor, taylor_id]

namespace IsAugmented

/-- Composition of augmented `A∞` morphisms is augmented. -/
theorem comp {C : Type uC} [AddCommGroup C] [Module R C] {CC : AInfinityAlgebra R C}
    {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    {εA : AA.Augmentation} {εB : BB.Augmentation} {εC : CC.Augmentation}
    (hg : g.IsAugmented εB εC) (hf : f.IsAugmented εA εB) :
    (g.comp f).IsAugmented εA εC := by
  rw [isAugmented_iff_taylor] at hg hf ⊢
  rw [taylor_comp, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, ← f.taylor_def, hf]

/-- On bar words over the source augmentation ideal, the suspended Taylor map of an augmented
morphism lands in the target augmentation ideal. -/
theorem taylor_map_subtype_mem {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB)
    (w : ReducedTensorWords R εA.augmentationIdeal) :
    f.taylor (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w) ∈
      εB.augmentationIdeal := by
  rw [εB.mem_augmentationIdeal]
  have ht := LinearMap.congr_fun (isAugmented_iff_taylor.1 hf)
    (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w)
  have hl := LinearMap.congr_fun
    (ReducedTensorWords.letter_comp_map (R := R) εA.augmentationIdeal.subtype) w
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at ht hl
  rw [ht, hl]
  exact (εA.mem_augmentationIdeal).1 (ReducedTensorWords.letter R εA.augmentationIdeal w).property

/-- Suspended Taylor map of the induced `A∞` morphism `ker ε_A ⟶ ker ε_B`. -/
private noncomputable def reducedHomTaylor {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (_ : f.IsAugmented εA εB) :
    ReducedTensorWords R εA.augmentationIdeal →ₗ[R] εB.augmentationIdeal :=
  εB.reducedPart ∘ₗ f.taylor ∘ₗ
    ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype

private theorem isHomogeneous_reducedHomTaylor {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) :
    LinearMap.IsHomogeneous hf.reducedHomTaylor
      (ReducedTensorWords.gradedPiece (εA.reducedAlgebra.grading.shift 1))
      (εB.reducedAlgebra.grading.shift 1).piece 0 := by
  have h1 : LinearMap.IsHomogeneous
      (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype)
      (ReducedTensorWords.gradedPiece (εA.reducedAlgebra.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 0 := by
    simpa [AInfinityStrictHom.barMap_def] using εA.inclusionStrictHom.isHomogeneous_barMap
  simpa [reducedHomTaylor] using
    εB.isHomogeneous_reducedPart_shift_one.comp (f.isHomogeneous_taylor.comp h1)

private theorem subtype_comp_reducedHomTaylor {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) :
    εB.augmentationIdeal.subtype ∘ₗ hf.reducedHomTaylor =
      f.taylor ∘ₗ ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype := by
  refine LinearMap.ext fun w ↦ ?_
  dsimp only [reducedHomTaylor, LinearMap.comp_apply, Submodule.subtype_apply]
  exact congrArg Subtype.val (εB.reducedPart_coe ⟨_, hf.taylor_map_subtype_mem w⟩)

private theorem taylor_comp_coalgHom_reducedHomTaylor {f : AInfinityHom AA BB}
    {εA : AA.Augmentation} {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) :
    εB.reducedAlgebra.taylor ∘ₗ ReducedTensorWords.coalgHom R hf.reducedHomTaylor =
      hf.reducedHomTaylor ∘ₗ εA.reducedAlgebra.barDifferential := by
  refine LinearMap.ext fun w ↦ εB.augmentationIdeal.injective_subtype ?_
  have hB := LinearMap.congr_fun εB.inclusionStrictHom.taylor_comp_barMap
    (ReducedTensorWords.coalgHom R hf.reducedHomTaylor w)
  have hm := LinearMap.congr_fun
    (ReducedTensorWords.map_comp_coalgHom (R := R)
      εB.augmentationIdeal.subtype hf.reducedHomTaylor) w
  simp only [AInfinityStrictHom.barMap_def,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap,
    LinearMap.comp_apply, hf.subtype_comp_reducedHomTaylor] at hB hm ⊢
  rw [← hB, hm]
  have hc := LinearMap.congr_fun
    (((ReducedTensorWords.isCoalgHom_coalgHom f.taylor).comp
      (ReducedTensorWords.isCoalgHom_map (R := R) εA.augmentationIdeal.subtype)).eq_coalgHom) w
  rw [← LinearMap.comp_assoc, ReducedTensorWords.letter_comp_coalgHom] at hc
  have hf' := LinearMap.congr_fun f.taylor_comp_barMap
    (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w)
  rw [f.barMap_eq_coalgHom] at hf'
  simp only [LinearMap.comp_apply] at hc hf'
  have hA := LinearMap.congr_fun εA.inclusionStrictHom.barDifferential_comp_barMap w
  simp only [AInfinityStrictHom.barMap_def,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap,
    LinearMap.comp_apply] at hA
  have hsub' := LinearMap.congr_fun hf.subtype_comp_reducedHomTaylor
    (εA.reducedAlgebra.barDifferential w)
  simp only [LinearMap.comp_apply] at hsub'
  rw [← hc, hf', hA, ← hsub']

/-- The `A∞` morphism `ker ε_A ⟶ ker ε_B` induced on the reduced augmentation ideals by an
augmented `A∞` morphism `f : A ⟶ B`. -/
noncomputable def reducedHom {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) :
    AInfinityHom εA.reducedAlgebra εB.reducedAlgebra :=
  ofTaylor hf.reducedHomTaylor hf.isHomogeneous_reducedHomTaylor
    hf.taylor_comp_coalgHom_reducedHomTaylor

/-- The suspended Taylor map of `hf.reducedHom` includes words from `ker ε_A`, applies `f.taylor`,
and projects onto `ker ε_B`. -/
@[simp]
theorem taylor_reducedHom {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) :
    hf.reducedHom.taylor =
      εB.reducedPart ∘ₗ f.taylor ∘ₗ
        ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype :=
  taylor_ofTaylor _ _ _

/-- On elements of `ker ε_A`, the linear part of `hf.reducedHom` agrees with `f.linearPart` after
coercion to `B`. -/
theorem coe_linearPart_reducedHom {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) (x : εA.augmentationIdeal) :
    (hf.reducedHom.linearPart x : B) = f.linearPart (x : A) := by
  have hx : f.linearPart x ∈ εB.augmentationIdeal :=
    (εB.mem_augmentationIdeal).2 ((hf.map_linearPart x).trans ((εA.mem_augmentationIdeal).1 x.2))
  rw [linearPart_apply, hf.taylor_reducedHom, LinearMap.comp_apply, LinearMap.comp_apply,
    ReducedTensorWords.map_ofLetter, Submodule.subtype_apply, ← linearPart_apply]
  exact congrArg Subtype.val (εB.reducedPart_coe ⟨f.linearPart x, hx⟩)

/-- The induced morphism `hf.reducedHom` intertwines the inclusions of the reduced augmentation
ideals. -/
theorem inclusionStrictHom_comp_reducedHom {f : AInfinityHom AA BB} {εA : AA.Augmentation}
    {εB : BB.Augmentation} (hf : f.IsAugmented εA εB) :
    εB.inclusionStrictHom.toAInfinityHom.comp hf.reducedHom =
      f.comp εA.inclusionStrictHom.toAInfinityHom := by
  apply AInfinityHom.ext
  have ht : hf.reducedHom.taylor = hf.reducedHomTaylor := taylor_ofTaylor _ _ _
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_comp,
    AInfinityStrictHom.barMap_toAInfinityHom, AInfinityStrictHom.barMap_def,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap, ht]
  exact hf.subtype_comp_reducedHomTaylor

/-- The identity augmented morphism induces the identity on the reduced augmentation ideal. -/
@[simp]
theorem reducedHom_id (εA : AA.Augmentation) :
    (isAugmented_id εA).reducedHom = AInfinityHom.id εA.reducedAlgebra := by
  apply AInfinityHom.ext
  rw [taylor_reducedHom, taylor_id, ReducedTensorWords.letter_comp_map,
    ← LinearMap.comp_assoc, εA.reducedPart_comp_subtype, LinearMap.id_comp, taylor_id]

/-- Restricting augmented morphisms to the reduced augmentation ideals commutes with
composition. -/
theorem reducedHom_comp {C : Type uC} [AddCommGroup C] [Module R C] {CC : AInfinityAlgebra R C}
    {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    {εA : AA.Augmentation} {εB : BB.Augmentation} {εC : CC.Augmentation}
    (hg : g.IsAugmented εB εC) (hf : f.IsAugmented εA εB) :
    (hg.comp hf).reducedHom = hg.reducedHom.comp hf.reducedHom := by
  apply AInfinityHom.ext
  have hbar := congrArg AInfinityHom.barMap hf.inclusionStrictHom_comp_reducedHom
  rw [barMap_comp, barMap_comp, AInfinityStrictHom.barMap_toAInfinityHom,
    AInfinityStrictHom.barMap_toAInfinityHom, AInfinityStrictHom.barMap_def,
    AInfinityStrictHom.barMap_def,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap,
    AInfinityAlgebra.Augmentation.inclusionStrictHom_toLinearMap] at hbar
  rw [taylor_reducedHom, taylor_comp, taylor_comp, taylor_reducedHom,
    LinearMap.comp_assoc, LinearMap.comp_assoc, LinearMap.comp_assoc, hbar]

end IsAugmented

end AInfinityHom

end IsAugmented

end TauCeti
