/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.OnePoint

import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Character space of a unitization

For a nonunital normed `𝕜`-algebra `A`, `Unitization 𝕜 A` carries the product topology from
`𝕜 × A`. Every continuous nonunital character `χ : characterSpace 𝕜 A` extends by unitality to a
character `u ↦ u.fst + χ u.snd` on `Unitization 𝕜 A` distinct from the augmentation character
`ε : u ↦ u.fst`, and restricting characters of `Unitization 𝕜 A` along
`Unitization.inr : A → Unitization 𝕜 A` inverts this extension.

## Main definitions and results

* `WeakDual.CharacterSpace.instLocallyCompactSpace`: the character space of any nonunital Banach
  algebra over a proper nontrivially normed field is locally compact, realized inside the weak-star
  compact closed unit ball as `(characterSpace 𝕜 A ∪ {0}) \ {0}`.
* `Unitization.augmentation`: the augmentation character `u ↦ u.fst` in
  `characterSpace 𝕜 (Unitization 𝕜 A)`, whose kernel on `Unitization 𝕜 A` is `Set.range inr`.
* `WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph`: the weak-star homeomorphism
  between `characterSpace 𝕜 A` and
  `{φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}` given by unital
  extension `u ↦ u.fst + χ u.snd` and restriction along `inr`.
* `WeakDual.CharacterSpace.onePointHomeomorphUnitization`: when `A` has a regular norm, `𝕜` is
  proper, and `A` is complete, the homeomorphism
  `OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A)` sending `∞` to
  `Unitization.augmentation 𝕜 A`.
* `Unitization.isClopen_singleton_augmentation`: when `A` is unital, `{augmentation 𝕜 A}` is clopen
  (isolated) in `characterSpace 𝕜 (Unitization 𝕜 A)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, §VIII.2.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §2.1.
-/

public section

open Filter Function Set Topology OnePoint WeakDual

namespace WeakDual.CharacterSpace

section LocallyCompact

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [CompleteSpace A]

/-- The character space of any nonunital Banach algebra over a proper nontrivially normed field is
locally compact: `characterSpace 𝕜 A ∪ {0}` is weak-star closed inside the compact closed unit
ball, and `characterSpace 𝕜 A` is the complement of `0` inside it. -/
instance instLocallyCompactSpace : LocallyCompactSpace (characterSpace 𝕜 A) := by
  let K : Set (WeakDual 𝕜 A) := characterSpace 𝕜 A ∪ {0}
  have hsub : K ⊆ toStrongDual ⁻¹' Metric.closedBall 0 1 := by
    rintro φ (hφ | rfl)
    · rw [Set.mem_preimage, mem_closedBall_zero_iff]
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
      have hbound : ‖(toStrongDual φ) a‖ ≤ ‖a‖ :=
        NonUnitalAlgHom.norm_apply_le_self (⟨φ, hφ⟩ : characterSpace 𝕜 A) a
      simpa only [one_mul] using hbound
    · simp
  have : CompactSpace K := isCompact_iff_compactSpace.mp <|
    (isCompact_closedBall 0 1).of_isClosed_subset (union_zero_isClosed 𝕜 A) hsub
  let z₀ : K := ⟨0, Or.inr rfl⟩
  let e : characterSpace 𝕜 A ≃ₜ {x : K // x ≠ z₀} :=
    { toFun φ := ⟨⟨φ.1, Or.inl φ.2⟩, fun h => φ.2.1 (congrArg Subtype.val h)⟩
      invFun x := ⟨x.1.1, x.1.2.resolve_right fun h0 => x.2 (Subtype.ext h0)⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact e.isOpenEmbedding.locallyCompactSpace

end LocallyCompact

end WeakDual.CharacterSpace

namespace Unitization

section NormedAlgebra

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The augmentation character `u ↦ u.fst` on `Unitization 𝕜 A` as an element of
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
noncomputable def augmentation : characterSpace 𝕜 (Unitization 𝕜 A) where
  val := ({ (fstHom 𝕜 A).toLinearMap with cont := Unitization.continuous_fst } :
    Unitization 𝕜 A →L[𝕜] 𝕜)
  property := by
    rw [CharacterSpace.eq_set_map_one_map_mul]
    exact ⟨fst_one (R := 𝕜) (A := A), fun x y => fst_mul x y⟩

variable {𝕜 A}

@[simp]
theorem augmentation_apply (u : Unitization 𝕜 A) :
    augmentation 𝕜 A u = u.fst := (rfl)

/-- The augmentation character vanishes on elements of `A` embedded via `Unitization.inr`. -/
theorem augmentation_inr (a : A) :
    augmentation 𝕜 A (a : Unitization 𝕜 A) = 0 :=
  fst_inr 𝕜 a

/-- On scalars embedded via `Unitization.inl`, the augmentation character recovers the scalar. -/
theorem augmentation_inl (k : 𝕜) :
    augmentation 𝕜 A (inl k : Unitization 𝕜 A) = k :=
  fst_inl A k

@[simp]
theorem toAlgHom_augmentation :
    CharacterSpace.toAlgHom (augmentation 𝕜 A) = fstHom 𝕜 A := by
  ext
  rfl

/-- As a ring ideal, the kernel of `Unitization.augmentation 𝕜 A` agrees with `ker (fstHom 𝕜 A)`. -/
theorem ker_augmentation :
    RingHom.ker (augmentation 𝕜 A) = RingHom.ker (fstHom 𝕜 A) := by
  ext
  rfl

/-- An element of `Unitization 𝕜 A` lies in `ker (augmentation 𝕜 A)` iff its scalar part is `0`. -/
theorem mem_ker_augmentation {u : Unitization 𝕜 A} :
    u ∈ RingHom.ker (augmentation 𝕜 A) ↔ u.fst = 0 :=
  Iff.rfl

/-- The image of `A` in `Unitization 𝕜 A` is the kernel of the augmentation character. -/
theorem range_inr_eq_ker_augmentation :
    Set.range (inr : A → Unitization 𝕜 A) =
      (RingHom.ker (augmentation 𝕜 A) : Set (Unitization 𝕜 A)) := by
  ext u
  refine ⟨?_, fun hu => ⟨u.snd, ?_⟩⟩
  · rintro ⟨a, rfl⟩
    simp
  · ext
    · exact (mem_ker_augmentation.mp hu).symm
    · simp

/-- A character of `Unitization 𝕜 A` equals the augmentation character if and only if it vanishes on
`A`. -/
theorem eq_augmentation_iff {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ = augmentation 𝕜 A ↔ ∀ a : A, φ (a : Unitization 𝕜 A) = 0 := by
  refine ⟨fun h a => by simp [h], fun h => ?_⟩
  ext u
  induction u using Unitization.ind with
  | inl_add_inr k a =>
    rw [map_add, ← algebraMap_eq_inl, AlgHomClass.commutes, h a, add_zero]
    simp [algebraMap_eq_inl]

/-- A character of `Unitization 𝕜 A` differs from the augmentation character if and only if it is
nonzero at some element of `A`. -/
theorem ne_augmentation_iff {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ ≠ augmentation 𝕜 A ↔ ∃ a : A, φ (a : Unitization 𝕜 A) ≠ 0 := by
  simp [eq_augmentation_iff]

/-- When `A` is a subsingleton, the augmentation character is the unique character of
`Unitization 𝕜 A`. -/
noncomputable instance instUniqueCharacterSpace [Subsingleton A] :
    Unique (characterSpace 𝕜 (Unitization 𝕜 A)) where
  default := augmentation 𝕜 A
  uniq φ := eq_augmentation_iff.2 fun a => by
    rw [Subsingleton.elim a 0, inr_zero, map_zero]

/-- When `A` is a subsingleton, there are no characters of `Unitization 𝕜 A` other than the
augmentation character. -/
instance instIsEmptyComplAugmentation [Subsingleton A] :
    IsEmpty {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ augmentation 𝕜 A} :=
  ⟨fun φ => φ.2 (Subsingleton.elim φ.1 _)⟩

end NormedAlgebra

section UnitalAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- When `A` has a multiplicative identity `1`, every character of `Unitization 𝕜 A` sends
`((1 : A) : Unitization 𝕜 A)` to the idempotent `0` or `1` in `𝕜`. -/
theorem apply_inr_one_eq_zero_or_one (φ : characterSpace 𝕜 (Unitization 𝕜 A)) :
    φ ((1 : A) : Unitization 𝕜 A) = 0 ∨ φ ((1 : A) : Unitization 𝕜 A) = 1 := by
  have hidem :
      φ ((1 : A) : Unitization 𝕜 A) * (φ ((1 : A) : Unitization 𝕜 A) - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, ← inr_mul, one_mul, sub_self]
  rcases mul_eq_zero.mp hidem with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- For unital `A`, a character of `Unitization 𝕜 A` is the augmentation character if and only if it
vanishes at `(1 : A)`. -/
theorem eq_augmentation_iff_apply_inr_one {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ = augmentation 𝕜 A ↔ φ ((1 : A) : Unitization 𝕜 A) = 0 := by
  refine ⟨fun h => by simp [h], fun h0 => eq_augmentation_iff.2 fun a => ?_⟩
  rw [← mul_one a, inr_mul, map_mul, h0, mul_zero]

/-- For unital `A`, a character of `Unitization 𝕜 A` differs from the augmentation character if and
only if it sends `(1 : A)` to `1`. -/
theorem ne_augmentation_iff_apply_inr_one {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ ≠ augmentation 𝕜 A ↔ φ ((1 : A) : Unitization 𝕜 A) = 1 := by
  rw [ne_eq, eq_augmentation_iff_apply_inr_one]
  rcases apply_inr_one_eq_zero_or_one φ with h0 | h1
  · simp [h0]
  · simp [h1]

/-- When `A` is unital, the singleton `{augmentation 𝕜 A}` is open in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isOpen_singleton_augmentation :
    IsOpen ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) := by
  have heq :
      ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) =
        (fun φ : characterSpace 𝕜 (Unitization 𝕜 A) => φ ((1 : A) : Unitization 𝕜 A)) ⁻¹'
          ({1}ᶜ : Set 𝕜) := by
    ext φ
    simp [← not_iff_not, ne_augmentation_iff_apply_inr_one]
  rw [heq]
  exact isClosed_singleton.isOpen_compl.preimage
    ((WeakDual.eval_continuous ((1 : A) : Unitization 𝕜 A)).comp continuous_subtype_val)

/-- When `A` is unital, `{augmentation 𝕜 A}` is clopen in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isClopen_singleton_augmentation :
    IsClopen ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  ⟨isClosed_singleton, isOpen_singleton_augmentation⟩

/-- When `A` is unital, the complement of `augmentation 𝕜 A` is closed in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isClosed_compl_singleton_augmentation :
    IsClosed ({augmentation 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  isOpen_singleton_augmentation.isClosed_compl

end UnitalAlgebra

end Unitization

namespace WeakDual.CharacterSpace

section Extension

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- Unital extension of a character `χ : characterSpace 𝕜 A` to a character of `Unitization 𝕜 A`
distinct from `Unitization.augmentation 𝕜 A`, sending `u` to `u.fst + χ u.snd`. -/
noncomputable def unitizationExtend (χ : characterSpace 𝕜 A) :
    {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A} :=
  let fstCLM : Unitization 𝕜 A →L[𝕜] 𝕜 :=
    { (Unitization.fstHom 𝕜 A).toLinearMap with cont := Unitization.continuous_fst }
  let sndCLM : Unitization 𝕜 A →L[𝕜] A :=
    { Unitization.sndHom 𝕜 𝕜 A with cont := Unitization.continuous_snd }
  ⟨⟨(fstCLM + (toCLM χ).comp sndCLM : Unitization 𝕜 A →L[𝕜] 𝕜),
      by
        rw [eq_set_map_one_map_mul]
        refine ⟨?_, fun x y => ?_⟩
        · -- `WeakDual` is a `WeakBilin` type synonym over `ContinuousLinearMap` without a coercion
          -- simp lemma, so unfold `WeakBilin` evaluation to the underlying linear map.
          change (1 : Unitization 𝕜 A).fst + χ (1 : Unitization 𝕜 A).snd = 1
          simp
        · -- Unfold `WeakBilin` evaluation to `u ↦ u.fst + χ u.snd` to check multiplicativity.
          change (x * y).fst + χ (x * y).snd = (x.fst + χ x.snd) * (y.fst + χ y.snd)
          simp only [Unitization.fst_mul, Unitization.snd_mul, map_add, map_smul, map_mul,
            smul_eq_mul]
          ring⟩,
    by
      rw [Unitization.ne_augmentation_iff]
      by_contra! hzero
      apply χ.prop.1
      exact ContinuousLinearMap.ext fun a => by
        -- `WeakDual` is a `WeakBilin` type synonym without simp lemmas for `(0 : _) a`.
        have ha : (0 : 𝕜) + χ a = 0 := hzero a
        change χ a = 0
        simpa using ha⟩

@[simp]
theorem unitizationExtend_apply (χ : characterSpace 𝕜 A) (u : Unitization 𝕜 A) :
    (unitizationExtend χ).1 u = u.fst + χ u.snd := (rfl)

/-- On elements of `A` embedded in `Unitization 𝕜 A`, `unitizationExtend χ` agrees with `χ`. -/
theorem unitizationExtend_apply_inr (χ : characterSpace 𝕜 A) (a : A) :
    (unitizationExtend χ).1 (a : Unitization 𝕜 A) = χ a := by
  simp

/-- Restriction of a non-augmentation character of `Unitization 𝕜 A` along
`Unitization.inr : A → Unitization 𝕜 A` to an element of `characterSpace 𝕜 A`. -/
noncomputable def unitizationRestrict
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    characterSpace 𝕜 A :=
  ⟨((toCLM φ.1).comp
      ({ Unitization.inrHom 𝕜 𝕜 A with
         cont := Unitization.isUniformEmbedding_addEquiv.isEmbedding.continuous_iff.2
           (continuous_const.prodMk continuous_id) } : A →L[𝕜] Unitization 𝕜 A) : A →L[𝕜] 𝕜),
    by
      refine ⟨?_, fun x y => ?_⟩
      · obtain ⟨a, ha⟩ := Unitization.ne_augmentation_iff.mp φ.2
        intro h0
        have ha0 := DFunLike.congr_fun h0 a
        -- Unfold `WeakBilin` evaluation on both sides of `ha0` to `φ.1 ↑a = 0`.
        change φ.1 (a : Unitization 𝕜 A) = 0 at ha0
        exact ha ha0
      · -- Unfold `WeakBilin` evaluation to `φ.1` applied to `Unitization.inr`.
        change φ.1 ((x * y : A) : Unitization 𝕜 A) =
          φ.1 (x : Unitization 𝕜 A) * φ.1 (y : Unitization 𝕜 A)
        rw [Unitization.inr_mul, map_mul]⟩

@[simp]
theorem unitizationRestrict_apply
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) (a : A) :
    unitizationRestrict φ a = φ.1 (a : Unitization 𝕜 A) := (rfl)

@[simp]
theorem unitizationRestrict_unitizationExtend (χ : characterSpace 𝕜 A) :
    unitizationRestrict (unitizationExtend χ) = χ := by
  ext a
  simp

@[simp]
theorem unitizationExtend_unitizationRestrict
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    unitizationExtend (unitizationRestrict φ) = φ := by
  apply Subtype.ext
  ext u
  induction u using Unitization.ind with
  | inl_add_inr k a =>
    rw [unitizationExtend_apply, map_add, ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes]
    simp [Unitization.algebraMap_eq_inl]

variable (𝕜 A) in
/-- Weak-star homeomorphism between `characterSpace 𝕜 A` and the punctured character space
`{φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}` given by unital
extension `χ ↦ (u ↦ u.fst + χ u.snd)` and restriction along `Unitization.inr`. -/
noncomputable def unitizationComplAugmentationHomeomorph :
    characterSpace 𝕜 A ≃ₜ
      {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A} where
  toFun := unitizationExtend
  invFun := unitizationRestrict
  left_inv := unitizationRestrict_unitizationExtend
  right_inv := unitizationExtend_unitizationRestrict
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      (WeakDual.continuous_of_continuous_eval
        (g := fun χ : characterSpace 𝕜 A =>
          ((unitizationExtend χ).1 : WeakDual 𝕜 (Unitization 𝕜 A)))
        fun u => continuous_const.add
          ((WeakDual.eval_continuous u.snd).comp continuous_subtype_val)) _) _
  continuous_invFun := by
    rw [continuous_induced_rng]
    refine WeakDual.continuous_of_continuous_eval fun a => ?_
    exact (WeakDual.eval_continuous (a : Unitization 𝕜 A)).comp
      (continuous_subtype_val.comp continuous_subtype_val)

@[simp]
theorem unitizationComplAugmentationHomeomorph_apply (χ : characterSpace 𝕜 A) :
    unitizationComplAugmentationHomeomorph 𝕜 A χ = unitizationExtend χ := (rfl)

@[simp]
theorem unitizationComplAugmentationHomeomorph_symm_apply
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    (unitizationComplAugmentationHomeomorph 𝕜 A).symm φ = unitizationRestrict φ := (rfl)

variable (𝕜 A) in
/-- When `A` has a regular norm, `𝕜` is proper, and `A` is complete, `OnePoint (characterSpace 𝕜 A)`
is canonically homeomorphic to `characterSpace 𝕜 (Unitization 𝕜 A)`, sending `∞` to
`Unitization.augmentation 𝕜 A` and `(χ : characterSpace 𝕜 A)` to `u ↦ u.fst + χ u.snd`. -/
noncomputable def onePointHomeomorphUnitization [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] :
    OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A) :=
  (unitizationComplAugmentationHomeomorph 𝕜 A).onePointCongr.trans
    (OnePoint.homeomorphComplSingleton (Unitization.augmentation 𝕜 A))

@[simp]
theorem onePointHomeomorphUnitization_apply_infty [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] :
    onePointHomeomorphUnitization 𝕜 A ∞ = Unitization.augmentation 𝕜 A := by
  simp [onePointHomeomorphUnitization]

@[simp]
theorem onePointHomeomorphUnitization_apply_coe [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] (χ : characterSpace 𝕜 A) :
    onePointHomeomorphUnitization 𝕜 A χ = (unitizationExtend χ).1 := by
  simp [onePointHomeomorphUnitization]

@[simp]
theorem onePointHomeomorphUnitization_symm_apply_augmentation [RegularNormedAlgebra 𝕜 A]
    [ProperSpace 𝕜] [CompleteSpace A] :
    (onePointHomeomorphUnitization 𝕜 A).symm (Unitization.augmentation 𝕜 A) = ∞ := by
  simp [onePointHomeomorphUnitization]

theorem onePointHomeomorphUnitization_symm_apply_of_ne [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] {φ : characterSpace 𝕜 (Unitization 𝕜 A)}
    (hφ : φ ≠ Unitization.augmentation 𝕜 A) :
    (onePointHomeomorphUnitization 𝕜 A).symm φ = (unitizationRestrict ⟨φ, hφ⟩ : OnePoint _) := by
  rw [Homeomorph.symm_apply_eq]
  simp

end Extension

end WeakDual.CharacterSpace
