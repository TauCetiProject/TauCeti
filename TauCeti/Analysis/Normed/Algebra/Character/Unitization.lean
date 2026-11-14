/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Topology.Compactification.OnePoint.ComplSingleton

import TauCeti.Topology.Compactness.Compact

/-!
# Character space of a unitization

For a nonunital normed `𝕜`-algebra `A`, `Unitization 𝕜 A` carries the product topology from
`𝕜 × A`. Every continuous nonunital character `χ : characterSpace 𝕜 A` extends by unitality
(`Unitization.lift`) to a character `u ↦ u.fst + χ u.snd` on `Unitization 𝕜 A` distinct from the
augmentation character `ε : u ↦ u.fst`, and restricting characters of `Unitization 𝕜 A` along
`Unitization.inr : A → Unitization 𝕜 A` inverts this extension.

## Main definitions and results

* `Unitization.augmentation`: the augmentation character `u ↦ u.fst` in
  `characterSpace 𝕜 (Unitization 𝕜 A)`, whose kernel on `Unitization 𝕜 A` is `Set.range inr`.
* `WeakDual.CharacterSpace.unitizationComplAugmentationHomeomorph`: the weak-star homeomorphism
  between `characterSpace 𝕜 A` and
  `{φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}` given by unital
  extension `u ↦ u.fst + χ u.snd` and restriction along `inr`.
* `WeakDual.CharacterSpace.instCompactSpaceCharacterSpaceUnitization` and
  `WeakDual.CharacterSpace.onePointHomeomorphUnitization`: when `𝕜` is proper and `A` is complete
  (with no regular-norm assumption on `A`), `characterSpace 𝕜 (Unitization 𝕜 A)` is compact and
  homeomorphic to `OnePoint (characterSpace 𝕜 A)` with `∞` sent to `Unitization.augmentation 𝕜 A`.
* `Unitization.isOpen_singleton_augmentation_of_forall_mul_eq`,
  `Unitization.isClopen_singleton_augmentation`, and
  `WeakDual.CharacterSpace.compactSpace_of_isUnital`: when `A` has a right (in particular,
  two-sided) multiplicative identity, `{augmentation 𝕜 A}` is open in
  `characterSpace 𝕜 (Unitization 𝕜 A)` and `characterSpace 𝕜 A` is compact.

## References

* J. B. Conway, *A Course in Functional Analysis*, §VIII.2.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §2.1.
-/

@[expose] public section

open Filter Function Set Topology OnePoint WeakDual

namespace Unitization

section NormedAlgebra

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The augmentation character `u ↦ u.fst` on `Unitization 𝕜 A` as an element of
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
noncomputable def augmentation : characterSpace 𝕜 (Unitization 𝕜 A) where
  val := StrongDual.toWeakDual
    { (fstHom 𝕜 A).toLinearMap with cont := Unitization.continuous_fst }
  property := by
    rw [CharacterSpace.eq_set_map_one_map_mul]
    exact ⟨fst_one (R := 𝕜) (A := A), fun x y ↦ fst_mul x y⟩

variable {𝕜 A}

/-- `augmentation 𝕜 A` extracts the scalar component `u.fst`. -/
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

/-- Viewed as an `AlgHom`, `augmentation 𝕜 A` is `Unitization.fstHom 𝕜 A`. -/
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

/-- An element of `Unitization 𝕜 A` killed by `augmentation 𝕜 A` equals the image of its `A`
component under `Unitization.inr`. -/
theorem inr_snd_of_augmentation_eq_zero {u : Unitization 𝕜 A}
    (hu : augmentation 𝕜 A u = 0) : (u.snd : Unitization 𝕜 A) = u := by
  have hfst : u.fst = 0 := hu
  simpa [hfst] using inl_fst_add_inr_snd_eq u

/-- The image of `A` in `Unitization 𝕜 A` is the kernel of the augmentation character. -/
theorem range_inr_eq_ker_augmentation :
    Set.range (inr : A → Unitization 𝕜 A) =
      (RingHom.ker (augmentation 𝕜 A) : Set (Unitization 𝕜 A)) := by
  ext u
  exact ⟨by rintro ⟨a, rfl⟩; simp, fun hu ↦ ⟨u.snd, inr_snd_of_augmentation_eq_zero hu⟩⟩

/-- A character of `Unitization 𝕜 A` equals the augmentation character if and only if it vanishes on
`A`. -/
theorem eq_augmentation_iff {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ = augmentation 𝕜 A ↔ ∀ a : A, φ (a : Unitization 𝕜 A) = 0 :=
  ⟨fun h a ↦ by simp [h],
   fun h ↦ algHom_ext'' fun a ↦ (h a).trans (augmentation_inr a).symm⟩

/-- A character of `Unitization 𝕜 A` differs from the augmentation character if and only if it is
nonzero at some element of `A`. -/
theorem ne_augmentation_iff {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ ≠ augmentation 𝕜 A ↔ ∃ a : A, φ (a : Unitization 𝕜 A) ≠ 0 := by
  simp [eq_augmentation_iff]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- Every character of `Unitization 𝕜 A` sends an idempotent `e : A` (`e * e = e`) to `0` or `1` in
`𝕜`. -/
theorem apply_inr_eq_zero_or_one {e : A} (he : e * e = e)
    (φ : characterSpace 𝕜 (Unitization 𝕜 A)) :
    φ (e : Unitization 𝕜 A) = 0 ∨ φ (e : Unitization 𝕜 A) = 1 := by
  have hidem : φ (e : Unitization 𝕜 A) * (φ (e : Unitization 𝕜 A) - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, ← inr_mul, he, sub_self]
  exact (mul_eq_zero.mp hidem).imp_right sub_eq_zero.mp

/-- When `e : A` is a right multiplicative identity on `A`, a character of `Unitization 𝕜 A` equals
the augmentation character if and only if it vanishes at `e`. -/
theorem eq_augmentation_iff_apply_inr_eq_zero {e : A} (he : ∀ a : A, a * e = a)
    {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ = augmentation 𝕜 A ↔ φ (e : Unitization 𝕜 A) = 0 := by
  refine ⟨fun h ↦ by simp [h], fun h0 ↦ eq_augmentation_iff.2 fun a ↦ ?_⟩
  rw [← he a, inr_mul, map_mul, h0, mul_zero]

/-- When `e : A` is a right multiplicative identity on `A`, a character of `Unitization 𝕜 A` differs
from the augmentation character if and only if it sends `e` to `1`. -/
theorem ne_augmentation_iff_apply_inr_eq_one {e : A} (he : ∀ a : A, a * e = a)
    {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ ≠ augmentation 𝕜 A ↔ φ (e : Unitization 𝕜 A) = 1 := by
  rw [ne_eq, eq_augmentation_iff_apply_inr_eq_zero he]
  rcases apply_inr_eq_zero_or_one (he e) φ with h0 | h1
  · simp [h0]
  · simp [h1]

/-- When `A` admits a right multiplicative identity `e`, the singleton `{augmentation 𝕜 A}` is open
in `characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isOpen_singleton_augmentation_of_forall_mul_eq {e : A} (he : ∀ a : A, a * e = a) :
    IsOpen ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) := by
  have heq :
      ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) =
        (fun φ : characterSpace 𝕜 (Unitization 𝕜 A) ↦ φ (e : Unitization 𝕜 A)) ⁻¹'
          ({1}ᶜ : Set 𝕜) := by
    ext φ
    simp [← not_iff_not, ne_augmentation_iff_apply_inr_eq_one he]
  rw [heq]
  exact isClosed_singleton.isOpen_compl.preimage
    ((WeakDual.eval_continuous (e : Unitization 𝕜 A)).comp continuous_subtype_val)

/-- When `IsUnital A` holds, `{augmentation 𝕜 A}` is open in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isOpen_singleton_augmentation_of_isUnital [IsUnital A] :
    IsOpen ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) := by
  obtain ⟨e, he⟩ := IsUnital.isUnital (A := A)
  exact isOpen_singleton_augmentation_of_forall_mul_eq fun a ↦ (he a).2

/-- When `A` is a subsingleton, the augmentation character is the unique character of
`Unitization 𝕜 A`. -/
noncomputable instance instUniqueCharacterSpace [Subsingleton A] :
    Unique (characterSpace 𝕜 (Unitization 𝕜 A)) where
  default := augmentation 𝕜 A
  uniq φ := eq_augmentation_iff.2 fun a ↦ by
    rw [Subsingleton.elim a 0, inr_zero, map_zero]

/-- When `A` is a subsingleton, there are no characters of `Unitization 𝕜 A` other than the
augmentation character. -/
instance instIsEmptyComplAugmentation [Subsingleton A] :
    IsEmpty {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ augmentation 𝕜 A} :=
  ⟨fun φ ↦ φ.2 (Subsingleton.elim φ.1 _)⟩

end NormedAlgebra

section UnitalAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- When `A` has a multiplicative identity `1`, every character of `Unitization 𝕜 A` sends
`((1 : A) : Unitization 𝕜 A)` to the idempotent `0` or `1` in `𝕜`. -/
theorem apply_inr_one_eq_zero_or_one (φ : characterSpace 𝕜 (Unitization 𝕜 A)) :
    φ ((1 : A) : Unitization 𝕜 A) = 0 ∨ φ ((1 : A) : Unitization 𝕜 A) = 1 :=
  apply_inr_eq_zero_or_one (one_mul 1) φ

/-- For unital `A`, a character of `Unitization 𝕜 A` is the augmentation character if and only if it
vanishes at `(1 : A)`. -/
theorem eq_augmentation_iff_apply_inr_one {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ = augmentation 𝕜 A ↔ φ ((1 : A) : Unitization 𝕜 A) = 0 :=
  eq_augmentation_iff_apply_inr_eq_zero mul_one

/-- For unital `A`, a character of `Unitization 𝕜 A` differs from the augmentation character if and
only if it sends `(1 : A)` to `1`. -/
theorem ne_augmentation_iff_apply_inr_one {φ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    φ ≠ augmentation 𝕜 A ↔ φ ((1 : A) : Unitization 𝕜 A) = 1 :=
  ne_augmentation_iff_apply_inr_eq_one mul_one

/-- When `A` is unital, the singleton `{augmentation 𝕜 A}` is open in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isOpen_singleton_augmentation :
    IsOpen ({augmentation 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  isOpen_singleton_augmentation_of_forall_mul_eq mul_one

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
  let L : Unitization 𝕜 A →ₐ[𝕜] 𝕜 := Unitization.lift (toNonUnitalAlgHom χ)
  ⟨⟨StrongDual.toWeakDual
      { L.toLinearMap with
        cont := Unitization.continuous_fst.add
          ((map_continuous χ).comp Unitization.continuous_snd) },
    by
      rw [eq_set_map_one_map_mul]
      exact ⟨L.map_one, L.map_mul⟩⟩,
    by
      rw [Unitization.ne_augmentation_iff]
      obtain ⟨a, ha⟩ := exists_ne_zero χ
      refine ⟨a, ?_⟩
      rw [← CharacterSpace.coe_coe]
      simpa [L] using ha⟩

/-- `unitizationExtend χ` evaluates on `u : Unitization 𝕜 A` as `u.fst + χ u.snd`. -/
@[simp]
theorem unitizationExtend_apply (χ : characterSpace 𝕜 A) (u : Unitization 𝕜 A) :
    (unitizationExtend χ).1 u = u.fst + χ u.snd := (rfl)

/-- On elements of `A` embedded in `Unitization 𝕜 A`, `unitizationExtend χ` agrees with `χ`. -/
theorem unitizationExtend_apply_inr (χ : characterSpace 𝕜 A) (a : A) :
    (unitizationExtend χ).1 (a : Unitization 𝕜 A) = χ a := by
  simp

/-- Viewed as an `AlgHom`, `(unitizationExtend χ).1` is `Unitization.lift (toNonUnitalAlgHom χ)`. -/
@[simp]
theorem toAlgHom_unitizationExtend (χ : characterSpace 𝕜 A) :
    toAlgHom (unitizationExtend χ).1 = Unitization.lift (toNonUnitalAlgHom χ) := (rfl)

/-- Restriction of a non-augmentation character of `Unitization 𝕜 A` along
`Unitization.inr : A → Unitization 𝕜 A` to an element of `characterSpace 𝕜 A`. -/
noncomputable def unitizationRestrict
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    characterSpace 𝕜 A :=
  ⟨StrongDual.toWeakDual
    ((toCLM φ.1).comp
      { Unitization.inrHom 𝕜 𝕜 A with
        cont := Unitization.isUniformEmbedding_addEquiv.isEmbedding.continuous_iff.2
          (continuous_const.prodMk continuous_id) }),
    by
      refine ⟨?_, fun x y ↦ ?_⟩
      · obtain ⟨a, ha⟩ := Unitization.ne_augmentation_iff.mp φ.2
        exact fun h0 ↦ ha <| by
          simpa using DFunLike.congr_fun (StrongDual.toWeakDual.map_eq_zero_iff.mp h0) a
      · simp [Unitization.inr_mul]⟩

/-- `unitizationRestrict φ` restricts `φ.1` along `Unitization.inr`. -/
@[simp]
theorem unitizationRestrict_apply
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) (a : A) :
    unitizationRestrict φ a = φ.1 (a : Unitization 𝕜 A) := (rfl)

/-- Viewed as a `NonUnitalAlgHom`, `unitizationRestrict φ` is
`Unitization.lift.symm (toAlgHom φ.1)`. -/
@[simp]
theorem toNonUnitalAlgHom_unitizationRestrict
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    toNonUnitalAlgHom (unitizationRestrict φ) = Unitization.lift.symm (toAlgHom φ.1) := (rfl)

/-- Restricting `unitizationExtend χ` recovers `χ`. -/
@[simp]
theorem unitizationRestrict_unitizationExtend (χ : characterSpace 𝕜 A) :
    unitizationRestrict (unitizationExtend χ) = χ := by
  ext a
  simp

/-- Extending `unitizationRestrict φ` recovers `φ`. -/
@[simp]
theorem unitizationExtend_unitizationRestrict
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    unitizationExtend (unitizationRestrict φ) = φ :=
  Subtype.ext <| Unitization.algHom_ext'' (unitizationExtend_apply_inr _)

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
        (g := fun χ : characterSpace 𝕜 A ↦
          ((unitizationExtend χ).1 : WeakDual 𝕜 (Unitization 𝕜 A)))
        fun u ↦ continuous_const.add
          ((WeakDual.eval_continuous u.snd).comp continuous_subtype_val)) _) _
  continuous_invFun := by
    rw [continuous_induced_rng]
    refine WeakDual.continuous_of_continuous_eval fun a ↦ ?_
    exact (WeakDual.eval_continuous (a : Unitization 𝕜 A)).comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- `unitizationComplAugmentationHomeomorph 𝕜 A` applies `unitizationExtend`. -/
@[simp]
theorem unitizationComplAugmentationHomeomorph_apply (χ : characterSpace 𝕜 A) :
    unitizationComplAugmentationHomeomorph 𝕜 A χ = unitizationExtend χ := (rfl)

/-- `(unitizationComplAugmentationHomeomorph 𝕜 A).symm` applies `unitizationRestrict`. -/
@[simp]
theorem unitizationComplAugmentationHomeomorph_symm_apply
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    (unitizationComplAugmentationHomeomorph 𝕜 A).symm φ = unitizationRestrict φ := (rfl)

/-- For any nonunital Banach algebra `A` over a proper nontrivially normed field `𝕜`, the character
space of `Unitization 𝕜 A` is compact (with no regular-norm assumption on `A`). -/
instance instCompactSpaceCharacterSpaceUnitization [ProperSpace 𝕜] [CompleteSpace A] :
    CompactSpace (characterSpace 𝕜 (Unitization 𝕜 A)) := by
  rw [← isCompact_iff_compactSpace]
  let sndCLM : Unitization 𝕜 A →L[𝕜] A :=
    { Unitization.sndHom 𝕜 𝕜 A with cont := Unitization.continuous_snd }
  let g : WeakDual 𝕜 A → WeakDual 𝕜 (Unitization 𝕜 A) := fun ψ ↦
    StrongDual.toWeakDual
      (toCLM (Unitization.augmentation 𝕜 A) + (WeakDual.toStrongDual ψ).comp sndCLM)
  have hg : Continuous g :=
    WeakDual.continuous_of_continuous_eval fun u ↦
      continuous_const.add (WeakDual.eval_continuous u.snd)
  have hg0 : g 0 = (Unitization.augmentation 𝕜 A).1 :=
    DFunLike.ext _ _ fun u ↦ by simp [g, sndCLM]
  have himg : g '' (characterSpace 𝕜 A ∪ {0}) = characterSpace 𝕜 (Unitization 𝕜 A) := by
    ext φ
    refine ⟨?_, fun hφ ↦ ?_⟩
    · rintro ⟨ψ, hψ | rfl, rfl⟩
      · exact (unitizationExtend ⟨ψ, hψ⟩).1.2
      · rw [hg0]
        exact (Unitization.augmentation 𝕜 A).2
    · by_cases haug : (⟨φ, hφ⟩ : characterSpace 𝕜 (Unitization 𝕜 A)) = Unitization.augmentation 𝕜 A
      · exact ⟨0, Or.inr rfl, hg0.trans (congrArg Subtype.val haug.symm)⟩
      · refine ⟨(unitizationRestrict ⟨⟨φ, hφ⟩, haug⟩).1,
          Or.inl (unitizationRestrict ⟨⟨φ, hφ⟩, haug⟩).2, ?_⟩
        exact congrArg (Subtype.val ∘ Subtype.val)
          (unitizationExtend_unitizationRestrict ⟨⟨φ, hφ⟩, haug⟩)
  rw [← himg]
  exact isCompact_union_zero.image hg

/-- When a nonunital Banach algebra `A` over a proper nontrivially normed field `𝕜` has a right
multiplicative identity, `characterSpace 𝕜 A` is compact. -/
theorem compactSpace_of_forall_mul_eq [ProperSpace 𝕜] [CompleteSpace A] {e : A}
    (he : ∀ a : A, a * e = a) : CompactSpace (characterSpace 𝕜 A) := by
  have : CompactSpace
      {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A} :=
    TauCeti.compactSpace_complSingleton_iff_isOpen_singleton.mpr
      (Unitization.isOpen_singleton_augmentation_of_forall_mul_eq he)
  exact (unitizationComplAugmentationHomeomorph 𝕜 A).symm.compactSpace

/-- When `IsUnital A` holds for a nonunital Banach algebra `A` over a proper nontrivially normed
field `𝕜`, `characterSpace 𝕜 A` is compact. -/
theorem compactSpace_of_isUnital [ProperSpace 𝕜] [CompleteSpace A] [IsUnital A] :
    CompactSpace (characterSpace 𝕜 A) := by
  obtain ⟨e, he⟩ := IsUnital.isUnital (A := A)
  exact compactSpace_of_forall_mul_eq fun a ↦ (he a).2

variable (𝕜 A) in
/-- When `𝕜` is proper and `A` is complete, `OnePoint (characterSpace 𝕜 A)` is canonically
homeomorphic to `characterSpace 𝕜 (Unitization 𝕜 A)`, sending `∞` to `Unitization.augmentation 𝕜 A`
and `(χ : characterSpace 𝕜 A)` to `u ↦ u.fst + χ u.snd`. -/
noncomputable def onePointHomeomorphUnitization [ProperSpace 𝕜] [CompleteSpace A] :
    OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A) :=
  (unitizationComplAugmentationHomeomorph 𝕜 A).onePointCongr.trans
    (TauCeti.onePointComplSingletonHomeomorph (Unitization.augmentation 𝕜 A))

/-- `onePointHomeomorphUnitization 𝕜 A` sends `∞` to `Unitization.augmentation 𝕜 A`. -/
@[simp]
theorem onePointHomeomorphUnitization_apply_infty [ProperSpace 𝕜] [CompleteSpace A] :
    onePointHomeomorphUnitization 𝕜 A ∞ = Unitization.augmentation 𝕜 A := by
  simp [onePointHomeomorphUnitization]

/-- `onePointHomeomorphUnitization 𝕜 A` sends a finite point `χ` to `(unitizationExtend χ).1`. -/
@[simp]
theorem onePointHomeomorphUnitization_apply_coe [ProperSpace 𝕜] [CompleteSpace A]
    (χ : characterSpace 𝕜 A) :
    onePointHomeomorphUnitization 𝕜 A χ = (unitizationExtend χ).1 := by
  simp [onePointHomeomorphUnitization]

/-- `(onePointHomeomorphUnitization 𝕜 A).symm` sends `Unitization.augmentation 𝕜 A` to `∞`. -/
@[simp]
theorem onePointHomeomorphUnitization_symm_apply_augmentation [ProperSpace 𝕜] [CompleteSpace A] :
    (onePointHomeomorphUnitization 𝕜 A).symm (Unitization.augmentation 𝕜 A) = ∞ := by
  simp [onePointHomeomorphUnitization]

/-- Away from `Unitization.augmentation 𝕜 A`, `(onePointHomeomorphUnitization 𝕜 A).symm` restricts
along `Unitization.inr`. -/
theorem onePointHomeomorphUnitization_symm_apply_of_ne [ProperSpace 𝕜] [CompleteSpace A]
    {φ : characterSpace 𝕜 (Unitization 𝕜 A)} (hφ : φ ≠ Unitization.augmentation 𝕜 A) :
    (onePointHomeomorphUnitization 𝕜 A).symm φ = (unitizationRestrict ⟨φ, hφ⟩ : OnePoint _) := by
  rw [Homeomorph.symm_apply_eq, onePointHomeomorphUnitization_apply_coe,
    unitizationExtend_unitizationRestrict]

/-- On a punctured character `φ`, `(onePointHomeomorphUnitization 𝕜 A).symm φ.1` equals
`unitizationRestrict φ`. -/
@[simp]
theorem onePointHomeomorphUnitization_symm_apply_coe [ProperSpace 𝕜] [CompleteSpace A]
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 A) // φ ≠ Unitization.augmentation 𝕜 A}) :
    (onePointHomeomorphUnitization 𝕜 A).symm φ.1 = unitizationRestrict φ :=
  onePointHomeomorphUnitization_symm_apply_of_ne φ.2

end Extension

end WeakDual.CharacterSpace
