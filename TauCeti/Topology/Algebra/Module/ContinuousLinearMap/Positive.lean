/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Faithfulness of positive continuous linear maps

A positive continuous linear map `f : A →P[R] B` out of a star ring with a partial order is
**faithful** (`PositiveContinuousLinearMap.IsFaithful`) when `f (star a * a) = 0` implies `a = 0`.

## Main definitions and results

* `PositiveContinuousLinearMap.domRestrict`: restrict the domain of `f : E₁ →P[R] E₂` to an
  additive `R`-subobject `s` (such as a `Submodule`, `StarSubalgebra`, or
  `NonUnitalStarSubalgebra`).
* `PositiveContinuousLinearMap.IsFaithful`: `∀ a : A, f (star a * a) = 0 → a = 0`.
* `PositiveContinuousLinearMap.isFaithful_iff_pos_star_mul_self`: over a `StarOrderedRing`, `f` is
  faithful if and only if `0 < f (star a * a)` for every nonzero `a`.
* `PositiveContinuousLinearMap.isFaithful_iff_of_nonneg` and
  `PositiveContinuousLinearMap.isFaithful_iff_pos_of_pos`: over a proper `StarOrderedRing`, `f` is
  faithful if and only if no nonzero nonnegative element maps to `0`, equivalently `0 < a` implies
  `0 < f a`.
* `PositiveContinuousLinearMap.IsFaithful.comp_of_injective`: pulling a faithful positive continuous
  linear map back along an injective positive continuous linear star-multiplicative map preserves
  faithfulness.
-/

public section

namespace PositiveContinuousLinearMap

section DomRestrict

variable {R E₁ E₂ M : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid E₂] [PartialOrder E₂] [Module R E₂] [TopologicalSpace E₂]
  [SetLike M E₁] [AddSubmonoidClass M E₁] [SMulMemClass M R E₁]

/-- Restrict the domain of a positive continuous linear map `f : E₁ →P[R] E₂` to an additive
`R`-subobject `s` (for instance a `Submodule`, `StarSubalgebra`, or `NonUnitalStarSubalgebra`). -/
def domRestrict (f : E₁ →P[R] E₂) (s : M) : s →P[R] E₂ where
  toFun x := f x
  map_add' x y := map_add f (x : E₁) (y : E₁)
  map_smul' c x := by
    simp only [RingHom.id_apply, SetLike.val_smul, map_smul]
  cont := (map_continuous f).comp continuous_subtype_val
  monotone' _ _ h := f.mono h

/-- `f.domRestrict s` evaluates on `x : s` as `f x`. -/
@[simp]
theorem domRestrict_apply (f : E₁ →P[R] E₂) (s : M) (x : s) : f.domRestrict s x = f x :=
  (rfl)

end DomRestrict

section General

variable {R A B : Type*} [Semiring R]
  [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [Module R A] [TopologicalSpace A]
  [AddCommMonoid B] [PartialOrder B] [Module R B] [TopologicalSpace B]

/-- A positive continuous linear map `f : A →P[R] B` out of a star-ordered ring is **faithful** if
`f (star a * a) = 0` implies `a = 0`. -/
def IsFaithful (f : A →P[R] B) : Prop :=
  ∀ a : A, f (star a * a) = 0 → a = 0

/-- Unfolding `PositiveContinuousLinearMap.IsFaithful`. -/
theorem isFaithful_iff {f : A →P[R] B} :
    f.IsFaithful ↔ ∀ a : A, f (star a * a) = 0 → a = 0 :=
  (Iff.rfl)

/-- If `f` is faithful and `f (star a * a) = 0`, then `a = 0`. -/
theorem IsFaithful.eq_zero_of_map_star_mul_self_eq_zero {f : A →P[R] B} (hf : f.IsFaithful)
    {a : A} (ha : f (star a * a) = 0) : a = 0 :=
  hf a ha

/-- **Pullback of faithfulness.** Pulling a faithful positive continuous linear map back along an
injective positive continuous linear map preserving multiplication and `star` yields a faithful
positive continuous linear map. -/
theorem IsFaithful.comp_of_injective {C F : Type*}
    [NonUnitalSemiring C] [PartialOrder C] [StarRing C] [Module R C] [TopologicalSpace C]
    [FunLike F A C] [ContinuousLinearMapClass F R A C] [MulHomClass F A C] [StarHomClass F A C]
    [OrderHomClass F A C] {ω : C →P[R] B} (hω : ω.IsFaithful) (f : F) (hf : Function.Injective f) :
    (ω.comp (.ofClass f)).IsFaithful := by
  intro a ha
  apply hf
  rw [map_zero]
  apply hω
  simpa [map_mul, map_star] using ha

end General

section StarMulSelfPos

variable {R A B : Type*} [Semiring R]
  [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [Module R A] [TopologicalSpace A]
  [AddCommMonoid B] [PartialOrder B] [Module R B] [TopologicalSpace B]
  {f : A →P[R] B}

/-- Over a `StarOrderedRing`, a positive continuous linear map is faithful if and only if
`0 < f (star a * a)` for every nonzero `a : A`. -/
theorem isFaithful_iff_pos_star_mul_self :
    f.IsFaithful ↔ ∀ a : A, a ≠ 0 → 0 < f (star a * a) := by
  rw [isFaithful_iff]
  refine ⟨fun hf a ha => ?_, fun h a ha => ?_⟩
  · exact lt_of_le_of_ne (f.map_nonneg (star_mul_self_nonneg a))
      fun h0 => ha (hf a h0.symm)
  · by_contra hne
    exact (h a hne).ne' ha

end StarMulSelfPos

section ProperStarOrdered

variable {R A B : Type*} [Semiring R]
  [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
  [Module R A] [TopologicalSpace A]
  [AddCommGroup B] [PartialOrder B] [IsOrderedAddMonoid B] [Module R B] [TopologicalSpace B]
  {f : A →P[R] B}

/-- Over a proper `StarOrderedRing`, a positive continuous linear map is faithful if and only if no
nonzero nonnegative element lies in its kernel. -/
theorem isFaithful_iff_of_nonneg :
    f.IsFaithful ↔ ∀ a : A, 0 ≤ a → f a = 0 → a = 0 := by
  refine ⟨fun hf a ha => ?_,
    fun h a ha => star_mul_self_eq_zero.mp (h _ (star_mul_self_nonneg a) ha)⟩
  rw [StarOrderedRing.nonneg_iff] at ha
  refine (AddSubmonoid.closure_induction (motive := fun x _ => 0 ≤ x ∧ (f x = 0 → x = 0))
    (fun x hx => ?_) ⟨le_rfl, fun _ => rfl⟩ (fun x y _ _ ihx ihy => ?_) ha).2
  · obtain ⟨s, rfl⟩ := hx
    exact ⟨star_mul_self_nonneg s, fun hs => by dsimp only at hs ⊢; rw [hf s hs, mul_zero]⟩
  · refine ⟨add_nonneg ihx.1 ihy.1, fun hxy => ?_⟩
    rw [map_add, add_eq_zero_iff_of_nonneg (f.map_nonneg ihx.1) (f.map_nonneg ihy.1)] at hxy
    rw [ihx.2 hxy.1, ihy.2 hxy.2, add_zero]

/-- Over a proper `StarOrderedRing`, a positive continuous linear map is faithful if and only if it
maps strictly positive elements to strictly positive elements. -/
theorem isFaithful_iff_pos_of_pos :
    f.IsFaithful ↔ ∀ a : A, 0 < a → 0 < f a := by
  rw [isFaithful_iff_of_nonneg]
  refine ⟨fun h a ha => ?_, fun h a ha hfa => ?_⟩
  · exact lt_of_le_of_ne (f.map_nonneg ha.le) fun h0 => ha.ne' (h a ha.le h0.symm)
  · by_contra hne
    exact (h a (lt_of_le_of_ne ha (Ne.symm hne))).ne' hfa

end ProperStarOrdered

end PositiveContinuousLinearMap
