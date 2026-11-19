/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Annihilators of two-sided ideals

For a two-sided ideal `I` of a possibly nonunital associative ring `R`, the left annihilator
`I.annihilator = {a : R | ∀ x ∈ I, a * x = 0}` is again a two-sided ideal: it absorbs
multiplication on the left trivially, and on the right because `I` absorbs multiplication on the
left. It reverses inclusion, sends `I ⊔ J` to `I.annihilator ⊓ J.annihilator`, and contains every
two-sided ideal disjoint from `I`. For a unital ring it is the module annihilator of `I`, viewed as
a left `R`-module, made two-sided.

In a ring with a proper involution (`star x * x = 0` only for `x = 0`), the annihilator of a
self-adjoint ideal `I` behaves like a pseudocomplement: it is self-adjoint, it is also the right
annihilator `{a | ∀ x ∈ I, x * a = 0}`, and it is the largest two-sided ideal disjoint from `I`.
Consequently `I ≤ I.annihilator.annihilator`, the annihilator is unchanged after three
applications, and `I.annihilator = ⊥` exactly when `I` is essential, meaning that `I` meets every
nonzero two-sided ideal. Closed two-sided ideals of C⋆-algebras are self-adjoint, which is how these
results apply there.

## Main declarations

* `TwoSidedIdeal.annihilator`: the left annihilator of a two-sided ideal, as a two-sided ideal.
* `TwoSidedIdeal.annihilator_eq_toTwoSided_annihilator`: for unital rings, the annihilator is the
  two-sided ideal `Module.annihilator R I.asIdeal`.
* `TwoSidedIdeal.IsEssential`: a two-sided ideal meeting every nonzero two-sided ideal.
* `TwoSidedIdeal.mem_annihilator_iff_mul_left`: in a proper star ring, the annihilator of a
  self-adjoint ideal is also its right annihilator.
* `TwoSidedIdeal.le_annihilator_iff_disjoint`: the annihilator of a self-adjoint ideal is the
  largest two-sided ideal disjoint from it.
* `TwoSidedIdeal.annihilator_eq_bot_iff_isEssential`: a self-adjoint ideal is essential exactly when
  its annihilator vanishes.

## References

* B. Blackadar, *Operator Algebras*, II.5.4 (annihilators and essential ideals).
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.1 (essential ideals).
-/

public section

namespace TwoSidedIdeal

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R] {I J : TwoSidedIdeal R} {a : R}

/-- The left annihilator `{a | ∀ x ∈ I, a * x = 0}` of a two-sided ideal `I`, which is a
two-sided ideal. -/
def annihilator (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  .mk' {a | ∀ x ∈ I, a * x = 0} (fun _ _ ↦ zero_mul _)
    (fun ha hb x hx ↦ by rw [add_mul, ha x hx, hb x hx, add_zero])
    (fun ha x hx ↦ by rw [neg_mul, ha x hx, neg_zero])
    (fun {b _} ha x hx ↦ by rw [mul_assoc, ha x hx, mul_zero])
    (fun {_ b} ha x hx ↦ by rw [mul_assoc, ha _ (I.mul_mem_left b x hx)])

@[simp]
theorem mem_annihilator : a ∈ I.annihilator ↔ ∀ x ∈ I, a * x = 0 := by
  simp [annihilator]

theorem mul_eq_zero_of_mem_annihilator {x : R} (ha : a ∈ I.annihilator) (hx : x ∈ I) :
    a * x = 0 :=
  mem_annihilator.1 ha x hx

/-- A two-sided ideal lies in the annihilator of `I` exactly when its elements annihilate `I`
from the left. -/
theorem le_annihilator_iff : J ≤ I.annihilator ↔ ∀ a ∈ J, ∀ x ∈ I, a * x = 0 :=
  forall_congr' fun _ ↦ imp_congr_right fun _ ↦ mem_annihilator

/-- Taking annihilators reverses inclusion. -/
theorem annihilator_antitone : Antitone (annihilator : TwoSidedIdeal R → TwoSidedIdeal R) :=
  fun _ _ hIJ _ ha ↦ mem_annihilator.2 fun _ hx ↦ mul_eq_zero_of_mem_annihilator ha (hIJ hx)

theorem annihilator_le_annihilator (h : I ≤ J) : J.annihilator ≤ I.annihilator :=
  annihilator_antitone h

@[simp]
theorem annihilator_bot : (⊥ : TwoSidedIdeal R).annihilator = ⊤ :=
  eq_top_iff.2 fun a _ ↦ mem_annihilator.2 fun x hx ↦ by
    rw [(mem_bot R).1 hx, mul_zero]

@[simp]
theorem annihilator_sup : (I ⊔ J).annihilator = I.annihilator ⊓ J.annihilator :=
  le_antisymm (le_inf (annihilator_le_annihilator le_sup_left)
      (annihilator_le_annihilator le_sup_right))
    fun a ha ↦ by
      rw [mem_inf R, mem_annihilator, mem_annihilator] at ha
      refine mem_annihilator.2 fun x hx ↦ ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
      rw [mul_add, ha.1 y hy, ha.2 z hz, add_zero]

/-- Every two-sided ideal disjoint from `I` annihilates `I`. -/
theorem le_annihilator_of_disjoint (h : Disjoint J I) : J ≤ I.annihilator :=
  le_annihilator_iff.2 fun a ha x hx ↦ (mem_bot R).1 <|
    h.le_bot ((mem_inf R).2 ⟨J.mul_mem_right a x ha, I.mul_mem_left a x hx⟩)

/-- A two-sided ideal is *essential* when it meets every nonzero two-sided ideal. -/
def IsEssential (I : TwoSidedIdeal R) : Prop :=
  ∀ J : TwoSidedIdeal R, Disjoint I J → J = ⊥

theorem isEssential_iff : I.IsEssential ↔ ∀ J : TwoSidedIdeal R, Disjoint I J → J = ⊥ :=
  Iff.rfl

theorem IsEssential.eq_bot_of_disjoint (hI : I.IsEssential) (h : Disjoint I J) : J = ⊥ :=
  hI J h

theorem isEssential_top : (⊤ : TwoSidedIdeal R).IsEssential :=
  fun _ h ↦ disjoint_top.1 h.symm

theorem IsEssential.mono (hI : I.IsEssential) (h : I ≤ J) : J.IsEssential :=
  fun _ hK ↦ hI _ (hK.mono_left h)

/-- An ideal with zero annihilator is essential. -/
theorem isEssential_of_annihilator_eq_bot (h : I.annihilator = ⊥) : I.IsEssential :=
  fun _ hJ ↦ eq_bot_iff.2 <| h ▸ le_annihilator_of_disjoint hJ.symm

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R)

/-- In a unital ring, the annihilator of a two-sided ideal `I` is the module annihilator of `I`
as a left `R`-module, made two-sided. -/
theorem annihilator_eq_toTwoSided_annihilator :
    I.annihilator = (Module.annihilator R I.asIdeal).toTwoSided := by
  ext a
  simp [Module.mem_annihilator]

@[simp]
theorem annihilator_top : (⊤ : TwoSidedIdeal R).annihilator = ⊥ :=
  eq_bot_iff.2 fun a ha ↦ (mem_bot R).2 <| by
    simpa using mul_eq_zero_of_mem_annihilator ha (mem_top R (x := (1 : R)))

end Ring

section IsProperStar

variable {R : Type*} [NonUnitalRing R] [StarRing R] [IsProperStar R] {I J : TwoSidedIdeal R}
  {a : R}

/-- In a proper star ring, an element annihilating a self-adjoint ideal from the left also
annihilates it from the right. -/
theorem mul_eq_zero_of_star_mem_of_mem_annihilator (hI : ∀ x ∈ I, star x ∈ I)
    (ha : a ∈ I.annihilator) {x : R} (hx : x ∈ I) : x * a = 0 := by
  -- `(x * a) * star (x * a) = x * (a * (star a * star x))`, and `star a * star x ∈ I`.
  rw [← mul_star_self_eq_zero, star_mul, mul_assoc,
    mul_eq_zero_of_mem_annihilator ha (I.mul_mem_left _ _ (hI x hx)), mul_zero]

/-- The annihilator of a self-adjoint ideal is self-adjoint. -/
theorem star_mem_annihilator (hI : ∀ x ∈ I, star x ∈ I) (ha : a ∈ I.annihilator) :
    star a ∈ I.annihilator :=
  mem_annihilator.2 fun x hx ↦ by
    rw [← star_star x, ← star_mul,
      mul_eq_zero_of_star_mem_of_mem_annihilator hI ha (hI x hx), star_zero]

theorem star_mem_annihilator_iff (hI : ∀ x ∈ I, star x ∈ I) :
    star a ∈ I.annihilator ↔ a ∈ I.annihilator :=
  ⟨fun h ↦ star_star a ▸ star_mem_annihilator hI h, star_mem_annihilator hI⟩

/-- In a proper star ring, the annihilator of a self-adjoint ideal is also its right
annihilator. -/
theorem mem_annihilator_iff_mul_left (hI : ∀ x ∈ I, star x ∈ I) :
    a ∈ I.annihilator ↔ ∀ x ∈ I, x * a = 0 := by
  refine ⟨fun ha x hx ↦ mul_eq_zero_of_star_mem_of_mem_annihilator hI ha hx, fun ha ↦ ?_⟩
  rw [← star_mem_annihilator_iff hI]
  exact mem_annihilator.2 fun x hx ↦ by
    rw [← star_star x, ← star_mul, ha _ (hI x hx), star_zero]

/-- A self-adjoint ideal meets its annihilator only in `0`. -/
theorem disjoint_annihilator (hI : ∀ x ∈ I, star x ∈ I) : Disjoint I I.annihilator := by
  refine disjoint_iff.2 <| eq_bot_iff.2 fun a ha ↦ (mem_bot R).2 ?_
  rw [mem_inf R] at ha
  exact mul_star_self_eq_zero.1 (mul_eq_zero_of_mem_annihilator ha.2 (hI a ha.1))

@[simp]
theorem inf_annihilator (hI : ∀ x ∈ I, star x ∈ I) : I ⊓ I.annihilator = ⊥ :=
  disjoint_iff.1 (disjoint_annihilator hI)

/-- The annihilator of a self-adjoint ideal `I` is the largest two-sided ideal disjoint from
`I`. -/
theorem le_annihilator_iff_disjoint (hI : ∀ x ∈ I, star x ∈ I) :
    J ≤ I.annihilator ↔ Disjoint J I :=
  ⟨fun h ↦ (disjoint_annihilator hI).symm.mono_left h, le_annihilator_of_disjoint⟩

theorem le_annihilator_annihilator (hI : ∀ x ∈ I, star x ∈ I) :
    I ≤ I.annihilator.annihilator :=
  le_annihilator_iff_disjoint (fun _ ↦ star_mem_annihilator hI) |>.2 (disjoint_annihilator hI)

@[simp]
theorem annihilator_annihilator_annihilator (hI : ∀ x ∈ I, star x ∈ I) :
    I.annihilator.annihilator.annihilator = I.annihilator :=
  le_antisymm (annihilator_le_annihilator (le_annihilator_annihilator hI))
    (le_annihilator_annihilator fun _ ↦ star_mem_annihilator hI)

/-- In a proper star ring, nothing annihilates the whole ring. -/
@[simp]
theorem annihilator_top_of_isProperStar : (⊤ : TwoSidedIdeal R).annihilator = ⊥ := by
  simpa using inf_annihilator (I := (⊤ : TwoSidedIdeal R)) fun _ _ ↦ mem_top R

/-- A self-adjoint ideal is essential exactly when its annihilator vanishes. -/
theorem annihilator_eq_bot_iff_isEssential (hI : ∀ x ∈ I, star x ∈ I) :
    I.annihilator = ⊥ ↔ I.IsEssential :=
  ⟨isEssential_of_annihilator_eq_bot, fun h ↦ h _ (disjoint_annihilator hI)⟩

end IsProperStar

end TwoSidedIdeal
