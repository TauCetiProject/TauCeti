/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic
public import Mathlib.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.GroupAlgebra.Average

/-!
# The principal block of a group algebra

The augmentation `ε : R[G] → R` restricts to an `R`-algebra homomorphism on the centre `Z(R[G])`
(`TauCeti.centerAugmentation`). Over a domain it sends every central idempotent to `0` or `1`, and
at most one block idempotent to `1`: two block idempotents `e ≠ f` are orthogonal, so
`ε(e) ε(f) = ε(e f) = 0`. Over a field `k` and for a finite group `G`, the block idempotents sum
to `1`, so exactly one of them has augmentation `1`. This is the idempotent of the **principal
block** `B₀(G)` (`TauCeti.principalBlockIdempotent`); every other block idempotent has
augmentation `0`.

The trivial module lies in the principal block: an element `x ∈ k[G]` acts on the trivial
representation as multiplication by `ε(x)` (`Representation.asAlgebraHom_trivial`), so the
principal block idempotent acts as the identity and every other block idempotent acts as `0`.

For the trivial group the augmentation is injective, and the principal block idempotent is `1`.
When `|G|` is invertible in `k`, the principal block idempotent is the averaging idempotent
`|G|⁻¹ ∑ g` (`GroupAlgebra.average`): it is central, and `x e = ε(x) e` for every `x`, so every
central idempotent below it is `0` or `e`. Over `𝔽₂` and for `G = C₃` this is `1 + r + r²`.

## Main definitions

* `TauCeti.centerAugmentation R G`: the augmentation on the centre `Z(R[G])`.
* `TauCeti.principalBlockIdempotent k G`: the block idempotent of augmentation `1`.

## Main results

* `TauCeti.centerAugmentation_eq_zero_or_one`: over a domain, central idempotents have
  augmentation `0` or `1`.
* `TauCeti.IsBlockIdempotent.eq_of_centerAugmentation_eq_one`: at most one block idempotent has
  augmentation `1`.
* `TauCeti.existsUnique_isBlockIdempotent_centerAugmentation_eq_one`: over a field and for a
  finite group, exactly one block idempotent has augmentation `1`.
* `TauCeti.IsBlockIdempotent.eq_principalBlockIdempotent_iff`: a block idempotent is the principal
  one exactly when its augmentation is nonzero.
* `TauCeti.asAlgebraHom_trivial_principalBlockIdempotent`: the principal block idempotent acts as
  the identity on the trivial module, and
  `TauCeti.IsBlockIdempotent.asAlgebraHom_trivial_eq_zero`: every other block idempotent acts as
  `0`.
* `TauCeti.principalBlockIdempotent_eq_one_of_subsingleton`: for the trivial group the principal
  block idempotent is `1`.
* `TauCeti.coe_principalBlockIdempotent_eq_average`: when `|G|` is invertible in `k`, the principal
  block idempotent is `|G|⁻¹ ∑ g`.

## References

* B. Sambale, *Blocks of Finite Groups and Their Invariants*, Lecture Notes in Mathematics 2127,
  Definition 1.2, p. 14.
-/

public section

noncomputable section

namespace TauCeti

open MonoidAlgebra

variable (R G : Type*) [CommRing R] [Monoid G]

/-- The augmentation `ε : R[G] → R`, restricted to the centre `Z(R[G])`, as an `R`-algebra
homomorphism. -/
def centerAugmentation : Subalgebra.center R (MonoidAlgebra R G) →ₐ[R] R :=
  (lift R R G 1).comp (Subalgebra.center R (MonoidAlgebra R G)).val

variable {R G}

@[simp]
theorem centerAugmentation_apply (b : Subalgebra.center R (MonoidAlgebra R G)) :
    centerAugmentation R G b = augmentation R G b := by
  simp [centerAugmentation, lift_one_apply]

/-- Over a domain, the augmentation of a central idempotent is `0` or `1`. -/
theorem centerAugmentation_eq_zero_or_one [IsDomain R]
    {b : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsIdempotentElem b) :
    centerAugmentation R G b = 0 ∨ centerAugmentation R G b = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.mp (hb.map (centerAugmentation R G))

/-- **At most one block idempotent has augmentation `1`**: two block idempotents with nonzero
product are equal, and the product of two block idempotents of augmentation `1` has
augmentation `1`. -/
theorem IsBlockIdempotent.eq_of_centerAugmentation_eq_one
    {b b' : Subalgebra.center R (MonoidAlgebra R G)} (hb : IsBlockIdempotent b)
    (hb' : IsBlockIdempotent b') (h : centerAugmentation R G b = 1)
    (h' : centerAugmentation R G b' = 1) : b = b' :=
  hb.eq_of_commute_of_mul_ne_zero hb' (Commute.all _ _) fun h0 ↦ by
    have := congrArg (centerAugmentation R G) h0
    rw [map_mul, h, h', mul_one, map_zero] at this
    exact hb.ne_zero (by rw [← one_smul R b, this, zero_smul])

/-- **Exactly one block idempotent has augmentation `1`**, over a field and for a finite group:
the augmentations of a complete family of block idempotents are `0` or `1` and sum to `1`. -/
theorem existsUnique_isBlockIdempotent_centerAugmentation_eq_one (k G : Type*) [Field k] [Monoid G]
    [Finite G] :
    ∃! b : Subalgebra.center k (MonoidAlgebra k G),
      IsBlockIdempotent b ∧ centerAugmentation k G b = 1 := by
  obtain ⟨n, e, he, hep⟩ := exists_completeOrthogonalIdempotents_isBlockIdempotent k G
  obtain ⟨i, hi⟩ : ∃ i, centerAugmentation k G (e i) ≠ 0 := by
    by_contra! h
    have := congrArg (centerAugmentation k G) he.complete
    simp [map_sum, h] at this
  have h1 := (centerAugmentation_eq_zero_or_one (he.idem i)).resolve_left hi
  exact ⟨e i, ⟨hep i, h1⟩, fun b hb ↦ hb.1.eq_of_centerAugmentation_eq_one (hep i) hb.2 h1⟩

variable (k G : Type*) [Field k] [Monoid G] [Finite G]

/-- The idempotent of the **principal block** `B₀(G)` of `k[G]`: the unique block idempotent
whose augmentation is `1`. -/
def principalBlockIdempotent : Subalgebra.center k (MonoidAlgebra k G) :=
  (existsUnique_isBlockIdempotent_centerAugmentation_eq_one k G).exists.choose

/-- The principal block idempotent is a block idempotent. -/
theorem isBlockIdempotent_principalBlockIdempotent :
    IsBlockIdempotent (principalBlockIdempotent k G) :=
  (existsUnique_isBlockIdempotent_centerAugmentation_eq_one k G).exists.choose_spec.1

/-- The principal block idempotent has augmentation `1`. -/
theorem centerAugmentation_principalBlockIdempotent :
    centerAugmentation k G (principalBlockIdempotent k G) = 1 :=
  (existsUnique_isBlockIdempotent_centerAugmentation_eq_one k G).exists.choose_spec.2

/-- The principal block idempotent has augmentation `1`, as an element of `k[G]`. -/
@[simp]
theorem augmentation_principalBlockIdempotent :
    augmentation k G (principalBlockIdempotent k G : MonoidAlgebra k G) = 1 := by
  rw [← centerAugmentation_apply, centerAugmentation_principalBlockIdempotent]

variable {k G}

/-- A block idempotent is the principal block idempotent exactly when its augmentation is
nonzero. -/
theorem IsBlockIdempotent.eq_principalBlockIdempotent_iff
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) :
    b = principalBlockIdempotent k G ↔ centerAugmentation k G b ≠ 0 := by
  refine ⟨fun h ↦ by rw [h, centerAugmentation_principalBlockIdempotent]; exact one_ne_zero,
    fun h ↦ ?_⟩
  exact hb.eq_of_centerAugmentation_eq_one (isBlockIdempotent_principalBlockIdempotent k G)
    ((centerAugmentation_eq_zero_or_one hb.isIdempotentElem).resolve_left h)
    (centerAugmentation_principalBlockIdempotent k G)

/-- Every block idempotent other than the principal one has augmentation `0`. -/
theorem IsBlockIdempotent.centerAugmentation_eq_zero
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (hne : b ≠ principalBlockIdempotent k G) : centerAugmentation k G b = 0 := by
  by_contra h
  exact hne (hb.eq_principalBlockIdempotent_iff.mpr h)

/-- **The trivial module lies in the principal block**: the principal block idempotent acts on
the trivial representation as the identity. -/
theorem asAlgebraHom_trivial_principalBlockIdempotent :
    (Representation.trivial k G k).asAlgebraHom (principalBlockIdempotent k G) = 1 := by
  rw [Representation.asAlgebraHom_trivial, augmentation_principalBlockIdempotent, one_smul]

/-- Every block idempotent other than the principal one acts on the trivial representation as
`0`. -/
theorem IsBlockIdempotent.asAlgebraHom_trivial_eq_zero
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (hne : b ≠ principalBlockIdempotent k G) :
    (Representation.trivial k G k).asAlgebraHom b = 0 := by
  rw [Representation.asAlgebraHom_trivial, ← centerAugmentation_apply,
    hb.centerAugmentation_eq_zero hne, zero_smul]

/-- **The principal block of the trivial group** is `1`: for a group with one element the
augmentation is injective. -/
theorem principalBlockIdempotent_eq_one_of_subsingleton [Subsingleton G] :
    principalBlockIdempotent k G = 1 := by
  have h : augmentation k G = (uniqueRingEquiv (R := k) G).toRingHom :=
    ringHom_ext (by simp) fun g ↦ by simp [Subsingleton.elim g 1]
  refine Subtype.ext ((uniqueRingEquiv G).injective ?_)
  simpa using (RingHom.congr_fun h (principalBlockIdempotent k G)).symm

section Average

variable {k G : Type*} [Field k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]

variable (k G) in
/-- **The principal block when `|G|` is invertible**: the principal block idempotent of `k[G]` is
the averaging idempotent `|G|⁻¹ ∑ g`. -/
theorem coe_principalBlockIdempotent_eq_average :
    (principalBlockIdempotent k G : MonoidAlgebra k G) = GroupAlgebra.average k G := by
  let a : Subalgebra.center k (MonoidAlgebra k G) := ⟨_, GroupAlgebra.average_mem_center⟩
  have ha : IsBlockIdempotent a := by
    refine isPrimitiveIdempotent_of_eq_zero_or_eq
      (Subtype.ext (by rw [Subalgebra.coe_mul]; exact GroupAlgebra.isIdempotentElem_average k G))
      (fun h ↦ ?_) fun f hf h _ ↦ ?_
    · simpa [a] using congrArg (augmentation k G ∘ Subtype.val) h
    · have hf' : (f : MonoidAlgebra k G) = augmentation k G f • GroupAlgebra.average k G := by
        rw [← GroupAlgebra.average_mul]
        simpa [a, Subalgebra.coe_mul] using congrArg Subtype.val h.symm
      rcases centerAugmentation_eq_zero_or_one hf with h0 | h1
      · exact Or.inl (Subtype.ext (by
          rw [hf', ← centerAugmentation_apply, h0, zero_smul, ZeroMemClass.coe_zero]))
      · exact Or.inr (Subtype.ext (by rw [hf', ← centerAugmentation_apply, h1, one_smul]))
  exact congrArg Subtype.val (ha.eq_principalBlockIdempotent_iff.mpr (by simp [a])).symm

end Average

end TauCeti
