/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import TauCeti.Algebra.Group.Pi.Finset
public import TauCeti.Logic.Equiv.Pi

/-!
# Linear equivalences of products indexed by finite sets and by relabelled index types

For disjoint finite sets `s` and `t` of indices and a family of modules `M i`, gluing a family on
`s` and a family on `t` into a family on `s ∪ t` is a linear equivalence
`LinearEquiv.piFinsetUnion R M h : (∀ i : s, M i) × (∀ i : t, M i) ≃ₗ[R] ∀ i : s ∪ t, M i`; it is
`Equiv.piFinsetUnion` as a linear map, so its inverse takes the restrictions to `s` and to `t`.
Relabelling the factors of `∀ i, M i` along an equivalence `e₁` of index types and then along
`e₂` is relabelling them along `e₁.trans e₂` (`LinearEquiv.piCongrLeft_trans`).

These are the identifications `E_(I ⊔ J) ≅ E_I ⊕ E_J` and `E_I ≅ E_(e I)` of the direct sums
`E_I = ⊕_(α ∈ I) E_α` attached to finite sets `I` of charts of an implicit atlas, in the sense of
Pardon.

## Main definitions

* `LinearEquiv.piFinsetUnion`: `Equiv.piFinsetUnion` as a linear equivalence.

## Main results

* `LinearEquiv.piCongrLeft_symm_apply`: the inverse of relabelling reads coordinates through the
  relabelling.
* `LinearEquiv.piCongrLeft_trans`: relabelling along two equivalences in turn is relabelling
  along their composite.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Definition 3.1.1.
-/

public section

namespace LinearEquiv

variable (R : Type*) [Semiring R] {ι : Type*} (M : ι → Type*) [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

/-- The inverse of relabelling along `e` reads the coordinate at `i'` from `e i'`. -/
@[simp]
theorem piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (f : ∀ i, M i) (i' : ι') :
    (piCongrLeft R M e).symm f i' = f (e i') :=
  (rfl)

/-- Relabelling the factors along `e₁` and then along `e₂` is relabelling them along
`e₁.trans e₂`. -/
theorem piCongrLeft_trans {ι' ι'' : Type*} (e₁ : ι'' ≃ ι') (e₂ : ι' ≃ ι) :
    (piCongrLeft R (fun i' ↦ M (e₂ i')) e₁).trans (piCongrLeft R M e₂) =
      piCongrLeft R M (e₁.trans e₂) :=
  toEquiv_injective (Equiv.piCongrLeft_trans M e₁ e₂)

variable [DecidableEq ι] {s t : Finset ι}

/-- Gluing a family on `s` and a family on `t` into a family on `s ∪ t`, for disjoint `s` and
`t`. This is `Equiv.piFinsetUnion` as a `LinearEquiv`. -/
def piFinsetUnion (h : Disjoint s t) :
    ((∀ i : s, M i) × ∀ i : t, M i) ≃ₗ[R] ∀ i : (s ∪ t : Finset ι), M i where
  toEquiv := Equiv.piFinsetUnion M h
  map_add' x y := by simpa using map_add (AddEquiv.piFinsetUnion M h) x y
  map_smul' c x := Finset.restrict₂_union_injective
    ((Equiv.restrict₂_piFinsetUnion_left M h (c • x)).trans
      (congr_arg (c • ·) (Equiv.restrict₂_piFinsetUnion_left M h x).symm))
    ((Equiv.restrict₂_piFinsetUnion_right M h (c • x)).trans
      (congr_arg (c • ·) (Equiv.restrict₂_piFinsetUnion_right M h x).symm))

@[simp]
theorem coe_piFinsetUnion (h : Disjoint s t) :
    ⇑(piFinsetUnion R M h) = Equiv.piFinsetUnion M h :=
  (rfl)

@[simp]
theorem coe_piFinsetUnion_symm (h : Disjoint s t) :
    ⇑(piFinsetUnion R M h).symm = (Equiv.piFinsetUnion M h).symm :=
  (rfl)

end LinearEquiv
