/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Fin.Basic

/-!
# The extended Dynkin quiver of type `D~`

For `m : ℕ`, the quiver `TauCeti.Quiver.AffineD m` has a *spine* of `m + 1` vertices
`spine 0 → spine 1 → ⋯ → spine m`, joined by one arrow from each spine vertex to the next, and
four *leaves*: the leaves `0` and `1` each carry one arrow into the first spine vertex `spine 0`,
and the leaves `2` and `3` each carry one arrow into the last spine vertex `spine m`. Its
underlying graph is the extended Dynkin diagram `D~ₘ₊₄`, on `m + 5` vertices, in one fixed
orientation. For `m = 0` the spine is a single vertex receiving all four arrows, and the quiver is
the four subspace quiver `TauCeti.Quiver.Subspace (Fin 4)` of the extended Dynkin diagram `D~₄`.

This file carries the vertex and arrow data alone; the representation theory, that the quiver has
infinite representation type, is in `TauCeti.RepresentationTheory.Quiver.AffineD.FiniteRepType`.

## Main definitions

* `TauCeti.Quiver.AffineD`: the vertex type, with constructors `leaf` and `spine`, and a `Quiver`
  instance.
* `TauCeti.Quiver.AffineD.vertexEquiv`: the vertices as `Fin 4 ⊕ Fin (m + 1)`, so that there are
  `m + 5` of them (`TauCeti.Quiver.AffineD.card_eq`).
* `TauCeti.Quiver.AffineD.leafTarget`: the spine vertex a leaf is attached to.
* `TauCeti.Quiver.AffineD.leafArrow` and `TauCeti.Quiver.AffineD.spineArrow`: the arrow from a
  leaf into the spine, and the arrow from a spine vertex to the next one.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

namespace Quiver

/-- The extended Dynkin quiver `D~ₘ₊₄`: a spine of `m + 1` vertices with an arrow from each to the
next, and four leaves, two attached by an arrow into each end of the spine. -/
inductive AffineD (m : ℕ) : Type
  | /-- The leaf indexed by `i`, the tail of a single arrow into an end of the spine. -/
    leaf (i : Fin 4) : AffineD m
  | /-- The spine vertex indexed by `j`. -/
    spine (j : Fin (m + 1)) : AffineD m
  deriving DecidableEq

namespace AffineD

variable {m : ℕ}

/-! ### The `m + 5` vertices -/

variable (m) in
/-- The vertices of `TauCeti.Quiver.AffineD m` as `Fin 4 ⊕ Fin (m + 1)`: the leaves on the left,
the spine on the right. -/
def vertexEquiv : AffineD m ≃ Fin 4 ⊕ Fin (m + 1) where
  toFun
    | .leaf i => .inl i
    | .spine j => .inr j
  invFun
    | .inl i => leaf i
    | .inr j => spine j
  left_inv v := by cases v <;> rfl
  right_inv s := by cases s <;> rfl

instance : Fintype (AffineD m) := Fintype.ofEquiv _ (vertexEquiv m).symm

/-- `TauCeti.Quiver.AffineD m` has `m + 5` vertices, as the extended Dynkin diagram `D~ₘ₊₄`
should. -/
@[simp]
theorem card_eq : Fintype.card (AffineD m) = m + 5 := by
  rw [Fintype.card_congr (vertexEquiv m), Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

/-! ### The arrows -/

variable (m) in
/-- The spine vertex a leaf is attached to: the first one for the leaves `0` and `1`, the last one
for the leaves `2` and `3`. -/
def leafTarget (i : Fin 4) : Fin (m + 1) :=
  if (i : ℕ) < 2 then 0 else Fin.last m

instance : _root_.Quiver.{0} (AffineD m) where
  Hom a b :=
    match a, b with
    | .leaf i, .spine j => PLift (j = leafTarget m i)
    | .spine j, .spine j' => PLift ((j' : ℕ) = j + 1)
    | _, _ => PEmpty

variable (m) in
/-- The arrow from the leaf indexed by `i` into the spine vertex it is attached to. -/
def leafArrow (i : Fin 4) : leaf i ⟶ spine (leafTarget m i) := PLift.up rfl

/-- The arrow from the spine vertex indexed by `j` to the next one. -/
def spineArrow (j : Fin m) : spine j.castSucc ⟶ (spine j.succ : AffineD m) := PLift.up rfl

instance (i i' : Fin 4) : IsEmpty ((leaf i : AffineD m) ⟶ leaf i') :=
  inferInstanceAs (IsEmpty PEmpty)

instance (j : Fin (m + 1)) (i : Fin 4) : IsEmpty ((spine j : AffineD m) ⟶ leaf i) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- Between any two vertices of `TauCeti.Quiver.AffineD m` there is at most one arrow. -/
instance instSubsingletonHom : ∀ a b : AffineD m, Subsingleton (a ⟶ b)
  | .leaf _, .spine _ => inferInstanceAs (Subsingleton (PLift _))
  | .spine _, .spine _ => inferInstanceAs (Subsingleton (PLift _))
  | .leaf _, .leaf _ => inferInstanceAs (Subsingleton PEmpty)
  | .spine _, .leaf _ => inferInstanceAs (Subsingleton PEmpty)

end AffineD

end Quiver

end TauCeti
