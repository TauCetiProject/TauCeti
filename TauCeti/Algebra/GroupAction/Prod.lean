/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Prod
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Independent product actions and their orbit spaces

For actions of `G` on `X` and `K` on `Y`, the independent action of `G × K` on `X × Y` acts
coordinatewise. It is scoped to avoid competing with the diagonal action when both are available.
Use `open scoped TauCeti.IndependentProd` for this action. Its orbit space is canonically
equivalent to the product of the two orbit spaces, using Mathlib's `Setoid.prodQuotientEquiv`.
-/

public section

namespace TauCeti.IndependentProd

variable {G K X Y : Type*}

/-- The independent product scalar action, scoped to avoid competing with diagonal actions. -/
@[to_additive /-- The independent product additive action, scoped to avoid competing with
 diagonal actions. -/]
scoped instance smul [SMul G X] [SMul K Y] : SMul (G × K) (X × Y) where
  smul g x := (g.1 • x.1, g.2 • x.2)

open scoped TauCeti.IndependentProd

section SMul

variable [SMul G X] [SMul K Y]

/-- The independent product action acts on each coordinate. Use this as a named rewrite to expand
an abstract pair; simplification preserves the action and computes projections and constructors. -/
@[to_additive /-- The independent product additive action acts on each
coordinate. Use this as a named rewrite to expand an abstract pair; simplification preserves the
action and computes projections and constructors. -/]
theorem smul_def (g : G × K) (x : X × Y) : g • x = (g.1 • x.1, g.2 • x.2) := (rfl)

/- These rules run before generic product normalization, preserving the original component
actions in the resulting expressions. -/

/-- The first coordinate of the independent product action is the first action. -/
@[to_additive (attr := simp↓) /-- The first coordinate of the independent product additive action
is the first action. -/]
theorem smul_fst (g : G × K) (x : X × Y) : (g • x).1 = g.1 • x.1 := (rfl)

/-- The second coordinate of the independent product action is the second action. -/
@[to_additive (attr := simp↓) /-- The second coordinate of the independent product additive action
is the second action. -/]
theorem smul_snd (g : G × K) (x : X × Y) : (g • x).2 = g.2 • x.2 := (rfl)

/-- The independent product action on a constructed pair acts coordinatewise. -/
@[to_additive (attr := simp↓) /-- The independent product additive action on a constructed pair
acts coordinatewise. -/]
theorem smul_mk (g : G × K) (x : X) (y : Y) : g • (x, y) = (g.1 • x, g.2 • y) := (rfl)

/-- Independent products of left-cancellative scalar actions are left-cancellative. -/
@[to_additive /-- Independent products of left-cancellative additive actions are
left-cancellative. -/]
scoped instance isLeftCancelSMul [IsLeftCancelSMul G X] [IsLeftCancelSMul K Y] :
    IsLeftCancelSMul (G × K) (X × Y) where
  left_cancel' g x y h := Prod.ext
    (IsLeftCancelSMul.left_cancel g.1 x.1 y.1 (congrArg Prod.fst h))
    (IsLeftCancelSMul.left_cancel g.2 x.2 y.2 (congrArg Prod.snd h))

/-- Independent products of cancellative scalar actions are cancellative. -/
@[to_additive /-- Independent products of cancellative additive actions are cancellative. -/]
scoped instance isCancelSMul [IsCancelSMul G X] [IsCancelSMul K Y] :
    IsCancelSMul (G × K) (X × Y) where
  right_cancel' g h x hx := Prod.ext
    (IsCancelSMul.right_cancel g.1 h.1 x.1 (congrArg Prod.fst hx))
    (IsCancelSMul.right_cancel g.2 h.2 x.2 (congrArg Prod.snd hx))

end SMul

/-- The independent product action, obtained by restricting the two actions along the monoid
projections and taking their product, with the independent product scalar action. -/
@[to_additive /-- The independent product additive action, obtained by restricting the two
actions along the additive monoid projections and taking their product. -/]
scoped instance mulAction [Monoid G] [Monoid K] [MulAction G X] [MulAction K Y] :
    MulAction (G × K) (X × Y) :=
  { @Prod.mulAction (G × K) X Y _
      (MulAction.compHom X (MonoidHom.fst G K)) (MulAction.compHom Y (MonoidHom.snd G K)) with
    toSMul := smul }

end TauCeti.IndependentProd

namespace TauCeti

open scoped IndependentProd

variable {G K X Y : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]

/-- The orbit relation of the independent product action is the product of the orbit relations. -/
@[to_additive AddAction.orbitRel_prod /-- The orbit relation of the independent product additive
action is the product of the orbit relations. -/]
theorem MulAction.orbitRel_prod :
    MulAction.orbitRel (G × K) (X × Y) =
      (MulAction.orbitRel G X).prod (MulAction.orbitRel K Y) := by
  ext x y
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨⟨g.1, congrArg Prod.fst hg⟩, ⟨g.2, congrArg Prod.snd hg⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨k, hk⟩⟩
    exact ⟨(g, k), Prod.ext hg hk⟩

/-- The orbit space of the independent product action is the product of the orbit spaces. -/
@[to_additive AddAction.orbitRelQuotientProdEquiv /-- The orbit space of the independent
product additive action is the product of the orbit spaces. -/]
def MulAction.orbitRelQuotientProdEquiv :
    MulAction.orbitRel.Quotient (G × K) (X × Y) ≃
      MulAction.orbitRel.Quotient G X × MulAction.orbitRel.Quotient K Y :=
  (Quotient.congrRight fun x y ↦ by rw [MulAction.orbitRel_prod]).trans
    (Setoid.prodQuotientEquiv _ _).symm

/-- The product comparison sends the orbit of a pair to its two component orbits. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdEquiv_mk /-- The product comparison
sends the orbit of a pair to its two component orbits. -/]
theorem MulAction.orbitRelQuotientProdEquiv_mk (x : X × Y) :
    MulAction.orbitRelQuotientProdEquiv (G := G) (K := K) (Quotient.mk _ x) =
      (Quotient.mk _ x.1, Quotient.mk _ x.2) := (rfl)

/-- The inverse product comparison sends a pair of orbits to the orbit of a pair. -/
@[to_additive (attr := simp) AddAction.orbitRelQuotientProdEquiv_symm_mk /-- The inverse product
comparison sends a pair of orbits to the orbit of a pair. -/]
theorem MulAction.orbitRelQuotientProdEquiv_symm_mk (x : X) (y : Y) :
    (MulAction.orbitRelQuotientProdEquiv (G := G) (K := K)).symm
      (Quotient.mk _ x, Quotient.mk _ y) = Quotient.mk _ (x, y) := (rfl)

/-- Descent of a product of independently invariant maps is the product of their descents,
through the canonical comparison of orbit spaces. -/
@[to_additive AddAction.orbitRelQuotientLift_prodMap /-- Descent of a product of independently
invariant maps is the product of their descents, through the orbit-space comparison. -/]
theorem MulAction.orbitRelQuotientLift_prodMap {Z W : Type*} (f : X → Z) (g : Y → W)
    (hf : ∀ a : G, ∀ x, f (a • x) = f x) (hg : ∀ a : K, ∀ y, g (a • y) = g y) :
    MulAction.orbitRelQuotientLift (Prod.map f g)
        (fun (a : G × K) (x : X × Y) ↦ Prod.ext (hf a.1 x.1) (hg a.2 x.2)) =
      Prod.map (MulAction.orbitRelQuotientLift f hf) (MulAction.orbitRelQuotientLift g hg) ∘
        MulAction.orbitRelQuotientProdEquiv := by
  funext q
  induction q using Quotient.inductionOn with | h x =>
  rcases x with ⟨x, y⟩
  simp

end TauCeti
