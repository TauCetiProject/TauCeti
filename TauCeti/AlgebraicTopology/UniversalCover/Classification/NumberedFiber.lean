/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.FundamentalGroupAction
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Transport
import Mathlib.Algebra.Group.Action.TransferInstance
-- The realisation proof uses the defining equation of `Equiv.permutationRepresentation`.
import all TauCeti.Algebra.GroupAction.PermutationRepresentation
import TauCeti.Topology.Covering.Clopen
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Basic
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Monodromy
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# Numbered, pointed and bare connected covers of degree `n`

A connected cover of degree `n` over a basepoint `x` can be rigidified in three ways, and each
rigidification has its own notion of isomorphism:

* a **fibre-numbered** cover `TauCeti.ConnectedFiberNumberedCover x n` carries a numbering
  `ν : p ⁻¹' {x} ≃ Fin n` of the fibre, and its isomorphisms preserve the label of every point of
  the fibre;
* a **pointed** cover `TauCeti.ConnectedPointedCover x n` carries one point of the fibre, and its
  isomorphisms preserve that point;
* a **bare** cover `TauCeti.ConnectedCover x n` carries neither, and its isomorphisms are all
  isomorphisms of covers.

All three are built on `TauCeti.ConnectedCoveringSpace X`. The degree is a parameter rather than
something recovered afterwards: it is the cardinality of the fibre over `x`, recorded by the
numbering itself or by the existence of one. Isomorphism is an equivalence relation in each case,
and the three types of isomorphism classes are the quotients
`TauCeti.ConnectedFiberNumberedCoverClass`, `TauCeti.ConnectedPointedCoverClass` and
`TauCeti.ConnectedCoverClass`.

The rigidifications are related by forgetful maps — forgetting the numbering, keeping only the
point with a given label, forgetting the point — which descend to isomorphism classes and form a
commuting triangle. The symmetric group `Equiv.Perm (Fin n)` acts on numberings by relabelling,
`τ • ν = ν.trans τ`. The forgetful maps have these orbit descriptions:

* two numbered classes have the same underlying cover exactly when they differ by a relabelling,
  so the bare classes are the relabelling orbits of the numbered ones
  (`TauCeti.ConnectedFiberNumberedCoverClass.orbitRelQuotientEquiv`);
* two marked numbered classes give the same pointed class exactly when a relabelling carries one
  to the other and carries its marked label to the other label, so the pointed classes are the
  orbits of the diagonal action on numbered classes paired with a label
  (`TauCeti.ConnectedFiberNumberedCoverClass.markedOrbitRelQuotientEquiv`).

These are the covering-space counterparts of the passage from literal permutation triples to
their simultaneous-conjugacy classes (`TauCeti.ConnectedIsoClass`) and to marked triples modulo
the diagonal action: a classification of numbered covers that is equivariant for relabelling
therefore descends to the other two rigidifications.

Over a path-connected base the degree does not depend on the basepoint, and over a preconnected
base a connected cover has positive degree.

The basepoint can be moved. A bare cover at `x₀` is a bare cover at any point of the connected
component of `x₀`, with no choice involved. A numbered cover is moved along a path `γ` from `x₀` to
`x₁`: lifting `γ` identifies the two fibres, so the numbering of the fibre over `x₀` induces one of
the fibre over `x₁`, and the numbered monodromy of `π₁(X, x₁)` is that of `π₁(X, x₀)` read through
the change of basepoint along `γ`.

Over a path-connected, locally path-connected base, a numbered cover is determined up to
isomorphism by its monodromy representation read through the numbering,
`π₁(X, x) →* Equiv.Perm (Fin n)`: taking the fibre over `x` with its monodromy action is faithful
and full (`TauCeti.CoveringSpace.fiberActionFunctor_faithful`,
`TauCeti.CoveringSpace.fiberActionFunctor_full`), and the numberings turn equal representations
into an isomorphism of `π₁(X, x)`-sets preserving the labels.

Conversely, over a locally path-connected, semilocally simply connected base, every
representation `π₁(X, x) →* Equiv.Perm (Fin n)` with `n ≠ 0` and transitive image is the numbered
monodromy of some numbered cover: the realisation theorem for transitive fundamental-group sets
(`TauCeti.ConnectedCoveringSpace.exists_fiberAction_iso`) supplies a connected cover whose fibre
is equivariantly identified with the finite set, and that identification is a numbering.

A deck transformation of a numbered cover permutes the fibre, hence the labels
(`TauCeti.ConnectedFiberNumberedCover.deckPerm`). Over a preconnected base this determines the deck
transformation, and over a path-connected, locally path-connected base the permutations so obtained
are exactly those commuting with the numbered monodromy: a permutation `τ` commuting with it leaves
the numbered monodromy of the relabelled cover unchanged, so some isomorphism from the cover to its
relabelling preserves every label, and that isomorphism is a deck transformation inducing `τ`.
Relabelling the fibre conjugates the induced permutations.

## Main declarations

* `TauCeti.ConnectedFiberNumberedCover`, `TauCeti.ConnectedPointedCover`,
  `TauCeti.ConnectedCover`: the three carriers.
* `TauCeti.ConnectedFiberNumberedCoverIso`, `TauCeti.ConnectedPointedCoverIso`: the isomorphism
  relations of numbered and pointed covers, with setoids
  `TauCeti.connectedFiberNumberedCoverSetoid` and `TauCeti.connectedPointedCoverSetoid`. Bare covers
  are related by `CategoryTheory.IsIsomorphic` of their underlying covers, with setoid
  `TauCeti.connectedCoverSetoid`.
* `TauCeti.ConnectedFiberNumberedCoverClass`, `TauCeti.ConnectedPointedCoverClass`,
  `TauCeti.ConnectedCoverClass`: the types of isomorphism classes.
* `forgetNumbering`, `markLabel`, `forgetPoint`: the forgetful maps, on carriers and on classes,
  with `TauCeti.ConnectedFiberNumberedCoverClass.forgetPoint_markLabel`.
* `TauCeti.ConnectedFiberNumberedCoverClass.forgetNumbering_eq_forgetNumbering_iff` and
  `TauCeti.ConnectedFiberNumberedCoverClass.orbitRelQuotientEquiv`: bare classes are relabelling
  orbits of numbered classes.
* `TauCeti.ConnectedFiberNumberedCoverClass.markLabel_eq_markLabel_iff` and
  `TauCeti.ConnectedFiberNumberedCoverClass.markedOrbitRelQuotientEquiv`: pointed classes are
  diagonal orbits of marked numbered classes.
* `TauCeti.ConnectedCover.nonempty_equiv_fin_of_mem_connectedComponent`: the degree is the same
  over the whole connected component of the base point;
  `TauCeti.ConnectedCover.ne_zero`: over a preconnected base the degree is positive.
* `TauCeti.ConnectedFiberNumberedCover.basepointChange`, `TauCeti.ConnectedCover.basepointChange`,
  `TauCeti.ConnectedCoverClass.basepointChange`: moving the basepoint, with
  `TauCeti.ConnectedFiberNumberedCover.permCongrHom_comp_monodromyPerm_basepointChange` computing
  the numbered monodromy of the moved cover.
* `TauCeti.connectedFiberNumberedCoverIso_iff_permCongrHom_comp_monodromyPerm_eq`: two numbered
  covers are isomorphic exactly when their numbered monodromy representations agree.
* `TauCeti.ConnectedFiberNumberedCover.exists_permCongrHom_comp_monodromyPerm_eq`: over a
  semilocally simply connected base, every transitive representation on `Fin n` is the numbered
  monodromy of some numbered cover.
* `TauCeti.ConnectedFiberNumberedCover.deckPerm`: the permutation of the labels induced by a deck
  transformation, with `deckPerm_injective` and `deckPerm_smul`.
* `TauCeti.ConnectedFiberNumberedCover.range_deckPerm`: the induced permutations are exactly those
  commuting with the numbered monodromy.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (isomorphism of
  covering spaces, the change of basepoint within a fibre, and deck transformations).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7 (the monodromy of a cover is well defined up to the numbering of the fibre).
-/

public section

open CategoryTheory Equiv

universe u

namespace TauCeti

variable {X : TopCat.{u}}

/-! ### The three carriers -/

/-- A connected covering space of `X` of degree `n`, with its fibre over `x` numbered by
`Fin n`. This is the rigidification at which the monodromy of the cover is a literal action of
`π₁(X, x)` on `Fin n`, rather than an action up to relabelling. -/
structure ConnectedFiberNumberedCover (x : X) (n : ℕ) where
  /-- The underlying connected covering space. -/
  cover : ConnectedCoveringSpace X
  /-- The numbering of the fibre over the basepoint. -/
  ν : ⇑cover.proj ⁻¹' {x} ≃ Fin n

/-- A connected covering space of `X` of degree `n` with one chosen point of its fibre over `x`.
Only that point is rigidified: the relabellings of the fibre fixing it survive. -/
structure ConnectedPointedCover (x : X) (n : ℕ) where
  /-- The underlying connected covering space. -/
  cover : ConnectedCoveringSpace X
  /-- The chosen point of the fibre over the basepoint. -/
  e : ⇑cover.proj ⁻¹' {x}
  /-- The fibre over the basepoint has `n` points. -/
  nonempty_equiv_fin : Nonempty (⇑cover.proj ⁻¹' {x} ≃ Fin n)

/-- A connected covering space of `X` whose fibre over `x` has `n` points, with no further
rigidification. Two such covers are equal exactly when their underlying covers are
(`TauCeti.ConnectedCover.ext`). -/
@[ext]
structure ConnectedCover (x : X) (n : ℕ) where
  /-- The underlying connected covering space. -/
  cover : ConnectedCoveringSpace X
  /-- The fibre over the basepoint has `n` points. -/
  nonempty_equiv_fin : Nonempty (⇑cover.proj ⁻¹' {x} ≃ Fin n)

variable {x : X} {n : ℕ}

/-- The homeomorphism of total spaces underlying an isomorphism of connected covers. -/
private def coverHomeomorph {p q : ConnectedCoveringSpace X} (f : p ≅ q) :
    (p : TopCat) ≃ₜ (q : TopCat) :=
  TopCat.homeoOfIso ((CoveringSpace.FullSubcategory.totalSpace X _).mapIso f)

private theorem coverHomeomorph_apply {p q : ConnectedCoveringSpace X} (f : p ≅ q)
    (e : (p : TopCat)) : coverHomeomorph f e = f.hom.hom.left e :=
  rfl

private theorem proj_coverHomeomorph {p q : ConnectedCoveringSpace X} (f : p ≅ q)
    (e : (p : TopCat)) : q.proj (coverHomeomorph f e) = p.proj e :=
  ConcreteCategory.congr_hom (CoveringSpace.FullSubcategory.w f.hom) e

/-- The bijection between the fibres over `x` induced by an isomorphism of connected covers.

This is the bijection underlying
`(CoveringSpace.fiberActionFunctor x).mapIso ((ConnectedCoveringSpace.forget X).mapIso f)`,
rebuilt from `Deck.fiberMap` because that functor acts on points only up to a lemma
(`CoveringSpace.fiberActionFunctor_map_hom`), while here the value at a point is definitionally
`f.hom.hom.left` (`coe_fiberEquiv_apply`). -/
private def fiberEquiv {p q : ConnectedCoveringSpace X} (f : p ≅ q) :
    ⇑p.proj ⁻¹' {x} ≃ ⇑q.proj ⁻¹' {x} :=
  (Deck.fiberMap (coverHomeomorph f) (proj_coverHomeomorph f) x).toEquiv

private theorem coe_fiberEquiv_apply {p q : ConnectedCoveringSpace X} (f : p ≅ q)
    (e : ⇑p.proj ⁻¹' {x}) : (fiberEquiv f e : (q : TopCat)) = f.hom.hom.left e.1 :=
  rfl

/-- The identity isomorphism of covers acts on total-space points as the identity. -/
private theorem coverMap_id_apply (p : ConnectedCoveringSpace X) (e : (p : TopCat)) :
    (Iso.refl p).hom.hom.left e = e :=
  rfl

/-- A composite of cover morphisms acts on total-space points as the composite of the maps. -/
private theorem coverMap_comp_apply {p q r : ConnectedCoveringSpace X}
    (f : p ⟶ q) (g : q ⟶ r) (e : (p : TopCat)) :
    (f ≫ g).hom.left e = g.hom.left (f.hom.left e) :=
  rfl

/-- The two directions of an isomorphism of covers cancel on total-space points. -/
private theorem coverMap_inv_apply {p q : ConnectedCoveringSpace X}
    (f : p ≅ q) (e : (q : TopCat)) :
    f.hom.hom.left (f.inv.hom.left e) = e :=
  Iso.inv_hom_id_apply ((CoveringSpace.FullSubcategory.totalSpace X _).mapIso f) e

/-! ### Isomorphisms -/

/-- Two fibre-numbered covers are isomorphic when some isomorphism of the underlying covers carries
the point labelled `i` to the point labelled `i`, for every label `i`. -/
def ConnectedFiberNumberedCoverIso (c c' : ConnectedFiberNumberedCover x n) : Prop :=
  ∃ f : c.cover ≅ c'.cover, ∀ i, f.hom.hom.left (c.ν.symm i).1 = (c'.ν.symm i).1

/-- Two pointed covers are isomorphic when some isomorphism of the underlying covers carries the
chosen point to the chosen point. -/
def ConnectedPointedCoverIso (c c' : ConnectedPointedCover x n) : Prop :=
  ∃ f : c.cover ≅ c'.cover, f.hom.hom.left c.e.1 = c'.e.1

/-- A numbered isomorphism consists of a cover isomorphism preserving every fibre label. -/
theorem connectedFiberNumberedCoverIso_iff_exists {c c' : ConnectedFiberNumberedCover x n} :
    ConnectedFiberNumberedCoverIso c c' ↔
      ∃ f : c.cover ≅ c'.cover, ∀ i, f.hom.hom.left (c.ν.symm i).1 = (c'.ν.symm i).1 :=
  Iff.rfl

/-- A pointed isomorphism consists of a cover isomorphism preserving the chosen point. -/
theorem connectedPointedCoverIso_iff_exists {c c' : ConnectedPointedCover x n} :
    ConnectedPointedCoverIso c c' ↔
      ∃ f : c.cover ≅ c'.cover, f.hom.hom.left c.e.1 = c'.e.1 :=
  Iff.rfl

namespace ConnectedFiberNumberedCoverIso

/-- Every fibre-numbered cover is isomorphic to itself, by the identity. -/
@[refl]
theorem refl (c : ConnectedFiberNumberedCover x n) : ConnectedFiberNumberedCoverIso c c :=
  ⟨Iso.refl _, fun _ => coverMap_id_apply _ _⟩

/-- Label-preserving isomorphism of fibre-numbered covers is symmetric. -/
@[symm]
theorem symm {c c' : ConnectedFiberNumberedCover x n} (h : ConnectedFiberNumberedCoverIso c c') :
    ConnectedFiberNumberedCoverIso c' c := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, fun i => ?_⟩
  rw [← hf i]
  exact coverMap_inv_apply f.symm _

/-- Label-preserving isomorphism of fibre-numbered covers is transitive. -/
@[trans]
theorem trans {c c' c'' : ConnectedFiberNumberedCover x n}
    (h : ConnectedFiberNumberedCoverIso c c') (h' : ConnectedFiberNumberedCoverIso c' c'') :
    ConnectedFiberNumberedCoverIso c c'' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  refine ⟨f ≪≫ g, fun i => ?_⟩
  rw [Iso.trans_hom, coverMap_comp_apply, hf i, hg i]

end ConnectedFiberNumberedCoverIso

namespace ConnectedPointedCoverIso

/-- Every pointed cover is isomorphic to itself, by the identity. -/
@[refl]
theorem refl (c : ConnectedPointedCover x n) : ConnectedPointedCoverIso c c :=
  ⟨Iso.refl _, coverMap_id_apply _ _⟩

/-- Isomorphism of pointed covers is symmetric. -/
@[symm]
theorem symm {c c' : ConnectedPointedCover x n} (h : ConnectedPointedCoverIso c c') :
    ConnectedPointedCoverIso c' c := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, ?_⟩
  rw [← hf]
  exact coverMap_inv_apply f.symm _

/-- Isomorphism of pointed covers is transitive. -/
@[trans]
theorem trans {c c' c'' : ConnectedPointedCover x n} (h : ConnectedPointedCoverIso c c')
    (h' : ConnectedPointedCoverIso c' c'') : ConnectedPointedCoverIso c c'' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  refine ⟨f ≪≫ g, ?_⟩
  rw [Iso.trans_hom, coverMap_comp_apply, hf, hg]

end ConnectedPointedCoverIso

/-- Fibre-numbered covers related by label-preserving isomorphism. -/
instance connectedFiberNumberedCoverSetoid (x : X) (n : ℕ) :
    Setoid (ConnectedFiberNumberedCover x n) where
  r := ConnectedFiberNumberedCoverIso
  iseqv := ⟨ConnectedFiberNumberedCoverIso.refl, .symm, .trans⟩

/-- Pointed covers related by pointed isomorphism. -/
instance connectedPointedCoverSetoid (x : X) (n : ℕ) : Setoid (ConnectedPointedCover x n) where
  r := ConnectedPointedCoverIso
  iseqv := ⟨ConnectedPointedCoverIso.refl, .symm, .trans⟩

/-- Covers related by isomorphism of the underlying covers. -/
instance connectedCoverSetoid (x : X) (n : ℕ) : Setoid (ConnectedCover x n) :=
  (isIsomorphicSetoid (ConnectedCoveringSpace X)).comap ConnectedCover.cover

/-! ### Isomorphism classes -/

/-- Fibre-numbered connected covers of degree `n` up to label-preserving isomorphism. -/
def ConnectedFiberNumberedCoverClass (x : X) (n : ℕ) : Type (u + 1) :=
  Quotient (connectedFiberNumberedCoverSetoid x n)

/-- Pointed connected covers of degree `n` up to pointed isomorphism. -/
def ConnectedPointedCoverClass (x : X) (n : ℕ) : Type (u + 1) :=
  Quotient (connectedPointedCoverSetoid x n)

/-- Connected covers of degree `n` up to isomorphism. -/
def ConnectedCoverClass (x : X) (n : ℕ) : Type (u + 1) :=
  Quotient (connectedCoverSetoid x n)

/-- The isomorphism class of a fibre-numbered cover. -/
def ConnectedFiberNumberedCoverClass.mk (c : ConnectedFiberNumberedCover x n) :
    ConnectedFiberNumberedCoverClass x n :=
  Quotient.mk _ c

/-- The isomorphism class of a pointed cover. -/
def ConnectedPointedCoverClass.mk (c : ConnectedPointedCover x n) :
    ConnectedPointedCoverClass x n :=
  Quotient.mk _ c

/-- The isomorphism class of a cover. -/
def ConnectedCoverClass.mk (c : ConnectedCover x n) : ConnectedCoverClass x n :=
  Quotient.mk _ c

/-- Two fibre-numbered covers have the same class exactly when they are isomorphic by a
label-preserving isomorphism. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.mk_eq_mk_iff {c c' : ConnectedFiberNumberedCover x n} :
    mk c = mk c' ↔ ConnectedFiberNumberedCoverIso c c' :=
  Quotient.eq

/-- Two pointed covers have the same class exactly when they are isomorphic as pointed covers. -/
@[simp]
theorem ConnectedPointedCoverClass.mk_eq_mk_iff {c c' : ConnectedPointedCover x n} :
    mk c = mk c' ↔ ConnectedPointedCoverIso c c' :=
  Quotient.eq

/-- Two covers have the same class exactly when their underlying covers are isomorphic. -/
@[simp]
theorem ConnectedCoverClass.mk_eq_mk_iff {c c' : ConnectedCover x n} :
    mk c = mk c' ↔ IsIsomorphic c.cover c'.cover :=
  Quotient.eq

/-- Every class of fibre-numbered covers is the class of a fibre-numbered cover. -/
theorem ConnectedFiberNumberedCoverClass.mk_surjective :
    Function.Surjective (mk : ConnectedFiberNumberedCover x n → _) :=
  Quotient.mk_surjective

/-- A function on numbered covers that is constant on label-preserving isomorphism classes, as a
function on the classes. -/
def ConnectedFiberNumberedCoverClass.lift {α : Sort*} (f : ConnectedFiberNumberedCover x n → α)
    (hf : ∀ c c', ConnectedFiberNumberedCoverIso c c' → f c = f c') :
    ConnectedFiberNumberedCoverClass x n → α :=
  Quotient.lift f hf

/-- The lift of `f` takes the class of `c` to `f c`. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.lift_mk {α : Sort*}
    (f : ConnectedFiberNumberedCover x n → α)
    (hf : ∀ c c', ConnectedFiberNumberedCoverIso c c' → f c = f c')
    (c : ConnectedFiberNumberedCover x n) :
    ConnectedFiberNumberedCoverClass.lift f hf (ConnectedFiberNumberedCoverClass.mk c) = f c :=
  (rfl)

/-- A property of the classes holds for every class once it holds for the class of every numbered
cover. -/
@[elab_as_elim]
theorem ConnectedFiberNumberedCoverClass.ind
    {motive : ConnectedFiberNumberedCoverClass x n → Prop}
    (h : ∀ c, motive (ConnectedFiberNumberedCoverClass.mk c))
    (C : ConnectedFiberNumberedCoverClass x n) : motive C :=
  Quotient.ind h C

/-- Every class of pointed covers is the class of a pointed cover. -/
theorem ConnectedPointedCoverClass.mk_surjective :
    Function.Surjective (mk : ConnectedPointedCover x n → _) :=
  Quotient.mk_surjective

/-- Every class of covers is the class of a cover. -/
theorem ConnectedCoverClass.mk_surjective :
    Function.Surjective (mk : ConnectedCover x n → _) :=
  Quotient.mk_surjective

/-! ### The forgetful maps -/

/-- Forgetting the numbering of the fibre. -/
def ConnectedFiberNumberedCover.forgetNumbering (c : ConnectedFiberNumberedCover x n) :
    ConnectedCover x n where
  cover := c.cover
  nonempty_equiv_fin := ⟨c.ν⟩

/-- Keeping only the point labelled `i`. -/
-- The type of `e` depends on the projected cover, so this definition must expose that projection.
@[expose] def ConnectedFiberNumberedCover.markLabel (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) :
    ConnectedPointedCover x n where
  cover := c.cover
  e := c.ν.symm i
  nonempty_equiv_fin := ⟨c.ν⟩

/-- Forgetting the chosen point. -/
def ConnectedPointedCover.forgetPoint (c : ConnectedPointedCover x n) :
    ConnectedCover x n where
  cover := c.cover
  nonempty_equiv_fin := c.nonempty_equiv_fin

/-- Forgetting the numbering keeps the underlying cover. -/
@[simp]
theorem ConnectedFiberNumberedCover.forgetNumbering_cover (c : ConnectedFiberNumberedCover x n) :
    c.forgetNumbering.cover = c.cover :=
  (rfl)

/-- Marking a label keeps the underlying cover. -/
@[simp]
theorem ConnectedFiberNumberedCover.markLabel_cover (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (c.markLabel i).cover = c.cover :=
  (rfl)

/-- The point chosen by marking the label `i` is the point labelled `i`. -/
@[simp]
theorem ConnectedFiberNumberedCover.markLabel_e (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (c.markLabel i).e = c.ν.symm i :=
  (rfl)

/-- Forgetting the chosen point keeps the underlying cover. -/
@[simp]
theorem ConnectedPointedCover.forgetPoint_cover (c : ConnectedPointedCover x n) :
    c.forgetPoint.cover = c.cover :=
  (rfl)

/-- A cover with some numbering chosen. -/
noncomputable def ConnectedCover.numbering (c : ConnectedCover x n) :
    ConnectedFiberNumberedCover x n where
  cover := c.cover
  ν := c.nonempty_equiv_fin.some

/-- Choosing a numbering keeps the underlying cover. -/
@[simp]
theorem ConnectedCover.numbering_cover (c : ConnectedCover x n) : c.numbering.cover = c.cover :=
  (rfl)

/-- Marking a label and then forgetting the point is forgetting the numbering. -/
@[simp]
theorem ConnectedFiberNumberedCover.forgetPoint_markLabel (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (c.markLabel i).forgetPoint = c.forgetNumbering :=
  (rfl)

/-- Choosing a numbering and then forgetting it gives back the cover. -/
@[simp]
theorem ConnectedCover.forgetNumbering_numbering (c : ConnectedCover x n) :
    c.numbering.forgetNumbering = c :=
  (rfl)

/-- Forgetting the numbering, on isomorphism classes. -/
def ConnectedFiberNumberedCoverClass.forgetNumbering :
    ConnectedFiberNumberedCoverClass x n → ConnectedCoverClass x n :=
  Quotient.map ConnectedFiberNumberedCover.forgetNumbering fun _ _ ⟨f, _⟩ => ⟨f⟩

/-- Keeping only the point labelled `i`, on isomorphism classes: a label-preserving isomorphism
preserves in particular the point labelled `i`. -/
def ConnectedFiberNumberedCoverClass.markLabel (C : ConnectedFiberNumberedCoverClass x n)
    (i : Fin n) : ConnectedPointedCoverClass x n :=
  Quotient.map (·.markLabel i) (fun _ _ h => by
    obtain ⟨f, hf⟩ := h
    exact Exists.intro f (hf i)) C

/-- Forgetting the chosen point, on isomorphism classes. -/
def ConnectedPointedCoverClass.forgetPoint :
    ConnectedPointedCoverClass x n → ConnectedCoverClass x n :=
  Quotient.map ConnectedPointedCover.forgetPoint fun _ _ ⟨f, _⟩ => ⟨f⟩

/-- Forgetting the numbering of the class of `c` gives the class of `c.forgetNumbering`. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.forgetNumbering_mk (c : ConnectedFiberNumberedCover x n) :
    (mk c).forgetNumbering = ConnectedCoverClass.mk c.forgetNumbering :=
  (rfl)

/-- Marking the label `i` in the class of `c` gives the class of `c.markLabel i`. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.markLabel_mk (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (mk c).markLabel i = ConnectedPointedCoverClass.mk (c.markLabel i) :=
  (rfl)

/-- Forgetting the point of the class of `c` gives the class of `c.forgetPoint`. -/
@[simp]
theorem ConnectedPointedCoverClass.forgetPoint_mk (c : ConnectedPointedCover x n) :
    (mk c).forgetPoint = ConnectedCoverClass.mk c.forgetPoint :=
  (rfl)

/-- The forgetful triangle commutes: marking a label and then forgetting the point is forgetting
the numbering. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.forgetPoint_markLabel
    (C : ConnectedFiberNumberedCoverClass x n) (i : Fin n) :
    (C.markLabel i).forgetPoint = C.forgetNumbering :=
  Quotient.inductionOn C fun _ => rfl

/-- Every bare class is obtained by forgetting the numbering of a numbered class, since every cover
has a numbering. -/
theorem ConnectedFiberNumberedCoverClass.forgetNumbering_surjective :
    Function.Surjective (forgetNumbering : ConnectedFiberNumberedCoverClass x n → _) :=
  Quotient.map_surjective _ fun c => ⟨c.numbering, rfl⟩

/-- Every pointed class is obtained by marking a label in a numbered class. -/
theorem ConnectedPointedCoverClass.exists_markLabel_eq (C : ConnectedPointedCoverClass x n) :
    ∃ (N : ConnectedFiberNumberedCoverClass x n) (i : Fin n), N.markLabel i = C := by
  obtain ⟨c, rfl⟩ := mk_surjective C
  refine ⟨.mk c.forgetPoint.numbering, c.forgetPoint.numbering.ν c.e, congrArg mk ?_⟩
  obtain ⟨cover, e, h⟩ := c
  exact congrArg (fun e' => ConnectedPointedCover.mk cover e' h) (symm_apply_apply _ e)

/-! ### Relabelling the fibre -/

namespace ConnectedFiberNumberedCover

/-- The symmetric group on the labels acts on numberings by relabelling: `τ • ν = ν.trans τ`. -/
instance : SMul (Perm (Fin n)) (ConnectedFiberNumberedCover x n) where
  smul τ c := ⟨c.cover, c.ν.trans τ⟩

/-- Relabelling keeps the underlying cover. -/
@[simp]
theorem smul_cover (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    (τ • c).cover = c.cover :=
  (rfl)

/-- Relabelling by `τ` composes the numbering with `τ`. -/
@[simp]
theorem smul_ν (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    (τ • c).ν = c.ν.trans τ :=
  rfl

/-- Relabelling is an action of the symmetric group on fibre-numbered covers. -/
instance : MulAction (Perm (Fin n)) (ConnectedFiberNumberedCover x n) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Relabelling does not change the cover left after forgetting the numbering. -/
@[simp]
theorem forgetNumbering_smul (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    (τ • c).forgetNumbering = c.forgetNumbering :=
  (rfl)

/-- Relabelling by `τ` and then marking the label `i` marks the original label `τ.symm i`. -/
@[simp]
theorem markLabel_smul (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) (i : Fin n) :
    (τ • c).markLabel i = c.markLabel (τ.symm i) := by
  simp [markLabel]

/-- An isomorphism of the underlying covers makes two numbered covers isomorphic after the
relabelling it induces on the fibre. -/
private theorem exists_smul_iso_of_iso {c c' : ConnectedFiberNumberedCover x n}
    (f : c.cover ≅ c'.cover) :
    ∃ τ : Perm (Fin n), ConnectedFiberNumberedCoverIso (τ • c) c' ∧
      ∀ i, τ i = c'.ν (fiberEquiv f (c.ν.symm i)) :=
  ⟨(c.ν.symm.trans (fiberEquiv f)).trans c'.ν,
    ⟨f, fun i => by rw [← coe_fiberEquiv_apply]; simp⟩, fun _ => rfl⟩

end ConnectedFiberNumberedCover

/-- Relabelling both sides preserves label-preserving isomorphism. -/
theorem ConnectedFiberNumberedCoverIso.smul {c c' : ConnectedFiberNumberedCover x n}
    (h : ConnectedFiberNumberedCoverIso c c') (τ : Perm (Fin n)) :
    ConnectedFiberNumberedCoverIso (τ • c) (τ • c') := by
  obtain ⟨f, hf⟩ := h
  refine Exists.intro f fun i => ?_
  simpa only [ConnectedFiberNumberedCover.smul_ν, Equiv.symm_trans_apply] using hf (τ.symm i)

namespace ConnectedFiberNumberedCoverClass

open ConnectedFiberNumberedCover

/-- Relabelling descends to classes, since relabelling both sides preserves label-preserving
isomorphism. -/
instance : SMul (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n) where
  smul τ := lift (fun c => mk (τ • c)) fun _ _ h => mk_eq_mk_iff.2 (h.smul τ)

/-- Relabelling the class of `c` gives the class of the relabelled cover. -/
@[simp]
theorem smul_mk (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    τ • mk c = mk (τ • c) :=
  lift_mk _ _ c

/-- Relabelling is an action of the symmetric group on classes of fibre-numbered covers. -/
instance : MulAction (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n) :=
  mk_surjective.mulAction mk fun τ c => (smul_mk τ c).symm

/-- Relabelling a class does not change its bare class. -/
@[simp]
theorem forgetNumbering_smul (τ : Perm (Fin n)) (C : ConnectedFiberNumberedCoverClass x n) :
    (τ • C).forgetNumbering = C.forgetNumbering :=
  Quotient.inductionOn C fun _ => rfl

/-- Relabelling a class by `τ` and then marking the label `i` marks the original label
`τ.symm i`. -/
@[simp]
theorem markLabel_smul (τ : Perm (Fin n)) (C : ConnectedFiberNumberedCoverClass x n)
    (i : Fin n) : (τ • C).markLabel i = C.markLabel (τ.symm i) :=
  Quotient.inductionOn C fun c => congrArg ConnectedPointedCoverClass.mk (c.markLabel_smul τ i)

/-- **Forgetting the numbering is passing to the relabelling orbit.** Two numbered classes have
the same underlying cover exactly when a relabelling carries one to the other. -/
theorem forgetNumbering_eq_forgetNumbering_iff {C C' : ConnectedFiberNumberedCoverClass x n} :
    C.forgetNumbering = C'.forgetNumbering ↔ ∃ τ : Perm (Fin n), τ • C' = C := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := mk_surjective C
    obtain ⟨c', rfl⟩ := mk_surjective C'
    rw [forgetNumbering_mk, forgetNumbering_mk] at h
    obtain ⟨f⟩ := ConnectedCoverClass.mk_eq_mk_iff.1 h.symm
    obtain ⟨τ, hτ, -⟩ := exists_smul_iso_of_iso f
    exact ⟨τ, by rw [smul_mk, mk_eq_mk_iff.2 hτ]⟩
  · rintro ⟨τ, rfl⟩
    exact forgetNumbering_smul τ C'

/-- **Marking a label is passing to the diagonal relabelling orbit.** Two numbered classes with
marked labels give the same pointed class exactly when a relabelling carries the second class to
the first and the second label to the first. -/
theorem markLabel_eq_markLabel_iff {C C' : ConnectedFiberNumberedCoverClass x n} {i j : Fin n} :
    C.markLabel i = C'.markLabel j ↔ ∃ τ : Perm (Fin n), τ • C' = C ∧ τ j = i := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := mk_surjective C
    obtain ⟨c', rfl⟩ := mk_surjective C'
    rw [markLabel_mk, markLabel_mk] at h
    obtain ⟨f, hf⟩ := ConnectedPointedCoverClass.mk_eq_mk_iff.1 h.symm
    obtain ⟨τ, hτ, hτi⟩ := exists_smul_iso_of_iso f
    have he : fiberEquiv f (c'.ν.symm j) = c.ν.symm i :=
      Subtype.ext ((coe_fiberEquiv_apply f _).trans hf)
    refine ⟨τ, by rw [smul_mk, mk_eq_mk_iff.2 hτ], ?_⟩
    rw [hτi]
    exact (congrArg c.ν he).trans (apply_symm_apply _ _)
  · rintro ⟨τ, rfl, rfl⟩
    rw [markLabel_smul, symm_apply_apply]

/-- The bare isomorphism classes of connected covers of degree `n` are the relabelling orbits of
the numbered classes. -/
noncomputable def orbitRelQuotientEquiv :
    MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n) ≃
      ConnectedCoverClass x n :=
  (Quotient.congrRight fun _ _ => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Setoid.ker_def,
      forgetNumbering_eq_forgetNumbering_iff]).trans
    (Setoid.quotientKerEquivOfSurjective _ forgetNumbering_surjective)

/-- `orbitRelQuotientEquiv` sends the orbit of a numbered class to its bare class. -/
@[simp]
theorem orbitRelQuotientEquiv_mk (C : ConnectedFiberNumberedCoverClass x n) :
    orbitRelQuotientEquiv (Quotient.mk _ C) = C.forgetNumbering :=
  (rfl)

/-- The inverse of `orbitRelQuotientEquiv` sends the bare class of a numbered class to its orbit. -/
@[simp]
theorem orbitRelQuotientEquiv_symm_forgetNumbering (C : ConnectedFiberNumberedCoverClass x n) :
    orbitRelQuotientEquiv.symm C.forgetNumbering = Quotient.mk _ C :=
  orbitRelQuotientEquiv.symm_apply_eq.2 (orbitRelQuotientEquiv_mk C).symm

/-- The pointed isomorphism classes of connected covers of degree `n` are the orbits of the
diagonal relabelling action on numbered classes with a marked label. -/
noncomputable def markedOrbitRelQuotientEquiv :
    MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n × Fin n) ≃
      ConnectedPointedCoverClass x n :=
  (Quotient.congrRight fun ⟨C, i⟩ ⟨C', j⟩ => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Setoid.ker_def]
    dsimp only [Function.uncurry_apply_pair]
    rw [markLabel_eq_markLabel_iff]
    simp [Prod.ext_iff, Perm.smul_def]).trans
    (Setoid.quotientKerEquivOfSurjective (Function.uncurry markLabel) fun C =>
      let ⟨N, i, h⟩ := C.exists_markLabel_eq
      ⟨(N, i), h⟩)

/-- `markedOrbitRelQuotientEquiv` sends the orbit of a numbered class with a marked label to the
pointed class obtained by marking that label. -/
@[simp]
theorem markedOrbitRelQuotientEquiv_mk (C : ConnectedFiberNumberedCoverClass x n) (i : Fin n) :
    markedOrbitRelQuotientEquiv (Quotient.mk _ (C, i)) = C.markLabel i :=
  (rfl)

/-- The inverse of `markedOrbitRelQuotientEquiv` sends the pointed class obtained by marking the
label `i` of a numbered class to the orbit of that class and label. -/
@[simp]
theorem markedOrbitRelQuotientEquiv_symm_markLabel (C : ConnectedFiberNumberedCoverClass x n)
    (i : Fin n) : markedOrbitRelQuotientEquiv.symm (C.markLabel i) = Quotient.mk _ (C, i) :=
  markedOrbitRelQuotientEquiv.symm_apply_eq.2 (markedOrbitRelQuotientEquiv_mk C i).symm

end ConnectedFiberNumberedCoverClass

/-! ### Degree and inhabited fibres -/

namespace ConnectedCover

/-- The degree is the same over every point of the connected component of `x`: the number of
points in a fibre of a covering map is locally constant. -/
theorem nonempty_equiv_fin_of_mem_connectedComponent (c : ConnectedCover x n) {y : X}
    (hy : y ∈ connectedComponent x) : Nonempty (⇑c.cover.proj ⁻¹' {y} ≃ Fin n) :=
  (c.cover.isCoveringMap_proj.isClopen_setOf_nonempty_fiber_equiv (Fin n)).connectedComponent_subset
    c.nonempty_equiv_fin hy

variable [PreconnectedSpace X]

/-- A connected cover of a preconnected space has positive degree. -/
theorem ne_zero (c : ConnectedCover x n) : n ≠ 0 := by
  rintro rfl
  obtain ⟨ν⟩ := c.nonempty_equiv_fin
  obtain ⟨e⟩ := ConnectedCoveringSpace.nonempty_fiber c.cover x
  exact (ν e).elim0

end ConnectedCover

/-- For positive degree, every bare cover has a point over `x`, so forgetting the point is
surjective on isomorphism classes. -/
theorem ConnectedPointedCoverClass.forgetPoint_surjective (hn : n ≠ 0) :
    Function.Surjective (forgetPoint : ConnectedPointedCoverClass x n → _) := by
  rintro ⟨c⟩
  exact ⟨mk (c.numbering.markLabel ⟨0, Nat.pos_of_ne_zero hn⟩), rfl⟩

/-! ### Moving the basepoint -/

section BasepointChange

variable {x₀ x₁ : X}

/-- Moving the basepoint of a numbered cover along a path `γ` from `x₀` to `x₁`: the same cover,
with the fibre over `x₁` numbered by transporting it back to the fibre over `x₀` along `γ`. The
numbering depends on `γ`, through the monodromy of loops at `x₀`. -/
noncomputable def ConnectedFiberNumberedCover.basepointChange
    (c : ConnectedFiberNumberedCover x₀ n) (γ : Path x₀ x₁) : ConnectedFiberNumberedCover x₁ n where
  cover := c.cover
  ν := (coveringFiberEquiv c.cover.isCoveringMap_proj (.mk γ)).symm.trans c.ν

namespace ConnectedFiberNumberedCover

variable (c : ConnectedFiberNumberedCover x₀ n) (γ : Path x₀ x₁)

@[simp]
theorem basepointChange_cover : (c.basepointChange γ).cover = c.cover :=
  (rfl)

/-- The numbering of the moved cover transports the fibre over `x₁` back to the fibre over `x₀`
along `γ` and numbers it there. The two fibres live over the same cover only up to
`basepointChange_cover`, so the equality is heterogeneous. -/
theorem basepointChange_ν :
    (c.basepointChange γ).ν ≍
      (coveringFiberEquiv c.cover.isCoveringMap_proj (.mk γ)).symm.trans c.ν :=
  HEq.rfl

/-- **Moving the basepoint along `γ` conjugates the numbered monodromy by `γ`.** The numbered
monodromy representation of `π₁(X, x₁)` of the moved cover is that of `π₁(X, x₀)` precomposed with
the basepoint-change isomorphism `π₁(X, x₁) ≃* π₁(X, x₀)`, which sends the class of a loop `g` at
`x₁` to the class of `γ ⬝ g ⬝ γ⁻¹`. -/
theorem permCongrHom_comp_monodromyPerm_basepointChange :
    (c.basepointChange γ).ν.permCongrHom.toMonoidHom.comp
        ((c.basepointChange γ).cover.isCoveringMap_proj.monodromyPerm x₁) =
      (c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x₀)).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm.toMonoidHom := by
  have hp := c.cover.isCoveringMap_proj
  -- transporting back along `γ` is the monodromy along the reversed path
  have hback (e : ⇑c.cover.proj ⁻¹' {x₁}) :
      (coveringFiberEquiv hp (.mk γ)).symm e =
        hp.monodromy (Path.Homotopic.Quotient.mk γ).symm e := by
    rw [Equiv.symm_apply_eq, coveringFiberEquiv_apply, ← hp.monodromy_trans_apply,
      Path.Homotopic.Quotient.symm_trans, hp.monodromy_refl, id]
  refine MonoidHom.ext fun g => Equiv.ext fun i => congrArg c.ν ?_
  -- The fibres of the moved cover are those of `c` only definitionally (`basepointChange_cover`),
  -- so the goal is restated over `c.cover` before rewriting.
  change (coveringFiberEquiv hp (.mk γ)).symm
      (hp.monodromy g (coveringFiberEquiv hp (.mk γ) (c.ν.symm i))) =
    hp.monodromy ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g) (c.ν.symm i)
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, hp.monodromy_trans_apply,
    hp.monodromy_trans_apply, hback, coveringFiberEquiv_apply]

end ConnectedFiberNumberedCover

/-- Moving the basepoint of a bare cover of degree `n` from `x₀` to a point `x₁` of its connected
component: the same cover, which has degree `n` over `x₁` as well
(`TauCeti.ConnectedCover.nonempty_equiv_fin_of_mem_connectedComponent`). -/
def ConnectedCover.basepointChange (c : ConnectedCover x₀ n) (h : x₁ ∈ connectedComponent x₀) :
    ConnectedCover x₁ n where
  cover := c.cover
  nonempty_equiv_fin := c.nonempty_equiv_fin_of_mem_connectedComponent h

@[simp]
theorem ConnectedCover.basepointChange_cover (c : ConnectedCover x₀ n)
    (h : x₁ ∈ connectedComponent x₀) : (c.basepointChange h).cover = c.cover :=
  (rfl)

/-- Moving the basepoint of a numbered cover along a path and then forgetting the numbering is
forgetting the numbering and then moving the basepoint. -/
theorem ConnectedFiberNumberedCover.forgetNumbering_basepointChange
    (c : ConnectedFiberNumberedCover x₀ n) (γ : Path x₀ x₁) (h : x₁ ∈ connectedComponent x₀) :
    (c.basepointChange γ).forgetNumbering = c.forgetNumbering.basepointChange h :=
  ConnectedCover.ext (rfl)

/-- Moving the basepoint of a bare cover to a point of its connected component, on isomorphism
classes. -/
def ConnectedCoverClass.basepointChange (C : ConnectedCoverClass x₀ n)
    (h : x₁ ∈ connectedComponent x₀) : ConnectedCoverClass x₁ n :=
  Quotient.map (·.basepointChange h) (fun _ _ hcc => hcc) C

@[simp]
theorem ConnectedCoverClass.basepointChange_mk (c : ConnectedCover x₀ n)
    (h : x₁ ∈ connectedComponent x₀) : (mk c).basepointChange h = mk (c.basepointChange h) :=
  (rfl)

end BasepointChange

/-! ### Numbered monodromy -/

/-- **Isomorphic numbered covers have the same numbered monodromy.** A label-preserving
isomorphism of covers identifies their monodromy representations `π₁(X, x) →* Equiv.Perm (Fin n)`
read through the numberings; this direction needs no hypothesis on the base. -/
theorem ConnectedFiberNumberedCoverIso.permCongrHom_comp_monodromyPerm_eq
    {c c' : ConnectedFiberNumberedCover x n} (h : ConnectedFiberNumberedCoverIso c c') :
    c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x) =
      c'.ν.permCongrHom.toMonoidHom.comp (c'.cover.isCoveringMap_proj.monodromyPerm x) := by
  obtain ⟨f, hf⟩ := connectedFiberNumberedCoverIso_iff_exists.1 h
  refine (c.cover.isCoveringMap_proj.permutationRepresentation_eq_of_fiberMap
    c'.cover.isCoveringMap_proj x c.ν c'.ν f.hom.hom.left.hom
    (CoveringSpace.proj_hom_comp_hom_left_hom ((ConnectedCoveringSpace.forget X).map f.hom))
    fun e => ?_).symm
  rw [← c'.ν.apply_symm_apply (c.ν e)]
  refine congrArg c'.ν (Subtype.ext ?_)
  rw [Function.fiberMap_apply_coe, ← hf, symm_apply_apply]

section Monodromy

variable [PathConnectedSpace X] [LocallyPathConnectedSpace X]

/-- **Numbered covers with the same numbered monodromy are isomorphic.** Over a path-connected,
locally path-connected base, if the monodromy representations `π₁(X, x) →* Equiv.Perm (Fin n)` of
two numbered covers, read through their numberings, agree, then some isomorphism of the covers
preserves every label. -/
theorem ConnectedFiberNumberedCoverIso.of_permCongrHom_comp_monodromyPerm_eq
    {c c' : ConnectedFiberNumberedCover x n}
    (h : c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x) =
      c'.ν.permCongrHom.toMonoidHom.comp (c'.cover.isCoveringMap_proj.monodromyPerm x)) :
    ConnectedFiberNumberedCoverIso c c' := by
  -- The relabelling `c.ν.trans c'.ν.symm` of fibres is `π₁(X, x)`-equivariant; the fibre-action
  -- functor is fully faithful, so it is the fibre map of an isomorphism of covers.
  have hcomm : ∀ (γ : FundamentalGroup X x) e,
      (c.ν.trans c'.ν.symm) (c.cover.isCoveringMap_proj.monodromy γ e) =
        c'.cover.isCoveringMap_proj.monodromy γ ((c.ν.trans c'.ν.symm) e) := fun γ e => by
    simpa [permCongr_apply, symm_apply_eq] using
      DFunLike.congr_fun (DFunLike.congr_fun h γ) (c.ν e)
  let F := ConnectedCoveringSpace.forget X ⋙ CoveringSpace.fiberActionFunctor x
  let φ : F.obj c.cover ≅ F.obj c'.cover :=
    Action.mkIso (Equiv.toIso (c.ν.trans c'.ν.symm)) fun γ => by
      ext e
      exact hcomm γ e
  refine connectedFiberNumberedCoverIso_iff_exists.2 ⟨F.preimageIso φ, fun i => ?_⟩
  have hφ : (CoveringSpace.fiberActionFunctor x).map
      ((ConnectedCoveringSpace.forget X).map (F.preimage φ.hom)) = φ.hom := F.map_preimage φ.hom
  have hi := congrArg (fun ψ => ψ.hom (c.ν.symm i)) hφ
  have hφi : φ.hom.hom (c.ν.symm i) = c'.ν.symm i :=
    (Equiv.toIso_hom_hom_apply (c.ν.trans c'.ν.symm) (c.ν.symm i)).trans (by simp)
  rw [CoveringSpace.fiberActionFunctor_map_hom, hφi] at hi
  rw [Functor.preimageIso_hom]
  exact (Function.fiberMap_apply_coe _ (CoveringSpace.proj_hom_comp_hom_left_hom
    ((ConnectedCoveringSpace.forget X).map (F.preimage φ.hom))) x (c.ν.symm i)).symm.trans
    (congrArg Subtype.val hi)

/-- **A numbered connected cover is determined by its numbered monodromy.** Over a path-connected,
locally path-connected base, two numbered covers are isomorphic, by an isomorphism preserving every
label, exactly when their monodromy representations `π₁(X, x) →* Equiv.Perm (Fin n)`, read through
the numberings, agree. -/
theorem connectedFiberNumberedCoverIso_iff_permCongrHom_comp_monodromyPerm_eq
    {c c' : ConnectedFiberNumberedCover x n} :
    ConnectedFiberNumberedCoverIso c c' ↔
      c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x) =
        c'.ν.permCongrHom.toMonoidHom.comp (c'.cover.isCoveringMap_proj.monodromyPerm x) :=
  ⟨ConnectedFiberNumberedCoverIso.permCongrHom_comp_monodromyPerm_eq,
    ConnectedFiberNumberedCoverIso.of_permCongrHom_comp_monodromyPerm_eq⟩

end Monodromy

/-! ### Realising a numbered monodromy -/

/-- **Every transitive representation on `Fin n` is the numbered monodromy of a cover.** Over a
locally path-connected, semilocally simply connected base, a homomorphism
`ρ : π₁(X, x) →* Equiv.Perm (Fin n)` whose image acts transitively on the nonempty set `Fin n` is
the monodromy representation, read through the numbering, of some connected cover with numbered
fibre. -/
theorem ConnectedFiberNumberedCover.exists_permCongrHom_comp_monodromyPerm_eq
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (ρ : FundamentalGroup X x →* Perm (Fin n)) (hn : n ≠ 0)
    (hρ : MulAction.IsPretransitive ρ.range (Fin n)) :
    ∃ c : ConnectedFiberNumberedCover x n,
      c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x) = ρ := by
  -- `π₁(X, x)` acts on `Fin n` through `ρ`, transitively because the image of `ρ` does.
  let _ : MulAction (FundamentalGroup X x) (Fin n) := MulAction.compHom _ ρ.rangeRestrict
  have := MulAction.isPretransitive_compHom (G := Fin n) ρ.rangeRestrict_surjective
  -- Lift the finite set to the universe of the base before applying the realisation theorem.
  let _ := (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).mulAction (FundamentalGroup X x)
  let A := Action.ofMulAction (FundamentalGroup X x) (ULift.{u} (Fin n))
  have hA : isTransitiveAction (FundamentalGroup X x) A := by
    rw [isTransitiveAction_iff]
    refine ⟨⟨fun i j => ?_⟩, ⟨ULift.up ⟨0, Nat.pos_of_ne_zero hn⟩⟩⟩
    obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq (FundamentalGroup X x) i.down j.down
    exact ⟨γ, ULift.ext hγ⟩
  obtain ⟨c, ⟨e⟩⟩ := ConnectedCoveringSpace.exists_fiberAction_iso x A hA
  let ν : ⇑c.proj ⁻¹' {x} ≃ Fin n :=
    ((Action.forget _ _).mapIso e).toEquiv.trans Equiv.ulift
  let _ := c.isCoveringMap_proj.fundamentalGroupMulAction x
  refine ⟨⟨c, ν⟩, ?_⟩
  rw [← c.isCoveringMap_proj.toPermHom_eq_monodromyPerm,
    ← Equiv.permutationRepresentation.eq_def]
  refine Equiv.permutationRepresentation_eq_of_map_smul ν (ρ := ρ) fun γ a => ?_
  -- Spell out both actions: their carriers are hidden under the functor and `A.V`, so
  -- rewriting the composition in `e.hom.comm` cannot identify the underlying types.
  have he : e.hom.hom (c.isCoveringMap_proj.monodromy γ a) = ULift.up (ρ γ (ν a)) :=
    ConcreteCategory.congr_hom (e.hom.comm γ) a
  exact congrArg ULift.down he

/-! ### Deck transformations -/

namespace ConnectedFiberNumberedCover

variable (c : ConnectedFiberNumberedCover x n)

/-- The permutation of the labels induced by a deck transformation of a numbered cover: the label
`i` goes to the label of the image of the point labelled `i` (`deckPerm_apply`). This is the
permutation representation of the deck action on the fibre, read through the numbering. -/
def deckPerm : deck ⇑c.cover.proj →* Perm (Fin n) :=
  Equiv.permutationRepresentation c.ν

/-- The label of the image of the point labelled `i` under a deck transformation. -/
@[simp]
theorem deckPerm_apply (φ : deck ⇑c.cover.proj) (i : Fin n) :
    c.deckPerm φ i = c.ν (φ • c.ν.symm i) :=
  Equiv.permutationRepresentation_apply c.ν φ i

/-- The permutations of the labels induced by deck transformations act transitively exactly when
the deck group acts transitively on the fibre. -/
theorem isPretransitive_range_deckPerm_iff :
    MulAction.IsPretransitive c.deckPerm.range (Fin n) ↔
      MulAction.IsPretransitive (deck ⇑c.cover.proj) (⇑c.cover.proj ⁻¹' {x}) :=
  Equiv.isPretransitive_range_permutationRepresentation_iff c.ν

/-- Relabelling the fibre by `τ` conjugates the permutation induced by each deck transformation
by `τ`. -/
@[simp]
theorem deckPerm_smul (τ : Perm (Fin n)) (φ : deck ⇑c.cover.proj) :
    (τ • c).deckPerm φ = τ * c.deckPerm φ * τ⁻¹ := by
  ext i
  simp [Perm.mul_apply]

/-- **A deck transformation of a numbered cover is determined by the permutation it induces on the
labels.** Over a preconnected base the fibre is nonempty, and a deck transformation of a connected
cover is determined by its value at one point. -/
theorem deckPerm_injective [PreconnectedSpace X] : Function.Injective c.deckPerm := by
  intro φ ψ h
  have hi := DFunLike.congr_fun h ⟨0, Nat.pos_of_ne_zero c.forgetNumbering.ne_zero⟩
  simp only [deckPerm_apply, EmbeddingLike.apply_eq_iff_eq] at hi
  exact Deck.eq_of_fiber_smul_eq_fiber_smul c.cover.isCoveringMap_proj φ ψ hi

/-- **The permutations of the labels induced by deck transformations are exactly those commuting
with the numbered monodromy.** Over a path-connected, locally path-connected base, the image of
`deckPerm` is the centralizer in `Equiv.Perm (Fin n)` of the monodromy representation
`π₁(X, x) →* Equiv.Perm (Fin n)` read through the numbering. -/
theorem range_deckPerm [PathConnectedSpace X] [LocallyPathConnectedSpace X] :
    c.deckPerm.range = Subgroup.centralizer
      ((c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x)).range :
        Set (Perm (Fin n))) := by
  ext τ
  constructor
  · -- Deck transformations commute with monodromy.
    rintro ⟨φ, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, rfl⟩
    ext i
    simp [Perm.mul_apply, permCongr_apply, Deck.monodromy_smul]
  · -- A relabelling commuting with the monodromy does not change it, so it is induced by a
    -- label-preserving isomorphism from the cover to its relabelling, that is, by a deck
    -- transformation.
    intro hτ
    have h : c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm x) =
        (τ⁻¹ • c).ν.permCongrHom.toMonoidHom.comp
          ((τ⁻¹ • c).cover.isCoveringMap_proj.monodromyPerm x) := by
      refine MonoidHom.ext fun γ => Equiv.ext fun i => ?_
      have hci := DFunLike.congr_fun (Subgroup.mem_centralizer_iff.1 hτ _ ⟨γ, rfl⟩) i
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, permCongrHom_coe,
        permCongr_apply, Perm.mul_apply, smul_ν, symm_trans_apply, Perm.inv_def, symm_symm,
        trans_apply] at hci ⊢
      rw [hci, symm_apply_apply]
    obtain ⟨f, hf⟩ := ConnectedFiberNumberedCoverIso.of_permCongrHom_comp_monodromyPerm_eq h
    refine ⟨⟨coverHomeomorph f, deck.mem_iff.2 (funext (proj_coverHomeomorph f))⟩, ?_⟩
    refine Equiv.ext fun i => ?_
    rw [deckPerm_apply, ← c.ν.apply_symm_apply (τ i)]
    refine congrArg c.ν (Subtype.ext ?_)
    simp only [deck.fiber_smul_coe]
    rw [coverHomeomorph_apply, hf i, smul_ν, symm_trans_apply, Perm.inv_def, symm_symm]

end ConnectedFiberNumberedCover

end TauCeti
