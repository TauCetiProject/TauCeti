/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Transport
public import TauCeti.Topology.Covering.Monodromy.Transitive

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

All three are built on `TauCeti.ConnectedCoveringSpace X` and additionally carry
path-connectedness of the total space. The degree is a parameter rather than something recovered
afterwards: it is the cardinality of the fibre over `x`, recorded by the numbering itself or by
the existence of one. Isomorphism is an equivalence relation in each case, and the three types of
isomorphism classes are the quotients
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

Over a path-connected base the degree does not depend on the basepoint, and a connected cover has
positive degree.

## Main declarations

* `TauCeti.ConnectedFiberNumberedCover`, `TauCeti.ConnectedPointedCover`,
  `TauCeti.ConnectedCover`: the three carriers.
* `TauCeti.ConnectedFiberNumberedCoverIso`, `TauCeti.ConnectedPointedCoverIso`,
  `TauCeti.ConnectedCoverIso`: their isomorphism relations, with setoids
  `TauCeti.connectedFiberNumberedCoverSetoid`, `TauCeti.connectedPointedCoverSetoid`,
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
* `TauCeti.ConnectedCover.nonempty_equiv_fin_of`: a path transports the degree between fibres;
  `TauCeti.ConnectedCover.ne_zero`: over a path-connected base the degree is positive.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (isomorphism of
  covering spaces, and the change of basepoint within a fibre).
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
  /-- The total space is path connected. -/
  pathConnected : PathConnectedSpace (cover : TopCat)

/-- A connected covering space of `X` of degree `n` with one chosen point of its fibre over `x`.
Only that point is rigidified: the relabellings of the fibre fixing it survive. -/
structure ConnectedPointedCover (x : X) (n : ℕ) where
  /-- The underlying connected covering space. -/
  cover : ConnectedCoveringSpace X
  /-- The chosen point of the fibre over the basepoint. -/
  e : ⇑cover.proj ⁻¹' {x}
  /-- The fibre over the basepoint has `n` points. -/
  nonempty_equiv_fin : Nonempty (⇑cover.proj ⁻¹' {x} ≃ Fin n)
  /-- The total space is path connected. -/
  pathConnected : PathConnectedSpace (cover : TopCat)

/-- A connected covering space of `X` whose fibre over `x` has `n` points, with no further
rigidification. -/
structure ConnectedCover (x : X) (n : ℕ) where
  /-- The underlying connected covering space. -/
  cover : ConnectedCoveringSpace X
  /-- The fibre over the basepoint has `n` points. -/
  nonempty_equiv_fin : Nonempty (⇑cover.proj ⁻¹' {x} ≃ Fin n)
  /-- The total space is path connected. -/
  pathConnected : PathConnectedSpace (cover : TopCat)

variable {x : X} {n : ℕ}

/-- The homeomorphism of total spaces underlying an isomorphism of connected covers. -/
private def coverHomeomorph {p q : ConnectedCoveringSpace X} (f : p ≅ q) :
    (p : TopCat) ≃ₜ (q : TopCat) :=
  TopCat.homeoOfIso ((CoveringSpace.FullSubcategory.totalSpace X _).mapIso f)

private theorem proj_coverHomeomorph {p q : ConnectedCoveringSpace X} (f : p ≅ q)
    (e : (p : TopCat)) : q.proj (coverHomeomorph f e) = p.proj e := by
  rw [← CoveringSpace.FullSubcategory.w f.hom]
  rfl

/-- The bijection between the fibres over `x` induced by an isomorphism of connected covers.

This is the underlying equivalence of `(CoveringSpace.fiberFunctor x).mapIso f`, rebuilt from
`Deck.fiberMap` because the fibre functor acts on points only up to a lemma, while here the value
at a point is definitionally `f.hom.hom.left` (`coe_fiberEquiv_apply`). -/
private def fiberEquiv {p q : ConnectedCoveringSpace X} (f : p ≅ q) :
    ⇑p.proj ⁻¹' {x} ≃ ⇑q.proj ⁻¹' {x} :=
  (Deck.fiberMap (coverHomeomorph f) (proj_coverHomeomorph f) x).toEquiv

private theorem coe_fiberEquiv_apply {p q : ConnectedCoveringSpace X} (f : p ≅ q)
    (e : ⇑p.proj ⁻¹' {x}) : (fiberEquiv f e : (q : TopCat)) = f.hom.hom.left e.1 :=
  rfl

/- The pointwise laws isolate how the cover-category wrappers act on total-space points. -/
private theorem coverMap_id_apply (p : ConnectedCoveringSpace X) (e : (p : TopCat)) :
    (Iso.refl p).hom.hom.left e = e :=
  rfl

private theorem coverMap_comp_apply {p q r : ConnectedCoveringSpace X}
    (f : p ⟶ q) (g : q ⟶ r) (e : (p : TopCat)) :
    (f ≫ g).hom.left e = g.hom.left (f.hom.left e) :=
  rfl

private theorem coverMap_inv_apply {p q : ConnectedCoveringSpace X}
    (f : p ≅ q) (e : (q : TopCat)) :
    f.hom.hom.left (f.inv.hom.left e) = e := by
  rw [← coverMap_comp_apply f.inv f.hom e, f.inv_hom_id]
  exact coverMap_id_apply q e

private theorem fiberEquiv_refl (p : ConnectedCoveringSpace X) :
    fiberEquiv (x := x) (Iso.refl p) = Equiv.refl _ := by
  apply Equiv.ext
  intro e
  apply Subtype.ext
  rw [coe_fiberEquiv_apply]
  exact coverMap_id_apply p e.1

private theorem fiberEquiv_symm {p q : ConnectedCoveringSpace X} (f : p ≅ q) :
    fiberEquiv (x := x) f.symm = (fiberEquiv f).symm := by
  apply Equiv.ext
  intro e
  apply (fiberEquiv f).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_fiberEquiv_apply, coe_fiberEquiv_apply]
  exact coverMap_inv_apply f e.1

private theorem fiberEquiv_trans {p q r : ConnectedCoveringSpace X} (f : p ≅ q) (g : q ≅ r) :
    fiberEquiv (x := x) (f ≪≫ g) = (fiberEquiv f).trans (fiberEquiv g) := by
  apply Equiv.ext
  intro e
  apply Subtype.ext
  rw [coe_fiberEquiv_apply, Equiv.trans_apply, coe_fiberEquiv_apply,
    coe_fiberEquiv_apply]
  exact coverMap_comp_apply f.hom g.hom e.1

/-! ### Isomorphisms -/

/-- Isomorphism of fibre-numbered covers: an isomorphism of the underlying covers which carries
the point labelled `i` to the point labelled `i`, for every label `i`. -/
def ConnectedFiberNumberedCoverIso (c c' : ConnectedFiberNumberedCover x n) : Prop :=
  ∃ f : c.cover ≅ c'.cover, ∀ i, f.hom.hom.left (c.ν.symm i).1 = (c'.ν.symm i).1

/-- Isomorphism of pointed covers: an isomorphism of the underlying covers carrying the chosen
point to the chosen point. -/
def ConnectedPointedCoverIso (c c' : ConnectedPointedCover x n) : Prop :=
  ∃ f : c.cover ≅ c'.cover, f.hom.hom.left c.e.1 = c'.e.1

/-- Isomorphism of bare covers: an isomorphism of the underlying covers. -/
def ConnectedCoverIso (c c' : ConnectedCover x n) : Prop :=
  IsIsomorphic c.cover c'.cover

/-- A numbered isomorphism consists of a cover isomorphism preserving every fibre label. -/
@[simp]
theorem connectedFiberNumberedCoverIso_iff_exists {c c' : ConnectedFiberNumberedCover x n} :
    ConnectedFiberNumberedCoverIso c c' ↔
      ∃ f : c.cover ≅ c'.cover, ∀ i, f.hom.hom.left (c.ν.symm i).1 = (c'.ν.symm i).1 :=
  Iff.rfl

/-- A pointed isomorphism consists of a cover isomorphism preserving the chosen point. -/
@[simp]
theorem connectedPointedCoverIso_iff_exists {c c' : ConnectedPointedCover x n} :
    ConnectedPointedCoverIso c c' ↔
      ∃ f : c.cover ≅ c'.cover, f.hom.hom.left c.e.1 = c'.e.1 :=
  Iff.rfl

/-- Bare covers are isomorphic exactly when their underlying covers are. -/
@[simp]
theorem connectedCoverIso_iff_nonempty {c c' : ConnectedCover x n} :
    ConnectedCoverIso c c' ↔ Nonempty (c.cover ≅ c'.cover) :=
  Iff.rfl

/-- A numbered isomorphism is an isomorphism of covers whose bijection of fibres intertwines the
numberings. -/
private theorem connectedFiberNumberedCoverIso_iff_fiberEquiv
    {c c' : ConnectedFiberNumberedCover x n} :
    ConnectedFiberNumberedCoverIso c c' ↔
      ∃ f : c.cover ≅ c'.cover, (fiberEquiv f).trans c'.ν = c.ν := by
  refine exists_congr fun f => ⟨fun h => ?_, fun h i => ?_⟩
  · refine Equiv.ext fun e => ?_
    obtain ⟨i, rfl⟩ := c.ν.symm.surjective e
    rw [Equiv.trans_apply, Equiv.apply_symm_apply, ← Equiv.eq_symm_apply, Subtype.ext_iff,
      coe_fiberEquiv_apply, h i]
  · have hi : c.ν.symm i = (fiberEquiv f).symm (c'.ν.symm i) := by
      rw [← h]
      rfl
    rw [← coe_fiberEquiv_apply, hi, apply_symm_apply]

private theorem connectedPointedCoverIso_iff_fiberEquiv {c c' : ConnectedPointedCover x n} :
    ConnectedPointedCoverIso c c' ↔ ∃ f : c.cover ≅ c'.cover, fiberEquiv f c.e = c'.e :=
  exists_congr fun f => by rw [Subtype.ext_iff, coe_fiberEquiv_apply]

namespace ConnectedFiberNumberedCoverIso

@[refl]
theorem refl (c : ConnectedFiberNumberedCover x n) : ConnectedFiberNumberedCoverIso c c :=
  connectedFiberNumberedCoverIso_iff_fiberEquiv.2
    ⟨Iso.refl _, by rw [fiberEquiv_refl, Equiv.refl_trans]⟩

@[symm]
theorem symm {c c' : ConnectedFiberNumberedCover x n} (h : ConnectedFiberNumberedCoverIso c c') :
    ConnectedFiberNumberedCoverIso c' c := by
  obtain ⟨f, hf⟩ := connectedFiberNumberedCoverIso_iff_fiberEquiv.1 h
  refine connectedFiberNumberedCoverIso_iff_fiberEquiv.2 ⟨f.symm, ?_⟩
  rw [fiberEquiv_symm, ← hf, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]

@[trans]
theorem trans {c c' c'' : ConnectedFiberNumberedCover x n}
    (h : ConnectedFiberNumberedCoverIso c c') (h' : ConnectedFiberNumberedCoverIso c' c'') :
    ConnectedFiberNumberedCoverIso c c'' := by
  obtain ⟨f, hf⟩ := connectedFiberNumberedCoverIso_iff_fiberEquiv.1 h
  obtain ⟨g, hg⟩ := connectedFiberNumberedCoverIso_iff_fiberEquiv.1 h'
  refine connectedFiberNumberedCoverIso_iff_fiberEquiv.2 ⟨f ≪≫ g, ?_⟩
  rw [fiberEquiv_trans, Equiv.trans_assoc, hg, hf]

end ConnectedFiberNumberedCoverIso

namespace ConnectedPointedCoverIso

@[refl]
theorem refl (c : ConnectedPointedCover x n) : ConnectedPointedCoverIso c c :=
  connectedPointedCoverIso_iff_fiberEquiv.2
    ⟨Iso.refl _, by rw [fiberEquiv_refl, Equiv.refl_apply]⟩

@[symm]
theorem symm {c c' : ConnectedPointedCover x n} (h : ConnectedPointedCoverIso c c') :
    ConnectedPointedCoverIso c' c := by
  obtain ⟨f, hf⟩ := connectedPointedCoverIso_iff_fiberEquiv.1 h
  exact connectedPointedCoverIso_iff_fiberEquiv.2
    ⟨f.symm, by rw [fiberEquiv_symm, ← hf, symm_apply_apply]⟩

@[trans]
theorem trans {c c' c'' : ConnectedPointedCover x n} (h : ConnectedPointedCoverIso c c')
    (h' : ConnectedPointedCoverIso c' c'') : ConnectedPointedCoverIso c c'' := by
  obtain ⟨f, hf⟩ := connectedPointedCoverIso_iff_fiberEquiv.1 h
  obtain ⟨g, hg⟩ := connectedPointedCoverIso_iff_fiberEquiv.1 h'
  exact connectedPointedCoverIso_iff_fiberEquiv.2
    ⟨f ≪≫ g, by rw [fiberEquiv_trans, Equiv.trans_apply, hf, hg]⟩

end ConnectedPointedCoverIso

instance connectedFiberNumberedCoverSetoid (x : X) (n : ℕ) :
    Setoid (ConnectedFiberNumberedCover x n) where
  r := ConnectedFiberNumberedCoverIso
  iseqv := ⟨ConnectedFiberNumberedCoverIso.refl, .symm, .trans⟩

instance connectedPointedCoverSetoid (x : X) (n : ℕ) : Setoid (ConnectedPointedCover x n) where
  r := ConnectedPointedCoverIso
  iseqv := ⟨ConnectedPointedCoverIso.refl, .symm, .trans⟩

instance connectedCoverSetoid (x : X) (n : ℕ) : Setoid (ConnectedCover x n) :=
  (isIsomorphicSetoid (ConnectedCoveringSpace X)).comap ConnectedCover.cover

/-! ### Isomorphism classes -/

/-- Fibre-numbered connected covers of degree `n` up to label-preserving isomorphism. -/
@[expose] def ConnectedFiberNumberedCoverClass (x : X) (n : ℕ) : Type (u + 1) :=
  Quotient (connectedFiberNumberedCoverSetoid x n)

/-- Pointed connected covers of degree `n` up to pointed isomorphism. -/
@[expose] def ConnectedPointedCoverClass (x : X) (n : ℕ) : Type (u + 1) :=
  Quotient (connectedPointedCoverSetoid x n)

/-- Connected covers of degree `n` up to isomorphism. -/
@[expose] def ConnectedCoverClass (x : X) (n : ℕ) : Type (u + 1) :=
  Quotient (connectedCoverSetoid x n)

/-- The isomorphism class of a fibre-numbered cover. -/
@[expose] def ConnectedFiberNumberedCoverClass.mk (c : ConnectedFiberNumberedCover x n) :
    ConnectedFiberNumberedCoverClass x n :=
  Quotient.mk _ c

/-- The isomorphism class of a pointed cover. -/
@[expose] def ConnectedPointedCoverClass.mk (c : ConnectedPointedCover x n) :
    ConnectedPointedCoverClass x n :=
  Quotient.mk _ c

/-- The isomorphism class of a cover. -/
@[expose] def ConnectedCoverClass.mk (c : ConnectedCover x n) : ConnectedCoverClass x n :=
  Quotient.mk _ c

@[simp]
theorem ConnectedFiberNumberedCoverClass.mk_eq_mk_iff {c c' : ConnectedFiberNumberedCover x n} :
    mk c = mk c' ↔ ConnectedFiberNumberedCoverIso c c' :=
  Quotient.eq

@[simp]
theorem ConnectedPointedCoverClass.mk_eq_mk_iff {c c' : ConnectedPointedCover x n} :
    mk c = mk c' ↔ ConnectedPointedCoverIso c c' :=
  Quotient.eq

@[simp]
theorem ConnectedCoverClass.mk_eq_mk_iff {c c' : ConnectedCover x n} :
    mk c = mk c' ↔ ConnectedCoverIso c c' :=
  Quotient.eq

theorem ConnectedFiberNumberedCoverClass.mk_surjective :
    Function.Surjective (mk : ConnectedFiberNumberedCover x n → _) :=
  Quotient.mk_surjective

theorem ConnectedPointedCoverClass.mk_surjective :
    Function.Surjective (mk : ConnectedPointedCover x n → _) :=
  Quotient.mk_surjective

theorem ConnectedCoverClass.mk_surjective :
    Function.Surjective (mk : ConnectedCover x n → _) :=
  Quotient.mk_surjective

/-! ### The forgetful maps -/

/-- Forgetting the numbering of the fibre. -/
def ConnectedFiberNumberedCover.forgetNumbering (c : ConnectedFiberNumberedCover x n) :
    ConnectedCover x n where
  cover := c.cover
  nonempty_equiv_fin := ⟨c.ν⟩
  pathConnected := c.pathConnected

/-- Keeping only the point labelled `i`. -/
-- The type of `e` depends on the projected cover, so this definition must expose that projection.
@[expose] def ConnectedFiberNumberedCover.markLabel (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) :
    ConnectedPointedCover x n where
  cover := c.cover
  e := c.ν.symm i
  nonempty_equiv_fin := ⟨c.ν⟩
  pathConnected := c.pathConnected

/-- Forgetting the chosen point. -/
def ConnectedPointedCover.forgetPoint (c : ConnectedPointedCover x n) :
    ConnectedCover x n where
  cover := c.cover
  nonempty_equiv_fin := c.nonempty_equiv_fin
  pathConnected := c.pathConnected

@[simp]
theorem ConnectedFiberNumberedCover.forgetNumbering_cover (c : ConnectedFiberNumberedCover x n) :
    c.forgetNumbering.cover = c.cover :=
  (rfl)

@[simp]
theorem ConnectedFiberNumberedCover.markLabel_cover (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (c.markLabel i).cover = c.cover :=
  (rfl)

@[simp]
theorem ConnectedFiberNumberedCover.markLabel_e (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (c.markLabel i).e = c.ν.symm i :=
  (rfl)

@[simp]
theorem ConnectedPointedCover.forgetPoint_cover (c : ConnectedPointedCover x n) :
    c.forgetPoint.cover = c.cover :=
  (rfl)

/-- A cover with some numbering chosen. -/
noncomputable def ConnectedCover.numbering (c : ConnectedCover x n) :
    ConnectedFiberNumberedCover x n where
  cover := c.cover
  ν := c.nonempty_equiv_fin.some
  pathConnected := c.pathConnected

/-- Chooses an arbitrary numbering of the fibre of a pointed cover. -/
-- Applying the chosen numbering to `c.e` requires its projected cover to be definitionally
-- `c.cover`.
@[expose] noncomputable def ConnectedPointedCover.numbering (c : ConnectedPointedCover x n) :
    ConnectedFiberNumberedCover x n where
  cover := c.cover
  ν := c.nonempty_equiv_fin.some
  pathConnected := c.pathConnected

@[simp]
theorem ConnectedCover.numbering_cover (c : ConnectedCover x n) : c.numbering.cover = c.cover :=
  (rfl)

@[simp]
theorem ConnectedPointedCover.numbering_cover (c : ConnectedPointedCover x n) :
    c.numbering.cover = c.cover :=
  (rfl)

@[simp]
theorem ConnectedFiberNumberedCover.forgetPoint_markLabel (c : ConnectedFiberNumberedCover x n)
    (i : Fin n) : (c.markLabel i).forgetPoint = c.forgetNumbering :=
  (rfl)

@[simp]
theorem ConnectedCover.forgetNumbering_numbering (c : ConnectedCover x n) :
    c.numbering.forgetNumbering = c :=
  (rfl)

/-- A pointed cover is its chosen numbering with the label of its chosen point marked. -/
@[simp]
theorem ConnectedPointedCover.markLabel_numbering (c : ConnectedPointedCover x n) :
    c.numbering.markLabel (c.numbering.ν c.e) = c := by
  obtain ⟨cover, e, h, hp⟩ := c
  exact congrArg (fun e' => ConnectedPointedCover.mk cover e' h hp) (symm_apply_apply _ e)

/-- Forgetting the numbering, on isomorphism classes. -/
def ConnectedFiberNumberedCoverClass.forgetNumbering :
    ConnectedFiberNumberedCoverClass x n → ConnectedCoverClass x n :=
  Quotient.map ConnectedFiberNumberedCover.forgetNumbering fun _ _ h => by
    obtain ⟨f, -⟩ := h
    exact Nonempty.intro f

/-- Keeping only the point labelled `i`, on isomorphism classes: a label-preserving isomorphism
preserves in particular the point labelled `i`. -/
def ConnectedFiberNumberedCoverClass.markLabel (i : Fin n) :
    ConnectedFiberNumberedCoverClass x n → ConnectedPointedCoverClass x n :=
  Quotient.map (·.markLabel i) fun _ _ h => by
    obtain ⟨f, hf⟩ := h
    exact Exists.intro f (hf i)

/-- Forgetting the chosen point, on isomorphism classes. -/
def ConnectedPointedCoverClass.forgetPoint :
    ConnectedPointedCoverClass x n → ConnectedCoverClass x n :=
  Quotient.map ConnectedPointedCover.forgetPoint fun _ _ h => by
    obtain ⟨f, -⟩ := h
    exact Nonempty.intro f

@[simp]
theorem ConnectedFiberNumberedCoverClass.forgetNumbering_mk (c : ConnectedFiberNumberedCover x n) :
    (mk c).forgetNumbering = ConnectedCoverClass.mk c.forgetNumbering :=
  (rfl)

@[simp]
theorem ConnectedFiberNumberedCoverClass.markLabel_mk (i : Fin n)
    (c : ConnectedFiberNumberedCover x n) :
    (mk c).markLabel i = ConnectedPointedCoverClass.mk (c.markLabel i) :=
  (rfl)

@[simp]
theorem ConnectedPointedCoverClass.forgetPoint_mk (c : ConnectedPointedCover x n) :
    (mk c).forgetPoint = ConnectedCoverClass.mk c.forgetPoint :=
  (rfl)

/-- The forgetful triangle commutes: marking a label and then forgetting the point is forgetting
the numbering. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.forgetPoint_markLabel (i : Fin n)
    (C : ConnectedFiberNumberedCoverClass x n) :
    (C.markLabel i).forgetPoint = C.forgetNumbering :=
  Quotient.inductionOn C fun _ => rfl

theorem ConnectedFiberNumberedCoverClass.forgetNumbering_surjective :
    Function.Surjective (forgetNumbering : ConnectedFiberNumberedCoverClass x n → _) := by
  rintro ⟨c⟩
  exact ⟨mk c.numbering, rfl⟩

/-- Every pointed class is obtained by marking a label in a numbered class. -/
theorem ConnectedPointedCoverClass.exists_markLabel_eq (C : ConnectedPointedCoverClass x n) :
    ∃ (N : ConnectedFiberNumberedCoverClass x n) (i : Fin n), N.markLabel i = C := by
  obtain ⟨c, rfl⟩ := mk_surjective C
  exact ⟨.mk c.numbering, c.numbering.ν c.e, congrArg mk c.markLabel_numbering⟩

/-! ### Relabelling the fibre -/

namespace ConnectedFiberNumberedCover

/-- The symmetric group on the labels acts on numberings by relabelling: `τ • ν = ν.trans τ`. -/
instance : SMul (Perm (Fin n)) (ConnectedFiberNumberedCover x n) where
  smul τ c := ⟨c.cover, c.ν.trans τ, c.pathConnected⟩

@[simp]
theorem smul_cover (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    (τ • c).cover = c.cover :=
  (rfl)

@[simp]
theorem smul_ν (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    (τ • c).ν = c.ν.trans τ :=
  (rfl)

instance : MulAction (Perm (Fin n)) (ConnectedFiberNumberedCover x n) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem forgetNumbering_smul (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    (τ • c).forgetNumbering = c.forgetNumbering :=
  (rfl)

@[simp]
theorem markLabel_smul (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) (i : Fin n) :
    (τ • c).markLabel (τ i) = c.markLabel i := by
  have h : (τ • c).ν.symm (τ i) = c.ν.symm i := by simp
  exact congrArg (fun e => ConnectedPointedCover.mk c.cover e ⟨c.ν⟩ c.pathConnected) h

/-- An isomorphism of the underlying covers makes two numbered covers isomorphic after the
relabelling it induces on the fibre. -/
private theorem exists_smul_iso_of_iso {c c' : ConnectedFiberNumberedCover x n}
    (f : c.cover ≅ c'.cover) :
    ∃ τ : Perm (Fin n), ConnectedFiberNumberedCoverIso (τ • c) c' ∧
      ∀ i, τ i = c'.ν (fiberEquiv f (c.ν.symm i)) :=
  ⟨(c.ν.symm.trans (fiberEquiv f)).trans c'.ν,
    connectedFiberNumberedCoverIso_iff_fiberEquiv.2 ⟨f, by ext; simp⟩, fun _ => rfl⟩

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

instance : SMul (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n) where
  smul τ := Quotient.map (τ • ·) fun _ _ h => h.smul τ

@[simp]
theorem smul_mk (τ : Perm (Fin n)) (c : ConnectedFiberNumberedCover x n) :
    τ • mk c = mk (τ • c) :=
  (rfl)

instance : MulAction (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n) where
  one_smul C := Quotient.inductionOn C fun c => congrArg mk (one_smul _ c)
  mul_smul τ σ C := Quotient.inductionOn C fun c => congrArg mk (mul_smul τ σ c)

@[simp]
theorem forgetNumbering_smul (τ : Perm (Fin n)) (C : ConnectedFiberNumberedCoverClass x n) :
    (τ • C).forgetNumbering = C.forgetNumbering :=
  Quotient.inductionOn C fun _ => rfl

@[simp]
theorem markLabel_smul (τ : Perm (Fin n)) (C : ConnectedFiberNumberedCoverClass x n)
    (i : Fin n) : (τ • C).markLabel (τ i) = C.markLabel i :=
  Quotient.inductionOn C fun c => congrArg ConnectedPointedCoverClass.mk (c.markLabel_smul τ i)

/-- **Forgetting the numbering is passing to the relabelling orbit.** Two numbered classes have
the same underlying cover exactly when a relabelling carries one to the other. -/
@[simp]
theorem forgetNumbering_eq_forgetNumbering_iff {C C' : ConnectedFiberNumberedCoverClass x n} :
    C.forgetNumbering = C'.forgetNumbering ↔ ∃ τ : Perm (Fin n), τ • C = C' := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := mk_surjective C
    obtain ⟨c', rfl⟩ := mk_surjective C'
    rw [forgetNumbering_mk, forgetNumbering_mk] at h
    obtain ⟨f⟩ := ConnectedCoverClass.mk_eq_mk_iff.1 h
    obtain ⟨τ, hτ, -⟩ := exists_smul_iso_of_iso f
    exact ⟨τ, by rw [smul_mk, mk_eq_mk_iff.2 hτ]⟩
  · rintro ⟨τ, rfl⟩
    exact (forgetNumbering_smul τ C).symm

/-- **Marking a label is passing to the diagonal relabelling orbit.** Two numbered classes with
marked labels give the same pointed class exactly when a relabelling carries the first class to
the second and the first label to the second. -/
@[simp]
theorem markLabel_eq_markLabel_iff {C C' : ConnectedFiberNumberedCoverClass x n} {i j : Fin n} :
    C.markLabel i = C'.markLabel j ↔ ∃ τ : Perm (Fin n), τ • C = C' ∧ τ i = j := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := mk_surjective C
    obtain ⟨c', rfl⟩ := mk_surjective C'
    rw [markLabel_mk, markLabel_mk] at h
    obtain ⟨f, hf⟩ := ConnectedPointedCoverClass.mk_eq_mk_iff.1 h
    obtain ⟨τ, hτ, hτi⟩ := exists_smul_iso_of_iso f
    have he : fiberEquiv f (c.ν.symm i) = c'.ν.symm j :=
      Subtype.ext ((coe_fiberEquiv_apply f _).trans hf)
    refine ⟨τ, by rw [smul_mk, mk_eq_mk_iff.2 hτ], ?_⟩
    rw [hτi]
    exact (congrArg c'.ν he).trans (apply_symm_apply _ _)
  · rintro ⟨τ, rfl, rfl⟩
    exact (markLabel_smul τ C i).symm

/-- The bare isomorphism classes of connected covers of degree `n` are the relabelling orbits of
the numbered classes. -/
noncomputable def orbitRelQuotientEquiv :
    MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n) ≃
      ConnectedCoverClass x n :=
  Equiv.ofBijective
    (Quotient.lift forgetNumbering fun _ _ ⟨τ, hτ⟩ =>
      (forgetNumbering_eq_forgetNumbering_iff.2 ⟨τ, hτ⟩).symm)
    ⟨fun C C' => Quotient.inductionOn₂ C C' fun _ _ h =>
        Quotient.sound (by
          obtain ⟨τ, hτ⟩ := forgetNumbering_eq_forgetNumbering_iff.1 h
          exact ⟨τ⁻¹, inv_smul_eq_iff.2 hτ.symm⟩),
      fun C => by
        obtain ⟨N, h⟩ := forgetNumbering_surjective C
        exact ⟨Quotient.mk _ N, h⟩⟩

@[simp]
theorem orbitRelQuotientEquiv_mk (C : ConnectedFiberNumberedCoverClass x n) :
    orbitRelQuotientEquiv (Quotient.mk _ C) = C.forgetNumbering :=
  (rfl)

/-- The pointed isomorphism classes of connected covers of degree `n` are the orbits of the
diagonal relabelling action on numbered classes with a marked label. -/
noncomputable def markedOrbitRelQuotientEquiv :
    MulAction.orbitRel.Quotient (Perm (Fin n)) (ConnectedFiberNumberedCoverClass x n × Fin n) ≃
      ConnectedPointedCoverClass x n :=
  Equiv.ofBijective
    (Quotient.lift (fun Ci => Ci.1.markLabel Ci.2) fun _ _ ⟨τ, hτ⟩ =>
      (markLabel_eq_markLabel_iff.2 ⟨τ, congrArg Prod.fst hτ, congrArg Prod.snd hτ⟩).symm)
    ⟨fun C C' => Quotient.inductionOn₂ C C' fun _ _ h =>
        Quotient.sound (by
          obtain ⟨τ, hτ, hτi⟩ := markLabel_eq_markLabel_iff.1 h
          refine ⟨τ⁻¹, Prod.ext ?_ ?_⟩
          · exact inv_smul_eq_iff.2 hτ.symm
          · simp [← hτi]),
      fun C => by
        obtain ⟨N, i, h⟩ := C.exists_markLabel_eq
        exact ⟨Quotient.mk _ (N, i), h⟩⟩

@[simp]
theorem markedOrbitRelQuotientEquiv_mk (C : ConnectedFiberNumberedCoverClass x n) (i : Fin n) :
    markedOrbitRelQuotientEquiv (Quotient.mk _ (C, i)) = C.markLabel i :=
  (rfl)

end ConnectedFiberNumberedCoverClass

/-! ### Degree and inhabited fibres -/

namespace ConnectedCover

/-- A path from `x` to `y` identifies their fibres, so the degree agrees at the two points. -/
theorem nonempty_equiv_fin_of (c : ConnectedCover x n) {y : X} (γ : Path x y) :
    Nonempty (⇑c.cover.proj ⁻¹' {y} ≃ Fin n) :=
  c.nonempty_equiv_fin.map fun ν => (coveringFiberEquiv c.cover.isCoveringMap_proj
    (Path.Homotopic.Quotient.mk γ)).symm.trans ν

variable [PathConnectedSpace X]

/-- A connected cover of a path-connected space has positive degree. -/
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
  obtain ⟨ν⟩ := c.nonempty_equiv_fin
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨i⟩ := this
  let e := ν.symm i
  exact ⟨mk ⟨c.cover, e, c.nonempty_equiv_fin, c.pathConnected⟩, rfl⟩

end TauCeti
