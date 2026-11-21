/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Opposites
public import Mathlib.GroupTheory.Perm.Basic
public import TauCeti.KnotTheory.Foam.ClosedWeb.Basic

/-!
# Labelled closed webs

A labelled closed web assigns a label to each interval edge and each vertex-free circle of a
`ClosedWeb`, subject to an ordered rule at every trivalent vertex. Labels live in a type `Λ` with
an addition that need be neither commutative nor associative. At a vertex, `c` labels the end
whose orientation differs from the other two (slot zero of `ClosedWeb.ends`), and `a`, `b` label
the next two ends in cyclic order (slots one and two); the rule is the ordered equation
`a + b = c`. This one equation covers merges and splits alike: the merge/split role is recorded
by the underlying web, never inferred from labels, so it survives when labels coincide or vanish.

Because the rule is ordered, mirror reversal of cyclic orders does not preserve it: a mirrored
labelled web carries its labels in the additive opposite `Λᵃᵒᵖ`. When the label addition is
commutative the mirror of a labelling is again a labelling in `Λ`. Orientation reversal keeps the
odd end odd and the cyclic orders unchanged, so it preserves labellings with the same labels.

## Main definitions

* `TauCeti.ClosedWeb.IsLabeling`: the ordered vertex rule for an edge-label function.
* `TauCeti.LabeledClosedWeb`: a closed web with edge and circle labels satisfying the rule.
* `TauCeti.LabeledClosedWeb.Iso`: web isomorphisms preserving every label.
* `TauCeti.LabeledClosedWeb.map`: change of labels along an additive map.
* `TauCeti.LabeledClosedWeb.reverse`, `TauCeti.LabeledClosedWeb.mirror` and
  `TauCeti.LabeledClosedWeb.sum`: orientation reversal, mirror reversal into opposite labels,
  and disjoint union with its unit, associativity and symmetry isomorphisms.

## Main results

* `TauCeti.ClosedWeb.isLabeling_mirror_op_comp_iff`: mirroring corresponds to opposite labels.
* `TauCeti.ClosedWeb.isLabeling_theta_iff`: labellings of the theta web are determined by the
  ordered sum `ℓ 1 + ℓ 2 = ℓ 0`.
* `TauCeti.ClosedWeb.exists_isLabeling_theta_not_isLabeling_mirror`: with labels in the
  symmetric group `S₃`, a labelling of the theta web need not be a labelling of its mirror,
  since `(0 1)(1 2) ≠ (1 2)(0 1)`.
* `TauCeti.LabeledClosedWeb.nonempty_iso_circle_iff`: one-circle webs with labels `a` and `b`
  are isomorphic exactly when `a = b`.

The vertex convention is that of Goertz–Marino–Wedrich, *Monoidal 2-categories from foam
evaluation*, arXiv:2602.11120v1, Definition 3.12.
-/

public section

namespace TauCeti

universe u v w w'

variable {Λ : Type w} {Λ' : Type w'}

namespace ClosedWeb

variable (W : ClosedWeb.{u})

section IsLabeling

variable [Add Λ]

/-- An edge labelling satisfies the ordered vertex rule `a + b = c` at each vertex, where `c`
labels the end of odd orientation and `a`, `b` label the next two ends in cyclic order. -/
def IsLabeling (ℓ : W.Edge → Λ) : Prop :=
  ∀ v, ℓ (W.ends (v, 1)).1 + ℓ (W.ends (v, 2)).1 = ℓ (W.ends (v, 0)).1

variable {W}

theorem isLabeling_def {ℓ : W.Edge → Λ} :
    W.IsLabeling ℓ ↔ ∀ v, ℓ (W.ends (v, 1)).1 + ℓ (W.ends (v, 2)).1 = ℓ (W.ends (v, 0)).1 :=
  Iff.rfl

/-- The ordered vertex rule at one vertex. -/
theorem IsLabeling.add_eq {ℓ : W.Edge → Λ} (h : W.IsLabeling ℓ) (v : W.Vertex) :
    ℓ (W.ends (v, 1)).1 + ℓ (W.ends (v, 2)).1 = ℓ (W.ends (v, 0)).1 :=
  h v

/-- Every labelling of a vertex-free web is admissible. -/
theorem isLabeling_of_isEmpty_vertex [IsEmpty W.Vertex] (ℓ : W.Edge → Λ) : W.IsLabeling ℓ :=
  isEmptyElim

/-- Change of labels along an additive map preserves the vertex rule. -/
theorem IsLabeling.comp_addHom [Add Λ'] {ℓ : W.Edge → Λ} (h : W.IsLabeling ℓ) (f : Λ →ₙ+ Λ') :
    W.IsLabeling (f ∘ ℓ) :=
  fun v ↦ by simp only [Function.comp_apply, ← map_add, h.add_eq v]

/-- Orientation reversal keeps the odd end and the cyclic order, hence every labelling. -/
@[simp] theorem isLabeling_reverse_iff {ℓ : W.Edge → Λ} :
    W.reverse.IsLabeling ℓ ↔ W.IsLabeling ℓ :=
  Iff.rfl

/-- Mirror reversal exchanges the two ordered inputs of the vertex rule. -/
theorem isLabeling_mirror_iff {ℓ : W.Edge → Λ} :
    W.mirror.IsLabeling ℓ ↔
      ∀ v, ℓ (W.ends (v, 2)).1 + ℓ (W.ends (v, 1)).1 = ℓ (W.ends (v, 0)).1 :=
  Iff.rfl

/-- Mirror reversal corresponds to passing to the opposite label addition. -/
@[simp] theorem isLabeling_mirror_op_comp_iff {ℓ : W.Edge → Λ} :
    W.mirror.IsLabeling (AddOpposite.op ∘ ℓ) ↔ W.IsLabeling ℓ := by
  rw [isLabeling_mirror_iff]
  simp only [isLabeling_def, Function.comp_apply, ← AddOpposite.op_add, AddOpposite.op_inj]

/-- A labelling of a disjoint union is a labelling of each component. -/
@[simp] theorem isLabeling_sum_elim_iff {V : ClosedWeb.{v}} {ℓ : W.Edge → Λ}
    {ℓ' : V.Edge → Λ} :
    (W.sum V).IsLabeling (Sum.elim ℓ ℓ') ↔ W.IsLabeling ℓ ∧ V.IsLabeling ℓ' := by
  constructor
  · intro h
    exact ⟨fun v ↦ h (Sum.inl v), fun v ↦ h (Sum.inr v)⟩
  · rintro ⟨h, h'⟩ (v | v)
    · exact h v
    · exact h' v

/-- Labellings correspond under a web isomorphism. -/
theorem Iso.isLabeling_comp_edge_iff {V : ClosedWeb.{v}} (f : W.Iso V) {ℓ : V.Edge → Λ} :
    W.IsLabeling (ℓ ∘ f.edge) ↔ V.IsLabeling ℓ := by
  have key (v : W.Vertex) (i : Fin 3) :
      ℓ (f.edge (W.ends (v, i)).1) = ℓ (V.ends (f.vertex v, i)).1 := by
    rw [f.map_ends_apply]
  simp only [isLabeling_def, Function.comp_apply, key]
  exact f.vertex.forall_congr_right (q := fun v ↦
    ℓ (V.ends (v, 1)).1 + ℓ (V.ends (v, 2)).1 = ℓ (V.ends (v, 0)).1)

/-- The theta web has a single ordered vertex rule, shared by its merge and its split. -/
theorem isLabeling_theta_iff (ℓ : Fin 3 → Λ) : theta.IsLabeling ℓ ↔ ℓ 1 + ℓ 2 = ℓ 0 := by
  simp [isLabeling_def]

/-- The mirrored theta web has the ordered vertex rule with its two inputs exchanged. -/
theorem isLabeling_theta_mirror_iff (ℓ : Fin 3 → Λ) :
    theta.mirror.IsLabeling ℓ ↔ ℓ 2 + ℓ 1 = ℓ 0 := by
  simp [isLabeling_mirror_iff]

/-- With labels in the symmetric group `S₃`, a labelling of the theta web need not label its
mirror: the inputs `(0 1)` and `(1 2)` have ordered output `(0 1)(1 2)`, which is not
`(1 2)(0 1)`. -/
theorem exists_isLabeling_theta_not_isLabeling_mirror :
    ∃ ℓ : Fin 3 → Additive (Equiv.Perm (Fin 3)),
      theta.IsLabeling ℓ ∧ ¬theta.mirror.IsLabeling ℓ := by
  refine ⟨![.ofMul (Equiv.swap 0 1 * Equiv.swap 1 2), .ofMul (Equiv.swap 0 1),
    .ofMul (Equiv.swap 1 2)], ?_⟩
  rw [isLabeling_theta_iff, isLabeling_theta_mirror_iff]
  decide

end IsLabeling

variable {W}

/-- The all-zero labelling is admissible on every web. -/
theorem isLabeling_zero [AddZeroClass Λ] : W.IsLabeling (0 : W.Edge → Λ) :=
  fun _ ↦ add_zero 0

/-- For commutative label addition, mirror reversal preserves labellings. -/
@[simp] theorem isLabeling_mirror_iff_of_addCommMagma [AddCommMagma Λ] {ℓ : W.Edge → Λ} :
    W.mirror.IsLabeling ℓ ↔ W.IsLabeling ℓ := by
  rw [isLabeling_mirror_iff]
  exact forall_congr' fun v ↦ by rw [add_comm]

end ClosedWeb

/-- A closed web whose interval edges and vertex-free circles carry labels in `Λ`, satisfying
the ordered vertex rule `a + b = c` of `ClosedWeb.IsLabeling`. -/
structure LabeledClosedWeb (Λ : Type w) [Add Λ] extends ClosedWeb.{u} where
  /-- The label of each interval edge. -/
  edgeLabel : Edge → Λ
  /-- The label of each vertex-free circle. -/
  circleLabel : Circle → Λ
  /-- The edge labels satisfy the ordered vertex rule. -/
  isLabeling : toClosedWeb.IsLabeling edgeLabel

namespace LabeledClosedWeb

variable [Add Λ] (W : LabeledClosedWeb.{u} Λ)

/-- Isomorphisms of labelled webs: web isomorphisms preserving every edge and circle label. -/
structure Iso (V : LabeledClosedWeb.{v} Λ) extends W.toClosedWeb.Iso V.toClosedWeb where
  /-- Transport preserves edge labels. -/
  edgeLabel_edge : ∀ e, V.edgeLabel (edge e) = W.edgeLabel e
  /-- Transport preserves circle labels. -/
  circleLabel_circle : ∀ c, V.circleLabel (circle c) = W.circleLabel c

attribute [simp] Iso.edgeLabel_edge Iso.circleLabel_circle

namespace Iso

variable {W} {V : LabeledClosedWeb.{v} Λ}

/-- Isomorphisms of labelled webs are determined by their underlying web isomorphisms. -/
@[ext] theorem ext {f g : W.Iso V} (h : f.toIso = g.toIso) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity isomorphism of a labelled web. -/
def refl (W : LabeledClosedWeb.{u} Λ) : W.Iso W where
  toIso := ClosedWeb.Iso.refl W.toClosedWeb
  edgeLabel_edge _ := by simp
  circleLabel_circle _ := by simp

@[simp] theorem refl_toIso (W : LabeledClosedWeb.{u} Λ) :
    (refl W).toIso = ClosedWeb.Iso.refl W.toClosedWeb := (rfl)

/-- Inverse isomorphism of labelled webs. -/
def symm (f : W.Iso V) : V.Iso W where
  toIso := f.toIso.symm
  edgeLabel_edge e := by
    simpa using (f.edgeLabel_edge (f.edge.symm e)).symm
  circleLabel_circle c := by
    simpa using (f.circleLabel_circle (f.circle.symm c)).symm

@[simp] theorem symm_toIso (f : W.Iso V) : f.symm.toIso = f.toIso.symm := (rfl)

/-- Composition of isomorphisms of labelled webs. -/
def trans {U : LabeledClosedWeb Λ} (f : W.Iso V) (g : V.Iso U) : W.Iso U where
  toIso := f.toIso.trans g.toIso
  edgeLabel_edge e := by simp
  circleLabel_circle c := by simp

@[simp] theorem trans_toIso {U : LabeledClosedWeb Λ} (f : W.Iso V) (g : V.Iso U) :
    (f.trans g).toIso = f.toIso.trans g.toIso := (rfl)

@[simp] theorem symm_symm (f : W.Iso V) : f.symm.symm = f := by
  ext1
  simp

@[simp] theorem refl_trans (f : W.Iso V) : (refl W).trans f = f := by
  ext1
  simp

@[simp] theorem trans_refl (f : W.Iso V) : f.trans (refl V) = f := by
  ext1
  simp

@[simp] theorem symm_trans_self (f : W.Iso V) : f.symm.trans f = refl V := by
  ext1
  simp

@[simp] theorem self_trans_symm (f : W.Iso V) : f.trans f.symm = refl W := by
  ext1
  simp

/-- Composition of isomorphisms of labelled webs is associative. -/
theorem trans_assoc {U T : LabeledClosedWeb Λ} (f : W.Iso V) (g : V.Iso U) (h : U.Iso T) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext1
  simp [ClosedWeb.Iso.trans_assoc]

end Iso

/-! The record constructors below are reducible, like those of `ClosedWeb`, so that their
carriers and labels compute. Their label equations are explicit rewrite lemmas, not simp lemmas:
projections of these constructors already reduce. -/

/-- Change of labels along an additive map, which preserves the ordered vertex rule. -/
abbrev map [Add Λ'] (f : Λ →ₙ+ Λ') : LabeledClosedWeb.{u} Λ' where
  toClosedWeb := W.toClosedWeb
  edgeLabel := f ∘ W.edgeLabel
  circleLabel := f ∘ W.circleLabel
  isLabeling := W.isLabeling.comp_addHom f

theorem map_edgeLabel [Add Λ'] (f : Λ →ₙ+ Λ') (e : W.Edge) :
    (W.map f).edgeLabel e = f (W.edgeLabel e) := (rfl)

theorem map_circleLabel [Add Λ'] (f : Λ →ₙ+ Λ') (c : W.Circle) :
    (W.map f).circleLabel c = f (W.circleLabel c) := (rfl)

/-- Changing labels along the identity does nothing. -/
@[simp] theorem map_id : W.map (AddHom.id Λ) = W := (rfl)

/-- Changing labels twice is changing labels along the composite. -/
@[simp] theorem map_map {Λ'' : Type*} [Add Λ'] [Add Λ''] (f : Λ →ₙ+ Λ') (g : Λ' →ₙ+ Λ'') :
    (W.map f).map g = W.map (g.comp f) := (rfl)

/-- Reverse every interval orientation, keeping all labels. -/
abbrev reverse : LabeledClosedWeb.{u} Λ where
  toClosedWeb := W.toClosedWeb.reverse
  edgeLabel := W.edgeLabel
  circleLabel := W.circleLabel
  isLabeling := ClosedWeb.isLabeling_reverse_iff.mpr W.isLabeling

theorem reverse_edgeLabel (e : W.Edge) : W.reverse.edgeLabel e = W.edgeLabel e := (rfl)

theorem reverse_circleLabel (c : W.Circle) : W.reverse.circleLabel c = W.circleLabel c := (rfl)

/-- Orientation reversal of labelled webs is an involution. -/
@[simp] theorem reverse_reverse : W.reverse.reverse = W := by
  rcases W with ⟨W, ℓ, c, h⟩
  dsimp only [reverse]
  congr 1
  exact W.reverse_reverse

/-- Reverse cyclic orders. The two ordered inputs at each vertex are exchanged, so the labels
pass to the additive opposite `Λᵃᵒᵖ`. -/
abbrev mirror : LabeledClosedWeb.{u} Λᵃᵒᵖ where
  toClosedWeb := W.toClosedWeb.mirror
  edgeLabel := AddOpposite.op ∘ W.edgeLabel
  circleLabel := AddOpposite.op ∘ W.circleLabel
  isLabeling := ClosedWeb.isLabeling_mirror_op_comp_iff.mpr W.isLabeling

theorem mirror_edgeLabel (e : W.Edge) :
    W.mirror.edgeLabel e = AddOpposite.op (W.edgeLabel e) := (rfl)

theorem mirror_circleLabel (c : W.Circle) :
    W.mirror.circleLabel c = AddOpposite.op (W.circleLabel c) := (rfl)

/-- Orientation reversal and mirror reversal commute. -/
theorem mirror_reverse : W.reverse.mirror = W.mirror.reverse := (rfl)

/-- The labelled web of a finite set of vertex-free circles with specified labels. -/
abbrev circles (C : Type u) [Finite C] (ℓ : C → Λ) : LabeledClosedWeb.{u} Λ where
  toClosedWeb := ClosedWeb.circles C
  edgeLabel := PEmpty.elim
  circleLabel := ℓ
  isLabeling := ClosedWeb.isLabeling_of_isEmpty_vertex _

/-- The empty labelled web. -/
abbrev empty : LabeledClosedWeb.{u} Λ := circles PEmpty PEmpty.elim

/-- One vertex-free circle with label `a`. -/
abbrev circle (a : Λ) : LabeledClosedWeb.{u} Λ := circles PUnit fun _ ↦ a

/-- One-circle labelled webs are isomorphic exactly when their labels agree. -/
theorem nonempty_iso_circle_iff {a b : Λ} :
    Nonempty ((circle a : LabeledClosedWeb.{u} Λ).Iso (circle b : LabeledClosedWeb.{v} Λ)) ↔
      a = b := by
  constructor
  · rintro ⟨f⟩
    exact (f.circleLabel_circle PUnit.unit).symm
  · rintro rfl
    exact ⟨⟨⟨Equiv.equivOfIsEmpty _ _, Equiv.equivOfIsEmpty _ _, Equiv.punitEquivPUnit,
      fun x ↦ isEmptyElim x.1⟩, fun e ↦ isEmptyElim e, fun _ ↦ rfl⟩⟩

/-- Disjoint union of labelled webs, retaining every label. -/
abbrev sum (V : LabeledClosedWeb.{v} Λ) : LabeledClosedWeb.{max u v} Λ where
  toClosedWeb := W.toClosedWeb.sum V.toClosedWeb
  edgeLabel := Sum.elim W.edgeLabel V.edgeLabel
  circleLabel := Sum.elim W.circleLabel V.circleLabel
  isLabeling := ClosedWeb.isLabeling_sum_elim_iff.mpr ⟨W.isLabeling, V.isLabeling⟩

theorem sum_edgeLabel (V : LabeledClosedWeb.{v} Λ) (e : W.Edge ⊕ V.Edge) :
    (W.sum V).edgeLabel e = Sum.elim W.edgeLabel V.edgeLabel e := (rfl)

theorem sum_circleLabel (V : LabeledClosedWeb.{v} Λ) (c : W.Circle ⊕ V.Circle) :
    (W.sum V).circleLabel c = Sum.elim W.circleLabel V.circleLabel c := (rfl)

/-- The disjoint-union left unit isomorphism of labelled webs. -/
def emptySum : (empty.{v}.sum W).Iso W where
  toIso := W.toClosedWeb.emptySum
  edgeLabel_edge e := by rcases e with e | e; exacts [e.elim, by simp]
  circleLabel_circle c := by rcases c with c | c; exacts [c.elim, by simp]

@[simp] theorem emptySum_toIso : W.emptySum.toIso = W.toClosedWeb.emptySum := (rfl)

/-- The disjoint-union right unit isomorphism of labelled webs. -/
def sumEmpty : (W.sum empty.{v}).Iso W where
  toIso := W.toClosedWeb.sumEmpty
  edgeLabel_edge e := by rcases e with e | e; exacts [by simp, e.elim]
  circleLabel_circle c := by rcases c with c | c; exacts [by simp, c.elim]

@[simp] theorem sumEmpty_toIso : W.sumEmpty.toIso = W.toClosedWeb.sumEmpty := (rfl)

/-- The disjoint-union associativity isomorphism of labelled webs. -/
def sumAssoc (V : LabeledClosedWeb.{v} Λ) (U : LabeledClosedWeb Λ) :
    ((W.sum V).sum U).Iso (W.sum (V.sum U)) where
  toIso := W.toClosedWeb.sumAssoc V.toClosedWeb U.toClosedWeb
  edgeLabel_edge e := by rcases e with (e | e) | e <;> simp
  circleLabel_circle c := by rcases c with (c | c) | c <;> simp

@[simp] theorem sumAssoc_toIso (V : LabeledClosedWeb.{v} Λ) (U : LabeledClosedWeb Λ) :
    (W.sumAssoc V U).toIso = W.toClosedWeb.sumAssoc V.toClosedWeb U.toClosedWeb := (rfl)

/-- Exchange the two components of a disjoint union of labelled webs. -/
def sumComm (V : LabeledClosedWeb.{v} Λ) : (W.sum V).Iso (V.sum W) where
  toIso := W.toClosedWeb.sumComm V.toClosedWeb
  edgeLabel_edge e := by rcases e with e | e <;> simp
  circleLabel_circle c := by rcases c with c | c <;> simp

@[simp] theorem sumComm_toIso (V : LabeledClosedWeb.{v} Λ) :
    (W.sumComm V).toIso = W.toClosedWeb.sumComm V.toClosedWeb := (rfl)

namespace Iso

variable {W} {V : LabeledClosedWeb.{v} Λ}

/-- Isomorphisms of labelled webs correspond under change of labels. -/
def map [Add Λ'] (f : W.Iso V) (g : Λ →ₙ+ Λ') : (W.map g).Iso (V.map g) where
  toIso := f.toIso
  edgeLabel_edge e := congrArg g (f.edgeLabel_edge e)
  circleLabel_circle c := congrArg g (f.circleLabel_circle c)

@[simp] theorem map_toIso [Add Λ'] (f : W.Iso V) (g : Λ →ₙ+ Λ') : (f.map g).toIso = f.toIso :=
  (rfl)

/-- Reverse both labelled webs in an isomorphism. -/
def reverse (f : W.Iso V) : W.reverse.Iso V.reverse where
  toIso := f.toIso.reverse
  edgeLabel_edge e := by simp
  circleLabel_circle c := by simp

@[simp] theorem reverse_toIso (f : W.Iso V) : f.reverse.toIso = f.toIso.reverse := (rfl)

/-- Mirror both labelled webs in an isomorphism. -/
def mirror (f : W.Iso V) : W.mirror.Iso V.mirror where
  toIso := f.toIso.mirror
  edgeLabel_edge e := by simp
  circleLabel_circle c := by simp

@[simp] theorem mirror_toIso (f : W.Iso V) : f.mirror.toIso = f.toIso.mirror := (rfl)

/-- Disjoint union transports isomorphisms of labelled webs on both components. -/
def sum {W' V' : LabeledClosedWeb Λ} (f : W.Iso V) (g : W'.Iso V') :
    (W.sum W').Iso (V.sum V') where
  toIso := f.toIso.sum g.toIso
  edgeLabel_edge e := by rcases e with e | e <;> simp
  circleLabel_circle c := by rcases c with c | c <;> simp

@[simp] theorem sum_toIso {W' V' : LabeledClosedWeb Λ} (f : W.Iso V) (g : W'.Iso V') :
    (f.sum g).toIso = f.toIso.sum g.toIso := (rfl)

end Iso

/-- The oriented theta web with edges one and two labelled `a` and `b`, and edge zero, the odd
end at both the merge and the split, labelled `a + b`. -/
abbrev theta (a b : Λ) : LabeledClosedWeb Λ where
  toClosedWeb := ClosedWeb.theta
  edgeLabel := ![a + b, a, b]
  circleLabel := PEmpty.elim
  isLabeling := (ClosedWeb.isLabeling_theta_iff _).mpr rfl

theorem theta_edgeLabel (a b : Λ) : (theta a b).edgeLabel = ![a + b, a, b] := (rfl)

end LabeledClosedWeb

end TauCeti
