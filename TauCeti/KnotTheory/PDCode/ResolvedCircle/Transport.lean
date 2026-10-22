/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.DisjointUnion.Basic
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Basic
public import TauCeti.KnotTheory.PDCode.RotateCrossing

/-!
# Transport of the circles of a smoothed PD-code

The circles of a smoothed PD-code (`TauCeti.PDCode.ResolvedCircle`) are built from half-edge
labels, so two codes describing the same smoothed diagram have different, but canonically
bijective, circle types. The Khovanov chain groups are tensor products indexed by these circles,
so every comparison of diagrams has to carry such a bijection along, functorially.

A `TauCeti.PDCode.SmoothingEquiv D s D' s'` is a bijection of half-edges carrying the arcs of `D`
to the arcs of `D'` and the traversal of `D` smoothed by `s` to the traversal of `D'` smoothed by
`s'`, together with a bijection between the labels of the crossing-free circles. It induces a
bijection of resolved circles, `TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr`, sending the
circle through a half-edge to the circle through its image. Smoothing equivalences form a
groupoid, and the induced bijections respect identities, inverses and composition.

The smoothing equivalences provided here are those of the native operations which keep the
smoothed diagram:

* relabelling half-edges and crossings (`TauCeti.PDCode.relabel`), where the state is read at the
  old crossing names;
* mirroring (`TauCeti.PDCode.mirror`), which exchanges the `A`- and `B`-smoothings and so negates
  the state;
* reading a crossing from another slot (`TauCeti.PDCode.rotateCrossing`);
* permuting the labels of the crossing-free circles.

Finally, the circles of a disjoint union (`TauCeti.PDCode.disjointUnion`) are the circles of the
two summands, smoothed by the two restrictions of the state
(`TauCeti.PDCode.disjointUnionResolvedCircleEquiv`).

## Main definitions

* `TauCeti.PDCode.SmoothingEquiv`: an isomorphism of smoothed PD-codes.
* `TauCeti.PDCode.SmoothingEquiv.crossingCircleCongr`,
  `TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr`: the induced bijections of circles.
* `TauCeti.PDCode.SmoothingEquiv.relabel`, `TauCeti.PDCode.SmoothingEquiv.mirror`,
  `TauCeti.PDCode.SmoothingEquiv.rotateCrossing`,
  `TauCeti.PDCode.SmoothingEquiv.crossinglessPerm`: the smoothing equivalences of the native
  operations.
* `TauCeti.PDCode.disjointUnionResolvedCircleEquiv`: the circles of a disjoint union.

## Main results

* `TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr_refl`,
  `TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr_symm`,
  `TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr_trans`: the identity, inverse and
  composition laws.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359-426,
  §2 (the circles of a resolution).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PDCode

variable {n m r : ℕ}

/-- An isomorphism between the PD-code `D` smoothed according to the state `s` and the PD-code
`D'` smoothed according to `s'`: a bijection of half-edges carrying the arc matching of `D` to
that of `D'` and the smoothed traversal `TauCeti.PDCode.statePerm D s` to `D'.statePerm s'`,
together with a bijection between the labels of the crossing-free circles. It induces a bijection
between the circles of the two smoothed diagrams
(`TauCeti.PDCode.SmoothingEquiv.resolvedCircleCongr`). -/
@[ext]
structure SmoothingEquiv (D : PDCode n) (s : Fin n → Bool) (D' : PDCode m) (s' : Fin m → Bool)
    where
  /-- The bijection of half-edges. -/
  halfEdgeEquiv : Fin (4 * n) ≃ Fin (4 * m)
  /-- The bijection between the labels of the crossing-free circles. -/
  crossinglessEquiv : Fin D.crossinglessComponentCount ≃ Fin D'.crossinglessComponentCount
  /-- The half-edge bijection carries the arc matching of `D` to that of `D'`. -/
  edgePair_apply (x : Fin (4 * n)) :
    D'.edgePair.val (halfEdgeEquiv x) = halfEdgeEquiv (D.edgePair.val x)
  /-- The half-edge bijection carries the smoothed traversal of `D` to that of `D'`. -/
  statePerm_apply (x : Fin (4 * n)) :
    D'.statePerm s' (halfEdgeEquiv x) = halfEdgeEquiv (D.statePerm s x)

namespace SmoothingEquiv

variable {D : PDCode n} {s : Fin n → Bool} {D' : PDCode m} {s' : Fin m → Bool}
  {D'' : PDCode r} {s'' : Fin r → Bool}

/-! ### The groupoid of smoothing equivalences -/

/-- The identity smoothing equivalence. -/
def refl (D : PDCode n) (s : Fin n → Bool) : D.SmoothingEquiv s D s where
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := Equiv.refl _
  edgePair_apply _ := rfl
  statePerm_apply _ := rfl

/-- The identity smoothing equivalence is the identity on half-edges. -/
@[simp]
theorem refl_halfEdgeEquiv (D : PDCode n) (s : Fin n → Bool) :
    (refl D s).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- The identity smoothing equivalence is the identity on crossing-free labels. -/
@[simp]
theorem refl_crossinglessEquiv (D : PDCode n) (s : Fin n → Bool) :
    (refl D s).crossinglessEquiv = Equiv.refl _ :=
  (rfl)

/-- The inverse of a smoothing equivalence. -/
def symm (e : D.SmoothingEquiv s D' s') : D'.SmoothingEquiv s' D s where
  halfEdgeEquiv := e.halfEdgeEquiv.symm
  crossinglessEquiv := e.crossinglessEquiv.symm
  edgePair_apply x := e.halfEdgeEquiv.injective <| by
    rw [← e.edgePair_apply, apply_symm_apply, apply_symm_apply]
  statePerm_apply x := e.halfEdgeEquiv.injective <| by
    rw [← e.statePerm_apply, apply_symm_apply, apply_symm_apply]

/-- The inverse smoothing equivalence inverts the half-edge bijection. -/
@[simp]
theorem symm_halfEdgeEquiv (e : D.SmoothingEquiv s D' s') :
    e.symm.halfEdgeEquiv = e.halfEdgeEquiv.symm :=
  (rfl)

/-- The inverse smoothing equivalence inverts the bijection of crossing-free labels. -/
@[simp]
theorem symm_crossinglessEquiv (e : D.SmoothingEquiv s D' s') :
    e.symm.crossinglessEquiv = e.crossinglessEquiv.symm :=
  (rfl)

/-- The composite of two smoothing equivalences. -/
def trans (e : D.SmoothingEquiv s D' s') (f : D'.SmoothingEquiv s' D'' s'') :
    D.SmoothingEquiv s D'' s'' where
  halfEdgeEquiv := e.halfEdgeEquiv.trans f.halfEdgeEquiv
  crossinglessEquiv := e.crossinglessEquiv.trans f.crossinglessEquiv
  edgePair_apply x := by simp only [trans_apply, f.edgePair_apply, e.edgePair_apply]
  statePerm_apply x := by simp only [trans_apply, f.statePerm_apply, e.statePerm_apply]

/-- A composite smoothing equivalence composes the half-edge bijections. -/
@[simp]
theorem trans_halfEdgeEquiv (e : D.SmoothingEquiv s D' s') (f : D'.SmoothingEquiv s' D'' s'') :
    (e.trans f).halfEdgeEquiv = e.halfEdgeEquiv.trans f.halfEdgeEquiv :=
  (rfl)

/-- A composite smoothing equivalence composes the bijections of crossing-free labels. -/
@[simp]
theorem trans_crossinglessEquiv (e : D.SmoothingEquiv s D' s')
    (f : D'.SmoothingEquiv s' D'' s'') :
    (e.trans f).crossinglessEquiv = e.crossinglessEquiv.trans f.crossinglessEquiv :=
  (rfl)

/-- Inverting a smoothing equivalence twice gives it back. -/
@[simp]
theorem symm_symm (e : D.SmoothingEquiv s D' s') : e.symm.symm = e := by
  ext <;> simp

/-- The identity is a left unit for composition. -/
@[simp]
theorem refl_trans (e : D.SmoothingEquiv s D' s') : (refl D s).trans e = e := by
  ext <;> simp

/-- The identity is a right unit for composition. -/
@[simp]
theorem trans_refl (e : D.SmoothingEquiv s D' s') : e.trans (refl D' s') = e := by
  ext <;> simp

/-- A smoothing equivalence followed by its inverse is the identity. -/
@[simp]
theorem self_trans_symm (e : D.SmoothingEquiv s D' s') : e.trans e.symm = refl D s := by
  ext <;> simp

/-- The inverse of a smoothing equivalence followed by it is the identity. -/
@[simp]
theorem symm_trans_self (e : D.SmoothingEquiv s D' s') : e.symm.trans e = refl D' s' := by
  ext <;> simp

/-- Composition of smoothing equivalences is associative. -/
theorem trans_assoc {r' : ℕ} {D₃ : PDCode r'} {s₃ : Fin r' → Bool}
    (e : D.SmoothingEquiv s D' s') (f : D'.SmoothingEquiv s' D'' s'')
    (g : D''.SmoothingEquiv s'' D₃ s₃) : (e.trans f).trans g = e.trans (f.trans g) := by
  ext <;> simp

/-! ### The induced bijection of circles -/

/-- A smoothing equivalence transports the smoothed traversal. -/
theorem statePerm_eq_permCongr (e : D.SmoothingEquiv s D' s') :
    D'.statePerm s' = e.halfEdgeEquiv.permCongr (D.statePerm s) := by
  ext x
  obtain ⟨x, rfl⟩ := e.halfEdgeEquiv.surjective x
  rw [e.statePerm_apply, permCongr_apply, symm_apply_apply]

/-- Two half-edges lie on one circle of the smoothed `D'` exactly when their preimages under a
smoothing equivalence lie on one circle of the smoothed `D`. -/
theorem eqvGen_circleStep_apply_iff (e : D.SmoothingEquiv s D' s') {x y : Fin (4 * n)} :
    Relation.EqvGen (D'.CircleStep s') (e.halfEdgeEquiv x) (e.halfEdgeEquiv y) ↔
      Relation.EqvGen (D.CircleStep s) x y := by
  rw [PDCode.eqvGen_circleStep_iff, PDCode.eqvGen_circleStep_iff, e.statePerm_eq_permCongr,
    e.edgePair_apply, sameCycle_permCongr, sameCycle_permCongr]

/-- The bijection between the circles meeting a crossing induced by a smoothing equivalence: the
circle through a half-edge goes to the circle through its image. -/
def crossingCircleCongr (e : D.SmoothingEquiv s D' s') :
    D.CrossingCircle s ≃ D'.CrossingCircle s' :=
  Quotient.congr e.halfEdgeEquiv fun _ _ ↦ e.eqvGen_circleStep_apply_iff.symm

/-- The induced bijection sends the circle through a half-edge to the circle through its image. -/
@[simp]
theorem crossingCircleCongr_mk (e : D.SmoothingEquiv s D' s') (x : Fin (4 * n)) :
    e.crossingCircleCongr ⟦x⟧ = ⟦e.halfEdgeEquiv x⟧ :=
  Quotient.congr_mk _ _ x

/-- **The bijection of circles induced by a smoothing equivalence**: the circle through a
half-edge goes to the circle through its image, and the crossing-free circles are matched by the
bijection of their labels. -/
def resolvedCircleCongr (e : D.SmoothingEquiv s D' s') :
    D.ResolvedCircle s ≃ D'.ResolvedCircle s' :=
  e.crossingCircleCongr.sumCongr e.crossinglessEquiv

/-- On the circles meeting a crossing, the induced bijection is
`TauCeti.PDCode.SmoothingEquiv.crossingCircleCongr`. -/
@[simp]
theorem resolvedCircleCongr_inl (e : D.SmoothingEquiv s D' s') (c : D.CrossingCircle s) :
    e.resolvedCircleCongr (.inl c) = .inl (e.crossingCircleCongr c) :=
  (rfl)

/-- On the crossing-free circles, the induced bijection is the bijection of their labels. -/
@[simp]
theorem resolvedCircleCongr_inr (e : D.SmoothingEquiv s D' s')
    (i : Fin D.crossinglessComponentCount) :
    e.resolvedCircleCongr (.inr i) = .inr (e.crossinglessEquiv i) :=
  (rfl)

/-- The identity smoothing equivalence induces the identity on the circles meeting a crossing. -/
@[simp]
theorem crossingCircleCongr_refl : (refl D s).crossingCircleCongr = Equiv.refl _ := by
  ext c
  induction c using Quotient.inductionOn
  simp

/-- The inverse smoothing equivalence induces the inverse bijection of circles meeting a
crossing. -/
@[simp]
theorem crossingCircleCongr_symm (e : D.SmoothingEquiv s D' s') :
    e.symm.crossingCircleCongr = e.crossingCircleCongr.symm := by
  rw [eq_comm, Equiv.symm_eq_iff_trans_eq_refl]
  ext c
  induction c using Quotient.inductionOn
  simp

/-- A composite of smoothing equivalences induces the composite bijection of circles meeting a
crossing. -/
@[simp]
theorem crossingCircleCongr_trans (e : D.SmoothingEquiv s D' s')
    (f : D'.SmoothingEquiv s' D'' s'') :
    (e.trans f).crossingCircleCongr = e.crossingCircleCongr.trans f.crossingCircleCongr := by
  ext c
  induction c using Quotient.inductionOn
  simp

/-- **The identity law**: the identity smoothing equivalence induces the identity on circles. -/
@[simp]
theorem resolvedCircleCongr_refl : (refl D s).resolvedCircleCongr = Equiv.refl _ := by
  ext (c | i) <;> simp

/-- **The inverse law**: the inverse smoothing equivalence induces the inverse bijection of
circles. -/
@[simp]
theorem resolvedCircleCongr_symm (e : D.SmoothingEquiv s D' s') :
    e.symm.resolvedCircleCongr = e.resolvedCircleCongr.symm := by
  rw [resolvedCircleCongr, resolvedCircleCongr, crossingCircleCongr_symm, symm_crossinglessEquiv,
    Equiv.sumCongr_symm]

/-- **The composition law**: a composite of smoothing equivalences induces the composite
bijection of circles. -/
@[simp]
theorem resolvedCircleCongr_trans (e : D.SmoothingEquiv s D' s')
    (f : D'.SmoothingEquiv s' D'' s'') :
    (e.trans f).resolvedCircleCongr = e.resolvedCircleCongr.trans f.resolvedCircleCongr := by
  ext (c | i) <;> simp

/-! ### The smoothing equivalences of the native operations -/

/-- **Relabelling** the half-edges along `half` and the crossings along `cross` is a smoothing
equivalence from `D` smoothed by `t ∘ cross` to the relabelled code smoothed by `t`: the state is
read at the old crossing names. The crossing-free circles keep their labels. -/
def relabel (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)
    (t : Fin m → Bool) : D.SmoothingEquiv (t ∘ cross) (D.relabel half cross) t where
  halfEdgeEquiv := half
  crossinglessEquiv := finCongr (D.relabel_crossinglessComponentCount half cross).symm
  edgePair_apply x := by
    rw [relabel_edgePair, PerfectMatching.congr_val_apply_apply]
  statePerm_apply x := by
    rw [statePerm_relabel, permCongr_apply, symm_apply_apply]

/-- The relabelling smoothing equivalence is the half-edge relabelling. -/
@[simp]
theorem relabel_halfEdgeEquiv (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) (t : Fin m → Bool) : (relabel D half cross t).halfEdgeEquiv = half :=
  (rfl)

/-- The relabelling smoothing equivalence keeps the labels of the crossing-free circles. -/
@[simp]
theorem relabel_crossinglessEquiv (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) (t : Fin m → Bool) :
    (relabel D half cross t).crossinglessEquiv =
      finCongr (D.relabel_crossinglessComponentCount half cross).symm :=
  (rfl)

/-- **Mirroring** exchanges the `A`- and `B`-smoothings, so it is a smoothing equivalence from `D`
smoothed by the negated state to the mirror smoothed by `s`, which is the identity on
half-edges. -/
def mirror (D : PDCode n) (s : Fin n → Bool) :
    D.SmoothingEquiv (fun i ↦ !s i) D.mirror s where
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := finCongr D.mirror_crossinglessComponentCount.symm
  edgePair_apply x := by rw [mirror_edgePair, refl_apply, refl_apply]
  statePerm_apply x := by rw [statePerm_mirror, refl_apply, refl_apply]

/-- The mirror smoothing equivalence is the identity on half-edges. -/
@[simp]
theorem mirror_halfEdgeEquiv (D : PDCode n) (s : Fin n → Bool) :
    (mirror D s).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- The mirror smoothing equivalence keeps the labels of the crossing-free circles. -/
@[simp]
theorem mirror_crossinglessEquiv (D : PDCode n) (s : Fin n → Bool) :
    (mirror D s).crossinglessEquiv = finCongr D.mirror_crossinglessComponentCount.symm :=
  (rfl)

/-- **Reading a crossing from another slot** does not change the smoothed diagram: it is a
smoothing equivalence which is the identity on half-edges. -/
def rotateCrossing (D : PDCode n) (i : Fin n) (s : Fin n → Bool) :
    D.SmoothingEquiv s (D.rotateCrossing i) s where
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := finCongr (D.rotateCrossing_crossinglessComponentCount i).symm
  edgePair_apply x := by rw [rotateCrossing_edgePair, refl_apply, refl_apply]
  statePerm_apply x := by rw [statePerm_rotateCrossing, refl_apply, refl_apply]

/-- The rotation smoothing equivalence is the identity on half-edges. -/
@[simp]
theorem rotateCrossing_halfEdgeEquiv (D : PDCode n) (i : Fin n) (s : Fin n → Bool) :
    (rotateCrossing D i s).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- The rotation smoothing equivalence keeps the labels of the crossing-free circles. -/
@[simp]
theorem rotateCrossing_crossinglessEquiv (D : PDCode n) (i : Fin n) (s : Fin n → Bool) :
    (rotateCrossing D i s).crossinglessEquiv =
      finCongr (D.rotateCrossing_crossinglessComponentCount i).symm :=
  (rfl)

/-- **Permuting the labels of the crossing-free circles** is a smoothing equivalence of every
smoothed code to itself, which is the identity on half-edges. -/
def crossinglessPerm (D : PDCode n) (s : Fin n → Bool)
    (σ : Perm (Fin D.crossinglessComponentCount)) : D.SmoothingEquiv s D s where
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := σ
  edgePair_apply _ := rfl
  statePerm_apply _ := rfl

/-- Permuting the crossing-free labels is the identity on half-edges. -/
@[simp]
theorem crossinglessPerm_halfEdgeEquiv (D : PDCode n) (s : Fin n → Bool)
    (σ : Perm (Fin D.crossinglessComponentCount)) :
    (crossinglessPerm D s σ).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- Permuting the crossing-free labels by `σ` acts on them by `σ`. -/
@[simp]
theorem crossinglessPerm_crossinglessEquiv (D : PDCode n) (s : Fin n → Bool)
    (σ : Perm (Fin D.crossinglessComponentCount)) :
    (crossinglessPerm D s σ).crossinglessEquiv = σ :=
  (rfl)

end SmoothingEquiv

/-! ### The circles of a disjoint union -/

section DisjointUnion

variable (D : PDCode n) (E : PDCode m) (s : Fin (n + m) → Bool)

/-- Two half-edges of a disjoint union lie on one circle exactly when they come from the same
summand and lie on one circle of that summand, smoothed by the restricted state. -/
theorem eqvGen_circleStep_disjointUnion_iff {x y : Fin (4 * n) ⊕ Fin (4 * m)} :
    Relation.EqvGen ((D.disjointUnion E).CircleStep s) (disjointUnionHalfEdgeEquiv n m x)
        (disjointUnionHalfEdgeEquiv n m y) ↔
      Sum.LiftRel (Relation.EqvGen (D.CircleStep (s ∘ Fin.castAdd m)))
        (Relation.EqvGen (E.CircleStep (s ∘ Fin.natAdd n))) x y := by
  rw [eqvGen_circleStep_iff, statePerm_disjointUnion, disjointUnion_edgePair_val,
    permCongr_apply, symm_apply_apply, sameCycle_permCongr, sameCycle_permCongr]
  rcases x with x | x <;> rcases y with y | y
  · simp [sameCycle_sumCongr_inl, eqvGen_circleStep_iff]
  · simp
  · simpa using ⟨fun h ↦ not_sameCycle_sumCongr_inl_inr _ _ _ _ h.symm,
      fun h ↦ not_sameCycle_sumCongr_inl_inr _ _ _ _ h.symm⟩
  · simp [sameCycle_sumCongr_inr, eqvGen_circleStep_iff]

/-- The circles meeting a crossing of a smoothed disjoint union are those of the two summands,
smoothed by the two restrictions of the state. -/
def disjointUnionCrossingCircleEquiv :
    (D.disjointUnion E).CrossingCircle s ≃
      D.CrossingCircle (s ∘ Fin.castAdd m) ⊕ E.CrossingCircle (s ∘ Fin.natAdd n) where
  toFun := Quotient.lift (fun z ↦ ((disjointUnionHalfEdgeEquiv n m).symm z).map (⟦·⟧) (⟦·⟧))
    fun z w h ↦ by
      obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective z
      obtain ⟨y, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective w
      rw [symm_apply_apply, symm_apply_apply]
      cases (D.eqvGen_circleStep_disjointUnion_iff E s).mp h with
      | inl hr => exact congrArg Sum.inl (Quotient.sound hr)
      | inr hr => exact congrArg Sum.inr (Quotient.sound hr)
  invFun := Sum.elim
    (Quotient.lift (fun x ↦ ⟦disjointUnionHalfEdgeEquiv n m (.inl x)⟧) fun _ _ h ↦
      Quotient.sound ((D.eqvGen_circleStep_disjointUnion_iff E s).mpr (.inl h)))
    (Quotient.lift (fun y ↦ ⟦disjointUnionHalfEdgeEquiv n m (.inr y)⟧) fun _ _ h ↦
      Quotient.sound ((D.eqvGen_circleStep_disjointUnion_iff E s).mpr (.inr h)))
  left_inv c := by
    induction c using Quotient.inductionOn with | h z => ?_
    obtain ⟨x | x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective z <;> simp
  right_inv := by
    rintro (c | c) <;> induction c using Quotient.inductionOn <;> simp

/-- A circle through a half-edge of the first summand is a circle of the first summand. -/
@[simp]
theorem disjointUnionCrossingCircleEquiv_mk_inl (x : Fin (4 * n)) :
    D.disjointUnionCrossingCircleEquiv E s ⟦disjointUnionHalfEdgeEquiv n m (.inl x)⟧ =
      .inl ⟦x⟧ := by
  simp [disjointUnionCrossingCircleEquiv]

/-- A circle through a half-edge of the second summand is a circle of the second summand. -/
@[simp]
theorem disjointUnionCrossingCircleEquiv_mk_inr (y : Fin (4 * m)) :
    D.disjointUnionCrossingCircleEquiv E s ⟦disjointUnionHalfEdgeEquiv n m (.inr y)⟧ =
      .inr ⟦y⟧ := by
  simp [disjointUnionCrossingCircleEquiv]

/-- **The circles of a smoothed disjoint union** are the circles of the two summands, smoothed by
the two restrictions of the state. The circle through a half-edge of a summand is the circle
through it in that summand, and the crossing-free circles of the first summand are numbered
before those of the second. -/
def disjointUnionResolvedCircleEquiv :
    (D.disjointUnion E).ResolvedCircle s ≃
      D.ResolvedCircle (s ∘ Fin.castAdd m) ⊕ E.ResolvedCircle (s ∘ Fin.natAdd n) :=
  ((D.disjointUnionCrossingCircleEquiv E s).sumCongr
    ((finCongr (D.disjointUnion_crossinglessComponentCount E)).trans finSumFinEquiv.symm)).trans
    (sumSumSumComm _ _ _ _)

/-- The circle through a half-edge of the first summand is the circle through it in the first
summand. -/
@[simp]
theorem disjointUnionResolvedCircleEquiv_inl_mk_inl (x : Fin (4 * n)) :
    D.disjointUnionResolvedCircleEquiv E s (.inl ⟦disjointUnionHalfEdgeEquiv n m (.inl x)⟧) =
      .inl (.inl ⟦x⟧) := by
  simp [disjointUnionResolvedCircleEquiv]

/-- The circle through a half-edge of the second summand is the circle through it in the second
summand. -/
@[simp]
theorem disjointUnionResolvedCircleEquiv_inl_mk_inr (y : Fin (4 * m)) :
    D.disjointUnionResolvedCircleEquiv E s (.inl ⟦disjointUnionHalfEdgeEquiv n m (.inr y)⟧) =
      .inr (.inl ⟦y⟧) := by
  simp [disjointUnionResolvedCircleEquiv]

/-- The crossing-free circles of the first summand are numbered first in the disjoint union. -/
@[simp]
theorem disjointUnionResolvedCircleEquiv_symm_inl_inr (i : Fin D.crossinglessComponentCount) :
    (D.disjointUnionResolvedCircleEquiv E s).symm (.inl (.inr i)) =
      .inr (finCongr (D.disjointUnion_crossinglessComponentCount E).symm
        (Fin.castAdd E.crossinglessComponentCount i)) := by
  simp [disjointUnionResolvedCircleEquiv]

/-- The crossing-free circles of the second summand are numbered after those of the first in the
disjoint union. -/
@[simp]
theorem disjointUnionResolvedCircleEquiv_symm_inr_inr (j : Fin E.crossinglessComponentCount) :
    (D.disjointUnionResolvedCircleEquiv E s).symm (.inr (.inr j)) =
      .inr (finCongr (D.disjointUnion_crossinglessComponentCount E).symm
        (Fin.natAdd D.crossinglessComponentCount j)) := by
  simp [disjointUnionResolvedCircleEquiv]

end DisjointUnion

end PDCode

end TauCeti
