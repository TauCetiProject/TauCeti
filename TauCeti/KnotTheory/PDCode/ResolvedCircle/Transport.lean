/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.DisjointUnion.Basic
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Saddle
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

Transport carrying the slots of a crossing bijectively preserves the circles through that
crossing and hence their number. When the source and target transports of a saddle use the
same half-edge and isolated-circle bijections, the induced circle bijections commute with its
saddle correspondence. This supplies the circle-level naturality square for resolution maps.

The smoothing equivalences provided here are those of the native operations which keep the
smoothed diagram:

* relabelling half-edges and crossings (`TauCeti.PDCode.relabel`), where the state is read at the
  old crossing names;
* mirroring (`TauCeti.PDCode.mirror`), which exchanges the `A`- and `B`-smoothings and so negates
  the state;
* reading a crossing from another slot (`TauCeti.PDCode.rotateCrossing`);
* permuting the labels of the crossing-free circles.

A `TauCeti.PDCode.ResolutionEquiv D D'` identifies all smoothings of `D` with those of `D'` at
once, along a bijection of crossings, by one half-edge bijection and one bijection of crossing-free
labels. It gives a smoothing equivalence for every state, and so transports the whole cube of
resolutions. Relabelling, reading a crossing from another slot and permuting the crossing-free
labels are such identifications.

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
* `TauCeti.PDCode.ResolutionEquiv`: an identification of all smoothings of two codes, with its
  smoothing equivalences `TauCeti.PDCode.ResolutionEquiv.smoothingEquiv` and the instances
  `TauCeti.PDCode.ResolutionEquiv.relabel`, `TauCeti.PDCode.ResolutionEquiv.rotateCrossing` and
  `TauCeti.PDCode.ResolutionEquiv.crossinglessPerm`.
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

/-- A smoothing equivalence transports the native arc matching by conjugation. -/
theorem edgePair_val_eq_permCongr (e : D.SmoothingEquiv s D' s') :
    D'.edgePair.val = e.halfEdgeEquiv.permCongr D.edgePair.val := by
  ext x
  obtain ⟨x, rfl⟩ := e.halfEdgeEquiv.surjective x
  rw [e.edgePair_apply, permCongr_apply, symm_apply_apply]

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

/-! ### Transport of the circles through a crossing and of saddle correspondences -/

/-- A smoothing equivalence carrying the slots of `c` bijectively to those of `c'` carries
exactly the circles through `c` to those through `c'`. The slot bijection permits a different
choice of the first slot at the crossing. -/
theorem image_crossingCircleCongr_circlesAt (e : D.SmoothingEquiv s D' s')
    {c : Fin n} {c' : Fin m} (slots : Fin 4 ≃ Fin 4)
    (hcross : ∀ k, e.halfEdgeEquiv (D.crossing c k) = D'.crossing c' (slots k)) :
    (D.circlesAt s c).image e.crossingCircleCongr = D'.circlesAt s' c' := by
  ext C
  simp only [Finset.mem_image, mem_circlesAt]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨slots k, by rw [crossingCircleCongr_mk, hcross]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟦D.crossing c (slots.symm k)⟧, ⟨slots.symm k, rfl⟩, by
      simp only [crossingCircleCongr_mk, hcross, slots.apply_symm_apply]⟩

/-- The number of circles through a crossing is preserved when its slots are transported
bijectively by a smoothing equivalence. In particular, the merge/split conditions transport. -/
theorem card_circlesAt_eq (e : D.SmoothingEquiv s D' s')
    {c : Fin n} {c' : Fin m} (slots : Fin 4 ≃ Fin 4)
    (hcross : ∀ k, e.halfEdgeEquiv (D.crossing c k) = D'.crossing c' (slots k)) :
    (D.circlesAt s c).card = (D'.circlesAt s' c').card := by
  rw [← e.image_crossingCircleCongr_circlesAt slots hcross,
    Finset.card_image_of_injective _ e.crossingCircleCongr.injective]

/-- Saddle correspondences commute with smoothing equivalences that use the same half-edge
and isolated-circle bijections at the two endpoints. Every unaffected circle is retained. -/
theorem resolvedCircleCongr_saddleResolvedCircleMap
    {t : Fin n → Bool} {t' : Fin m → Bool} {c : Fin n} {c' : Fin m}
    (es : D.SmoothingEquiv s D' s') (et : D.SmoothingEquiv t D' t')
    (hhalf : es.halfEdgeEquiv = et.halfEdgeEquiv)
    (hisolated : es.crossinglessEquiv = et.crossinglessEquiv)
    (hst : ∀ j, j ≠ c → s j = t j) (hst' : ∀ j, j ≠ c' → s' j = t' j)
    (ht : (D.circlesAt t c).card = 1) (ht' : (D'.circlesAt t' c').card = 1)
    (C : D.ResolvedCircle s) :
    et.resolvedCircleCongr (D.saddleResolvedCircleMap hst ht C) =
      D'.saddleResolvedCircleMap hst' ht' (es.resolvedCircleCongr C) := by
  rcases C with C | i
  · obtain ⟨x, rfl⟩ := Quotient.exists_rep C
    simp [hhalf]
  · simp [hisolated]

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
smoothed by a state `t` to the mirror smoothed by the complementary state `s`, which is the
identity on half-edges. -/
def mirror (D : PDCode n) {s t : Fin n → Bool} (h : ∀ i, t i = !s i) :
    D.SmoothingEquiv t D.mirror s where
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := finCongr D.mirror_crossinglessComponentCount.symm
  edgePair_apply x := by rw [mirror_edgePair, refl_apply, refl_apply]
  statePerm_apply x := by rw [statePerm_mirror, refl_apply, refl_apply, ← funext h]

/-- The mirror smoothing equivalence is the identity on half-edges. -/
@[simp]
theorem mirror_halfEdgeEquiv (D : PDCode n) {s t : Fin n → Bool} (h : ∀ i, t i = !s i) :
    (mirror D h).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- The mirror smoothing equivalence keeps the labels of the crossing-free circles. -/
@[simp]
theorem mirror_crossinglessEquiv (D : PDCode n) {s t : Fin n → Bool} (h : ∀ i, t i = !s i) :
    (mirror D h).crossinglessEquiv = finCongr D.mirror_crossinglessComponentCount.symm :=
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

/-! ### Transport of all smoothings at once -/

/-- An identification of all the smoothings of `D` with those of `D'` along a bijection of
crossings: a bijection of half-edges carrying the arcs of `D` to those of `D'` and the slots of
each crossing `c` to those of `crossingEquiv c`, such that for every state `t` of `D'` it carries
the traversal of `D` smoothed by `t ∘ crossingEquiv` to the traversal of `D'` smoothed by `t`,
together with a bijection between the labels of the crossing-free circles. Each state then gives a
smoothing equivalence (`TauCeti.PDCode.ResolutionEquiv.smoothingEquiv`), all with the same
half-edge and isolated-circle bijections, so these transports commute with every saddle of the
cube of resolutions.

Relabelling (`TauCeti.PDCode.ResolutionEquiv.relabel`), reading a crossing from another slot
(`TauCeti.PDCode.ResolutionEquiv.rotateCrossing`) and permuting the crossing-free labels
(`TauCeti.PDCode.ResolutionEquiv.crossinglessPerm`) are such identifications. Mirroring is not:
it exchanges the `A`- and `B`-smoothings. -/
@[ext]
structure ResolutionEquiv (D : PDCode n) (D' : PDCode m) where
  /-- The bijection of crossings. -/
  crossingEquiv : Fin n ≃ Fin m
  /-- The bijection of half-edges. -/
  halfEdgeEquiv : Fin (4 * n) ≃ Fin (4 * m)
  /-- The bijection between the labels of the crossing-free circles. -/
  crossinglessEquiv : Fin D.crossinglessComponentCount ≃ Fin D'.crossinglessComponentCount
  /-- The half-edge bijection carries the arc matching of `D` to that of `D'`. -/
  edgePair_apply (x : Fin (4 * n)) :
    D'.edgePair.val (halfEdgeEquiv x) = halfEdgeEquiv (D.edgePair.val x)
  /-- The half-edge bijection carries the traversal of `D` smoothed by `t ∘ crossingEquiv` to the
  traversal of `D'` smoothed by `t`. -/
  statePerm_apply (t : Fin m → Bool) (x : Fin (4 * n)) :
    D'.statePerm t (halfEdgeEquiv x) = halfEdgeEquiv (D.statePerm (t ∘ crossingEquiv) x)
  /-- The half-edge bijection carries the slots of `c` bijectively to those of
  `crossingEquiv c`. -/
  exists_slots (c : Fin n) :
    ∃ slots : Fin 4 ≃ Fin 4, ∀ k, halfEdgeEquiv (D.crossing c k) = D'.crossing (crossingEquiv c)
      (slots k)

namespace ResolutionEquiv

variable {D : PDCode n} {D' : PDCode m} {D'' : PDCode r}

/-- The smoothing equivalence of an identification of all smoothings, from `D` smoothed by `s` to
`D'` smoothed by a state `t` which agrees with `s` along the crossing bijection. -/
def smoothingEquiv (E : D.ResolutionEquiv D') {s : Fin n → Bool} {t : Fin m → Bool}
    (h : ∀ i, t (E.crossingEquiv i) = s i) : D.SmoothingEquiv s D' t where
  halfEdgeEquiv := E.halfEdgeEquiv
  crossinglessEquiv := E.crossinglessEquiv
  edgePair_apply := E.edgePair_apply
  statePerm_apply x := by
    rw [E.statePerm_apply, show t ∘ E.crossingEquiv = s from funext h]

/-- The smoothing equivalences of an identification of all smoothings share its half-edge
bijection. -/
@[simp]
theorem smoothingEquiv_halfEdgeEquiv (E : D.ResolutionEquiv D') {s : Fin n → Bool}
    {t : Fin m → Bool} (h : ∀ i, t (E.crossingEquiv i) = s i) :
    (E.smoothingEquiv h).halfEdgeEquiv = E.halfEdgeEquiv :=
  (rfl)

/-- The smoothing equivalences of an identification of all smoothings share its bijection of
crossing-free labels. -/
@[simp]
theorem smoothingEquiv_crossinglessEquiv (E : D.ResolutionEquiv D') {s : Fin n → Bool}
    {t : Fin m → Bool} (h : ∀ i, t (E.crossingEquiv i) = s i) :
    (E.smoothingEquiv h).crossinglessEquiv = E.crossinglessEquiv :=
  (rfl)

/-- The identity identification of the smoothings of `D`. -/
def refl (D : PDCode n) : D.ResolutionEquiv D where
  crossingEquiv := Equiv.refl _
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := Equiv.refl _
  edgePair_apply _ := rfl
  statePerm_apply _ _ := rfl
  exists_slots _ := ⟨Equiv.refl _, fun _ ↦ rfl⟩

/-- The identity identification is the identity on crossings. -/
@[simp]
theorem refl_crossingEquiv (D : PDCode n) : (refl D).crossingEquiv = Equiv.refl _ :=
  (rfl)

/-- The identity identification is the identity on half-edges. -/
@[simp]
theorem refl_halfEdgeEquiv (D : PDCode n) : (refl D).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- The identity identification is the identity on crossing-free labels. -/
@[simp]
theorem refl_crossinglessEquiv (D : PDCode n) : (refl D).crossinglessEquiv = Equiv.refl _ :=
  (rfl)

/-- The identity identification gives the identity smoothing equivalences. -/
@[simp]
theorem refl_smoothingEquiv (D : PDCode n) {s : Fin n → Bool}
    (h : ∀ i, s ((refl D).crossingEquiv i) = s i) :
    (refl D).smoothingEquiv h = SmoothingEquiv.refl D s :=
  (rfl)

/-- The inverse of an identification of all smoothings. -/
def symm (E : D.ResolutionEquiv D') : D'.ResolutionEquiv D where
  crossingEquiv := E.crossingEquiv.symm
  halfEdgeEquiv := E.halfEdgeEquiv.symm
  crossinglessEquiv := E.crossinglessEquiv.symm
  edgePair_apply x := E.halfEdgeEquiv.injective <| by
    rw [← E.edgePair_apply, apply_symm_apply, apply_symm_apply]
  statePerm_apply t x := E.halfEdgeEquiv.injective <| by
    simpa [Function.comp_assoc] using
      (E.statePerm_apply (t ∘ E.crossingEquiv.symm) (E.halfEdgeEquiv.symm x)).symm
  exists_slots c := by
    obtain ⟨σ, hσ⟩ := E.exists_slots (E.crossingEquiv.symm c)
    refine ⟨σ.symm, fun k ↦ E.halfEdgeEquiv.injective ?_⟩
    rw [hσ, apply_symm_apply, apply_symm_apply, apply_symm_apply]

/-- The inverse identification inverts the crossing bijection. -/
@[simp]
theorem symm_crossingEquiv (E : D.ResolutionEquiv D') :
    E.symm.crossingEquiv = E.crossingEquiv.symm :=
  (rfl)

/-- The inverse identification inverts the half-edge bijection. -/
@[simp]
theorem symm_halfEdgeEquiv (E : D.ResolutionEquiv D') :
    E.symm.halfEdgeEquiv = E.halfEdgeEquiv.symm :=
  (rfl)

/-- The inverse identification inverts the bijection of crossing-free labels. -/
@[simp]
theorem symm_crossinglessEquiv (E : D.ResolutionEquiv D') :
    E.symm.crossinglessEquiv = E.crossinglessEquiv.symm :=
  (rfl)

/-- The smoothing equivalences of the inverse identification are the inverses of the smoothing
equivalences. -/
@[simp]
theorem smoothingEquiv_symm (E : D.ResolutionEquiv D') {s : Fin n → Bool} {t : Fin m → Bool}
    (h : ∀ i, t (E.crossingEquiv i) = s i) :
    (E.smoothingEquiv h).symm =
      E.symm.smoothingEquiv fun i ↦ by simpa using (h (E.crossingEquiv.symm i)).symm :=
  (rfl)

/-- The composite of two identifications of all smoothings. -/
def trans (E : D.ResolutionEquiv D') (F : D'.ResolutionEquiv D'') : D.ResolutionEquiv D'' where
  crossingEquiv := E.crossingEquiv.trans F.crossingEquiv
  halfEdgeEquiv := E.halfEdgeEquiv.trans F.halfEdgeEquiv
  crossinglessEquiv := E.crossinglessEquiv.trans F.crossinglessEquiv
  edgePair_apply x := by simp [F.edgePair_apply, E.edgePair_apply]
  statePerm_apply t x := by simp [F.statePerm_apply, E.statePerm_apply, Function.comp_assoc]
  exists_slots c := by
    obtain ⟨σ, hσ⟩ := E.exists_slots c
    obtain ⟨τ, hτ⟩ := F.exists_slots (E.crossingEquiv c)
    exact ⟨σ.trans τ, fun k ↦ by simp only [Equiv.trans_apply]; rw [hσ, hτ]⟩

/-- The crossing bijection of a composite is the composite of the crossing bijections. -/
@[simp]
theorem trans_crossingEquiv (E : D.ResolutionEquiv D') (F : D'.ResolutionEquiv D'') :
    (E.trans F).crossingEquiv = E.crossingEquiv.trans F.crossingEquiv :=
  (rfl)

/-- The half-edge bijection of a composite is the composite of the half-edge bijections. -/
@[simp]
theorem trans_halfEdgeEquiv (E : D.ResolutionEquiv D') (F : D'.ResolutionEquiv D'') :
    (E.trans F).halfEdgeEquiv = E.halfEdgeEquiv.trans F.halfEdgeEquiv :=
  (rfl)

/-- The bijection of crossing-free labels of a composite is the composite of these
bijections. -/
@[simp]
theorem trans_crossinglessEquiv (E : D.ResolutionEquiv D') (F : D'.ResolutionEquiv D'') :
    (E.trans F).crossinglessEquiv = E.crossinglessEquiv.trans F.crossinglessEquiv :=
  (rfl)

/-- The smoothing equivalences of a composite are the composites of the smoothing
equivalences. -/
@[simp]
theorem smoothingEquiv_trans_smoothingEquiv (E : D.ResolutionEquiv D')
    (F : D'.ResolutionEquiv D'') {s : Fin n → Bool} {t : Fin m → Bool} {u : Fin r → Bool}
    (h₁ : ∀ i, t (E.crossingEquiv i) = s i) (h₂ : ∀ i, u (F.crossingEquiv i) = t i) :
    (E.smoothingEquiv h₁).trans (F.smoothingEquiv h₂) =
      (E.trans F).smoothingEquiv fun i ↦ by simpa using (h₂ _).trans (h₁ i) :=
  (rfl)

/-- Inverting an identification of all smoothings twice gives it back. -/
@[simp]
theorem symm_symm (E : D.ResolutionEquiv D') : E.symm.symm = E := by
  ext <;> simp

/-- An identification of all smoothings followed by its inverse is the identity. -/
@[simp]
theorem self_trans_symm (E : D.ResolutionEquiv D') : E.trans E.symm = refl D := by
  ext <;> simp

/-- The inverse of an identification of all smoothings followed by it is the identity. -/
@[simp]
theorem symm_trans_self (E : D.ResolutionEquiv D') : E.symm.trans E = refl D' := by
  ext <;> simp

/-- **Relabelling** the half-edges along `half` and the crossings along `cross` identifies the
smoothings of `D` with those of the relabelled code. The crossing-free circles keep their
labels. -/
def relabel (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    D.ResolutionEquiv (D.relabel half cross) where
  crossingEquiv := cross
  halfEdgeEquiv := half
  crossinglessEquiv := finCongr (D.relabel_crossinglessComponentCount half cross).symm
  edgePair_apply x := by rw [relabel_edgePair, PerfectMatching.congr_val_apply_apply]
  statePerm_apply t := (SmoothingEquiv.relabel D half cross t).statePerm_apply
  exists_slots c := ⟨Equiv.refl _, fun k ↦ by rw [crossing_relabel, symm_apply_apply, refl_apply]⟩

/-- Relabelling acts on crossings by `cross`. -/
@[simp]
theorem relabel_crossingEquiv (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : (relabel D half cross).crossingEquiv = cross :=
  (rfl)

/-- Relabelling acts on half-edges by `half`. -/
@[simp]
theorem relabel_halfEdgeEquiv (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : (relabel D half cross).halfEdgeEquiv = half :=
  (rfl)

/-- Relabelling keeps the labels of the crossing-free circles. -/
@[simp]
theorem relabel_crossinglessEquiv (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) :
    (relabel D half cross).crossinglessEquiv =
      finCongr (D.relabel_crossinglessComponentCount half cross).symm :=
  (rfl)

/-- Relabelling is a smoothing equivalence of every state; it is
`TauCeti.PDCode.SmoothingEquiv.relabel`. -/
@[simp]
theorem relabel_smoothingEquiv (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) (t : Fin m → Bool)
    (h : ∀ i, t ((relabel D half cross).crossingEquiv i) = (t ∘ cross) i) :
    (relabel D half cross).smoothingEquiv h = SmoothingEquiv.relabel D half cross t :=
  (rfl)

/-- **Reading a crossing from another slot** keeps every smoothing: it identifies the smoothings
of `D` with those of the rotated code, by the identity on crossings and half-edges. -/
def rotateCrossing (D : PDCode n) (i : Fin n) : D.ResolutionEquiv (D.rotateCrossing i) where
  crossingEquiv := Equiv.refl _
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := finCongr (D.rotateCrossing_crossinglessComponentCount i).symm
  edgePair_apply x := by rw [rotateCrossing_edgePair, refl_apply, refl_apply]
  statePerm_apply t := (SmoothingEquiv.rotateCrossing D i t).statePerm_apply
  exists_slots c := by
    by_cases hc : c = i
    · subst hc
      -- Slot `k` of the rotated crossing is slot `k + 1` of the old one.
      exact ⟨Equiv.subRight 1, fun k ↦ by simp⟩
    · exact ⟨Equiv.refl _, fun k ↦ by simp [hc]⟩

/-- Reading a crossing from another slot is the identity on crossings. -/
@[simp]
theorem rotateCrossing_crossingEquiv (D : PDCode n) (i : Fin n) :
    (rotateCrossing D i).crossingEquiv = Equiv.refl _ :=
  (rfl)

/-- Reading a crossing from another slot is the identity on half-edges. -/
@[simp]
theorem rotateCrossing_halfEdgeEquiv (D : PDCode n) (i : Fin n) :
    (rotateCrossing D i).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- Reading a crossing from another slot keeps the labels of the crossing-free circles. -/
@[simp]
theorem rotateCrossing_crossinglessEquiv (D : PDCode n) (i : Fin n) :
    (rotateCrossing D i).crossinglessEquiv =
      finCongr (D.rotateCrossing_crossinglessComponentCount i).symm :=
  (rfl)

/-- Reading a crossing from another slot is a smoothing equivalence of every state; it is
`TauCeti.PDCode.SmoothingEquiv.rotateCrossing`. -/
@[simp]
theorem rotateCrossing_smoothingEquiv (D : PDCode n) (i : Fin n) (s : Fin n → Bool)
    (h : ∀ j, s ((rotateCrossing D i).crossingEquiv j) = s j) :
    (rotateCrossing D i).smoothingEquiv h = SmoothingEquiv.rotateCrossing D i s :=
  (rfl)

/-- **Permuting the labels of the crossing-free circles** identifies the smoothings of `D` with
themselves, by the identity on crossings and half-edges. -/
def crossinglessPerm (D : PDCode n) (σ : Perm (Fin D.crossinglessComponentCount)) :
    D.ResolutionEquiv D where
  crossingEquiv := Equiv.refl _
  halfEdgeEquiv := Equiv.refl _
  crossinglessEquiv := σ
  edgePair_apply _ := rfl
  statePerm_apply _ _ := rfl
  exists_slots _ := ⟨Equiv.refl _, fun _ ↦ rfl⟩

/-- Permuting the crossing-free labels is the identity on crossings. -/
@[simp]
theorem crossinglessPerm_crossingEquiv (D : PDCode n)
    (σ : Perm (Fin D.crossinglessComponentCount)) :
    (crossinglessPerm D σ).crossingEquiv = Equiv.refl _ :=
  (rfl)

/-- Permuting the crossing-free labels is the identity on half-edges. -/
@[simp]
theorem crossinglessPerm_halfEdgeEquiv (D : PDCode n)
    (σ : Perm (Fin D.crossinglessComponentCount)) :
    (crossinglessPerm D σ).halfEdgeEquiv = Equiv.refl _ :=
  (rfl)

/-- Permuting the crossing-free labels acts on them by `σ`. -/
@[simp]
theorem crossinglessPerm_crossinglessEquiv (D : PDCode n)
    (σ : Perm (Fin D.crossinglessComponentCount)) :
    (crossinglessPerm D σ).crossinglessEquiv = σ :=
  (rfl)

/-- Permuting the crossing-free labels is a smoothing equivalence of every state; it is
`TauCeti.PDCode.SmoothingEquiv.crossinglessPerm`. -/
@[simp]
theorem crossinglessPerm_smoothingEquiv (D : PDCode n)
    (σ : Perm (Fin D.crossinglessComponentCount)) (s : Fin n → Bool)
    (h : ∀ i, s ((crossinglessPerm D σ).crossingEquiv i) = s i) :
    (crossinglessPerm D σ).smoothingEquiv h = SmoothingEquiv.crossinglessPerm D s σ :=
  (rfl)

end ResolutionEquiv

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
