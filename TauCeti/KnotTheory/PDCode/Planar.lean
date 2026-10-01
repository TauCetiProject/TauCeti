/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.OrbitDecomposition
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# Faces and planarity of PD-codes

A `TauCeti.PDCode` lists the four half-edges at each crossing in counterclockwise order and pairs
the two ends of each arc, but nothing in the code forces these data to come from a diagram drawn
in the plane. This file supplies the face data that decides it. The half-edges of a code are the
darts of its underlying `4`-valent graph, the counterclockwise rotation of the slots at each
crossing (`TauCeti.PDCode.crossingRotation`) is its rotation system, and the arc matching is its
edge involution. As for any rotation system, the orbits of the composite `TauCeti.PDCode.facePerm`,
which turns to the next slot counterclockwise and then runs along the arc from there, are the faces
of the closed oriented surface on which the graph is cellularly embedded
(Lando–Zvonkin, §1.3). For a connected diagram in the plane they are the regions of the diagram.

This is the permutation-triple encoding of the graph: `TauCeti.PDCode.toPermutationTriple` has
the crossing rotation and the arc matching as its first two components and the inverse face
permutation as the third. Its Euler characteristic counts `n` vertices, `2 * n` edges and the
faces, so it is `faceCount - n` (`TauCeti.PDCode.eulerChar_toPermutationTriple`). Each connected
component of the graph contributes at most `2`, with equality exactly for a sphere, so a code is
**planar** (`TauCeti.PDCode.IsPlanar`) when the Euler characteristic is twice the number of
connected components, the monodromy orbits of the triple. For a connected code this is Euler's
count of `n + 2` regions (`TauCeti.PDCode.isPlanar_iff_faceCount_eq_of_isConnected`).

Throughout, the underlying graph is the one supported on the crossings: its vertices are the
crossings and its edges the arcs between them. The crossing-free circles of a code
(`TauCeti.PDCode.crossinglessComponentCount`) are not part of it, so they contribute neither faces
to `TauCeti.PDCode.faceCount` nor connected components to the monodromy orbits. They play no part
in planarity either, since a circle alone always lies in a sphere.

Planarity is invariant under mirroring and relabelling. The one-crossing kink is planar, while the
one-crossing code whose arcs join opposite slots, two circles meeting in a single crossing, is not
(`TauCeti.PDCode.exists_not_isPlanar`): its graph embeds only in the torus.

The face permutation locates the arcs that border a common region: two half-edges lie on the same
face exactly when `TauCeti.PDCode.face` agrees on them (`TauCeti.PDCode.face_eq_face_iff`). This
is the locality data that the second and third Reidemeister moves need beyond the algebraic
operation `TauCeti.PDCode.insertClasp`.

## Main definitions

* `TauCeti.PDCode.crossingRotation`: the counterclockwise rotation of the slots at each crossing.
* `TauCeti.PDCode.toPermutationTriple`: the permutation triple of the underlying graph.
* `TauCeti.PDCode.facePerm` and `TauCeti.PDCode.faceCount`: the face traversal and the number of
  faces of the underlying graph.
* `TauCeti.PDCode.Face` and `TauCeti.PDCode.face`: the faces, as orbits of the face traversal, and
  the face at a half-edge.
* `TauCeti.PDCode.IsPlanar`: every connected component of the underlying graph is a sphere.

## Main results

* `TauCeti.PDCode.eulerChar_toPermutationTriple`: the Euler characteristic is `faceCount - n`.
* `TauCeti.PDCode.faceCount_le`: if the underlying graph has `c` connected components, it has at
  most `n + 2 * c` faces, with equality exactly for planar codes
  (`TauCeti.PDCode.isPlanar_iff_faceCount_eq`).
* `TauCeti.PDCode.mem_orbit_of_face_eq_face`: half-edges on one face lie in one connected
  component, and so does a half-edge `h` with every half-edge on the face at the far end
  `D.edgePair.val h` of its arc (`TauCeti.PDCode.mem_orbit_of_face_edgePair_eq_face`).
* `TauCeti.PDCode.isPlanar_mirror` and `TauCeti.PDCode.isPlanar_relabel`: invariance.
* `TauCeti.PDCode.isPlanar_kink` and `TauCeti.PDCode.exists_not_isPlanar`.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 (rotation systems and their faces) and §1.5.
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2--3 (the PD convention).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PDCode

variable {n : ℕ}

/-! ### The crossing rotation -/

/-- The rotation of every half-edge to the next slot counterclockwise at its crossing. -/
def crossingRotation (D : PDCode n) : Perm (Fin (4 * n)) :=
  D.halfEdge.permCongr
    ((crossingSlotEquiv n).permCongr (prodCongrRight fun _ ↦ finRotate 4))

/-- The defining equation of the crossing rotation. -/
theorem crossingRotation_def (D : PDCode n) :
    D.crossingRotation = D.halfEdge.permCongr
      ((crossingSlotEquiv n).permCongr (prodCongrRight fun _ ↦ finRotate 4)) := (rfl)

/-- The crossing rotation moves the half-edge in a slot to the next slot counterclockwise. -/
@[simp]
theorem crossingRotation_crossing (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossingRotation (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      D.crossing i (slot + 1) := by
  simp [crossingRotation]

/-- Each crossing is one orbit of the crossing rotation. -/
@[simp]
theorem orbitCount_crossingRotation (D : PDCode n) : orbitCount D.crossingRotation = n := by
  rw [crossingRotation, orbitCount_permCongr, orbitCount_permCongr,
    orbitCount_prodCongrRight_const, orbitCount_finRotate]
  simp

/-- Mirroring preserves the crossing rotation. -/
@[simp]
theorem crossingRotation_mirror (D : PDCode n) :
    D.mirror.crossingRotation = D.crossingRotation := by
  simp [crossingRotation]

/-- Relabelling conjugates the crossing rotation by the half-edge relabelling. -/
@[simp]
theorem crossingRotation_relabel (D : PDCode n) (half : Perm (Fin (4 * n)))
    (cross : Perm (Fin n)) :
    (D.relabel half cross).crossingRotation = half.permCongr D.crossingRotation := by
  ext h
  obtain ⟨x, rfl⟩ := half.surjective h
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  have he : half (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      (D.relabel half cross).halfEdge (crossingSlotEquiv n (cross i, slot)) := by
    rw [← D.crossing_apply, ← (D.relabel half cross).crossing_apply]
    simpa only [Equiv.symm_apply_apply] using (D.crossing_relabel half cross (cross i) slot).symm
  rw [he, crossingRotation_crossing, crossing_relabel]
  simp

/-- Every arc is an orbit of the arc matching, so a code with `n` crossings has `2 * n` arcs. -/
@[simp]
theorem orbitCount_edgePair (D : PDCode n) : orbitCount D.edgePair.val = 2 * n := by
  have h := D.edgePair.prop.two_mul_orbitCount
  rw [Nat.card_fin] at h
  omega

/-! ### Faces -/

/-- The face traversal: turn to the next slot counterclockwise, then run along the arc from
there. Its orbits are the faces of the underlying graph. -/
def facePerm (D : PDCode n) : Perm (Fin (4 * n)) :=
  D.edgePair.val * D.crossingRotation

/-- The defining equation of the face traversal. -/
theorem facePerm_def (D : PDCode n) : D.facePerm = D.edgePair.val * D.crossingRotation := (rfl)

/-- The face traversal rotates at the crossing and then crosses the arc. -/
theorem facePerm_apply (D : PDCode n) (h : Fin (4 * n)) :
    D.facePerm h = D.edgePair.val (D.crossingRotation h) :=
  (rfl)

/-- The number of faces of the underlying graph: the orbits of the face traversal. Crossing-free
circles are not part of this graph and contribute no faces. -/
noncomputable def faceCount (D : PDCode n) : ℕ :=
  orbitCount D.facePerm

/-- The number of faces is the number of orbits of the face traversal. -/
theorem faceCount_def (D : PDCode n) : D.faceCount = orbitCount D.facePerm := (rfl)

/-- The faces of the underlying graph: the orbits of the face traversal. -/
abbrev Face (D : PDCode n) : Type :=
  Quotient (SameCycle.setoid D.facePerm)

/-- The face at a half-edge: the one in the corner at its crossing running counterclockwise from
it to the next slot. -/
def face (D : PDCode n) (h : Fin (4 * n)) : D.Face :=
  Quotient.mk _ h

/-- Two half-edges have the same face exactly when the face traversal carries one to the
other. -/
theorem face_eq_face_iff (D : PDCode n) {h h' : Fin (4 * n)} :
    D.face h = D.face h' ↔ D.facePerm.SameCycle h h' :=
  Quotient.eq

/-- Every face is the face at some half-edge. -/
theorem face_surjective (D : PDCode n) : Function.Surjective D.face :=
  Quotient.mk_surjective

/-- The face traversal stays in one face. -/
@[simp]
theorem face_facePerm (D : PDCode n) (h : Fin (4 * n)) : D.face (D.facePerm h) = D.face h :=
  D.face_eq_face_iff.mpr (sameCycle_apply_left.mpr (SameCycle.refl _ _))

/-- The number of faces is the cardinality of the type of faces. -/
@[simp↓]
theorem card_face (D : PDCode n) : Nat.card D.Face = D.faceCount :=
  (orbitCount_def _).symm

/-- Mirroring preserves the face traversal. -/
@[simp]
theorem facePerm_mirror (D : PDCode n) : D.mirror.facePerm = D.facePerm := by
  simp [facePerm]

/-- Relabelling conjugates the face traversal by the half-edge relabelling. -/
@[simp]
theorem facePerm_relabel (D : PDCode n) (half : Perm (Fin (4 * n))) (cross : Perm (Fin n)) :
    (D.relabel half cross).facePerm = half.permCongr D.facePerm := by
  rw [facePerm, facePerm, crossingRotation_relabel, relabel_edgePair, PerfectMatching.congr_val,
    permCongr_mul]

/-- Mirroring preserves the number of faces. -/
@[simp]
theorem faceCount_mirror (D : PDCode n) : D.mirror.faceCount = D.faceCount := by
  simp [faceCount]

/-- Relabelling preserves the number of faces. -/
@[simp]
theorem faceCount_relabel (D : PDCode n) (half : Perm (Fin (4 * n))) (cross : Perm (Fin n)) :
    (D.relabel half cross).faceCount = D.faceCount := by
  simp [faceCount]

/-- Relabelling preserves face incidence: two relabelled half-edges lie on the same face of the
relabelled code exactly when the original half-edges lie on the same face of the code. -/
@[simp]
theorem face_relabel_eq_face_relabel_iff (D : PDCode n) (half : Perm (Fin (4 * n)))
    (cross : Perm (Fin n)) {h h' : Fin (4 * n)} :
    (D.relabel half cross).face (half h) = (D.relabel half cross).face (half h') ↔
      D.face h = D.face h' := by
  rw [face_eq_face_iff, face_eq_face_iff, facePerm_relabel, permCongr_eq_mul, sameCycle_conj,
    Perm.inv_def, symm_apply_apply, symm_apply_apply]

/-- Two half-edges lie in one orbit of running along an arc and then turning exactly when the far
ends of their arcs lie on one face: this traversal is conjugate to the face traversal by the arc
matching. -/
theorem sameCycle_crossingRotation_mul_edgePair_iff (D : PDCode n) {h h' : Fin (4 * n)} :
    (D.crossingRotation * D.edgePair.val).SameCycle h h' ↔
      D.face (D.edgePair.val h) = D.face (D.edgePair.val h') := by
  rw [face_eq_face_iff, facePerm_def, sameCycle_mul_comm_iff]

/-- The faces may equally be counted as the orbits of running along an arc and then turning to
the next slot, which is conjugate to the face traversal. -/
theorem faceCount_eq_orbitCount_crossingRotation_mul_edgePair (D : PDCode n) :
    D.faceCount = orbitCount (D.crossingRotation * D.edgePair.val) := by
  rw [faceCount_def, facePerm_def, orbitCount_mul_comm]

/-! ### The permutation triple -/

/-- The permutation triple of the underlying graph of a PD-code: the crossing rotation, the arc
matching, and the inverse face traversal. -/
def toPermutationTriple (D : PDCode n) : PermutationTriple (4 * n) :=
  .ofTwo D.crossingRotation D.edgePair.val

/-- The first component of the triple is the crossing rotation. -/
@[simp]
theorem toPermutationTriple_σ0 (D : PDCode n) :
    D.toPermutationTriple.σ0 = D.crossingRotation := (rfl)

/-- The second component of the triple is the arc matching. -/
@[simp]
theorem toPermutationTriple_σ1 (D : PDCode n) :
    D.toPermutationTriple.σ1 = D.edgePair.val := (rfl)

/-- The third component of the triple is the inverse face traversal. -/
@[simp]
theorem toPermutationTriple_σinf (D : PDCode n) :
    D.toPermutationTriple.σinf = D.facePerm⁻¹ := (rfl)

/-- Mirroring preserves the underlying graph. -/
@[simp]
theorem toPermutationTriple_mirror (D : PDCode n) :
    D.mirror.toPermutationTriple = D.toPermutationTriple := by
  simp [toPermutationTriple]

/-- Relabelling relabels the sheets of the permutation triple by the half-edge relabelling. -/
@[simp]
theorem toPermutationTriple_relabel (D : PDCode n) (half : Perm (Fin (4 * n)))
    (cross : Perm (Fin n)) :
    (D.relabel half cross).toPermutationTriple = half • D.toPermutationTriple := by
  simp [toPermutationTriple, PerfectMatching.congr_val, permCongr_eq_mul]

/-- The crossing rotation lies in the monodromy group of the underlying graph. -/
@[simp]
theorem crossingRotation_mem_monodromyGroup (D : PDCode n) :
    D.crossingRotation ∈ D.toPermutationTriple.monodromyGroup :=
  D.toPermutationTriple.σ0_mem_monodromyGroup

/-- The arc matching lies in the monodromy group of the underlying graph. -/
@[simp]
theorem edgePair_mem_monodromyGroup (D : PDCode n) :
    D.edgePair.val ∈ D.toPermutationTriple.monodromyGroup :=
  D.toPermutationTriple.σ1_mem_monodromyGroup

/-- The face traversal lies in the monodromy group of the underlying graph. -/
@[simp]
theorem facePerm_mem_monodromyGroup (D : PDCode n) :
    D.facePerm ∈ D.toPermutationTriple.monodromyGroup :=
  mul_mem D.edgePair_mem_monodromyGroup D.crossingRotation_mem_monodromyGroup

/-- Two half-edges on one face lie in one connected component of the underlying graph: the face
traversal is a product of the crossing rotation and the arc matching. -/
theorem mem_orbit_of_face_eq_face (D : PDCode n) {h h' : Fin (4 * n)}
    (hface : D.face h = D.face h') :
    h' ∈ MulAction.orbit D.toPermutationTriple.monodromyGroup h := by
  obtain ⟨k, hk⟩ := D.face_eq_face_iff.mp hface
  exact ⟨⟨D.facePerm ^ k, zpow_mem D.facePerm_mem_monodromyGroup k⟩, hk⟩

/-- If the face at the far end of the arc ending at `h` is the face at `h'`, then `h'` lies in the
connected component of `h`. -/
theorem mem_orbit_of_face_edgePair_eq_face (D : PDCode n) {h h' : Fin (4 * n)}
    (hface : D.face (D.edgePair.val h) = D.face h') :
    h' ∈ MulAction.orbit D.toPermutationTriple.monodromyGroup h := by
  obtain ⟨g, hg⟩ := D.mem_orbit_of_face_eq_face hface
  exact ⟨g * ⟨D.edgePair.val, D.edgePair_mem_monodromyGroup⟩, (mul_smul g _ h).trans hg⟩

/-- **Euler's formula for a PD-code.** The underlying graph has `n` vertices and `2 * n` edges,
so its Euler characteristic is the number of faces less the number of crossings. -/
theorem eulerChar_toPermutationTriple (D : PDCode n) :
    D.toPermutationTriple.eulerChar = D.faceCount - n := by
  rw [PermutationTriple.eulerChar_def, toPermutationTriple_σ0, toPermutationTriple_σ1,
    toPermutationTriple_σinf, orbitCount_inv, orbitCount_crossingRotation, orbitCount_edgePair,
    faceCount_def]
  push_cast
  ring

/-- If the underlying graph of a PD-code has `c` connected components, it has at most `n + 2 * c`
faces. -/
theorem faceCount_le (D : PDCode n) :
    D.faceCount ≤ n + 2 * Nat.card D.toPermutationTriple.MonodromyOrbit := by
  have h : D.toPermutationTriple.eulerChar ≤
      2 * Nat.card D.toPermutationTriple.MonodromyOrbit :=
    D.toPermutationTriple.eulerChar_le_two_mul_card_monodromyOrbits
  rw [eulerChar_toPermutationTriple] at h
  omega

/-! ### Planarity -/

/-- A PD-code is **planar** when every connected component of its underlying graph, with the
counterclockwise rotation at each crossing, is embedded in a sphere. Since each component has
Euler characteristic at most `2`, with equality exactly for the sphere, this says that the Euler
characteristic is twice the number of components. Crossing-free circles are not part of the
underlying graph and do not affect planarity. -/
def IsPlanar (D : PDCode n) : Prop :=
  D.toPermutationTriple.eulerChar = 2 * Nat.card D.toPermutationTriple.MonodromyOrbit

/-- The defining equation of planarity. -/
theorem isPlanar_def (D : PDCode n) :
    D.IsPlanar ↔
      D.toPermutationTriple.eulerChar = 2 * Nat.card D.toPermutationTriple.MonodromyOrbit :=
  Iff.rfl

/-- A PD-code whose underlying graph has `c` connected components is planar exactly when the
graph has `n + 2 * c` faces, the largest possible number. -/
theorem isPlanar_iff_faceCount_eq (D : PDCode n) :
    D.IsPlanar ↔ D.faceCount = n + 2 * Nat.card D.toPermutationTriple.MonodromyOrbit := by
  rw [isPlanar_def, eulerChar_toPermutationTriple]
  omega

/-- A PD-code with `n` crossings and connected underlying graph is planar exactly when the graph
has `n + 2` faces. -/
theorem isPlanar_iff_faceCount_eq_of_isConnected {D : PDCode n}
    (hD : D.toPermutationTriple.IsConnected) : D.IsPlanar ↔ D.faceCount = n + 2 := by
  have := hD.isPretransitive
  have : Nonempty (Fin (4 * n)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hD.ne_zero)
  have hc : Nat.card D.toPermutationTriple.MonodromyOrbit = 1 :=
    MulAction.card_orbitRelQuotient_eq_one
  rw [isPlanar_iff_faceCount_eq, hc]

/-- A PD-code without crossings is planar. -/
@[simp]
theorem isPlanar_of_zero (D : PDCode 0) : D.IsPlanar := by
  have : IsEmpty (Fin (4 * 0)) := ⟨fun x ↦ by have := x.isLt; omega⟩
  rw [isPlanar_iff_faceCount_eq, faceCount_def, orbitCount_def, Nat.card_of_isEmpty,
    Nat.card_of_isEmpty]

/-- Mirroring preserves planarity. -/
@[simp]
theorem isPlanar_mirror (D : PDCode n) : D.mirror.IsPlanar ↔ D.IsPlanar := by
  simp [IsPlanar]

/-- Relabelling preserves planarity. -/
@[simp]
theorem isPlanar_relabel (D : PDCode n) (half : Perm (Fin (4 * n))) (cross : Perm (Fin n)) :
    (D.relabel half cross).IsPlanar ↔ D.IsPlanar := by
  simp [IsPlanar]

/-! ### One-crossing codes -/

/-- The underlying graph of a one-crossing code is connected: the rotation at its single crossing
already moves every half-edge to every other. -/
theorem isConnected_toPermutationTriple_of_one_crossing (D : PDCode 1) :
    D.toPermutationTriple.IsConnected := by
  refine PermutationTriple.isConnected_iff.mpr ⟨by decide, ⟨fun x y ↦ ?_⟩⟩
  have hcycle : ∀ x y, D.crossingRotation.SameCycle x y := by
    have h : Nat.card (Quotient (SameCycle.setoid D.crossingRotation)) = 1 := by
      rw [← orbitCount_def, orbitCount_crossingRotation]
    intro x y
    exact Quotient.exact ((Nat.card_eq_one_iff_unique.mp h).1.elim _ _)
  obtain ⟨k, hk⟩ := hcycle x y
  exact ⟨⟨D.crossingRotation ^ k, zpow_mem (D.toPermutationTriple.σ0_mem_monodromyGroup) k⟩, hk⟩

/-- The kink has three faces: the two sides of its loop and the region outside the strand. -/
@[simp]
theorem faceCount_kink : kink.faceCount = 3 := by
  have hface : kink.facePerm = (crossingSlotEquiv 1).permCongr
      (prodCongrRight fun _ ↦ 1 * swap (1 : Fin 4) 3) := by
    refine Equiv.ext fun h ↦ ?_
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
    have hrot := kink.crossingRotation_crossing i slot
    rw [kink_halfEdge, kink_crossing, Perm.one_apply] at hrot
    rw [facePerm_apply, hrot, kink_edgePair_apply]
    clear hrot
    simp only [permCongr_apply, symm_apply_apply, prodCongrRight_apply,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, true_and, slotSmoothing_true]
    revert slot
    decide
  have h := orbitCount_mul_swap_add_one (τ := (1 : Perm (Fin 4))) (p := 3) (a := 1) rfl
    (by decide)
  rw [orbitCount_one, Nat.card_fin] at h
  rw [faceCount_def, hface, orbitCount_permCongr, orbitCount_prodCongrRight_const, Nat.card_unique]
  omega

/-- **The kink is planar.** -/
@[simp]
theorem isPlanar_kink : kink.IsPlanar := by
  rw [isPlanar_iff_faceCount_eq_of_isConnected
    (isConnected_toPermutationTriple_of_one_crossing kink),
    faceCount_kink]

/-- **Not every PD-code is planar.** The one-crossing code whose two arcs join opposite slots
consists of two circles meeting in a single crossing, which no diagram in the plane can have. Its
face traversal is a single cycle, so its graph has one face and embeds in the torus but not in the
sphere. -/
theorem exists_not_isPlanar : ∃ D : PDCode 1, ¬ D.IsPlanar := by
  let D : PDCode 1 :=
    { halfEdge := 1
      edgePair := PerfectMatching.congr (crossingSlotEquiv 1)
        (PerfectMatching.mk (prodCongrRight fun _ ↦ swap 0 2 * swap 1 3) (by decide) (by decide))
      crossinglessComponentCount := 0
      overPair := fun _ ↦ true }
  refine ⟨D, fun hD ↦ ?_⟩
  have hface : D.facePerm = (crossingSlotEquiv 1).permCongr
      (prodCongrRight fun _ ↦ (finRotate 4)⁻¹) := by
    refine Equiv.ext fun h ↦ ?_
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
    have hrot := D.crossingRotation_crossing i slot
    simp only [D, crossing_apply, Perm.one_apply] at hrot
    simp only [facePerm_apply, hrot, D, PerfectMatching.congr_val, PerfectMatching.val_mk,
      permCongr_apply, symm_apply_apply, prodCongrRight_apply, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq, true_and]
    clear hrot
    rw [eq_comm, Perm.inv_eq_iff_eq, finRotate_apply]
    revert slot
    decide
  have hcount : D.faceCount = 1 := by
    rw [faceCount_def, hface, orbitCount_permCongr, orbitCount_prodCongrRight_const,
      orbitCount_inv, orbitCount_finRotate]
    simp
  rw [isPlanar_iff_faceCount_eq_of_isConnected
    (isConnected_toPermutationTriple_of_one_crossing D),
    hcount] at hD
  omega

end PDCode

end TauCeti
