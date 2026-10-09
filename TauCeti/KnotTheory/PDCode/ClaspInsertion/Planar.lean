/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ClaspInsertion.Basic

/-!
# Planarity of two-arc Reidemeister clasps

A clasp on two distinct arcs is planar exactly when its input is planar and
its arcs either border the same face on the chosen sides or belong to different connected
components of the crossing graph. This is the incidence condition in the two-arc generator
of `TauCeti.OrientedPDCode.IsReidemeisterMove`. It includes joining two crossing-bearing components,
which the same-face criterion alone does not cover.

The crossing-graph component calculation and the face counts are supplied by
`PDCode.card_monodromyOrbit_insertClasp_add_one_of_not_mem_orbit` and the clasp-insertion API.
Crossing-free circles are unaffected; insertions involving such circles use separate operations.

Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1, the second
Reidemeister move; S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*,
§1.3, rotation systems and faces.
-/

public section

namespace TauCeti.PDCode

variable {n : ℕ}

/-- A two-arc clasp is planar precisely when the original code is planar and
the insertion satisfies the common-face or distinct-component Reidemeister condition. -/
@[simp] theorem isPlanar_insertClasp_iff_face_eq_or_not_mem_orbit (D : PDCode n) (p q : Fin (4 * n))
    (b : Bool) (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p) :
    (D.insertClasp p q b hqp hqe).IsPlanar ↔ D.IsPlanar ∧
      (D.face (D.edgePair.val p) = D.face q ∨
        q ∉ MulAction.orbit D.toPermutationTriple.monodromyGroup p) := by
  classical
  by_cases hpq : q ∈ MulAction.orbit D.toPermutationTriple.monodromyGroup p
  · by_cases hface : D.face (D.edgePair.val p) = D.face q
    · simp [isPlanar_insertClasp_iff D p q b hqp hqe hface, hface]
    · simp [not_isPlanar_insertClasp_of_face_ne D p q b hqp hqe hface hpq,
        hface, hpq]
  · simp [isPlanar_insertClasp_iff_of_not_mem_orbit D p q b hqp hqe hpq, hpq]

end TauCeti.PDCode
