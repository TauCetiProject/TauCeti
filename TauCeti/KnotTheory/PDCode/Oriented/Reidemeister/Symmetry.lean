/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# Symmetries of Reidemeister equivalence

Mirroring and reversing all component orientations preserve every generating move of
oriented PD-codes, including moves involving crossing-free circles. Consequently both
operations preserve and reflect Reidemeister equivalence. They can therefore be applied
to an oriented link presentation independently of its diagram representative; in
particular the reverse mirror used as the concordance inverse is well defined at the
diagram-equivalence level.

Mirroring switches over- and under-strands while leaving the underlying ribbon graph
and its faces unchanged. Reversal changes directions, including those of crossing-free
components, while retaining all crossing information. Neither operation identifies a
link with its transformed link.

Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (oriented
diagrams and Reidemeister moves) and Chapter 8 (the reverse mirror in knot cobordism).
The proofs use the existing symmetry formulas for the individual PD-code moves.
-/

public section

namespace TauCeti.OrientedPDCode

variable {n m : ℕ} {D : OrientedPDCode n} {D' : OrientedPDCode m}

/-- Mirroring both diagrams carries a generating Reidemeister move to a generating move.
The face and component conditions of the two-arc move are preserved. -/
theorem IsReidemeisterMove.mirror
    (h : IsReidemeisterMove ⟨n, D⟩ ⟨m, D'⟩) :
    IsReidemeisterMove ⟨n, D.mirror⟩ ⟨m, D'.mirror⟩ := by
  cases h with
  | relabel D half cross =>
      simpa only [mirror_relabel] using IsReidemeisterMove.relabel D.mirror half cross
  | rotateCrossing D i =>
      simpa only [mirror_rotateCrossing] using IsReidemeisterMove.rotateCrossing D.mirror i
  | reidemeisterOne D p b =>
      simpa only [mirror_reidemeisterOne] using IsReidemeisterMove.reidemeisterOne D.mirror p (!b)
  | adjoinKink D o b =>
      simpa only [mirror_adjoinCircle, mirror_adjoinKink] using
        IsReidemeisterMove.adjoinKink D.mirror o (!b)
  | insertClasp D p q b hqp hqe hpq =>
      have hqe' : q ≠ D.mirror.edgePair.val p := by simpa using hqe
      have hpq' : D.mirror.face (D.mirror.edgePair.val p) = D.mirror.face q ∨
          q ∉ MulAction.orbit D.mirror.toPermutationTriple.monodromyGroup p := by
        rcases hpq with hface | hcomp
        · left
          simpa only [PDCode.face_eq_face_iff, mirror_toPDCode,
            PDCode.mirror_edgePair, PDCode.facePerm_mirror] using hface
        · right
          rwa [mirror_toPDCode, PDCode.toPermutationTriple_mirror]
      simpa only [mirror_insertClasp] using
        IsReidemeisterMove.insertClasp D.mirror p q (!b) hqp hqe' hpq'
  | insertCircleClasp D p o b =>
      simpa only [mirror_adjoinCircle, mirror_insertCircleClasp] using
        IsReidemeisterMove.insertCircleClasp D.mirror p o (!b)
  | adjoinTwoCircleClasp D o₁ o₂ b =>
      simpa only [mirror_adjoinCircle, mirror_adjoinTwoCircleClasp] using
        IsReidemeisterMove.adjoinTwoCircleClasp D.mirror o₁ o₂ (!b)
  | reidemeisterThree D c htri =>
      have htri' : D.mirror.HasReidemeisterThreeTriangle c := by simpa using htri
      simpa only [mirror_reidemeisterThree] using
        IsReidemeisterMove.reidemeisterThree D.mirror c htri'

/-- Reversing every component direction carries a generating Reidemeister move to a
generating move, with the crossing-free circles reversed as well. -/
theorem IsReidemeisterMove.reverse
    (h : IsReidemeisterMove ⟨n, D⟩ ⟨m, D'⟩) :
    IsReidemeisterMove ⟨n, D.reverse⟩ ⟨m, D'.reverse⟩ := by
  cases h with
  | relabel D half cross =>
      simpa only [reverse_relabel] using IsReidemeisterMove.relabel D.reverse half cross
  | rotateCrossing D i =>
      simpa only [reverse_rotateCrossing] using IsReidemeisterMove.rotateCrossing D.reverse i
  | reidemeisterOne D p b =>
      simpa only [reverse_reidemeisterOne] using IsReidemeisterMove.reidemeisterOne D.reverse p b
  | adjoinKink D o b =>
      simpa only [reverse_adjoinCircle, reverse_adjoinKink] using
        IsReidemeisterMove.adjoinKink D.reverse (!o) b
  | insertClasp D p q b hqp hqe hpq =>
      have hqe' : q ≠ D.reverse.edgePair.val p := by simpa using hqe
      have hpq' : D.reverse.face (D.reverse.edgePair.val p) = D.reverse.face q ∨
          q ∉ MulAction.orbit D.reverse.toPermutationTriple.monodromyGroup p := by
        rcases hpq with hface | hcomp
        · left
          simpa only [PDCode.face_eq_face_iff, reverse_toPDCode] using hface
        · right
          rwa [reverse_toPDCode]
      simpa only [reverse_insertClasp] using
        IsReidemeisterMove.insertClasp D.reverse p q b hqp hqe' hpq'
  | insertCircleClasp D p o b =>
      simpa only [reverse_adjoinCircle, reverse_insertCircleClasp] using
        IsReidemeisterMove.insertCircleClasp D.reverse p (!o) b
  | adjoinTwoCircleClasp D o₁ o₂ b =>
      simpa only [reverse_adjoinCircle, reverse_adjoinTwoCircleClasp] using
        IsReidemeisterMove.adjoinTwoCircleClasp D.reverse (!o₁) (!o₂) b
  | reidemeisterThree D c htri =>
      have htri' : D.reverse.HasReidemeisterThreeTriangle c := by simpa using htri
      simpa only [reverse_reidemeisterThree] using
        IsReidemeisterMove.reidemeisterThree D.reverse c htri'

/-- Mirroring preserves Reidemeister equivalence, even when the crossing counts differ. -/
theorem ReidemeisterEquiv.mirror (h : ReidemeisterEquiv D D') :
    ReidemeisterEquiv D.mirror D'.mirror := by
  refine ReidemeisterEquiv.induction
    (motive := fun x y => ReidemeisterEquiv x.2.mirror y.2.mirror)
    (fun h => h.mirror.reidemeisterEquiv) (fun _ => .refl _)
    (fun _ ih => ih.symm) (fun _ _ ih ih' => ih.trans ih') h

/-- Reversing all component orientations preserves Reidemeister equivalence. -/
theorem ReidemeisterEquiv.reverse (h : ReidemeisterEquiv D D') :
    ReidemeisterEquiv D.reverse D'.reverse := by
  refine ReidemeisterEquiv.induction
    (motive := fun x y => ReidemeisterEquiv x.2.reverse y.2.reverse)
    (fun h => h.reverse.reidemeisterEquiv) (fun _ => .refl _)
    (fun _ ih => ih.symm) (fun _ _ ih ih' => ih.trans ih') h

/-- Two mirror diagrams are equivalent exactly when the original diagrams are equivalent. -/
@[simp] theorem reidemeisterEquiv_mirror_iff :
    ReidemeisterEquiv D.mirror D'.mirror ↔ ReidemeisterEquiv D D' :=
  ⟨fun h => by simpa only [mirror_mirror] using h.mirror, ReidemeisterEquiv.mirror⟩

/-- Reversing all directions preserves and reflects equivalence of oriented diagrams. -/
@[simp] theorem reidemeisterEquiv_reverse_iff :
    ReidemeisterEquiv D.reverse D'.reverse ↔ ReidemeisterEquiv D D' :=
  ⟨fun h => by simpa only [reverse_reverse] using h.reverse, ReidemeisterEquiv.reverse⟩

end TauCeti.OrientedPDCode
