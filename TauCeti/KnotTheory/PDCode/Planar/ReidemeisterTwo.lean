/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Planar.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.ClaspInsertion
-- The finite witnesses below compute with these implementation bodies.
import all TauCeti.KnotTheory.PDCode.Basic
import all TauCeti.KnotTheory.PDCode.Planar.Basic
import all TauCeti.KnotTheory.PDCode.ClaspInsertion
import all TauCeti.KnotTheory.PDCode.Oriented.ClaspInsertion
import all TauCeti.Combinatorics.Enumerative.PerfectMatching

/-!
# Second Reidemeister moves on oriented planar diagrams

`OrientedPlanarDiagram.ReidemeisterTwo` inserts the existing oriented clasp across a common
face of a planar rotation system, or removes such a clasp. Both endpoints are planar diagrams;
the insertion constructor takes an explicit certificate for the resulting rotation system.
The relation covers arcs incident to crossings on a common face boundary. Moves involving
crossing-free circles or separate boundary cycles require additional placement data.

The normalized bracket is invariant under this relation, consuming the unrestricted algebraic
calculation in `OrientedPDCode.normalizedKauffmanBracket_insertClasp`. This is a diagram-level
second-move result for constructing the Jones polynomial, not invariance under all Reidemeister
moves or an equivalence with ambient isotopy.

The move conventions follow Lickorish, *An Introduction to Knot Theory*, Chapter 1 and
Chapter 3, Lemma 3.3; the algebraic calculation follows Kauffman, *State models and the Jones
polynomial*, Topology 26 (1987), 395–407.
-/

public section

/-! The two distinct arcs face one another across a common face in the endpoint convention
of `insertClasp`. The opposite side of the second arc is essential. -/
namespace TauCeti.PDCode

variable {n : ℕ}

/-- The two selected arc sides lie on one face boundary in the insertion convention. -/
structure ClaspLocal (D : PDCode n) (p q : Fin (4 * n)) : Prop where
  /-- The chosen endpoints differ. -/
  ne : q ≠ p
  /-- The chosen arcs differ. -/
  ne_edgePair : q ≠ D.edgePair.val p
  /-- The facing sides lie on the same boundary cycle. -/
  sameCycle : D.projectionTriple.σinf.SameCycle p (D.edgePair.val q)

end TauCeti.PDCode

namespace TauCeti.OrientedPlanarDiagram

/-- Second Reidemeister moves on planar rotation-system diagrams, with the two selected arc
sides on one face boundary. The symmetric constructor includes clasp removal. -/
inductive IsReidemeisterTwo : {n m : ℕ} → OrientedPlanarDiagram n →
    OrientedPlanarDiagram m → Prop
  | insert {n : ℕ} (D : OrientedPlanarDiagram n) (p q : Fin (4 * n)) (b : Bool)
      (h : D.val.toPDCode.ClaspLocal p q)
      (hplanar : (D.val.insertClasp p q b h.ne h.ne_edgePair).toPDCode.IsPlanar) :
      IsReidemeisterTwo D ⟨D.val.insertClasp p q b h.ne h.ne_edgePair, hplanar⟩
  | symm {n m : ℕ} {D : OrientedPlanarDiagram n} {E : OrientedPlanarDiagram m} :
      IsReidemeisterTwo D E → IsReidemeisterTwo E D

/-- A local second Reidemeister move between planar diagrams preserves the normalized bracket. -/
theorem IsReidemeisterTwo.normalizedKauffmanBracket_eq {n m : ℕ}
    {D : OrientedPlanarDiagram n} {E : OrientedPlanarDiagram m} (h : IsReidemeisterTwo D E)
    {R : Type*} [CommRing R] (a : Rˣ) :
    E.val.normalizedKauffmanBracket a = D.val.normalizedKauffmanBracket a := by
  induction h with
  | insert D p q b h hplanar =>
    exact D.val.normalizedKauffmanBracket_insertClasp p q b h.ne h.ne_edgePair a
  | symm _ ih => exact ih.symm

end TauCeti.OrientedPlanarDiagram

namespace TauCeti

/-! The existing one-crossing code detects both the local and the nonlocal endpoint choices.
The calculations below count faces independently of the bracket calculation. -/

local notation "D₀" => orientedPDCodeOneCrossingPositive

private theorem oneCrossing_connected : (D₀).toPDCode.projectionGraph.Connected := by
  let : DecidableRel (D₀).toPDCode.projectionGraph.Adj := fun x y =>
    decidable_of_iff _ (PDCode.projectionGraph_adj _ x y).symm
  let w := SimpleGraph.Walk.ofSupport (G := (D₀).toPDCode.projectionGraph)
    [0, 1, 2, 3] (by decide) (by decide)
  have hw (x : Fin 4) : x ∈ w.support := by
    rw [SimpleGraph.Walk.support_ofSupport]
    fin_cases x <;> simp
  exact ⟨fun x y => (w.takeUntil x (hw x)).reachable.symm.trans
    (w.takeUntil y (hw y)).reachable⟩

/-- The existing one-crossing example is planar: its connected projection has three faces. -/
theorem orientedPDCodeOneCrossingPositive_isPlanar : (D₀).toPDCode.IsPlanar := by
  rw [PDCode.isPlanar_iff_of_connected _ oneCrossing_connected,
    Equiv.Perm.orbitCount_eq_card_parts_partition]
  decide

/-- Slots zero and three face each other across the two-sided face of the one-crossing code. -/
theorem orientedPDCodeOneCrossingPositive_claspLocal : (D₀).toPDCode.ClaspLocal 0 3 := by
  constructor
  · decide
  · decide
  · simpa only [PDCode.projectionTriple_σinf] using
      (show (D₀).toPDCode.facePerm.SameCycle 0 ((D₀).edgePair.val 3) by decide)

/-- Reversing only the second selected arc chooses a different face and fails locality. -/
theorem orientedPDCodeOneCrossingPositive_not_claspLocal : ¬(D₀).toPDCode.ClaspLocal 0 2 := by
  intro h
  have hn : ¬(D₀).toPDCode.facePerm.SameCycle 0 ((D₀).edgePair.val 2) := by decide
  exact hn (by simpa only [PDCode.projectionTriple_σinf] using h.sameCycle)

private theorem oneCrossing_insertClasp_connected (t b : Bool) :
    ((D₀).insertClasp 0 (if t then 2 else 3) b (by cases t <;> decide)
      (by cases t <;> decide)).toPDCode.projectionGraph.Connected := by
  let G := ((D₀).insertClasp 0 (if t then 2 else 3) b (by cases t <;> decide)
    (by cases t <;> decide)).toPDCode.projectionGraph
  let : DecidableRel G.Adj := fun x y =>
    decidable_of_iff _ (PDCode.projectionGraph_adj _ x y).symm
  have hc : ([0, 4, 5, 6, 7, 8, 9, 10, 11, 1, 2, 3] : List (Fin 12)).IsChain G.Adj := by
    cases t <;> cases b <;> decide
  let w := SimpleGraph.Walk.ofSupport _ (by decide) hc
  have hw (x : Fin 12) : x ∈ w.support := by
    rw [SimpleGraph.Walk.support_ofSupport]
    fin_cases x <;> simp
  exact ⟨fun x y => (w.takeUntil x (hw x)).reachable.symm.trans
    (w.takeUntil y (hw y)).reachable⟩

/-- The local clasp has five faces and remains planar, for either over-strand. -/
theorem orientedPDCodeOneCrossingPositive_isPlanar_insertClasp (b : Bool) :
    ((D₀).insertClasp 0 3 b (by decide) (by decide)).toPDCode.IsPlanar := by
  have hc : ((D₀).insertClasp 0 3 b (by decide) (by decide)).toPDCode.projectionGraph.Connected :=
    by simpa using oneCrossing_insertClasp_connected false b
  rw [PDCode.isPlanar_iff_of_connected _ hc,
    Equiv.Perm.orbitCount_eq_card_parts_partition]
  cases b <;> decide +kernel

/-- The nonlocal endpoint choice has only three faces at three crossings, hence genus one.
It cannot be an endpoint of the planar second-move relation. -/
theorem orientedPDCodeOneCrossingPositive_not_isPlanar_insertClasp (b : Bool) :
    ¬((D₀).insertClasp 0 2 b (by decide) (by decide)).toPDCode.IsPlanar := by
  have hc : ((D₀).insertClasp 0 2 b (by decide) (by decide)).toPDCode.projectionGraph.Connected :=
    by simpa using oneCrossing_insertClasp_connected true b
  rw [PDCode.isPlanar_iff_of_connected _ hc,
    Equiv.Perm.orbitCount_eq_card_parts_partition]
  cases b <;> decide +kernel

/-- A nondegenerate second Reidemeister move on the existing one-crossing diagram. -/
theorem orientedPDCodeOneCrossingPositive_isReidemeisterTwo (b : Bool) :
    OrientedPlanarDiagram.IsReidemeisterTwo
      ⟨D₀, orientedPDCodeOneCrossingPositive_isPlanar⟩
      ⟨(D₀).insertClasp 0 3 b (by decide) (by decide),
        orientedPDCodeOneCrossingPositive_isPlanar_insertClasp b⟩ :=
  .insert (⟨D₀, orientedPDCodeOneCrossingPositive_isPlanar⟩ : OrientedPlanarDiagram 1)
    0 3 b orientedPDCodeOneCrossingPositive_claspLocal
    (orientedPDCodeOneCrossingPositive_isPlanar_insertClasp b)

end TauCeti
