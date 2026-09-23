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

`OrientedPlanarDiagram.IsReidemeisterTwo` inserts the existing oriented clasp across a common
face of a planar rotation system, or removes such a clasp. Both endpoints are planar diagrams.
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

open Equiv Equiv.Perm

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
      (hplanar : (D.val.insertClasp p q b h.ne h.ne_edgePair).toPDCode.IsPlanar)
      : IsReidemeisterTwo D ⟨D.val.insertClasp p q b h.ne h.ne_edgePair,
        hplanar⟩
  | symm {n m : ℕ} {D : OrientedPlanarDiagram n} {E : OrientedPlanarDiagram m} :
      IsReidemeisterTwo D E → IsReidemeisterTwo E D

/-- A local second Reidemeister move between planar diagrams preserves the normalized bracket. -/
theorem IsReidemeisterTwo.normalizedKauffmanBracket_eq {n m : ℕ}
    {D : OrientedPlanarDiagram n} {E : OrientedPlanarDiagram m} (h : IsReidemeisterTwo D E)
    {R : Type*} [CommRing R] (a : Rˣ) :
    E.val.normalizedKauffmanBracket a = D.val.normalizedKauffmanBracket a := by
  induction h with
  | insert D p q b h _ =>
    exact D.val.normalizedKauffmanBracket_insertClasp p q b h.ne h.ne_edgePair a
  | symm _ ih => exact ih.symm

end TauCeti.OrientedPlanarDiagram

namespace TauCeti

/-! The existing one-crossing code detects both the local and the nonlocal endpoint choices.
The calculations below count faces independently of the bracket calculation. -/

local notation "D₀" => orientedPDCodeOneCrossingPositive

private theorem projectionTriple_insertClasp_congr {n : ℕ} (D : PDCode n)
    (p q : Fin (4 * n)) (b b' : Bool) (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p) :
    (D.insertClasp p q b hqp hqe).projectionTriple =
      (D.insertClasp p q b' hqp hqe).projectionTriple := by
  rfl

private theorem connected_of_monodromy_orbit {m : ℕ} (t : PermutationTriple m)
    (hm : m ≠ 0) (x₀ : Fin m)
    (h : ∀ x : Fin m, ∃ g : t.monodromyGroup, g • x₀ = x) : t.IsConnected := by
  rw [PermutationTriple.isConnected_iff]
  exact ⟨hm, MulAction.IsPretransitive.of_orbit h⟩

private theorem oneCrossing_insertClasp_connected_q2_false :
    ((D₀).insertClasp 0 2 false (by decide) (by decide)).toPDCode.projectionTriple.IsConnected := by
  let t := ((D₀).insertClasp 0 2 false (by decide) (by decide)).projectionTriple
  have ht : t.IsConnected := connected_of_monodromy_orbit t (by decide) 0 (by
    intro x
    let g0 : t.monodromyGroup := ⟨t.σ0, t.σ0_mem_monodromyGroup⟩
    let g1 : t.monodromyGroup := ⟨t.σ1, t.σ1_mem_monodromyGroup⟩
    /- Each branch records one explicit word in the two monodromy generators sending `0`
       to the listed half-edge. Keeping this finite table local makes the witness independent
       of the implementation of the ribbon graph connected-component quotient. -/
    fin_cases x
    · exact ⟨1, by simp⟩
    · refine ⟨g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, Nat.reduceMul]
      decide
    · refine ⟨g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, Nat.reduceMul]
      decide
    · refine ⟨g1, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g1, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g0⁻¹ * g1, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0 * g1, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g1 * g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0 * g1 * g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g1 * g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g1 * g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide)
  exact ht

private theorem oneCrossing_insertClasp_connected_q3_false :
    ((D₀).insertClasp 0 3 false (by decide) (by decide)).toPDCode.projectionTriple.IsConnected := by
  let t := ((D₀).insertClasp 0 3 false (by decide) (by decide)).projectionTriple
  have ht : t.IsConnected := connected_of_monodromy_orbit t (by decide) 0 (by
    intro x
    let g0 : t.monodromyGroup := ⟨t.σ0, t.σ0_mem_monodromyGroup⟩
    let g1 : t.monodromyGroup := ⟨t.σ1, t.σ1_mem_monodromyGroup⟩
    /- The q3 table is the same orbit argument with the other endpoint routing. -/
    fin_cases x
    · exact ⟨1, by simp⟩
    · refine ⟨g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, Nat.reduceMul]
      decide
    · refine ⟨g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, Nat.reduceMul]
      decide
    · refine ⟨g1, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g1 * g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g1 * g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0 * g1, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0⁻¹ * g1 * g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g0 * g1 * g0 * g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g1 * g0 * g0, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide
    · refine ⟨g1 * g0⁻¹, ?_⟩
      dsimp [t, g0, g1]
      simp only [Fin.isValue, OrientedPDCode.toPDCode_insertClasp,
         PDCode.projectionTriple_σ0, PDCode.projectionTriple_σ1, Nat.reduceMul]
      decide)
  exact ht

private theorem oneCrossing_insertClasp_connected_q2 (b : Bool) :
    ((D₀).insertClasp 0 2 b (by decide) (by decide)).toPDCode.projectionTriple.IsConnected := by
  cases b
  · exact oneCrossing_insertClasp_connected_q2_false
  · have hT := projectionTriple_insertClasp_congr (D := (D₀).toPDCode) 0 2 true false
      (by decide) (by decide)
    simpa only [OrientedPDCode.toPDCode_insertClasp, hT] using
      oneCrossing_insertClasp_connected_q2_false

private theorem oneCrossing_insertClasp_connected_q3 (b : Bool) :
    ((D₀).insertClasp 0 3 b (by decide) (by decide)).toPDCode.projectionTriple.IsConnected := by
  cases b
  · exact oneCrossing_insertClasp_connected_q3_false
  · have hT := projectionTriple_insertClasp_congr (D := (D₀).toPDCode) 0 3 true false
      (by decide) (by decide)
    simpa only [OrientedPDCode.toPDCode_insertClasp, hT] using
      oneCrossing_insertClasp_connected_q3_false

/-- Inserting the local clasp into the one-crossing code preserves planarity. -/
theorem isPlanar_insertClasp_orientedPDCodeOneCrossingPositive (b : Bool) :
    ((D₀).insertClasp 0 3 b (by decide) (by decide)).toPDCode.IsPlanar := by
  have hc :
      ((D₀).insertClasp 0 3 b (by decide) (by decide)).toPDCode.projectionTriple.IsConnected :=
    oneCrossing_insertClasp_connected_q3 b
  rw [PDCode.isPlanar_iff_of_connected _ hc,
    Equiv.Perm.orbitCount_eq_card_parts_partition]
  cases b <;> decide +kernel

/-- Slots zero and three face each other across the two-sided face of the one-crossing code. -/
theorem claspLocal_orientedPDCodeOneCrossingPositive :
    (D₀).toPDCode.ClaspLocal 0 3 := by
  refine { ne := by decide, ne_edgePair := by decide, sameCycle := ?_ }
  · have hface : (D₀).toPDCode.facePerm.SameCycle 0 ((D₀).edgePair.val 3) := by
      decide
    simpa only [PDCode.projectionTriple_σinf] using hface

/-- Reversing only the second selected arc chooses a different face and fails locality. -/
theorem not_claspLocal_orientedPDCodeOneCrossingPositive :
    ¬(D₀).toPDCode.ClaspLocal 0 2 := by
  intro h
  have hn : ¬(D₀).toPDCode.facePerm.SameCycle 0 ((D₀).edgePair.val 2) := by
    decide
  exact hn (by simpa only [PDCode.projectionTriple_σinf] using h.sameCycle)

/-- The nonlocal endpoint choice is not planar, so it cannot be an endpoint of the planar
second-move relation. -/
theorem not_isPlanar_insertClasp_orientedPDCodeOneCrossingPositive (b : Bool) :
    ¬((D₀).insertClasp 0 2 b (by decide) (by decide)).toPDCode.IsPlanar := by
  have hc :
      ((D₀).insertClasp 0 2 b (by decide) (by decide)).toPDCode.projectionTriple.IsConnected :=
    oneCrossing_insertClasp_connected_q2 b
  rw [PDCode.isPlanar_iff_of_connected _ hc,
    Equiv.Perm.orbitCount_eq_card_parts_partition]
  cases b <;> decide +kernel

/-- A nondegenerate second Reidemeister move on the existing one-crossing diagram. -/
theorem isReidemeisterTwo_orientedPDCodeOneCrossingPositive (b : Bool) :
    OrientedPlanarDiagram.IsReidemeisterTwo
      ⟨D₀, isPlanar_orientedPDCodeOneCrossingPositive⟩
      ⟨(D₀).insertClasp 0 3 b (by decide) (by decide),
        isPlanar_insertClasp_orientedPDCodeOneCrossingPositive b⟩ :=
  .insert (⟨D₀, isPlanar_orientedPDCodeOneCrossingPositive⟩ : OrientedPlanarDiagram 1)
    0 3 b claspLocal_orientedPDCodeOneCrossingPositive
    (isPlanar_insertClasp_orientedPDCodeOneCrossingPositive b)

end TauCeti
