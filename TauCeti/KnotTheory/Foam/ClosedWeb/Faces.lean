/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.ClosedWeb.Planar
public import TauCeti.KnotTheory.Foam.ClosedWeb.Labeled
public import TauCeti.Combinatorics.RibbonGraph.Faces
import TauCeti.Dynamics.PeriodicPts.Bool
import TauCeti.GroupTheory.Perm.Semiconj

/-!
# Face lengths and small faces of closed webs

Faces are cycles of the effective face traversal on interval ends. Their lengths count
boundary occurrences, including repeated visits to the same edge or vertex. Vertex-free
circles do not enter this rotation system and are treated separately in web reduction.

Trivalence gives the identity `∑ f, (6 - length f) = 6 * eulerChar`. For a compatibly
planar web the right side is twelve times the number of components with vertices. Thus
any such web with vertices has a face of length less than six. A labelling by `1` and `2`
forces every edge to join a merge to a split, so every face has even length: there is a
digon or a square. These are face-boundary statements; they do not assume the boundary
is a simple cycle or select an orientation type of square.

The rotation-system conventions follow Goertz–Marino–Wedrich,
*Monoidal 2-categories from foam evaluation*, arXiv:2602.11120v1, Definition 3.4.
The small-face argument follows directly from the Euler identity and trivalence.
For background on four-valent planar reduction, see Carpentier,
*From planar graphs to embedded graphs*, arXiv:math/0005128v1, Lemma 2.
The finite counts use the native permutation cycle and quotient APIs.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm Function
open scoped BigOperators

universe u

namespace ClosedWeb

variable (W : ClosedWeb.{u})

/-- A face of the interval-edge rotation system, represented in its ribbon graph. -/
abbrev Face := W.toRibbonGraph.Face

/-- The face reached by traversing an effective end. The end swap accounts for the different
starting points in the effective and ribbon-graph face conventions. -/
noncomputable def faceOfEnd (d : W.End) : W.Face := W.toRibbonGraph.faceOfEdge (W.endSwap d)

/-- Every face is reached from an effective end. -/
theorem faceOfEnd_surjective : Surjective W.faceOfEnd :=
  W.toRibbonGraph.faceOfEdge_surjective.comp W.endSwap.surjective

/-- Two effective ends reach the same face exactly when they share a face-traversal cycle. -/
theorem faceOfEnd_eq_iff (d d' : W.End) :
    W.faceOfEnd d = W.faceOfEnd d' ↔ W.facePerm.SameCycle d d' := by
  refine (W.toRibbonGraph.faceOfEdge_eq_iff (W.endSwap d) (W.endSwap d')).trans ?_
  have h := (sameCycle_mul_comm_iff W.endSwap W.rotation (x := d) (y := d')).symm
  rw [← W.facePerm_def] at h
  -- The ribbon graph has carrier `W.End` with rotations `W.endSwap` and `W.rotation`.
  -- Applying the equivalence directly avoids rewriting across the two carrier expressions.
  exact (sameCycle_inv (f := W.endSwap * W.rotation)).trans h

/-- A step of the effective face traversal remains in the same face. -/
@[simp] theorem faceOfEnd_facePerm (d : W.End) :
    W.faceOfEnd (W.facePerm d) = W.faceOfEnd d :=
  (W.faceOfEnd_eq_iff _ _).mpr (sameCycle_apply_left.mpr (SameCycle.refl _ _))

/-- The number of interval-end occurrences along a face boundary. -/
noncomputable abbrev faceLength (f : W.Face) : ℕ := W.toRibbonGraph.faceLength f

/-- Face length counts the effective ends reaching that face. -/
theorem faceLength_def (f : W.Face) :
    W.faceLength f = Nat.card {d : W.End // W.faceOfEnd d = f} := by
  calc
    W.faceLength f = Nat.card {e : W.toRibbonGraph.E //
        W.toRibbonGraph.faceOfEdge e = f} := W.toRibbonGraph.faceLength_def f
    _ = _ := Nat.card_congr (W.endSwap.subtypeEquiv fun _ => by simp [faceOfEnd])

/-- The face through an end has length equal to the period of its effective face traversal. -/
@[simp] theorem faceLength_faceOfEnd (d : W.End) :
    W.faceLength (W.faceOfEnd d) = minimalPeriod W.facePerm d := by
  rw [faceLength_def, ← W.facePerm.ncard_setOf_sameCycle, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    (W.faceOfEnd_eq_iff _ _).trans sameCycle_comm)

/-- The number of faces agrees with the face count used in the Euler test. -/
@[simp] theorem card_face : Fintype.card W.Face = W.faceCount := W.faceCount_toRibbonGraph

/-- The face boundaries partition the interval ends, so each interval edge contributes twice. -/
theorem sum_faceLength : ∑ f : W.Face, W.faceLength f = 2 * Nat.card W.Edge := by
  rw [BipartiteRibbonGraph.sum_faceLength, ← Nat.card_eq_fintype_card]
  exact W.card_end

/-- The total face-degree defect of a trivalent rotation system is six times its Euler
characteristic. The subtraction takes place in `ℤ`, so long faces contribute negatively. -/
theorem sum_six_sub_faceLength :
    ∑ f : W.Face, (6 - (W.faceLength f : ℤ)) = 6 * W.eulerChar := by
  have hval := W.three_mul_card_vertex_eq_two_mul_card_edge
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.cast_sum, sum_faceLength, card_face, eulerChar_def, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- For a compatibly planar web the defect is twelve per component containing vertices. -/
theorem IsCompatiblyPlanar.sum_six_sub_faceLength (h : W.IsCompatiblyPlanar) :
    ∑ f : W.Face, (6 - (W.faceLength f : ℤ)) = 12 * Fintype.card W.Component := by
  rw [W.sum_six_sub_faceLength, W.isCompatiblyPlanar_def.mp h]
  ring

/-- A closed web with positive Euler characteristic has a face of length less than six. -/
theorem exists_faceLength_lt_six_of_eulerChar_pos (h : 0 < W.eulerChar) :
    ∃ f : W.Face, W.faceLength f < 6 := by
  classical
  have hs : (∑ _f : W.Face, (0 : ℤ)) < ∑ f : W.Face, (6 - (W.faceLength f : ℤ)) := by
    simp only [Finset.sum_const_zero, W.sum_six_sub_faceLength]
    omega
  obtain ⟨f, _, hf⟩ := Finset.exists_lt_of_sum_lt hs
  exact ⟨f, by omega⟩

/-- Every compatibly planar closed web with a vertex has a face of length less than six.
No connectedness or simplicity of the underlying graph is assumed. -/
theorem IsCompatiblyPlanar.exists_faceLength_lt_six (h : W.IsCompatiblyPlanar)
    [Nonempty W.Vertex] : ∃ f : W.Face, W.faceLength f < 6 := by
  obtain ⟨v⟩ := ‹Nonempty W.Vertex›
  have hc : 0 < Fintype.card W.Component :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk'' (W.ends (v, 0))⟩
  apply W.exists_faceLength_lt_six_of_eulerChar_pos
  rw [W.isCompatiblyPlanar_def.mp h]
  positivity

/-- A two-colouring of vertices which changes across every interval edge makes every face
boundary even, including boundaries with repeated edges. -/
theorem even_faceLength_of_bipartition (c : W.Vertex → Bool)
    (hc : ∀ d : W.End, c (W.incident (W.endSwap d)) = !(c (W.incident d)))
    (f : W.Face) : Even (W.faceLength f) := by
  obtain ⟨d, rfl⟩ := W.faceOfEnd_surjective f
  rw [faceLength_faceOfEnd, even_iff_two_dvd]
  have hsemi : Semiconj (c ∘ W.incident) W.facePerm Bool.not := fun d => by
    simp only [comp_apply, facePerm_apply, incident_rotation, hc]
  simpa only [comp_apply, Bool.minimalPeriod_not] using hsemi.minimalPeriod_dvd d

/-- Positive Euler characteristic and even face lengths force a digon or square boundary. -/
theorem exists_faceLength_two_or_four_of_eulerChar_pos (hχ : 0 < W.eulerChar)
    (heven : ∀ f : W.Face, Even (W.faceLength f)) :
    ∃ f : W.Face, W.faceLength f = 2 ∨ W.faceLength f = 4 := by
  obtain ⟨f, hf⟩ := W.exists_faceLength_lt_six_of_eulerChar_pos hχ
  have hpos : 0 < W.faceLength f := W.toRibbonGraph.faceLength_pos f
  obtain ⟨k, hk⟩ := heven f
  exact ⟨f, by omega⟩

/-- A compatibly planar bipartite closed web with a vertex has a digon or square face
boundary, counting occurrences even when the boundary is not simple. -/
theorem IsCompatiblyPlanar.exists_faceLength_two_or_four (h : W.IsCompatiblyPlanar)
    (c : W.Vertex → Bool)
    (hc : ∀ d : W.End, c (W.incident (W.endSwap d)) = !(c (W.incident d)))
    [Nonempty W.Vertex] : ∃ f : W.Face, W.faceLength f = 2 ∨ W.faceLength f = 4 := by
  obtain ⟨v⟩ := ‹Nonempty W.Vertex›
  have hc' : 0 < Fintype.card W.Component :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk'' (W.ends (v, 0))⟩
  apply W.exists_faceLength_two_or_four_of_eulerChar_pos
  · rw [W.isCompatiblyPlanar_def.mp h]
    positivity
  · exact W.even_faceLength_of_bipartition c hc

end ClosedWeb

namespace LabeledClosedWeb

variable (W : LabeledClosedWeb.{u} ℕ)

private theorem orientation_zero_incident_endSwap_eq_not_of_one_or_two
    (hl : ∀ e, W.edgeLabel e = 1 ∨ W.edgeLabel e = 2) (d : W.End) :
    (W.ends (W.incident (W.toClosedWeb.endSwap d), 0)).2 =
      !(W.ends (W.incident d, 0)).2 := by
  have h := W.isSplit_incident_iff_isMerge_incident_opposite_of_one_or_two d
    (fun _ => hl _) (fun _ => hl _)
  simp only [ClosedWeb.isSplit_def, ClosedWeb.isMerge_def] at h
  simp only [ClosedWeb.endSwap_apply]
  cases h0 : (W.ends (W.incident d, 0)).2 <;>
    cases h1 : (W.ends (W.incident (d.1, !d.2), 0)).2 <;> simp_all

/-- Every face of a `{1,2}`-labelled web has even boundary length. -/
theorem even_faceLength_of_one_or_two (hl : ∀ e, W.edgeLabel e = 1 ∨ W.edgeLabel e = 2)
    (f : W.toClosedWeb.Face) : Even (W.toClosedWeb.faceLength f) :=
  W.toClosedWeb.even_faceLength_of_bipartition (fun v => (W.ends (v, 0)).2)
    (W.orientation_zero_incident_endSwap_eq_not_of_one_or_two hl) f

/-- A compatibly planar `{1,2}`-labelled closed web with a vertex has a digon or square
face boundary. This counts occurrences and makes no assertion that the boundary is simple. -/
theorem exists_faceLength_two_or_four (hl : ∀ e, W.edgeLabel e = 1 ∨ W.edgeLabel e = 2)
    (hp : W.toClosedWeb.IsCompatiblyPlanar) [Nonempty W.Vertex] :
    ∃ f : W.toClosedWeb.Face,
      W.toClosedWeb.faceLength f = 2 ∨ W.toClosedWeb.faceLength f = 4 :=
  ClosedWeb.IsCompatiblyPlanar.exists_faceLength_two_or_four W.toClosedWeb hp
    (fun v => (W.ends (v, 0)).2)
    (W.orientation_zero_incident_endSwap_eq_not_of_one_or_two hl)

end LabeledClosedWeb

end TauCeti
