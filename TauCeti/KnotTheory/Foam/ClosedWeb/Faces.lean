/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.ClosedWeb.Planar
public import TauCeti.KnotTheory.Foam.ClosedWeb.Labeled
import TauCeti.Dynamics.PeriodicPts.Bool

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

/-- A face of the interval-edge rotation system, including one-element cycles. -/
abbrev Face := Quotient (SameCycle.setoid W.facePerm)

noncomputable instance : Fintype W.Face := Fintype.ofFinite _

/-- The number of interval-end occurrences along a face boundary. -/
noncomputable def faceLength (f : W.Face) : ℕ :=
  Nat.card {d : W.End // (Quotient.mk'' d : W.Face) = f}

/-- Face length is the cardinality of the fibre of interval ends belonging to that face. -/
theorem faceLength_def (f : W.Face) :
    W.faceLength f = Nat.card {d : W.End // (Quotient.mk'' d : W.Face) = f} := (rfl)

/-- The face through an end has length equal to the period of its face traversal. -/
@[simp] theorem faceLength_mk (d : W.End) :
    W.faceLength (Quotient.mk'' d) = minimalPeriod W.facePerm d := by
  rw [faceLength_def, ← W.facePerm.ncard_setOf_sameCycle, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    Quotient.eq''.trans sameCycle_comm)

/-- Every face contains at least one end. -/
@[simp] theorem faceLength_pos (f : W.Face) : 0 < W.faceLength f := by
  obtain ⟨d, rfl⟩ := Quotient.mk''_surjective f
  rw [faceLength_def]
  exact Nat.card_pos_iff.mpr ⟨⟨⟨d, rfl⟩⟩, inferInstance⟩

/-- The number of faces agrees with the face count used in the Euler test. -/
@[simp] theorem card_face : Fintype.card W.Face = W.faceCount := by
  rw [faceCount_def, orbitCount_def, Nat.card_eq_fintype_card]

/-- The face boundaries partition the interval ends, so each interval edge contributes twice. -/
theorem sum_faceLength : ∑ f : W.Face, W.faceLength f = 2 * Nat.card W.Edge := by
  classical
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv (fun d : W.End =>
    (Quotient.mk'' d : W.Face)))
  rw [Nat.card_sigma, W.card_end] at h
  simpa only [faceLength_def] using h

/-- The total face-degree defect of a trivalent rotation system is six times its Euler
characteristic. The subtraction takes place in `ℤ`, so long faces contribute negatively. -/
theorem sum_six_sub_faceLength :
    ∑ f : W.Face, (6 - (W.faceLength f : ℤ)) = 6 * W.eulerChar := by
  have hval := W.three_mul_card_vertex_eq_two_mul_card_edge
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.cast_sum, sum_faceLength, card_face, eulerChar_def]
  push_cast
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
  by_contra! hn
  have hs : ∑ f : W.Face, (6 - (W.faceLength f : ℤ)) ≤ 0 :=
    Finset.sum_nonpos fun f _ => by have hf := hn f; omega
  rw [W.sum_six_sub_faceLength] at hs
  omega

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
  obtain ⟨d, rfl⟩ := Quotient.mk''_surjective f
  rw [faceLength_mk, even_iff_two_dvd]
  have hsemi : Semiconj (c ∘ W.incident) W.facePerm Bool.not := fun d => by
    simp only [comp_apply, facePerm_apply, incident_rotation, hc]
  have hp := (isPeriodicPt_minimalPeriod W.facePerm d).map hsemi
  simpa only [comp_apply, Bool.minimalPeriod_not] using hp.minimalPeriod_dvd

/-- A compatibly planar bipartite closed web with a vertex has a digon or square face
boundary, counting occurrences even when the boundary is not simple. -/
theorem IsCompatiblyPlanar.exists_faceLength_two_or_four (h : W.IsCompatiblyPlanar)
    (c : W.Vertex → Bool)
    (hc : ∀ d : W.End, c (W.incident (W.endSwap d)) = !(c (W.incident d)))
    [Nonempty W.Vertex] : ∃ f : W.Face, W.faceLength f = 2 ∨ W.faceLength f = 4 := by
  obtain ⟨f, hf⟩ := h.exists_faceLength_lt_six
  have hpos := W.faceLength_pos f
  obtain ⟨k, hk⟩ := W.even_faceLength_of_bipartition c hc f
  exact ⟨f, by omega⟩

end ClosedWeb

namespace LabeledClosedWeb

variable (W : LabeledClosedWeb.{u} ℕ)

/-- The orientation of the odd end at the opposite endpoint of an interval is reversed in a
`{1,2}`-labelled web. Thus every edge joins a merge to a split. -/
theorem oddOrientation_endSwap_of_one_or_two
    (hl : ∀ e, W.edgeLabel e = 1 ∨ W.edgeLabel e = 2) (d : W.End) :
    (W.ends (W.incident (W.toClosedWeb.endSwap d), 0)).2 =
      !(W.ends (W.incident d, 0)).2 := by
  have horient : ∀ v (i : Fin 3),
      (W.ends (v, 0)).2 = if W.edgeLabel (W.ends (v, i)).1 = 2 then
        (W.ends (v, i)).2 else !(W.ends (v, i)).2 := by
    intro v i
    obtain ⟨h0, h1, h2⟩ := W.edgeLabel_ends_of_one_or_two v (fun i => hl _)
    fin_cases i <;> simp [h0, h1, h2]
  obtain ⟨⟨v, i⟩, hd⟩ := W.ends.surjective d
  obtain ⟨⟨v', j⟩, hd'⟩ := W.ends.surjective (W.toClosedWeb.endSwap d)
  have he : (W.ends (v', j)).1 = (W.ends (v, i)).1 := by
    simp only [hd', hd, ClosedWeb.endSwap_apply]
  have hb : (W.ends (v', j)).2 = !(W.ends (v, i)).2 := by
    simp only [hd', hd, ClosedWeb.endSwap_apply]
  rw [← hd', W.incident_ends, ← hd, W.incident_ends, horient v i, horient v' j, he, hb]
  split_ifs <;> simp

/-- Every face of a `{1,2}`-labelled web has even boundary length. -/
theorem even_faceLength_of_one_or_two (hl : ∀ e, W.edgeLabel e = 1 ∨ W.edgeLabel e = 2)
    (f : W.toClosedWeb.Face) : Even (W.toClosedWeb.faceLength f) :=
  W.toClosedWeb.even_faceLength_of_bipartition (fun v => (W.ends (v, 0)).2)
    (W.oddOrientation_endSwap_of_one_or_two hl) f

/-- A compatibly planar `{1,2}`-labelled closed web with a vertex has a digon or square
face boundary. This counts occurrences and makes no assertion that the boundary is simple. -/
theorem exists_faceLength_two_or_four (hl : ∀ e, W.edgeLabel e = 1 ∨ W.edgeLabel e = 2)
    (hp : W.toClosedWeb.IsCompatiblyPlanar) [Nonempty W.Vertex] :
    ∃ f : W.toClosedWeb.Face,
      W.toClosedWeb.faceLength f = 2 ∨ W.toClosedWeb.faceLength f = 4 :=
  ClosedWeb.IsCompatiblyPlanar.exists_faceLength_two_or_four W.toClosedWeb hp
    (fun v => (W.ends (v, 0)).2)
    (W.oddOrientation_endSwap_of_one_or_two hl)

end LabeledClosedWeb

end TauCeti
