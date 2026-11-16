/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.Path

import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# The Bass–Serre tree of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ` and fix a base vertex `v₀ : Γ.V`. The
Bass–Serre tree `X(𝔸, v₀)` (`GraphOfGroups.bassSerreTree 𝔸 v₀`) is a `π₁(𝔸, v₀)`-tree constructed
from `𝔸`-paths starting at `v₀`:

* Its vertices over `v : Γ.V` are homotopy classes of `𝔸`-paths `p` from `v₀` to `v` modulo right
  multiplication by the vertex group `A_v` (`p ~ p · g` for `g ∈ A_v`).
* Its darts over `e : Γ.E` are homotopy classes of `𝔸`-paths `p` from `v₀` to `Γ.src e` modulo
  right multiplication by `α_e(A_e)` (`p ~ p · α_e(c)` for `c ∈ A_e`).
* A dart `(e, [p])` starts at `(Γ.src e, [p])`, ends at `(Γ.tgt e, [p · e])`, and has reverse
  `(Γ.rev e, [p · e])`.
* The fundamental group `π₁(𝔸, v₀)` acts on the left by path concatenation without inversions.

Connectedness follows by induction on the length of an `𝔸`-path from `v₀`. Acyclicity follows from
the normal form theorem for alternating `𝔸`-paths: a reduced path in `X(𝔸, v₀)` lifts to a reduced
alternating `𝔸`-path of the same length, and a reduced alternating closed path cannot be homotopic
to a vertex group letter unless its length is zero.

The stabilizer of a vertex `[p]` is the conjugate `p A_v p⁻¹ = (π₁.vertexHom p).range`, and the
stabilizer of a dart `(e, [p])` is `p α_e(A_e) p⁻¹ = (𝔸.α e).range.map (π₁.vertexHom p)`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre tree `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreBaseVertex`,
  `TauCeti.GraphOfGroups.bassSerreDart`: constructors for vertices, the base vertex, and darts.
* `TauCeti.GraphOfGroups.bassSerreVertexLift`, `TauCeti.GraphOfGroups.bassSerreDartLift`:
  universal properties descending invariant maps from `𝔸`-paths to vertices and darts.
* `TauCeti.GraphOfGroups.stabilizerBassSerreVertexEquiv`,
  `TauCeti.GraphOfGroups.stabilizerBassSerreDartEquiv`: isomorphisms of vertex and edge groups
  with the corresponding stabilizers in `π₁(𝔸, v₀)`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `X(𝔸, v₀)` is a Serre tree.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreVertex`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart_tgt`: explicit formulas for vertex and dart
  stabilizers.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open SerreGraph _root_.MulAction

variable {Γ : SerreGraph.{u, v}}

/-! ### Path equivalence relations and underlying Serre graph -/

section Construction

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Two pairs `(v, p)` and `(w, q)` represent the same vertex of the Bass–Serre tree when `v = w`
and the paths `p, q` differ on the right by an element of `A_v`. -/
private inductive VertexRel :
    (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) → (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) → Prop
  | intro {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (g : 𝔸.vertexGroup v) :
      p.Homotopic (q.comp (Path.ofVertex g)) → VertexRel ⟨v, p⟩ ⟨v, q⟩

private theorem vertexRel_equivalence : Equivalence (VertexRel 𝔸 v₀) where
  refl x := .intro 1 (by simpa only [Path.comp_ofVertex] using (Path.Homotopic.one x.2).symm)
  symm := by
    rintro _ _ h
    cases h with
    | @intro v p q g h =>
      refine .intro g⁻¹ ?_
      have hq : q.Homotopic ((q.comp (Path.ofVertex g)).comp (Path.ofVertex g⁻¹)) := by
        simp only [Path.comp_ofVertex]
        exact ((Path.Homotopic.one q).symm).trans
          (by simpa only [mul_inv_cancel] using (Path.Homotopic.mul q g g⁻¹).symm)
      exact hq.trans (h.symm.comp_right (Path.ofVertex g⁻¹))
  trans := by
    rintro _ _ _ ⟨g, h₁⟩ ⟨h, h₂⟩
    refine .intro (h * g) ?_
    have h₃ := h₁.trans (h₂.comp_right (Path.ofVertex g))
    rw [Path.comp_ofVertex, Path.comp_ofVertex] at h₃
    rw [Path.comp_ofVertex]
    exact h₃.trans (Path.Homotopic.mul _ h g)

private def vertexSetoid : Setoid (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  ⟨VertexRel 𝔸 v₀, vertexRel_equivalence 𝔸 v₀⟩

/-- Two pairs `(e, p)` and `(f, q)` represent the same dart of the Bass–Serre tree when `e = f` and
the paths `p, q` differ on the right by an element of `α_e(A_e)`. -/
private inductive DartRel :
    (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) → (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) → Prop
  | intro {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
      p.Homotopic (q.comp (Path.ofVertex (𝔸.α e c))) → DartRel ⟨e, p⟩ ⟨e, q⟩

private theorem dartRel_equivalence : Equivalence (DartRel 𝔸 v₀) where
  refl d :=
    .intro 1 (by simpa only [map_one, Path.comp_ofVertex] using (Path.Homotopic.one d.2).symm)
  symm := by
    rintro _ _ h
    cases h with
    | @intro e p q c h =>
      refine .intro c⁻¹ ?_
      have hq : q.Homotopic
          ((q.comp (Path.ofVertex (𝔸.α e c))).comp (Path.ofVertex (𝔸.α e c⁻¹))) := by
        simp only [Path.comp_ofVertex, map_inv]
        exact ((Path.Homotopic.one q).symm).trans
          (by simpa only [mul_inv_cancel] using (Path.Homotopic.mul q (𝔸.α e c) (𝔸.α e c)⁻¹).symm)
      exact hq.trans (h.symm.comp_right (Path.ofVertex (𝔸.α e c⁻¹)))
  trans := by
    rintro _ _ _ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine .intro (c₂ * c₁) ?_
    have h₃ := h₁.trans (h₂.comp_right (Path.ofVertex (𝔸.α _ c₁)))
    rw [Path.comp_ofVertex, Path.comp_ofVertex] at h₃
    rw [Path.comp_ofVertex, map_mul]
    exact h₃.trans (Path.Homotopic.mul _ (𝔸.α _ c₂) (𝔸.α _ c₁))

private def dartSetoid : Setoid (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :=
  ⟨DartRel 𝔸 v₀, dartRel_equivalence 𝔸 v₀⟩

/-- Traversing a dart followed by its reversed dart is homotopic to the prefix, accounting for the
endpoint equality `Γ.tgt (Γ.rev e) = Γ.src e`. -/
private theorem path_cons_dart_rev_homotopic {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}
    (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    Path.Homotopic
      (((p.cons (Letter.dart (Γ.dart e))).cons (Letter.dart (Γ.dart (Γ.rev e)))).cast rfl
        (congrArg (fun a : Γ.V => (⟨a⟩ : 𝔸.LetterVertex)) (Γ.tgt_rev e))) p := by
  have key : ∀ {a : Γ.V} (ha : a = Γ.src e) (f : Γ.tgt e ⟶ a),
      f.1 = Γ.rev e →
      Path.Homotopic
        (((p.cons (Letter.dart (Γ.dart e))).cons (Letter.dart f)).cast rfl
          (congrArg (fun b : Γ.V => (⟨b⟩ : 𝔸.LetterVertex)) ha)) p := by
    rintro _ rfl f hf
    have hfe : f = Quiver.reverse (Γ.dart e) :=
      Γ.eq_reverse_of_val_eq_rev (by rw [hf, Γ.dart_val])
    rw [hfe, Quiver.Path.cast_rfl_rfl]
    exact Path.Homotopic.dart_reverse p (Γ.dart e)
  exact key (Γ.tgt_rev e) (Γ.dart (Γ.rev e)) (Γ.dart_val (Γ.rev e))

private theorem dartRel_of_eq {e₁ e₂ : Γ.E} (he : e₁ = e₂)
    (p₁ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₁⟩) (p₂ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₂⟩)
    (hp : Path.Homotopic
      (p₁.cast rfl (congrArg (fun e : Γ.E => (⟨Γ.src e⟩ : 𝔸.LetterVertex)) he)) p₂) :
    DartRel 𝔸 v₀ ⟨e₁, p₁⟩ ⟨e₂, p₂⟩ := by
  subst he
  rw [Quiver.Path.cast_rfl_rfl] at hp
  exact .intro 1 (by
    simpa only [map_one, Path.comp_ofVertex] using hp.trans (Path.Homotopic.one p₂).symm)

private theorem eq_of_dartRel {d₁ d₂ : Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    (h : DartRel 𝔸 v₀ d₁ d₂) : d₁.1 = d₂.1 := by
  cases h
  rfl

private theorem dartRel_cons_dart {d₁ d₂ : Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    (h : DartRel 𝔸 v₀ d₁ d₂) :
    DartRel 𝔸 v₀ ⟨Γ.rev d₁.1, d₁.2.cons (Letter.dart (Γ.dart d₁.1))⟩
      ⟨Γ.rev d₂.1, d₂.2.cons (Letter.dart (Γ.dart d₂.1))⟩ := by
  cases h with
  | @intro e p q c hc =>
    let c' : 𝔸.edgeGroup (Γ.toGeomEdge (Γ.rev e)) :=
      (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c
    refine .intro c' ?_
    have hα : 𝔸.α (Γ.rev e) c' = 𝔸.ω e c := by
      rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
    have h' : Path.Homotopic (p.cons (Letter.dart (Γ.dart e)))
        ((q.cons (Letter.vertex (𝔸.α e c))).cons (Letter.dart (Γ.dart e))) := by
      simpa only [Path.comp_ofVertex] using hc.cons (Letter.dart (Γ.dart e))
    have hω : Path.Homotopic (p.cons (Letter.dart (Γ.dart e)))
        ((q.cons (Letter.dart (Γ.dart e))).cons (Letter.vertex (𝔸.ω e c))) :=
      h'.trans (Path.Homotopic.dart_ω e c q).symm
    rw [Path.comp_ofVertex]
    rw [hα]
    exact hω

/-- The underlying Serre graph of the Bass–Serre tree `X(𝔸, v₀)`. -/
private def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := Quotient (vertexSetoid 𝔸 v₀)
  E := Quotient (dartSetoid 𝔸 v₀)
  src := Quotient.map (sa := dartSetoid 𝔸 v₀) (sb := vertexSetoid 𝔸 v₀)
    (fun d => ⟨Γ.src d.1, d.2⟩)
    (fun _ _ h => by cases h with | intro c hc => exact .intro (𝔸.α _ c) hc)
  rev := Quotient.map (sa := dartSetoid 𝔸 v₀) (sb := dartSetoid 𝔸 v₀)
    (fun d => ⟨Γ.rev d.1, d.2.cons (Letter.dart (Γ.dart d.1))⟩)
    (fun _ _ h => dartRel_cons_dart 𝔸 v₀ h)
  rev_rev d := by
    induction d using Quotient.ind with
    | _ d =>
      exact Quotient.sound (dartRel_of_eq 𝔸 v₀ (Γ.rev_rev d.1) _ d.2
        (path_cons_dart_rev_homotopic d.1 d.2))
  rev_ne d := by
    induction d using Quotient.ind with
    | _ d =>
      intro h
      exact Γ.rev_ne d.1 (eq_of_dartRel 𝔸 v₀ (Quotient.exact h))

private def mkVertex {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (bassSerreGraph 𝔸 v₀).V :=
  Quotient.mk (vertexSetoid 𝔸 v₀) ⟨v, p⟩

private def mkDart {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (bassSerreGraph 𝔸 v₀).E :=
  Quotient.mk (dartSetoid 𝔸 v₀) ⟨e, p⟩

private def mkDartArrow {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} {a b : Γ.V} (e : a ⟶ b)
    (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) : (bassSerreGraph 𝔸 v₀).E :=
  mkDart e.1 (p.cast rfl (congrArg (fun c : Γ.V => (⟨c⟩ : 𝔸.LetterVertex)) e.2.1.symm))

variable {𝔸 v₀}

private theorem eq_of_mkVertex_eq {v w : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩} {q : 𝔸.Path ⟨v₀⟩ ⟨w⟩}
    (h : mkVertex p = mkVertex q) : v = w := by
  cases Quotient.exact h
  rfl

private theorem eq_of_mkDart_eq {e f : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src f⟩} (h : mkDart e p = mkDart f q) : e = f :=
  eq_of_dartRel 𝔸 v₀ (Quotient.exact h)

private theorem mkVertex_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    mkVertex p = mkVertex q ↔ ∃ g : 𝔸.vertexGroup v, p.Homotopic (q.comp (Path.ofVertex g)) :=
  (Quotient.eq (r := vertexSetoid 𝔸 v₀)).trans
    ⟨fun h => by cases h with | intro g hg => exact ⟨g, hg⟩, fun ⟨g, hg⟩ => .intro g hg⟩

private theorem mkDart_eq_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    mkDart e p = mkDart e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.comp (Path.ofVertex (𝔸.α e c))) :=
  (Quotient.eq (r := dartSetoid 𝔸 v₀)).trans
    ⟨fun h => by cases h with | intro c hc => exact ⟨c, hc⟩, fun ⟨c, hc⟩ => .intro c hc⟩

private theorem mkVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    mkVertex p = mkVertex q :=
  mkVertex_eq_iff.mpr
    ⟨1, by simpa only [Path.comp_ofVertex] using h.trans (Path.Homotopic.one q).symm⟩

private theorem mkDart_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    mkDart e p = mkDart e q :=
  mkDart_eq_iff.mpr
    ⟨1, by simpa only [map_one, Path.comp_ofVertex] using h.trans (Path.Homotopic.one q).symm⟩

private theorem mkVertex_comp_ofVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v) :
    mkVertex (p.comp (Path.ofVertex g)) = mkVertex p :=
  mkVertex_eq_iff.mpr ⟨g, .refl _⟩

private theorem mkDart_comp_ofVertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    mkDart e (p.comp (Path.ofVertex (𝔸.α e c))) = mkDart e p :=
  mkDart_eq_iff.mpr ⟨c, .refl _⟩

private theorem mkDartArrow_congr {a b : Γ.V} (e : a ⟶ b) {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩}
    (h : p.Homotopic q) : mkDartArrow e p = mkDartArrow e q := by
  obtain ⟨e, rfl, rfl⟩ := e
  exact mkDart_congr h

private theorem mkDartArrow_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    mkDartArrow (Γ.dart e) p = mkDart e p := by
  rw [Γ.dart_def]
  rfl

private theorem src_mkDartArrow {a b : Γ.V} (e : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (bassSerreGraph 𝔸 v₀).src (mkDartArrow e p) = mkVertex p := by
  obtain ⟨e, rfl, rfl⟩ := e
  rfl

private theorem rev_mkDartArrow {a b : Γ.V} (e : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (bassSerreGraph 𝔸 v₀).rev (mkDartArrow e p) =
      mkDartArrow (Quiver.reverse e) (p.cons (Letter.dart e)) := by
  have key : ∀ (f : b ⟶ a), f.1 = Γ.rev e.1 →
      (bassSerreGraph 𝔸 v₀).rev (mkDartArrow e p) =
        mkDartArrow f (p.cons (Letter.dart e)) := by
    obtain ⟨e, rfl, rfl⟩ := e
    rintro ⟨f, _, _⟩ rfl
    simp only [bassSerreGraph, mkDartArrow, mkDart, Quotient.map_mk, Γ.dart_def]
    congr 1
  exact key (Quiver.reverse e) (Γ.reverse_val e)

private theorem tgt_mkDartArrow {a b : Γ.V} (e : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (bassSerreGraph 𝔸 v₀).tgt (mkDartArrow e p) = mkVertex (p.cons (Letter.dart e)) := by
  obtain ⟨e, rfl, rfl⟩ := e
  simp only [SerreGraph.tgt, bassSerreGraph, mkDartArrow, mkDart, mkVertex,
    Quiver.Path.cast_rfl_rfl, Quotient.map_mk, Γ.dart_def]

private theorem mkDartArrow_reverse_cons_ωArrow {a b : Γ.V} (e : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    mkDartArrow (Quiver.reverse e) ((p.cons (Letter.dart e)).cons (Letter.vertex (𝔸.ωArrow e c))) =
      mkDartArrow (Quiver.reverse e) (p.cons (Letter.dart e)) := by
  have key : ∀ (f : b ⟶ a), f.1 = Γ.rev e.1 →
      mkDartArrow f ((p.cons (Letter.dart e)).cons (Letter.vertex (𝔸.ωArrow e c))) =
        mkDartArrow f (p.cons (Letter.dart e)) := by
    obtain ⟨e, rfl, rfl⟩ := e
    rintro ⟨f, _, _⟩ rfl
    let c' : 𝔸.edgeGroup (Γ.toGeomEdge (Γ.rev e)) :=
      (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c
    have hα : 𝔸.α (Γ.rev e) c' = 𝔸.ω e c := by
      rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
    have h := mkDart_comp_ofVertex_α (Γ.rev e) (p.cons (Letter.dart ⟨e, rfl, rfl⟩)) c'
    rw [Path.comp_ofVertex, hα] at h
    rw [𝔸.ωArrow_mk]
    simpa only [mkDartArrow, SerreGraph.tgt, Quiver.Path.cast_rfl_rfl] using h
  exact key (Quiver.reverse e) (Γ.reverse_val e)

/-! ### Connectedness and acyclicity -/

private theorem nonempty_path_to_mkVertex :
    ∀ {y : 𝔸.LetterVertex} (p : 𝔸.Path ⟨v₀⟩ y),
      Nonempty ((bassSerreGraph 𝔸 v₀).Path (mkVertex (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) (mkVertex p))
  | _, .nil => ⟨.nil⟩
  | _, .cons p (.vertex g) => by
    have h := mkVertex_comp_ofVertex p g
    rw [Path.comp_ofVertex] at h
    rw [h]
    exact nonempty_path_to_mkVertex p
  | _, .cons p (.dart e) => by
    obtain ⟨γ⟩ := nonempty_path_to_mkVertex p
    exact ⟨γ.cons ⟨mkDartArrow e p, src_mkDartArrow e p, tgt_mkDartArrow e p⟩⟩

variable (𝔸 v₀) in
private theorem bassSerreGraph_connected : (bassSerreGraph 𝔸 v₀).Connected := by
  refine ((bassSerreGraph 𝔸 v₀).connected_iff).mpr
    ⟨⟨mkVertex (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)⟩,
      (bassSerreGraph 𝔸 v₀).preconnected_of_forall_nonempty_path
        (mkVertex (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) ?_⟩
  intro x
  induction x using Quotient.ind with
  | _ x => exact nonempty_path_to_mkVertex x.2

/-- If two consecutive darts in `bassSerreGraph` do not reverse each other, then the lifted
alternating path does not cancel at the new dart. -/
private theorem not_cancels_of_ne_rev {u a b c : Γ.V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨u⟩)
    (β : 𝔸.AlternatingPath u a) (e₀ : a ⟶ b) (g : 𝔸.vertexGroup b) (e : b ⟶ c)
    (hne : mkDartArrow e (p₀.comp (AlternatingPath.cons β e₀ g).toPath) ≠
      (bassSerreGraph 𝔸 v₀).rev (mkDartArrow e₀ (p₀.comp β.toPath))) :
    ¬ (AlternatingPath.cons β e₀ g).Cancels e := by
  intro hcan
  rw [AlternatingPath.cancels_cons_iff_ωArrow] at hcan
  obtain ⟨he_rev, k, hk⟩ := hcan
  have hc_eq : c = a := Γ.tgt_eq_src_of_val_eq_rev he_rev
  subst hc_eq
  have hrev_arrow : e = Quiver.reverse e₀ := Γ.eq_reverse_of_val_eq_rev he_rev
  apply hne
  rw [rev_mkDartArrow, hrev_arrow, ← hk, AlternatingPath.toPath_cons, Quiver.Path.comp_cons,
    Quiver.Path.comp_cons]
  exact mkDartArrow_reverse_cons_ωArrow e₀ (p₀.comp β.toPath) k

/-- Extending a lifted alternating path along a dart of `bassSerreGraph` preserves reducedness when
the extended graph path is reduced. -/
private theorem lift_step_isReduced {u : Γ.V} {x y z : (bassSerreGraph 𝔸 v₀).V}
    (p₀ : 𝔸.Path ⟨v₀⟩ ⟨u⟩) (γ : (bassSerreGraph 𝔸 v₀).Path x y) (e : Γ.E)
    (r : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (f : @Quiver.Hom (bassSerreGraph 𝔸 v₀).V (bassSerreGraph 𝔸 v₀).toQuiver y z)
    (hf : f.1 = mkDart e r) (α : 𝔸.AlternatingPath u (Γ.src e)) (g : 𝔸.vertexGroup (Γ.src e))
    (hlen : α.length = γ.length)
    (hdart_eq : mkDart e r = mkDartArrow (Γ.dart e) (p₀.comp (α.setLast (α.last * g)).toPath))
    (hred : SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) γ → α.IsReduced)
    (hlast : ∀ d ∈ (SerreGraph.Path.darts (bassSerreGraph 𝔸 v₀) γ).getLast?,
      ∃ (a : Γ.V) (β : 𝔸.AlternatingPath u a) (e₀ : a ⟶ Γ.src e),
        α = AlternatingPath.cons β e₀ 1 ∧ d = mkDartArrow e₀ (p₀.comp β.toPath))
    (hred_cons : SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) (γ.cons f)) :
    (AlternatingPath.cons (α.setLast (α.last * g)) (Γ.dart e) 1).IsReduced := by
  rw [AlternatingPath.isReduced_cons_iff]
  refine ⟨(AlternatingPath.isReduced_setLast α _).mpr (hred (hred_cons.of_cons _)), ?_⟩
  cases γ with
  | nil =>
    have hu : u = Γ.src e := by
      cases α with
      | single _ => rfl
      | cons _ _ _ => simp at hlen
    subst hu
    rw [AlternatingPath.length_eq_zero_iff.mp hlen]
    simp
  | cons γ₁ f₀ =>
    obtain ⟨_, hne⟩ :=
      (SerreGraph.Path.isReduced_cons_cons (bassSerreGraph 𝔸 v₀) γ₁ f₀ f).mp hred_cons
    obtain ⟨a, β, e₀, hα_eq, hf₀_eq⟩ := hlast f₀.1 (by simp)
    have hα₁_eq : α.setLast (α.last * g) = AlternatingPath.cons β e₀ g := by simp [hα_eq]
    rw [hα₁_eq]
    apply not_cancels_of_ne_rev p₀ β e₀ g (Γ.dart e)
    rw [← hα₁_eq, ← hdart_eq, ← hf, ← hf₀_eq]
    exact hne

/-- Extending an alternating-path lift by one dart of `bassSerreGraph`, preserving reducedness and
the last-dart invariant. -/
private theorem lift_step_alternatingPath {u v : Γ.V} {x y z : (bassSerreGraph 𝔸 v₀).V}
    (p₀ : 𝔸.Path ⟨v₀⟩ ⟨u⟩) (γ : (bassSerreGraph 𝔸 v₀).Path x y)
    (f : @Quiver.Hom (bassSerreGraph 𝔸 v₀).V (bassSerreGraph 𝔸 v₀).toQuiver y z)
    (α : 𝔸.AlternatingPath u v)
    (hlen : α.length = γ.length)
    (hend : mkVertex (p₀.comp α.toPath) = y)
    (hred : SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) γ → α.IsReduced)
    (hlast : ∀ d ∈ (SerreGraph.Path.darts (bassSerreGraph 𝔸 v₀) γ).getLast?,
      ∃ (a : Γ.V) (β : 𝔸.AlternatingPath u a) (e₀ : a ⟶ v),
        α = AlternatingPath.cons β e₀ 1 ∧ d = mkDartArrow e₀ (p₀.comp β.toPath)) :
    ∃ (w : Γ.V) (α' : 𝔸.AlternatingPath u w),
      α'.length = (γ.cons f).length ∧
      mkVertex (p₀.comp α'.toPath) = z ∧
      (SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) (γ.cons f) → α'.IsReduced) ∧
      ∀ d ∈ (SerreGraph.Path.darts (bassSerreGraph 𝔸 v₀) (γ.cons f)).getLast?,
        ∃ (a : Γ.V) (β : 𝔸.AlternatingPath u a) (e₀ : a ⟶ w),
          α' = AlternatingPath.cons β e₀ 1 ∧ d = mkDartArrow e₀ (p₀.comp β.toPath) := by
  rcases f with ⟨d, hf_src, hf_tgt⟩
  induction d using Quotient.ind with
  | _ d =>
    rcases d with ⟨e, r⟩
    have he_src : Γ.src e = v := eq_of_mkVertex_eq (hf_src.trans hend.symm)
    subst he_src
    obtain ⟨g, hg⟩ := mkVertex_eq_iff.mp (hf_src.trans hend.symm)
    let α₁ : 𝔸.AlternatingPath u (Γ.src e) := α.setLast (α.last * g)
    let α' : 𝔸.AlternatingPath u (Γ.tgt e) := AlternatingPath.cons α₁ (Γ.dart e) 1
    have hα₁_hom : Path.Homotopic r (p₀.comp α₁.toPath) := by
      have hmul := (AlternatingPath.toPath_setLast_mul_homotopic α g).comp_left p₀
      rw [Quiver.Path.comp_cons, ← Path.comp_ofVertex] at hmul
      exact hg.trans hmul.symm
    have hdart_eq : mkDart e r = mkDartArrow (Γ.dart e) (p₀.comp α₁.toPath) :=
      (mkDart_congr hα₁_hom).trans (mkDartArrow_dart e _).symm
    refine ⟨Γ.tgt e, α', by simp [α', α₁, hlen], ?_,
      lift_step_isReduced p₀ γ e r ⟨mkDart e r, hf_src, hf_tgt⟩ rfl α g hlen hdart_eq hred hlast,
      ?_⟩
    · have hend' : mkVertex (p₀.comp α'.toPath) =
          (bassSerreGraph 𝔸 v₀).tgt (mkDartArrow (Γ.dart e) (p₀.comp α₁.toPath)) := by
        rw [tgt_mkDartArrow, AlternatingPath.toPath_cons, Quiver.Path.comp_cons,
          Quiver.Path.comp_cons, ← Path.comp_ofVertex]
        exact mkVertex_comp_ofVertex _ 1
      rw [hend', ← hdart_eq]
      exact hf_tgt
    · intro d' hd'
      rw [SerreGraph.Path.darts_cons, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hd'
      exact ⟨Γ.src e, α₁, Γ.dart e, rfl, hd'.symm.trans hdart_eq⟩

/-- Every path in `bassSerreGraph` starting at `mkVertex p₀` lifts to an alternating `𝔸`-path of
the same length whose reducedness is inherited from the graph path. -/
private theorem exists_alternatingPath_of_path {u : Γ.V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨u⟩)
    {x y : (bassSerreGraph 𝔸 v₀).V} (hp₀ : mkVertex p₀ = x)
    (γ : (bassSerreGraph 𝔸 v₀).Path x y) :
    ∃ (w : Γ.V) (α : 𝔸.AlternatingPath u w),
      α.length = γ.length ∧
      mkVertex (p₀.comp α.toPath) = y ∧
      (SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) γ → α.IsReduced) ∧
      ∀ d ∈ (SerreGraph.Path.darts (bassSerreGraph 𝔸 v₀) γ).getLast?,
        ∃ (a : Γ.V) (β : 𝔸.AlternatingPath u a) (e₀ : a ⟶ w),
          α = AlternatingPath.cons β e₀ 1 ∧ d = mkDartArrow e₀ (p₀.comp β.toPath) := by
  induction γ with
  | nil =>
    exact ⟨u, AlternatingPath.single 1, by simp, by
      simpa only [AlternatingPath.toPath_single] using
        (mkVertex_comp_ofVertex p₀ 1).trans hp₀,
      fun _ => AlternatingPath.isReduced_single 1, fun _ hd => by simp at hd⟩
  | cons γ f ih =>
    obtain ⟨w, α, hlen, hend, hred, hlast⟩ := ih
    exact lift_step_alternatingPath p₀ γ f α hlen hend hred hlast

private theorem eq_nil_of_isReduced_mkVertex {v : Γ.V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (γ : (bassSerreGraph 𝔸 v₀).Path (mkVertex p₀) (mkVertex p₀))
    (hγ : SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) γ) : γ = .nil := by
  obtain ⟨w, α, hlen, hend, hred, -⟩ := exists_alternatingPath_of_path p₀ rfl γ
  have hwu : w = v := eq_of_mkVertex_eq hend
  subst hwu
  obtain ⟨g, hg⟩ := mkVertex_eq_iff.mp hend
  have hα_hom : α.toPath.Homotopic (Path.ofVertex g) :=
    (Path.Homotopic.comp_left_iff p₀).mp hg
  have hα_eq : α = AlternatingPath.single g :=
    (hred hγ).toPath_homotopic_ofVertex_iff.mp hα_hom
  have hγ_len : γ.length = 0 := by rw [← hlen, hα_eq]; simp
  cases γ with
  | nil => rfl
  | cons _ _ => simp at hγ_len

variable (𝔸 v₀) in
private theorem bassSerreGraph_isAcyclic : (bassSerreGraph 𝔸 v₀).IsAcyclic := by
  rw [SerreGraph.isAcyclic_iff]
  intro x
  induction x using Quotient.ind with
  | _ x => exact fun γ hγ => eq_nil_of_isReduced_mkVertex x.2 γ hγ

variable (𝔸 v₀) in
private theorem bassSerreGraph_isTree : (bassSerreGraph 𝔸 v₀).IsTree :=
  (SerreGraph.isTree_iff (bassSerreGraph 𝔸 v₀)).mpr
    ⟨bassSerreGraph_connected 𝔸 v₀, bassSerreGraph_isAcyclic 𝔸 v₀⟩

/-! ### Left action of `π₁(𝔸, v₀)` without inversions -/

private def smulV (g : π₁ 𝔸 v₀) (x : (bassSerreGraph 𝔸 v₀).V) : (bassSerreGraph 𝔸 v₀).V :=
  π₁.lift
    (fun s => Quotient.map (sa := vertexSetoid 𝔸 v₀) (sb := vertexSetoid 𝔸 v₀)
      (fun y => ⟨y.1, s.comp y.2⟩)
      (fun _ _ h => by
        cases h with
        | intro a ha =>
          exact .intro a (by simpa only [Quiver.Path.comp_assoc] using ha.comp_left s)) x)
    (fun s₁ s₂ hs => by
      induction x using Quotient.ind with
      | _ y =>
        exact Quotient.sound (.intro 1 (by
          simpa only [Path.comp_ofVertex] using
            (hs.comp_right y.2).trans (Path.Homotopic.one (s₂.comp y.2)).symm)))
    g

private def smulE (g : π₁ 𝔸 v₀) (d : (bassSerreGraph 𝔸 v₀).E) : (bassSerreGraph 𝔸 v₀).E :=
  π₁.lift
    (fun s => Quotient.map (sa := dartSetoid 𝔸 v₀) (sb := dartSetoid 𝔸 v₀)
      (fun y => ⟨y.1, s.comp y.2⟩)
      (fun _ _ h => by
        cases h with
        | intro c hc =>
          exact .intro c (by simpa only [Quiver.Path.comp_assoc] using hc.comp_left s)) d)
    (fun s₁ s₂ hs => by
      induction d using Quotient.ind with
      | _ y =>
        exact Quotient.sound (.intro 1 (by
          simpa only [map_one, Path.comp_ofVertex] using
            (hs.comp_right y.2).trans (Path.Homotopic.one (s₂.comp y.2)).symm)))
    g

private theorem smulV_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    smulV (π₁.mk s) (mkVertex p) = mkVertex (s.comp p) :=
  π₁.lift_mk (a := v₀) (β := (bassSerreGraph 𝔸 v₀).V) _ _ s

private theorem smulE_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    smulE (π₁.mk s) (mkDart e p) = mkDart e (s.comp p) :=
  π₁.lift_mk (a := v₀) (β := (bassSerreGraph 𝔸 v₀).E) _ _ s

private theorem smulV_one (x : (bassSerreGraph 𝔸 v₀).V) : smulV (1 : π₁ 𝔸 v₀) x = x := by
  induction x using Quotient.ind with
  | _ y =>
    rw [← π₁.mk_nil]
    refine (smulV_mk .nil y.2).trans (mkVertex_congr ?_)
    simp only [Quiver.Path.nil_comp]
    exact .refl _

private theorem smulV_mul (g h : π₁ 𝔸 v₀) (x : (bassSerreGraph 𝔸 v₀).V) :
    smulV (g * h) x = smulV g (smulV h x) := by
  induction g using π₁.induction_on with | h s =>
  induction h using π₁.induction_on with | h t =>
  induction x using Quotient.ind with | _ y =>
  rw [← π₁.mk_comp]
  exact (smulV_mk (s.comp t) y.2).trans <| by
    rw [Quiver.Path.comp_assoc, ← smulV_mk s (t.comp y.2), ← smulV_mk t y.2]
    rfl

private theorem smulE_one (d : (bassSerreGraph 𝔸 v₀).E) : smulE (1 : π₁ 𝔸 v₀) d = d := by
  induction d using Quotient.ind with
  | _ y =>
    rw [← π₁.mk_nil]
    refine (smulE_mk .nil y.1 y.2).trans (mkDart_congr ?_)
    simp only [Quiver.Path.nil_comp]
    exact .refl _

private theorem smulE_mul (g h : π₁ 𝔸 v₀) (d : (bassSerreGraph 𝔸 v₀).E) :
    smulE (g * h) d = smulE g (smulE h d) := by
  induction g using π₁.induction_on with | h s =>
  induction h using π₁.induction_on with | h t =>
  induction d using Quotient.ind with | _ y =>
  rw [← π₁.mk_comp]
  exact (smulE_mk (s.comp t) y.1 y.2).trans <| by
    rw [Quiver.Path.comp_assoc, ← smulE_mk s y.1 (t.comp y.2), ← smulE_mk t y.1 y.2]
    rfl

variable (𝔸 v₀) in
private def bassSerreAction : π₁ 𝔸 v₀ →* (bassSerreGraph 𝔸 v₀).Aut where
  toFun g :=
    { equivV :=
        { toFun := smulV g
          invFun := smulV g⁻¹
          left_inv x := by rw [← smulV_mul, inv_mul_cancel, smulV_one]
          right_inv x := by rw [← smulV_mul, mul_inv_cancel, smulV_one] }
      equivE :=
        { toFun := smulE g
          invFun := smulE g⁻¹
          left_inv d := by rw [← smulE_mul, inv_mul_cancel, smulE_one]
          right_inv d := by rw [← smulE_mul, mul_inv_cancel, smulE_one] }
      map_src d := by
        induction g using π₁.induction_on with | h s =>
        induction d using Quotient.ind with | _ y =>
        exact (congrArg (bassSerreGraph 𝔸 v₀).src (smulE_mk s y.1 y.2)).trans
          (smulV_mk s y.2).symm
      map_rev d := by
        induction g using π₁.induction_on with | h s =>
        induction d using Quotient.ind with | _ y =>
        exact (smulE_mk s (Γ.rev y.1) _).trans
          (congrArg (bassSerreGraph 𝔸 v₀).rev (smulE_mk s y.1 y.2)).symm }
  map_one' := SerreGraph.Iso.ext (fun x => smulV_one x) (fun d => smulE_one d)
  map_mul' g h := SerreGraph.Iso.ext (fun x => smulV_mul g h x) (fun d => smulE_mul g h d)

private theorem bassSerreAction_smul_ne_rev (g : π₁ 𝔸 v₀) (d : (bassSerreGraph 𝔸 v₀).E) :
    (bassSerreAction 𝔸 v₀ g).equivE d ≠ (bassSerreGraph 𝔸 v₀).rev d := by
  induction g using π₁.induction_on with | h s =>
  induction d using Quotient.ind with | _ y =>
  intro h
  have h' : mkDart y.1 (s.comp y.2) = mkDart (Γ.rev y.1) (y.2.cons (Letter.dart (Γ.dart y.1))) :=
    (smulE_mk s y.1 y.2).symm.trans h
  exact Γ.rev_ne y.1 (eq_of_mkDart_eq h').symm

end Construction

/-! ### The Bass–Serre tree -/

section PublicAPI

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`, as a
`π₁(𝔸, v₀)`-tree. -/
def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := bassSerreGraph 𝔸 v₀
  isTree := bassSerreGraph_isTree 𝔸 v₀
  action := bassSerreAction 𝔸 v₀
  action_smul_ne_rev := bassSerreAction_smul_ne_rev

/-- The underlying graph of the Bass–Serre tree is a Serre tree. -/
@[simp] theorem bassSerreTree_isTree : (𝔸.bassSerreTree v₀).toSerreGraph.IsTree :=
  (𝔸.bassSerreTree v₀).isTree

variable {𝔸 v₀}

/-- The vertex of `bassSerreTree 𝔸 v₀` represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (𝔸.bassSerreTree v₀).V :=
  mkVertex p

variable (𝔸 v₀) in
/-- The base vertex of `bassSerreTree 𝔸 v₀`, represented by the empty path at `v₀`. -/
def bassSerreBaseVertex : (𝔸.bassSerreTree v₀).V :=
  bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)

variable (𝔸 v₀) in
theorem bassSerreBaseVertex_def :
    𝔸.bassSerreBaseVertex v₀ = bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) := (rfl)

/-- The dart of `bassSerreTree 𝔸 v₀` over `e` represented by an `𝔸`-path `p` from `v₀` to
`Γ.src e`. -/
def bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreTree v₀).E :=
  mkDart e p

/-- Prove a property of vertices of the Bass–Serre tree by checking it on representatives
`bassSerreVertex p`. -/
@[elab_as_elim] theorem bassSerreVertex_induction_on
    {P : (𝔸.bassSerreTree v₀).V → Prop} (x : (𝔸.bassSerreTree v₀).V)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (bassSerreVertex p)) : P x :=
  Quotient.inductionOn x fun y => h y.2

/-- Prove a property of darts of the Bass–Serre tree by checking it on representatives
`bassSerreDart e p`. -/
@[elab_as_elim] theorem bassSerreDart_induction_on
    {P : (𝔸.bassSerreTree v₀).E → Prop} (d : (𝔸.bassSerreTree v₀).E)
    (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (bassSerreDart e p)) : P d :=
  Quotient.inductionOn d fun y => h y.1 y.2

variable (𝔸 v₀) in
/-- A family of functions on `𝔸`-paths from `v₀` that respects homotopy and right multiplication by
vertex group elements descends to the vertices of the Bass–Serre tree. -/
def bassSerreVertexLift {β : Sort*}
    (f : ∀ (v : Γ.V), 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (hhom : ∀ (v : Γ.V) {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f v p = f v q)
    (hmul : ∀ (v : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      f v (p.comp (Path.ofVertex g)) = f v p) :
    (𝔸.bassSerreTree v₀).V → β :=
  Quotient.lift (s := vertexSetoid 𝔸 v₀) (fun y => f y.1 y.2)
    (fun _ _ h => by cases h with | intro g hg => exact (hhom _ hg).trans (hmul _ _ g))

@[simp] theorem bassSerreVertexLift_vertex {β : Sort*}
    (f : ∀ (v : Γ.V), 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (hhom : ∀ (v : Γ.V) {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f v p = f v q)
    (hmul : ∀ (v : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      f v (p.comp (Path.ofVertex g)) = f v p)
    {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    bassSerreVertexLift 𝔸 v₀ f hhom hmul (bassSerreVertex p) = f v p := (rfl)

variable (𝔸 v₀) in
/-- A family of functions on pairs `(e, p)` that respects homotopy and right multiplication by
`α_e(A_e)` descends to the darts of the Bass–Serre tree. -/
def bassSerreDartLift {β : Sort*}
    (f : ∀ (e : Γ.E), 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → β)
    (hhom : ∀ (e : Γ.E) {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}, p.Homotopic q → f e p = f e q)
    (hmul : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      f e (p.comp (Path.ofVertex (𝔸.α e c))) = f e p) :
    (𝔸.bassSerreTree v₀).E → β :=
  Quotient.lift (s := dartSetoid 𝔸 v₀) (fun y => f y.1 y.2)
    (fun _ _ h => by cases h with | intro c hc => exact (hhom _ hc).trans (hmul _ _ c))

@[simp] theorem bassSerreDartLift_dart {β : Sort*}
    (f : ∀ (e : Γ.E), 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → β)
    (hhom : ∀ (e : Γ.E) {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}, p.Homotopic q → f e p = f e q)
    (hmul : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      f e (p.comp (Path.ofVertex (𝔸.α e c))) = f e p)
    (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    bassSerreDartLift 𝔸 v₀ f hhom hmul (bassSerreDart e p) = f e p := (rfl)

/-- Two paths with the same endpoint represent the same vertex of the Bass–Serre tree exactly when
they differ on the right by a vertex group element. -/
theorem bassSerreVertex_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    bassSerreVertex p = bassSerreVertex q ↔
      ∃ g : 𝔸.vertexGroup v, p.Homotopic (q.comp (Path.ofVertex g)) :=
  mkVertex_eq_iff

/-- Equal Bass–Serre vertices lie over the same vertex of `Γ`. -/
theorem eq_of_bassSerreVertex_eq {v w : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩} {q : 𝔸.Path ⟨v₀⟩ ⟨w⟩}
    (h : bassSerreVertex p = bassSerreVertex q) : v = w :=
  eq_of_mkVertex_eq h

/-- Two paths to `Γ.src e` represent the same dart over `e` in the Bass–Serre tree exactly when
they differ on the right by an element of `α_e(A_e)`. -/
theorem bassSerreDart_eq_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    bassSerreDart e p = bassSerreDart e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.comp (Path.ofVertex (𝔸.α e c))) :=
  mkDart_eq_iff

/-- Equal Bass–Serre darts lie over the same dart of `Γ`. -/
theorem eq_of_bassSerreDart_eq {e f : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src f⟩} (h : bassSerreDart e p = bassSerreDart f q) : e = f :=
  eq_of_mkDart_eq h

/-- Homotopic paths represent the same vertex of the Bass–Serre tree. -/
theorem bassSerreVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    bassSerreVertex p = bassSerreVertex q :=
  mkVertex_congr h

/-- Homotopic paths represent the same dart of the Bass–Serre tree. -/
theorem bassSerreDart_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    bassSerreDart e p = bassSerreDart e q :=
  mkDart_congr h

/-- Right multiplication by a vertex group element does not change a Bass–Serre vertex. -/
theorem bassSerreVertex_comp_ofVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (g : 𝔸.vertexGroup v) : bassSerreVertex (p.comp (Path.ofVertex g)) = bassSerreVertex p :=
  mkVertex_comp_ofVertex p g

/-- Appending a vertex group letter does not change a Bass–Serre vertex. -/
@[simp] theorem bassSerreVertex_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (g : 𝔸.vertexGroup v) : bassSerreVertex (p.cons (Letter.vertex g)) = bassSerreVertex p := by
  rw [← Path.comp_ofVertex, bassSerreVertex_comp_ofVertex]

/-- Right multiplication by `α_e(c)` does not change a Bass–Serre dart over `e`. -/
theorem bassSerreDart_comp_ofVertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart e (p.comp (Path.ofVertex (𝔸.α e c))) = bassSerreDart e p :=
  mkDart_comp_ofVertex_α e p c

/-- Appending the vertex group letter `α_e(c)` does not change a Bass–Serre dart over `e`. -/
@[simp] theorem bassSerreDart_cons_vertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart e (p.cons (Letter.vertex (𝔸.α e c))) = bassSerreDart e p := by
  rw [← Path.comp_ofVertex, bassSerreDart_comp_ofVertex_α]

@[simp] theorem bassSerreTree_src_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).src (bassSerreDart e p) = bassSerreVertex p := (rfl)

@[simp] theorem bassSerreTree_rev_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).rev (bassSerreDart e p) =
      bassSerreDart (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) := (rfl)

@[simp] theorem bassSerreTree_tgt_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).tgt (bassSerreDart e p) =
      bassSerreVertex (p.cons (Letter.dart (Γ.dart e))) := (rfl)

/-- The fundamental group acts on vertices of the Bass–Serre tree by left path concatenation. -/
@[simp] theorem smul_bassSerreVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • bassSerreVertex p = bassSerreVertex (s.comp p) :=
  smulV_mk s p

/-- The fundamental group acts on darts of the Bass–Serre tree by left path concatenation. -/
@[simp] theorem smul_bassSerreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk s • bassSerreDart e p = bassSerreDart e (s.comp p) :=
  smulE_mk s e p

end PublicAPI

/-! ### Stabilizers of vertices and darts -/

section Stabilizers

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- The stabilizer of the vertex `bassSerreVertex p` in `π₁(𝔸, v₀)` is `p A_v p⁻¹`. -/
theorem stabilizer_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p) = (π₁.vertexHom p).range := by
  ext x
  induction x using π₁.induction_on with | h s =>
  rw [mem_stabilizer_iff, smul_bassSerreVertex, bassSerreVertex_eq_iff, MonoidHom.mem_range]
  refine exists_congr fun g => ?_
  rw [Path.Homotopic.comp_homotopic_iff_homotopic_comp_reverse, π₁.vertexHom_apply, eq_comm,
    π₁.mk_eq_mk_iff]

/-- The stabilizer of the base vertex in `π₁(𝔸, v₀)` is the image of `A_{v₀}`. -/
theorem stabilizer_bassSerreBaseVertex (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreBaseVertex v₀) =
      (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  stabilizer_bassSerreVertex Quiver.Path.nil

/-- When a vertex group `A_v` is trivial, every Bass–Serre vertex over `v` has trivial
stabilizer. -/
theorem stabilizer_bassSerreVertex_eq_bot_of_subsingleton {v : Γ.V}
    [Subsingleton (𝔸.vertexGroup v)] (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p) = ⊥ := by
  rw [stabilizer_bassSerreVertex, eq_bot_iff]
  rintro _ ⟨g, rfl⟩
  rw [Subsingleton.elim g 1, map_one]
  exact Subgroup.one_mem ⊥

/-- The stabilizer of the dart `bassSerreDart e p` in `π₁(𝔸, v₀)` is `p α_e(A_e) p⁻¹`. -/
theorem stabilizer_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p) = (𝔸.α e).range.map (π₁.vertexHom p) := by
  ext x
  induction x using π₁.induction_on with | h s =>
  rw [mem_stabilizer_iff, smul_bassSerreDart, bassSerreDart_eq_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨𝔸.α e c, ⟨c, rfl⟩, ?_⟩
    rw [π₁.vertexHom_apply, eq_comm, π₁.mk_eq_mk_iff]
    exact Path.Homotopic.comp_homotopic_iff_homotopic_comp_reverse.mp hc
  · rintro ⟨_, ⟨c, rfl⟩, hc⟩
    rw [π₁.vertexHom_apply] at hc
    refine ⟨c, Path.Homotopic.comp_homotopic_iff_homotopic_comp_reverse.mpr ?_⟩
    rw [← π₁.mk_eq_mk_iff, eq_comm]
    exact hc

/-- Expressed at its target vertex, the stabilizer of `bassSerreDart e p` is
`(p e) ω_e(A_e) (p e)⁻¹`. -/
theorem stabilizer_bassSerreDart_tgt (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p) =
      (𝔸.ω e).range.map (π₁.vertexHom (p.cons (Letter.dart (Γ.dart e)))) := by
  rw [← (𝔸.bassSerreTree v₀).stabilizer_rev (bassSerreDart e p), bassSerreTree_rev_dart,
    stabilizer_bassSerreDart]
  congr 1
  ext g
  simp only [MonoidHom.mem_range]
  refine ⟨fun ⟨c, hc⟩ => ⟨_, (𝔸.α_rev_apply e c).symm.trans hc⟩, fun ⟨c, hc⟩ => ?_⟩
  refine ⟨(MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c, ?_⟩
  rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
  exact hc

/-- The isomorphism of the vertex group `A_v` with the stabilizer of `bassSerreVertex p`. -/
noncomputable def stabilizerBassSerreVertexEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.vertexGroup v ≃* stabilizer (π₁ 𝔸 v₀) (bassSerreVertex p) :=
  (MonoidHom.ofInjective (π₁.vertexHom_injective p)).trans
    (MulEquiv.subgroupCongr (stabilizer_bassSerreVertex p).symm)

@[simp] theorem stabilizerBassSerreVertexEquiv_apply_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (g : 𝔸.vertexGroup v) :
    (stabilizerBassSerreVertexEquiv p g : π₁ 𝔸 v₀) = π₁.vertexHom p g := by
  simp [stabilizerBassSerreVertexEquiv, MonoidHom.ofInjective_apply]

/-- The isomorphism of the edge group `A_e` with the stabilizer of `bassSerreDart e p`. -/
noncomputable def stabilizerBassSerreDartEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.edgeGroup (Γ.toGeomEdge e) ≃* stabilizer (π₁ 𝔸 v₀) (bassSerreDart e p) :=
  (MonoidHom.ofInjective (f := (π₁.vertexHom p).comp (𝔸.α e))
      ((π₁.vertexHom_injective p).comp (𝔸.α_injective e))).trans
    (MulEquiv.subgroupCongr (by rw [stabilizer_bassSerreDart, MonoidHom.range_comp]))

@[simp] theorem stabilizerBassSerreDartEquiv_apply_val (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    (stabilizerBassSerreDartEquiv e p c : π₁ 𝔸 v₀) = π₁.vertexHom p (𝔸.α e c) := by
  simp [stabilizerBassSerreDartEquiv, MonoidHom.ofInjective_apply]

end Stabilizers

end GraphOfGroups

end TauCeti
