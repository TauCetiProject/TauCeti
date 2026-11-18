/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.Combinatorics.Graph.Serre.Reduction
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# Construction, action, stabilizers, and stars of the Bass–Serre tree

Let `𝔸` be a graph of groups over a Serre graph `Γ`, with a chosen base vertex `v₀ : Γ.V`. The
Bass–Serre covering tree `𝔸.bassSerreTree v₀` is a `GTree (𝔸.π₁ v₀)` constructed directly from
`𝔸`-paths starting at `v₀`:

* Its vertices (`GraphOfGroups.bassSerreVertex`) are equivalence classes `p A_v` of `𝔸`-paths `p`
  from `v₀` to `v`, modulo homotopy and right multiplication by `A_v`.
* Its darts (`GraphOfGroups.bassSerreDart`) are equivalence classes of pairs `(p, e)` of an
  `𝔸`-path `p` from `v₀` to `v` and an arrow `e : v ⟶ v'` of `Γ`, modulo right multiplication of
  `p` by `α_e(A_e)`, with source `p A_v`, reversal `(p e, rev e)`, and target `(p e) A_{v'}`.
* The fundamental group `π₁(𝔸, v₀)` acts on the left by path concatenation without inversions.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre `GTree (𝔸.π₁ v₀)` of `𝔸` at `v₀`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreBase`,
  `TauCeti.GraphOfGroups.bassSerreDart`: constructors for vertices, the base vertex, and darts,
  with projections `bassSerreVertexProj`, `bassSerreDartProj` and eliminators
  `bassSerreVertexLift`, `bassSerreDartLift`.
* `TauCeti.GraphOfGroups.bassSerreOutDartEquiv`, `TauCeti.GraphOfGroups.bassSerreStarEquiv`:
  outgoing darts at `p A_v` above `e` as `A_v / α_e(A_e)`, and the full outgoing star at `p A_v`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `𝔸.bassSerreTree v₀` is a tree.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreVertex`,
  `TauCeti.GraphOfGroups.isEllipticSubgroup_range_vertexHom`: vertex stabilizers are `p A_v p⁻¹`.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreDart`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart_cons_vertex`,
  `TauCeti.GraphOfGroups.isRelative_bassSerreTree`: dart stabilizers are `p α_e(A_e) p⁻¹`.
* `TauCeti.GraphOfGroups.mk_src_eq_bassSerreTree`,
  `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree`: cardinal and finite vertex degrees.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti

open _root_.MulAction

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}}

/-! ### Internal carriers and setoids -/

/-- A representative of a vertex of the Bass–Serre tree: a target vertex in `Γ` together with an
`𝔸`-path from `v₀` to it. -/
private structure PreVertex (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) : Type (max u v w) where
  {vertex : Γ.V}
  path : 𝔸.Path ⟨v₀⟩ ⟨vertex⟩

/-- Two `𝔸`-paths from `v₀` represent the same Bass–Serre vertex when they end at the same vertex
`v` and differ on the right by an element of `A_v` up to homotopy. -/
private inductive VertexRel (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    PreVertex 𝔸 v₀ → PreVertex 𝔸 v₀ → Prop
  | intro {v : Γ.V} (p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v)
      (h : p.Homotopic (q.cons (Letter.vertex g))) : VertexRel 𝔸 v₀ ⟨p⟩ ⟨q⟩

private theorem VertexRel.equivalence {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    Equivalence (VertexRel 𝔸 v₀) where
  refl x := ⟨x.path, x.path, 1, (Path.Homotopic.one x.path).symm⟩
  symm := by
    rintro _ _ ⟨p, q, g, h⟩
    refine ⟨q, p, g⁻¹, (Path.Homotopic.one q).symm.trans ?_⟩
    rw [← mul_inv_cancel g]
    exact (Path.Homotopic.mul q g g⁻¹).symm.trans (h.symm.cons _)
  trans := by
    rintro _ _ _ ⟨p, q, g, h₁⟩ ⟨_, r, k, h₂⟩
    exact ⟨p, r, k * g, h₁.trans ((h₂.cons _).trans (Path.Homotopic.mul r k g))⟩

private instance vertexSetoid (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Setoid (PreVertex 𝔸 v₀) := ⟨VertexRel 𝔸 v₀, VertexRel.equivalence⟩

/-- A representative of a dart of the Bass–Serre tree: an arrow `e : v ⟶ v'` of `Γ` together with
an `𝔸`-path from `v₀` to `v`. -/
private structure PreDart (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) : Type (max u v w) where
  {src tgt : Γ.V}
  path : 𝔸.Path ⟨v₀⟩ ⟨src⟩
  dart : src ⟶ tgt

/-- Two pre-darts represent the same Bass–Serre dart when they carry the same arrow `e` and their
paths differ on the right by an element of `α_e(A_e)` up to homotopy. -/
private inductive DartRel (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    PreDart 𝔸 v₀ → PreDart 𝔸 v₀ → Prop
  | intro {v v' : Γ.V} (p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v')
      (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1))
      (h : p.Homotopic (q.cons (Letter.vertex (𝔸.αArrow e c)))) : DartRel 𝔸 v₀ ⟨p, e⟩ ⟨q, e⟩

private theorem DartRel.equivalence {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} :
    Equivalence (DartRel 𝔸 v₀) where
  refl x := ⟨x.path, x.path, x.dart, 1, by rw [map_one]; exact (Path.Homotopic.one x.path).symm⟩
  symm := by
    rintro _ _ ⟨p, q, e, c, h⟩
    refine ⟨q, p, e, c⁻¹, ?_⟩
    rw [map_inv]
    refine (Path.Homotopic.one q).symm.trans ?_
    rw [← mul_inv_cancel (𝔸.αArrow e c)]
    exact (Path.Homotopic.mul q _ _).symm.trans (h.symm.cons _)
  trans := by
    rintro _ _ _ ⟨p, q, e, c₁, h₁⟩ ⟨_, r, _, c₂, h₂⟩
    refine ⟨p, r, e, c₂ * c₁, ?_⟩
    rw [map_mul]
    exact h₁.trans ((h₂.cons _).trans (Path.Homotopic.mul r _ _))

private instance dartSetoid (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Setoid (PreDart 𝔸 v₀) := ⟨DartRel 𝔸 v₀, DartRel.equivalence⟩

private def preDartProj (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    Quotient (dartSetoid 𝔸 v₀) → Γ.E :=
  Quotient.lift (fun x => x.dart.1) fun _ _ ⟨_, _, _, _, _⟩ => rfl

/-- The underlying Serre graph of the Bass–Serre tree. -/
private def bassSerreGraph (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V) :
    SerreGraph.{max u v w, max u v w} where
  V := Quotient (vertexSetoid 𝔸 v₀)
  E := Quotient (dartSetoid 𝔸 v₀)
  src := Quotient.map (fun x => ⟨x.path⟩) fun _ _ ⟨p, q, e, c, h⟩ => ⟨p, q, 𝔸.αArrow e c, h⟩
  rev := Quotient.map (fun x => ⟨x.path.cons (Letter.dart x.dart), Quiver.reverse x.dart⟩) <| by
    rintro _ _ ⟨p, q, e, c, h⟩
    obtain ⟨c', hc', -⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e c
    exact ⟨_, _, _, c', hc' ▸ (h.cons _).trans (Path.Homotopic.dart_ωArrow q e c).symm⟩
  rev_rev := by
    rintro ⟨⟨p, e⟩⟩
    apply Quotient.sound
    have h : DartRel 𝔸 v₀
        ⟨(p.cons (Letter.dart e)).cons (Letter.dart (Quiver.reverse e)),
          Quiver.reverse (Quiver.reverse e)⟩ ⟨p, e⟩ := by
      rw [Quiver.reverse_reverse]
      exact ⟨_, p, e, 1, by
        rw [map_one]; exact (Path.Homotopic.dart_reverse p e).trans (Path.Homotopic.one p).symm⟩
    exact h
  rev_ne := fun d => Quotient.inductionOn d fun ⟨_, e⟩ h =>
    Γ.rev_ne e.1 (by simpa [preDartProj, Γ.reverse_val] using congrArg (preDartProj 𝔸 v₀) h)

/-! ### Connectedness and acyclicity -/

section TreeProof

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- Every vertex of `bassSerreGraph` is reachable by a path from the class of the empty path. -/
private theorem nonempty_path_bassSerreGraph :
    ∀ {y : 𝔸.LetterVertex} (p : 𝔸.Path ⟨v₀⟩ y),
      Nonempty ((bassSerreGraph 𝔸 v₀).Path
        (Quotient.mk (vertexSetoid 𝔸 v₀) ⟨Quiver.Path.nil⟩)
        (Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p⟩))
  | _, .nil => ⟨.nil⟩
  | _, .cons p (.vertex g) => by
    have heq : Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p.cons (Letter.vertex g)⟩ =
        Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p⟩ := Quotient.sound ⟨_, p, g, .refl _⟩
    exact heq ▸ nonempty_path_bassSerreGraph p
  | _, .cons p (.dart e) =>
    (nonempty_path_bassSerreGraph p).map fun q =>
      q.cons ⟨Quotient.mk (dartSetoid 𝔸 v₀) ⟨p, e⟩, rfl, rfl⟩

private theorem bassSerreGraph_connected : (bassSerreGraph 𝔸 v₀).Connected :=
  ((bassSerreGraph 𝔸 v₀).connected_iff).2
    ⟨⟨Quotient.mk (vertexSetoid 𝔸 v₀) ⟨Quiver.Path.nil⟩⟩,
      (bassSerreGraph 𝔸 v₀).preconnected_of_forall_nonempty_path
        (Quotient.mk (vertexSetoid 𝔸 v₀) ⟨Quiver.Path.nil⟩) fun x =>
          Quotient.inductionOn x fun ⟨p⟩ => nonempty_path_bassSerreGraph p⟩

/-- A dart of `bassSerreGraph` starting at the class of `p` has a representative extending `p` by a
vertex group element. -/
private theorem exists_preDart_of_src_eq {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    {d : (bassSerreGraph 𝔸 v₀).E}
    (hd : (bassSerreGraph 𝔸 v₀).src d = Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p⟩) :
    ∃ (b : Γ.V) (e : a ⟶ b) (g : 𝔸.vertexGroup a),
      d = Quotient.mk (dartSetoid 𝔸 v₀) ⟨p.cons (Letter.vertex g), e⟩ ∧
        (bassSerreGraph 𝔸 v₀).tgt d =
          Quotient.mk (vertexSetoid 𝔸 v₀) ⟨(p.cons (Letter.vertex g)).cons (Letter.dart e)⟩ := by
  obtain ⟨⟨q, e⟩, rfl⟩ := Quotient.mk_surjective d
  obtain ⟨q, p, g, hg⟩ := Quotient.exact hd
  have hdeq : Quotient.mk (dartSetoid 𝔸 v₀) ⟨q, e⟩ =
      Quotient.mk (dartSetoid 𝔸 v₀) ⟨p.cons (Letter.vertex g), e⟩ :=
    Quotient.sound ⟨q, p.cons (Letter.vertex g), e, 1, by
      rw [map_one]; exact hg.trans (Path.Homotopic.one _).symm⟩
  exact ⟨_, e, g, hdeq, by rw [hdeq]; rfl⟩

private theorem isReduced_cons_setLast {x y z : (bassSerreGraph 𝔸 v₀).V}
    {γ' : (bassSerreGraph 𝔸 v₀).Path x y} {f : y ⟶ z}
    (hγ : SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) (γ'.cons f))
    {a b b' : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨a⟩} {w : 𝔸.AlternatingPath a b}
    (hw_red : w.IsReduced) (hw_len : w.length = γ'.length)
    (hw_last : ∀ d ∈ (SerreGraph.Path.darts (bassSerreGraph 𝔸 v₀) γ').getLast?,
      ∃ (c : Γ.V) (w₀ : 𝔸.AlternatingPath a c) (e₀ : c ⟶ b),
        w = .cons w₀ e₀ 1 ∧
          (bassSerreGraph 𝔸 v₀).rev d =
            Quotient.mk (dartSetoid 𝔸 v₀) ⟨p.comp w.toPath, Quiver.reverse e₀⟩)
    (e : b ⟶ b') (g : 𝔸.vertexGroup b)
    (hf : f.1 = Quotient.mk (dartSetoid 𝔸 v₀) ⟨(p.comp w.toPath).cons (Letter.vertex g), e⟩) :
    (AlternatingPath.cons (w.setLast (w.last * g)) e 1).IsReduced := by
  let w' : 𝔸.AlternatingPath a b := w.setLast (w.last * g)
  refine (AlternatingPath.isReduced_cons_iff w' e 1).2
    ⟨(w.isReduced_setLast _).2 hw_red, fun hcanc => ?_⟩
  cases γ' with
  | nil =>
    have h0 : w'.length = 0 := by simp [w', hw_len]
    obtain rfl : a = b := w'.eq_of_length_zero h0
    rw [AlternatingPath.length_eq_zero_iff.1 h0] at hcanc
    exact AlternatingPath.not_cancels_single _ _ hcanc
  | cons γ'' f₀ =>
    have hne : f.1 ≠ (bassSerreGraph 𝔸 v₀).rev f₀.1 :=
      ((SerreGraph.Path.isReduced_cons_cons _ _ _ _).1 hγ).2
    obtain ⟨c, w₀, e₀, hw_eq, hrev₀⟩ := hw_last f₀.1 (by simp)
    have hcanc' : (AlternatingPath.cons w₀ e₀ g).Cancels e := by simpa [w', hw_eq] using hcanc
    obtain ⟨he₀, hg_mem⟩ := (AlternatingPath.cancels_cons_iff w₀ e₀ g e).1 hcanc'
    obtain ⟨c₀, hg_eq⟩ := MonoidHom.mem_range.1 hg_mem
    obtain rfl : c = b' := Γ.src_eq_tgt_of_val_eq_rev he₀
    obtain rfl : e₀ = Quiver.reverse e := Γ.eq_reverse_of_val_eq_rev he₀
    exact hne <| by
      rw [hf, hrev₀, Quiver.reverse_reverse, ← hg_eq]
      exact Quotient.sound ⟨_, _, _, c₀, .refl _⟩

/-- A reduced path in `bassSerreGraph` starting at the class of `p` spells a reduced alternating
`𝔸`-path of the same length. -/
private theorem exists_isReduced_alternatingPath {x y : (bassSerreGraph 𝔸 v₀).V}
    (γ : (bassSerreGraph 𝔸 v₀).Path x y)
    (hγ : SerreGraph.Path.IsReduced (bassSerreGraph 𝔸 v₀) γ)
    {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (hp : Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p⟩ = x) :
    ∃ (b : Γ.V) (w : 𝔸.AlternatingPath a b),
      w.IsReduced ∧ w.length = γ.length ∧
        Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p.comp w.toPath⟩ = y ∧
        ∀ d ∈ (SerreGraph.Path.darts (bassSerreGraph 𝔸 v₀) γ).getLast?,
          ∃ (c : Γ.V) (w₀ : 𝔸.AlternatingPath a c) (e₀ : c ⟶ b),
            w = .cons w₀ e₀ 1 ∧
              (bassSerreGraph 𝔸 v₀).rev d =
                Quotient.mk (dartSetoid 𝔸 v₀) ⟨p.comp w.toPath, Quiver.reverse e₀⟩ := by
  induction γ with
  | nil =>
    refine ⟨a, .single 1, AlternatingPath.isReduced_single 1, by simp, hp ▸ ?_, by simp⟩
    exact Quotient.sound
      ⟨_, p, 1, by rw [AlternatingPath.toPath_single, Path.comp_ofVertex]; exact .refl _⟩
  | @cons y z γ' f ih =>
    obtain ⟨b, w, hw_red, hw_len, hw_end, hw_last⟩ := ih (hγ.of_cons _)
    obtain ⟨b', e, g, hf, hz⟩ :=
      exists_preDart_of_src_eq (p.comp w.toPath) (f.2.1.trans hw_end.symm)
    let w' : 𝔸.AlternatingPath a b := w.setLast (w.last * g)
    let w₁ : 𝔸.AlternatingPath a b' := .cons w' e 1
    have hpw' : Path.Homotopic (p.comp w'.toPath) ((p.comp w.toPath).cons (Letter.vertex g)) :=
      (w.toPath_setLast_mul_homotopic g).comp_left p
    have hpw₁ : Path.Homotopic (p.comp w₁.toPath)
        (((p.comp w.toPath).cons (Letter.vertex g)).cons (Letter.dart e)) := by
      rw [AlternatingPath.toPath_cons, Quiver.Path.comp_cons, Quiver.Path.comp_cons]
      exact (Path.Homotopic.one ((p.comp w'.toPath).cons (Letter.dart e))).trans (hpw'.cons _)
    refine ⟨b', w₁, isReduced_cons_setLast hγ hw_red hw_len hw_last e g hf,
      by simp [w₁, w', hw_len], ?_, ?_⟩
    · rw [← f.2.2, hz]
      exact Quotient.sound ⟨_, _, 1, hpw₁.trans (Path.Homotopic.one _).symm⟩
    · intro d hd
      simp only [SerreGraph.Path.darts_cons, List.getLast?_concat, Option.mem_def,
        Option.some.injEq] at hd
      subst hd
      refine ⟨b, w', e, rfl, hf ▸ Quotient.sound ⟨_, _, _, 1, ?_⟩⟩
      rw [map_one]; exact hpw₁.symm.trans (Path.Homotopic.one _).symm

private theorem bassSerreGraph_isAcyclic : (bassSerreGraph 𝔸 v₀).IsAcyclic := by
  refine ((bassSerreGraph 𝔸 v₀).isAcyclic_iff).2 fun x γ hγ => ?_
  obtain ⟨⟨p⟩, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨b, w, hw_red, hw_len, hw_end, -⟩ := exists_isReduced_alternatingPath γ hγ p rfl
  obtain ⟨_, _, g, hg⟩ := Quotient.exact hw_end
  have hhom : w.toPath.Homotopic (Path.ofVertex g) :=
    Path.Homotopic.of_comp_left p (by simpa [Path.comp_ofVertex] using hg)
  have hlen : w.length ≤ 0 := by simpa using hw_red.length_le_length_edgePath_of_homotopic hhom
  exact Quiver.Path.eq_nil_of_length_zero _ (Nat.eq_zero_of_le_zero (hw_len ▸ hlen))

private theorem bassSerreGraph_isTree : (bassSerreGraph 𝔸 v₀).IsTree :=
  ((bassSerreGraph 𝔸 v₀).isTree_iff).2 ⟨bassSerreGraph_connected, bassSerreGraph_isAcyclic⟩

end TreeProof

/-! ### Left action of `π₁(𝔸, v₀)` -/

section Action

variable (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

private def smulPreVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (bassSerreGraph 𝔸 v₀).V → (bassSerreGraph 𝔸 v₀).V :=
  Quotient.map (fun x => ⟨s.comp x.path⟩) fun _ _ ⟨p, q, g, h⟩ =>
    ⟨s.comp p, s.comp q, g, h.comp_left s⟩

private def smulPreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (bassSerreGraph 𝔸 v₀).E → (bassSerreGraph 𝔸 v₀).E :=
  Quotient.map (fun x => ⟨s.comp x.path, x.dart⟩) fun _ _ ⟨p, q, e, c, h⟩ =>
    ⟨s.comp p, s.comp q, e, c, h.comp_left s⟩

private theorem smulPreVertex_congr {s t : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩} (h : s.Homotopic t)
    (x : (bassSerreGraph 𝔸 v₀).V) : smulPreVertex 𝔸 v₀ s x = smulPreVertex 𝔸 v₀ t x :=
  Quotient.inductionOn x fun ⟨p⟩ =>
    Quotient.sound ⟨s.comp p, t.comp p, 1, (h.comp_right p).trans (Path.Homotopic.one _).symm⟩

private theorem smulPreDart_congr {s t : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩} (h : s.Homotopic t)
    (d : (bassSerreGraph 𝔸 v₀).E) : smulPreDart 𝔸 v₀ s d = smulPreDart 𝔸 v₀ t d :=
  Quotient.inductionOn d fun ⟨p, e⟩ =>
    Quotient.sound ⟨s.comp p, t.comp p, e, 1, by
      rw [map_one]; exact (h.comp_right p).trans (Path.Homotopic.one _).symm⟩

private theorem smulPreVertex_comp (s t : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (x : (bassSerreGraph 𝔸 v₀).V) :
    smulPreVertex 𝔸 v₀ (s.comp t) x = smulPreVertex 𝔸 v₀ s (smulPreVertex 𝔸 v₀ t x) :=
  Quotient.inductionOn x fun ⟨_⟩ =>
    congrArg (Quotient.mk (vertexSetoid 𝔸 v₀)) (by simp [Quiver.Path.comp_assoc])

private theorem smulPreDart_comp (s t : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (d : (bassSerreGraph 𝔸 v₀).E) :
    smulPreDart 𝔸 v₀ (s.comp t) d = smulPreDart 𝔸 v₀ s (smulPreDart 𝔸 v₀ t d) :=
  Quotient.inductionOn d fun ⟨_, _⟩ =>
    congrArg (Quotient.mk (dartSetoid 𝔸 v₀)) (by simp [Quiver.Path.comp_assoc])

private theorem smulPreVertex_nil (x : (bassSerreGraph 𝔸 v₀).V) :
    smulPreVertex 𝔸 v₀ Quiver.Path.nil x = x :=
  Quotient.inductionOn x fun ⟨_⟩ => congrArg (Quotient.mk (vertexSetoid 𝔸 v₀)) (by simp)

private theorem smulPreDart_nil (d : (bassSerreGraph 𝔸 v₀).E) :
    smulPreDart 𝔸 v₀ Quiver.Path.nil d = d :=
  Quotient.inductionOn d fun ⟨_, _⟩ => congrArg (Quotient.mk (dartSetoid 𝔸 v₀)) (by simp)

private def autOfClosedPath (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) : (bassSerreGraph 𝔸 v₀).Aut where
  equivV :=
    { toFun := smulPreVertex 𝔸 v₀ s
      invFun := smulPreVertex 𝔸 v₀ s.reverse
      left_inv x := by
        rw [← smulPreVertex_comp,
          smulPreVertex_congr 𝔸 v₀ (Path.Homotopic.reverse_comp s), smulPreVertex_nil]
      right_inv x := by
        rw [← smulPreVertex_comp,
          smulPreVertex_congr 𝔸 v₀ (Path.Homotopic.comp_reverse s), smulPreVertex_nil] }
  equivE :=
    { toFun := smulPreDart 𝔸 v₀ s
      invFun := smulPreDart 𝔸 v₀ s.reverse
      left_inv d := by
        rw [← smulPreDart_comp,
          smulPreDart_congr 𝔸 v₀ (Path.Homotopic.reverse_comp s), smulPreDart_nil]
      right_inv d := by
        rw [← smulPreDart_comp,
          smulPreDart_congr 𝔸 v₀ (Path.Homotopic.comp_reverse s), smulPreDart_nil] }
  map_src d := Quotient.inductionOn d fun ⟨_, _⟩ => rfl
  map_rev d := Quotient.inductionOn d fun ⟨_, _⟩ => rfl

private def bassSerreAction : 𝔸.π₁ v₀ →* (bassSerreGraph 𝔸 v₀).Aut where
  toFun := π₁.lift (autOfClosedPath 𝔸 v₀) fun _ _ h =>
    SerreGraph.Iso.ext (smulPreVertex_congr 𝔸 v₀ h) (smulPreDart_congr 𝔸 v₀ h)
  map_one' := by
    rw [← π₁.mk_nil, π₁.lift_mk]
    exact SerreGraph.Iso.ext
      (fun v => by simpa [autOfClosedPath] using smulPreVertex_nil 𝔸 v₀ v)
      (fun d => by simpa [autOfClosedPath] using smulPreDart_nil 𝔸 v₀ d)
  map_mul' g h := π₁.induction_on g fun s => π₁.induction_on h fun t => by
    rw [← π₁.mk_comp, π₁.lift_mk, π₁.lift_mk, π₁.lift_mk]
    exact SerreGraph.Iso.ext
      (fun v => by simpa [autOfClosedPath] using smulPreVertex_comp 𝔸 v₀ s t v)
      (fun d => by simpa [autOfClosedPath] using smulPreDart_comp 𝔸 v₀ s t d)

@[simp] private theorem bassSerreAction_mk_equivV (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (x : (bassSerreGraph 𝔸 v₀).V) :
    (bassSerreAction 𝔸 v₀ (π₁.mk s)).equivV x = smulPreVertex 𝔸 v₀ s x := by
  simp [bassSerreAction, autOfClosedPath]

@[simp] private theorem bassSerreAction_mk_equivE (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (d : (bassSerreGraph 𝔸 v₀).E) :
    (bassSerreAction 𝔸 v₀ (π₁.mk s)).equivE d = smulPreDart 𝔸 v₀ s d := by
  simp [bassSerreAction, autOfClosedPath]

private theorem bassSerreAction_smul_ne_rev (g : 𝔸.π₁ v₀) (d : (bassSerreGraph 𝔸 v₀).E) :
    bassSerreAction 𝔸 v₀ g • d ≠ (bassSerreGraph 𝔸 v₀).rev d := by
  induction g using π₁.induction_on with | h s
  rw [SerreGraph.Aut.smul_dart_def, bassSerreAction_mk_equivE]
  exact Quotient.inductionOn d fun x heq => Γ.rev_ne x.dart.1 <| by
    simpa [smulPreDart, bassSerreGraph, preDartProj, Γ.reverse_val]
      using (congrArg (preDartProj 𝔸 v₀) heq).symm

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`, as a
`GTree` for the fundamental group `π₁(𝔸, v₀)`. -/
def bassSerreTree : GTree.{max u v w, max u v w} (𝔸.π₁ v₀) where
  toSerreGraph := bassSerreGraph 𝔸 v₀
  isTree := bassSerreGraph_isTree
  action := bassSerreAction 𝔸 v₀
  action_smul_ne_rev := bassSerreAction_smul_ne_rev 𝔸 v₀

/-- The Bass–Serre graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree : (𝔸.bassSerreTree v₀).IsTree := (𝔸.bassSerreTree v₀).isTree

end Action

/-! ### Constructors, projections, and action rules -/

section API

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- The vertex `p A_v` of the Bass–Serre tree represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (𝔸.bassSerreTree v₀).V :=
  Quotient.mk (vertexSetoid 𝔸 v₀) ⟨p⟩

variable (𝔸 v₀) in
/-- The base vertex `1 · A_{v₀}` of the Bass–Serre tree, represented by the empty path at `v₀`. -/
def bassSerreBase : (𝔸.bassSerreTree v₀).V :=
  bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)

/-- The dart `(p, e) α_e(A_e)` of the Bass–Serre tree represented by an `𝔸`-path `p` from `v₀` to
`v` and an arrow `e : v ⟶ v'` of `Γ`. -/
def bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') : (𝔸.bassSerreTree v₀).E :=
  Quotient.mk (dartSetoid 𝔸 v₀) ⟨p, e⟩

/-- The vertex of `Γ` underlying a vertex of the Bass–Serre tree. -/
def bassSerreVertexProj : (𝔸.bassSerreTree v₀).V → Γ.V :=
  Quotient.lift (fun x => x.vertex) fun _ _ ⟨_, _, _, _⟩ => rfl

/-- The dart of `Γ` underlying a dart of the Bass–Serre tree. -/
def bassSerreDartProj : (𝔸.bassSerreTree v₀).E → Γ.E := preDartProj 𝔸 v₀

/-- A function on `𝔸`-paths from `v₀` that is invariant under homotopy and right multiplication
by vertex group elements descends to the vertices of the Bass–Serre tree. -/
def bassSerreVertexLift {β : Sort*} (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (h_hom : ∀ {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f p = f q)
    (h_vertex : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      f (p.cons (Letter.vertex g)) = f p) :
    (𝔸.bassSerreTree v₀).V → β :=
  Quotient.lift (fun x => f x.path) fun _ _ ⟨_, q, g, h⟩ => (h_hom h).trans (h_vertex q g)

/-- A function on pairs `(p, e)` of an `𝔸`-path from `v₀` to `v` and an arrow `e : v ⟶ v'` that
is invariant under homotopy of `p` and right multiplication by `α_e(A_e)` descends to the darts
of the Bass–Serre tree. -/
def bassSerreDartLift {β : Sort*} (f : ∀ {v v' : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → (v ⟶ v') → β)
    (h_hom : ∀ {v v' : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (e : v ⟶ v'),
      p.Homotopic q → f p e = f q e)
    (h_αArrow : ∀ {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v')
      (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)),
      f (p.cons (Letter.vertex (𝔸.αArrow e c))) e = f p e) :
    (𝔸.bassSerreTree v₀).E → β :=
  Quotient.lift (fun x => f x.path x.dart) fun _ _ ⟨_, q, e, c, h⟩ =>
    (h_hom e h).trans (h_αArrow q e c)

@[simp] theorem bassSerreVertexLift_bassSerreVertex {β : Sort*}
    (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (h_hom : ∀ {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f p = f q)
    (h_vertex : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      f (p.cons (Letter.vertex g)) = f p)
    {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    bassSerreVertexLift f h_hom h_vertex (bassSerreVertex p) = f p := (rfl)

@[simp] theorem bassSerreVertexLift_bassSerreBase {β : Sort*}
    (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (h_hom : ∀ {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f p = f q)
    (h_vertex : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v),
      f (p.cons (Letter.vertex g)) = f p) :
    bassSerreVertexLift f h_hom h_vertex (𝔸.bassSerreBase v₀) =
      f (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) := (rfl)

@[simp] theorem bassSerreDartLift_bassSerreDart {β : Sort*}
    (f : ∀ {v v' : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → (v ⟶ v') → β)
    (h_hom : ∀ {v v' : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (e : v ⟶ v'),
      p.Homotopic q → f p e = f q e)
    (h_αArrow : ∀ {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v')
      (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)),
      f (p.cons (Letter.vertex (𝔸.αArrow e c))) e = f p e)
    {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    bassSerreDartLift f h_hom h_αArrow (bassSerreDart p e) = f p e := (rfl)

/-- Eliminate a property on the vertices of the Bass–Serre tree by checking it on `𝔸`-paths from
`v₀`. -/
@[elab_as_elim] theorem bassSerreVertex_induction_on {P : (𝔸.bassSerreTree v₀).V → Prop}
    (x : (𝔸.bassSerreTree v₀).V)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (bassSerreVertex p)) : P x :=
  Quotient.inductionOn x fun ⟨p⟩ => h p

/-- Eliminate a property on the darts of the Bass–Serre tree by checking it on pairs `(p, e)`. -/
@[elab_as_elim] theorem bassSerreDart_induction_on {P : (𝔸.bassSerreTree v₀).E → Prop}
    (d : (𝔸.bassSerreTree v₀).E)
    (h : ∀ {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v'), P (bassSerreDart p e)) : P d :=
  Quotient.inductionOn d fun ⟨p, e⟩ => h p e

@[simp] theorem bassSerreVertex_nil :
    bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) = 𝔸.bassSerreBase v₀ := (rfl)

@[simp] theorem bassSerreVertexProj_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    bassSerreVertexProj (bassSerreVertex p) = v := (rfl)

@[simp] theorem bassSerreVertexProj_bassSerreBase :
    bassSerreVertexProj (𝔸.bassSerreBase v₀) = v₀ := (rfl)

@[simp] theorem bassSerreDartProj_bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    bassSerreDartProj (bassSerreDart p e) = e.1 := (rfl)

@[simp] theorem src_bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    (𝔸.bassSerreTree v₀).src (bassSerreDart p e) = bassSerreVertex p := (rfl)

@[simp] theorem rev_bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    (𝔸.bassSerreTree v₀).rev (bassSerreDart p e) =
      bassSerreDart (p.cons (Letter.dart e)) (Quiver.reverse e) := (rfl)

@[simp] theorem tgt_bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    (𝔸.bassSerreTree v₀).tgt (bassSerreDart p e) = bassSerreVertex (p.cons (Letter.dart e)) := (rfl)

@[simp] theorem src_bassSerreDartProj (d : (𝔸.bassSerreTree v₀).E) :
    Γ.src (bassSerreDartProj d) = bassSerreVertexProj ((𝔸.bassSerreTree v₀).src d) :=
  bassSerreDart_induction_on d fun _ e => e.2.1

@[simp] theorem bassSerreDartProj_rev (d : (𝔸.bassSerreTree v₀).E) :
    bassSerreDartProj ((𝔸.bassSerreTree v₀).rev d) = Γ.rev (bassSerreDartProj d) :=
  bassSerreDart_induction_on d fun _ e => Γ.reverse_val e

@[simp] theorem tgt_bassSerreDartProj (d : (𝔸.bassSerreTree v₀).E) :
    Γ.tgt (bassSerreDartProj d) = bassSerreVertexProj ((𝔸.bassSerreTree v₀).tgt d) :=
  bassSerreDart_induction_on d fun _ e => e.2.2

/-- Two `𝔸`-paths ending at `v` represent the same vertex of `X(𝔸, v₀)` if and only if they differ
on the right by an element of `A_v` up to homotopy. -/
theorem bassSerreVertex_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    bassSerreVertex p = bassSerreVertex q ↔
      ∃ g : 𝔸.vertexGroup v, p.Homotopic (q.cons (Letter.vertex g)) :=
  Quotient.eq.trans ⟨fun ⟨_, _, g, h⟩ => ⟨g, h⟩, fun ⟨g, h⟩ => ⟨p, q, g, h⟩⟩

/-- Two pairs `(p, e)` and `(q, e)` with the same arrow `e` represent the same dart of `X(𝔸, v₀)`
if and only if `p` and `q` differ on the right by an element of `α_e(A_e)` up to homotopy. -/
theorem bassSerreDart_eq_iff {v v' : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} {e : v ⟶ v'} :
    bassSerreDart p e = bassSerreDart q e ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e.1),
        p.Homotopic (q.cons (Letter.vertex (𝔸.αArrow e c))) :=
  Quotient.eq.trans ⟨fun ⟨_, _, _, c, h⟩ => ⟨c, h⟩, fun ⟨c, h⟩ => ⟨p, q, e, c, h⟩⟩

/-- Homotopic `𝔸`-paths represent the same vertex of `X(𝔸, v₀)`. -/
theorem bassSerreVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    bassSerreVertex p = bassSerreVertex q :=
  bassSerreVertex_eq_iff.2 ⟨1, h.trans (Path.Homotopic.one q).symm⟩

/-- Homotopic `𝔸`-paths with the same arrow represent the same dart of `X(𝔸, v₀)`. -/
theorem bassSerreDart_congr {v v' : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q)
    (e : v ⟶ v') : bassSerreDart p e = bassSerreDart q e :=
  bassSerreDart_eq_iff.2 ⟨1, by rw [map_one]; exact h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem bassSerreVertex_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (g : 𝔸.vertexGroup v) :
    bassSerreVertex (p.cons (Letter.vertex g)) = bassSerreVertex p :=
  bassSerreVertex_eq_iff.2 ⟨g, .refl _⟩

/-- Composing a path on the right with a single vertex-group element leaves the represented
Bass–Serre vertex unchanged. -/
theorem bassSerreVertex_comp_ofVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (g : 𝔸.vertexGroup v) :
    bassSerreVertex (p.comp (Path.ofVertex g)) = bassSerreVertex p := by
  rw [Path.comp_ofVertex, bassSerreVertex_cons_vertex]

@[simp] theorem bassSerreVertex_ofVertex (g : 𝔸.vertexGroup v₀) :
    bassSerreVertex (Path.ofVertex g) = 𝔸.bassSerreBase v₀ := by
  simp [Path.ofVertex_eq_nil_cons]

@[simp] theorem bassSerreDart_cons_αArrow {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v')
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    bassSerreDart (p.cons (Letter.vertex (𝔸.αArrow e c))) e = bassSerreDart p e :=
  bassSerreDart_eq_iff.2 ⟨c, .refl _⟩

@[simp] theorem bassSerreDart_cons_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart (p.cons (Letter.vertex (𝔸.α e c))) (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) =
      bassSerreDart p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) := by
  simpa only [𝔸.αArrow_mk] using bassSerreDart_cons_αArrow p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) c

@[simp] theorem bassSerreDart_ofVertex_αArrow {v' : Γ.V} (e : v₀ ⟶ v')
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    bassSerreDart (Path.ofVertex (𝔸.αArrow e c)) e = bassSerreDart Quiver.Path.nil e := by
  rw [Path.ofVertex_eq_nil_cons, bassSerreDart_cons_αArrow]

@[simp] theorem bassSerreDart_ofVertex_α (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart (Path.ofVertex (𝔸.α e c)) (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) =
      bassSerreDart Quiver.Path.nil (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) := by
  simpa only [𝔸.αArrow_mk] using bassSerreDart_ofVertex_αArrow (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) c

/-- When `𝔸.vertexGroup v₀` is nontrivial, `bassSerreVertex` descended to homotopy classes of
closed `𝔸`-paths at `v₀` is not injective. -/
theorem not_injective_lift_bassSerreVertex [Nontrivial (𝔸.vertexGroup v₀)] :
    ¬ Function.Injective
      (Quotient.lift (bassSerreVertex (𝔸 := 𝔸) (v₀ := v₀) (v := v₀))
        fun _ _ => bassSerreVertex_congr) := by
  obtain ⟨g, hg⟩ := exists_ne (1 : 𝔸.vertexGroup v₀)
  intro hinj
  have h : Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex g) =
      Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil := hinj (bassSerreVertex_ofVertex g)
  exact hg (Path.ofVertex_homotopic_nil_iff.1 (Quotient.exact h))

/-- Left action of `π₁(𝔸, v₀)` on vertices of the Bass–Serre tree: concatenation on the left. -/
@[simp] theorem mk_smul_bassSerreVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • bassSerreVertex p = bassSerreVertex (s.comp p) := by
  rw [GTree.smul_vertex_def]; exact bassSerreAction_mk_equivV 𝔸 v₀ s _

@[simp] theorem mk_smul_bassSerreBase (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    π₁.mk s • 𝔸.bassSerreBase v₀ = bassSerreVertex s := by
  rw [bassSerreBase, mk_smul_bassSerreVertex, Quiver.Path.comp_nil]

/-- Left action of `π₁(𝔸, v₀)` on darts of the Bass–Serre tree: concatenation on the left. -/
@[simp] theorem mk_smul_bassSerreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v v' : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    π₁.mk s • bassSerreDart p e = bassSerreDart (s.comp p) e := by
  rw [GTree.smul_dart_def]; exact bassSerreAction_mk_equivE 𝔸 v₀ s _

@[simp] theorem bassSerreVertexProj_smul (g : 𝔸.π₁ v₀) (x : (𝔸.bassSerreTree v₀).V) :
    bassSerreVertexProj (g • x) = bassSerreVertexProj x :=
  π₁.induction_on g fun _ => bassSerreVertex_induction_on x fun _ => by
    rw [mk_smul_bassSerreVertex]; rfl

@[simp] theorem bassSerreDartProj_smul (g : 𝔸.π₁ v₀) (d : (𝔸.bassSerreTree v₀).E) :
    bassSerreDartProj (g • d) = bassSerreDartProj d :=
  π₁.induction_on g fun _ => bassSerreDart_induction_on d fun _ _ => by
    rw [mk_smul_bassSerreDart]; rfl

end API

/-! ### Vertex and dart stabilizers -/

section Stabilizers

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- Conjugating an element of `A_v` along `p` fixes the vertex `p A_v`. -/
@[simp] theorem vertexHom_smul_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) : π₁.vertexHom p a • bassSerreVertex p = bassSerreVertex p := by
  rw [π₁.vertexHom_apply, mk_smul_bassSerreVertex]
  refine (bassSerreVertex_congr ?_).trans (bassSerreVertex_comp_ofVertex p a)
  exact Path.Homotopic.comp_reverse_comp_comp (p.comp (Path.ofVertex a)) p .nil

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` of the Bass–Serre tree is `p A_v p⁻¹`,
the range of `π₁.vertexHom p`. -/
@[simp] theorem stabilizer_bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    stabilizer (𝔸.π₁ v₀) (bassSerreVertex p) = (π₁.vertexHom p).range := by
  ext g; refine ⟨fun hg => ?_,
    fun ⟨a, ha⟩ => ha ▸ mem_stabilizer_iff.2 (vertexHom_smul_bassSerreVertex p a)⟩
  induction g using π₁.induction_on with | h s
  rw [mem_stabilizer_iff, mk_smul_bassSerreVertex, bassSerreVertex_eq_iff] at hg
  obtain ⟨a, ha⟩ := hg
  rw [← Path.comp_ofVertex] at ha
  exact ⟨a, by
    rw [π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
    exact (ha.comp_right p.reverse).symm.trans (Path.Homotopic.comp_comp_reverse s p)⟩

/-- The stabilizer of the base vertex `1 · A_{v₀}` is the image of `A_{v₀}` at the basepoint. -/
@[simp] theorem stabilizer_bassSerreBase :
    stabilizer (𝔸.π₁ v₀) (𝔸.bassSerreBase v₀) =
      (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  stabilizer_bassSerreVertex _

/-- Every vertex stabilizer of `X(𝔸, v₀)` is the image of a vertex group along an `𝔸`-path from
`v₀`. -/
theorem exists_stabilizer_bassSerreTree_vertex_eq (x : (𝔸.bassSerreTree v₀).V) :
    ∃ (v : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), stabilizer (𝔸.π₁ v₀) x = (π₁.vertexHom p).range :=
  bassSerreVertex_induction_on x fun p => ⟨_, p, stabilizer_bassSerreVertex p⟩

/-- Every embedded vertex group `p A_v p⁻¹` is an elliptic subgroup for the action on the
Bass–Serre tree. -/
theorem isEllipticSubgroup_range_vertexHom {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  GTree.isEllipticSubgroup_iff.2 ⟨bassSerreVertex p, (stabilizer_bassSerreVertex p).ge⟩

/-- Conjugating an edge group image `α_e(c)` along `p` fixes the dart `(p, e)`. -/
@[simp] theorem vertexHom_αArrow_smul_bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : v ⟶ v') (c : 𝔸.edgeGroup (Γ.toGeomEdge e.1)) :
    π₁.vertexHom p (𝔸.αArrow e c) • bassSerreDart p e = bassSerreDart p e := by
  rw [π₁.vertexHom_apply, mk_smul_bassSerreDart]
  refine (bassSerreDart_congr ?_ e).trans (bassSerreDart_cons_αArrow p e c)
  rw [← Path.comp_ofVertex]
  exact Path.Homotopic.comp_reverse_comp_comp (p.comp (Path.ofVertex (𝔸.αArrow e c))) p .nil

@[simp] theorem vertexHom_α_smul_bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    π₁.vertexHom p (𝔸.α e c) • bassSerreDart p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) =
      bassSerreDart p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) := by
  simpa only [𝔸.αArrow_mk] using
    vertexHom_αArrow_smul_bassSerreDart p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) c

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart `(p, e)` of the Bass–Serre tree is `p α_e(A_e) p⁻¹`,
the range of `(π₁.vertexHom p).comp (𝔸.αArrow e)`. -/
@[simp] theorem stabilizer_bassSerreDart {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    stabilizer (𝔸.π₁ v₀) (bassSerreDart p e) = ((π₁.vertexHom p).comp (𝔸.αArrow e)).range := by
  ext g
  refine ⟨fun hg => ?_,
    fun ⟨c, hc⟩ => hc ▸ mem_stabilizer_iff.2 (vertexHom_αArrow_smul_bassSerreDart p e c)⟩
  induction g using π₁.induction_on with | h s
  rw [mem_stabilizer_iff, mk_smul_bassSerreDart, bassSerreDart_eq_iff] at hg
  obtain ⟨c, hc⟩ := hg
  rw [← Path.comp_ofVertex] at hc
  exact ⟨c, by
    rw [MonoidHom.comp_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
    exact (hc.comp_right p.reverse).symm.trans (Path.Homotopic.comp_comp_reverse s p)⟩

/-- The stabilizer of the dart `(p a, e)` joining `p A_v` to `p a e A_{v'}` is the conjugate
`p a α_e(A_e) a⁻¹ p⁻¹`. -/
theorem stabilizer_bassSerreDart_cons_vertex {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) (e : v ⟶ v') :
    stabilizer (𝔸.π₁ v₀) (bassSerreDart (p.cons (Letter.vertex a)) e) =
      (((𝔸.αArrow e).range).map (MulAut.conj a : 𝔸.vertexGroup v →* 𝔸.vertexGroup v)).map
        (π₁.vertexHom p) := by
  rw [stabilizer_bassSerreDart, π₁.vertexHom_cons_vertex, MonoidHom.comp_assoc,
    MonoidHom.range_comp, MonoidHom.range_comp]

/-- Every dart stabilizer of `X(𝔸, v₀)` is a conjugate of an edge group image along an `𝔸`-path
from `v₀`. -/
theorem exists_stabilizer_bassSerreTree_dart_eq (d : (𝔸.bassSerreTree v₀).E) :
    ∃ (v v' : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v'),
      stabilizer (𝔸.π₁ v₀) d = ((π₁.vertexHom p).comp (𝔸.αArrow e)).range :=
  bassSerreDart_induction_on d fun p e => ⟨_, _, p, e, stabilizer_bassSerreDart p e⟩

/-- The Bass–Serre tree is relative to families `(𝒜, ℋ)` whenever `𝒜` contains all edge group
images along `𝔸`-paths from `v₀` and every subgroup in `ℋ` is elliptic. -/
theorem isRelative_bassSerreTree {𝒜 ℋ : Set (Subgroup (𝔸.π₁ v₀))}
    (h𝒜 : ∀ {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v'),
      ((π₁.vertexHom p).comp (𝔸.αArrow e)).range ∈ 𝒜)
    (hℋ : ∀ H ∈ ℋ, (𝔸.bassSerreTree v₀).IsEllipticSubgroup H) :
    (𝔸.bassSerreTree v₀).IsRelative 𝒜 ℋ :=
  GTree.isRelative_iff.2 ⟨fun d => bassSerreDart_induction_on d fun p e => by
    rw [stabilizer_bassSerreDart]; exact h𝒜 p e, hℋ⟩

/-- When the vertex group at `bassSerreVertexProj x` is trivial, the vertex `x` has trivial
stabilizer in `π₁(𝔸, v₀)`. -/
@[simp] theorem stabilizer_bassSerreTree_vertex_eq_bot (x : (𝔸.bassSerreTree v₀).V)
    [Subsingleton (𝔸.vertexGroup (bassSerreVertexProj x))] :
    stabilizer (𝔸.π₁ v₀) x = ⊥ := by
  have h := @bassSerreVertex_induction_on _ _ _
    (fun x => ∀ [Subsingleton (𝔸.vertexGroup (bassSerreVertexProj x))],
      stabilizer (𝔸.π₁ v₀) x = ⊥) x fun p => by
    rw [bassSerreVertexProj_bassSerreVertex]; intro; rw [stabilizer_bassSerreVertex]
    exact (π₁.vertexHom p).range_eq_bot_iff.mpr (Subsingleton.elim _ _)
  exact h

/-- When the edge group of `bassSerreDartProj d` is trivial, the dart `d` has trivial stabilizer
in `π₁(𝔸, v₀)`. -/
@[simp] theorem stabilizer_bassSerreTree_dart_eq_bot (d : (𝔸.bassSerreTree v₀).E)
    [Subsingleton (𝔸.edgeGroup (Γ.toGeomEdge (bassSerreDartProj d)))] :
    stabilizer (𝔸.π₁ v₀) d = ⊥ := by
  have h := @bassSerreDart_induction_on _ _ _
    (fun d => ∀ [Subsingleton (𝔸.edgeGroup (Γ.toGeomEdge (bassSerreDartProj d)))],
      stabilizer (𝔸.π₁ v₀) d = ⊥) d fun p e => by
    rw [bassSerreDartProj_bassSerreDart]; intro; rw [stabilizer_bassSerreDart]
    exact ((π₁.vertexHom p).comp (𝔸.αArrow e)).range_eq_bot_iff.mpr (Subsingleton.elim _ _)
  exact h

end Stabilizers

/-! ### Outgoing stars and vertex degrees -/

section Star

variable {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- Outgoing darts of `X(𝔸, v₀)` at `p A_v` lifting a fixed arrow `e : v ⟶ v'` correspond to left
cosets `A_v / α_e(A_e)`, via `g α_e(A_e) ↦ (p g, e)`. -/
noncomputable def bassSerreOutDartEquiv {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v') :
    𝔸.vertexGroup v ⧸ (𝔸.αArrow e).range ≃
      {d : (𝔸.bassSerreTree v₀).E //
        (𝔸.bassSerreTree v₀).src d = bassSerreVertex p ∧ bassSerreDartProj d = e.1} := by
  refine Equiv.ofBijective
    (Quotient.lift
      (fun g : 𝔸.vertexGroup v =>
        ⟨bassSerreDart (p.cons (Letter.vertex g)) e, bassSerreVertex_cons_vertex p g, rfl⟩)
      fun g₁ g₂ h => by
        obtain ⟨c, hc⟩ : g₁⁻¹ * g₂ ∈ (𝔸.αArrow e).range := QuotientGroup.leftRel_apply.1 h
        apply Subtype.ext
        rw [eq_mul_of_inv_mul_eq hc.symm]
        exact (bassSerreDart_eq_iff.2 ⟨c, (Path.Homotopic.mul p g₁ _).symm⟩).symm)
    ⟨fun x₁ x₂ h => ?_, fun ⟨d, hsrc, hproj⟩ => ?_⟩
  · induction x₁ using QuotientGroup.induction_on with | H g₁
    induction x₂ using QuotientGroup.induction_on with | H g₂
    obtain ⟨c, hc⟩ := bassSerreDart_eq_iff.1 (congrArg Subtype.val h)
    have hhom : (Path.ofVertex g₁).Homotopic (Path.ofVertex (g₂ * 𝔸.αArrow e c)) := by
      refine Path.Homotopic.of_comp_left p ?_
      rw [Path.comp_ofVertex, Path.comp_ofVertex]
      exact hc.trans (Path.Homotopic.mul p g₂ _)
    have hg : g₁ = g₂ * 𝔸.αArrow e c := Path.ofVertex_homotopic_ofVertex_iff.1 hhom
    exact (QuotientGroup.eq.2 (MonoidHom.mem_range.2 ⟨c, by rw [hg, inv_mul_cancel_left]⟩)).symm
  · obtain ⟨w, e', g, rfl, -⟩ := exists_preDart_of_src_eq p hsrc
    have he' : e'.1 = e.1 := hproj
    have hw : w = v' := e'.2.2.symm.trans ((congrArg Γ.tgt he').trans e.2.2)
    subst hw
    obtain rfl : e = e' := (Subtype.ext he').symm
    exact ⟨(g : 𝔸.vertexGroup v ⧸ (𝔸.αArrow e).range), rfl⟩

@[simp] theorem bassSerreOutDartEquiv_mk_val {v v' : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e : v ⟶ v')
    (g : 𝔸.vertexGroup v) :
    (bassSerreOutDartEquiv p e (g : 𝔸.vertexGroup v ⧸ (𝔸.αArrow e).range)).1 =
      bassSerreDart (p.cons (Letter.vertex g)) e := (rfl)

/-- The outgoing star of `p A_v` in `X(𝔸, v₀)` decomposes over the darts of `Γ` starting at `v`
into the coset spaces `A_v / α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v},
      𝔸.vertexGroup v ⧸ (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1)).range) ≃
      {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = bassSerreVertex p} :=
  Equiv.trans
    (Equiv.sigmaCongrRight fun e : {e : Γ.E // Γ.src e = v} =>
      Equiv.trans
        (bassSerreOutDartEquiv p (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1))
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun d : (𝔸.bassSerreTree v₀).E => (𝔸.bassSerreTree v₀).src d = bassSerreVertex p)
          (fun d : (𝔸.bassSerreTree v₀).E => bassSerreDartProj d = e.1)).symm)
    (Equiv.sigmaSubtypeFiberEquiv
      (α := {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = bassSerreVertex p})
      (β := Γ.E) (fun d => bassSerreDartProj d.1) (fun e => Γ.src e = v)
      fun d => (src_bassSerreDartProj d.1).trans
        ((congrArg bassSerreVertexProj d.2).trans (bassSerreVertexProj_bassSerreVertex p)))

@[simp] theorem bassSerreStarEquiv_mk_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (g : 𝔸.vertexGroup v) :
    (bassSerreStarEquiv p ⟨e, (g : 𝔸.vertexGroup v ⧸ _)⟩).1 =
      bassSerreDart (p.cons (Letter.vertex g)) (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1) :=
  bassSerreOutDartEquiv_mk_val p (⟨e.1, e.2, rfl⟩ : v ⟶ Γ.tgt e.1) g

/-- Cardinality of the outgoing star of a vertex `x` in `X(𝔸, v₀)` with underlying vertex
`v = bassSerreVertexProj x`, as the sum of the coset cardinals `#(A_v / α_e(A_e))` over outgoing
darts `e` at `v`. -/
theorem mk_src_eq_bassSerreTree (x : (𝔸.bassSerreTree v₀).V) :
    Cardinal.mk {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = x} =
      Cardinal.lift.{u} (Cardinal.sum
        fun e : {e : Γ.E // Γ.src e = bassSerreVertexProj x} =>
          Cardinal.mk (𝔸.vertexGroup (bassSerreVertexProj x) ⧸
            (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : bassSerreVertexProj x ⟶ Γ.tgt e.1)).range)) := by
  induction x using bassSerreVertex_induction_on with | h p
  rw [← Cardinal.mk_sigma, ← Cardinal.mk_uLift]
  exact Cardinal.mk_congr ((bassSerreStarEquiv p).symm.trans Equiv.ulift.symm)

/-- When `v = bassSerreVertexProj x` has finitely many outgoing darts in `Γ` and each edge group
image at `v` has finite index in `A_v`, the degree of `x` in `X(𝔸, v₀)` is the sum of the
subgroup indices `[A_v : α_e(A_e)]`. -/
theorem card_src_eq_bassSerreTree (x : (𝔸.bassSerreTree v₀).V)
    [Fintype {e : Γ.E // Γ.src e = bassSerreVertexProj x}]
    [∀ e : {e : Γ.E // Γ.src e = bassSerreVertexProj x},
      Finite (𝔸.vertexGroup (bassSerreVertexProj x) ⧸
        (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : bassSerreVertexProj x ⟶ Γ.tgt e.1)).range)] :
    Nat.card {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = x} =
      ∑ e : {e : Γ.E // Γ.src e = bassSerreVertexProj x},
        (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : bassSerreVertexProj x ⟶ Γ.tgt e.1)).range.index := by
  have h := @bassSerreVertex_induction_on _ _ _
    (fun x =>
      ∀ [Fintype {e : Γ.E // Γ.src e = bassSerreVertexProj x}]
        [∀ e : {e : Γ.E // Γ.src e = bassSerreVertexProj x},
          Finite (𝔸.vertexGroup (bassSerreVertexProj x) ⧸
            (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : bassSerreVertexProj x ⟶ Γ.tgt e.1)).range)],
        Nat.card {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = x} =
          ∑ e : {e : Γ.E // Γ.src e = bassSerreVertexProj x},
            (𝔸.αArrow (⟨e.1, e.2, rfl⟩ : bassSerreVertexProj x ⟶ Γ.tgt e.1)).range.index)
    x fun p => by
      rw [bassSerreVertexProj_bassSerreVertex]; intro _ _
      rw [Nat.card_congr (bassSerreStarEquiv p).symm, Nat.card_sigma]
      simp_rw [Subgroup.index_eq_card]
  exact h

end Star

end GraphOfGroups

end TauCeti
