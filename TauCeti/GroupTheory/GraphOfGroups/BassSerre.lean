/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.Combinatorics.Graph.Serre.Quotient
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# The Bass–Serre tree of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ` with base vertex `v₀`. Following Kapovich,
Weidmann and Myasnikov (Definition 2.5) and Serre (Chapter I, §5.3), the Bass–Serre covering tree
`X(𝔸, v₀)` is constructed from `𝔸`-paths starting at `v₀`:

* Its vertices (`GraphOfGroups.BassSerreVertex`) are the equivalence classes `p A_v` of pairs
  `(v, p)` where `p` is an `𝔸`-path from `v₀` to `v`, with `(v, p) ≈ (v, q)` when `p` is homotopic
  to `q · a` for some `a ∈ A_v`.
* Its darts (`GraphOfGroups.BassSerreDart`) are the equivalence classes `[e, p]` of pairs `(e, p)`
  where `e` is a dart of `Γ` and `p` is an `𝔸`-path from `v₀` to `src e`, with `(e, p) ≈ (e, q)`
  when `p` is homotopic to `q · α_e(c)` for some `c ∈ A_e`. For `a ∈ A_v` and a dart `e` from `v`
  to `v'`, the dart `[e, p · a]` has source `p A_v`, reversal `[rev e, p · a · e]`, and target
  `(p a e) A_{v'}`.

The fundamental group `π₁(𝔸, v₀)` acts on `X(𝔸, v₀)` on the left by concatenating closed `𝔸`-paths
at `v₀`. Because the type projection `X(𝔸, v₀) → Γ` sending `p A_v` to `v` and `[e, p]` to `e` is
invariant under this action, no element inverts a dart. Connectedness of `X(𝔸, v₀)` follows by
induction on `𝔸`-paths from the base vertex `1 · A_{v₀}`, while acyclicity follows from Britton's
lemma (`AlternatingPath.IsReduced.not_homotopic_ofVertex_cons`): a nonempty reduced closed path in
`X(𝔸, v₀)` lifts to a reduced closed alternating `𝔸`-path containing at least one dart and homotopic
to a single vertex group letter, which is impossible. Bundling the graph, tree proof, and action
gives `GraphOfGroups.bassSerreTree` as a `GTree (π₁ 𝔸 v₀)`.

From the path model of `X(𝔸, v₀)` we read off the fundamental invariants of Bass–Serre theory:

* **Vertex stabilizers** (`GraphOfGroups.stabilizer_vertex`): the stabilizer of `p A_v` in
  `π₁(𝔸, v₀)` is `(π₁.vertexHom p).range = p A_v p⁻¹`, isomorphic to `A_v` via
  `GraphOfGroups.vertexStabilizerEquiv`.
* **Edge stabilizers** (`GraphOfGroups.stabilizer_edge`): the stabilizer of `[e, p]` is
  `((𝔸.α e).range).map (π₁.vertexHom p) = p α_e(A_e) p⁻¹`, isomorphic to `A_e` via
  `GraphOfGroups.edgeStabilizerEquiv`; for `[e, p · a]` from `p A_v` to `(p a e) A_{v'}` this is
  `p a α_e(A_e) a⁻¹ p⁻¹`.
* **Quotient graph** (`GraphOfGroups.bassSerreQuotientIso`): the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)`
  is isomorphic to the connected component `Γ.component v₀`, and hence to `Γ` itself when `Γ` is
  preconnected (`GraphOfGroups.bassSerreQuotientIsoOfPreconnected`).
* **Local star and neighbours** (`GraphOfGroups.bassSerreStarEquiv`,
  `GraphOfGroups.bassSerreAdjacentEquiv`): the darts issuing from `p A_v` and its adjacent vertices
  `(p a e) A_{tgt e}` are in canonical bijection with
  `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ α_e(A_e)`.

We verify the construction on edgeless graphs (`GraphOfGroups.bassSerreTree_point`), free products
including `ℤ ∗ ℤ` (`GraphOfGroups.bassSerreTree_free_product`), Baumslag–Solitar groups `BS(m, n)`
and `BS(1, 2)` (`GraphOfGroups.bassSerreTree_BS12`), unquotiented homotopy classes of based
`𝔸`-paths (`GraphOfGroups.bassSerreTree_not_quotient_paths`), and disconnected graphs
(`GraphOfGroups.bassSerreTree_two_isolated`).

## Main definitions

* `TauCeti.GraphOfGroups.BassSerreVertex`, `TauCeti.GraphOfGroups.BassSerreDart`: vertex and dart
  types of the Bass–Serre tree.
* `TauCeti.GraphOfGroups.bassSerreGraph`: the underlying `SerreGraph` of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTree`: `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreBaseVertex`,
  `TauCeti.GraphOfGroups.bassSerreDart`: path constructors for vertices and darts of
  `𝔸.bassSerreTree v₀`.
* `TauCeti.GraphOfGroups.vertexStabilizerEquiv`, `TauCeti.GraphOfGroups.edgeStabilizerEquiv`:
  isomorphisms of `A_v` and `A_e` with the corresponding vertex and dart stabilizers.
* `TauCeti.GraphOfGroups.bassSerreQuotientIso`,
  `TauCeti.GraphOfGroups.bassSerreQuotientIsoOfPreconnected`: isomorphisms of the quotient graph
  with `Γ.component v₀` and (when `Γ` is preconnected) with `Γ`.
* `TauCeti.GraphOfGroups.bassSerreStarEquiv`, `TauCeti.GraphOfGroups.bassSerreAdjacentEquiv`:
  canonical bijections identifying the star and neighbours of `p A_v`.
* `TauCeti.GraphOfGroups.freeProductGraph`, `TauCeti.GraphOfGroups.baumslagSolitar`: graphs of
  groups of free products `A ∗ B` and Baumslag–Solitar groups `BS(m, n)`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `X(𝔸, v₀)` is a tree.
* `TauCeti.GraphOfGroups.stabilizer_vertex`, `TauCeti.GraphOfGroups.stabilizer_edge`: explicit
  vertex and dart stabilizers.
* `TauCeti.GraphOfGroups.card_bassSerreStar`: vertex degree equals `∑_{src e = v} [A_v : α_e(A_e)]`.
* `TauCeti.GraphOfGroups.bassSerreTree_point`, `TauCeti.GraphOfGroups.bassSerreTree_free_product`,
  `TauCeti.GraphOfGroups.bassSerreTree_BS12`,
  `TauCeti.GraphOfGroups.bassSerreTree_not_quotient_paths`,
  `TauCeti.GraphOfGroups.bassSerreTree_two_isolated`: structural checks and examples.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5, pp. 6–7.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-! ### Vertices and darts of the Bass–Serre graph -/

/-- Two `𝔸`-paths starting at `v₀` represent the same vertex `p A_v` of `X(𝔸, v₀)` when they end
at the same vertex `v` of `Γ` and differ on the right by an element of `A_v` up to homotopy. -/
def vertexRel (x y : Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) : Prop :=
  ∃ (h : x.1 = y.1) (a : 𝔸.vertexGroup y.1),
    Path.Homotopic (h ▸ x.2) (y.2.cons (Letter.vertex a))

private theorem vertexRel_equivalence : Equivalence (𝔸.vertexRel v₀) where
  refl x := ⟨rfl, 1, (Path.Homotopic.one x.2).symm⟩
  symm := by
    rintro ⟨v, p⟩ ⟨w, q⟩ ⟨h, a, ha⟩
    cases h
    dsimp only at ha
    refine ⟨rfl, a⁻¹, (Path.Homotopic.one q).symm.trans ?_⟩
    rw [← mul_inv_cancel a]
    exact (Path.Homotopic.mul q a a⁻¹).symm.trans (ha.cons (Letter.vertex a⁻¹)).symm
  trans := by
    rintro ⟨v, p⟩ ⟨w, q⟩ ⟨u, r⟩ ⟨h₁, a, ha⟩ ⟨h₂, b, hb⟩
    dsimp only at h₁ h₂ ha hb
    subst h₁ h₂
    exact ⟨rfl, b * a, ha.trans ((hb.cons (Letter.vertex a)).trans (Path.Homotopic.mul r b a))⟩

/-- The right-coset setoid on `𝔸`-paths from `v₀` defining the vertices of `X(𝔸, v₀)`. -/
def vertexSetoid : Setoid (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  ⟨𝔸.vertexRel v₀, 𝔸.vertexRel_equivalence v₀⟩

/-- The vertex type of the Bass–Serre tree `X(𝔸, v₀)`: equivalence classes `p A_v` of `𝔸`-paths `p`
starting at `v₀`. -/
def BassSerreVertex : Type (max u v w) :=
  Quotient (𝔸.vertexSetoid v₀)

/-- Path constructor for `BassSerreVertex`. -/
def BassSerreVertex.mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : 𝔸.BassSerreVertex v₀ :=
  Quotient.mk (𝔸.vertexSetoid v₀) ⟨v, p⟩

instance : Inhabited (𝔸.BassSerreVertex v₀) :=
  ⟨BassSerreVertex.mk 𝔸 v₀ .nil⟩

section RawVertexAPI

variable {𝔸 v₀}

/-- Prove a property of `BassSerreVertex` by checking it on `𝔸`-paths from `v₀`. -/
@[elab_as_elim] theorem BassSerreVertex.induction_on {P : 𝔸.BassSerreVertex v₀ → Prop}
    (u : 𝔸.BassSerreVertex v₀)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (BassSerreVertex.mk 𝔸 v₀ p)) : P u :=
  Quotient.ind (fun ⟨_, p⟩ => h p) u

theorem BassSerreVertex.mk_eq_mk_iff_exists {v w : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨w⟩} :
    BassSerreVertex.mk 𝔸 v₀ p = BassSerreVertex.mk 𝔸 v₀ q ↔
      ∃ (h : v = w) (a : 𝔸.vertexGroup w), Path.Homotopic (h ▸ p) (q.cons (Letter.vertex a)) :=
  Quotient.eq (r := 𝔸.vertexSetoid v₀)

theorem BassSerreVertex.mk_eq_mk_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    BassSerreVertex.mk 𝔸 v₀ p = BassSerreVertex.mk 𝔸 v₀ q ↔
      ∃ a : 𝔸.vertexGroup v, Path.Homotopic p (q.cons (Letter.vertex a)) :=
  BassSerreVertex.mk_eq_mk_iff_exists.trans
    ⟨fun ⟨h, a, ha⟩ => ⟨a, by rwa [Subsingleton.elim h rfl] at ha⟩, fun ⟨a, ha⟩ => ⟨rfl, a, ha⟩⟩

theorem BassSerreVertex.mk_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    BassSerreVertex.mk 𝔸 v₀ p = BassSerreVertex.mk 𝔸 v₀ q :=
  BassSerreVertex.mk_eq_mk_iff.mpr ⟨1, h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem BassSerreVertex.mk_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    BassSerreVertex.mk 𝔸 v₀ (p.cons (Letter.vertex a)) = BassSerreVertex.mk 𝔸 v₀ p :=
  BassSerreVertex.mk_eq_mk_iff.mpr ⟨a, .refl _⟩

end RawVertexAPI

/-- Two pairs `(e, p)` and `(e', q)` represent the same dart of `X(𝔸, v₀)` when `e = e'` and `p`
and `q` differ on the right by an element of `α_e(A_e)` up to homotopy. -/
def dartRel (x y : Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : Prop :=
  ∃ (h : x.1 = y.1) (c : 𝔸.edgeGroup (Γ.toGeomEdge y.1)),
    Path.Homotopic (h ▸ x.2) (y.2.cons (Letter.vertex (𝔸.α y.1 c)))

private theorem dartRel_equivalence : Equivalence (𝔸.dartRel v₀) where
  refl x := ⟨rfl, 1, by rw [map_one]; exact (Path.Homotopic.one x.2).symm⟩
  symm := by
    rintro ⟨e, p⟩ ⟨e', q⟩ ⟨h, c, hc⟩
    cases h
    dsimp only at hc
    refine ⟨rfl, c⁻¹, (Path.Homotopic.one q).symm.trans ?_⟩
    rw [← map_one (𝔸.α e), ← mul_inv_cancel c, map_mul]
    exact (Path.Homotopic.mul q (𝔸.α e c) (𝔸.α e c⁻¹)).symm.trans
      (hc.cons (Letter.vertex (𝔸.α e c⁻¹))).symm
  trans := by
    rintro ⟨e, p⟩ ⟨e₁, q⟩ ⟨e₂, r⟩ ⟨h₁, c₁, hc₁⟩ ⟨h₂, c₂, hc₂⟩
    dsimp only at h₁ h₂ hc₁ hc₂
    subst h₁ h₂
    refine ⟨rfl, c₂ * c₁, hc₁.trans ((hc₂.cons _).trans ?_)⟩
    rw [map_mul]
    exact Path.Homotopic.mul r (𝔸.α e c₂) (𝔸.α e c₁)

/-- The right-coset setoid on `(e, p)` defining the darts of `X(𝔸, v₀)`. -/
def dartSetoid : Setoid (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :=
  ⟨𝔸.dartRel v₀, 𝔸.dartRel_equivalence v₀⟩

/-- The dart type of the Bass–Serre tree `X(𝔸, v₀)`: equivalence classes `[e, p]` of a dart `e` of
`Γ` and an `𝔸`-path `p` from `v₀` to `src e`, modulo right multiplication by `α_e(A_e)`. -/
def BassSerreDart : Type (max u v w) :=
  Quotient (𝔸.dartSetoid v₀)

/-- Path constructor for `BassSerreDart`. -/
def BassSerreDart.mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : 𝔸.BassSerreDart v₀ :=
  Quotient.mk (𝔸.dartSetoid v₀) ⟨e, p⟩

section RawDartAPI

variable {𝔸 v₀}

/-- Prove a property of `BassSerreDart` by checking it on pairs `(e, p)`. -/
@[elab_as_elim] theorem BassSerreDart.induction_on {P : 𝔸.BassSerreDart v₀ → Prop}
    (d : 𝔸.BassSerreDart v₀)
    (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (BassSerreDart.mk 𝔸 v₀ e p)) : P d :=
  Quotient.ind (fun ⟨e, p⟩ => h e p) d

theorem BassSerreDart.mk_eq_mk_iff_exists {e e' : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e'⟩} :
    BassSerreDart.mk 𝔸 v₀ e p = BassSerreDart.mk 𝔸 v₀ e' q ↔
      ∃ (h : e = e') (c : 𝔸.edgeGroup (Γ.toGeomEdge e')),
        Path.Homotopic (h ▸ p) (q.cons (Letter.vertex (𝔸.α e' c))) :=
  Quotient.eq (r := 𝔸.dartSetoid v₀)

theorem BassSerreDart.mk_eq_mk_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    BassSerreDart.mk 𝔸 v₀ e p = BassSerreDart.mk 𝔸 v₀ e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e),
        Path.Homotopic p (q.cons (Letter.vertex (𝔸.α e c))) :=
  BassSerreDart.mk_eq_mk_iff_exists.trans
    ⟨fun ⟨h, c, hc⟩ => ⟨c, by rwa [Subsingleton.elim h rfl] at hc⟩, fun ⟨c, hc⟩ => ⟨rfl, c, hc⟩⟩

theorem BassSerreDart.mk_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    BassSerreDart.mk 𝔸 v₀ e p = BassSerreDart.mk 𝔸 v₀ e q :=
  BassSerreDart.mk_eq_mk_iff.mpr ⟨1, by rw [map_one]; exact h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem BassSerreDart.mk_cons_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    BassSerreDart.mk 𝔸 v₀ e (p.cons (Letter.vertex (𝔸.α e c))) = BassSerreDart.mk 𝔸 v₀ e p :=
  BassSerreDart.mk_eq_mk_iff.mpr ⟨c, .refl _⟩

end RawDartAPI

/-- Source vertex `p A_{src e}` of a Bass–Serre dart `[e, p]`. -/
def BassSerreDart.src : 𝔸.BassSerreDart v₀ → 𝔸.BassSerreVertex v₀ :=
  Quotient.lift (fun x => BassSerreVertex.mk 𝔸 v₀ x.2) <| by
    rintro ⟨e, p⟩ ⟨e', q⟩ ⟨h, c, hc⟩
    dsimp only at h hc
    subst h
    exact BassSerreVertex.mk_eq_mk_iff.mpr ⟨𝔸.α e c, hc⟩

/-- Reversed Bass–Serre dart `[rev e, p · e]`. -/
def BassSerreDart.rev : 𝔸.BassSerreDart v₀ → 𝔸.BassSerreDart v₀ :=
  Quotient.lift
    (fun x => BassSerreDart.mk 𝔸 v₀ (Γ.rev x.1) (x.2.cons (Letter.dart (Γ.dart x.1)))) <| by
    rintro ⟨e, p⟩ ⟨e', q⟩ ⟨h, c, hc⟩
    dsimp only at h hc
    subst h
    refine BassSerreDart.mk_eq_mk_iff.mpr
      ⟨(MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c, ?_⟩
    rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
    exact (hc.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.dart_ω e c q).symm

private theorem bassSerreRev_aux {e' e : Γ.E} (he : Γ.rev e' = e) (q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e'⟩) :
    BassSerreDart.mk 𝔸 v₀ (Γ.rev e') (q.cons (Letter.dart (Γ.dart e'))) =
      BassSerreDart.mk 𝔸 v₀ e (q.cons (Letter.dart ⟨e', rfl, by rw [Γ.tgt_def, he]⟩)) := by
  subst he
  rw [Γ.dart_def]
  rfl

theorem BassSerreDart.rev_rev (d : 𝔸.BassSerreDart v₀) :
    BassSerreDart.rev 𝔸 v₀ (BassSerreDart.rev 𝔸 v₀ d) = d :=
  BassSerreDart.induction_on d fun e p => by
    refine (𝔸.bassSerreRev_aux v₀ (Γ.rev_rev e) (p.cons (Letter.dart (Γ.dart e)))).trans ?_
    have hdart : (⟨Γ.rev e, rfl, by rw [Γ.tgt_def, Γ.rev_rev e]⟩ : Γ.tgt e ⟶ Γ.src e) =
        Quiver.reverse (Γ.dart e) :=
      @SerreGraph.eq_reverse_of_val_eq_rev Γ _ _
        ⟨Γ.rev e, rfl, by rw [Γ.tgt_def, Γ.rev_rev e]⟩ (Γ.dart e) (by simp)
    exact (congrArg (fun f : Γ.tgt e ⟶ Γ.src e =>
      BassSerreDart.mk 𝔸 v₀ e ((p.cons (Letter.dart (Γ.dart e))).cons (Letter.dart f))) hdart).trans
      (BassSerreDart.mk_congr (Path.Homotopic.dart_reverse p (Γ.dart e)))

theorem BassSerreDart.rev_ne (d : 𝔸.BassSerreDart v₀) : BassSerreDart.rev 𝔸 v₀ d ≠ d :=
  BassSerreDart.induction_on d fun e p h => by
    obtain ⟨he, -, -⟩ := BassSerreDart.mk_eq_mk_iff_exists.mp h
    exact Γ.rev_ne e he

/-- The underlying Serre graph of the Bass–Serre tree `X(𝔸, v₀)`. -/
@[expose] def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := 𝔸.BassSerreVertex v₀
  E := 𝔸.BassSerreDart v₀
  src := BassSerreDart.src 𝔸 v₀
  rev := BassSerreDart.rev 𝔸 v₀
  rev_rev := BassSerreDart.rev_rev 𝔸 v₀
  rev_ne := BassSerreDart.rev_ne 𝔸 v₀

@[simp] theorem bassSerreGraph_src_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).src (BassSerreDart.mk 𝔸 v₀ e p) = BassSerreVertex.mk 𝔸 v₀ p :=
  (rfl)

@[simp] theorem bassSerreGraph_rev_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).rev (BassSerreDart.mk 𝔸 v₀ e p) =
      BassSerreDart.mk 𝔸 v₀ (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem bassSerreGraph_tgt_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).tgt (BassSerreDart.mk 𝔸 v₀ e p) =
      BassSerreVertex.mk 𝔸 v₀ (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

/-! ### Type projection to `Γ` and to `Γ.component v₀` -/

/-- The projection morphism from `X(𝔸, v₀)` to `Γ`, sending `p A_v` to `v` and `[e, p]` to `e`. -/
def bassSerreTypeHom : (𝔸.bassSerreGraph v₀).Hom Γ where
  mapV := Quotient.lift Sigma.fst fun _ _ ⟨h, _, _⟩ => h
  mapE := Quotient.lift Sigma.fst fun _ _ ⟨h, _, _⟩ => h
  map_src := fun d => BassSerreDart.induction_on d fun _ _ => rfl
  map_rev := fun d => BassSerreDart.induction_on d fun _ _ => rfl

@[simp] theorem bassSerreTypeHom_mapV_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTypeHom v₀).mapV (BassSerreVertex.mk 𝔸 v₀ p) = v :=
  (rfl)

@[simp] theorem bassSerreTypeHom_mapE_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTypeHom v₀).mapE (BassSerreDart.mk 𝔸 v₀ e p) = e :=
  (rfl)

/-- Every `𝔸`-path from `v₀` ends in `Γ.component v₀`, so the type projection factors through
`Γ.component v₀`. -/
def bassSerreComponentHom : (𝔸.bassSerreGraph v₀).Hom (Γ.component v₀) where
  mapV := Quotient.lift (fun x => ⟨x.1, (Γ.mem_componentVertices_iff v₀ x.1).mpr ⟨x.2.edgePath⟩⟩)
    fun _ _ ⟨h, _, _⟩ => Subtype.ext h
  mapE := Quotient.lift (fun x => ⟨x.1, (Γ.mem_componentDarts_iff v₀ x.1).mpr ⟨x.2.edgePath⟩⟩)
    fun _ _ ⟨h, _, _⟩ => Subtype.ext h
  map_src := fun d => BassSerreDart.induction_on d fun _ _ => rfl
  map_rev := fun d => BassSerreDart.induction_on d fun _ _ => rfl

@[simp] theorem bassSerreComponentHom_mapV_mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ((𝔸.bassSerreComponentHom v₀).mapV (BassSerreVertex.mk 𝔸 v₀ p)).1 = v :=
  (rfl)

@[simp] theorem bassSerreComponentHom_mapE_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ((𝔸.bassSerreComponentHom v₀).mapE (BassSerreDart.mk 𝔸 v₀ e p)).1 = e :=
  (rfl)

@[simp] theorem componentInclusion_comp_bassSerreComponentHom :
    (Γ.componentInclusion v₀).comp (𝔸.bassSerreComponentHom v₀) = 𝔸.bassSerreTypeHom v₀ := by
  ext d
  · rw [SerreGraph.Hom.comp_mapV]
    exact BassSerreVertex.induction_on d fun _ => rfl
  · rw [SerreGraph.Hom.comp_mapE]
    exact BassSerreDart.induction_on d fun _ _ => rfl

/-! ### Connectedness and acyclicity of `X(𝔸, v₀)` -/

/-- Every vertex of `X(𝔸, v₀)` is reachable from the base vertex `1 · A_{v₀}`. -/
theorem bassSerreGraph_reachable (u : (𝔸.bassSerreGraph v₀).V) :
    Nonempty ((𝔸.bassSerreGraph v₀).Path
      (BassSerreVertex.mk 𝔸 v₀ (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) u) := by
  refine BassSerreVertex.induction_on u fun {v} p => ?_
  have aux : ∀ {y : 𝔸.LetterVertex} (q : 𝔸.Path ⟨v₀⟩ y),
      Nonempty ((𝔸.bassSerreGraph v₀).Path
        (BassSerreVertex.mk 𝔸 v₀ (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩))
        (BassSerreVertex.mk 𝔸 v₀ (v := y.as) q)) := by
    intro y q
    induction q with
    | nil => exact ⟨.nil⟩
    | @cons y₁ y₂ q l ih =>
      cases y₁ with | mk w₁ =>
      cases y₂ with | mk w₂ =>
      cases l with
      | vertex a => simpa only [BassSerreVertex.mk_cons_vertex] using ih
      | dart f =>
        rcases f with ⟨e, rfl, rfl⟩
        exact ih.map fun P => P.cons
          ⟨BassSerreDart.mk 𝔸 v₀ e q, rfl, by rw [← Γ.dart_def]; rfl⟩
  exact aux p

/-- `X(𝔸, v₀)` is preconnected. -/
theorem bassSerreGraph_preconnected : (𝔸.bassSerreGraph v₀).Preconnected :=
  (𝔸.bassSerreGraph v₀).preconnected_of_forall_nonempty_path
    (BassSerreVertex.mk 𝔸 v₀ (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) (𝔸.bassSerreGraph_reachable v₀)

/-- `X(𝔸, v₀)` is connected. -/
theorem bassSerreGraph_connected : (𝔸.bassSerreGraph v₀).Connected :=
  ((𝔸.bassSerreGraph v₀).connected_iff).mpr
    ⟨⟨BassSerreVertex.mk 𝔸 v₀ (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)⟩, 𝔸.bassSerreGraph_preconnected v₀⟩

private theorem cons_dart_eq_arrow {v₁ : Γ.V} {e₀ : Γ.E} (q₀ : 𝔸.AlternatingPath v₁ (Γ.src e₀))
    {c : Γ.V} (hc : Γ.tgt e₀ = c) (p₁ : 𝔸.Path ⟨v₀⟩ ⟨v₁⟩) (p₀ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₀⟩)
    (hq₀ : (AlternatingPath.cons q₀ (Γ.dart e₀) 1).IsReduced)
    (hp₀ : Path.Homotopic (p₀.cons (Letter.dart (Γ.dart e₀)))
      (p₁.comp (AlternatingPath.cons q₀ (Γ.dart e₀) 1).toPath))
    (p_e : 𝔸.Path ⟨v₀⟩ ⟨c⟩)
    (hmid : BassSerreVertex.mk 𝔸 v₀ p_e =
      BassSerreVertex.mk 𝔸 v₀ (p₀.cons (Letter.dart (Γ.dart e₀)))) :
    ∃ g : 𝔸.vertexGroup c,
      (AlternatingPath.cons q₀ ⟨e₀, rfl, hc⟩ g).IsReduced ∧
        Path.Homotopic p_e ((p₁.comp (AlternatingPath.cons q₀ ⟨e₀, rfl, hc⟩ g).toPath)) ∧
        Path.Homotopic p_e ((p₀.cons (Letter.dart ⟨e₀, rfl, hc⟩)).cons (Letter.vertex g)) := by
  subst hc
  rw [← Γ.dart_def]
  obtain ⟨g, hg⟩ := BassSerreVertex.mk_eq_mk_iff.mp hmid
  have hqg_red : (AlternatingPath.cons q₀ (Γ.dart e₀) g).IsReduced := by
    simpa only [AlternatingPath.setLast_cons] using
      (AlternatingPath.isReduced_setLast (AlternatingPath.cons q₀ (Γ.dart e₀) 1) g).mpr hq₀
  refine ⟨g, hqg_red, ?_, hg⟩
  have hmul := (AlternatingPath.cons q₀ (Γ.dart e₀) 1).toPath_setLast_mul_homotopic g
  simp only [AlternatingPath.last_cons, one_mul, AlternatingPath.setLast_cons] at hmul
  exact hg.trans <| (hp₀.cons (Letter.vertex g)).trans <|
    (Quiver.Path.comp_cons p₁ (AlternatingPath.cons q₀ (Γ.dart e₀) 1).toPath (Letter.vertex g)) ▸
      hmul.symm.comp_left p₁

/-- Lifting a nonempty reduced path in `X(𝔸, v₀)` to a reduced alternating `𝔸`-path containing at
least one dart. -/
private theorem lift_isReduced_cons :
    ∀ {u₁ u_mid : (𝔸.bassSerreGraph v₀).V} (P₀ : (𝔸.bassSerreGraph v₀).Path u₁ u_mid)
      {u₂ : (𝔸.bassSerreGraph v₀).V} (E : u_mid ⟶ u₂),
      SerreGraph.Path.IsReduced (𝔸.bassSerreGraph v₀) (P₀.cons E) →
      ∀ {v₁ : Γ.V} (p₁ : 𝔸.Path ⟨v₀⟩ ⟨v₁⟩), u₁ = BassSerreVertex.mk 𝔸 v₀ p₁ →
      ∀ (e : Γ.E) (p_e : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), E.1 = BassSerreDart.mk 𝔸 v₀ e p_e →
      ∃ q : 𝔸.AlternatingPath v₁ (Γ.src e),
        (AlternatingPath.cons q (Γ.dart e) 1).IsReduced ∧
          Path.Homotopic (p_e.cons (Letter.dart (Γ.dart e)))
            (p₁.comp (AlternatingPath.cons q (Γ.dart e) 1).toPath)
  | _, _, .nil, _, E, _, _, p₁, hu₁, e, p_e, hE => by
    have hsrc : BassSerreVertex.mk 𝔸 v₀ p_e = BassSerreVertex.mk 𝔸 v₀ p₁ := by
      rw [← hu₁, ← E.2.1, hE, bassSerreGraph_src_mk]
    obtain ⟨rfl, g₀, hg₀⟩ := BassSerreVertex.mk_eq_mk_iff_exists.mp hsrc
    refine ⟨.single g₀, by simp, ?_⟩
    rw [AlternatingPath.toPath_cons, AlternatingPath.toPath_single, Path.ofVertex_eq_nil_cons]
    simp only [Quiver.Path.comp_cons, Quiver.Path.comp_nil]
    exact (hg₀.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.one _).symm
  | _, _, .cons P₁ E₀, _, E, hp, _, p₁, hu₁, e, p_e, hE => by
    obtain ⟨hp₀, hne⟩ := (SerreGraph.Path.isReduced_cons_cons _ P₁ E₀ E).mp hp
    refine BassSerreDart.induction_on (P := fun d => E₀.1 = d → _) E₀.1 (fun e₀ p₀ hE₀ => ?_) rfl
    obtain ⟨q₀, hq₀, hpath₀⟩ := lift_isReduced_cons P₁ E₀ hp₀ p₁ hu₁ e₀ p₀ hE₀
    have hmid : BassSerreVertex.mk 𝔸 v₀ p_e =
        BassSerreVertex.mk 𝔸 v₀ (p₀.cons (Letter.dart (Γ.dart e₀))) := by
      rw [← bassSerreGraph_src_mk, ← hE, E.2.1, ← E₀.2.2, hE₀, bassSerreGraph_tgt_mk]
    have hmidV : Γ.tgt e₀ = Γ.src e :=
      (BassSerreVertex.mk_eq_mk_iff_exists.mp hmid).choose.symm
    obtain ⟨g, hqg_red, hpe_comp, hpe_p₀⟩ :=
      cons_dart_eq_arrow 𝔸 v₀ q₀ hmidV p₁ p₀ hq₀ hpath₀ p_e hmid
    refine ⟨.cons q₀ ⟨e₀, rfl, hmidV⟩ g,
      (AlternatingPath.isReduced_cons_iff _ _ _).mpr ⟨hqg_red, fun hcanc => hne ?_⟩, ?_⟩
    · obtain ⟨he_rev, c, hc⟩ :=
        (AlternatingPath.cancels_cons_iff q₀ ⟨e₀, rfl, hmidV⟩ g (Γ.dart e)).mp hcanc
      have he_eq : e = Γ.rev e₀ := by
        simpa only [Γ.dart_val, Γ.rev_rev] using congrArg Γ.rev he_rev.symm
      subst he_eq
      obtain ⟨c', hc'⟩ : g ∈ (𝔸.α (Γ.rev e₀)).range :=
        (𝔸.range_αArrow_dart (Γ.rev e₀)) ▸ ⟨c, hc⟩
      have hdart_eq : (⟨e₀, rfl, hmidV⟩ : Γ.src e₀ ⟶ Γ.src (Γ.rev e₀)) = Γ.dart e₀ :=
        Subtype.ext (Γ.dart_val e₀).symm
      rw [hE, hE₀, bassSerreGraph_rev_mk]
      refine BassSerreDart.mk_eq_mk_iff.mpr ⟨c', ?_⟩
      rwa [hdart_eq, ← hc'] at hpe_p₀
    · rw [AlternatingPath.toPath_cons, Quiver.Path.comp_cons, Quiver.Path.comp_cons]
      exact (hpe_comp.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.one _).symm

private theorem not_closed_lift_of_isReduced (e : Γ.E) (p_e : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ∀ (w : Γ.V), Γ.tgt e = w → ∀ (p_w : 𝔸.Path ⟨v₀⟩ ⟨w⟩) (q : 𝔸.AlternatingPath w (Γ.src e)),
      (AlternatingPath.cons q (Γ.dart e) 1).IsReduced →
      Path.Homotopic (p_e.cons (Letter.dart (Γ.dart e)))
        (p_w.comp (AlternatingPath.cons q (Γ.dart e) 1).toPath) →
      BassSerreVertex.mk 𝔸 v₀ (p_e.cons (Letter.dart (Γ.dart e))) =
        BassSerreVertex.mk 𝔸 v₀ p_w → False := by
  intro w hw p_w q hr hp_hom hv_eq
  subst hw
  obtain ⟨g, hg⟩ := BassSerreVertex.mk_eq_mk_iff.mp hv_eq
  have h₁ := (hp_hom.symm.trans hg).comp_left p_w.reverse
  have h₂ : Path.Homotopic
      (p_w.reverse.comp (p_w.comp (AlternatingPath.cons q (Γ.dart e) 1).toPath))
      (AlternatingPath.cons q (Γ.dart e) 1).toPath := by
    simpa using Path.Homotopic.comp_reverse_comp_comp .nil p_w
      (AlternatingPath.cons q (Γ.dart e) 1).toPath
  have h₃ : Path.Homotopic (p_w.reverse.comp (p_w.cons (Letter.vertex g)))
      (Path.ofVertex g) := by
    rw [← Path.comp_ofVertex]
    simpa using Path.Homotopic.comp_reverse_comp_comp .nil p_w (Path.ofVertex g)
  exact hr.not_homotopic_ofVertex_cons (h₂.symm.trans (h₁.trans h₃))

/-- `X(𝔸, v₀)` is acyclic: a nonempty reduced closed path would lift to a reduced closed alternating
`𝔸`-path containing a dart and homotopic to a vertex group letter, contradicting Britton's lemma. -/
theorem bassSerreGraph_isAcyclic : (𝔸.bassSerreGraph v₀).IsAcyclic := by
  rw [SerreGraph.isAcyclic_iff]
  intro u P hp
  cases P with
  | nil => rfl
  | cons P₀ E =>
    refine False.elim <|
      BassSerreVertex.induction_on (P := fun d => u = d → False) u (fun {v₁} p₁ hu => ?_) rfl
    refine BassSerreDart.induction_on (P := fun d => E.1 = d → False) E.1 (fun e p_e hE => ?_) rfl
    obtain ⟨q, hq_red, hpath⟩ := 𝔸.lift_isReduced_cons v₀ P₀ E hp p₁ hu e p_e hE
    have htgt : BassSerreVertex.mk 𝔸 v₀ (p_e.cons (Letter.dart (Γ.dart e))) =
        BassSerreVertex.mk 𝔸 v₀ p₁ := by
      rw [← bassSerreGraph_tgt_mk, ← hE, E.2.2, hu]
    exact 𝔸.not_closed_lift_of_isReduced v₀ e p_e v₁
      (BassSerreVertex.mk_eq_mk_iff_exists.mp htgt).choose p₁ q hq_red hpath htgt

/-- The Bass–Serre graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree : (𝔸.bassSerreGraph v₀).IsTree :=
  (SerreGraph.isTree_iff _).mpr ⟨𝔸.bassSerreGraph_connected v₀, 𝔸.bassSerreGraph_isAcyclic v₀⟩

/-! ### Left action of `π₁(𝔸, v₀)` and the bundled `GTree` -/

private def smulVertexAux (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (𝔸.bassSerreGraph v₀).V → (𝔸.bassSerreGraph v₀).V :=
  Quotient.lift (fun x => BassSerreVertex.mk 𝔸 v₀ (s.comp x.2)) <| by
    rintro ⟨v, p⟩ ⟨w, q⟩ ⟨h, a, ha⟩
    dsimp only at h ha
    subst h
    exact BassSerreVertex.mk_eq_mk_iff.mpr ⟨a, ha.comp_left s⟩

private def smulVertex : π₁ 𝔸 v₀ → (𝔸.bassSerreGraph v₀).V → (𝔸.bassSerreGraph v₀).V :=
  π₁.lift (𝔸.smulVertexAux v₀) fun _ _ hs => funext fun u =>
    BassSerreVertex.induction_on u fun p => BassSerreVertex.mk_congr (hs.comp_right p)

private def smulDartAux (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (𝔸.bassSerreGraph v₀).E → (𝔸.bassSerreGraph v₀).E :=
  Quotient.lift (fun x => BassSerreDart.mk 𝔸 v₀ x.1 (s.comp x.2)) <| by
    rintro ⟨e, p⟩ ⟨e', q⟩ ⟨h, c, hc⟩
    dsimp only at h hc
    subst h
    exact BassSerreDart.mk_eq_mk_iff.mpr ⟨c, hc.comp_left s⟩

private def smulDart : π₁ 𝔸 v₀ → (𝔸.bassSerreGraph v₀).E → (𝔸.bassSerreGraph v₀).E :=
  π₁.lift (𝔸.smulDartAux v₀) fun _ _ hs => funext fun d =>
    BassSerreDart.induction_on d fun _ p => BassSerreDart.mk_congr (hs.comp_right p)

@[simp] private theorem smulVertex_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.smulVertex v₀ (π₁.mk s) (BassSerreVertex.mk 𝔸 v₀ p) =
      BassSerreVertex.mk 𝔸 v₀ (s.comp p) := by
  rw [smulVertex, π₁.lift_mk]
  rfl

@[simp] private theorem smulDart_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.smulDart v₀ (π₁.mk s) (BassSerreDart.mk 𝔸 v₀ e p) =
      BassSerreDart.mk 𝔸 v₀ e (s.comp p) := by
  rw [smulDart, π₁.lift_mk]
  rfl

private theorem one_smulVertex (u : (𝔸.bassSerreGraph v₀).V) : 𝔸.smulVertex v₀ 1 u = u :=
  BassSerreVertex.induction_on u fun p => by
    rw [← π₁.mk_nil, smulVertex_mk, Quiver.Path.nil_comp]

private theorem mul_smulVertex (g h : π₁ 𝔸 v₀) (u : (𝔸.bassSerreGraph v₀).V) :
    𝔸.smulVertex v₀ (g * h) u = 𝔸.smulVertex v₀ g (𝔸.smulVertex v₀ h u) :=
  π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    BassSerreVertex.induction_on u fun p => by
      rw [← π₁.mk_comp, smulVertex_mk, smulVertex_mk, smulVertex_mk, Quiver.Path.comp_assoc]

private theorem one_smulDart (d : (𝔸.bassSerreGraph v₀).E) : 𝔸.smulDart v₀ 1 d = d :=
  BassSerreDart.induction_on d fun e p => by
    rw [← π₁.mk_nil, smulDart_mk, Quiver.Path.nil_comp]

private theorem mul_smulDart (g h : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    𝔸.smulDart v₀ (g * h) d = 𝔸.smulDart v₀ g (𝔸.smulDart v₀ h d) :=
  π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    BassSerreDart.induction_on d fun e p => by
      rw [← π₁.mk_comp, smulDart_mk, smulDart_mk, smulDart_mk, Quiver.Path.comp_assoc]

private def smulVertexEquiv (g : π₁ 𝔸 v₀) : (𝔸.bassSerreGraph v₀).V ≃ (𝔸.bassSerreGraph v₀).V where
  toFun := 𝔸.smulVertex v₀ g
  invFun := 𝔸.smulVertex v₀ g⁻¹
  left_inv u := by rw [← mul_smulVertex, inv_mul_cancel, one_smulVertex]
  right_inv u := by rw [← mul_smulVertex, mul_inv_cancel, one_smulVertex]

private def smulDartEquiv (g : π₁ 𝔸 v₀) : (𝔸.bassSerreGraph v₀).E ≃ (𝔸.bassSerreGraph v₀).E where
  toFun := 𝔸.smulDart v₀ g
  invFun := 𝔸.smulDart v₀ g⁻¹
  left_inv d := by rw [← mul_smulDart, inv_mul_cancel, one_smulDart]
  right_inv d := by rw [← mul_smulDart, mul_inv_cancel, one_smulDart]

/-- The left action of `π₁(𝔸, v₀)` on `X(𝔸, v₀)` by graph automorphisms via path concatenation. -/
def bassSerreAction : π₁ 𝔸 v₀ →* (𝔸.bassSerreGraph v₀).Aut where
  toFun g :=
    { equivV := 𝔸.smulVertexEquiv v₀ g
      equivE := 𝔸.smulDartEquiv v₀ g
      map_src := fun d => π₁.induction_on g fun s => BassSerreDart.induction_on d fun e p =>
        (congrArg (𝔸.bassSerreGraph v₀).src (𝔸.smulDart_mk v₀ s e p)).trans
          (𝔸.smulVertex_mk v₀ s p).symm
      map_rev := fun d => π₁.induction_on g fun s => BassSerreDart.induction_on d fun e p =>
        ((𝔸.smulDart_mk v₀ s (Γ.rev e) (p.cons (Letter.dart (Γ.dart e)))).trans
          (congrArg (BassSerreDart.mk 𝔸 v₀ (Γ.rev e)) (Quiver.Path.comp_cons ..))).trans
          (congrArg (𝔸.bassSerreGraph v₀).rev (𝔸.smulDart_mk v₀ s e p)).symm }
  map_one' := SerreGraph.Iso.ext (𝔸.one_smulVertex v₀) (𝔸.one_smulDart v₀)
  map_mul' g h := SerreGraph.Iso.ext (𝔸.mul_smulVertex v₀ g h) (𝔸.mul_smulDart v₀ g h)

/-- The type projection to `Γ` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreTypeHom_comp_action (g : π₁ 𝔸 v₀) :
    (𝔸.bassSerreTypeHom v₀).comp (𝔸.bassSerreAction v₀ g).toHom = 𝔸.bassSerreTypeHom v₀ :=
  π₁.induction_on g fun s => by
    ext d
    · rw [SerreGraph.Hom.comp_mapV]
      exact BassSerreVertex.induction_on d fun p =>
        (congrArg (𝔸.bassSerreTypeHom v₀).mapV (𝔸.smulVertex_mk v₀ s p)).trans rfl
    · rw [SerreGraph.Hom.comp_mapE]
      exact BassSerreDart.induction_on d fun e p =>
        (congrArg (𝔸.bassSerreTypeHom v₀).mapE (𝔸.smulDart_mk v₀ s e p)).trans rfl

/-- The component projection to `Γ.component v₀` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreComponentHom_comp_action (g : π₁ 𝔸 v₀) :
    (𝔸.bassSerreComponentHom v₀).comp (𝔸.bassSerreAction v₀ g).toHom =
      𝔸.bassSerreComponentHom v₀ :=
  π₁.induction_on g fun s => by
    ext d
    · rw [SerreGraph.Hom.comp_mapV]
      exact BassSerreVertex.induction_on d fun p => Subtype.ext <|
        (congrArg (fun x => ((𝔸.bassSerreComponentHom v₀).mapV x).1)
          (𝔸.smulVertex_mk v₀ s p)).trans rfl
    · rw [SerreGraph.Hom.comp_mapE]
      exact BassSerreDart.induction_on d fun e p => Subtype.ext <|
        (congrArg (fun x => ((𝔸.bassSerreComponentHom v₀).mapE x).1)
          (𝔸.smulDart_mk v₀ s e p)).trans rfl

/-- `π₁(𝔸, v₀)` acts on `X(𝔸, v₀)` without inversions: any inverted dart would map to a fixed dart
of `Γ.rev` under the invariant type projection. -/
theorem bassSerreAction_smul_ne_rev (g : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    (𝔸.bassSerreAction v₀ g).equivE d ≠ (𝔸.bassSerreGraph v₀).rev d :=
  SerreGraph.Aut.smul_ne_rev_of_comp_toHom_eq (𝔸.bassSerreTypeHom v₀)
    (𝔸.bassSerreAction v₀ g) (𝔸.bassSerreTypeHom_comp_action v₀ g) d

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at base vertex `v₀`, as a `GTree` for
`π₁(𝔸, v₀)`. -/
@[expose] def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := 𝔸.bassSerreGraph v₀
  isTree := 𝔸.bassSerreTree_isTree v₀
  action := 𝔸.bassSerreAction v₀
  action_smul_ne_rev := 𝔸.bassSerreAction_smul_ne_rev v₀

/-! ### Path constructors and basic API on `bassSerreTree` -/

/-- The vertex `p A_v` of `𝔸.bassSerreTree v₀` represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (𝔸.bassSerreTree v₀).V :=
  BassSerreVertex.mk 𝔸 v₀ p

/-- The base vertex `1 · A_{v₀}` of `𝔸.bassSerreTree v₀`, represented by the empty path at `v₀`. -/
def bassSerreBaseVertex : (𝔸.bassSerreTree v₀).V :=
  𝔸.bassSerreVertex v₀ .nil

/-- The dart `[e, p]` of `𝔸.bassSerreTree v₀`, with source `p A_{src e}` and target
`(p · e) A_{tgt e}`. -/
def bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreTree v₀).E :=
  BassSerreDart.mk 𝔸 v₀ e p

section TreeAPI

variable {𝔸 v₀}

/-- Prove a property of vertices of `𝔸.bassSerreTree v₀` by checking it on `𝔸`-paths from `v₀`. -/
@[elab_as_elim] theorem bassSerreVertex_induction {P : (𝔸.bassSerreTree v₀).V → Prop}
    (u : (𝔸.bassSerreTree v₀).V)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (𝔸.bassSerreVertex v₀ p)) : P u :=
  BassSerreVertex.induction_on u h

/-- Prove a property of darts of `𝔸.bassSerreTree v₀` by checking it on pairs `(e, p)`. -/
@[elab_as_elim] theorem bassSerreDart_induction {P : (𝔸.bassSerreTree v₀).E → Prop}
    (d : (𝔸.bassSerreTree v₀).E)
    (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (𝔸.bassSerreDart v₀ e p)) : P d :=
  BassSerreDart.induction_on d h

theorem bassSerreVertex_eq_iff_exists_eq {v w : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨w⟩} :
    𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ q ↔
      ∃ (h : v = w) (a : 𝔸.vertexGroup w), Path.Homotopic (h ▸ p) (q.cons (Letter.vertex a)) :=
  BassSerreVertex.mk_eq_mk_iff_exists

/-- Two `𝔸`-paths from `v₀` to `v` represent the same vertex of `X(𝔸, v₀)` if and only if they
differ on the right by an element of `A_v` up to homotopy. -/
theorem bassSerreVertex_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ q ↔
      ∃ a : 𝔸.vertexGroup v, Path.Homotopic p (q.cons (Letter.vertex a)) :=
  BassSerreVertex.mk_eq_mk_iff

/-- Normal-form characterization of equality of Bass–Serre vertices over `v`: two paths define the
same vertex exactly when their normal forms agree up to the final vertex group element. -/
theorem bassSerreVertex_eq_iff_setLast_eq (d : 𝔸.Transversal) {v : Γ.V}
    {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ q ↔
      (normalForm d p).toAlternatingPath.setLast 1 =
        (normalForm d q).toAlternatingPath.setLast 1 :=
  bassSerreVertex_eq_iff.trans (exists_homotopic_cons_vertex_iff_setLast_eq d)

/-- Homotopic `𝔸`-paths represent the same vertex of `X(𝔸, v₀)`. -/
theorem bassSerreVertex_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ q :=
  BassSerreVertex.mk_congr h

@[simp] theorem bassSerreVertex_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    𝔸.bassSerreVertex v₀ (p.cons (Letter.vertex a)) = 𝔸.bassSerreVertex v₀ p :=
  BassSerreVertex.mk_cons_vertex p a

theorem bassSerreVertex_comp_ofVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    𝔸.bassSerreVertex v₀ (p.comp (Path.ofVertex a)) = 𝔸.bassSerreVertex v₀ p := by
  rw [Path.comp_ofVertex, bassSerreVertex_cons_vertex]

@[simp] theorem bassSerreVertex_ofVertex (a : 𝔸.vertexGroup v₀) :
    𝔸.bassSerreVertex v₀ (Path.ofVertex a) = 𝔸.bassSerreBaseVertex v₀ := by
  rw [Path.ofVertex_eq_nil_cons, bassSerreVertex_cons_vertex]
  rfl

theorem bassSerreDart_eq_iff_exists_eq {e e' : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e'⟩} :
    𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e' q ↔
      ∃ (h : e = e') (c : 𝔸.edgeGroup (Γ.toGeomEdge e')),
        Path.Homotopic (h ▸ p) (q.cons (Letter.vertex (𝔸.α e' c))) :=
  BassSerreDart.mk_eq_mk_iff_exists

/-- Two paths from `v₀` to `src e` define the same dart over `e` if and only if they differ on the
right by an element of `α_e(A_e)` up to homotopy. -/
theorem bassSerreDart_eq_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e),
        Path.Homotopic p (q.cons (Letter.vertex (𝔸.α e c))) :=
  BassSerreDart.mk_eq_mk_iff

/-- Homotopic `𝔸`-paths define the same dart over `e`. -/
theorem bassSerreDart_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e q :=
  BassSerreDart.mk_congr h

@[simp] theorem bassSerreDart_cons_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex (𝔸.α e c))) = 𝔸.bassSerreDart v₀ e p :=
  BassSerreDart.mk_cons_α e p c

theorem bassSerreDart_comp_ofVertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.bassSerreDart v₀ e (p.comp (Path.ofVertex (𝔸.α e c))) = 𝔸.bassSerreDart v₀ e p := by
  rw [Path.comp_ofVertex, bassSerreDart_cons_α]

@[simp] theorem bassSerreTree_src_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDart v₀ e p) = 𝔸.bassSerreVertex v₀ p :=
  (rfl)

@[simp] theorem bassSerreTree_rev_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).rev (𝔸.bassSerreDart v₀ e p) =
      𝔸.bassSerreDart v₀ (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem bassSerreTree_tgt_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).tgt (𝔸.bassSerreDart v₀ e p) =
      𝔸.bassSerreVertex v₀ (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem bassSerreTypeHom_mapV {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTypeHom v₀).mapV (𝔸.bassSerreVertex v₀ p) = v :=
  (rfl)

@[simp] theorem bassSerreTypeHom_mapE (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTypeHom v₀).mapE (𝔸.bassSerreDart v₀ e p) = e :=
  (rfl)

@[simp] theorem mk_smul_bassSerreVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • 𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ (s.comp p) :=
  𝔸.smulVertex_mk v₀ s p

@[simp] theorem mk_smul_bassSerreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk s • 𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e (s.comp p) :=
  𝔸.smulDart_mk v₀ s e p

end TreeAPI

/-! ### Vertex and edge stabilizers -/

section Stabilizers

variable {𝔸 v₀}

private theorem homotopic_comp_iff_homotopic_comp_reverse {v : Γ.V} (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    Path.Homotopic (s.comp p) (p.cons (Letter.vertex a)) ↔
      Path.Homotopic s ((p.comp (Path.ofVertex a)).comp p.reverse) := by
  rw [← Path.comp_ofVertex]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (Path.Homotopic.comp_comp_reverse s p).symm.trans (h.comp_right p.reverse)
  · exact (h.comp_right p).trans <| by
      simpa using Path.Homotopic.comp_reverse_comp_comp (p.comp (Path.ofVertex a)) p .nil

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex `p A_v` of `X(𝔸, v₀)` is `p A_v p⁻¹`, the image of
`π₁.vertexHom p : A_v →* π₁(𝔸, v₀)`. -/
theorem stabilizer_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreVertex v₀ p) = (π₁.vertexHom p).range := by
  ext g
  refine π₁.induction_on g fun s => ?_
  rw [mem_stabilizer_iff, mk_smul_bassSerreVertex, bassSerreVertex_eq_iff, MonoidHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ => ⟨a, ?_⟩, fun ⟨a, ha⟩ => ⟨a, ?_⟩⟩
  · rw [π₁.vertexHom_apply]
    exact (π₁.mk_eq_mk_iff.mpr ((homotopic_comp_iff_homotopic_comp_reverse s p a).mp ha)).symm
  · rw [π₁.vertexHom_apply] at ha
    exact (homotopic_comp_iff_homotopic_comp_reverse s p a).mpr (π₁.mk_eq_mk_iff.mp ha.symm)

/-- At the base vertex `1 · A_{v₀}`, the stabilizer is the image of `A_{v₀}` in `π₁(𝔸, v₀)`. -/
@[simp] theorem stabilizer_bassSerreBaseVertex :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreBaseVertex v₀) =
      (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  stabilizer_vertex .nil

/-- Because `π₁.vertexHom p` is injective, the vertex group `A_v` is isomorphic to the stabilizer
of `p A_v` in `π₁(𝔸, v₀)`. -/
noncomputable def vertexStabilizerEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.vertexGroup v ≃* stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreVertex v₀ p) :=
  (MonoidHom.ofInjective (π₁.vertexHom_injective p)).trans
    (MulEquiv.subgroupCongr (stabilizer_vertex p).symm)

@[simp] theorem coe_vertexStabilizerEquiv_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) : (vertexStabilizerEquiv p a : π₁ 𝔸 v₀) = π₁.vertexHom p a :=
  (rfl)

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart `[e, p]` of `X(𝔸, v₀)` is `p α_e(A_e) p⁻¹`, the
conjugate along `p` of the edge-group image `α_e(A_e)`. For `p = q · a` (the dart between `q A_v`
and `(q a e) A_{v'}`), this is `q a α_e(A_e) a⁻¹ q⁻¹`. -/
theorem stabilizer_edge (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreDart v₀ e p) = ((𝔸.α e).range).map (π₁.vertexHom p) := by
  ext g
  refine π₁.induction_on g fun s => ?_
  rw [mem_stabilizer_iff, mk_smul_bassSerreDart, bassSerreDart_eq_iff, ← MonoidHom.range_comp,
    MonoidHom.mem_range]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [MonoidHom.comp_apply, π₁.vertexHom_apply]
    exact (π₁.mk_eq_mk_iff.mpr
      ((homotopic_comp_iff_homotopic_comp_reverse s p (𝔸.α e c)).mp hc)).symm
  · rw [MonoidHom.comp_apply, π₁.vertexHom_apply] at hc
    exact (homotopic_comp_iff_homotopic_comp_reverse s p (𝔸.α e c)).mpr
      (π₁.mk_eq_mk_iff.mp hc.symm)

/-- Because both `𝔸.α e` and `π₁.vertexHom p` are injective, the edge group `A_e` is isomorphic to
the stabilizer of `[e, p]` in `π₁(𝔸, v₀)`. -/
noncomputable def edgeStabilizerEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.edgeGroup (Γ.toGeomEdge e) ≃* stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreDart v₀ e p) :=
  (MonoidHom.ofInjective (f := (π₁.vertexHom p).comp (𝔸.α e))
      ((π₁.vertexHom_injective p).comp (𝔸.α_injective e))).trans
    (MulEquiv.subgroupCongr ((MonoidHom.range_comp (π₁.vertexHom p) (𝔸.α e)).trans
      (stabilizer_edge e p).symm))

@[simp] theorem coe_edgeStabilizerEquiv_apply (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    (edgeStabilizerEquiv e p c : π₁ 𝔸 v₀) = π₁.vertexHom p (𝔸.α e c) :=
  (rfl)

/-- Every conjugated vertex group `p A_v p⁻¹` is elliptic in the Bass–Serre tree `X(𝔸, v₀)`. -/
theorem isEllipticSubgroup_vertexHom_range {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  stabilizer_vertex p ▸ (𝔸.bassSerreTree v₀).isEllipticSubgroup_stabilizer _

end Stabilizers

/-! ### The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` -/

/-- The quotient Serre graph `X(𝔸, v₀) / π₁(𝔸, v₀)`. -/
abbrev bassSerreQuotient : SerreGraph.{max u v w, max u v w} :=
  (𝔸.bassSerreTree v₀).toSerreGraph.quotient (𝔸.bassSerreTree v₀).action
    (𝔸.bassSerreTree v₀).action_smul_ne_rev

/-- The morphism from `X(𝔸, v₀) / π₁(𝔸, v₀)` to `Γ.component v₀` induced by the invariant
component projection. -/
def bassSerreQuotientToComponent : (𝔸.bassSerreQuotient v₀).Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (𝔸.bassSerreTree v₀).action_smul_ne_rev (𝔸.bassSerreComponentHom v₀)
    (𝔸.bassSerreComponentHom_comp_action v₀)

@[simp] theorem bassSerreQuotientToComponent_mapV_quotientMap (u : (𝔸.bassSerreTree v₀).V) :
    (𝔸.bassSerreQuotientToComponent v₀).mapV
      (((𝔸.bassSerreTree v₀).toSerreGraph.quotientMap
        (𝔸.bassSerreTree v₀).action (𝔸.bassSerreTree v₀).action_smul_ne_rev).mapV u) =
      (𝔸.bassSerreComponentHom v₀).mapV u :=
  SerreGraph.quotientLift_mapV_quotientMap _ _ u

@[simp] theorem bassSerreQuotientToComponent_mapE_quotientMap (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.bassSerreQuotientToComponent v₀).mapE
      (((𝔸.bassSerreTree v₀).toSerreGraph.quotientMap
        (𝔸.bassSerreTree v₀).action (𝔸.bassSerreTree v₀).action_smul_ne_rev).mapE d) =
      (𝔸.bassSerreComponentHom v₀).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap _ _ d

private theorem bassSerreQuotientToComponent_mapV_bijective :
    Function.Bijective (𝔸.bassSerreQuotientToComponent v₀).mapV := by
  refine ⟨fun x y => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨u₁, rfl⟩ := SerreGraph.quotientMap_mapV_surjective _ _ _ x
    obtain ⟨u₂, rfl⟩ := SerreGraph.quotientMap_mapV_surjective _ _ _ y
    rw [bassSerreQuotientToComponent_mapV_quotientMap,
      bassSerreQuotientToComponent_mapV_quotientMap]
    refine bassSerreVertex_induction u₁ fun {v₁} p₁ =>
      bassSerreVertex_induction u₂ fun {v₂} p₂ => fun h => ?_
    have hv_eq : v₁ = v₂ := congrArg Subtype.val h
    subst hv_eq
    refine SerreGraph.quotientMap_mapV_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [← GTree.smul_vertex_def, mk_smul_bassSerreVertex]
    exact bassSerreVertex_congr (by simpa using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨P⟩ := (Γ.mem_componentVertices_iff v₀ v).mp hv
    refine ⟨((𝔸.bassSerreTree v₀).toSerreGraph.quotientMap _ _).mapV
      (𝔸.bassSerreVertex v₀ ((dartPrefunctor 𝔸).mapPath P)), Subtype.ext ?_⟩
    rw [bassSerreQuotientToComponent_mapV_quotientMap]
    rfl

private theorem bassSerreQuotientToComponent_mapE_bijective :
    Function.Bijective (𝔸.bassSerreQuotientToComponent v₀).mapE := by
  refine ⟨fun x y => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨d₁, rfl⟩ := SerreGraph.quotientMap_mapE_surjective _ _ _ x
    obtain ⟨d₂, rfl⟩ := SerreGraph.quotientMap_mapE_surjective _ _ _ y
    rw [bassSerreQuotientToComponent_mapE_quotientMap,
      bassSerreQuotientToComponent_mapE_quotientMap]
    refine bassSerreDart_induction d₁ fun e₁ p₁ =>
      bassSerreDart_induction d₂ fun e₂ p₂ => fun h => ?_
    have he_eq : e₁ = e₂ := congrArg Subtype.val h
    subst he_eq
    refine SerreGraph.quotientMap_mapE_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [← GTree.smul_dart_def, mk_smul_bassSerreDart]
    exact bassSerreDart_congr (by simpa using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨P⟩ := (Γ.mem_componentDarts_iff v₀ e).mp he
    refine ⟨((𝔸.bassSerreTree v₀).toSerreGraph.quotientMap _ _).mapE
      (𝔸.bassSerreDart v₀ e ((dartPrefunctor 𝔸).mapPath P)), Subtype.ext ?_⟩
    rw [bassSerreQuotientToComponent_mapE_quotientMap]
    rfl

/-- The quotient of the Bass–Serre tree `X(𝔸, v₀)` by `π₁(𝔸, v₀)` is isomorphic to the connected
component `Γ.component v₀` of the base vertex in `Γ`. -/
noncomputable def bassSerreQuotientIso : (𝔸.bassSerreQuotient v₀).Iso (Γ.component v₀) :=
  (𝔸.bassSerreQuotientToComponent v₀).toIso (𝔸.bassSerreQuotientToComponent_mapV_bijective v₀)
    (𝔸.bassSerreQuotientToComponent_mapE_bijective v₀)

@[simp] theorem bassSerreQuotientIso_toHom :
    (𝔸.bassSerreQuotientIso v₀).toHom = 𝔸.bassSerreQuotientToComponent v₀ :=
  SerreGraph.Hom.toIso_toHom _ _ _

/-- When the underlying graph `Γ` is preconnected, the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` is
isomorphic to `Γ` itself. -/
noncomputable def bassSerreQuotientIsoOfPreconnected (hΓ : Γ.Preconnected) :
    (𝔸.bassSerreQuotient v₀).Iso Γ :=
  (𝔸.bassSerreQuotientIso v₀).trans (Γ.componentIsoOfPreconnected hΓ)

/-- When `Γ` is connected, the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` is isomorphic to `Γ`. -/
noncomputable def bassSerreQuotientIsoOfConnected (hΓ : Γ.Connected) :
    (𝔸.bassSerreQuotient v₀).Iso Γ :=
  𝔸.bassSerreQuotientIsoOfPreconnected v₀ (Γ.connected_iff.mp hΓ).2

/-! ### Local star, adjacent vertices, and vertex degrees -/

section Star

/-- Transported dart constructor for an arrow `⟨e, he, rfl⟩` issuing from `v`. -/
def bassSerreDartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).E :=
  𝔸.bassSerreDart v₀ e (he.symm ▸ p)

variable {𝔸 v₀}

@[simp] theorem bassSerreDartOfSrcEq_rfl (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.bassSerreDartOfSrcEq v₀ e rfl p = 𝔸.bassSerreDart v₀ e p :=
  (rfl)

@[simp] theorem bassSerreTree_src_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDartOfSrcEq v₀ e he p) = 𝔸.bassSerreVertex v₀ p := by
  subst he
  rfl

@[simp] theorem bassSerreTree_tgt_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).tgt (𝔸.bassSerreDartOfSrcEq v₀ e he p) =
      𝔸.bassSerreVertex v₀ (p.cons (Letter.dart ⟨e, he, rfl⟩)) := by
  subst he
  rw [← Γ.dart_def]
  rfl

@[simp] theorem bassSerreTypeHom_mapE_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTypeHom v₀).mapE (𝔸.bassSerreDartOfSrcEq v₀ e he p) = e := by
  subst he
  rfl

private theorem bassSerreDartOfSrcEq_cons_eq_iff (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a₁ a₂ : 𝔸.vertexGroup v) :
    𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a₁)) =
      𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a₂)) ↔
      (a₁ : 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e, he, rfl⟩).range) = a₂ := by
  subst he
  rw [bassSerreDartOfSrcEq_rfl, bassSerreDartOfSrcEq_rfl, bassSerreDart_eq_iff, QuotientGroup.eq,
    MonoidHom.mem_range, αArrow_mk]
  refine ⟨fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩, fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩⟩
  · have hmul : Path.Homotopic (p.cons (Letter.vertex a₁))
        (p.cons (Letter.vertex (a₂ * 𝔸.α e c))) :=
      hc.trans (Path.Homotopic.mul p a₂ (𝔸.α e c))
    have hkey : ∀ x y : 𝔸.vertexGroup (Γ.src e),
        Path.Homotopic (p.cons (Letter.vertex x)) (p.cons (Letter.vertex y)) → x = y := by
      intro x y hxy
      rw [← Path.comp_ofVertex, ← Path.comp_ofVertex] at hxy
      have hx : Path.Homotopic (p.reverse.comp (p.comp (Path.ofVertex x))) (Path.ofVertex x) := by
        simpa using Path.Homotopic.comp_reverse_comp_comp .nil p (Path.ofVertex x)
      have hy : Path.Homotopic (p.reverse.comp (p.comp (Path.ofVertex y))) (Path.ofVertex y) := by
        simpa using Path.Homotopic.comp_reverse_comp_comp .nil p (Path.ofVertex y)
      exact Path.ofVertex_homotopic_ofVertex_iff.mp
        (hx.symm.trans ((hxy.comp_left p.reverse).trans hy))
    have ha : a₁ = a₂ * 𝔸.α e c := hkey _ _ hmul
    rw [ha, map_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  · have ha : a₁ = a₂ * 𝔸.α e c⁻¹ := by
      rw [map_inv, hc, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [ha]
    exact (Path.Homotopic.mul p a₂ (𝔸.α e c⁻¹)).symm

private def starFromCosets {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range) →
      {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} :=
  fun ⟨e, q⟩ => Quotient.liftOn' q
    (fun a => ⟨𝔸.bassSerreDartOfSrcEq v₀ e.1 e.2 (p.cons (Letter.vertex a)), by simp⟩)
    (fun a₁ a₂ h => Subtype.ext <| (bassSerreDartOfSrcEq_cons_eq_iff e.1 e.2 p a₁ a₂).mpr
      (Quotient.sound h))

private theorem starFromCosets_bijective {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Function.Bijective (starFromCosets p) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨e₁, he₁⟩, q₁⟩ ⟨⟨e₂, he₂⟩, q₂⟩ h
    refine Quotient.inductionOn₂' q₁ q₂ (fun a₁ a₂ h => ?_) h
    have hval : 𝔸.bassSerreDartOfSrcEq v₀ e₁ he₁ (p.cons (Letter.vertex a₁)) =
        𝔸.bassSerreDartOfSrcEq v₀ e₂ he₂ (p.cons (Letter.vertex a₂)) := congrArg Subtype.val h
    have he_eq : e₁ = e₂ := by
      simpa using congrArg (𝔸.bassSerreTypeHom v₀).mapE hval
    subst he_eq
    obtain rfl : he₁ = he₂ := Subsingleton.elim _ _
    exact Sigma.ext rfl (heq_of_eq ((bassSerreDartOfSrcEq_cons_eq_iff e₁ he₁ p a₁ a₂).mp hval))
  · rintro ⟨E, hE⟩
    revert hE
    refine bassSerreDart_induction E fun e₀ q hE => ?_
    have hsrc : 𝔸.bassSerreVertex v₀ q = 𝔸.bassSerreVertex v₀ p := hE
    have he₀ : Γ.src e₀ = v := (bassSerreVertex_eq_iff_exists_eq.mp hsrc).choose
    -- Generalize `v` along `he₀` so `q` and `p` share the same endpoint without casts.
    have key : ∀ (w : Γ.V), Γ.src e₀ = w → ∀ (p_w : 𝔸.Path ⟨v₀⟩ ⟨w⟩),
        𝔸.bassSerreVertex v₀ q = 𝔸.bassSerreVertex v₀ p_w →
        ∃ x, (starFromCosets p_w x).1 = 𝔸.bassSerreDart v₀ e₀ q := by
      intro w hw p_w hsrc_w
      subst hw
      obtain ⟨a, ha⟩ := bassSerreVertex_eq_iff.mp hsrc_w
      exact ⟨⟨⟨e₀, rfl⟩, a⟩, (bassSerreDart_congr ha).symm⟩
    obtain ⟨x, hx⟩ := key v he₀ p hsrc
    exact ⟨x, Subtype.ext hx⟩

variable (𝔸 v₀) in
/-- The star of a vertex `p A_v` in `X(𝔸, v₀)` is in bijection with the disjoint union, over all
darts `e` of `Γ` with `src e = v`, of the left coset spaces `A_v ⧸ α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} ≃
      Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range :=
  (Equiv.ofBijective (starFromCosets p) (starFromCosets_bijective p)).symm

@[simp] theorem bassSerreStarEquiv_symm_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    ((𝔸.bassSerreStarEquiv v₀ p).symm ⟨e, a⟩).1 =
      𝔸.bassSerreDartOfSrcEq v₀ e.1 e.2 (p.cons (Letter.vertex a)) :=
  (rfl)

/-- Because `X(𝔸, v₀)` is acyclic, the target map identifies the outgoing darts at any vertex `u`
with the adjacent vertices `{w // Nonempty (u ⟶ w)}`. -/
private noncomputable def treeStarEquivAdjacent (u : (𝔸.bassSerreTree v₀).V) :
    {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = u} ≃
      {w : (𝔸.bassSerreTree v₀).V // Nonempty (u ⟶ w)} :=
  Equiv.ofBijective (fun E => ⟨(𝔸.bassSerreTree v₀).tgt E.1, ⟨⟨E.1, E.2, rfl⟩⟩⟩)
    ⟨fun ⟨E₁, h₁⟩ ⟨E₂, h₂⟩ h => Subtype.ext <| by
      have htgt : (𝔸.bassSerreTree v₀).tgt E₁ = (𝔸.bassSerreTree v₀).tgt E₂ :=
        congrArg Subtype.val h
      let f₁ : u ⟶ (𝔸.bassSerreTree v₀).tgt E₁ := ⟨E₁, h₁, rfl⟩
      let f₂ : u ⟶ (𝔸.bassSerreTree v₀).tgt E₁ := ⟨E₂, h₂, htgt.symm⟩
      have hpath := (𝔸.bassSerreGraph_isAcyclic v₀).eq_of_isReduced
        (SerreGraph.Path.isReduced_toPath _ f₁) (SerreGraph.Path.isReduced_toPath _ f₂)
      injection hpath with _ _ _ hf
      exact congrArg (fun f : u ⟶ (𝔸.bassSerreTree v₀).tgt E₁ => f.1) hf,
     fun ⟨w, ⟨f⟩⟩ => ⟨⟨f.1, f.2.1⟩, Subtype.ext f.2.2⟩⟩

variable (𝔸 v₀) in
/-- The vertices of `X(𝔸, v₀)` adjacent to `p A_v` correspond bijectively to pairs `(e, a α_e(A_e))`
with `src e = v`, sending `(e, a α_e(A_e))` to `(p a e) A_{tgt e}`. -/
noncomputable def bassSerreAdjacentEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range) ≃
      {w : (𝔸.bassSerreTree v₀).V // Nonempty (𝔸.bassSerreVertex v₀ p ⟶ w)} :=
  (𝔸.bassSerreStarEquiv v₀ p).symm.trans (treeStarEquivAdjacent (𝔸.bassSerreVertex v₀ p))

@[simp] theorem bassSerreAdjacentEquiv_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    (𝔸.bassSerreAdjacentEquiv v₀ p ⟨e, a⟩).1 =
      𝔸.bassSerreVertex v₀ ((p.cons (Letter.vertex a)).cons (Letter.dart ⟨e.1, e.2, rfl⟩)) :=
  bassSerreTree_tgt_dartOfSrcEq e.1 e.2 (p.cons (Letter.vertex a))

/-- When finitely many darts issue from `v` in `Γ` and each edge-group image has finite index in
`A_v`, the degree of `p A_v` in `X(𝔸, v₀)` is `∑_{src e = v} [A_v : α_e(A_e)]`. -/
theorem card_bassSerreStar {v : Γ.V} [Fintype {e : Γ.E // Γ.src e = v}]
    [∀ e : {e : Γ.E // Γ.src e = v}, Finite (𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range)]
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Nat.card {E : (𝔸.bassSerreTree v₀).E //
      (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} =
      ∑ e : {e : Γ.E // Γ.src e = v}, (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range.index := by
  rw [Nat.card_congr (𝔸.bassSerreStarEquiv v₀ p), Nat.card_sigma]
  exact Finset.sum_congr rfl fun _ _ => (Subgroup.index_eq_card _).symm

end Star

/-! ### Checks and canonical examples -/

/-! #### 1. Graphs without edges (`bassSerreTree_point`) -/

section Edgeless

instance [IsEmpty Γ.E] : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun d => bassSerreDart_induction d fun e _ => isEmptyElim e⟩

instance [IsEmpty Γ.E] : Unique (𝔸.bassSerreTree v₀).V where
  default := 𝔸.bassSerreBaseVertex v₀
  uniq u := bassSerreVertex_induction u fun {v} p => by
    have aux : ∀ {y : 𝔸.LetterVertex} (q : 𝔸.Path ⟨v₀⟩ y),
        𝔸.bassSerreVertex v₀ (v := y.as) q = 𝔸.bassSerreBaseVertex v₀ := by
      intro y q
      induction q with
      | nil => rfl
      | @cons y₁ y₂ q l ih =>
        cases y₁ with | mk _ =>
        cases y₂ with | mk _ =>
        cases l with
        | vertex a => exact (bassSerreVertex_cons_vertex q a).trans ih
        | dart e => exact isEmptyElim e.1
    exact aux p

/-- Over a graph without edges, `X(𝔸, v₀)` is isomorphic as a Serre graph to `SerreGraph.point`. -/
def bassSerreTreeIsoPoint [IsEmpty Γ.E] :
    (𝔸.bassSerreTree v₀).toSerreGraph.Iso SerreGraph.point.{u, v} where
  equivV := Equiv.ofUnique _ _
  equivE := Equiv.equivOfIsEmpty _ _
  map_src d := isEmptyElim d
  map_rev d := isEmptyElim d

/-- For any graph of groups over the one-vertex edgeless graph `SerreGraph.point`, the Bass–Serre
tree is a single point without darts. -/
theorem bassSerreTree_point (𝔸 : GraphOfGroups.{0, 0, w, x} SerreGraph.point) :
    Nonempty ((𝔸.bassSerreTree PUnit.unit).toSerreGraph.Iso SerreGraph.point.{0, 0}) ∧
      Subsingleton (𝔸.bassSerreTree PUnit.unit).V ∧
      IsEmpty (𝔸.bassSerreTree PUnit.unit).E :=
  ⟨⟨𝔸.bassSerreTreeIsoPoint PUnit.unit⟩, inferInstance, inferInstance⟩

end Edgeless

/-! #### 2. Free products and `ℤ ∗ ℤ` (`bassSerreTree_free_product`) -/

section FreeProduct

/-- The one-edge graph of groups of a free product `A ∗ B`: the segment with vertex groups `A` at
`false` and `B` at `true` and trivial edge group `PUnit`. -/
@[expose] def freeProductGraph (A B : Type w) [Group A] [Group B] :
    GraphOfGroups.{0, 0, w, 0} SerreGraph.segment :=
  segment (1 : PUnit →* A) (1 : PUnit →* B) (Function.injective_of_subsingleton _)
    (Function.injective_of_subsingleton _)

@[instance_reducible]
private def segmentStarFalseUnique (v₀ : SerreGraph.segment.V) (hv₀ : v₀ = false) :
    Unique {e : SerreGraph.segment.E // SerreGraph.segment.src e = v₀} where
  default := ⟨false, hv₀.symm⟩
  uniq := by
    subst hv₀
    rintro ⟨b, hb⟩
    cases b
    · rfl
    · cases hb

/-- In the Bass–Serre tree of `A ∗ B`, the outgoing darts at the base vertex `1 · A` correspond
bijectively to the elements of `A`. -/
noncomputable def freeProductStarEquiv (A B : Type w) [Group A] [Group B] :
    {E : ((freeProductGraph A B).bassSerreTree false).E //
      ((freeProductGraph A B).bassSerreTree false).src E =
        (freeProductGraph A B).bassSerreBaseVertex false} ≃ A := by
  let v₀ : SerreGraph.segment.V := false
  let v₁ : SerreGraph.segment.V := true
  let e₀ : SerreGraph.segment.E := false
  refine (((freeProductGraph A B).bassSerreStarEquiv v₀ .nil).trans
    (@Equiv.uniqueSigma _ _ (segmentStarFalseUnique v₀ rfl))).trans ?_
  have hbot : ((freeProductGraph A B).αArrow (⟨e₀, rfl, rfl⟩ : v₀ ⟶ v₁)).range =
      (⊥ : Subgroup A) :=
    (congrArg (fun f : PUnit →* A => f.range)
      (((freeProductGraph A B).αArrow_mk e₀).trans
        (segment_α_false (1 : PUnit →* A) (1 : PUnit →* B) _ _))).trans
      MonoidHom.range_one
  exact (Subgroup.quotientEquivOfEq hbot).trans (QuotientGroup.quotientEquivSelf A)

/-- In the Bass–Serre tree of `A ∗ B`, the neighbours of the base vertex `1 · A` correspond
bijectively to `A` via `a ↦ (a · e) B`. -/
noncomputable def freeProductAdjacentEquiv (A B : Type w) [Group A] [Group B] :
    A ≃ {w : ((freeProductGraph A B).bassSerreTree false).V //
      Nonempty ((freeProductGraph A B).bassSerreBaseVertex false ⟶ w)} :=
  (freeProductStarEquiv A B).symm.trans (treeStarEquivAdjacent _)

@[simp] theorem freeProductAdjacentEquiv_apply (A B : Type w) [Group A] [Group B] (a : A) :
    (freeProductAdjacentEquiv A B a).1 =
      (freeProductGraph A B).bassSerreVertex false
        ((Path.ofVertex a).cons (Letter.dart (SerreGraph.segment.dart false))) := by
  let v₀ : SerreGraph.segment.V := false
  let e₀ : SerreGraph.segment.E := false
  let a' : (freeProductGraph A B).vertexGroup (SerreGraph.segment.src e₀) := a
  have h1 : ((freeProductStarEquiv A B).symm a).1 =
      (freeProductGraph A B).bassSerreDartOfSrcEq v₀ e₀
        (segmentStarFalseUnique v₀ rfl).default.2 (Quiver.Path.nil.cons (Letter.vertex a')) := rfl
  have h2 : (segmentStarFalseUnique v₀ rfl).default.2 = (rfl : SerreGraph.segment.src e₀ = v₀) :=
    Subsingleton.elim _ _
  have h3 : ((freeProductStarEquiv A B).symm a).1 =
      (freeProductGraph A B).bassSerreDart v₀ e₀ (Path.ofVertex a') := by
    refine h1.trans ((congrArg (fun h => (freeProductGraph A B).bassSerreDartOfSrcEq v₀ e₀ h _)
      h2).trans ?_)
    exact congrArg ((freeProductGraph A B).bassSerreDart v₀ e₀)
      (Path.ofVertex_eq_nil_cons a').symm
  exact congrArg ((freeProductGraph A B).bassSerreTree v₀).tgt h3

/-- For `ℤ ∗ ℤ`, the base vertex `⟨a⟩` in the Bass–Serre tree has neighbours `a^k ⟨b⟩` indexed
bijectively by `k ∈ ℤ`, and its degree is `ℵ₀`. -/
theorem bassSerreTree_free_product :
    let F2 := freeProductGraph (Multiplicative ℤ) (Multiplicative ℤ)
    (∃ equiv : ℤ ≃ {w : (F2.bassSerreTree false).V //
          Nonempty (F2.bassSerreBaseVertex false ⟶ w)},
      ∀ k : ℤ, (equiv k).1 = F2.bassSerreVertex false
        ((Path.ofVertex (Multiplicative.ofAdd k)).cons
          (Letter.dart (SerreGraph.segment.dart false)))) ∧
    Cardinal.mk {E : (F2.bassSerreTree false).E //
      (F2.bassSerreTree false).src E = F2.bassSerreBaseVertex false} =
      Cardinal.aleph0 := by
  refine ⟨⟨Multiplicative.ofAdd.trans
      (freeProductAdjacentEquiv (Multiplicative ℤ) (Multiplicative ℤ)), fun k =>
      freeProductAdjacentEquiv_apply (Multiplicative ℤ) (Multiplicative ℤ)
        (Multiplicative.ofAdd k)⟩, ?_⟩
  rw [Cardinal.mk_congr ((freeProductStarEquiv (Multiplicative ℤ) (Multiplicative ℤ)).trans
    Multiplicative.toAdd), Cardinal.mk_int]

end FreeProduct

/-! #### 3. Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)` (`bassSerreTree_BS12`) -/

section BaumslagSolitar

private theorem zpowGroupHom_injective_int {m : ℤ} (hm : m ≠ 0) :
    Function.Injective (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ) :=
  fun _ _ h => Multiplicative.toAdd.injective <| mul_left_cancel₀ hm <|
    (smul_eq_mul _ _).symm.trans ((congrArg Multiplicative.toAdd h).trans (smul_eq_mul _ _))

private theorem index_range_zpowGroupHom_int (m : ℤ) :
    (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range.index = m.natAbs := by
  let g : Multiplicative ℤ := Multiplicative.ofAdd 1
  have hg_top : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ =>
    ⟨Multiplicative.toAdd x, by
      apply Multiplicative.toAdd.injective
      simp [g, toAdd_zpow]⟩
  have hrange : (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range =
      Subgroup.zpowers (g ^ m) := by
    ext x
    simp only [MonoidHom.mem_range, zpowGroupHom_apply, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨y, hy⟩ => ⟨Multiplicative.toAdd y, ?_⟩,
      fun ⟨k, hk⟩ => ⟨Multiplicative.ofAdd k, ?_⟩⟩
    · rw [← hy, ← zpow_mul]
      apply Multiplicative.toAdd.injective
      simp [g, toAdd_zpow, mul_comm]
    · rw [← hk, ← zpow_mul]
      apply Multiplicative.toAdd.injective
      simp [g, toAdd_zpow]
  have hord : orderOf g = 0 := orderOf_eq_zero_iff'.mpr fun n hn hgn => by
    have h0 : (n : ℤ) = 0 := by simpa [g, toAdd_pow] using congrArg Multiplicative.toAdd hgn
    omega
  rw [hrange, Subgroup.index_zpowers_zpow hg_top m, hord]
  simp

/-- The graph of groups of the Baumslag–Solitar group `BS(m, n) = ⟨a, t | t a^m t⁻¹ = a^n⟩` for
nonzero integers `m` and `n`: a single loop with vertex and edge groups `ℤ` and boundary maps `m`
and `n`. -/
@[expose] def baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    GraphOfGroups.{0, 0, 0, 0} (SerreGraph.rose Unit) :=
  loop (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)
    (zpowGroupHom n : Multiplicative ℤ →* Multiplicative ℤ)
    (fun _ _ h => Multiplicative.toAdd.injective <| mul_left_cancel₀ hm <|
      (smul_eq_mul _ _).symm.trans ((congrArg Multiplicative.toAdd h).trans (smul_eq_mul _ _)))
    (fun _ _ h => Multiplicative.toAdd.injective <| mul_left_cancel₀ hn <|
      (smul_eq_mul _ _).symm.trans ((congrArg Multiplicative.toAdd h).trans (smul_eq_mul _ _)))

private def roseDartSign (e : (SerreGraph.rose Unit).E) : Bool := e.2

private theorem index_range_α_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (v₀ : (SerreGraph.rose Unit).V) (e : (SerreGraph.rose Unit).E)
    (hsrc : (SerreGraph.rose Unit).src e = v₀) :
    ((baumslagSolitar m n hm hn).αArrow
      (⟨e, hsrc, rfl⟩ : v₀ ⟶ (SerreGraph.rose Unit).tgt e)).range.index =
      cond (roseDartSign e) m.natAbs n.natAbs := by
  obtain ⟨⟨⟩, b⟩ := e
  cases v₀
  obtain rfl : hsrc = rfl := Subsingleton.elim _ _
  cases b
  · let e₀ : (SerreGraph.rose Unit).E := ((), false)
    exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (((baumslagSolitar m n hm hn).αArrow_mk e₀).trans
        (loop_α_false (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)
          (zpowGroupHom n : Multiplicative ℤ →* Multiplicative ℤ)
          (zpowGroupHom_injective_int hm) (zpowGroupHom_injective_int hn)))).trans
      (index_range_zpowGroupHom_int n)
  · let e₁ : (SerreGraph.rose Unit).E := ((), true)
    exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (((baumslagSolitar m n hm hn).αArrow_mk e₁).trans
        (loop_α_true (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ)
          (zpowGroupHom n : Multiplicative ℤ →* Multiplicative ℤ)
          (zpowGroupHom_injective_int hm) (zpowGroupHom_injective_int hn)))).trans
      (index_range_zpowGroupHom_int m)

/-- Every vertex of the Bass–Serre tree of `BS(m, n)` has finite degree `|m| + |n|`. -/
theorem card_star_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (u : ((baumslagSolitar m n hm hn).bassSerreTree ()).V) :
    Nat.card {E : ((baumslagSolitar m n hm hn).bassSerreTree ()).E //
      ((baumslagSolitar m n hm hn).bassSerreTree ()).src E = u} =
      m.natAbs + n.natAbs := by
  let v₀ : (SerreGraph.rose Unit).V := ()
  refine bassSerreVertex_induction u fun {v} p => ?_
  obtain rfl : v = v₀ := rfl
  let starRoseEquivBool :
      {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀} ≃ Bool :=
    { toFun := fun e => roseDartSign e.1
      invFun := fun b => ⟨((), b), rfl⟩
      left_inv := fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl
      right_inv := fun _ => rfl }
  let instFintype : Fintype {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀} :=
    Fintype.ofEquiv Bool starRoseEquivBool.symm
  have instFinite : ∀ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀},
      Finite ((baumslagSolitar m n hm hn).vertexGroup v₀ ⧸
        ((baumslagSolitar m n hm hn).αArrow ⟨e.1, e.2, rfl⟩).range) := by
    intro e
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card, index_range_α_baumslagSolitar m n hm hn v₀ e.1 e.2]
    cases roseDartSign e.1
    · exact Int.natAbs_ne_zero.mpr hn
    · exact Int.natAbs_ne_zero.mpr hm
  rw [@card_bassSerreStar _ (baumslagSolitar m n hm hn) v₀ v₀ instFintype instFinite p]
  have hcongr : ∀ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀},
      ((baumslagSolitar m n hm hn).αArrow ⟨e.1, e.2, rfl⟩).range.index =
        cond (starRoseEquivBool e) m.natAbs n.natAbs :=
    fun e => index_range_α_baumslagSolitar m n hm hn v₀ e.1 e.2
  simp_rw [hcongr]
  exact (Equiv.sum_comp starRoseEquivBool (fun b => cond b m.natAbs n.natAbs)).trans
    (Fintype.sum_bool _)

/-- For `BS(1, 2)`, the boundary images have indices `[A : α(C)] = 1` and `[A : ω(C)] = 2`, and
every vertex of the Bass–Serre tree has degree `3`. -/
theorem bassSerreTree_BS12 :
    let BS := baumslagSolitar 1 2 one_ne_zero two_ne_zero
    (BS.α (((), true) : (SerreGraph.rose Unit).E)).range.index = 1 ∧
      (BS.ω (((), true) : (SerreGraph.rose Unit).E)).range.index = 2 ∧
      ∀ u : (BS.bassSerreTree ()).V,
        Nat.card {E : (BS.bassSerreTree ()).E // (BS.bassSerreTree ()).src E = u} = 3 := by
  refine ⟨?_, ?_, fun u => card_star_baumslagSolitar 1 2 one_ne_zero two_ne_zero u⟩
  · exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (loop_α_true (zpowGroupHom 1 : Multiplicative ℤ →* Multiplicative ℤ)
        (zpowGroupHom 2 : Multiplicative ℤ →* Multiplicative ℤ)
        (zpowGroupHom_injective_int one_ne_zero)
        (zpowGroupHom_injective_int two_ne_zero))).trans
      (index_range_zpowGroupHom_int 1)
  · exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (loop_ω_true (zpowGroupHom 1 : Multiplicative ℤ →* Multiplicative ℤ)
        (zpowGroupHom 2 : Multiplicative ℤ →* Multiplicative ℤ)
        (zpowGroupHom_injective_int one_ne_zero)
        (zpowGroupHom_injective_int two_ne_zero))).trans
      (index_range_zpowGroupHom_int 2)

end BaumslagSolitar

/-! #### 4. Unquotiented homotopy classes of based `𝔸`-paths (`bassSerreTree_not_quotient_paths`) -/

section UnquotientedPaths

/-- A based `𝔸`-path starting at `v₀` up to homotopy, without quotienting on the right by the
terminal vertex group `A_v`. -/
structure HomotopyPathFrom : Type (max u v w) where
  /-- The endpoint vertex in `Γ`. -/
  vertex : Γ.V
  /-- The homotopy class of the `𝔸`-path from `v₀` to `vertex`. -/
  pathClass : Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨vertex⟩)

noncomputable instance : MulAction (π₁ 𝔸 v₀) (𝔸.HomotopyPathFrom v₀) where
  smul g x := ⟨x.vertex, π₁.lift (fun s => Quotient.lift (fun p => Quotient.mk _ (s.comp p))
      fun _ _ hp => Quotient.sound (Path.Homotopic.comp_left hp s))
    (fun _ _ hs => funext fun q => Quotient.inductionOn q fun p =>
      Quotient.sound (Path.Homotopic.comp_right hs p)) g x.pathClass⟩
  one_smul := fun ⟨v, q⟩ => Quotient.inductionOn q fun p => by
    simp [HSMul.hSMul, SMul.smul, ← π₁.mk_nil]
  mul_smul g h := fun ⟨v, q⟩ => π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    Quotient.inductionOn q fun p => by
      simp [HSMul.hSMul, SMul.smul, ← π₁.mk_comp]

/-- Without the right-coset relation `≈`, homotopy classes of based `𝔸`-paths carry a distinct
point `⟦ofVertex a⟧` at `v₀` for every `a ∈ A_{v₀}`, and the empty path has trivial stabilizer
under `π₁(𝔸, v₀)` instead of `(π₁.vertexHom nil).range ≅ A_{v₀}`. -/
theorem bassSerreTree_not_quotient_paths :
    Function.Injective (fun a : 𝔸.vertexGroup v₀ =>
      (⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex a)⟩ :
        𝔸.HomotopyPathFrom v₀)) ∧
    stabilizer (π₁ 𝔸 v₀)
      (⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil⟩ :
        𝔸.HomotopyPathFrom v₀) = ⊥ := by
  refine ⟨fun a b hab => ?_, eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_⟩
  · have hq : Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex a) =
        Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex b) := by
      injection hab
    exact Path.ofVertex_homotopic_ofVertex_iff.mp (Quotient.exact hq)
  · refine π₁.induction_on (P := fun g => g ∈ stabilizer (π₁ 𝔸 v₀) _ → g = 1) g (fun s hs => ?_) hg
    rw [mem_stabilizer_iff] at hs
    have hq : Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (s.comp Quiver.Path.nil) =
        Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil := by
      have hs' : (⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (s.comp Quiver.Path.nil)⟩ :
          𝔸.HomotopyPathFrom v₀) = ⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil⟩ := by
        simpa [HSMul.hSMul, SMul.smul] using hs
      injection hs'
    rw [Quiver.Path.comp_nil] at hq
    exact π₁.mk_eq_mk_iff.mpr (Quotient.exact hq)

end UnquotientedPaths

/-! #### 5. Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- The graph of groups on two isolated vertices (`false` and `true`) with trivial vertex groups. -/
@[expose] def twoIsolated :
    GraphOfGroups.{0, 0, 0, 0} (SerreGraph.segment.restrict ∅ fun _ h => h.elim) :=
  (freeProductGraph PUnit PUnit).restrict ∅ (fun _ h => h.elim)

private instance : IsEmpty (SerreGraph.segment.restrict ∅ fun _ h => h.elim).E :=
  ⟨fun e => e.2.elim⟩

/-- Over two isolated vertices with basepoint at `false`, both the Bass–Serre tree `X` and its
quotient `X / π₁` have a single vertex, whereas the ambient graph has two vertices and no `𝔸`-path
connects `false` to `true` (so §4.2 supplies no based `π₁.vertexHom` for `true`). -/
theorem bassSerreTree_two_isolated :
    Nat.card (twoIsolated.bassSerreTree false).V = 1 ∧
      Nat.card (twoIsolated.bassSerreQuotient false).V = 1 ∧
      Nat.card (SerreGraph.segment.restrict ∅ fun _ h => h.elim).V = 2 ∧
      IsEmpty (twoIsolated.Path ⟨false⟩ ⟨true⟩) := by
  let Γ₀ := SerreGraph.segment.restrict ∅ fun _ h => h.elim
  let b₀ : Γ₀.V := false
  have hTreeCard : Nat.card (twoIsolated.bassSerreTree b₀).V = 1 := Nat.card_unique
  have hCompCard : Nat.card (Γ₀.component b₀).V = 1 := Nat.card_unique
  have hQuotCard : Nat.card (twoIsolated.bassSerreQuotient b₀).V = 1 :=
    (Nat.card_congr (twoIsolated.bassSerreQuotientIso b₀).equivV).trans hCompCard
  have hAmbCard : Nat.card Bool = 2 := by simp
  have hempty : IsEmpty (twoIsolated.Path ⟨false⟩ ⟨true⟩) := by
    refine ⟨fun p => ?_⟩
    have aux : ∀ {y : twoIsolated.LetterVertex}, twoIsolated.Path ⟨false⟩ y → y = ⟨false⟩ := by
      intro y q
      induction q with
      | nil => rfl
      | cons _ l ih =>
        cases l with
        | vertex _ => exact ih
        | dart e => exact e.1.2.elim
    cases aux p
  exact ⟨hTreeCard, hQuotCard, hAmbCard, hempty⟩

end Disconnected

end GraphOfGroups

end TauCeti
