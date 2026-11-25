/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm
public import TauCeti.GroupTheory.GTree.Basic
public import Mathlib.Algebra.Group.Action.Sigma

/-!
# The Bass–Serre tree of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ` and let `a` be a vertex of `Γ`. The
Bass–Serre tree `X(𝔸, a)` has

* a vertex `p A_b` for every `𝔸`-path `p` from `a` to a vertex `b`, two paths `p` and `q` giving
  the same vertex when `q` is homotopic to `p g` for some `g ∈ A_b`;
* a dart `p α_e(A_e)` from `p A_b` to `p e A_c` for every `𝔸`-path `p` from `a` to `b` and every
  dart `e : b ⟶ c` of `Γ`, two paths `p` and `q` giving the same dart when `q` is homotopic to
  `p α_e(c₀)` for some `c₀ ∈ A_e`. Its reverse is the dart `p e ω_e(A_e)` of `rev e`.

The fundamental group `π₁(𝔸, a)` of closed `𝔸`-paths at `a` acts on it by concatenation on the
left. The action has no inversions, since it does not change the dart of `Γ` underlying a dart.

The graph `X(𝔸, a)` is a tree. It is connected because an `𝔸`-path from `a` is read letter by
letter as a path of `X(𝔸, a)` from the vertex `A_a` of the empty path. It has no reduced closed
paths because a reduced path of length `k` in `X(𝔸, a)` starting at `p A_b` is read off a reduced
alternating `𝔸`-path `g₀, e₁, g₁, …, e_k, g_k` from `b`: the darts of `X(𝔸, a)` along it are the
`p g₀ e₁ ⋯ g_{i-1} α_{e_i}(A_{e_i})`. For a closed path this alternating path is homotopic to a
vertex group element, which by the normal form theorem forces `k = 0`.

The stabilizer of the vertex `p A_b` is the conjugate `p A_b p⁻¹` of the vertex group, and the
stabilizer of the dart `p α_e(A_e)` is the conjugate `p α_e(A_e) p⁻¹` of the edge group. Over a
graph without edges, every `𝔸`-path from `a` is homotopic to an element of `A_a`, so `X(𝔸, a)` is a
single vertex with no darts. When all vertex groups are trivial, the vertices of `X(𝔸, a)`
correspond bijectively to reduced edge paths of `Γ` starting at `a`.

Sending `p A_b` to `b` and `p α_e(A_e)` to `e` projects `X(𝔸, a)` onto `Γ` and onto the connected
component `Γ.component a`, and `π₁(𝔸, a)` acts transitively on each fibre: `q p⁻¹` carries `p A_b`
to `q A_b`. Hence the quotient graph `X(𝔸, a) / π₁(𝔸, a)` is canonically isomorphic to
`Γ.component a` (`bassSerreQuotientIsoComponent`), and to `Γ` when `Γ` is preconnected
(`bassSerreQuotientIso`).

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre tree `X(𝔸, a)`, a tree for `π₁(𝔸, a)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreDart`: the vertex
  `p A_b` and dart `p α_e(A_e)`, with eliminators `bassSerreVertexLift`, `bassSerreDartLift`,
  `bassSerreVertex_induction_on`, and `bassSerreDart_induction_on`.
* `TauCeti.GraphOfGroups.HomotopyPathFrom.toBassSerreVertex`: the quotient map from homotopy
  classes of based `𝔸`-paths at `a` to vertices of `X(𝔸, a)`.
* `TauCeti.GraphOfGroups.bassSerreProjection`,
  `TauCeti.GraphOfGroups.bassSerreProjectionComponent`: projections to `Γ` and `Γ.component a`.
* `TauCeti.GraphOfGroups.bassSerreQuotientHom`,
  `TauCeti.GraphOfGroups.bassSerreQuotientHomComponent`,
  `TauCeti.GraphOfGroups.bassSerreQuotientIsoComponent`,
  `TauCeti.GraphOfGroups.bassSerreQuotientIso`: morphisms and isomorphisms from the quotient graph
  `X(𝔸, a) / π₁(𝔸, a)` to `Γ.component a` and (for preconnected `Γ`) to `Γ`.
* `TauCeti.GraphOfGroups.bassSerreVertexEquivReducedPath`: bijection between `(bassSerreTree 𝔸 a).V`
  and reduced edge paths of `Γ` from `a` when all vertex groups are trivial.

## Main results

* `TauCeti.GraphOfGroups.bassSerreVertex_eq_bassSerreVertex_iff`,
  `TauCeti.GraphOfGroups.bassSerreDart_eq_bassSerreDart_iff`: when two paths give the same vertex
  or dart.
* `TauCeti.GraphOfGroups.HomotopyPathFrom.not_injective_toBassSerreVertex`: when a reachable vertex
  group is nontrivial, `toBassSerreVertex` is not injective.
* `TauCeti.GraphOfGroups.src_bassSerreDart`, `TauCeti.GraphOfGroups.rev_bassSerreDart`,
  `TauCeti.GraphOfGroups.tgt_bassSerreDart`: the incidence of the tree.
* `TauCeti.GraphOfGroups.smul_bassSerreVertex`, `TauCeti.GraphOfGroups.smul_bassSerreDart`,
  `TauCeti.GraphOfGroups.vertexHom_smul_bassSerreVertex`,
  `TauCeti.GraphOfGroups.vertexHom_smul_bassSerreVertex_cons_dart`: the action of `π₁(𝔸, a)`.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreVertex`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart_cons_vertex`,
  `TauCeti.GraphOfGroups.isRelative_bassSerreTree`: vertex and dart stabilizers and relativity.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreTree_vertex_eq_bot`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreTree_dart_eq_bot`: trivial vertex or edge groups give
  trivial stabilizers.
* `TauCeti.GraphOfGroups.vertexHom_smul_bassSerreDart_eq_self_iff`,
  `TauCeti.GraphOfGroups.vertexHom_cons_smul_bassSerreDart_eq_self_iff`: which elements of the
  stabilizers of the endpoints of a dart fix the dart.
* `TauCeti.GraphOfGroups.exists_smul_bassSerreVertex_eq`,
  `TauCeti.GraphOfGroups.exists_smul_bassSerreDart_eq`: the action is transitive on the fibres of
  the projection to `Γ`.
* `TauCeti.GraphOfGroups.bassSerreQuotientHom_mapV_injective`,
  `TauCeti.GraphOfGroups.bassSerreQuotientHom_mapE_injective`,
  `TauCeti.GraphOfGroups.range_bassSerreQuotientHom_mapV`,
  `TauCeti.GraphOfGroups.range_bassSerreQuotientHom_mapE`: the quotient graph is the connected
  component of `a` in `Γ`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ}

/-! ### Cosets of paths -/

section PathCoset

variable (𝔸) (a : Γ.V) {b : Γ.V} (H : Subgroup (𝔸.vertexGroup b))

/-- Two `𝔸`-paths `p` and `q` from `a` to `b` are related when `q` is homotopic to `p h` for some
element `h` of a subgroup `H` of `A_b`. -/
private def pathCosetSetoid : Setoid (𝔸.Path ⟨a⟩ ⟨b⟩) where
  r p q := ∃ h ∈ H, q.Homotopic (p.cons (.vertex h))
  iseqv := {
    refl p := ⟨1, H.one_mem, (Path.Homotopic.one p).symm⟩
    symm := by
      rintro p q ⟨h, hH, hq⟩
      -- `p ~ p h h⁻¹ ~ q h⁻¹`.
      have hp := Path.Homotopic.cons_cons_reverse p (.vertex h)
      rw [Letter.reverse_vertex] at hp
      exact ⟨h⁻¹, H.inv_mem hH, hp.symm.trans (hq.symm.cons _)⟩
    trans := by
      rintro p q r ⟨h, hH, hq⟩ ⟨k, hK, hr⟩
      exact ⟨h * k, H.mul_mem hH hK, hr.trans ((hq.cons _).trans (Path.Homotopic.mul p h k))⟩ }

/-- The `𝔸`-paths from `a` to `b` modulo homotopy and right multiplication by a subgroup `H` of
`A_b`: the cosets `p H`. -/
private def PathCoset : Type (max u v w) := Quotient (pathCosetSetoid 𝔸 a H)

namespace PathCoset

variable {𝔸 a H}

/-- The coset `p H` of an `𝔸`-path `p`. -/
private def mk (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : PathCoset 𝔸 a H := Quotient.mk _ p

private theorem mk_surjective : Function.Surjective (mk : 𝔸.Path ⟨a⟩ ⟨b⟩ → PathCoset 𝔸 a H) :=
  Quotient.mk_surjective

private theorem mk_eq_mk_iff {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} :
    (mk p : PathCoset 𝔸 a H) = mk q ↔ ∃ h ∈ H, q.Homotopic (p.cons (.vertex h)) :=
  Quotient.eq

private theorem mk_eq_mk_of_homotopic {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (hpq : p.Homotopic q) :
    (mk p : PathCoset 𝔸 a H) = mk q :=
  mk_eq_mk_iff.2 ⟨1, H.one_mem, hpq.symm.trans (Path.Homotopic.one p).symm⟩

/-- Enlarging the subgroup: `p H ↦ p K` for `H ≤ K`. -/
private def map {K : Subgroup (𝔸.vertexGroup b)} (hHK : H ≤ K) :
    PathCoset 𝔸 a H → PathCoset 𝔸 a K :=
  Quotient.map id fun _ _ ⟨h, hH, hq⟩ ↦ ⟨h, hHK hH, hq⟩

private theorem map_mk {K : Subgroup (𝔸.vertexGroup b)} (hHK : H ≤ K) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    map hHK (mk p : PathCoset 𝔸 a H) = mk p :=
  (rfl)

/-- Crossing a dart `e : b ⟶ c`: `p α_e(A_e) ↦ p e ω_e(A_e)`, where `ω_e(A_e) = α_{rev e}(A_e)`. -/
private def consDart {c : Γ.V} (e : b ⟶ c) :
    PathCoset 𝔸 a (𝔸.αArrow e).range → PathCoset 𝔸 a (𝔸.αArrow (Quiver.reverse e)).range :=
  Quotient.map (fun p ↦ p.cons (.dart e)) fun p q ⟨_, ⟨c₀, hc₀⟩, hq⟩ ↦ by
    -- `q e ~ p α_e(c₀) e ~ p e ω_e(c₀)`.
    subst hc₀
    refine ⟨𝔸.ωArrow e c₀, (𝔸.range_αArrow_reverse e).symm ▸ ⟨c₀, rfl⟩, ?_⟩
    exact (hq.cons _).trans (Path.Homotopic.dart_ωArrow p e c₀).symm

private theorem consDart_mk {c : Γ.V} (e : b ⟶ c) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    consDart e (mk p) = mk (p.cons (.dart e)) :=
  (rfl)

private instance : SMul (π₁ 𝔸 a) (PathCoset 𝔸 a H) where
  smul := π₁.lift (fun γ ↦ Quotient.map (γ.comp ·) fun _ _ ⟨h, hH, hq⟩ ↦ ⟨h, hH, hq.comp_left γ⟩)
    fun _ _ hγ ↦ funext fun x ↦ Quotient.inductionOn x fun p ↦
      mk_eq_mk_of_homotopic (hγ.comp_right p)

private theorem smul_mk (γ : 𝔸.Path ⟨a⟩ ⟨a⟩) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    π₁.mk γ • (mk p : PathCoset 𝔸 a H) = mk (γ.comp p) :=
  congrFun (π₁.lift_mk _ _ γ) (mk p)

private instance : MulAction (π₁ 𝔸 a) (PathCoset 𝔸 a H) where
  one_smul y := by
    obtain ⟨p, rfl⟩ := mk_surjective y
    rw [← π₁.mk_nil, smul_mk, Quiver.Path.nil_comp]
  mul_smul g g' y := π₁.induction_on g fun γ ↦ π₁.induction_on g' fun δ ↦ by
    obtain ⟨p, rfl⟩ := mk_surjective y
    rw [← π₁.mk_comp, smul_mk, smul_mk, smul_mk, Quiver.Path.comp_assoc]

private theorem map_smul {K : Subgroup (𝔸.vertexGroup b)} (hHK : H ≤ K) (g : π₁ 𝔸 a)
    (y : PathCoset 𝔸 a H) : map hHK (g • y) = g • map hHK y :=
  π₁.induction_on g fun _ ↦ by
    obtain ⟨p, rfl⟩ := mk_surjective y
    rw [smul_mk, map_mk, map_mk, smul_mk]

private theorem consDart_smul {c : Γ.V} (e : b ⟶ c) (g : π₁ 𝔸 a)
    (y : PathCoset 𝔸 a (𝔸.αArrow e).range) : consDart e (g • y) = g • consDart e y :=
  π₁.induction_on g fun _ ↦ by
    obtain ⟨p, rfl⟩ := mk_surjective y
    rw [smul_mk, consDart_mk, consDart_mk, smul_mk, Quiver.Path.comp_cons]

/-- The stabilizer of the coset `p H` is the conjugate `p H p⁻¹`. -/
private theorem stabilizer_mk (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    stabilizer (π₁ 𝔸 a) (mk p : PathCoset 𝔸 a H) = H.map (π₁.vertexHom p) := by
  ext g
  induction g using π₁.induction_on with | h γ => ?_
  rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_mk_iff, Subgroup.mem_map]
  refine exists_congr fun h ↦ and_congr_right fun _ ↦ ?_
  rw [π₁.vertexHom_apply, π₁.mk_eq_mk_iff, Path.comp_ofVertex]
  -- `γ p ~ p h` exactly when `γ ~ p h p⁻¹`.
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ ?_⟩
  · exact (hγ.comp_right p.reverse).symm.trans (Path.Homotopic.comp_comp_reverse γ p)
  · exact (hγ.symm.comp_right p).trans
      (Path.Homotopic.comp_reverse_comp (p.cons (.vertex h)) p)

end PathCoset

end PathCoset

/-! ### The Bass–Serre graph -/

section Graph

variable (𝔸) (a : Γ.V)

/-- The vertices of the Bass–Serre graph: the cosets `p A_b`. -/
private abbrev BSVertex : Type (max u v w) :=
  Σ b : Γ.V, PathCoset 𝔸 a (⊤ : Subgroup (𝔸.vertexGroup b))

/-- The darts of the Bass–Serre graph: the cosets `p α_e(A_e)`. -/
private abbrev BSDart : Type (max u v w) :=
  Σ (b c : Γ.V) (e : b ⟶ c), PathCoset 𝔸 a (𝔸.αArrow e).range

variable {𝔸 a}

/-- The source `p A_b` of the dart `p α_e(A_e)`. -/
private def BSDart.src (d : BSDart 𝔸 a) : BSVertex 𝔸 a := ⟨d.1, d.2.2.2.map le_top⟩

/-- The reverse `p e ω_e(A_e)` of the dart `p α_e(A_e)`. -/
private def BSDart.rev (d : BSDart 𝔸 a) : BSDart 𝔸 a :=
  ⟨d.2.1, d.1, Quiver.reverse d.2.2.1, d.2.2.2.consDart d.2.2.1⟩

private theorem BSDart.rev_rev (d : BSDart 𝔸 a) : d.rev.rev = d := by
  obtain ⟨b, c, e, y⟩ := d
  obtain ⟨p, rfl⟩ := PathCoset.mk_surjective y
  simp only [BSDart.rev, PathCoset.consDart_mk]
  have hp := Path.Homotopic.cons_cons_reverse p (.dart e)
  rw [Letter.reverse_dart] at hp
  -- Transport along `reverse (reverse e) = e`, then cancel `e, rev e`.
  generalize hf : Quiver.reverse (Quiver.reverse e) = f
  rw [Quiver.reverse_reverse] at hf
  subst hf
  exact congrArg (fun y ↦ (⟨b, c, e, y⟩ : BSDart 𝔸 a)) (PathCoset.mk_eq_mk_of_homotopic hp)

variable (𝔸 a)

/-- The Bass–Serre graph: vertices are the cosets `p A_b` and darts the cosets `p α_e(A_e)`. -/
private def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := BSVertex 𝔸 a
  E := BSDart 𝔸 a
  src := BSDart.src
  rev := BSDart.rev
  rev_rev := BSDart.rev_rev
  rev_ne d h :=
    Γ.rev_ne d.2.2.1.val ((Γ.reverse_val _).symm.trans (congrArg (fun d ↦ d.2.2.1.val) h))

variable {𝔸 a}

/-- The vertex `p A_b` of an `𝔸`-path `p` from `a` to `b`. -/
private def bsVertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : BSVertex 𝔸 a := ⟨b, PathCoset.mk p⟩

/-- The dart `p α_e(A_e)` of an `𝔸`-path `p` from `a` to `b` and a dart `e : b ⟶ c`. -/
private def bsDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) : BSDart 𝔸 a :=
  ⟨b, c, e, PathCoset.mk p⟩

private theorem src_bsDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreGraph 𝔸 a).src (bsDart p e) = bsVertex p :=
  (rfl)

private theorem rev_bsDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreGraph 𝔸 a).rev (bsDart p e) = bsDart (p.cons (.dart e)) (Quiver.reverse e) :=
  (rfl)

private theorem tgt_bsDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreGraph 𝔸 a).tgt (bsDart p e) = bsVertex (p.cons (.dart e)) :=
  (rfl)

private theorem bsVertex_surjective (y : BSVertex 𝔸 a) :
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), bsVertex p = y := by
  obtain ⟨b, y⟩ := y
  obtain ⟨p, rfl⟩ := PathCoset.mk_surjective y
  exact ⟨b, p, rfl⟩

private theorem bsDart_surjective (d : BSDart 𝔸 a) :
    ∃ (b c : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c), bsDart p e = d := by
  obtain ⟨b, c, e, y⟩ := d
  obtain ⟨p, rfl⟩ := PathCoset.mk_surjective y
  exact ⟨b, c, p, e, rfl⟩

private theorem eq_of_bsVertex_eq {b c : Γ.V} {p : 𝔸.Path ⟨a⟩ ⟨b⟩} {q : 𝔸.Path ⟨a⟩ ⟨c⟩}
    (h : bsVertex p = bsVertex q) : b = c :=
  congrArg Sigma.fst h

private theorem bsVertex_eq_bsVertex_iff {b : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} :
    bsVertex p = bsVertex q ↔ ∃ g, q.Homotopic (p.cons (.vertex g)) :=
  sigma_mk_injective.eq_iff.trans (PathCoset.mk_eq_mk_iff.trans (by simp))

private theorem bsDart_eq_bsDart_iff {b c : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} {e : b ⟶ c} :
    bsDart p e = bsDart q e ↔ ∃ c₀, q.Homotopic (p.cons (.vertex (𝔸.αArrow e c₀))) :=
  sigma_mk_injective.eq_iff.trans <| sigma_mk_injective.eq_iff.trans <|
    sigma_mk_injective.eq_iff.trans <| PathCoset.mk_eq_mk_iff.trans (by simp)

private theorem bsVertex_congr {b : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic q) :
    bsVertex p = bsVertex q :=
  congrArg (Sigma.mk b) (PathCoset.mk_eq_mk_of_homotopic h)

private theorem bsDart_congr {b c : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic q) (e : b ⟶ c) :
    bsDart p e = bsDart q e :=
  bsDart_eq_bsDart_iff.2 ⟨1, h.symm.trans (by simpa using (Path.Homotopic.one p).symm)⟩

private theorem bsVertex_cons_vertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b) :
    bsVertex (p.cons (.vertex g)) = bsVertex p :=
  (bsVertex_eq_bsVertex_iff.2 ⟨g, .refl _⟩).symm

/-! ### Connectedness -/

/-- Every vertex `p A_b` is joined to the vertex `A_a` of the empty path, by the path of darts read
off the darts of `p`. -/
private theorem nonempty_path_bsVertex :
    ∀ {y : 𝔸.LetterVertex} (p : 𝔸.Path ⟨a⟩ y),
      Nonempty ((bassSerreGraph 𝔸 a).Path (bsVertex (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩))
        (bsVertex p))
  | _, .nil => ⟨.nil⟩
  | _, .cons p (.vertex g) => by
    rw [bsVertex_cons_vertex]
    exact nonempty_path_bsVertex p
  | _, .cons p (.dart e) =>
    ⟨(nonempty_path_bsVertex p).some.cons ⟨bsDart p e, src_bsDart p e, tgt_bsDart p e⟩⟩

private theorem bassSerreGraph_connected : (bassSerreGraph 𝔸 a).Connected := by
  refine (SerreGraph.connected_iff _).2 ⟨⟨bsVertex (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩)⟩,
    SerreGraph.preconnected_of_forall_nonempty_path _ (bsVertex .nil) fun y ↦ ?_⟩
  obtain ⟨b, p, rfl⟩ := bsVertex_surjective y
  exact nonempty_path_bsVertex p

/-! ### Acyclicity -/

/-- If `S ~ q`, `e' : d ⟶ c` and `g' ∈ α_{e'}(A_{e'})`, then the dart `q α_{rev e'}(A_{e'})` is
the reverse of the dart `S (rev e') g' α_{e'}(A_{e'})`: crossing `rev e'`, then `g'`, then `e'`
backtracks. -/
private theorem bsDart_reverse_eq_rev {c d : Γ.V} {q S : 𝔸.Path ⟨a⟩ ⟨c⟩} (hS : S.Homotopic q)
    (e' : d ⟶ c) {g' : 𝔸.vertexGroup d} (hg' : g' ∈ (𝔸.αArrow e').range) :
    bsDart q (Quiver.reverse e') =
      (bassSerreGraph 𝔸 a).rev
        (bsDart ((S.cons (.dart (Quiver.reverse e'))).cons (.vertex g')) e') := by
  obtain ⟨c₁, rfl⟩ := hg'
  obtain ⟨c', -, hω⟩ := 𝔸.exists_αArrow_reverse_eq_and_ωArrow_reverse_eq e' c₁
  rw [rev_bsDart]
  refine bsDart_eq_bsDart_iff.2 ⟨c', ?_⟩
  -- `S (rev e') ω_{rev e'}(c') e' ~ S α_{rev e'}(c') (rev e') e' ~ S α_{rev e'}(c')`.
  have hback := Path.Homotopic.dart_reverse (S.cons (.vertex (𝔸.αArrow (Quiver.reverse e') c')))
    (Quiver.reverse e')
  rw [Quiver.reverse_reverse] at hback
  rw [← hω]
  exact (((Path.Homotopic.dart_ωArrow S _ c').cons _).trans hback).trans (hS.cons _)

/-- A reduced path of the Bass–Serre graph of length `k` from `p A_b` is read off a reduced
alternating path `r` of length `k` from `b`: it ends at `p r A_c`. Moreover, if appending to `r`
the elements `g` and `e` would backtrack, then the path ends with the reverse of the dart
`p r g α_e(A_e)`. -/
private theorem exists_alternatingPath_of_isReduced {x y : (bassSerreGraph 𝔸 a).V}
    (P : (bassSerreGraph 𝔸 a).Path x y) (hP : SerreGraph.Path.IsReduced _ P) {b : Γ.V}
    (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (hx : x = bsVertex p) :
    ∃ (c : Γ.V) (r : 𝔸.AlternatingPath b c), r.IsReduced ∧ r.length = P.length ∧
      y = bsVertex (p.comp r.toPath) ∧
      ∀ (d : Γ.V) (e : c ⟶ d) (g : 𝔸.vertexGroup c), (r.setLast (r.last * g)).Cancels e →
        ∃ (y₀ : (bassSerreGraph 𝔸 a).V) (P₀ : (bassSerreGraph 𝔸 a).Path x y₀) (f : y₀ ⟶ y),
          P = P₀.cons f ∧
            f.val = (bassSerreGraph 𝔸 a).rev (bsDart (p.comp (r.setLast (r.last * g)).toPath) e)
                := by
  induction P with
  | nil =>
    refine ⟨b, .single 1, AlternatingPath.isReduced_single 1, by simp, ?_,
      fun d e g hc ↦ by simp at hc⟩
    rw [hx, AlternatingPath.toPath_single, Path.comp_ofVertex, bsVertex_cons_vertex]
  | cons P f ih =>
    obtain ⟨c, r, hr, hlen, hy, hgood⟩ := ih (SerreGraph.Path.IsReduced.of_cons _ hP)
    obtain ⟨c', d, q, e, hf⟩ := bsDart_surjective f.val
    have hsrc : bsVertex q = bsVertex (p.comp r.toPath) := by
      rw [← hy, ← f.property.1, ← hf, src_bsDart]
    obtain rfl := eq_of_bsVertex_eq hsrc
    obtain ⟨g, hq⟩ := bsVertex_eq_bsVertex_iff.1 hsrc.symm
    have hS : Path.Homotopic (p.comp (r.setLast (r.last * g)).toPath) q :=
      ((AlternatingPath.toPath_setLast_mul_homotopic r g).comp_left p).trans hq.symm
    refine ⟨d, (r.setLast (r.last * g)).cons e 1,
      (AlternatingPath.isReduced_cons_iff _ _ _).2 ⟨(r.isReduced_setLast _).2 hr, fun hc ↦ ?_⟩,
      by simp [hlen], ?_, fun d' e' g' hc ↦ ⟨_, P, f, rfl, ?_⟩⟩
    · -- Backtracking in `r` would make the path backtrack at its last two darts.
      obtain ⟨y₀, P₀, f₀, rfl, hf₀⟩ := hgood d e g hc
      rw [bsDart_congr hS, hf] at hf₀
      exact ((SerreGraph.Path.isReduced_cons_cons _ _ _ _).1 hP).2
        (by rw [hf₀, SerreGraph.rev_rev])
    · rw [← f.property.2, ← hf, tgt_bsDart, AlternatingPath.toPath_cons]
      exact (bsVertex_congr (hS.symm.cons _)).trans (bsVertex_cons_vertex _ 1).symm
    · -- Backtracking after the new dart `e` means `e' = rev e`, and the path ends with `e`.
      simp only [AlternatingPath.last_cons, AlternatingPath.setLast_cons, one_mul,
        AlternatingPath.cancels_cons_iff] at hc ⊢
      obtain ⟨h, hg'⟩ := hc
      obtain rfl := Γ.src_eq_tgt_of_val_eq_rev h
      obtain rfl := Γ.eq_reverse_of_val_eq_rev h
      rw [AlternatingPath.toPath_cons]
      exact hf.symm.trans (bsDart_reverse_eq_rev hS e' hg')

private theorem bassSerreGraph_isAcyclic : (bassSerreGraph 𝔸 a).IsAcyclic := by
  refine (SerreGraph.isAcyclic_iff _).2 fun x P hP ↦ ?_
  obtain ⟨b, p, rfl⟩ := bsVertex_surjective x
  obtain ⟨c, r, hr, hlen, hx, -⟩ := exists_alternatingPath_of_isReduced P hP p rfl
  obtain rfl := eq_of_bsVertex_eq hx
  obtain ⟨g, hg⟩ := bsVertex_eq_bsVertex_iff.1 hx
  -- `p r ~ p g`, so `r ~ g`, and by the normal form theorem `r` is the element `g`.
  rw [← Path.comp_ofVertex, Path.Homotopic.comp_left_iff] at hg
  obtain rfl := (AlternatingPath.IsReduced.toPath_homotopic_ofVertex_iff hr).1 hg
  exact Quiver.Path.eq_nil_of_length_zero P (by simpa using hlen.symm)

/-! ### The action -/

private theorem BSDart.src_smul (g : π₁ 𝔸 a) (d : BSDart 𝔸 a) : (g • d).src = g • d.src := by
  obtain ⟨b, c, e, y⟩ := d
  simp only [Sigma.smul_mk, BSDart.src]
  exact congrArg (Sigma.mk b) (PathCoset.map_smul _ g y)

private theorem BSDart.rev_smul (g : π₁ 𝔸 a) (d : BSDart 𝔸 a) : (g • d).rev = g • d.rev := by
  obtain ⟨b, c, e, y⟩ := d
  simp only [Sigma.smul_mk, BSDart.rev]
  exact congrArg (fun z ↦ (⟨c, b, Quiver.reverse e, z⟩ : BSDart 𝔸 a))
    (PathCoset.consDart_smul e g y)

variable (𝔸 a)

/-- The action of `π₁(𝔸, a)` on the Bass–Serre graph by concatenation on the left. -/
private def bassSerreAction : π₁ 𝔸 a →* (bassSerreGraph 𝔸 a).Aut where
  toFun g :=
    { equivV := MulAction.toPerm (β := BSVertex 𝔸 a) g
      equivE := MulAction.toPerm (β := BSDart 𝔸 a) g
      map_src d := BSDart.src_smul g d
      map_rev d := (BSDart.rev_smul g d).symm }
  map_one' := SerreGraph.Iso.ext (fun (y : BSVertex 𝔸 a) ↦ one_smul (π₁ 𝔸 a) y)
    fun (d : BSDart 𝔸 a) ↦ one_smul (π₁ 𝔸 a) d
  map_mul' g g' := SerreGraph.Iso.ext (fun (y : BSVertex 𝔸 a) ↦ mul_smul g g' y)
    fun (d : BSDart 𝔸 a) ↦ mul_smul g g' d

variable {𝔸 a}

/-- `bassSerreAction g` moves the coset `p A_b` to `(g p) A_b`. -/
private theorem bassSerreAction_equivV (g : π₁ 𝔸 a) (y : BSVertex 𝔸 a) :
    (bassSerreAction 𝔸 a g).equivV y = ⟨y.1, g • y.2⟩ := by
  -- By definition, `bassSerreAction g` permutes vertices by `toPerm g`.
  refine (MulAction.toPerm_apply (β := BSVertex 𝔸 a) g y).trans ?_
  obtain ⟨b, y⟩ := y
  rw [Sigma.smul_mk]

/-- `bassSerreAction g` moves the coset `p α_e(A_e)` to `(g p) α_e(A_e)`, over the same dart `e`. -/
private theorem bassSerreAction_equivE (g : π₁ 𝔸 a) (d : BSDart 𝔸 a) :
    (bassSerreAction 𝔸 a g).equivE d = ⟨d.1, d.2.1, d.2.2.1, g • d.2.2.2⟩ := by
  -- By definition, `bassSerreAction g` permutes darts by `toPerm g`.
  refine (MulAction.toPerm_apply (β := BSDart 𝔸 a) g d).trans ?_
  obtain ⟨b, c, e, y⟩ := d
  rw [Sigma.smul_mk, Sigma.smul_mk, Sigma.smul_mk]

variable (𝔸 a)

/-! ### The Bass–Serre tree -/

/-- The Bass–Serre tree `X(𝔸, a)` of a graph of groups `𝔸` at a vertex `a`, a tree for the
fundamental group `π₁(𝔸, a)`. Its vertices are the cosets `p A_b` of `𝔸`-paths `p` from `a` to
`b` (`bassSerreVertex`), its darts the cosets `p α_e(A_e)` for darts `e : b ⟶ c`
(`bassSerreDart`), from `p A_b` to `p e A_c`, and `π₁(𝔸, a)` acts by concatenation on the left. -/
def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 a) where
  toSerreGraph := bassSerreGraph 𝔸 a
  isTree := (SerreGraph.isTree_iff _).2 ⟨bassSerreGraph_connected, bassSerreGraph_isAcyclic⟩
  action := bassSerreAction 𝔸 a
  action_smul_ne_rev g d h := by
    obtain ⟨b, c, e, y⟩ := d
    rw [bassSerreAction_equivE] at h
    -- The action keeps the dart `e` of `Γ` underlying a dart, while reversal (`BSDart.rev`)
    -- reverses it.
    exact Γ.rev_ne e.val
      ((Γ.reverse_val e).symm.trans (congrArg (fun d : BSDart 𝔸 a ↦ d.2.2.1.val) h).symm)

variable {𝔸 a}

/-- The action of `π₁(𝔸, a)` on the vertices of the Bass–Serre tree is its action on the cosets
`p A_b`. -/
private theorem bassSerreTree_smul_vertex (g : π₁ 𝔸 a) (y : (bassSerreTree 𝔸 a).V) :
    g • y = (⟨y.1, g • y.2⟩ : BSVertex 𝔸 a) := by
  rw [GTree.smul_vertex_def, SerreGraph.Aut.smul_vertex_def]
  -- The action of `bassSerreTree` is `bassSerreAction`.
  exact bassSerreAction_equivV g y

/-- The action of `π₁(𝔸, a)` on the darts of the Bass–Serre tree is its action on the cosets
`p α_e(A_e)`. -/
private theorem bassSerreTree_smul_dart (g : π₁ 𝔸 a) (d : (bassSerreTree 𝔸 a).E) :
    g • d = (⟨d.1, d.2.1, d.2.2.1, g • d.2.2.2⟩ : BSDart 𝔸 a) := by
  rw [GTree.smul_dart_def, SerreGraph.Aut.smul_dart_def]
  -- The action of `bassSerreTree` is `bassSerreAction`.
  exact bassSerreAction_equivE g d

/-- The vertex `p A_b` of the Bass–Serre tree given by an `𝔸`-path `p` from `a` to `b`. -/
-- The definitions below are `noncomputable` because the vertex and dart types of `bassSerreTree`,
-- whose body is not exposed, cannot be compiled in importing modules.
noncomputable def bassSerreVertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : (bassSerreTree 𝔸 a).V :=
  bsVertex p

/-- The dart `p α_e(A_e)` of the Bass–Serre tree given by an `𝔸`-path `p` from `a` to `b` and a
dart `e : b ⟶ c` of `Γ`. It goes from `p A_b` to `p e A_c`. -/
noncomputable def bassSerreDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreTree 𝔸 a).E :=
  bsDart p e

/-- Every vertex of the Bass–Serre tree is the coset `p A_b` of an `𝔸`-path. -/
theorem bassSerreVertex_surjective (y : (bassSerreTree 𝔸 a).V) :
    ∃ (b : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩), bassSerreVertex p = y :=
  bsVertex_surjective y

/-- Every dart of the Bass–Serre tree is the coset `p α_e(A_e)` of an `𝔸`-path and a dart. -/
theorem bassSerreDart_surjective (d : (bassSerreTree 𝔸 a).E) :
    ∃ (b c : Γ.V) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c), bassSerreDart p e = d :=
  bsDart_surjective d

/-- Eliminate a property on the vertices of the Bass–Serre tree by checking it on `𝔸`-paths from
`a`. -/
@[elab_as_elim] theorem bassSerreVertex_induction_on {P : (bassSerreTree 𝔸 a).V → Prop}
    (y : (bassSerreTree 𝔸 a).V)
    (h : ∀ {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩), P (bassSerreVertex p)) : P y := by
  obtain ⟨_, p, rfl⟩ := bassSerreVertex_surjective y
  exact h p

/-- Eliminate a property on the darts of the Bass–Serre tree by checking it on pairs `(p, e)`. -/
@[elab_as_elim] theorem bassSerreDart_induction_on {P : (bassSerreTree 𝔸 a).E → Prop}
    (d : (bassSerreTree 𝔸 a).E)
    (h : ∀ {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c), P (bassSerreDart p e)) : P d := by
  obtain ⟨_, _, p, e, rfl⟩ := bassSerreDart_surjective d
  exact h p e

/-- A function on `𝔸`-paths from `a` that is invariant under homotopy and right multiplication by
vertex group elements descends to the vertices of the Bass–Serre tree. -/
noncomputable def bassSerreVertexLift {β : Sort*} (f : ∀ {b : Γ.V}, 𝔸.Path ⟨a⟩ ⟨b⟩ → β)
    (h_hom : ∀ {b : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩}, p.Homotopic q → f p = f q)
    (h_vertex : ∀ {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b),
      f (p.cons (.vertex g)) = f p) :
    (bassSerreTree 𝔸 a).V → β :=
  fun ⟨_, y⟩ ↦ Quotient.lift f
    (by rintro p _ ⟨g, _, hq⟩; exact (h_vertex p g).symm.trans (h_hom hq).symm) y

@[simp] theorem bassSerreVertexLift_bassSerreVertex {β : Sort*}
    (f : ∀ {b : Γ.V}, 𝔸.Path ⟨a⟩ ⟨b⟩ → β)
    (h_hom : ∀ {b : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩}, p.Homotopic q → f p = f q)
    (h_vertex : ∀ {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b),
      f (p.cons (.vertex g)) = f p)
    {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    bassSerreVertexLift f h_hom h_vertex (bassSerreVertex p) = f p :=
  (rfl)

/-- A function on pairs `(p, e)` of an `𝔸`-path from `a` to `b` and an arrow `e : b ⟶ c` that is
invariant under homotopy of `p` and right multiplication by `α_e(A_e)` descends to the darts of the
Bass–Serre tree. -/
noncomputable def bassSerreDartLift {β : Sort*}
    (f : ∀ {b c : Γ.V}, 𝔸.Path ⟨a⟩ ⟨b⟩ → (b ⟶ c) → β)
    (h_hom : ∀ {b c : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (e : b ⟶ c), p.Homotopic q → f p e = f q e)
    (h_αArrow : ∀ {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
      (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.val)),
      f (p.cons (.vertex (𝔸.αArrow e c₀))) e = f p e) :
    (bassSerreTree 𝔸 a).E → β :=
  fun ⟨_, _, e, y⟩ ↦ Quotient.lift (fun p ↦ f p e)
    (by rintro p _ ⟨_, ⟨c₀, rfl⟩, hq⟩; exact (h_αArrow p e c₀).symm.trans (h_hom e hq).symm) y

@[simp] theorem bassSerreDartLift_bassSerreDart {β : Sort*}
    (f : ∀ {b c : Γ.V}, 𝔸.Path ⟨a⟩ ⟨b⟩ → (b ⟶ c) → β)
    (h_hom : ∀ {b c : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (e : b ⟶ c), p.Homotopic q → f p e = f q e)
    (h_αArrow : ∀ {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
      (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.val)),
      f (p.cons (.vertex (𝔸.αArrow e c₀))) e = f p e)
    {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    bassSerreDartLift f h_hom h_αArrow (bassSerreDart p e) = f p e :=
  (rfl)

/-- Two `𝔸`-paths `p` and `q` from `a` to `b` give the same vertex exactly when `q` is homotopic
to `p g` for some `g ∈ A_b`. -/
theorem bassSerreVertex_eq_bassSerreVertex_iff {b : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} :
    bassSerreVertex p = bassSerreVertex q ↔ ∃ g, q.Homotopic (p.cons (.vertex g)) :=
  bsVertex_eq_bsVertex_iff

/-- Two `𝔸`-paths `p` and `q` from `a` to `b` give the same dart over `e : b ⟶ c` exactly when
`q` is homotopic to `p α_e(c₀)` for some `c₀ ∈ A_e`. -/
theorem bassSerreDart_eq_bassSerreDart_iff {b c : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} {e : b ⟶ c} :
    bassSerreDart p e = bassSerreDart q e ↔
      ∃ c₀, q.Homotopic (p.cons (.vertex (𝔸.αArrow e c₀))) :=
  bsDart_eq_bsDart_iff

/-- Homotopic paths give the same vertex. -/
theorem bassSerreVertex_congr {b : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic q) :
    bassSerreVertex p = bassSerreVertex q :=
  bsVertex_congr h

/-- Homotopic paths give the same dart. -/
theorem bassSerreDart_congr {b c : Γ.V} {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic q)
    (e : b ⟶ c) : bassSerreDart p e = bassSerreDart q e :=
  bsDart_congr h e

/-- Right multiplication by an element of `A_b` does not change the vertex `p A_b`. -/
@[simp] theorem bassSerreVertex_cons_vertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (g : 𝔸.vertexGroup b) : bassSerreVertex (p.cons (.vertex g)) = bassSerreVertex p :=
  bsVertex_cons_vertex p g

/-- Composing a path on the right with a single vertex-group element leaves the represented
Bass–Serre vertex unchanged. -/
theorem bassSerreVertex_comp_ofVertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b) :
    bassSerreVertex (p.comp (Path.ofVertex g)) = bassSerreVertex p := by
  rw [Path.comp_ofVertex, bassSerreVertex_cons_vertex]

@[simp] theorem bassSerreVertex_ofVertex (g : 𝔸.vertexGroup a) :
    bassSerreVertex (Path.ofVertex g) = bassSerreVertex .nil := by
  simp [Path.ofVertex_eq_nil_cons]

/-- Right multiplication by an element of `α_e(A_e)` does not change the dart `p α_e(A_e)`. -/
@[simp] theorem bassSerreDart_cons_vertex_αArrow {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.val)) :
    bassSerreDart (p.cons (.vertex (𝔸.αArrow e c₀))) e = bassSerreDart p e :=
  (bassSerreDart_eq_bassSerreDart_iff.2 ⟨c₀, .refl _⟩).symm

@[simp] theorem bassSerreDart_cons_vertex_α (e : Γ.E) (p : 𝔸.Path ⟨a⟩ ⟨Γ.src e⟩)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart (p.cons (.vertex (𝔸.α e c₀))) (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) =
      bassSerreDart p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) := by
  simpa only [𝔸.αArrow_mk] using
    bassSerreDart_cons_vertex_αArrow p (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) c₀

@[simp] theorem bassSerreDart_ofVertex_αArrow {c : Γ.V} (e : a ⟶ c)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.val)) :
    bassSerreDart (Path.ofVertex (𝔸.αArrow e c₀)) e = bassSerreDart .nil e := by
  rw [Path.ofVertex_eq_nil_cons, bassSerreDart_cons_vertex_αArrow]

@[simp] theorem bassSerreDart_ofVertex_α (e : Γ.E) (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    bassSerreDart (Path.ofVertex (𝔸.α e c₀)) (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) =
      bassSerreDart .nil (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) := by
  simpa only [𝔸.αArrow_mk] using
    bassSerreDart_ofVertex_αArrow (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) c₀

/-- The quotient map sending the homotopy class of a based `𝔸`-path `p` from `a` to `b` to its
right-coset vertex `p A_b` in `X(𝔸, a)`. -/
noncomputable def HomotopyPathFrom.toBassSerreVertex :
    𝔸.HomotopyPathFrom a → (bassSerreTree 𝔸 a).V :=
  HomotopyPathFrom.lift (fun p ↦ bassSerreVertex p) fun _ _ ↦ bassSerreVertex_congr

@[simp] theorem HomotopyPathFrom.toBassSerreVertex_ofPath {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (HomotopyPathFrom.ofPath p).toBassSerreVertex = bassSerreVertex p :=
  HomotopyPathFrom.lift_ofPath ..

/-- When a vertex `b` reachable from `a` by an `𝔸`-path `p` has nontrivial vertex group `A_b`, the
quotient map `HomotopyPathFrom.toBassSerreVertex` is not injective. -/
theorem HomotopyPathFrom.not_injective_toBassSerreVertex {b : Γ.V} [Nontrivial (𝔸.vertexGroup b)]
    (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    ¬ Function.Injective (HomotopyPathFrom.toBassSerreVertex (𝔸 := 𝔸) (a := a)) := by
  obtain ⟨g, hg⟩ := exists_ne (1 : 𝔸.vertexGroup b)
  intro hinj
  have hEq : (HomotopyPathFrom.ofPath (p.cons (.vertex g))).toBassSerreVertex =
      (HomotopyPathFrom.ofPath p).toBassSerreVertex := by simp
  have hhom : Path.Homotopic (p.cons (.vertex g)) p :=
    HomotopyPathFrom.ofPath_eq_ofPath_iff.1 (hinj hEq)
  rw [← Path.comp_ofVertex] at hhom
  have h1 : Path.Homotopic (Path.ofVertex g) .nil :=
    Path.Homotopic.comp_left_iff.1 (by simpa only [Quiver.Path.comp_nil] using hhom)
  exact hg (Path.ofVertex_homotopic_nil_iff.1 h1)

/-- The dart `p α_e(A_e)` starts at `p A_b`. -/
@[simp] theorem src_bassSerreDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreTree 𝔸 a).src (bassSerreDart p e) = bassSerreVertex p :=
  src_bsDart p e

/-- The reverse of the dart `p α_e(A_e)` is the dart `p e α_{rev e}(A_e)`. -/
@[simp] theorem rev_bassSerreDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreTree 𝔸 a).rev (bassSerreDart p e) =
      bassSerreDart (p.cons (.dart e)) (Quiver.reverse e) :=
  rev_bsDart p e

/-- The dart `p α_e(A_e)` ends at `p e A_c`. -/
@[simp] theorem tgt_bassSerreDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    (bassSerreTree 𝔸 a).tgt (bassSerreDart p e) = bassSerreVertex (p.cons (.dart e)) :=
  tgt_bsDart p e

/-- The fundamental group acts on vertices by concatenation on the left. -/
@[simp] theorem smul_bassSerreVertex (γ : 𝔸.Path ⟨a⟩ ⟨a⟩) {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    π₁.mk γ • bassSerreVertex p = bassSerreVertex (γ.comp p) := by
  rw [bassSerreTree_smul_vertex]
  exact congrArg (Sigma.mk b) (PathCoset.smul_mk γ p)

@[simp] theorem HomotopyPathFrom.toBassSerreVertex_smul (g : π₁ 𝔸 a) (x : 𝔸.HomotopyPathFrom a) :
    (g • x).toBassSerreVertex = g • x.toBassSerreVertex :=
  π₁.induction_on g fun _ ↦ HomotopyPathFrom.induction_on x fun _ ↦ by simp

/-- The fundamental group acts on darts by concatenation on the left. -/
@[simp] theorem smul_bassSerreDart (γ : 𝔸.Path ⟨a⟩ ⟨a⟩) {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) : π₁.mk γ • bassSerreDart p e = bassSerreDart (γ.comp p) e := by
  rw [bassSerreTree_smul_dart]
  exact congrArg (fun y ↦ (⟨b, c, e, y⟩ : BSDart 𝔸 a)) (PathCoset.smul_mk γ p)

/-- Conjugating an element of `A_b` along `p` fixes the vertex `p A_b`. -/
@[simp] theorem vertexHom_smul_bassSerreVertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (g : 𝔸.vertexGroup b) : π₁.vertexHom p g • bassSerreVertex p = bassSerreVertex p := by
  rw [π₁.vertexHom_apply, smul_bassSerreVertex]
  exact (bassSerreVertex_congr (Path.Homotopic.comp_reverse_comp _ p)).trans
    (bassSerreVertex_comp_ofVertex p g)

/-- Acting by `π₁.vertexHom p g` on the adjacent vertex `p e A_c` inserts `g` before `e`, producing
`p g e A_c`. -/
theorem vertexHom_smul_bassSerreVertex_cons_dart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (g : 𝔸.vertexGroup b) (e : b ⟶ c) :
    π₁.vertexHom p g • bassSerreVertex (p.cons (.dart e)) =
      bassSerreVertex ((p.cons (.vertex g)).cons (.dart e)) := by
  rw [π₁.vertexHom_apply, smul_bassSerreVertex, ← Path.comp_ofDart p e, ← Path.comp_ofDart,
    ← Path.comp_ofVertex]
  exact bassSerreVertex_congr (Path.Homotopic.comp_reverse_comp_comp _ p _)

/-- The stabilizer of the vertex `p A_b` is the conjugate `p A_b p⁻¹` of the vertex group. -/
theorem stabilizer_bassSerreVertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    stabilizer (π₁ 𝔸 a) (bassSerreVertex p) = (π₁.vertexHom p).range := by
  rw [MonoidHom.range_eq_map, ← PathCoset.stabilizer_mk (H := ⊤)]
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, bassSerreTree_smul_vertex]
  exact sigma_mk_injective.eq_iff

/-- The stabilizer of the dart `p α_e(A_e)` is the conjugate `p α_e(A_e) p⁻¹` of the image of the
edge group. -/
theorem stabilizer_bassSerreDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    stabilizer (π₁ 𝔸 a) (bassSerreDart p e) = (𝔸.αArrow e).range.map (π₁.vertexHom p) := by
  rw [← PathCoset.stabilizer_mk]
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, bassSerreTree_smul_dart]
  exact sigma_mk_injective.eq_iff.trans <| sigma_mk_injective.eq_iff.trans
    sigma_mk_injective.eq_iff

/-- The stabilizer of the dart `(p g) α_e(A_e)` joining `p A_b` to `p g e A_c` is the conjugate
`p g α_e(A_e) g⁻¹ p⁻¹`. -/
theorem stabilizer_bassSerreDart_cons_vertex {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (g : 𝔸.vertexGroup b) (e : b ⟶ c) :
    stabilizer (π₁ 𝔸 a) (bassSerreDart (p.cons (.vertex g)) e) =
      (((𝔸.αArrow e).range).map (MulAut.conj g : 𝔸.vertexGroup b →* 𝔸.vertexGroup b)).map
        (π₁.vertexHom p) := by
  rw [stabilizer_bassSerreDart, π₁.vertexHom_cons_vertex, Subgroup.map_map]

/-- The Bass–Serre tree is relative to families `(𝒜, ℋ)` whenever `𝒜` contains all edge group
images along `𝔸`-paths from `a` and every subgroup in `ℋ` is elliptic. -/
theorem isRelative_bassSerreTree {𝒜 ℋ : Set (Subgroup (π₁ 𝔸 a))}
    (h𝒜 : ∀ {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c),
      (𝔸.αArrow e).range.map (π₁.vertexHom p) ∈ 𝒜)
    (hℋ : ∀ H ∈ ℋ, (bassSerreTree 𝔸 a).IsEllipticSubgroup H) :
    (bassSerreTree 𝔸 a).IsRelative 𝒜 ℋ :=
  GTree.isRelative_iff.2 ⟨fun d ↦ bassSerreDart_induction_on d fun p e ↦ by
    rw [stabilizer_bassSerreDart]; exact h𝒜 p e, hℋ⟩

/-- A vertex `p A_b` with trivial vertex group `A_b` has trivial stabilizer. -/
theorem stabilizer_bassSerreVertex_eq_bot {b : Γ.V} [Subsingleton (𝔸.vertexGroup b)]
    (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : stabilizer (π₁ 𝔸 a) (bassSerreVertex p) = ⊥ := by
  rw [stabilizer_bassSerreVertex, MonoidHom.range_eq_bot_iff]
  exact Subsingleton.elim _ _

/-- The element `p g p⁻¹` with `g ∈ A_b` fixes the dart `p α_e(A_e)` exactly when
`g ∈ α_e(A_e)`. -/
@[simp]
theorem vertexHom_smul_bassSerreDart_eq_self_iff {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (g : 𝔸.vertexGroup b) :
    π₁.vertexHom p g • bassSerreDart p e = bassSerreDart p e ↔ g ∈ (𝔸.αArrow e).range := by
  rw [← mem_stabilizer_iff, stabilizer_bassSerreDart,
    Subgroup.mem_map_iff_mem (π₁.vertexHom_injective p)]

/-- The element `(p e) h (p e)⁻¹` with `h ∈ A_c` fixes the dart `p α_e(A_e)` exactly when
`h ∈ ω_e(A_e)`: it fixes the reverse dart `(p e) α_{rev e}(A_e)`, and
`α_{rev e}(A_e) = ω_e(A_e)`. -/
@[simp]
theorem vertexHom_cons_smul_bassSerreDart_eq_self_iff {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) (h : 𝔸.vertexGroup c) :
    π₁.vertexHom (p.cons (.dart e)) h • bassSerreDart p e = bassSerreDart p e ↔
      h ∈ (𝔸.ωArrow e).range := by
  rw [← mem_stabilizer_iff, ← GTree.stabilizer_rev, rev_bassSerreDart, stabilizer_bassSerreDart,
    range_αArrow_reverse, Subgroup.mem_map_iff_mem (π₁.vertexHom_injective _)]

/-- `π₁(𝔸, a)` acts transitively on the vertices `p A_b` over a vertex `b` of `Γ`: the class of
`q p⁻¹` carries `p A_b` to `q A_b`. -/
theorem exists_smul_bassSerreVertex_eq {b : Γ.V} (p q : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    ∃ g : π₁ 𝔸 a, g • bassSerreVertex p = bassSerreVertex q :=
  ⟨π₁.mk (q.comp p.reverse), by
    rw [smul_bassSerreVertex]
    exact bassSerreVertex_congr (Path.Homotopic.comp_reverse_comp q p)⟩

/-- `π₁(𝔸, a)` acts transitively on the darts `p α_e(A_e)` over a dart `e` of `Γ`. -/
theorem exists_smul_bassSerreDart_eq {b c : Γ.V} (p q : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    ∃ g : π₁ 𝔸 a, g • bassSerreDart p e = bassSerreDart q e :=
  ⟨π₁.mk (q.comp p.reverse), by
    rw [smul_bassSerreDart]
    exact bassSerreDart_congr (Path.Homotopic.comp_reverse_comp q p) e⟩

/-! ### Graphs without edges -/

/-- Over a graph without edges, the Bass–Serre tree has no darts. -/
instance [IsEmpty Γ.E] : IsEmpty (bassSerreTree 𝔸 a).E :=
  ⟨fun d ↦ bassSerreDart_induction_on d fun _ e ↦ isEmptyElim e.val⟩

/-- Over a graph without edges, for instance for the trivial splitting of a group as a single
vertex group, the Bass–Serre tree is a point: every `𝔸`-path from `a` stays at `a` and is homotopic
to a single element of `A_a`. -/
noncomputable instance [IsEmpty Γ.E] : Unique (bassSerreTree 𝔸 a).V where
  default := bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩)
  uniq y := by
    obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
    obtain rfl : a = b := Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim (Path.edgePath p)
    obtain ⟨g, hg⟩ := π₁.exists_homotopic_ofVertex_of_isEmpty p
    rw [bassSerreVertex_congr hg, Path.ofVertex_eq_nil_cons, bassSerreVertex_cons_vertex]

/-! ### The quotient graph -/

variable (𝔸 a)

/-- The projection of the Bass–Serre tree to `Γ`, sending the vertex `p A_b` to `b` and the dart
`p α_e(A_e)` to `e`. -/
noncomputable def bassSerreProjection : (bassSerreTree 𝔸 a).Hom Γ where
  mapV y := y.1
  mapE d := d.2.2.1.val
  map_src d := d.2.2.1.property.1
  map_rev d := Γ.reverse_val d.2.2.1

variable {𝔸 a}

@[simp] theorem bassSerreProjection_mapV_bassSerreVertex {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (bassSerreProjection 𝔸 a).mapV (bassSerreVertex p) = b :=
  (rfl)

@[simp] theorem bassSerreProjection_mapE_bassSerreDart {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) : (bassSerreProjection 𝔸 a).mapE (bassSerreDart p e) = e.val :=
  (rfl)

/-- When the vertex group at the underlying vertex of `y` is trivial, `y` has trivial stabilizer in
`π₁(𝔸, a)`. -/
@[simp] theorem stabilizer_bassSerreTree_vertex_eq_bot (y : (bassSerreTree 𝔸 a).V)
    [Subsingleton (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y))] :
    stabilizer (π₁ 𝔸 a) y = ⊥ := by
  have h := @bassSerreVertex_induction_on _ _ _
    (fun y ↦ ∀ [Subsingleton (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y))],
      stabilizer (π₁ 𝔸 a) y = ⊥) y fun p ↦ by
    rw [bassSerreProjection_mapV_bassSerreVertex]
    intro
    exact stabilizer_bassSerreVertex_eq_bot p
  exact h

/-- When the edge group of the underlying dart of `d` is trivial, `d` has trivial stabilizer in
`π₁(𝔸, a)`. -/
@[simp] theorem stabilizer_bassSerreTree_dart_eq_bot (d : (bassSerreTree 𝔸 a).E)
    [Subsingleton (𝔸.edgeGroup (Γ.toGeomEdge ((bassSerreProjection 𝔸 a).mapE d)))] :
    stabilizer (π₁ 𝔸 a) d = ⊥ := by
  have h := @bassSerreDart_induction_on _ _ _
    (fun d ↦ ∀ [Subsingleton (𝔸.edgeGroup (Γ.toGeomEdge ((bassSerreProjection 𝔸 a).mapE d)))],
      stabilizer (π₁ 𝔸 a) d = ⊥) d fun p e ↦ by
    rw [bassSerreProjection_mapE_bassSerreDart]
    intro
    rw [stabilizer_bassSerreDart, MonoidHom.range_eq_bot_iff.2 (Subsingleton.elim _ _),
      Subgroup.map_bot]
  exact h

/-- The projection to `Γ` is invariant under the action on vertices. -/
@[simp] theorem bassSerreProjection_mapV_smul (g : π₁ 𝔸 a) (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreProjection 𝔸 a).mapV (g • y) = (bassSerreProjection 𝔸 a).mapV y := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
  induction g using π₁.induction_on with | h γ => ?_
  simp

/-- The projection to `Γ` is invariant under the action on darts. -/
@[simp] theorem bassSerreProjection_mapE_smul (g : π₁ 𝔸 a) (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreProjection 𝔸 a).mapE (g • d) = (bassSerreProjection 𝔸 a).mapE d := by
  obtain ⟨b, c, p, e, rfl⟩ := bassSerreDart_surjective d
  induction g using π₁.induction_on with | h γ => ?_
  simp

/-- The projection to `Γ` is invariant under the action of `π₁(𝔸, a)`. -/
theorem bassSerreProjection_comp_toHom (g : π₁ 𝔸 a) :
    (bassSerreProjection 𝔸 a).comp ((bassSerreTree 𝔸 a).action g).toHom =
      bassSerreProjection 𝔸 a :=
  SerreGraph.Hom.ext _
    (funext fun y ↦ by rw [SerreGraph.Hom.comp_mapV, Function.comp_apply,
      GTree.action_toHom_mapV, bassSerreProjection_mapV_smul])
    (funext fun d ↦ by rw [SerreGraph.Hom.comp_mapE, Function.comp_apply,
      GTree.action_toHom_mapE, bassSerreProjection_mapE_smul])

/-- Every vertex of `X(𝔸, a)` projects into the connected component of `a` in `Γ`. -/
theorem bassSerreProjection_mapV_mem_componentVertices (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreProjection 𝔸 a).mapV y ∈ Γ.componentVertices a :=
  bassSerreVertex_induction_on y fun p ↦ (Γ.mem_componentVertices_iff a _).2 ⟨p.edgePath⟩

/-- Every dart of `X(𝔸, a)` projects into the connected component of `a` in `Γ`. -/
theorem bassSerreProjection_mapE_mem_componentDarts (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreProjection 𝔸 a).mapE d ∈ Γ.componentDarts a := by
  rw [Γ.mem_componentDarts_iff, (bassSerreProjection 𝔸 a).map_src]
  exact (Γ.mem_componentVertices_iff a _).1
    (bassSerreProjection_mapV_mem_componentVertices ((bassSerreTree 𝔸 a).src d))

variable (𝔸 a) in
/-- The canonical projection from `X(𝔸, a)` onto the connected component `Γ.component a` of the
base vertex. -/
noncomputable def bassSerreProjectionComponent : (bassSerreTree 𝔸 a).Hom (Γ.component a) where
  mapV y := ⟨(bassSerreProjection 𝔸 a).mapV y, bassSerreProjection_mapV_mem_componentVertices y⟩
  mapE d := ⟨(bassSerreProjection 𝔸 a).mapE d, bassSerreProjection_mapE_mem_componentDarts d⟩
  map_src d := Subtype.ext ((bassSerreProjection 𝔸 a).map_src d)
  map_rev d := Subtype.ext ((bassSerreProjection 𝔸 a).map_rev d)

@[simp] theorem bassSerreProjectionComponent_mapV_val (y : (bassSerreTree 𝔸 a).V) :
    ((bassSerreProjectionComponent 𝔸 a).mapV y).val = (bassSerreProjection 𝔸 a).mapV y :=
  (rfl)

@[simp] theorem bassSerreProjectionComponent_mapE_val (d : (bassSerreTree 𝔸 a).E) :
    ((bassSerreProjectionComponent 𝔸 a).mapE d).val = (bassSerreProjection 𝔸 a).mapE d :=
  (rfl)

@[simp] theorem bassSerreProjectionComponent_mapV_nil :
    (bassSerreProjectionComponent 𝔸 a).mapV
      (bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩)) = Γ.componentBase a :=
  Subtype.ext <| (bassSerreProjection_mapV_bassSerreVertex
    (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩)).trans (Γ.componentBase_val a).symm

@[simp] theorem componentInclusion_comp_bassSerreProjectionComponent :
    (Γ.componentInclusion a).comp (bassSerreProjectionComponent 𝔸 a) = bassSerreProjection 𝔸 a := by
  ext <;> rfl

/-- The projection to `Γ.component a` is invariant under the action of `π₁(𝔸, a)`. -/
theorem bassSerreProjectionComponent_comp_toHom (g : π₁ 𝔸 a) :
    (bassSerreProjectionComponent 𝔸 a).comp ((bassSerreTree 𝔸 a).action g).toHom =
      bassSerreProjectionComponent 𝔸 a :=
  SerreGraph.Hom.ext _
    (funext fun y ↦ Subtype.ext <| by
      rw [SerreGraph.Hom.comp_mapV, Function.comp_apply, GTree.action_toHom_mapV,
        bassSerreProjectionComponent_mapV_val, bassSerreProjectionComponent_mapV_val,
        bassSerreProjection_mapV_smul])
    (funext fun d ↦ Subtype.ext <| by
      rw [SerreGraph.Hom.comp_mapE, Function.comp_apply, GTree.action_toHom_mapE,
        bassSerreProjectionComponent_mapE_val, bassSerreProjectionComponent_mapE_val,
        bassSerreProjection_mapE_smul])

variable (𝔸 a)

/-- The morphism from the quotient graph `X(𝔸, a) / π₁(𝔸, a)` to `Γ` induced by the projection.
It is injective, with image the connected component of `a`
(`bassSerreQuotientHom_mapV_injective`, `range_bassSerreQuotientHom_mapV`), so it is an isomorphism
when `Γ` is connected (`bassSerreQuotientIso`). -/
noncomputable def bassSerreQuotientHom : (bassSerreTree 𝔸 a).quotient.Hom Γ :=
  SerreGraph.quotientLift _ (bassSerreProjection 𝔸 a) bassSerreProjection_comp_toHom

/-- The morphism from the quotient graph `X(𝔸, a) / π₁(𝔸, a)` to `Γ.component a` induced by the
`π₁(𝔸, a)`-invariant projection onto the connected component. -/
noncomputable def bassSerreQuotientHomComponent :
    (bassSerreTree 𝔸 a).quotient.Hom (Γ.component a) :=
  SerreGraph.quotientLift _ (bassSerreProjectionComponent 𝔸 a)
    bassSerreProjectionComponent_comp_toHom

variable {𝔸 a}

@[simp] theorem bassSerreQuotientHom_mapV_quotientMap (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientHom 𝔸 a).mapV ((bassSerreTree 𝔸 a).quotientMap.mapV y) =
      (bassSerreProjection 𝔸 a).mapV y :=
  SerreGraph.quotientLift_mapV_quotientMap _ _ y

@[simp] theorem bassSerreQuotientHom_mapE_quotientMap (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientHom 𝔸 a).mapE ((bassSerreTree 𝔸 a).quotientMap.mapE d) =
      (bassSerreProjection 𝔸 a).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap _ _ d

@[simp] theorem bassSerreQuotientHomComponent_comp_quotientMap :
    (bassSerreQuotientHomComponent 𝔸 a).comp (bassSerreTree 𝔸 a).quotientMap =
      bassSerreProjectionComponent 𝔸 a :=
  SerreGraph.quotientLift_comp_quotientMap ..

@[simp] theorem bassSerreQuotientHomComponent_mapV_quotientMap (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientHomComponent 𝔸 a).mapV ((bassSerreTree 𝔸 a).quotientMap.mapV y) =
      (bassSerreProjectionComponent 𝔸 a).mapV y :=
  SerreGraph.quotientLift_mapV_quotientMap _ _ y

@[simp] theorem bassSerreQuotientHomComponent_mapE_quotientMap (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientHomComponent 𝔸 a).mapE ((bassSerreTree 𝔸 a).quotientMap.mapE d) =
      (bassSerreProjectionComponent 𝔸 a).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap _ _ d

@[simp] theorem componentInclusion_comp_bassSerreQuotientHomComponent :
    (Γ.componentInclusion a).comp (bassSerreQuotientHomComponent 𝔸 a) =
      bassSerreQuotientHom 𝔸 a := by
  refine ((bassSerreTree 𝔸 a).quotientMap.cancel_right
    (bassSerreTree 𝔸 a).quotientMap_mapV_surjective
    (bassSerreTree 𝔸 a).quotientMap_mapE_surjective).1 ?_
  rw [← SerreGraph.Hom.comp_assoc, bassSerreQuotientHomComponent_comp_quotientMap,
    componentInclusion_comp_bassSerreProjectionComponent, bassSerreQuotientHom,
    SerreGraph.quotientLift_comp_quotientMap]

/-- Vertices of the Bass–Serre tree over the same vertex of `Γ` lie in one orbit. -/
theorem bassSerreQuotientHom_mapV_injective :
    Function.Injective (bassSerreQuotientHom 𝔸 a).mapV := by
  intro y₁ y₂ h
  obtain ⟨y₁, rfl⟩ := (bassSerreTree 𝔸 a).quotientMap_mapV_surjective y₁
  obtain ⟨y₂, rfl⟩ := (bassSerreTree 𝔸 a).quotientMap_mapV_surjective y₂
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y₁
  obtain ⟨b', q, rfl⟩ := bassSerreVertex_surjective y₂
  obtain rfl : b = b' := by simpa using h
  exact GTree.quotientMap_mapV_eq_iff.2 (exists_smul_bassSerreVertex_eq p q)

/-- Darts of the Bass–Serre tree over the same dart of `Γ` lie in one orbit. -/
theorem bassSerreQuotientHom_mapE_injective :
    Function.Injective (bassSerreQuotientHom 𝔸 a).mapE := by
  intro d₁ d₂ h
  obtain ⟨d₁, rfl⟩ := (bassSerreTree 𝔸 a).quotientMap_mapE_surjective d₁
  obtain ⟨d₂, rfl⟩ := (bassSerreTree 𝔸 a).quotientMap_mapE_surjective d₂
  obtain ⟨_, _, p, ⟨e, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d₁
  obtain ⟨_, _, q, ⟨e', rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d₂
  obtain rfl : e = e' := by simpa using h
  exact GTree.quotientMap_mapE_eq_iff.2 (exists_smul_bassSerreDart_eq p q _)

/-- The vertices of `Γ` under vertices of the Bass–Serre tree are those joined to `a` by a path. -/
theorem range_bassSerreQuotientHom_mapV :
    Set.range (bassSerreQuotientHom 𝔸 a).mapV = {b | Nonempty (Γ.Path a b)} := by
  ext b
  refine ⟨?_, fun ⟨q⟩ ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := (bassSerreTree 𝔸 a).quotientMap_mapV_surjective y
    obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective y
    exact ⟨by simpa using p.edgePath⟩
  · refine ⟨(bassSerreTree 𝔸 a).quotientMap.mapV
      (bassSerreVertex ((dartPrefunctor 𝔸).mapPath q)), ?_⟩
    simp

/-- The darts of `Γ` under darts of the Bass–Serre tree are those whose source is joined to `a`
by a path. -/
theorem range_bassSerreQuotientHom_mapE :
    Set.range (bassSerreQuotientHom 𝔸 a).mapE = {e | Nonempty (Γ.Path a (Γ.src e))} := by
  ext e
  refine ⟨?_, fun ⟨q⟩ ↦ ?_⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨d, rfl⟩ := (bassSerreTree 𝔸 a).quotientMap_mapE_surjective d
    obtain ⟨b, c, p, e, rfl⟩ := bassSerreDart_surjective d
    exact ⟨by simpa [e.property.1] using p.edgePath⟩
  · refine ⟨(bassSerreTree 𝔸 a).quotientMap.mapE
      (bassSerreDart ((dartPrefunctor 𝔸).mapPath q) (Γ.dart e)), ?_⟩
    simp

private theorem bassSerreQuotientHomComponent_mapV_bijective :
    Function.Bijective (bassSerreQuotientHomComponent 𝔸 a).mapV := by
  refine ⟨fun y₁ y₂ h ↦ bassSerreQuotientHom_mapV_injective ?_, fun ⟨b, hb⟩ ↦ ?_⟩
  · rw [← componentInclusion_comp_bassSerreQuotientHomComponent]
    exact congrArg (Γ.componentInclusion a).mapV h
  · obtain ⟨y, hy⟩ := (Set.ext_iff.1 range_bassSerreQuotientHom_mapV b).2
      ((Γ.mem_componentVertices_iff a b).1 hb)
    exact ⟨y, Subtype.ext (by
      simpa [← componentInclusion_comp_bassSerreQuotientHomComponent] using hy)⟩

private theorem bassSerreQuotientHomComponent_mapE_bijective :
    Function.Bijective (bassSerreQuotientHomComponent 𝔸 a).mapE := by
  refine ⟨fun d₁ d₂ h ↦ bassSerreQuotientHom_mapE_injective ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · rw [← componentInclusion_comp_bassSerreQuotientHomComponent]
    exact congrArg (Γ.componentInclusion a).mapE h
  · obtain ⟨d, hd⟩ := (Set.ext_iff.1 range_bassSerreQuotientHom_mapE e).2
      ((Γ.mem_componentDarts_iff a e).1 he)
    exact ⟨d, Subtype.ext (by
      simpa [← componentInclusion_comp_bassSerreQuotientHomComponent] using hd)⟩

variable (𝔸 a)

/-- The quotient graph `X(𝔸, a) / π₁(𝔸, a)` is canonically isomorphic to the connected component of
`a` in `Γ`. -/
noncomputable def bassSerreQuotientIsoComponent :
    (bassSerreTree 𝔸 a).quotient.Iso (Γ.component a) :=
  (bassSerreQuotientHomComponent 𝔸 a).toIso
    bassSerreQuotientHomComponent_mapV_bijective
    bassSerreQuotientHomComponent_mapE_bijective

section ComponentIso

variable {𝔸 a}

@[simp] theorem bassSerreQuotientIsoComponent_toHom :
    (bassSerreQuotientIsoComponent 𝔸 a).toHom = bassSerreQuotientHomComponent 𝔸 a :=
  SerreGraph.Hom.toIso_toHom _ _ _

@[simp] theorem bassSerreQuotientIsoComponent_equivV_quotientMap (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientIsoComponent 𝔸 a).equivV ((bassSerreTree 𝔸 a).quotientMap.mapV y) =
      (bassSerreProjectionComponent 𝔸 a).mapV y := by
  rw [← SerreGraph.Iso.toHom_mapV, bassSerreQuotientIsoComponent_toHom,
    bassSerreQuotientHomComponent_mapV_quotientMap]

@[simp] theorem bassSerreQuotientIsoComponent_equivE_quotientMap (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientIsoComponent 𝔸 a).equivE ((bassSerreTree 𝔸 a).quotientMap.mapE d) =
      (bassSerreProjectionComponent 𝔸 a).mapE d := by
  rw [← SerreGraph.Iso.toHom_mapE, bassSerreQuotientIsoComponent_toHom,
    bassSerreQuotientHomComponent_mapE_quotientMap]

@[simp] theorem bassSerreQuotientIsoComponent_equivV_symm_mapV (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientIsoComponent 𝔸 a).equivV.symm
      ((bassSerreProjectionComponent 𝔸 a).mapV y) = (bassSerreTree 𝔸 a).quotientMap.mapV y :=
  (bassSerreQuotientIsoComponent 𝔸 a).equivV.symm_apply_eq.2
    (bassSerreQuotientIsoComponent_equivV_quotientMap y).symm

@[simp] theorem bassSerreQuotientIsoComponent_equivV_symm_componentBase :
    (bassSerreQuotientIsoComponent 𝔸 a).equivV.symm (Γ.componentBase a) =
      (bassSerreTree 𝔸 a).quotientMap.mapV (bassSerreVertex .nil) := by
  rw [← bassSerreProjectionComponent_mapV_nil, bassSerreQuotientIsoComponent_equivV_symm_mapV]

/-- Evaluating the inverse vertex equivalence of `bassSerreQuotientIsoComponent` on a vertex
reached from `a` by an edge path `γ` lifts `γ` to the Bass–Serre tree and projects to the
quotient. -/
theorem bassSerreQuotientIsoComponent_equivV_symm_mk {b : Γ.V} (γ : Γ.Path a b) :
    (bassSerreQuotientIsoComponent 𝔸 a).equivV.symm
      ⟨b, (Γ.mem_componentVertices_iff a b).2 ⟨γ⟩⟩ =
      (bassSerreTree 𝔸 a).quotientMap.mapV
        (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)) := by
  have h : (bassSerreProjectionComponent 𝔸 a).mapV
      (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)) =
      ⟨b, (Γ.mem_componentVertices_iff a b).2 ⟨γ⟩⟩ :=
    Subtype.ext (bassSerreProjection_mapV_bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ))
  rw [← h, bassSerreQuotientIsoComponent_equivV_symm_mapV]

@[simp] theorem bassSerreQuotientIsoComponent_equivE_symm_mapE (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientIsoComponent 𝔸 a).equivE.symm
      ((bassSerreProjectionComponent 𝔸 a).mapE d) = (bassSerreTree 𝔸 a).quotientMap.mapE d :=
  (bassSerreQuotientIsoComponent 𝔸 a).equivE.symm_apply_eq.2
    (bassSerreQuotientIsoComponent_equivE_quotientMap d).symm

/-- Evaluating the inverse dart equivalence of `bassSerreQuotientIsoComponent` on a dart `e` whose
source is reached from `a` by an edge path `γ` lifts `(γ, e)` to the Bass–Serre tree and projects
to the quotient. -/
theorem bassSerreQuotientIsoComponent_equivE_symm_mk {e : Γ.E} (γ : Γ.Path a (Γ.src e)) :
    (bassSerreQuotientIsoComponent 𝔸 a).equivE.symm
      ⟨e, (Γ.mem_componentDarts_iff a e).2 ⟨γ⟩⟩ =
      (bassSerreTree 𝔸 a).quotientMap.mapE
        (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)) := by
  have h : (bassSerreProjectionComponent 𝔸 a).mapE
      (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)) =
      ⟨e, (Γ.mem_componentDarts_iff a e).2 ⟨γ⟩⟩ :=
    Subtype.ext <| (bassSerreProjection_mapE_bassSerreDart
      ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)).trans (Γ.dart_val e)
  rw [← h, bassSerreQuotientIsoComponent_equivE_symm_mapE]

end ComponentIso

/-- For a preconnected graph `Γ`, the quotient of the Bass–Serre tree by `π₁(𝔸, a)` is `Γ`. -/
noncomputable def bassSerreQuotientIso (hΓ : Γ.Preconnected) :
    (bassSerreTree 𝔸 a).quotient.Iso Γ :=
  (bassSerreQuotientHom 𝔸 a).toIso
    ⟨bassSerreQuotientHom_mapV_injective, fun b ↦
      (Set.ext_iff.1 range_bassSerreQuotientHom_mapV b).2 ((Γ.preconnected_iff.1 hΓ) a b)⟩
    ⟨bassSerreQuotientHom_mapE_injective, fun e ↦
      (Set.ext_iff.1 range_bassSerreQuotientHom_mapE e).2 ((Γ.preconnected_iff.1 hΓ) a _)⟩

section PreconnectedIso

variable {𝔸 a}

/-- The isomorphism from the quotient graph to `Γ` is the morphism `bassSerreQuotientHom`. -/
@[simp] theorem bassSerreQuotientIso_toHom (hΓ : Γ.Preconnected) :
    (bassSerreQuotientIso 𝔸 a hΓ).toHom = bassSerreQuotientHom 𝔸 a :=
  SerreGraph.Hom.toIso_toHom _ _ _

@[simp] theorem bassSerreQuotientIsoComponent_trans_componentIsoOfPreconnected
    (hΓ : Γ.Preconnected) :
    (bassSerreQuotientIsoComponent 𝔸 a).trans (Γ.componentIsoOfPreconnected hΓ) =
      bassSerreQuotientIso 𝔸 a hΓ := by
  have hhom : ((bassSerreQuotientIsoComponent 𝔸 a).trans (Γ.componentIsoOfPreconnected hΓ)).toHom =
      (bassSerreQuotientIso 𝔸 a hΓ).toHom := by
    simp
  exact SerreGraph.Iso.ext
    (fun x ↦ congrFun (congrArg SerreGraph.Hom.mapV hhom) x)
    (fun d ↦ congrFun (congrArg SerreGraph.Hom.mapE hhom) d)

@[simp] theorem bassSerreQuotientIso_equivV_quotientMap (hΓ : Γ.Preconnected)
    (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivV ((bassSerreTree 𝔸 a).quotientMap.mapV y) =
      (bassSerreProjection 𝔸 a).mapV y := by
  rw [← SerreGraph.Iso.toHom_mapV, bassSerreQuotientIso_toHom,
    bassSerreQuotientHom_mapV_quotientMap]

@[simp] theorem bassSerreQuotientIso_equivE_quotientMap (hΓ : Γ.Preconnected)
    (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivE ((bassSerreTree 𝔸 a).quotientMap.mapE d) =
      (bassSerreProjection 𝔸 a).mapE d := by
  rw [← SerreGraph.Iso.toHom_mapE, bassSerreQuotientIso_toHom,
    bassSerreQuotientHom_mapE_quotientMap]

@[simp] theorem bassSerreQuotientIso_equivV_symm_mapV (hΓ : Γ.Preconnected)
    (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivV.symm ((bassSerreProjection 𝔸 a).mapV y) =
      (bassSerreTree 𝔸 a).quotientMap.mapV y :=
  (bassSerreQuotientIso 𝔸 a hΓ).equivV.symm_apply_eq.2
    (bassSerreQuotientIso_equivV_quotientMap hΓ y).symm

@[simp] theorem bassSerreQuotientIso_equivV_symm_self (hΓ : Γ.Preconnected) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivV.symm a =
      (bassSerreTree 𝔸 a).quotientMap.mapV (bassSerreVertex .nil) :=
  bassSerreQuotientIso_equivV_symm_mapV hΓ (bassSerreVertex .nil)

@[simp] theorem bassSerreQuotientIso_equivE_symm_mapE (hΓ : Γ.Preconnected)
    (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivE.symm ((bassSerreProjection 𝔸 a).mapE d) =
      (bassSerreTree 𝔸 a).quotientMap.mapE d :=
  (bassSerreQuotientIso 𝔸 a hΓ).equivE.symm_apply_eq.2
    (bassSerreQuotientIso_equivE_quotientMap hΓ d).symm

/-- For preconnected `Γ`, evaluating the inverse vertex equivalence of `bassSerreQuotientIso` on a
vertex reached from `a` by `γ` lifts `γ` to the Bass–Serre tree and projects to the quotient. -/
theorem bassSerreQuotientIso_equivV_symm_of_path (hΓ : Γ.Preconnected) {b : Γ.V}
    (γ : Γ.Path a b) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivV.symm b =
      (bassSerreTree 𝔸 a).quotientMap.mapV
        (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)) :=
  (congrArg (bassSerreQuotientIso 𝔸 a hΓ).equivV.symm
    (bassSerreProjection_mapV_bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)).symm).trans
    (bassSerreQuotientIso_equivV_symm_mapV hΓ (bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ)))

/-- For preconnected `Γ`, evaluating the inverse dart equivalence of `bassSerreQuotientIso` on a
dart `e` whose source is reached from `a` by `γ` lifts `(γ, e)` to the Bass–Serre tree and projects
to the quotient. -/
theorem bassSerreQuotientIso_equivE_symm_of_path (hΓ : Γ.Preconnected) {e : Γ.E}
    (γ : Γ.Path a (Γ.src e)) :
    (bassSerreQuotientIso 𝔸 a hΓ).equivE.symm e =
      (bassSerreTree 𝔸 a).quotientMap.mapE
        (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)) :=
  (congrArg (bassSerreQuotientIso 𝔸 a hΓ).equivE.symm
    ((bassSerreProjection_mapE_bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)).trans
      (Γ.dart_val e)).symm).trans
    (bassSerreQuotientIso_equivE_symm_mapE hΓ
      (bassSerreDart ((dartPrefunctor 𝔸).mapPath γ) (Γ.dart e)))

end PreconnectedIso

end Graph

/-! ### Universal cover for trivial vertex groups -/

section Subsingleton

variable (𝔸) (a : Γ.V) [∀ b, Subsingleton (𝔸.vertexGroup b)]

/-- When all vertex groups are trivial, the vertices of `X(𝔸, a)` correspond bijectively to the
reduced edge paths of `Γ` starting at `a`. -/
noncomputable def bassSerreVertexEquivReducedPath :
    (bassSerreTree 𝔸 a).V ≃
      {q : Σ b : Γ.V, Γ.Path a b // SerreGraph.Path.IsReduced Γ q.2} :=
  (Equiv.ofBijective
    (fun q : {q : Σ b : Γ.V, Γ.Path a b // SerreGraph.Path.IsReduced Γ q.2} ↦
      bassSerreVertex ((dartPrefunctor 𝔸).mapPath q.val.2))
    ⟨fun ⟨⟨b₁, γ₁⟩, h₁⟩ ⟨⟨b₂, γ₂⟩, h₂⟩ h ↦ by
      have hb : b₁ = b₂ :=
        (bassSerreProjection_mapV_bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ₁)).symm.trans
          ((congrArg (bassSerreProjection 𝔸 a).mapV h).trans
            (bassSerreProjection_mapV_bassSerreVertex ((dartPrefunctor 𝔸).mapPath γ₂)))
      subst hb
      obtain ⟨g, hg⟩ := bassSerreVertex_eq_bassSerreVertex_iff.1 h.symm
      rw [Subsingleton.elim g 1] at hg
      have hhom : SerreGraph.Path.Homotopic Γ γ₁ γ₂ :=
        (Path.homotopic_mapPath_dartPrefunctor_iff (𝔸 := 𝔸)).1 (hg.trans (Path.Homotopic.one _))
      exact Subtype.ext (congrArg (Sigma.mk b₁) (hhom.eq_of_isReduced Γ h₁ h₂)),
    fun y ↦ bassSerreVertex_induction_on y fun {b} p ↦
      ⟨⟨⟨b, SerreGraph.Path.reduce Γ p.edgePath⟩, SerreGraph.Path.isReduced_reduce Γ p.edgePath⟩,
        bassSerreVertex_congr <|
          ((SerreGraph.Path.homotopic_reduce Γ p.edgePath).symm.mapPath_dartPrefunctor 𝔸).trans
            (Path.homotopic_mapPath_edgePath p).symm⟩⟩).symm

@[simp] theorem bassSerreVertexEquivReducedPath_symm_apply
    (q : {q : Σ b : Γ.V, Γ.Path a b // SerreGraph.Path.IsReduced Γ q.2}) :
    (bassSerreVertexEquivReducedPath 𝔸 a).symm q =
      bassSerreVertex ((dartPrefunctor 𝔸).mapPath q.val.2) :=
  (rfl)

@[simp] theorem bassSerreVertexEquivReducedPath_bassSerreVertex {b : Γ.V}
    (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    bassSerreVertexEquivReducedPath 𝔸 a (bassSerreVertex p) =
      ⟨⟨b, SerreGraph.Path.reduce Γ p.edgePath⟩,
        SerreGraph.Path.isReduced_reduce Γ p.edgePath⟩ :=
  (Equiv.eq_symm_apply _).1 <| (bassSerreVertex_congr <|
    ((SerreGraph.Path.homotopic_reduce Γ p.edgePath).symm.mapPath_dartPrefunctor 𝔸).trans
      (Path.homotopic_mapPath_edgePath p).symm).symm

end Subsingleton

end GraphOfGroups

end TauCeti
