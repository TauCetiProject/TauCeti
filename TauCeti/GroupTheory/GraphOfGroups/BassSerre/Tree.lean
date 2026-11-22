/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
single vertex.

Sending `p A_b` to `b` and `p α_e(A_e)` to `e` projects `X(𝔸, a)` onto `Γ`, and `π₁(𝔸, a)` acts
transitively on each fibre: `q p⁻¹` carries `p A_b` to `q A_b`. Hence the quotient graph
`X(𝔸, a) / π₁(𝔸, a)` maps injectively to `Γ`, onto the connected component of `a`; when `Γ` is
connected, the quotient graph is `Γ`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre tree `X(𝔸, a)`, a tree for `π₁(𝔸, a)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`: the vertex `p A_b` of an `𝔸`-path `p`.
* `TauCeti.GraphOfGroups.bassSerreDart`: the dart `p α_e(A_e)` of an `𝔸`-path `p` and a dart `e`.
* `TauCeti.GraphOfGroups.bassSerreProjection`: the projection of `X(𝔸, a)` onto `Γ`.
* `TauCeti.GraphOfGroups.bassSerreQuotientHom`: the induced morphism from the quotient graph to
  `Γ`.
* `TauCeti.GraphOfGroups.bassSerreQuotientIso`: for connected `Γ`, the quotient graph is `Γ`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreVertex_eq_bassSerreVertex_iff`,
  `TauCeti.GraphOfGroups.bassSerreDart_eq_bassSerreDart_iff`: when two paths give the same vertex
  or dart.
* `TauCeti.GraphOfGroups.src_bassSerreDart`, `TauCeti.GraphOfGroups.rev_bassSerreDart`,
  `TauCeti.GraphOfGroups.tgt_bassSerreDart`: the incidence of the tree.
* `TauCeti.GraphOfGroups.smul_bassSerreVertex`, `TauCeti.GraphOfGroups.smul_bassSerreDart`: the
  action of `π₁(𝔸, a)`.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreVertex`,
  `TauCeti.GraphOfGroups.stabilizer_bassSerreDart`: the vertex and dart stabilizers are the
  conjugates of the vertex groups and of the edge group images.
* `TauCeti.GraphOfGroups.stabilizer_bassSerreVertex_eq_bot`,
  `TauCeti.GraphOfGroups.stabilizer_dart_eq_bot_of_subsingleton`: trivial vertex groups give
  trivial vertex stabilizers, and trivial edge groups give trivial dart stabilizers.
* `TauCeti.GraphOfGroups.vertexHom_smul_bassSerreDart_eq_self_iff`,
  `TauCeti.GraphOfGroups.vertexHom_cons_smul_bassSerreDart_eq_self_iff`: which elements of the
  stabilizers of the endpoints of a dart fix the dart.
* `TauCeti.GraphOfGroups.instUniqueVBassSerreTreeOfIsEmptyE`: over a graph without edges, the
  Bass–Serre tree has exactly one vertex.
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

/-- Right multiplication by an element of `α_e(A_e)` does not change the dart `p α_e(A_e)`. -/
@[simp] theorem bassSerreDart_cons_vertex_αArrow {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (c₀ : 𝔸.edgeGroup (Γ.toGeomEdge e.val)) :
    bassSerreDart (p.cons (.vertex (𝔸.αArrow e c₀))) e = bassSerreDart p e :=
  (bassSerreDart_eq_bassSerreDart_iff.2 ⟨c₀, .refl _⟩).symm

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

/-- The fundamental group acts on darts by concatenation on the left. -/
@[simp] theorem smul_bassSerreDart (γ : 𝔸.Path ⟨a⟩ ⟨a⟩) {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : b ⟶ c) : π₁.mk γ • bassSerreDart p e = bassSerreDart (γ.comp p) e := by
  rw [bassSerreTree_smul_dart]
  exact congrArg (fun y ↦ (⟨b, c, e, y⟩ : BSDart 𝔸 a)) (PathCoset.smul_mk γ p)

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

/-- A vertex `p A_b` with trivial vertex group `A_b` has trivial stabilizer. -/
theorem stabilizer_bassSerreVertex_eq_bot {b : Γ.V} [Subsingleton (𝔸.vertexGroup b)]
    (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : stabilizer (π₁ 𝔸 a) (bassSerreVertex p) = ⊥ := by
  rw [stabilizer_bassSerreVertex, MonoidHom.range_eq_bot_iff]
  exact Subsingleton.elim _ _

/-- When every edge group is trivial, for instance for a free product, every dart of the
Bass–Serre tree has trivial stabilizer. -/
theorem stabilizer_dart_eq_bot_of_subsingleton [∀ z, Subsingleton (𝔸.edgeGroup z)]
    (d : (bassSerreTree 𝔸 a).E) : stabilizer (π₁ 𝔸 a) d = ⊥ := by
  obtain ⟨b, c, p, e, rfl⟩ := bassSerreDart_surjective d
  rw [stabilizer_bassSerreDart, MonoidHom.range_eq_bot_iff.2 (Subsingleton.elim _ _),
    Subgroup.map_bot]

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

variable (𝔸 a)

/-- The morphism from the quotient graph `X(𝔸, a) / π₁(𝔸, a)` to `Γ` induced by the projection.
It is injective, with image the connected component of `a`
(`bassSerreQuotientHom_mapV_injective`, `range_bassSerreQuotientHom_mapV`), so it is an isomorphism
when `Γ` is connected (`bassSerreQuotientIso`). -/
noncomputable def bassSerreQuotientHom : (bassSerreTree 𝔸 a).quotient.Hom Γ :=
  SerreGraph.quotientLift _ (bassSerreProjection 𝔸 a) bassSerreProjection_comp_toHom

variable {𝔸 a}

@[simp] theorem bassSerreQuotientHom_mapV_quotientMap (y : (bassSerreTree 𝔸 a).V) :
    (bassSerreQuotientHom 𝔸 a).mapV ((bassSerreTree 𝔸 a).quotientMap.mapV y) =
      (bassSerreProjection 𝔸 a).mapV y :=
  SerreGraph.quotientLift_mapV_quotientMap _ _ y

@[simp] theorem bassSerreQuotientHom_mapE_quotientMap (d : (bassSerreTree 𝔸 a).E) :
    (bassSerreQuotientHom 𝔸 a).mapE ((bassSerreTree 𝔸 a).quotientMap.mapE d) =
      (bassSerreProjection 𝔸 a).mapE d :=
  SerreGraph.quotientLift_mapE_quotientMap _ _ d

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

variable (𝔸 a)

/-- For a connected graph `Γ`, the quotient of the Bass–Serre tree by `π₁(𝔸, a)` is `Γ`. -/
noncomputable def bassSerreQuotientIso (hΓ : Γ.Preconnected) :
    (bassSerreTree 𝔸 a).quotient.Iso Γ :=
  (bassSerreQuotientHom 𝔸 a).toIso
    ⟨bassSerreQuotientHom_mapV_injective, fun b ↦
      (Set.ext_iff.1 range_bassSerreQuotientHom_mapV b).2 ((Γ.preconnected_iff.1 hΓ) a b)⟩
    ⟨bassSerreQuotientHom_mapE_injective, fun e ↦
      (Set.ext_iff.1 range_bassSerreQuotientHom_mapE e).2 ((Γ.preconnected_iff.1 hΓ) a _)⟩

variable {𝔸 a} in
/-- The isomorphism from the quotient graph to `Γ` is the morphism `bassSerreQuotientHom`. -/
@[simp] theorem bassSerreQuotientIso_toHom (hΓ : Γ.Preconnected) :
    (bassSerreQuotientIso 𝔸 a hΓ).toHom = bassSerreQuotientHom 𝔸 a :=
  SerreGraph.Hom.toIso_toHom _ _ _

end Graph

end GraphOfGroups

end TauCeti
