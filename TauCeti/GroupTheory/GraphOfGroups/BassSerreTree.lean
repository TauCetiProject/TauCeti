/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.Combinatorics.Graph.Serre.Quotient
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm
public import Mathlib.GroupTheory.Index

import Mathlib.Data.ZMod.QuotientGroup

/-!
# The Bass–Serre tree of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ` and let `v₀` be a base vertex of `Γ`. The
Bass–Serre tree `X(𝔸, v₀)` is constructed from `𝔸`-paths starting at `v₀`:

* A vertex over `a : Γ.V` is an equivalence class `p A_a` of `𝔸`-paths `p` from `v₀` to `a`,
  where `p ≈ q` when `p` is homotopic to `q g` for some `g ∈ A_a`.
* A dart over `e : Γ.E` is an equivalence class `p α_e(A_e)` of `𝔸`-paths `p` from `v₀` to
  `Γ.src e`, where `p ≈ q` when `p` is homotopic to `q α_e(c)` for some `c ∈ A_e`. Its source is
  `p A_{src e}`, its reverse is `(p e) α_{rev e}(A_e)` over `Γ.rev e`, and its target is
  `(p e) A_{tgt e}`. Because `α_{rev e}` agrees with `ω_e` across reversal and
  `e ω_e(c) ∼ α_e(c) e`, reversal is well-defined and involutive, and never fixes a dart since
  `Γ.rev e ≠ e`.

Concatenating closed `𝔸`-paths at `v₀` on the left defines an action of `π₁(𝔸, v₀)` by graph
automorphisms without inversions, because left concatenation preserves the underlying dart of `Γ`.

Every vertex `p A_a` is joined to the base vertex `1 A_{v₀}` by traversing the darts appearing in
`p`, so the graph is connected. A nonempty reduced closed path in `X(𝔸, v₀)` lifts to a reduced
alternating `𝔸`-path of positive dart length whose `𝔸`-path is homotopic to a single vertex-group
letter, contradicting `GraphOfGroups.AlternatingPath.IsReduced.not_toPath_homotopic_ofVertex`. Thus
`X(𝔸, v₀)` is a `π₁(𝔸, v₀)`-tree (`GraphOfGroups.bassSerreTree`).

For an `𝔸`-path `p` from `v₀` to `a`, the stabilizer of `p A_a` in `π₁(𝔸, v₀)` is the image
`p A_a p⁻¹` of `π₁.vertexHom p` (`GraphOfGroups.stabilizer_vertex`), isomorphic to `A_a`, and the
stabilizer of the dart `p α_e(A_e)` is `p α_e(A_e) p⁻¹` (`GraphOfGroups.stabilizer_edge`),
isomorphic to `A_e`. Forgetting the path data projects `X(𝔸, v₀)` onto `Γ.component v₀` and induces
an isomorphism `X(𝔸, v₀) / π₁(𝔸, v₀) ≅ Γ.component v₀` (`GraphOfGroups.quotientBassSerreTreeIso`),
and onto `Γ` itself when `Γ` is preconnected
(`GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`). The outgoing darts at `p A_a` are indexed
by pairs of an outgoing dart `e` of `Γ` at `a` and a left coset in `A_{src e} / α_e(A_e)`
(`GraphOfGroups.outDartEquiv`), so the degree of `p A_a` is the sum of the subgroup indices
`[A_{src e} : α_e(A_e)]`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreGraph`: the underlying `SerreGraph` of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTree`: the Bass–Serre `π₁(𝔸, v₀)`-tree `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.mkVertex`, `TauCeti.GraphOfGroups.baseVertex`,
  `TauCeti.GraphOfGroups.mkDart`: vertices, base vertex and darts of `X(𝔸, v₀)` represented by
  `𝔸`-paths.
* `TauCeti.GraphOfGroups.vertexBase`, `TauCeti.GraphOfGroups.dartBase`: the underlying vertex and
  dart in `Γ` of a vertex or dart of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.stabilizerVertexEquiv`, `TauCeti.GraphOfGroups.stabilizerEdgeEquiv`:
  isomorphisms `A_a ≃* stabilizer (p A_a)` and `A_e ≃* stabilizer (p α_e(A_e))`.
* `TauCeti.GraphOfGroups.bassSerreProj`: the `π₁(𝔸, v₀)`-invariant projection onto
  `Γ.component v₀`.
* `TauCeti.GraphOfGroups.quotientBassSerreTreeIso`,
  `TauCeti.GraphOfGroups.quotientBassSerreTreeIsoOfPreconnected`: the quotient graph of `X(𝔸, v₀)`
  by `π₁(𝔸, v₀)` is isomorphic to `Γ.component v₀`, and to `Γ` when `Γ` is preconnected.
* `TauCeti.GraphOfGroups.outDartEquiv`: outgoing darts at `p A_a` correspond to
  `Σ e : {e : Γ.E // Γ.src e = a}, A_{src e} ⧸ α_e(A_e)`.
* `TauCeti.GraphOfGroups.freeProduct`: the segment graph of groups of a free product `A ∗ B`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `X(𝔸, v₀)` is a tree.
* `TauCeti.GraphOfGroups.stabilizer_vertex`, `TauCeti.GraphOfGroups.stabilizer_edge`,
  `TauCeti.GraphOfGroups.stabilizer_edge_comp_ofVertex`: vertex and dart stabilizers in
  `π₁(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.isEmpty_quotientBassSerreTree_iso_of_not_preconnected`: over a
  disconnected graph `Γ`, `X(𝔸, v₀) / π₁(𝔸, v₀)` is not isomorphic to `Γ`.
* `TauCeti.GraphOfGroups.mk_outDart_eq_sum`, `TauCeti.GraphOfGroups.card_outDart_eq_sum_index`:
  cardinal and finite degree formulas at a vertex of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.card_outDart_baumslagSolitar`,
  `TauCeti.GraphOfGroups.card_outDart_baumslagSolitar_one_two`: every vertex of the Bass–Serre tree
  of `BS(m, n)` has degree `|m| + |n|` (`3` for `BS(1, 2)`).
* `TauCeti.GraphOfGroups.mk_outDart_freeProduct_int`: every vertex of the Bass–Serre tree of
  `ℤ ∗ ℤ` has countably infinite degree `ℵ₀`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

open SerreGraph _root_.MulAction
open scoped Cardinal

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-! ### Equivalence relations on `𝔸`-paths and the underlying graph -/

/-- Two `𝔸`-paths from `v₀` to `a` represent the same vertex coset `p A_a` when `p` is homotopic to
`q g` for some `g ∈ A_a`. -/
@[expose] def vertexRel (a : Γ.V) (p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩) : Prop :=
  ∃ g : 𝔸.vertexGroup a, p.Homotopic (q.comp (Path.ofVertex g))

/-- Homotopic `𝔸`-paths represent the same vertex coset. -/
theorem vertexRel_of_homotopic {a : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q) :
    𝔸.vertexRel v₀ a p q :=
  ⟨1, by rw [Path.comp_ofVertex]; exact h.trans (Path.Homotopic.one q).symm⟩

/-- Right multiplication by `A_a` up to homotopy is an equivalence relation on `𝔸`-paths from `v₀`
to `a`. -/
theorem vertexRel_equivalence (a : Γ.V) : Equivalence (𝔸.vertexRel v₀ a) where
  refl p := 𝔸.vertexRel_of_homotopic v₀ (.refl p)
  symm := by
    rintro p q ⟨g, h⟩
    refine ⟨g⁻¹, ((h.comp_right (Path.ofVertex g⁻¹)).trans ?_).symm⟩
    rw [Path.comp_ofVertex, Path.comp_ofVertex]
    exact (Path.Homotopic.mul q g g⁻¹).trans (by rw [mul_inv_cancel]; exact Path.Homotopic.one q)
  trans := by
    rintro p q r ⟨g, hp⟩ ⟨k, hq⟩
    refine ⟨k * g, (hp.trans (hq.comp_right (Path.ofVertex g))).trans ?_⟩
    rw [Path.comp_ofVertex, Path.comp_ofVertex, Path.comp_ofVertex]
    exact Path.Homotopic.mul r k g

/-- The setoid of `𝔸`-paths from `v₀` to `a` modulo right multiplication by `A_a`. -/
@[expose] def vertexSetoid (a : Γ.V) : Setoid (𝔸.Path ⟨v₀⟩ ⟨a⟩) :=
  ⟨𝔸.vertexRel v₀ a, 𝔸.vertexRel_equivalence v₀ a⟩

/-- Two `𝔸`-paths from `v₀` to `Γ.src e` represent the same dart coset `p α_e(A_e)` when `p` is
homotopic to `q α_e(c)` for some `c ∈ A_e`. -/
@[expose] def dartRel (e : Γ.E) (p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : Prop :=
  ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.comp (Path.ofVertex (𝔸.α e c)))

/-- Homotopic `𝔸`-paths represent the same dart coset. -/
theorem dartRel_of_homotopic {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    𝔸.dartRel v₀ e p q :=
  ⟨1, by rw [map_one, Path.comp_ofVertex]; exact h.trans (Path.Homotopic.one q).symm⟩

/-- Right multiplication by `α_e(A_e)` up to homotopy is an equivalence relation on `𝔸`-paths from
`v₀` to `Γ.src e`. -/
theorem dartRel_equivalence (e : Γ.E) : Equivalence (𝔸.dartRel v₀ e) where
  refl p := 𝔸.dartRel_of_homotopic v₀ (.refl p)
  symm := by
    rintro p q ⟨c, h⟩
    refine ⟨c⁻¹, ((h.comp_right (Path.ofVertex (𝔸.α e c⁻¹))).trans ?_).symm⟩
    rw [map_inv, Path.comp_ofVertex, Path.comp_ofVertex]
    exact (Path.Homotopic.mul q (𝔸.α e c) (𝔸.α e c)⁻¹).trans
      (by rw [mul_inv_cancel]; exact Path.Homotopic.one q)
  trans := by
    rintro p q r ⟨c₁, hp⟩ ⟨c₂, hq⟩
    refine ⟨c₂ * c₁, (hp.trans (hq.comp_right (Path.ofVertex (𝔸.α e c₁)))).trans ?_⟩
    rw [map_mul, Path.comp_ofVertex, Path.comp_ofVertex, Path.comp_ofVertex]
    exact Path.Homotopic.mul r (𝔸.α e c₂) (𝔸.α e c₁)

/-- The setoid of `𝔸`-paths from `v₀` to `Γ.src e` modulo right multiplication by `α_e(A_e)`. -/
@[expose] def dartSetoid (e : Γ.E) : Setoid (𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :=
  ⟨𝔸.dartRel v₀ e, 𝔸.dartRel_equivalence v₀ e⟩

/-- Reversing a dart sends equivalent `𝔸`-paths at `Γ.src e` to equivalent `𝔸`-paths at
`Γ.src (Γ.rev e)`. -/
theorem dartRel_rev_cons (e : Γ.E) {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    (h : 𝔸.dartRel v₀ e p q) :
    𝔸.dartRel v₀ (Γ.rev e)
      (p.cons (Letter.dart (Γ.dart e)))
      (q.cons (Letter.dart (Γ.dart e))) := by
  obtain ⟨c, hc⟩ := h
  rw [Path.comp_ofVertex] at hc
  have hα : 𝔸.α (Γ.rev e) ((MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c) =
      𝔸.ω e c := by
    rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
  refine ⟨(MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c, ?_⟩
  have hcomp :
      ((q.cons (Letter.dart (Γ.dart e))).comp
        (Path.ofVertex
          (𝔸.α (Γ.rev e) ((MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c)))) =
      (q.cons (Letter.dart (Γ.dart e))).cons (Letter.vertex (𝔸.ω e c)) :=
    (Path.comp_ofVertex (q.cons (Letter.dart (Γ.dart e))) _).trans
      (congrArg (fun x => (q.cons (Letter.dart (Γ.dart e))).cons (Letter.vertex x)) hα)
  exact hcomp.symm ▸ (hc.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.dart_ω e c q).symm

/-- The underlying Serre graph of the Bass–Serre tree `X(𝔸, v₀)`: vertices are pairs `(a, p A_a)`
and darts are pairs `(e, p α_e(A_e))`. The body is exposed so Lean's module code generator can
compile functions on vertices and darts; use `mkVertex`, `mkDart`, `vertexBase`, and `dartBase` to
work with them. -/
@[expose] def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := Σ a : Γ.V, Quotient (𝔸.vertexSetoid v₀ a)
  E := Σ e : Γ.E, Quotient (𝔸.dartSetoid v₀ e)
  src d := ⟨Γ.src d.1,
    @Quotient.map _ _ (𝔸.dartSetoid v₀ d.1) (𝔸.vertexSetoid v₀ (Γ.src d.1)) id
      (by rintro _ _ ⟨c, hc⟩; exact ⟨𝔸.α d.1 c, hc⟩) d.2⟩
  rev d := ⟨Γ.rev d.1,
    @Quotient.map _ _ (𝔸.dartSetoid v₀ d.1) (𝔸.dartSetoid v₀ (Γ.rev d.1))
      (fun p => p.cons (Letter.dart (Γ.dart d.1)))
      (fun _ _ => 𝔸.dartRel_rev_cons v₀ d.1) d.2⟩
  rev_rev := by
    rintro ⟨e, q⟩
    refine Quotient.inductionOn q fun p => ?_
    let q₀ : 𝔸.Path ⟨v₀⟩ ⟨Γ.tgt e⟩ := p.cons (Letter.dart (Γ.dart e))
    have key : ∀ (e' : Γ.E) (_ : e = e') (f : Γ.tgt e ⟶ Γ.src e'), f.1 = Γ.rev e →
        (⟨e', Quotient.mk (𝔸.dartSetoid v₀ e') (q₀.cons (Letter.dart f))⟩ :
          Σ d : Γ.E, Quotient (𝔸.dartSetoid v₀ d)) =
          ⟨e, Quotient.mk (𝔸.dartSetoid v₀ e)
            (q₀.cons (Letter.dart (Quiver.reverse (Γ.dart e))))⟩ := by
      rintro _ rfl f hf
      rw [Γ.eq_reverse_of_val_eq_rev (hf.trans (congrArg Γ.rev (Γ.dart_val e).symm))]
    refine (key (Γ.rev (Γ.rev e)) (Γ.rev_rev e).symm (Γ.dart (Γ.rev e))
      (Γ.dart_val (Γ.rev e))).trans ?_
    exact congrArg (Sigma.mk e)
      (Quotient.sound (𝔸.dartRel_of_homotopic v₀ (Path.Homotopic.dart_reverse p (Γ.dart e))))
  rev_ne := by
    rintro ⟨e, _⟩ h
    exact Γ.rev_ne e (congrArg Sigma.fst h)

/-! ### Left action of `π₁(𝔸, v₀)` -/

private def smulVertexPath (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (𝔸.bassSerreGraph v₀).V → (𝔸.bassSerreGraph v₀).V
  | ⟨a, q⟩ =>
    ⟨a, @Quotient.map _ _ (𝔸.vertexSetoid v₀ a) (𝔸.vertexSetoid v₀ a) (fun p => γ.comp p)
      (by rintro _ _ ⟨g, h⟩; exact ⟨g, Quiver.Path.comp_assoc γ _ _ ▸ h.comp_left γ⟩) q⟩

private theorem smulVertexPath_congr {γ₁ γ₂ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩} (h : γ₁.Homotopic γ₂)
    (u : (𝔸.bassSerreGraph v₀).V) :
    smulVertexPath 𝔸 v₀ γ₁ u = smulVertexPath 𝔸 v₀ γ₂ u := by
  obtain ⟨a, q⟩ := u
  exact Quotient.inductionOn q fun p =>
    congrArg (Sigma.mk a) (Quotient.sound (𝔸.vertexRel_of_homotopic v₀ (h.comp_right p)))

private def smulVertex (x : π₁ 𝔸 v₀) (u : (𝔸.bassSerreGraph v₀).V) : (𝔸.bassSerreGraph v₀).V :=
  π₁.lift (fun γ => smulVertexPath 𝔸 v₀ γ u) (fun _ _ h => smulVertexPath_congr 𝔸 v₀ h u) x

@[simp] private theorem smulVertex_mk (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (u : (𝔸.bassSerreGraph v₀).V) :
    smulVertex 𝔸 v₀ (π₁.mk γ) u = smulVertexPath 𝔸 v₀ γ u :=
  π₁.lift_mk _ _ γ

private theorem smulVertex_one (u : (𝔸.bassSerreGraph v₀).V) :
    smulVertex 𝔸 v₀ 1 u = u := by
  rw [← π₁.mk_nil, smulVertex_mk]
  obtain ⟨a, q⟩ := u
  exact Quotient.inductionOn q fun p =>
    congrArg (Sigma.mk a) (congrArg (Quotient.mk (𝔸.vertexSetoid v₀ a)) (Quiver.Path.nil_comp p))

private theorem smulVertex_mul (x y : π₁ 𝔸 v₀) (u : (𝔸.bassSerreGraph v₀).V) :
    smulVertex 𝔸 v₀ (x * y) u = smulVertex 𝔸 v₀ x (smulVertex 𝔸 v₀ y u) :=
  π₁.induction_on x fun γ₁ => π₁.induction_on y fun γ₂ => by
    rw [← π₁.mk_comp, smulVertex_mk, smulVertex_mk, smulVertex_mk]
    obtain ⟨a, q⟩ := u
    exact Quotient.inductionOn q fun p =>
      congrArg (Sigma.mk a)
        (congrArg (Quotient.mk (𝔸.vertexSetoid v₀ a)) (Quiver.Path.comp_assoc γ₁ γ₂ p))

private def smulDartPath (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (𝔸.bassSerreGraph v₀).E → (𝔸.bassSerreGraph v₀).E
  | ⟨e, q⟩ =>
    ⟨e, @Quotient.map _ _ (𝔸.dartSetoid v₀ e) (𝔸.dartSetoid v₀ e) (fun p => γ.comp p)
      (by rintro _ _ ⟨c, h⟩; exact ⟨c, Quiver.Path.comp_assoc γ _ _ ▸ h.comp_left γ⟩) q⟩

private theorem smulDartPath_congr {γ₁ γ₂ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩} (h : γ₁.Homotopic γ₂)
    (d : (𝔸.bassSerreGraph v₀).E) :
    smulDartPath 𝔸 v₀ γ₁ d = smulDartPath 𝔸 v₀ γ₂ d := by
  obtain ⟨e, q⟩ := d
  exact Quotient.inductionOn q fun p =>
    congrArg (Sigma.mk e) (Quotient.sound (𝔸.dartRel_of_homotopic v₀ (h.comp_right p)))

private def smulDart (x : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) : (𝔸.bassSerreGraph v₀).E :=
  π₁.lift (fun γ => smulDartPath 𝔸 v₀ γ d) (fun _ _ h => smulDartPath_congr 𝔸 v₀ h d) x

@[simp] private theorem smulDart_mk (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (d : (𝔸.bassSerreGraph v₀).E) :
    smulDart 𝔸 v₀ (π₁.mk γ) d = smulDartPath 𝔸 v₀ γ d :=
  π₁.lift_mk _ _ γ

private theorem smulDart_one (d : (𝔸.bassSerreGraph v₀).E) :
    smulDart 𝔸 v₀ 1 d = d := by
  rw [← π₁.mk_nil, smulDart_mk]
  obtain ⟨e, q⟩ := d
  exact Quotient.inductionOn q fun p =>
    congrArg (Sigma.mk e) (congrArg (Quotient.mk (𝔸.dartSetoid v₀ e)) (Quiver.Path.nil_comp p))

private theorem smulDart_mul (x y : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    smulDart 𝔸 v₀ (x * y) d = smulDart 𝔸 v₀ x (smulDart 𝔸 v₀ y d) :=
  π₁.induction_on x fun γ₁ => π₁.induction_on y fun γ₂ => by
    rw [← π₁.mk_comp, smulDart_mk, smulDart_mk, smulDart_mk]
    obtain ⟨e, q⟩ := d
    exact Quotient.inductionOn q fun p =>
      congrArg (Sigma.mk e)
        (congrArg (Quotient.mk (𝔸.dartSetoid v₀ e)) (Quiver.Path.comp_assoc γ₁ γ₂ p))

private theorem smulDart_src (x : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    (𝔸.bassSerreGraph v₀).src (smulDart 𝔸 v₀ x d) =
      smulVertex 𝔸 v₀ x ((𝔸.bassSerreGraph v₀).src d) :=
  π₁.induction_on x fun _ => by
    rw [smulDart_mk, smulVertex_mk]
    obtain ⟨_, q⟩ := d
    exact Quotient.inductionOn q fun _ => rfl

private theorem smulDart_rev (x : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    smulDart 𝔸 v₀ x ((𝔸.bassSerreGraph v₀).rev d) =
      (𝔸.bassSerreGraph v₀).rev (smulDart 𝔸 v₀ x d) :=
  π₁.induction_on x fun _ => by
    rw [smulDart_mk, smulDart_mk]
    obtain ⟨_, q⟩ := d
    exact Quotient.inductionOn q fun _ => rfl

/-- The action of `π₁(𝔸, v₀)` on `bassSerreGraph` by left concatenation of closed `𝔸`-paths. -/
def bassSerreAction : π₁ 𝔸 v₀ →* (𝔸.bassSerreGraph v₀).Aut where
  toFun x :=
    { equivV :=
        { toFun := smulVertex 𝔸 v₀ x
          invFun := smulVertex 𝔸 v₀ x⁻¹
          left_inv u := by rw [← smulVertex_mul, inv_mul_cancel, smulVertex_one]
          right_inv u := by rw [← smulVertex_mul, mul_inv_cancel, smulVertex_one] }
      equivE :=
        { toFun := smulDart 𝔸 v₀ x
          invFun := smulDart 𝔸 v₀ x⁻¹
          left_inv d := by rw [← smulDart_mul, inv_mul_cancel, smulDart_one]
          right_inv d := by rw [← smulDart_mul, mul_inv_cancel, smulDart_one] }
      map_src := smulDart_src 𝔸 v₀ x
      map_rev := smulDart_rev 𝔸 v₀ x }
  map_one' := Iso.ext (smulVertex_one 𝔸 v₀) (smulDart_one 𝔸 v₀)
  map_mul' x y := Iso.ext (smulVertex_mul 𝔸 v₀ x y) (smulDart_mul 𝔸 v₀ x y)

/-- Left concatenation of closed `𝔸`-paths preserves the underlying dart in `Γ`, so no element of
`π₁(𝔸, v₀)` inverts a dart of `bassSerreGraph`. -/
theorem bassSerreAction_smul_ne_rev (x : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    (𝔸.bassSerreAction v₀ x).equivE d ≠ (𝔸.bassSerreGraph v₀).rev d :=
  π₁.induction_on x fun γ h => by
    obtain ⟨e, q⟩ := d
    exact (Γ.rev_ne e).symm (congrArg Sigma.fst ((smulDart_mk 𝔸 v₀ γ ⟨e, q⟩).symm.trans h))

/-! ### Connectedness and acyclicity -/

section IsTree

/-- Every vertex of `bassSerreGraph` is reachable from `1 A_{v₀}` by traversing the darts of a
representing `𝔸`-path. -/
private theorem bassSerreGraph_reachable {y : 𝔸.LetterVertex} (p : 𝔸.Path ⟨v₀⟩ y) :
    Nonempty ((𝔸.bassSerreGraph v₀).Path
      ⟨v₀, Quotient.mk (𝔸.vertexSetoid v₀ v₀) .nil⟩
      ⟨y.as, Quotient.mk (𝔸.vertexSetoid v₀ y.as) p⟩) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | cons p l ih =>
    cases l with
    | vertex g =>
      have heq :
          (⟨_, Quotient.mk (𝔸.vertexSetoid v₀ _) (p.cons (Letter.vertex g))⟩ :
            (𝔸.bassSerreGraph v₀).V) =
          ⟨_, Quotient.mk (𝔸.vertexSetoid v₀ _) p⟩ :=
        congrArg (Sigma.mk _) (Quotient.sound ⟨g, by rw [Path.comp_ofVertex]; exact .refl _⟩)
      exact heq ▸ ih
    | dart e =>
      obtain ⟨d, rfl, rfl⟩ := e
      exact ih.map fun q =>
        q.cons
          (⟨⟨d, Quotient.mk (𝔸.dartSetoid v₀ d) p⟩, rfl,
            congrArg (Sigma.mk _) (congrArg (Quotient.mk _)
              (congrArg (Quiver.Path.cons p ∘ Letter.dart) (Γ.dart_def d)))⟩ :
            Quiver.Hom (V := (𝔸.bassSerreGraph v₀).V) _ _)

/-- The Bass–Serre graph is connected. -/
theorem bassSerreGraph_connected : (𝔸.bassSerreGraph v₀).Connected := by
  refine ((𝔸.bassSerreGraph v₀).connected_iff).mpr
    ⟨⟨⟨v₀, Quotient.mk (𝔸.vertexSetoid v₀ v₀) .nil⟩⟩, ?_⟩
  refine preconnected_of_forall_nonempty_path _
    ⟨v₀, Quotient.mk (𝔸.vertexSetoid v₀ v₀) .nil⟩ ?_
  rintro ⟨a, q⟩
  obtain ⟨p, rfl⟩ := Quotient.exists_rep q
  exact bassSerreGraph_reachable 𝔸 v₀ p

/-- Unpack a dart of `bassSerreGraph` whose source is `⟨b, ⟦r₀⟧⟩`. -/
private theorem exists_dart_of_src_eq {b : Γ.V} {r₀ : 𝔸.Path ⟨v₀⟩ ⟨b⟩}
    {d : (𝔸.bassSerreGraph v₀).E}
    (hd : (𝔸.bassSerreGraph v₀).src d = ⟨b, Quotient.mk (𝔸.vertexSetoid v₀ b) r₀⟩) :
    ∃ (e : Γ.E) (hs : Γ.src e = b) (g : 𝔸.vertexGroup b),
      (𝔸.bassSerreGraph v₀).tgt d =
        ⟨Γ.tgt e, Quotient.mk (𝔸.vertexSetoid v₀ (Γ.tgt e))
          ((r₀.cons (Letter.vertex g)).cons (Letter.dart ⟨e, hs, rfl⟩))⟩ ∧
      (𝔸.bassSerreGraph v₀).rev d =
        ⟨Γ.rev e, Quotient.mk (𝔸.dartSetoid v₀ (Γ.rev e))
          ((r₀.cons (Letter.vertex g)).cons (Letter.dart ⟨e, hs, rfl⟩))⟩ ∧
      ∀ (e' : Γ.E) (r' : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e'⟩),
        (⟨b, r₀⟩ : Σ x : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨x⟩) = ⟨Γ.src e', r'⟩ →
        (d = ⟨e', Quotient.mk (𝔸.dartSetoid v₀ e') r'⟩ ↔
          e = e' ∧ g ∈ (𝔸.αArrow (⟨e, hs, rfl⟩ : b ⟶ Γ.tgt e)).range) := by
  obtain ⟨e, qbar⟩ := d
  obtain ⟨q, rfl⟩ := Quotient.exists_rep qbar
  have hs : Γ.src e = b := congrArg Sigma.fst hd
  subst hs
  obtain ⟨g, hq⟩ : 𝔸.vertexRel v₀ (Γ.src e) q r₀ :=
    Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp hd).2)
  have hd_eq : (⟨e, Quotient.mk (𝔸.dartSetoid v₀ e) q⟩ : (𝔸.bassSerreGraph v₀).E) =
      ⟨e, Quotient.mk (𝔸.dartSetoid v₀ e) (r₀.cons (Letter.vertex g))⟩ := by
    rw [← Path.comp_ofVertex]
    exact congrArg (Sigma.mk e) (Quotient.sound (𝔸.dartRel_of_homotopic v₀ hq))
  refine ⟨e, rfl, g, ?_, ?_, fun e' r' hpair => ?_⟩
  · refine (congrArg (𝔸.bassSerreGraph v₀).tgt hd_eq).trans ?_
    exact congrArg (Sigma.mk (Γ.tgt e)) (congrArg (Quotient.mk _)
      (congrArg (fun x => (r₀.cons (Letter.vertex g)).cons (Letter.dart x)) (Γ.dart_def e)))
  · refine (congrArg (𝔸.bassSerreGraph v₀).rev hd_eq).trans ?_
    exact congrArg (Sigma.mk (Γ.rev e)) (congrArg (Quotient.mk _)
      (congrArg (fun x => (r₀.cons (Letter.vertex g)).cons (Letter.dart x)) (Γ.dart_def e)))
  · rw [hd_eq, αArrow_mk]
    refine ⟨fun h => ?_, ?_⟩
    · have he : e = e' := congrArg Sigma.fst h
      subst he
      obtain rfl : r₀ = r' := eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
      obtain ⟨c, hc⟩ : 𝔸.dartRel v₀ e (r₀.cons (Letter.vertex g)) r₀ :=
        Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      rw [← Path.comp_ofVertex] at hc
      exact ⟨rfl, c, (Path.ofVertex_homotopic_ofVertex_iff.mp hc.of_comp_left).symm⟩
    · rintro ⟨rfl, c, hc⟩
      obtain rfl : r₀ = r' := eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
      refine congrArg (Sigma.mk e) (Quotient.sound ⟨c, ?_⟩)
      rw [← hc, Path.comp_ofVertex]
      exact .refl _

/-- Lift a nonempty reduced path in `bassSerreGraph` starting at `⟨a, ⟦p₀⟧⟩` to a reduced
alternating `𝔸`-path of positive dart length. -/
private theorem lift_reduced_path {a : Γ.V} (p₀ : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    {v : (𝔸.bassSerreGraph v₀).V}
    (P : (𝔸.bassSerreGraph v₀).Path
      (⟨a, Quotient.mk (𝔸.vertexSetoid v₀ a) p₀⟩ : (𝔸.bassSerreGraph v₀).V) v) :
    ∀ {w : (𝔸.bassSerreGraph v₀).V} (f : v ⟶ w),
      SerreGraph.Path.IsReduced (𝔸.bassSerreGraph v₀) (P.cons f) →
      ∃ (b : Γ.V) (r : 𝔸.AlternatingPath a b) (e₀ : Γ.E) (hs : Γ.src e₀ = b),
        (r.cons ⟨e₀, hs, rfl⟩ 1).IsReduced ∧
        w = ⟨Γ.tgt e₀, Quotient.mk (𝔸.vertexSetoid v₀ (Γ.tgt e₀))
          (p₀.comp (r.cons ⟨e₀, hs, rfl⟩ 1).toPath)⟩ ∧
        (𝔸.bassSerreGraph v₀).rev f.1 =
          ⟨Γ.rev e₀, Quotient.mk (𝔸.dartSetoid v₀ (Γ.rev e₀))
            (p₀.comp (r.cons ⟨e₀, hs, rfl⟩ 1).toPath)⟩ := by
  induction P with
  | nil =>
    intro w f _
    obtain ⟨e₀, hs₀, g, htgt, hrev, -⟩ := exists_dart_of_src_eq 𝔸 v₀ f.2.1
    have hhom :
        Path.Homotopic (p₀.comp ((AlternatingPath.single g).cons ⟨e₀, hs₀, rfl⟩ 1).toPath)
          ((p₀.cons (Letter.vertex g)).cons (Letter.dart ⟨e₀, hs₀, rfl⟩)) := by
      simp only [AlternatingPath.toPath_cons, AlternatingPath.toPath_single,
        Path.ofVertex_eq_nil_cons, Quiver.Path.comp_cons, Quiver.Path.comp_nil]
      exact Path.Homotopic.one _
    exact ⟨a, .single g, e₀, hs₀,
      (AlternatingPath.isReduced_cons_iff _ _ _).mpr
        ⟨AlternatingPath.isReduced_single g, AlternatingPath.not_cancels_single g _⟩,
      f.2.2.symm.trans
        (htgt.trans (congrArg (Sigma.mk _)
          (Quotient.sound (𝔸.vertexRel_of_homotopic v₀ hhom.symm)))),
      hrev.trans (congrArg (Sigma.mk _) (Quotient.sound (𝔸.dartRel_of_homotopic v₀ hhom.symm)))⟩
  | cons P f₀ ih =>
    intro w f₁ hred
    obtain ⟨hred₀, hne⟩ :=
      (SerreGraph.Path.isReduced_cons_cons (𝔸.bassSerreGraph v₀) P f₀ f₁).mp hred
    obtain ⟨b₀, r, e₀, hs₀, hq_red, hv, hf₀_rev⟩ := ih f₀ hred₀
    let q : 𝔸.AlternatingPath a (Γ.tgt e₀) := r.cons ⟨e₀, hs₀, rfl⟩ 1
    obtain ⟨e₁, hs₁, g, htgt, hrev, hiff⟩ := exists_dart_of_src_eq 𝔸 v₀ (f₁.2.1.trans hv)
    have hnot : ¬ (r.cons ⟨e₀, hs₀, rfl⟩ g).Cancels ⟨e₁, hs₁, rfl⟩ := by
      rw [AlternatingPath.cancels_cons_iff]
      rintro ⟨he, hg⟩
      have he' : e₁ = Γ.rev e₀ := by
        simpa only [Γ.rev_rev] using (congrArg Γ.rev he).symm
      exact hne ((hiff (Γ.rev e₀) (p₀.comp q.toPath) rfl).mpr ⟨he', hg⟩ ▸ hf₀_rev.symm)
    have hhom :
        Path.Homotopic (p₀.comp ((r.cons ⟨e₀, hs₀, rfl⟩ g).cons ⟨e₁, hs₁, rfl⟩ 1).toPath)
          (((p₀.comp q.toPath).cons (Letter.vertex g)).cons (Letter.dart ⟨e₁, hs₁, rfl⟩)) := by
      have hset : Path.Homotopic (r.cons ⟨e₀, hs₀, rfl⟩ g).toPath
          (q.toPath.cons (Letter.vertex g)) := by
        simpa [q] using q.toPath_setLast_mul_homotopic g
      rw [AlternatingPath.toPath_cons, Quiver.Path.comp_cons, Quiver.Path.comp_cons,
        ← Quiver.Path.comp_cons p₀ q.toPath]
      exact (Path.Homotopic.one _).trans ((hset.comp_left p₀).cons _)
    exact ⟨Γ.tgt e₀, r.cons ⟨e₀, hs₀, rfl⟩ g, e₁, hs₁,
      (AlternatingPath.isReduced_cons_iff _ _ _).mpr
        ⟨(AlternatingPath.isReduced_cons_iff _ _ _).mpr
          ((AlternatingPath.isReduced_cons_iff _ _ _).mp hq_red), hnot⟩,
      f₁.2.2.symm.trans
        (htgt.trans (congrArg (Sigma.mk _)
          (Quotient.sound (𝔸.vertexRel_of_homotopic v₀ hhom.symm)))),
      hrev.trans (congrArg (Sigma.mk _) (Quotient.sound (𝔸.dartRel_of_homotopic v₀ hhom.symm)))⟩

/-- The Bass–Serre graph is acyclic. -/
theorem bassSerreGraph_isAcyclic : (𝔸.bassSerreGraph v₀).IsAcyclic := by
  refine (𝔸.bassSerreGraph v₀).isAcyclic_iff.mpr fun u P hP => ?_
  cases P with
  | nil => rfl
  | cons P f =>
    obtain ⟨a, ubar⟩ := u
    obtain ⟨p₀, rfl⟩ := Quotient.exists_rep ubar
    obtain ⟨b, r, e₀, hs₀, hq_red, hu, -⟩ := lift_reduced_path 𝔸 v₀ p₀ P f hP
    have htgt : Γ.tgt e₀ = a := (congrArg Sigma.fst hu).symm
    cases htgt
    obtain ⟨g, hg⟩ : 𝔸.vertexRel v₀ (Γ.tgt e₀)
        (p₀.comp (r.cons ⟨e₀, hs₀, rfl⟩ 1).toPath) p₀ :=
      Quotient.exact (eq_of_heq (Sigma.mk.inj_iff.mp hu.symm).2)
    have hpos : 0 < (r.cons ⟨e₀, hs₀, rfl⟩ 1).dartLength :=
      (AlternatingPath.dartLength_cons r ⟨e₀, hs₀, rfl⟩ 1).symm ▸ Nat.succ_pos r.dartLength
    exact (hq_red.not_toPath_homotopic_ofVertex hpos g hg.of_comp_left).elim

/-- The Bass–Serre graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree : (𝔸.bassSerreGraph v₀).IsTree :=
  ((𝔸.bassSerreGraph v₀).isTree_iff).mpr
    ⟨𝔸.bassSerreGraph_connected v₀, 𝔸.bassSerreGraph_isAcyclic v₀⟩

end IsTree

/-! ### The Bass–Serre `π₁(𝔸, v₀)`-tree and its constructors -/

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`, as a
`π₁(𝔸, v₀)`-tree: its vertices are the cosets `p A_a` of `𝔸`-paths from `v₀` to `a`, its darts
are the cosets `p α_e(A_e)` of `𝔸`-paths from `v₀` to `src e`, and `π₁(𝔸, v₀)` acts on the left by
path concatenation without inversions. -/
@[expose] def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := 𝔸.bassSerreGraph v₀
  isTree := 𝔸.bassSerreTree_isTree v₀
  action := 𝔸.bassSerreAction v₀
  action_smul_ne_rev := 𝔸.bassSerreAction_smul_ne_rev v₀

theorem bassSerreTree_toSerreGraph :
    (𝔸.bassSerreTree v₀).toSerreGraph = 𝔸.bassSerreGraph v₀ :=
  (rfl)

theorem bassSerreTree_action :
    (𝔸.bassSerreTree v₀).action = 𝔸.bassSerreAction v₀ :=
  (rfl)

/-- The vertex coset `p A_a` of `X(𝔸, v₀)` represented by an `𝔸`-path `p` from `v₀` to `a`. -/
def mkVertex (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) : (𝔸.bassSerreTree v₀).V :=
  ⟨a, Quotient.mk (𝔸.vertexSetoid v₀ a) p⟩

/-- The base vertex `1 A_{v₀}` of `X(𝔸, v₀)`, represented by the empty path at `v₀`. -/
def baseVertex : (𝔸.bassSerreTree v₀).V :=
  𝔸.mkVertex v₀ v₀ .nil

/-- The dart coset `p α_e(A_e)` of `X(𝔸, v₀)` over `e : Γ.E` represented by an `𝔸`-path `p` from
`v₀` to `Γ.src e`. -/
def mkDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreTree v₀).E :=
  ⟨e, Quotient.mk (𝔸.dartSetoid v₀ e) p⟩

/-- The underlying vertex of `Γ` beneath a vertex of `X(𝔸, v₀)`. -/
def vertexBase (u : (𝔸.bassSerreTree v₀).V) : Γ.V :=
  u.1

/-- The underlying dart of `Γ` beneath a dart of `X(𝔸, v₀)`. -/
def dartBase (d : (𝔸.bassSerreTree v₀).E) : Γ.E :=
  d.1

@[simp] theorem vertexBase_mkVertex (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    𝔸.vertexBase v₀ (𝔸.mkVertex v₀ a p) = a :=
  (rfl)

@[simp] theorem vertexBase_baseVertex : 𝔸.vertexBase v₀ (𝔸.baseVertex v₀) = v₀ :=
  (rfl)

@[simp] theorem dartBase_mkDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.dartBase v₀ (𝔸.mkDart v₀ e p) = e :=
  (rfl)

@[simp] theorem vertexBase_src (d : (𝔸.bassSerreTree v₀).E) :
    𝔸.vertexBase v₀ ((𝔸.bassSerreTree v₀).src d) = Γ.src (𝔸.dartBase v₀ d) :=
  (rfl)

@[simp] theorem dartBase_rev (d : (𝔸.bassSerreTree v₀).E) :
    𝔸.dartBase v₀ ((𝔸.bassSerreTree v₀).rev d) = Γ.rev (𝔸.dartBase v₀ d) :=
  (rfl)

@[simp] theorem vertexBase_tgt (d : (𝔸.bassSerreTree v₀).E) :
    𝔸.vertexBase v₀ ((𝔸.bassSerreTree v₀).tgt d) = Γ.tgt (𝔸.dartBase v₀ d) :=
  (rfl)

/-- Every vertex of `X(𝔸, v₀)` is of the form `mkVertex v₀ a p`. -/
theorem exists_mkVertex (u : (𝔸.bassSerreTree v₀).V) :
    ∃ (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩), u = 𝔸.mkVertex v₀ a p := by
  obtain ⟨a, q⟩ := u
  obtain ⟨p, rfl⟩ := Quotient.exists_rep q
  exact ⟨a, p, rfl⟩

/-- Every dart of `X(𝔸, v₀)` is of the form `mkDart v₀ e p`. -/
theorem exists_mkDart (d : (𝔸.bassSerreTree v₀).E) :
    ∃ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), d = 𝔸.mkDart v₀ e p := by
  obtain ⟨e, q⟩ := d
  obtain ⟨p, rfl⟩ := Quotient.exists_rep q
  exact ⟨e, p, rfl⟩

/-- Homotopic `𝔸`-paths represent the same vertex of `X(𝔸, v₀)`. -/
theorem mkVertex_congr {a : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q) :
    𝔸.mkVertex v₀ a p = 𝔸.mkVertex v₀ a q :=
  congrArg (Sigma.mk a) (Quotient.sound (𝔸.vertexRel_of_homotopic v₀ h))

/-- Homotopic `𝔸`-paths represent the same dart of `X(𝔸, v₀)`. -/
theorem mkDart_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    𝔸.mkDart v₀ e p = 𝔸.mkDart v₀ e q :=
  congrArg (Sigma.mk e) (Quotient.sound (𝔸.dartRel_of_homotopic v₀ h))

/-- Two `𝔸`-paths to `a` represent the same vertex of `X(𝔸, v₀)` exactly when they differ on the
right by an element of `A_a` up to homotopy. -/
theorem mkVertex_same_eq_iff {a : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} :
    𝔸.mkVertex v₀ a p = 𝔸.mkVertex v₀ a q ↔
      ∃ g : 𝔸.vertexGroup a, p.Homotopic (q.comp (Path.ofVertex g)) :=
  ⟨fun h => Quotient.exact (eq_of_heq (Sigma.mk.inj h).2),
    fun h => congrArg (Sigma.mk a) (Quotient.sound h)⟩

/-- Two `𝔸`-paths to `Γ.src e` represent the same dart over `e` in `X(𝔸, v₀)` exactly when they
differ on the right by an element of `α_e(A_e)` up to homotopy. -/
theorem mkDart_same_eq_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    𝔸.mkDart v₀ e p = 𝔸.mkDart v₀ e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.comp (Path.ofVertex (𝔸.α e c))) :=
  ⟨fun h => Quotient.exact (eq_of_heq (Sigma.mk.inj h).2),
    fun h => congrArg (Sigma.mk e) (Quotient.sound h)⟩

@[simp] theorem mkVertex_cons_vertex (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (g : 𝔸.vertexGroup a) :
    𝔸.mkVertex v₀ a (p.cons (Letter.vertex g)) = 𝔸.mkVertex v₀ a p :=
  (𝔸.mkVertex_same_eq_iff v₀).mpr ⟨g, by rw [Path.comp_ofVertex]; exact .refl _⟩

theorem mkVertex_comp_ofVertex (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (g : 𝔸.vertexGroup a) :
    𝔸.mkVertex v₀ a (p.comp (Path.ofVertex g)) = 𝔸.mkVertex v₀ a p := by
  rw [Path.comp_ofVertex, mkVertex_cons_vertex]

@[simp] theorem mkVertex_ofVertex (g : 𝔸.vertexGroup v₀) :
    𝔸.mkVertex v₀ v₀ (Path.ofVertex g) = 𝔸.baseVertex v₀ := by
  rw [Path.ofVertex_eq_nil_cons, mkVertex_cons_vertex]
  rfl

@[simp] theorem mkDart_cons_vertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.mkDart v₀ e (p.cons (Letter.vertex (𝔸.α e c))) = 𝔸.mkDart v₀ e p :=
  (𝔸.mkDart_same_eq_iff v₀).mpr ⟨c, by rw [Path.comp_ofVertex]; exact .refl _⟩

theorem mkDart_comp_ofVertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.mkDart v₀ e (p.comp (Path.ofVertex (𝔸.α e c))) = 𝔸.mkDart v₀ e p := by
  rw [Path.comp_ofVertex, mkDart_cons_vertex_α]

@[simp] theorem src_mkDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).src (𝔸.mkDart v₀ e p) = 𝔸.mkVertex v₀ (Γ.src e) p :=
  (rfl)

@[simp] theorem rev_mkDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).rev (𝔸.mkDart v₀ e p) =
      𝔸.mkDart v₀ (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem tgt_mkDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).tgt (𝔸.mkDart v₀ e p) =
      𝔸.mkVertex v₀ (Γ.tgt e) (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem mk_smul_mkVertex (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (a : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    π₁.mk γ • 𝔸.mkVertex v₀ a p = 𝔸.mkVertex v₀ a (γ.comp p) := by
  rw [GTree.smul_vertex_def, Aut.smul_vertex_def]
  exact smulVertex_mk 𝔸 v₀ γ (𝔸.mkVertex v₀ a p)

@[simp] theorem mk_smul_mkDart (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk γ • 𝔸.mkDart v₀ e p = 𝔸.mkDart v₀ e (γ.comp p) := by
  rw [GTree.smul_dart_def, Aut.smul_dart_def]
  exact smulDart_mk 𝔸 v₀ γ (𝔸.mkDart v₀ e p)

@[simp] theorem vertexBase_smul (x : π₁ 𝔸 v₀) (u : (𝔸.bassSerreTree v₀).V) :
    𝔸.vertexBase v₀ (x • u) = 𝔸.vertexBase v₀ u := by
  obtain ⟨a, p, rfl⟩ := 𝔸.exists_mkVertex v₀ u
  exact π₁.induction_on x fun γ => by
    rw [mk_smul_mkVertex, vertexBase_mkVertex, vertexBase_mkVertex]

@[simp] theorem dartBase_smul (x : π₁ 𝔸 v₀) (d : (𝔸.bassSerreTree v₀).E) :
    𝔸.dartBase v₀ (x • d) = 𝔸.dartBase v₀ d := by
  obtain ⟨e, p, rfl⟩ := 𝔸.exists_mkDart v₀ d
  exact π₁.induction_on x fun γ => by rw [mk_smul_mkDart, dartBase_mkDart, dartBase_mkDart]

/-! ### Vertex and dart stabilizers -/

/-- The stabilizer in `π₁(𝔸, v₀)` of the vertex coset `p A_a` is `p A_a p⁻¹`, the image of
`π₁.vertexHom p`. -/
theorem stabilizer_vertex {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.mkVertex v₀ a p) = (π₁.vertexHom p).range := by
  ext x
  refine π₁.induction_on x fun γ => ?_
  rw [mem_stabilizer_iff, mk_smul_mkVertex, mkVertex_same_eq_iff, MonoidHom.mem_range]
  refine exists_congr fun g => ?_
  rw [π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
  refine ⟨fun h => (h.comp_right p.reverse).symm.trans (Path.Homotopic.comp_comp_reverse γ p),
    fun h => (h.symm.comp_right p).trans ?_⟩
  simpa only [Quiver.Path.comp_assoc, Quiver.Path.comp_nil] using
    (Path.Homotopic.reverse_comp p).comp_left (p.comp (Path.ofVertex g))

@[simp] theorem stabilizer_baseVertex :
    stabilizer (π₁ 𝔸 v₀) (𝔸.baseVertex v₀) =
      (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range :=
  𝔸.stabilizer_vertex v₀ .nil

/-- The vertex group `A_a` is isomorphic to the stabilizer of `p A_a` in `π₁(𝔸, v₀)` via
`g ↦ p g p⁻¹`. -/
noncomputable def stabilizerVertexEquiv {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    𝔸.vertexGroup a ≃* stabilizer (π₁ 𝔸 v₀) (𝔸.mkVertex v₀ a p) :=
  (MonoidHom.ofInjective (π₁.vertexHom_injective p)).trans
    (MulEquiv.subgroupCongr (𝔸.stabilizer_vertex v₀ p).symm)

@[simp] theorem stabilizerVertexEquiv_coe_apply {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (g : 𝔸.vertexGroup a) :
    ((𝔸.stabilizerVertexEquiv v₀ p g : stabilizer (π₁ 𝔸 v₀) (𝔸.mkVertex v₀ a p)) : π₁ 𝔸 v₀) =
      π₁.vertexHom p g := by
  rw [stabilizerVertexEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

/-- The stabilizer in `π₁(𝔸, v₀)` of the dart coset `p α_e(A_e)` is `p α_e(A_e) p⁻¹`. -/
theorem stabilizer_edge (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.mkDart v₀ e p) = ((π₁.vertexHom p).comp (𝔸.α e)).range := by
  ext x
  refine π₁.induction_on x fun γ => ?_
  rw [mem_stabilizer_iff, mk_smul_mkDart, mkDart_same_eq_iff, MonoidHom.mem_range]
  refine exists_congr fun c => ?_
  rw [MonoidHom.comp_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
  refine ⟨fun h => (h.comp_right p.reverse).symm.trans (Path.Homotopic.comp_comp_reverse γ p),
    fun h => (h.symm.comp_right p).trans ?_⟩
  simpa only [Quiver.Path.comp_assoc, Quiver.Path.comp_nil] using
    (Path.Homotopic.reverse_comp p).comp_left (p.comp (Path.ofVertex (𝔸.α e c)))

/-- The stabilizer of the dart `(p g) α_e(A_e)` joining `p A_{src e}` to `(p g e) A_{tgt e}` is
`p g α_e(A_e) g⁻¹ p⁻¹`. -/
theorem stabilizer_edge_comp_ofVertex (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.mkDart v₀ e (p.comp (Path.ofVertex g))) =
      (((π₁.vertexHom p).comp
        (MulAut.conj g : 𝔸.vertexGroup (Γ.src e) →* 𝔸.vertexGroup (Γ.src e))).comp
        (𝔸.α e)).range := by
  rw [𝔸.stabilizer_edge v₀ e (p.comp (Path.ofVertex g)), π₁.vertexHom_comp_ofVertex]

/-- The edge group `A_e` is isomorphic to the stabilizer of `p α_e(A_e)` in `π₁(𝔸, v₀)` via
`c ↦ p α_e(c) p⁻¹`. -/
noncomputable def stabilizerEdgeEquiv (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.edgeGroup (Γ.toGeomEdge e) ≃* stabilizer (π₁ 𝔸 v₀) (𝔸.mkDart v₀ e p) :=
  (MonoidHom.ofInjective (f := (π₁.vertexHom p).comp (𝔸.α e))
    ((π₁.vertexHom_injective p).comp (𝔸.α_injective e))).trans
    (MulEquiv.subgroupCongr (𝔸.stabilizer_edge v₀ e p).symm)

@[simp] theorem stabilizerEdgeEquiv_coe_apply (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    ((𝔸.stabilizerEdgeEquiv v₀ e p c : stabilizer (π₁ 𝔸 v₀) (𝔸.mkDart v₀ e p)) : π₁ 𝔸 v₀) =
      π₁.vertexHom p (𝔸.α e c) := by
  rw [stabilizerEdgeEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply, MonoidHom.comp_apply]

/-- Every vertex-group image `p A_a p⁻¹` is an elliptic subgroup of `π₁(𝔸, v₀)` in `X(𝔸, v₀)`. -/
theorem isEllipticSubgroup_range_vertexHom {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreTree v₀).IsEllipticSubgroup (π₁.vertexHom p).range :=
  𝔸.stabilizer_vertex v₀ p ▸ (𝔸.bassSerreTree v₀).isEllipticSubgroup_stabilizer (𝔸.mkVertex v₀ a p)

/-- The stabilizer of `p A_a` in `π₁(𝔸, v₀)` is trivial if and only if `A_a` is trivial. -/
@[simp] theorem stabilizer_vertex_eq_bot_iff {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.mkVertex v₀ a p) = ⊥ ↔ Subsingleton (𝔸.vertexGroup a) := by
  rw [Subgroup.eq_bot_iff_forall]
  refine ⟨fun h => ⟨fun g₁ g₂ => ?_⟩, fun h x hx => ?_⟩
  · refine (π₁.vertexHom_injective p) ?_
    have h₁ := h (π₁.vertexHom p g₁) (by rw [stabilizer_vertex]; exact ⟨g₁, rfl⟩)
    have h₂ := h (π₁.vertexHom p g₂) (by rw [stabilizer_vertex]; exact ⟨g₂, rfl⟩)
    exact h₁.trans h₂.symm
  · rw [stabilizer_vertex] at hx
    obtain ⟨g, rfl⟩ := hx
    rw [h.elim g 1, map_one]

/-- When `A_a` is nontrivial, the stabilizer of `p A_a` in `π₁(𝔸, v₀)` is nontrivial. -/
theorem stabilizer_vertex_ne_bot {a : Γ.V} [Nontrivial (𝔸.vertexGroup a)]
    (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    stabilizer (π₁ 𝔸 v₀) (𝔸.mkVertex v₀ a p) ≠ ⊥ :=
  mt (𝔸.stabilizer_vertex_eq_bot_iff v₀ p).mp (not_subsingleton (𝔸.vertexGroup a))

/-- When all vertex groups are trivial, `π₁(𝔸, v₀)` acts freely on the vertices of `X(𝔸, v₀)`. -/
theorem stabilizer_vertex_eq_bot_of_subsingleton [∀ a, Subsingleton (𝔸.vertexGroup a)]
    (u : (𝔸.bassSerreTree v₀).V) :
    stabilizer (π₁ 𝔸 v₀) u = ⊥ := by
  obtain ⟨a, p, rfl⟩ := 𝔸.exists_mkVertex v₀ u
  exact (𝔸.stabilizer_vertex_eq_bot_iff v₀ p).mpr inferInstance

/-- When all vertex groups are trivial, `π₁(𝔸, v₀)` acts freely on the darts of `X(𝔸, v₀)`. -/
theorem stabilizer_edge_eq_bot_of_subsingleton [∀ a, Subsingleton (𝔸.vertexGroup a)]
    (d : (𝔸.bassSerreTree v₀).E) :
    stabilizer (π₁ 𝔸 v₀) d = ⊥ :=
  eq_bot_iff.mpr <| ((𝔸.bassSerreTree v₀).stabilizer_dart_le_stabilizer_src d).trans_eq
    (𝔸.stabilizer_vertex_eq_bot_of_subsingleton v₀ _)

/-! ### The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` -/

/-- Forgetting the path coset projects `X(𝔸, v₀)` onto the connected component `Γ.component v₀`
of `v₀` in `Γ`. -/
def bassSerreProj : (𝔸.bassSerreTree v₀).Hom (Γ.component v₀) where
  mapV u := ⟨u.1, by
    obtain ⟨p, _⟩ := Quotient.exists_rep u.2
    exact (Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩⟩
  mapE d := ⟨d.1, by
    obtain ⟨p, _⟩ := Quotient.exists_rep d.2
    exact (Γ.mem_componentDarts_iff v₀).mpr ⟨p.edgePath⟩⟩
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem bassSerreProj_mapV_val (u : (𝔸.bassSerreTree v₀).V) :
    ((𝔸.bassSerreProj v₀).mapV u).1 = 𝔸.vertexBase v₀ u :=
  (rfl)

@[simp] theorem bassSerreProj_mapE_val (d : (𝔸.bassSerreTree v₀).E) :
    ((𝔸.bassSerreProj v₀).mapE d).1 = 𝔸.dartBase v₀ d :=
  (rfl)

@[simp] theorem bassSerreProj_comp_action (x : π₁ 𝔸 v₀) :
    Hom.comp (𝔸.bassSerreProj v₀) ((𝔸.bassSerreTree v₀).action x).toHom = 𝔸.bassSerreProj v₀ := by
  ext u : 2
  · have h₁ :
        (Hom.comp (𝔸.bassSerreProj v₀) ((𝔸.bassSerreTree v₀).action x).toHom).mapV u =
          (𝔸.bassSerreProj v₀).mapV (x • u) := by
      rw [Hom.comp_mapV, Function.comp_apply, Iso.toHom_mapV,
        ← Aut.smul_vertex_def, ← GTree.smul_vertex_def]
    exact Subtype.ext <| (congrArg Subtype.val h₁).trans <|
      (𝔸.bassSerreProj_mapV_val v₀ (x • u)).trans
        ((𝔸.vertexBase_smul v₀ x u).trans (𝔸.bassSerreProj_mapV_val v₀ u).symm)
  · have h₁ :
        (Hom.comp (𝔸.bassSerreProj v₀) ((𝔸.bassSerreTree v₀).action x).toHom).mapE u =
          (𝔸.bassSerreProj v₀).mapE (x • u) := by
      rw [Hom.comp_mapE, Function.comp_apply, Iso.toHom_mapE,
        ← Aut.smul_dart_def, ← GTree.smul_dart_def]
    exact Subtype.ext <| (congrArg Subtype.val h₁).trans <|
      (𝔸.bassSerreProj_mapE_val v₀ (x • u)).trans
        ((𝔸.dartBase_smul v₀ x u).trans (𝔸.bassSerreProj_mapE_val v₀ u).symm)

/-- The morphism from `X(𝔸, v₀) / π₁(𝔸, v₀)` to `Γ.component v₀` induced by `bassSerreProj`. -/
def bassSerreQuotientHom :
    ((𝔸.bassSerreTree v₀).toSerreGraph.quotient (𝔸.bassSerreTree v₀).action
      (𝔸.bassSerreTree v₀).action_smul_ne_rev).Hom (Γ.component v₀) :=
  SerreGraph.quotientLift (𝔸.bassSerreTree v₀).action_smul_ne_rev (𝔸.bassSerreProj v₀)
    (𝔸.bassSerreProj_comp_action v₀)

private theorem bassSerreQuotientHom_mapV_bijective :
    Function.Bijective (𝔸.bassSerreQuotientHom v₀).mapV := by
  refine ⟨fun q₁ q₂ h => ?_, fun a => ?_⟩
  · obtain ⟨u₁, rfl⟩ := quotientMap_mapV_surjective _ _ _ q₁
    obtain ⟨u₂, rfl⟩ := quotientMap_mapV_surjective _ _ _ q₂
    obtain ⟨a₁, p₁, rfl⟩ := 𝔸.exists_mkVertex v₀ u₁
    obtain ⟨a₂, p₂, rfl⟩ := 𝔸.exists_mkVertex v₀ u₂
    have ha : a₁ = a₂ := by
      simpa [bassSerreQuotientHom] using congrArg Subtype.val h
    subst ha
    refine quotientMap_mapV_eq_iff.mpr ⟨π₁.mk (p₂.comp p₁.reverse), ?_⟩
    rw [← GTree.smul_vertex_def, mk_smul_mkVertex]
    exact 𝔸.mkVertex_congr v₀ (by
      simpa only [Quiver.Path.comp_nil] using Path.Homotopic.comp_reverse_comp_comp p₂ p₁ .nil)
  · obtain ⟨a, ha⟩ := a
    obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v₀).mp ha
    exact ⟨(quotientMap _ _ _).mapV (𝔸.mkVertex v₀ a ((dartPrefunctor 𝔸).mapPath p)),
      Subtype.ext (by simp [bassSerreQuotientHom])⟩

private theorem bassSerreQuotientHom_mapE_bijective :
    Function.Bijective (𝔸.bassSerreQuotientHom v₀).mapE := by
  refine ⟨fun q₁ q₂ h => ?_, fun e => ?_⟩
  · obtain ⟨d₁, rfl⟩ := quotientMap_mapE_surjective _ _ _ q₁
    obtain ⟨d₂, rfl⟩ := quotientMap_mapE_surjective _ _ _ q₂
    obtain ⟨e₁, p₁, rfl⟩ := 𝔸.exists_mkDart v₀ d₂
    obtain ⟨e₀, p₀, rfl⟩ := 𝔸.exists_mkDart v₀ d₁
    have he : e₀ = e₁ := by
      simpa [bassSerreQuotientHom] using congrArg Subtype.val h
    subst he
    refine quotientMap_mapE_eq_iff.mpr ⟨π₁.mk (p₁.comp p₀.reverse), ?_⟩
    rw [← GTree.smul_dart_def, mk_smul_mkDart]
    exact 𝔸.mkDart_congr v₀ (by
      simpa only [Quiver.Path.comp_nil] using Path.Homotopic.comp_reverse_comp_comp p₁ p₀ .nil)
  · obtain ⟨e, he⟩ := e
    obtain ⟨p⟩ := (Γ.mem_componentDarts_iff v₀).mp he
    exact ⟨(quotientMap _ _ _).mapE (𝔸.mkDart v₀ e ((dartPrefunctor 𝔸).mapPath p)),
      Subtype.ext (by simp [bassSerreQuotientHom])⟩

/-- The quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is isomorphic to the connected component
`Γ.component v₀` of `v₀` in `Γ`. -/
noncomputable def quotientBassSerreTreeIso :
    ((𝔸.bassSerreTree v₀).toSerreGraph.quotient (𝔸.bassSerreTree v₀).action
      (𝔸.bassSerreTree v₀).action_smul_ne_rev).Iso (Γ.component v₀) :=
  (𝔸.bassSerreQuotientHom v₀).toIso
    (bassSerreQuotientHom_mapV_bijective 𝔸 v₀)
    (bassSerreQuotientHom_mapE_bijective 𝔸 v₀)

@[simp] theorem quotientBassSerreTreeIso_toHom :
    (𝔸.quotientBassSerreTreeIso v₀).toHom = 𝔸.bassSerreQuotientHom v₀ :=
  Hom.toIso_toHom ..

/-- Over a preconnected graph `Γ`, the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀)` is isomorphic to `Γ`
itself. -/
noncomputable def quotientBassSerreTreeIsoOfPreconnected (hΓ : Γ.Preconnected) :
    ((𝔸.bassSerreTree v₀).toSerreGraph.quotient (𝔸.bassSerreTree v₀).action
      (𝔸.bassSerreTree v₀).action_smul_ne_rev).Iso Γ :=
  (𝔸.quotientBassSerreTreeIso v₀).trans (Γ.componentIsoOfPreconnected v₀ hΓ)

/-- No `𝔸`-path from `v₀` can reach a vertex outside the connected component of `v₀` in `Γ`. -/
theorem isEmpty_path_of_not_mem_componentVertices {a : Γ.V} (ha : a ∉ Γ.componentVertices v₀) :
    IsEmpty (𝔸.Path ⟨v₀⟩ ⟨a⟩) :=
  ⟨fun p => ha ((Γ.mem_componentVertices_iff v₀).mpr ⟨p.edgePath⟩)⟩

/-- Over a disconnected graph `Γ` (`¬ Γ.Preconnected`), the quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` is
isomorphic to `Γ.component v₀` rather than `Γ`: no graph isomorphism to `Γ` exists, since
`Γ.component v₀` is preconnected. -/
theorem isEmpty_quotientBassSerreTree_iso_of_not_preconnected (hΓ : ¬ Γ.Preconnected) :
    IsEmpty (((𝔸.bassSerreTree v₀).toSerreGraph.quotient (𝔸.bassSerreTree v₀).action
      (𝔸.bassSerreTree v₀).action_smul_ne_rev).Iso Γ) :=
  ⟨fun φ =>
    hΓ (((𝔸.quotientBassSerreTreeIso v₀).symm.trans φ).preconnected_iff.mpr
      (Γ.component_preconnected v₀))⟩

/-! ### Local structure: outgoing darts and vertex degrees -/

private def outDartFiberMap (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range →
      {qbar : Quotient (𝔸.dartSetoid v₀ e) //
        (𝔸.bassSerreTree v₀).src ⟨e, qbar⟩ = 𝔸.mkVertex v₀ (Γ.src e) p} :=
  Quotient.lift
    (fun g => ⟨Quotient.mk (𝔸.dartSetoid v₀ e) (p.comp (Path.ofVertex g)),
      𝔸.mkVertex_comp_ofVertex v₀ (Γ.src e) p g⟩)
    fun g₁ g₂ h => Subtype.ext <| by
      obtain ⟨c, hc⟩ := QuotientGroup.leftRel_apply.mp h
      have hg : g₁ = g₂ * 𝔸.α e c⁻¹ := by
        rw [map_inv, hc, mul_inv_rev, inv_inv, mul_inv_cancel_left]
      exact Quotient.sound ⟨c⁻¹, by
        rw [hg, Path.comp_ofVertex, Path.comp_ofVertex, Path.comp_ofVertex]
        exact (Path.Homotopic.mul p g₂ (𝔸.α e c⁻¹)).symm⟩

private theorem outDartFiberMap_bijective (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    Function.Bijective (outDartFiberMap 𝔸 v₀ e p) := by
  refine ⟨fun x₁ x₂ h => ?_, fun ⟨qbar, hsrc⟩ => ?_⟩
  · refine Quotient.inductionOn₂ x₁ x₂ (fun g₁ g₂ h => ?_) h
    have hd : 𝔸.mkDart v₀ e (p.comp (Path.ofVertex g₁)) =
        𝔸.mkDart v₀ e (p.comp (Path.ofVertex g₂)) :=
      congrArg (Sigma.mk e) (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := (𝔸.mkDart_same_eq_iff v₀).mp hd
    have hmul : Path.Homotopic (p.comp (Path.ofVertex g₁))
        (p.comp (Path.ofVertex (g₂ * 𝔸.α e c))) := by
      refine hc.trans ?_
      rw [Path.comp_ofVertex, Path.comp_ofVertex, Path.comp_ofVertex]
      exact Path.Homotopic.mul p g₂ (𝔸.α e c)
    have hg : g₁ = g₂ * 𝔸.α e c := Path.ofVertex_homotopic_ofVertex_iff.mp hmul.of_comp_left
    exact Quotient.sound <| QuotientGroup.leftRel_apply.mpr ⟨c⁻¹, by
      rw [map_inv, hg, mul_inv_rev, inv_mul_cancel_right]⟩
  · obtain ⟨q, rfl⟩ := Quotient.exists_rep qbar
    obtain ⟨g, hq⟩ := (𝔸.mkVertex_same_eq_iff v₀).mp hsrc
    exact ⟨QuotientGroup.mk g, Subtype.ext (Quotient.sound (𝔸.dartRel_of_homotopic v₀ hq.symm))⟩

private noncomputable def outDartFiberEquiv :
    ∀ {a : Γ.V} (e : Γ.E), Γ.src e = a → (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) →
      {qbar : Quotient (𝔸.dartSetoid v₀ e) //
        (𝔸.bassSerreTree v₀).src ⟨e, qbar⟩ = 𝔸.mkVertex v₀ a p} ≃
        𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range
  | _, e, rfl, p =>
    (Equiv.ofBijective (outDartFiberMap 𝔸 v₀ e p) (outDartFiberMap_bijective 𝔸 v₀ e p)).symm

private def outDartSigmaEquiv {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = 𝔸.mkVertex v₀ a p} ≃
      Σ e : {e : Γ.E // Γ.src e = a},
        {qbar : Quotient (𝔸.dartSetoid v₀ e.1) //
          (𝔸.bassSerreTree v₀).src ⟨e.1, qbar⟩ = 𝔸.mkVertex v₀ a p} where
  toFun := fun ⟨⟨e, qbar⟩, hd⟩ => ⟨⟨e, congrArg Sigma.fst hd⟩, ⟨qbar, hd⟩⟩
  invFun := fun ⟨⟨e, _⟩, ⟨qbar, hd⟩⟩ => ⟨⟨e, qbar⟩, hd⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- The outgoing darts of `X(𝔸, v₀)` at a vertex `p A_a` correspond bijectively to pairs of an
outgoing dart `e` of `Γ` at `a` and a left coset in `A_{src e} ⧸ α_e(A_e)`: the pair
`(e, g α_e(A_e))` corresponds to the dart `(p g) α_e(A_e)`. -/
noncomputable def outDartEquiv {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = 𝔸.mkVertex v₀ a p} ≃
      Σ e : {e : Γ.E // Γ.src e = a}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range :=
  (outDartSigmaEquiv 𝔸 v₀ p).trans
    (Equiv.sigmaCongrRight fun e => outDartFiberEquiv 𝔸 v₀ e.1 e.2 p)

@[simp] theorem outDartEquiv_symm_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    ((𝔸.outDartEquiv v₀ p).symm ⟨⟨e, rfl⟩, QuotientGroup.mk g⟩).1 =
      𝔸.mkDart v₀ e (p.comp (Path.ofVertex g)) :=
  (rfl)

/-- Cardinal degree formula: the cardinal of outgoing darts at `p A_a` in `X(𝔸, v₀)` is the
universe-lifted sum over outgoing darts `e` of `Γ` at `a` of `#(A_{src e} ⧸ α_e(A_e))`. -/
theorem mk_outDart_eq_sum {a : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    #{d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = 𝔸.mkVertex v₀ a p} =
      Cardinal.lift.{u} (Cardinal.sum fun e : {e : Γ.E // Γ.src e = a} =>
        #(𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range)) :=
  (Cardinal.mk_congr ((𝔸.outDartEquiv v₀ p).trans Equiv.ulift.symm)).trans
    ((Cardinal.mk_uLift _).trans (congrArg Cardinal.lift.{u} (Cardinal.mk_sigma _)))

/-- Finite degree formula: when `a` has finitely many outgoing darts in `Γ` and each `α_e(A_e)` has
finite index in `A_{src e}`, the vertex `p A_a` of `X(𝔸, v₀)` has degree
`∑ e, (𝔸.α e).range.index`. -/
theorem card_outDart_eq_sum_index {a : Γ.V} [Fintype {e : Γ.E // Γ.src e = a}]
    [∀ e : {e : Γ.E // Γ.src e = a}, (𝔸.α e.1).range.FiniteIndex] (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    Nat.card {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = 𝔸.mkVertex v₀ a p} =
      ∑ e : {e : Γ.E // Γ.src e = a}, (𝔸.α e.1).range.index := by
  rw [Nat.card_congr (𝔸.outDartEquiv v₀ p), Nat.card_sigma]
  exact Finset.sum_congr rfl fun e _ => (𝔸.α e.1).range.index_eq_card.symm

/-- When every boundary map `α_e` has trivial coset space (in particular when all vertex groups are
trivial), `bassSerreProj` restricts to a bijection on the outgoing star of every vertex:
`X(𝔸, v₀)` is a covering tree of `Γ.component v₀`. -/
theorem bassSerreProj_outDart_bijective
    [∀ e : Γ.E, Subsingleton (𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range)]
    (u : (𝔸.bassSerreTree v₀).V) :
    Function.Bijective
      (fun d : {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = u} =>
        (⟨(𝔸.bassSerreProj v₀).mapE d.1, by rw [Hom.map_src, d.2]⟩ :
          {e : (Γ.component v₀).E //
            (Γ.component v₀).src e = (𝔸.bassSerreProj v₀).mapV u})) := by
  obtain ⟨a, p, rfl⟩ := 𝔸.exists_mkVertex v₀ u
  refine ⟨fun d₁ d₂ h => ?_, fun ⟨⟨e, he⟩, hs⟩ => ?_⟩
  · have hd : ((𝔸.bassSerreProj v₀).mapE d₁.1).1 = ((𝔸.bassSerreProj v₀).mapE d₂.1).1 :=
      congrArg (fun x => x.1.1) h
    rw [bassSerreProj_mapE_val, bassSerreProj_mapE_val] at hd
    have hfst : ((𝔸.outDartEquiv v₀ p) d₁).1 = ((𝔸.outDartEquiv v₀ p) d₂).1 := by
      obtain ⟨⟨e₁, _⟩, _⟩ := d₁
      obtain ⟨⟨e₂, _⟩, _⟩ := d₂
      exact Subtype.ext hd
    refine (𝔸.outDartEquiv v₀ p).injective ?_
    rcases h₁ : (𝔸.outDartEquiv v₀ p) d₁ with ⟨e₁, c₁⟩
    rcases h₂ : (𝔸.outDartEquiv v₀ p) d₂ with ⟨e₂, c₂⟩
    rw [h₁, h₂] at hfst
    subst hfst
    exact congrArg (Sigma.mk e₁) (Subsingleton.elim c₁ c₂)
  · have hsa : Γ.src e = a :=
      (congrArg Subtype.val hs).trans (𝔸.bassSerreProj_mapV_val v₀ (𝔸.mkVertex v₀ a p))
    cases hsa
    refine ⟨(𝔸.outDartEquiv v₀ p).symm ⟨⟨e, rfl⟩, QuotientGroup.mk 1⟩, ?_⟩
    exact Subtype.ext (Subtype.ext
      ((𝔸.bassSerreProj_mapE_val v₀ _).trans (by rw [outDartEquiv_symm_mk, dartBase_mkDart])))

/-! ### Special cases and examples -/

section IsEmpty

variable [IsEmpty Γ.E]

instance : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun d => isEmptyElim (𝔸.dartBase v₀ d)⟩

instance : Unique (𝔸.bassSerreTree v₀).V where
  default := 𝔸.baseVertex v₀
  uniq u := by
    obtain ⟨a, p, rfl⟩ := 𝔸.exists_mkVertex v₀ u
    have ha : v₀ = a := Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim p.edgePath
    cases ha
    have hp := (toPath_normalForm_homotopic default p).symm
    rw [NormalWord.toPath_def] at hp
    cases h : (normalForm default p).toAlternatingPath with
    | single g =>
      rw [h, AlternatingPath.toPath_single] at hp
      exact (𝔸.mkVertex_congr v₀ hp).trans (𝔸.mkVertex_ofVertex v₀ g)
    | cons _ e _ => exact isEmptyElim e.1

/-- Over an edgeless graph (in particular `SerreGraph.point`), the Bass–Serre tree has one vertex
and no darts, so its underlying graph is isomorphic to `SerreGraph.point`. -/
noncomputable def bassSerreTreePointIso :
    (𝔸.bassSerreTree v₀).toSerreGraph.Iso SerreGraph.point where
  equivV := Equiv.ofUnique _ _
  equivE := Equiv.equivOfIsEmpty _ _
  map_src d := isEmptyElim d
  map_rev d := isEmptyElim d

end IsEmpty

section BaumslagSolitar

open Multiplicative

/-- Every vertex of the Bass–Serre tree of the Baumslag–Solitar group `BS(m, n)` has degree
`|m| + |n|`: the outgoing dart `((), true)` contributes index `|m|` and `((), false)` contributes
index `|n|`. -/
theorem card_outDart_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (u : ((baumslagSolitar m n hm hn).bassSerreTree ()).V) :
    Nat.card {d : ((baumslagSolitar m n hm hn).bassSerreTree ()).E //
      ((baumslagSolitar m n hm hn).bassSerreTree ()).src d = u} =
      m.natAbs + n.natAbs := by
  let 𝔸₀ := baumslagSolitar m n hm hn
  let v₀ : (SerreGraph.rose Unit).V := ()
  have hindex (k : ℤ) : (zpowGroupHom (α := Multiplicative ℤ) k).range.index = k.natAbs := by
    have hrange : (zpowGroupHom (α := Multiplicative ℤ) k).range =
        AddSubgroup.toSubgroup (AddSubgroup.zmultiples k) := by
      ext x
      rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
      refine ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, ?_⟩, fun ⟨q, hq⟩ => ⟨ofAdd q, ?_⟩⟩
      · simpa [zpowGroupHom_apply, mul_comm] using congrArg toAdd hc
      · apply toAdd.injective
        simpa [zpowGroupHom_apply, mul_comm] using hq
    rw [hrange, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  obtain ⟨⟨⟩, p, rfl⟩ := 𝔸₀.exists_mkVertex v₀ u
  let eEquiv : Bool ≃ {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀} :=
    { toFun := fun b => ⟨((), b), rfl⟩
      invFun := fun e => e.1.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl }
  let _ : Fintype {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀} :=
    Fintype.ofEquiv Bool eEquiv
  have : ∀ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀},
      (𝔸₀.α e.1).range.FiniteIndex := by
    intro ⟨e, _⟩
    obtain ⟨⟨⟩, _ | _⟩ := e
    · exact ⟨(congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
        (baumslagSolitar_α_false m n hm hn)).trans (hindex n) ▸ Int.natAbs_ne_zero.mpr hn⟩
    · exact ⟨(congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
        (baumslagSolitar_α_true m n hm hn)).trans (hindex m) ▸ Int.natAbs_ne_zero.mpr hm⟩
  rw [𝔸₀.card_outDart_eq_sum_index v₀ p, ← eEquiv.sum_comp, Fintype.sum_bool]
  exact congrArg₂ (· + ·)
    ((congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (baumslagSolitar_α_true m n hm hn)).trans (hindex m))
    ((congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (baumslagSolitar_α_false m n hm hn)).trans (hindex n))

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has degree `1 + 2 = 3`. -/
theorem card_outDart_baumslagSolitar_one_two
    (u : ((baumslagSolitar 1 2 one_ne_zero (by decide)).bassSerreTree ()).V) :
    Nat.card {d : ((baumslagSolitar 1 2 one_ne_zero (by decide)).bassSerreTree ()).E //
      ((baumslagSolitar 1 2 one_ne_zero (by decide)).bassSerreTree ()).src d = u} = 3 :=
  card_outDart_baumslagSolitar 1 2 one_ne_zero (by decide) u

end BaumslagSolitar

section FreeProduct

/-- The segment graph of groups of a free product `A ∗ B`: vertex groups `A` at `false` and `B`
at `true`, with trivial amalgamated edge group `PUnit`. -/
abbrev freeProduct (A B : Type w) [Group A] [Group B] :
    GraphOfGroups.{0, 0, w, 0} SerreGraph.segment :=
  segment (1 : PUnit →* A) (1 : PUnit →* B)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

instance {A B : Type w} [Group A] [Group B] (e : SerreGraph.segment.GeomEdge) :
    Unique ((freeProduct A B).edgeGroup e) :=
  inferInstanceAs (Unique PUnit)

/-- Outgoing darts at a vertex `p A` over `false` in the Bass–Serre tree of `A ∗ B` correspond
bijectively to `A`. -/
noncomputable def outDartFreeProductFalseEquiv {A B : Type w} [Group A] [Group B]
    (p : (freeProduct A B).Path ⟨false⟩ ⟨false⟩) :
    {d : ((freeProduct A B).bassSerreTree false).E //
      ((freeProduct A B).bassSerreTree false).src d =
        (freeProduct A B).mkVertex false false p} ≃ A := by
  let uniqueFalse : Unique {e : SerreGraph.segment.E // SerreGraph.segment.src e = false} :=
    { default := ⟨false, rfl⟩
      uniq := fun ⟨b, h⟩ => by
        cases b
        · exact Subtype.ext rfl
        · exact Bool.noConfusion h }
  refine ((freeProduct A B).outDartEquiv false p).trans ?_
  refine (Equiv.uniqueSigma _).trans ?_
  refine (Subgroup.quotientEquivOfEq ?_).trans QuotientGroup.quotientBot.toEquiv
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x 1, map_one]
  exact Subgroup.one_mem ⊥

/-- Outgoing darts at a vertex `p B` over `true` in the Bass–Serre tree of `A ∗ B` correspond
bijectively to `B`. -/
noncomputable def outDartFreeProductTrueEquiv {A B : Type w} [Group A] [Group B]
    (p : (freeProduct A B).Path ⟨false⟩ ⟨true⟩) :
    {d : ((freeProduct A B).bassSerreTree false).E //
      ((freeProduct A B).bassSerreTree false).src d =
        (freeProduct A B).mkVertex false true p} ≃ B := by
  let uniqueTrue : Unique {e : SerreGraph.segment.E // SerreGraph.segment.src e = true} :=
    { default := ⟨true, rfl⟩
      uniq := fun ⟨b, h⟩ => by
        cases b
        · exact Bool.noConfusion h
        · exact Subtype.ext rfl }
  refine ((freeProduct A B).outDartEquiv false p).trans ?_
  refine (Equiv.uniqueSigma _).trans ?_
  refine (Subgroup.quotientEquivOfEq ?_).trans QuotientGroup.quotientBot.toEquiv
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim x 1, map_one]
  exact Subgroup.one_mem ⊥

/-- At the base vertex `⟨A⟩` of the Bass–Serre tree of `A ∗ B`, the dart `(ofVertex a) {1}` ends at
the translate `a • ⟨B⟩`. -/
theorem tgt_mkDart_freeProduct_false_ofVertex {A B : Type w} [Group A] [Group B] (a : A) :
    ((freeProduct A B).bassSerreTree false).tgt
      ((freeProduct A B).mkDart false false (Path.ofVertex a)) =
      π₁.vertexHom (.nil : (freeProduct A B).Path ⟨false⟩ ⟨false⟩) a •
        (freeProduct A B).mkVertex false true (Path.ofDart (SerreGraph.segment.dart false)) := by
  let v₀ : SerreGraph.segment.V := false
  let v₁ : SerreGraph.segment.V := true
  let e₀ : SerreGraph.segment.E := false
  have h₁ := (freeProduct A B).tgt_mkDart v₀ e₀ (Path.ofVertex a)
  have h₂ := congrArg (fun x : π₁ (freeProduct A B) v₀ =>
      x • (freeProduct A B).mkVertex v₀ v₁ (Path.ofDart (SerreGraph.segment.dart e₀)))
    (π₁.vertexHom_nil_apply (𝔸 := freeProduct A B) (a := v₀) a)
  have h₃ := (freeProduct A B).mk_smul_mkVertex v₀ (Path.ofVertex a) v₁
    (Path.ofDart (SerreGraph.segment.dart e₀))
  have h₄ := Path.comp_ofDart
    (Path.ofVertex (𝔸 := freeProduct A B) (a := v₀) a) (SerreGraph.segment.dart e₀)
  exact h₁.trans ((h₂.trans (h₃.trans (congrArg _ h₄))).symm)

/-- In the Bass–Serre tree of `A ∗ B`, the translates `a • ⟨B⟩` for `a : A` are pairwise
distinct. -/
theorem freeProduct_vertexHom_smul_injective {A B : Type w} [Group A] [Group B] :
    Function.Injective (fun a : A =>
      π₁.vertexHom (.nil : (freeProduct A B).Path ⟨false⟩ ⟨false⟩) a •
        (freeProduct A B).mkVertex false true (Path.ofDart (SerreGraph.segment.dart false))) := by
  intro a₁ a₂ h
  let v₀ : SerreGraph.segment.V := false
  let e₀ : SerreGraph.segment.E := false
  let g₁ : (freeProduct A B).vertexGroup v₀ := a₁
  let g₂ : (freeProduct A B).vertexGroup v₀ := a₂
  let d₁ := (freeProduct A B).mkDart v₀ e₀ (Path.ofVertex g₁)
  let d₂ := (freeProduct A B).mkDart v₀ e₀ (Path.ofVertex g₂)
  have ht : ((freeProduct A B).bassSerreTree v₀).tgt d₁ =
      ((freeProduct A B).bassSerreTree v₀).tgt d₂ :=
    (tgt_mkDart_freeProduct_false_ofVertex a₁).trans
      (h.trans (tgt_mkDart_freeProduct_false_ofVertex a₂).symm)
  have hsrc₁ : ((freeProduct A B).bassSerreTree v₀).src d₁ = (freeProduct A B).baseVertex v₀ :=
    ((freeProduct A B).src_mkDart v₀ e₀ (Path.ofVertex g₁)).trans
      ((freeProduct A B).mkVertex_ofVertex v₀ g₁)
  have hsrc₂ : ((freeProduct A B).bassSerreTree v₀).src d₂ = (freeProduct A B).baseVertex v₀ :=
    ((freeProduct A B).src_mkDart v₀ e₀ (Path.ofVertex g₂)).trans
      ((freeProduct A B).mkVertex_ofVertex v₀ g₂)
  let f₁ : Quiver.Hom ((freeProduct A B).baseVertex v₀)
      (((freeProduct A B).bassSerreTree v₀).tgt d₁) := ⟨d₁, hsrc₁, rfl⟩
  let f₂ : Quiver.Hom ((freeProduct A B).baseVertex v₀)
      (((freeProduct A B).bassSerreTree v₀).tgt d₁) := ⟨d₂, hsrc₂, ht.symm⟩
  have heq := congrArg (SerreGraph.Path.darts ((freeProduct A B).bassSerreTree v₀).toSerreGraph)
    (((freeProduct A B).bassSerreTree v₀).isTree.isAcyclic.eq_of_isReduced
      (SerreGraph.Path.isReduced_toPath _ f₁) (SerreGraph.Path.isReduced_toPath _ f₂))
  simp only [SerreGraph.Path.darts_toPath, List.cons.injEq, and_true, f₁, f₂] at heq
  obtain ⟨c, hc⟩ := ((freeProduct A B).mkDart_same_eq_iff v₀).mp heq
  have hc₁ : (freeProduct A B).α e₀ c = 1 :=
    (Subsingleton.elim c 1).symm ▸ map_one ((freeProduct A B).α e₀)
  have hc' : (Path.ofVertex g₁).Homotopic ((Path.ofVertex g₂).comp (Path.ofVertex 1)) :=
    hc₁ ▸ hc
  have hmul : (Path.ofVertex g₁).Homotopic (Path.ofVertex (g₂ * 1)) := by
    refine hc'.trans ?_
    rw [Path.comp_ofVertex, Path.ofVertex_eq_nil_cons, Path.ofVertex_eq_nil_cons]
    exact Path.Homotopic.mul .nil g₂ 1
  exact (Path.ofVertex_homotopic_ofVertex_iff.mp hmul).trans (mul_one a₂)

/-- Every vertex of the Bass–Serre tree of `ℤ ∗ ℤ` has countably infinite degree `ℵ₀`. -/
theorem mk_outDart_freeProduct_int
    (u : ((freeProduct (Multiplicative ℤ) (Multiplicative ℤ)).bassSerreTree false).V) :
    #{d : ((freeProduct (Multiplicative ℤ) (Multiplicative ℤ)).bassSerreTree false).E //
      ((freeProduct (Multiplicative ℤ) (Multiplicative ℤ)).bassSerreTree false).src d = u} =
      ℵ₀ := by
  obtain ⟨b, p, rfl⟩ :=
    (freeProduct (Multiplicative ℤ) (Multiplicative ℤ)).exists_mkVertex false u
  cases b
  · exact (Cardinal.mk_congr (outDartFreeProductFalseEquiv p)).trans
      ((Cardinal.mk_congr Multiplicative.toAdd).trans Cardinal.mk_int)
  · exact (Cardinal.mk_congr (outDartFreeProductTrueEquiv p)).trans
      ((Cardinal.mk_congr Multiplicative.toAdd).trans Cardinal.mk_int)

end FreeProduct

end TauCeti.GraphOfGroups
