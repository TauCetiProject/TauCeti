/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.BaseVertex
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# The Bass–Serre tree of a graph of groups

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `v₀ : Γ.V`, the Bass–Serre
covering tree `X(𝔸, v₀)` is constructed from `𝔸`-paths starting at `v₀`:

* A vertex of `X(𝔸, v₀)` is an equivalence class `p A_v` of `𝔸`-paths `p` from `v₀` to a vertex
  `v : Γ.V`, where `p` and `p'` are equivalent when `p` is homotopic to `p'` followed by an
  element of `A_v`.
* A dart of `X(𝔸, v₀)` above `e : Γ.E` is an equivalence class `p α_e(A_e)` of `𝔸`-paths `p` from
  `v₀` to `Γ.src e`, where `p` and `p'` are equivalent when `p` is homotopic to `p'` followed by
  `α_e(c)` for some `c ∈ A_e`. Its source is `p A_{src e}`, its reverse is `(p · e) α_{rev e}(A_e)`
  above `Γ.rev e` (well-defined by `α_e(c) · e ∼ e · ω_e(c)`), and its target is
  `(p · e) A_{tgt e}`. Thus for `a ∈ A_v` and an edge `e` from `v` to `v'`, the dart
  `(p · a) α_e(A_e)` joins `p A_v` to `(p · a · e) A_{v'}`.

The fundamental group `π₁(𝔸, v₀)` acts on the left by path concatenation without inversions, turning
`X(𝔸, v₀)` into a `GTree (π₁ 𝔸 v₀)`. Left concatenation by an `𝔸`-path from `v₁` to `v₀` gives a
basepoint-change isomorphism `X(𝔸, v₀) ≅ X(𝔸, v₁)` semilinear with respect to `π₁.mulEquivOfPath`,
and forgetting vertex-group letters defines projections onto `Γ.component v₀` and `Γ`.

Vertex and dart stabilizers, coset parameterizations of outgoing darts, and the identification of
the quotient graph `π₁(𝔸, v₀) \ X(𝔸, v₀)` with `Γ.component v₀` are developed in
`TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Stabilizers`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreGraph`: the underlying `SerreGraph` of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTree`: `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.BassSerreTree.vertexMk`, `BassSerreTree.baseVertex`,
  `BassSerreTree.dartMk`, `BassSerreTree.arrowMk`: vertex and dart constructors.
* `TauCeti.GraphOfGroups.BassSerreTree.vertexLift`, `BassSerreTree.dartLift`: elimination maps out
  of the vertex and dart quotients.
* `TauCeti.GraphOfGroups.BassSerreTree.projHom`, `BassSerreTree.projComponentHom`: projections from
  `X(𝔸, v₀)` to `Γ` and `Γ.component v₀`.
* `TauCeti.GraphOfGroups.BassSerreTree.changeBaseIso`: isomorphism `X(𝔸, v₀) ≅ X(𝔸, v₁)` induced by
  left concatenation with an `𝔸`-path from `v₁` to `v₀`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `X(𝔸, v₀)` is a Serre tree.
* `TauCeti.GraphOfGroups.BassSerreTree.changeBaseIso_smul_vertex` and
  `BassSerreTree.changeBaseIso_smul_dart`: basepoint change is semilinear with respect to
  `π₁.mulEquivOfPath` on vertices and darts.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti
namespace GraphOfGroups

section PathHelpers

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ}

namespace Path

/-- Cancelling a common prefix `p` on the left of two homotopic `𝔸`-paths preserves homotopy. -/
theorem Homotopic.of_comp_left {a b c : 𝔸.LetterVertex} {p : 𝔸.Path a b} {q r : 𝔸.Path b c}
    (h : Homotopic (p.comp q) (p.comp r)) : Homotopic q r := by
  have key (s : 𝔸.Path b c) : Homotopic (p.reverse.comp (p.comp s)) s := by
    rw [← Quiver.Path.comp_assoc]
    simpa only [Quiver.Path.nil_comp] using (Homotopic.reverse_comp p).comp (.refl s)
  exact (key q).symm.trans ((h.comp_left p.reverse).trans (key r))

/-- Cancelling a common suffix `p` on the right of two homotopic `𝔸`-paths preserves homotopy. -/
theorem Homotopic.of_comp_right {a b c : 𝔸.LetterVertex} {q r : 𝔸.Path a b} {p : 𝔸.Path b c}
    (h : Homotopic (q.comp p) (r.comp p)) : Homotopic q r :=
  (Homotopic.comp_comp_reverse q p).symm.trans
    ((h.comp_right p.reverse).trans (Homotopic.comp_comp_reverse r p))

/-- Two right translates `p · g` and `p · h` of an `𝔸`-path by vertex group elements are homotopic
if and only if `g = h`. -/
@[simp] theorem cons_vertex_homotopic_cons_vertex_iff {a b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    {g h : 𝔸.vertexGroup b} :
    Homotopic (p.cons (Letter.vertex g)) (p.cons (Letter.vertex h)) ↔ g = h := by
  refine ⟨fun hgh => ?_, fun hgh => hgh ▸ .refl _⟩
  rw [← comp_ofVertex, ← comp_ofVertex] at hgh
  exact ofVertex_homotopic_ofVertex_iff.mp hgh.of_comp_left

end Path

end PathHelpers

/-! ### Construction of the Bass–Serre graph and tree -/

section Construction

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Raw representative of a vertex of `X(𝔸, v₀)`: a target vertex `v` and an `𝔸`-path from `v₀` to
`v`. -/
private structure RawVertex : Type (max u v w) where
  vertex : Γ.V
  path : 𝔸.Path ⟨v₀⟩ ⟨vertex⟩

/-- Equivalence of raw vertices: same endpoint `v` and `p ∼ p' · a` for some `a ∈ A_v`. -/
private def RawVertex.Rel : RawVertex 𝔸 v₀ → RawVertex 𝔸 v₀ → Prop
  | ⟨u, p⟩, ⟨v, q⟩ => ∃ h : u = v, ∃ a : 𝔸.vertexGroup v,
      Path.Homotopic (h ▸ p) (q.cons (Letter.vertex a))

private theorem RawVertex.rel_refl : ∀ x : RawVertex 𝔸 v₀, RawVertex.Rel 𝔸 v₀ x x
  | ⟨_, p⟩ => ⟨rfl, 1, (Path.Homotopic.one p).symm⟩

private theorem RawVertex.rel_symm :
    ∀ {x y : RawVertex 𝔸 v₀}, RawVertex.Rel 𝔸 v₀ x y → RawVertex.Rel 𝔸 v₀ y x
  | ⟨_, _⟩, ⟨_, q⟩, ⟨rfl, a, hpq⟩ =>
    ⟨rfl, a⁻¹, (((Path.Homotopic.one q).symm.trans
      (by simpa using (Path.Homotopic.mul q a a⁻¹).symm)).trans
        (hpq.cons (Letter.vertex a⁻¹)).symm)⟩

private theorem RawVertex.rel_trans :
    ∀ {x y z : RawVertex 𝔸 v₀},
      RawVertex.Rel 𝔸 v₀ x y → RawVertex.Rel 𝔸 v₀ y z → RawVertex.Rel 𝔸 v₀ x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, r⟩, ⟨rfl, a, hpq⟩, ⟨rfl, b, hqr⟩ =>
    ⟨rfl, b * a, (hpq.trans (hqr.cons (Letter.vertex a))).trans (Path.Homotopic.mul r b a)⟩

private def rawVertexSetoid : Setoid (RawVertex 𝔸 v₀) where
  r := RawVertex.Rel 𝔸 v₀
  iseqv := ⟨RawVertex.rel_refl 𝔸 v₀, RawVertex.rel_symm 𝔸 v₀, RawVertex.rel_trans 𝔸 v₀⟩

/-- Raw representative of a dart of `X(𝔸, v₀)`: a dart `e` of `Γ` and an `𝔸`-path from `v₀` to
`Γ.src e`. -/
private structure RawDart : Type (max u v w) where
  dart : Γ.E
  path : 𝔸.Path ⟨v₀⟩ ⟨Γ.src dart⟩

/-- Equivalence of raw darts: same underlying dart `e` and `p ∼ p' · α_e(c)` for some `c ∈ A_e`. -/
private def RawDart.Rel : RawDart 𝔸 v₀ → RawDart 𝔸 v₀ → Prop
  | ⟨e₁, p₁⟩, ⟨e₂, p₂⟩ => ∃ h : e₁ = e₂, ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e₂),
      Path.Homotopic (h ▸ p₁) (p₂.cons (Letter.vertex (𝔸.α e₂ c)))

private theorem RawDart.rel_refl : ∀ x : RawDart 𝔸 v₀, RawDart.Rel 𝔸 v₀ x x
  | ⟨_, p⟩ => ⟨rfl, 1, by simpa only [map_one] using (Path.Homotopic.one p).symm⟩

private theorem RawDart.rel_symm :
    ∀ {x y : RawDart 𝔸 v₀}, RawDart.Rel 𝔸 v₀ x y → RawDart.Rel 𝔸 v₀ y x
  | ⟨e, _⟩, ⟨_, q⟩, ⟨rfl, c, hpq⟩ => by
    have hmul :
        Path.Homotopic ((q.cons (Letter.vertex (𝔸.α e c))).cons (Letter.vertex (𝔸.α e c⁻¹))) q :=
      (Path.Homotopic.mul q _ _).trans (by simpa [← map_mul] using Path.Homotopic.one q)
    exact ⟨rfl, c⁻¹, hmul.symm.trans (hpq.cons (Letter.vertex (𝔸.α e c⁻¹))).symm⟩

private theorem RawDart.rel_trans :
    ∀ {x y z : RawDart 𝔸 v₀},
      RawDart.Rel 𝔸 v₀ x y → RawDart.Rel 𝔸 v₀ y z → RawDart.Rel 𝔸 v₀ x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨e, r⟩, ⟨rfl, c₁, hpq⟩, ⟨rfl, c₂, hqr⟩ => by
    have hmul : Path.Homotopic
        ((r.cons (Letter.vertex (𝔸.α e c₂))).cons (Letter.vertex (𝔸.α e c₁)))
        (r.cons (Letter.vertex (𝔸.α e (c₂ * c₁)))) := by
      rw [map_mul]
      exact Path.Homotopic.mul r (𝔸.α e c₂) (𝔸.α e c₁)
    exact ⟨rfl, c₂ * c₁, (hpq.trans (hqr.cons _)).trans hmul⟩

private def rawDartSetoid : Setoid (RawDart 𝔸 v₀) where
  r := RawDart.Rel 𝔸 v₀
  iseqv := ⟨RawDart.rel_refl 𝔸 v₀, RawDart.rel_symm 𝔸 v₀, RawDart.rel_trans 𝔸 v₀⟩

/-- Reversal on raw darts: `(e, p)` reverses to `(Γ.rev e, p · e)`. -/
private def RawDart.rev : RawDart 𝔸 v₀ → RawDart 𝔸 v₀
  | ⟨e, p⟩ => ⟨Γ.rev e, p.cons (Letter.dart (Γ.dart e))⟩

private theorem RawDart.rev_rel :
    ∀ {x y : RawDart 𝔸 v₀}, RawDart.Rel 𝔸 v₀ x y →
      RawDart.Rel 𝔸 v₀ (RawDart.rev 𝔸 v₀ x) (RawDart.rev 𝔸 v₀ y)
  | ⟨e, _⟩, ⟨_, q⟩, ⟨rfl, c, hpq⟩ => by
    refine ⟨rfl, MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e).symm c, ?_⟩
    rw [α_rev_apply]
    simp only [MulEquiv.cast_apply, cast_cast, cast_eq]
    exact (hpq.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.dart_ω e c q).symm

private theorem RawDart.rev_rev_rel :
    ∀ x : RawDart 𝔸 v₀, RawDart.Rel 𝔸 v₀ (RawDart.rev 𝔸 v₀ (RawDart.rev 𝔸 v₀ x)) x
  | ⟨e, p⟩ => by
    have aux : ∀ {e'' : Γ.E} (he : e = e'') (f' : Γ.tgt e ⟶ Γ.src e''),
        f'.1 = Γ.rev e →
          Path.Homotopic (he.symm ▸ ((p.cons (Letter.dart (Γ.dart e))).cons (Letter.dart f')))
            (p.cons (Letter.vertex (𝔸.α e 1))) := by
      rintro _ rfl f' hf'
      obtain rfl : f' = Quiver.reverse (Γ.dart e) :=
        Γ.eq_reverse_of_val_eq_rev (hf'.trans (congrArg Γ.rev (Γ.dart_val e).symm))
      rw [map_one]
      exact (Path.Homotopic.dart_reverse p (Γ.dart e)).trans (Path.Homotopic.one p).symm
    exact ⟨Γ.rev_rev e, 1, aux (Γ.rev_rev e).symm (Γ.dart (Γ.rev e)) (Γ.dart_val (Γ.rev e))⟩

/-- The underlying Serre graph of the Bass–Serre tree `X(𝔸, v₀)`. -/
def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := Quotient (rawVertexSetoid 𝔸 v₀)
  E := Quotient (rawDartSetoid 𝔸 v₀)
  src := Quotient.map (fun x => ⟨Γ.src x.dart, x.path⟩) (by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, c, hpq⟩
    exact ⟨rfl, 𝔸.α _ c, hpq⟩)
  rev := Quotient.map (RawDart.rev 𝔸 v₀) fun _ _ h => RawDart.rev_rel 𝔸 v₀ h
  rev_rev := Quotient.ind fun x => Quotient.sound (RawDart.rev_rev_rel 𝔸 v₀ x)
  rev_ne := Quotient.ind fun ⟨e, _⟩ h => by
    obtain ⟨hdart, _, _⟩ := Quotient.exact h
    exact Γ.rev_ne e hdart

namespace BassSerreTree

section Internal

variable {𝔸 v₀}

private def vMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (𝔸.bassSerreGraph v₀).V :=
  Quotient.mk (rawVertexSetoid 𝔸 v₀) ⟨v, p⟩

private def dMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreGraph v₀).E :=
  Quotient.mk (rawDartSetoid 𝔸 v₀) ⟨e, p⟩

private def aMk : ∀ {a b : Γ.V}, (a ⟶ b) → 𝔸.Path ⟨v₀⟩ ⟨a⟩ → (𝔸.bassSerreGraph v₀).E
  | _, _, ⟨e, rfl, _⟩, p => dMk e p

private theorem vMk_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    vMk (p.cons (Letter.vertex a)) = vMk p :=
  Quotient.sound ⟨rfl, a, .refl _⟩

private theorem vMk_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    vMk p = vMk q :=
  Quotient.sound ⟨rfl, 1, h.trans (Path.Homotopic.one q).symm⟩

private theorem aMk_congr {a b : Γ.V} (f : a ⟶ b) {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q) :
    aMk f p = aMk f q := by
  rcases f with ⟨e, rfl, rfl⟩
  exact Quotient.sound ⟨rfl, 1, h.trans (by simpa only [map_one] using (Path.Homotopic.one q).symm)⟩

@[simp] private theorem aMk_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    aMk (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) p = dMk e p :=
  rfl

private theorem aMk_cons_αArrow {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge f.1)) :
    aMk f (p.cons (Letter.vertex (𝔸.αArrow f c))) = aMk f p := by
  rcases f with ⟨e, rfl, rfl⟩
  rw [αArrow_mk]
  exact Quotient.sound ⟨rfl, c, .refl _⟩

private theorem src_aMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreGraph v₀).src (aMk f p) = vMk p := by
  rcases f with ⟨e, rfl, rfl⟩
  rfl

private theorem rev_dMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).rev (dMk e p) = dMk (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) :=
  rfl

private theorem tgt_dMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).tgt (dMk e p) = vMk (p.cons (Letter.dart (Γ.dart e))) :=
  rfl

private theorem rev_aMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreGraph v₀).rev (aMk f p) = aMk (Quiver.reverse f) (p.cons (Letter.dart f)) := by
  rcases hrev : Quiver.reverse f with ⟨e', he₁, _⟩
  rcases f with ⟨e, rfl, rfl⟩
  obtain rfl : e' = Γ.rev e :=
    (congrArg Subtype.val hrev).symm.trans (Γ.reverse_val (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e))
  obtain rfl : he₁ = rfl := rfl
  rw [aMk_mk, rev_dMk, Γ.dart_def]
  rfl

private theorem tgt_aMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreGraph v₀).tgt (aMk f p) = vMk (p.cons (Letter.dart f)) := by
  rcases f with ⟨e, rfl, rfl⟩
  rw [aMk_mk, tgt_dMk, Γ.dart_def]

private def rawProjE : (𝔸.bassSerreGraph v₀).E → Γ.E :=
  Quotient.lift RawDart.dart fun ⟨_, _⟩ ⟨_, _⟩ ⟨h, _, _⟩ => h

private def rawProjV : (𝔸.bassSerreGraph v₀).V → Γ.V :=
  Quotient.lift RawVertex.vertex fun ⟨_, _⟩ ⟨_, _⟩ ⟨h, _, _⟩ => h

private def rawPrecompHom {v₁ : Γ.V} (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) :
    (𝔸.bassSerreGraph v₀).Hom (𝔸.bassSerreGraph v₁) where
  mapV := Quotient.map (fun x => ⟨x.vertex, q.comp x.path⟩) (by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, a, hp⟩
    exact ⟨rfl, a, hp.comp_left q⟩)
  mapE := Quotient.map (fun x => ⟨x.dart, q.comp x.path⟩) (by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, c, hp⟩
    exact ⟨rfl, c, hp.comp_left q⟩)
  map_src := Quotient.ind fun ⟨_, _⟩ => rfl
  map_rev := Quotient.ind fun ⟨_, _⟩ => rfl

private def rawChangeBaseIso {v₁ : Γ.V} (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) :
    (𝔸.bassSerreGraph v₀).Iso (𝔸.bassSerreGraph v₁) where
  equivV :=
    { toFun := (rawPrecompHom q).mapV
      invFun := (rawPrecompHom q.reverse).mapV
      left_inv := Quotient.ind fun ⟨_, p⟩ => Quotient.sound ⟨rfl, 1, by
        rw [← Quiver.Path.comp_assoc]
        exact ((Path.Homotopic.reverse_comp q).comp (.refl p)).trans
          (by rw [Quiver.Path.nil_comp]; exact (Path.Homotopic.one p).symm)⟩
      right_inv := Quotient.ind fun ⟨_, p⟩ => Quotient.sound ⟨rfl, 1, by
        rw [← Quiver.Path.comp_assoc]
        exact ((Path.Homotopic.comp_reverse q).comp (.refl p)).trans
          (by rw [Quiver.Path.nil_comp]; exact (Path.Homotopic.one p).symm)⟩ }
  equivE :=
    { toFun := (rawPrecompHom q).mapE
      invFun := (rawPrecompHom q.reverse).mapE
      left_inv := Quotient.ind fun ⟨_, p⟩ => Quotient.sound ⟨rfl, 1, by
        rw [← Quiver.Path.comp_assoc, map_one]
        exact ((Path.Homotopic.reverse_comp q).comp (.refl p)).trans
          (by rw [Quiver.Path.nil_comp]; exact (Path.Homotopic.one p).symm)⟩
      right_inv := Quotient.ind fun ⟨_, p⟩ => Quotient.sound ⟨rfl, 1, by
        rw [← Quiver.Path.comp_assoc, map_one]
        exact ((Path.Homotopic.comp_reverse q).comp (.refl p)).trans
          (by rw [Quiver.Path.nil_comp]; exact (Path.Homotopic.one p).symm)⟩ }
  map_src := (rawPrecompHom q).map_src
  map_rev := (rawPrecompHom q).map_rev

private theorem rawChangeBaseIso_congr {v₁ : Γ.V} {q q' : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩}
    (h : q.Homotopic q') : rawChangeBaseIso q = rawChangeBaseIso q' :=
  SerreGraph.Iso.ext
    (Quotient.ind fun ⟨_, p⟩ => vMk_congr (h.comp_right p))
    (Quotient.ind fun ⟨_, p⟩ =>
      Quotient.sound ⟨rfl, 1, (h.comp_right p).trans
        (by simpa only [map_one] using (Path.Homotopic.one _).symm)⟩)

private theorem rawChangeBaseIso_nil :
    rawChangeBaseIso (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) = SerreGraph.Iso.refl (𝔸.bassSerreGraph v₀) :=
  SerreGraph.Iso.ext
    (Quotient.ind fun ⟨_, p⟩ => Quotient.sound ⟨rfl, 1, by
      rw [Quiver.Path.nil_comp]
      exact (Path.Homotopic.one p).symm⟩)
    (Quotient.ind fun ⟨_, p⟩ => Quotient.sound ⟨rfl, 1, by
      rw [Quiver.Path.nil_comp, map_one]
      exact (Path.Homotopic.one p).symm⟩)

private theorem rawChangeBaseIso_comp {v₁ v₂ : Γ.V} (r : 𝔸.Path ⟨v₂⟩ ⟨v₁⟩)
    (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) :
    (rawChangeBaseIso q).trans (rawChangeBaseIso r) = rawChangeBaseIso (r.comp q) :=
  SerreGraph.Iso.ext
    (Quotient.ind fun ⟨_, _⟩ => Quotient.sound ⟨rfl, 1, by
      rw [Quiver.Path.comp_assoc]
      exact (Path.Homotopic.one _).symm⟩)
    (Quotient.ind fun ⟨_, _⟩ => Quotient.sound ⟨rfl, 1, by
      rw [Quiver.Path.comp_assoc, map_one]
      exact (Path.Homotopic.one _).symm⟩)

variable (𝔸 v₀) in
/-- Left action of `π₁(𝔸, v₀)` by automorphisms of `X(𝔸, v₀)`, sending `[γ]` to left
concatenation by `γ`. -/
def action : π₁ 𝔸 v₀ →* (𝔸.bassSerreGraph v₀).Aut where
  toFun := π₁.lift rawChangeBaseIso fun _ _ h => rawChangeBaseIso_congr h
  map_one' := by rw [← π₁.mk_nil, π₁.lift_mk, rawChangeBaseIso_nil]; rfl
  map_mul' g h := π₁.induction_on g fun p => π₁.induction_on h fun q => by
    rw [← π₁.mk_comp, π₁.lift_mk, π₁.lift_mk, π₁.lift_mk, ← rawChangeBaseIso_comp]
    rfl

private theorem action_mk_eq_rawChangeBaseIso (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    action 𝔸 v₀ (π₁.mk γ) = rawChangeBaseIso γ :=
  π₁.lift_mk _ _ γ

variable (𝔸 v₀) in
/-- No element of `π₁(𝔸, v₀)` maps a dart of `X(𝔸, v₀)` to its reverse. -/
theorem action_smul_ne_rev (g : π₁ 𝔸 v₀) (δ : (𝔸.bassSerreGraph v₀).E) :
    (action 𝔸 v₀ g).equivE δ ≠ (𝔸.bassSerreGraph v₀).rev δ :=
  π₁.induction_on g fun γ => Quotient.inductionOn δ fun ⟨e, p⟩ h => by
    have hact : (action 𝔸 v₀ (π₁.mk γ)).equivE (dMk e p) = dMk e (γ.comp p) := by
      rw [action_mk_eq_rawChangeBaseIso]
      rfl
    have he : e = Γ.rev e := congrArg rawProjE (hact.symm.trans h)
    exact Γ.rev_ne e he.symm

private theorem nonempty_path_from_base :
    ∀ {y : 𝔸.LetterVertex} (p : 𝔸.Path ⟨v₀⟩ y),
      Nonempty ((𝔸.bassSerreGraph v₀).Path (vMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) (vMk p))
  | _, .nil => ⟨.nil⟩
  | _, .cons p (.vertex a) => by
    rw [vMk_cons_vertex]
    exact nonempty_path_from_base p
  | _, .cons p (.dart f) => by
    obtain ⟨P⟩ := nonempty_path_from_base p
    exact ⟨P.cons ⟨aMk f p, src_aMk f p, tgt_aMk f p⟩⟩

variable (𝔸 v₀) in
/-- The Bass–Serre graph `X(𝔸, v₀)` is connected. -/
theorem connected : (𝔸.bassSerreGraph v₀).Connected :=
  (𝔸.bassSerreGraph v₀).connected_iff.mpr ⟨⟨vMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)⟩,
    (𝔸.bassSerreGraph v₀).preconnected_of_forall_nonempty_path _
      (Quotient.ind fun ⟨_, p⟩ => nonempty_path_from_base p)⟩

private theorem alternatingPath_edgePath_setLast {a b : Γ.V} (q : 𝔸.AlternatingPath a b)
    (g : 𝔸.vertexGroup b) : (q.setLast g).toPath.edgePath = q.toPath.edgePath := by
  cases q <;> simp

private theorem not_cancels_of_edgePath_length_eq_zero {a b c : Γ.V} {q : 𝔸.AlternatingPath a b}
    (hq : q.toPath.edgePath.length = 0) (e : b ⟶ c) : ¬ q.Cancels e := by
  cases q with
  | single g => exact AlternatingPath.not_cancels_single g e
  | cons _ _ _ => simp at hq

/-- Dart length of the normal form of a vertex in `X(𝔸, v₀)` relative to a transversal `d`. -/
private noncomputable def vertexLength (d : 𝔸.Transversal) : (𝔸.bassSerreGraph v₀).V → ℕ :=
  Quotient.lift (fun x => (normalForm d x.path).toPath.edgePath.length) (by
    rintro ⟨_, p⟩ ⟨_, q⟩ ⟨rfl, a, hpq⟩
    have hnf : normalForm d p = (normalForm d q).mulLast a := by
      simpa using normalForm_eq_of_homotopic d hpq
    rw [hnf, NormalWord.toPath_def, NormalWord.toPath_def, NormalWord.toAlternatingPath_mulLast,
      alternatingPath_edgePath_setLast])

@[simp] private theorem vertexLength_vMk (d : 𝔸.Transversal) {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    vertexLength d (vMk p) = (normalForm d p).toPath.edgePath.length :=
  rfl

@[simp] private theorem vertexLength_nil (d : 𝔸.Transversal) :
    vertexLength d (vMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) = 0 := by
  simp [vertexLength_vMk]

private theorem exists_eq_aMk_of_src_eq {b : Γ.V} (r : 𝔸.Path ⟨v₀⟩ ⟨b⟩)
    {δ : (𝔸.bassSerreGraph v₀).E} (hsrc : (𝔸.bassSerreGraph v₀).src δ = vMk r) :
    ∃ (c : Γ.V) (f : b ⟶ c) (g : 𝔸.vertexGroup b),
      δ = aMk f (r.cons (Letter.vertex g)) := by
  refine Quotient.inductionOn δ (fun ⟨e, p⟩ hsrc => ?_) hsrc
  have hb : Γ.src e = b := congrArg rawProjV hsrc
  subst hb
  obtain ⟨_, g, hg⟩ := Quotient.exact hsrc
  refine ⟨Γ.tgt e, Γ.dart e, g, ?_⟩
  rw [Γ.dart_def]
  exact Quotient.sound ⟨rfl, 1,
    hg.trans (by simpa only [map_one] using (Path.Homotopic.one _).symm)⟩

private theorem vertexLength_tgt_aMk_of_not_cancels (d : 𝔸.Transversal) {a b : Γ.V}
    (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (hc : ¬ (normalForm d p).1.Cancels f) :
    vertexLength d ((𝔸.bassSerreGraph v₀).tgt (aMk f p)) =
      vertexLength d ((𝔸.bassSerreGraph v₀).src (aMk f p)) + 1 := by
  rw [tgt_aMk, src_aMk, vertexLength_vMk, vertexLength_vMk,
    normalForm_cons, NormalWord.appendLetter_dart, NormalWord.toPath_def, NormalWord.toPath_def,
    NormalWord.toAlternatingPath_appendDart, AlternatingPath.appendDart_of_not_cancels d hc]
  simp [alternatingPath_edgePath_setLast]

private theorem eq_rev_aMk_of_cancels (d : 𝔸.Transversal) {a b c : Γ.V} (f : a ⟶ b)
    (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (hc : ¬ (normalForm d p).1.Cancels f) (f' : b ⟶ c)
    (g' : 𝔸.vertexGroup b)
    (hc' : (normalForm d ((p.cons (Letter.dart f)).cons (Letter.vertex g'))).1.Cancels f') :
    aMk f' ((p.cons (Letter.dart f)).cons (Letter.vertex g')) =
      (𝔸.bassSerreGraph v₀).rev (aMk f p) := by
  have hw : (normalForm d ((p.cons (Letter.dart f)).cons (Letter.vertex g'))).1 =
      .cons ((normalForm d p).1.setLast (d.rep f (normalForm d p).1.last)) f
        (𝔸.ωArrow f (d.edgePart f (normalForm d p).1.last) * g') := by
    simp [AlternatingPath.appendDart_of_not_cancels d hc]
  rw [hw, AlternatingPath.cancels_cons_iff] at hc'
  obtain ⟨hf', hmem⟩ := hc'
  obtain rfl : a = c := Γ.src_eq_tgt_of_val_eq_rev hf'
  obtain rfl : f = Quiver.reverse f' := Γ.eq_reverse_of_val_eq_rev hf'
  have hf'_eq : f' = Quiver.reverse (Quiver.reverse f') := (Quiver.reverse_reverse f').symm
  have hω : 𝔸.ωArrow (Quiver.reverse f') (d.edgePart (Quiver.reverse f') (normalForm d p).1.last) ∈
      (𝔸.αArrow f').range := by
    rw [← 𝔸.range_ωArrow_reverse]
    exact ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : g' ∈ (𝔸.αArrow f').range :=
    ((𝔸.αArrow f').range.mul_mem_cancel_left hω).mp hmem
  rw [← hc₁, aMk_cons_αArrow, rev_aMk, ← hf'_eq]

private theorem not_cancels_of_eq_tgt_aMk (d : 𝔸.Transversal) {a b : Γ.V} (f : a ⟶ b)
    (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) (hnc : ¬ (normalForm d p).1.Cancels f) {δ : (𝔸.bassSerreGraph v₀).E}
    (hδ : δ = aMk f p) {c : Γ.V} (r : 𝔸.Path ⟨v₀⟩ ⟨c⟩)
    (hyr : vMk r = (𝔸.bassSerreGraph v₀).tgt δ) {c' : Γ.V} (f' : c ⟶ c')
    (g' : 𝔸.vertexGroup c)
    (hne : aMk f' (r.cons (Letter.vertex g')) ≠ (𝔸.bassSerreGraph v₀).rev δ) :
    ¬ (normalForm d (r.cons (Letter.vertex g'))).1.Cancels f' := by
  intro hc'
  rw [hδ, tgt_aMk] at hyr
  obtain ⟨rfl, a₀, ha⟩ := Quotient.exact hyr
  have hhom : Path.Homotopic (r.cons (Letter.vertex g'))
      ((p.cons (Letter.dart f)).cons (Letter.vertex (a₀ * g'))) :=
    (ha.cons (Letter.vertex g')).trans (Path.Homotopic.mul _ a₀ g')
  have hc'' := normalForm_eq_of_homotopic d hhom ▸ hc'
  exact hne ((aMk_congr f' hhom).trans
    ((eq_rev_aMk_of_cancels d f p hnc f' (a₀ * g') hc'').trans
      (congrArg (𝔸.bassSerreGraph v₀).rev hδ.symm)))

private theorem reduced_from_nil_step (d : 𝔸.Transversal) :
    ∀ {z : (𝔸.bassSerreGraph v₀).V}
      (P : (𝔸.bassSerreGraph v₀).Path (vMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) z)
      {y : (𝔸.bassSerreGraph v₀).V} (δ : z ⟶ y),
      SerreGraph.Path.IsReduced (𝔸.bassSerreGraph v₀) (P.cons δ) →
      vertexLength d y = P.length + 1 ∧
        ∀ {c : Γ.V} (r : 𝔸.Path ⟨v₀⟩ ⟨c⟩), y = vMk r →
          ∀ {c' : Γ.V} (f' : c ⟶ c') (g' : 𝔸.vertexGroup c),
            aMk f' (r.cons (Letter.vertex g')) ≠ (𝔸.bassSerreGraph v₀).rev δ.1 →
              ¬ (normalForm d (r.cons (Letter.vertex g'))).1.Cancels f'
  | _, .nil, _, δ, _ => by
    obtain ⟨b, f, g, hδ⟩ := exists_eq_aMk_of_src_eq (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) δ.2.1
    have hnc : ¬ (normalForm d ((.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩).cons (Letter.vertex g))).1.Cancels f :=
      not_cancels_of_edgePath_length_eq_zero (by simp) f
    refine ⟨?_, fun r hr => not_cancels_of_eq_tgt_aMk d f _ hnc hδ r (hr.symm.trans δ.2.2.symm)⟩
    rw [← δ.2.2, hδ, vertexLength_tgt_aMk_of_not_cancels d f _ hnc, src_aMk, vMk_cons_vertex]
    simp
  | _, .cons P₀ δ₀, _, δ, hred => by
    obtain ⟨hP₀, hne₀⟩ := (SerreGraph.Path.isReduced_cons_cons _ P₀ δ₀ δ).mp hred
    obtain ⟨hlen₀, hstep₀⟩ := reduced_from_nil_step d P₀ δ₀ hP₀
    refine Quotient.inductionOn (motive := fun x => δ₀.1 = x → _) δ₀.1 (fun ⟨e₀, p₀⟩ hδ₀ => ?_) rfl
    have hz : _ = vMk (p₀.cons (Letter.dart (Γ.dart e₀))) :=
      δ₀.2.2.symm.trans (congrArg (𝔸.bassSerreGraph v₀).tgt hδ₀)
    obtain ⟨b, f, g, hδ⟩ := exists_eq_aMk_of_src_eq _ (δ.2.1.trans hz)
    have hnc : ¬ (normalForm d ((p₀.cons (Letter.dart (Γ.dart e₀))).cons
        (Letter.vertex g))).1.Cancels f :=
      hstep₀ _ hz f g (hδ ▸ hne₀)
    refine ⟨?_, fun r hr =>
      not_cancels_of_eq_tgt_aMk d f _ hnc hδ r (hr.symm.trans δ.2.2.symm)⟩
    rw [← δ.2.2, hδ, vertexLength_tgt_aMk_of_not_cancels d f _ hnc, src_aMk,
      vMk_cons_vertex, ← hz, hlen₀, Quiver.Path.length_cons]

private theorem eq_nil_of_isReduced_nil
    (P : (𝔸.bassSerreGraph v₀).Path (vMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩))
      (vMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)))
    (hP : SerreGraph.Path.IsReduced (𝔸.bassSerreGraph v₀) P) : P = .nil := by
  cases P with
  | nil => rfl
  | cons P₀ δ =>
    have hlen := (reduced_from_nil_step (default : 𝔸.Transversal) P₀ δ hP).1
    rw [vertexLength_nil] at hlen
    exact absurd hlen.symm (Nat.succ_ne_zero _)

variable (𝔸 v₀) in
/-- The Bass–Serre graph `X(𝔸, v₀)` is acyclic. -/
theorem isAcyclic : (𝔸.bassSerreGraph v₀).IsAcyclic := by
  -- Transport any reduced closed path at `u = [p]` along `rawChangeBaseIso p.reverse` to a reduced
  -- closed path at the base vertex of `X(𝔸, v)`.
  refine ((𝔸.bassSerreGraph v₀).isAcyclic_iff).mpr fun u P hP => ?_
  refine Quotient.inductionOn u (fun ⟨v, p⟩ P hP => ?_) P hP
  let φ := rawChangeBaseIso p.reverse
  have hmap : SerreGraph.Path.IsReduced (𝔸.bassSerreGraph v) (φ.toHom.toPrefunctor.mapPath P) :=
    (SerreGraph.Hom.isReduced_mapPath_iff _ φ.toHom φ.toHom_mapE_injective P).mpr hP
  have hbase : φ.toHom.toPrefunctor.obj (vMk p) = vMk (.nil : 𝔸.Path ⟨v⟩ ⟨v⟩) :=
    vMk_congr (Path.Homotopic.reverse_comp p)
  have hcast : SerreGraph.Path.IsReduced (𝔸.bassSerreGraph v)
      ((φ.toHom.toPrefunctor.mapPath P).cast hbase hbase) :=
    (SerreGraph.Path.isReduced_cast _ hbase hbase _).mpr hmap
  have hnil := eq_nil_of_isReduced_nil _ hcast
  have hcl : ∀ {w w' : (𝔸.bassSerreGraph v).V} (hw : w = w')
      (Q : (𝔸.bassSerreGraph v).Path w w), (Q.cast hw hw).length = Q.length := by
    rintro _ _ rfl _; rfl
  have hlen : P.length = 0 :=
    (φ.toHom.toPrefunctor.length_mapPath P).symm.trans
      ((hcl hbase _).symm.trans (congrArg (fun Q => Q.length) hnil))
  exact Quiver.Path.eq_nil_of_length_zero P hlen

end Internal

end BassSerreTree

/-- The Bass–Serre graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree : (𝔸.bassSerreGraph v₀).IsTree :=
  (𝔸.bassSerreGraph v₀).isTree_iff.mpr ⟨BassSerreTree.connected 𝔸 v₀, BassSerreTree.isAcyclic 𝔸 v₀⟩

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`, as a
`GTree` for `π₁(𝔸, v₀)` acting on the left by path concatenation. -/
@[expose] def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := 𝔸.bassSerreGraph v₀
  isTree := 𝔸.bassSerreTree_isTree v₀
  action := BassSerreTree.action 𝔸 v₀
  action_smul_ne_rev := BassSerreTree.action_smul_ne_rev 𝔸 v₀

end Construction

/-! ### Constructors, elimination principles, projections, basepoint change, and action API -/

section API

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ v₁ v₂ : Γ.V}

namespace BassSerreTree

@[simp] theorem toSerreGraph_bassSerreTree :
    (𝔸.bassSerreTree v₀).toSerreGraph = 𝔸.bassSerreGraph v₀ :=
  (rfl)

/-- The vertex `p A_v` of `X(𝔸, v₀)` represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (𝔸.bassSerreTree v₀).V :=
  Quotient.mk (rawVertexSetoid 𝔸 v₀) ⟨v, p⟩

variable (𝔸 v₀) in
/-- The distinguished base vertex `1 · A_{v₀}` of `X(𝔸, v₀)`, represented by the empty path at
`v₀`. -/
@[expose] def baseVertex : (𝔸.bassSerreTree v₀).V :=
  vertexMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)

/-- Definitional unfolding of `baseVertex` as `vertexMk .nil`. -/
theorem baseVertex_def : baseVertex 𝔸 v₀ = vertexMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :=
  (rfl)

/-- The dart `p α_e(A_e)` of `X(𝔸, v₀)` above `e : Γ.E`, represented by an `𝔸`-path `p` from `v₀`
to `Γ.src e`. -/
def dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreTree v₀).E :=
  Quotient.mk (rawDartSetoid 𝔸 v₀) ⟨e, p⟩

/-- The dart of `X(𝔸, v₀)` above an arrow `f : a ⟶ b` of `Γ`, represented by an `𝔸`-path `p` from
`v₀` to `a`. -/
def arrowMk : ∀ {a b : Γ.V}, (a ⟶ b) → 𝔸.Path ⟨v₀⟩ ⟨a⟩ → (𝔸.bassSerreTree v₀).E
  | _, _, ⟨e, rfl, _⟩, p => dartMk e p

@[simp] theorem arrowMk_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    arrowMk (Γ.dart e) p = dartMk e p := by
  rw [Γ.dart_def]
  rfl

/-- Induction principle for vertices of `X(𝔸, v₀)`. -/
@[elab_as_elim]
theorem vertex_induction_on {motive : (𝔸.bassSerreTree v₀).V → Prop}
    (x : (𝔸.bassSerreTree v₀).V)
    (mk : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), motive (vertexMk p)) : motive x :=
  Quotient.inductionOn x fun ⟨_, p⟩ => mk p

/-- Induction principle for darts of `X(𝔸, v₀)`. -/
@[elab_as_elim]
theorem dart_induction_on {motive : (𝔸.bassSerreTree v₀).E → Prop}
    (δ : (𝔸.bassSerreTree v₀).E)
    (mk : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), motive (dartMk e p)) : motive δ :=
  Quotient.inductionOn δ fun ⟨e, p⟩ => mk e p

@[simp] theorem arrowMk_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    arrowMk (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e) p = dartMk e p :=
  (rfl)

/-- Lift a family of maps on `𝔸`-paths starting at `v₀` to vertices of `X(𝔸, v₀)`, provided the
map is invariant under path homotopy and right multiplication by vertex group elements. -/
def vertexLift {α : Sort*} (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → α)
    (h_congr : ∀ {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f p = f q)
    (h_vertex : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v),
      f (p.cons (Letter.vertex a)) = f p) :
    (𝔸.bassSerreTree v₀).V → α :=
  Quotient.lift (fun x => f x.path) (by
    rintro ⟨_, _⟩ ⟨_, q⟩ ⟨rfl, a, hpq⟩
    exact (h_congr hpq).trans (h_vertex q a))

@[simp] theorem vertexLift_vertexMk {α : Sort*} (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → α)
    (h_congr) (h_vertex) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    vertexLift f h_congr h_vertex (vertexMk p) = f p :=
  (rfl)

/-- Lift a family of maps on raw darts `(e, p)` to darts of `X(𝔸, v₀)`, provided the map is
invariant under path homotopy and right multiplication by `α_e(A_e)`. -/
def dartLift {α : Sort*} (f : ∀ (e : Γ.E), 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → α)
    (h_congr : ∀ {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}, p.Homotopic q → f e p = f e q)
    (h_α : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      f e (p.cons (Letter.vertex (𝔸.α e c))) = f e p) :
    (𝔸.bassSerreTree v₀).E → α :=
  Quotient.lift (fun x => f x.dart x.path) (by
    rintro ⟨e, _⟩ ⟨_, q⟩ ⟨rfl, c, hpq⟩
    exact (h_congr hpq).trans (h_α e q c))

@[simp] theorem dartLift_dartMk {α : Sort*} (f : ∀ (e : Γ.E), 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → α)
    (h_congr) (h_α) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    dartLift f h_congr h_α (dartMk e p) = f e p :=
  (rfl)

/-- Appending an element of `A_v` at the end of `p` does not change the vertex `p A_v`. -/
@[simp] theorem vertexMk_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    vertexMk (p.cons (Letter.vertex a)) = vertexMk p :=
  Quotient.sound ⟨rfl, a, .refl _⟩

@[simp] theorem vertexMk_ofVertex (a : 𝔸.vertexGroup v₀) :
    vertexMk (Path.ofVertex a) = baseVertex 𝔸 v₀ := by
  rw [Path.ofVertex_eq_nil_cons, vertexMk_cons_vertex, baseVertex]

/-- Homotopic `𝔸`-paths define the same vertex of `X(𝔸, v₀)`. -/
theorem vertexMk_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : p.Homotopic q) :
    vertexMk p = vertexMk q :=
  Quotient.sound ⟨rfl, 1, h.trans (Path.Homotopic.one q).symm⟩

/-- Two `𝔸`-paths with arbitrary endpoints define the same vertex of `X(𝔸, v₀)` if and only if
their endpoints agree and they differ on the right by an element of the endpoint vertex group. -/
theorem vertexMk_eq_vertexMk_iff {u v : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨u⟩} {q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    vertexMk p = vertexMk q ↔
      ∃ h : u = v, ∃ a : 𝔸.vertexGroup v, Path.Homotopic (h ▸ p) (q.cons (Letter.vertex a)) :=
  Quotient.eq

/-- Two `𝔸`-paths to the same vertex `v` define the same vertex of `X(𝔸, v₀)` if and only if they
differ on the right by an element of `A_v`. -/
theorem vertexMk_eq_vertexMk_same_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    vertexMk p = vertexMk q ↔ ∃ a : 𝔸.vertexGroup v, p.Homotopic (q.cons (Letter.vertex a)) :=
  vertexMk_eq_vertexMk_iff.trans ⟨fun ⟨_, a, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨rfl, a, h⟩⟩

/-- Appending `α_e(c)` at the end of `p` does not change the dart `p α_e(A_e)`. -/
@[simp] theorem dartMk_cons_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    dartMk e (p.cons (Letter.vertex (𝔸.α e c))) = dartMk e p :=
  Quotient.sound ⟨rfl, c, .refl _⟩

@[simp] theorem arrowMk_cons_αArrow {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge f.1)) :
    arrowMk f (p.cons (Letter.vertex (𝔸.αArrow f c))) = arrowMk f p := by
  rcases f with ⟨e, rfl, rfl⟩
  rw [αArrow_mk, arrowMk_mk, arrowMk_mk]
  exact dartMk_cons_α e p c

/-- Homotopic `𝔸`-paths define the same dart of `X(𝔸, v₀)`. -/
theorem dartMk_congr (e : Γ.E) {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    dartMk e p = dartMk e q :=
  Quotient.sound ⟨rfl, 1, h.trans (by simpa only [map_one] using (Path.Homotopic.one q).symm)⟩

/-- Homotopic `𝔸`-paths define the same dart above an arrow `f`. -/
theorem arrowMk_congr {a b : Γ.V} (f : a ⟶ b) {p q : 𝔸.Path ⟨v₀⟩ ⟨a⟩} (h : p.Homotopic q) :
    arrowMk f p = arrowMk f q := by
  rcases f with ⟨e, rfl, rfl⟩
  exact dartMk_congr e h

/-- Two raw darts define the same dart of `X(𝔸, v₀)` if and only if they have the same underlying
dart `e` and their paths differ on the right by an element of `α_e(A_e)`. -/
theorem dartMk_eq_dartMk_iff {e₁ e₂ : Γ.E} {p₁ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₁⟩}
    {p₂ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₂⟩} :
    dartMk e₁ p₁ = dartMk e₂ p₂ ↔
      ∃ h : e₁ = e₂, ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e₂),
        Path.Homotopic (h ▸ p₁) (p₂.cons (Letter.vertex (𝔸.α e₂ c))) :=
  Quotient.eq

/-- Two `𝔸`-paths to `Γ.src e` define the same dart above `e` if and only if they differ on the
right by an element of `α_e(A_e)`. -/
theorem dartMk_eq_dartMk_same_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    dartMk e p = dartMk e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), p.Homotopic (q.cons (Letter.vertex (𝔸.α e c))) :=
  dartMk_eq_dartMk_iff.trans ⟨fun ⟨_, c, h⟩ => ⟨c, h⟩, fun ⟨c, h⟩ => ⟨rfl, c, h⟩⟩

@[simp] theorem src_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).src (dartMk e p) = vertexMk p :=
  (rfl)

@[simp] theorem rev_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).rev (dartMk e p) = dartMk (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem tgt_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).tgt (dartMk e p) = vertexMk (p.cons (Letter.dart (Γ.dart e))) :=
  (rfl)

@[simp] theorem src_arrowMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreTree v₀).src (arrowMk f p) = vertexMk p := by
  rcases f with ⟨e, rfl, rfl⟩
  rfl

@[simp] theorem rev_arrowMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreTree v₀).rev (arrowMk f p) =
      arrowMk (Quiver.reverse f) (p.cons (Letter.dart f)) := by
  rcases hrev : Quiver.reverse f with ⟨e', he₁, _⟩
  rcases f with ⟨e, rfl, rfl⟩
  obtain rfl : e' = Γ.rev e :=
    (congrArg Subtype.val hrev).symm.trans (Γ.reverse_val (⟨e, rfl, rfl⟩ : Γ.src e ⟶ Γ.tgt e))
  obtain rfl : he₁ = rfl := rfl
  rw [arrowMk_mk, rev_dartMk, Γ.dart_def]
  rfl

@[simp] theorem tgt_arrowMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (𝔸.bassSerreTree v₀).tgt (arrowMk f p) = vertexMk (p.cons (Letter.dart f)) := by
  rcases f with ⟨e, rfl, rfl⟩
  rw [arrowMk_mk, tgt_dartMk, Γ.dart_def]

variable (𝔸 v₀) in
/-- Projection from `X(𝔸, v₀)` to the underlying graph `Γ`, sending `p A_v` to `v` and
`p α_e(A_e)` to `e`. -/
def projHom : (𝔸.bassSerreTree v₀).toSerreGraph.Hom Γ where
  mapV := vertexLift (fun {v} _ => v) (fun _ => rfl) (fun _ _ => rfl)
  mapE := dartLift (fun e _ => e) (fun _ => rfl) (fun _ _ _ => rfl)
  map_src := Quotient.ind fun ⟨_, _⟩ => rfl
  map_rev := Quotient.ind fun ⟨_, _⟩ => rfl

@[simp] theorem projHom_mapV_vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (projHom 𝔸 v₀).mapV (vertexMk p) = v :=
  (rfl)

@[simp] theorem projHom_mapV_baseVertex :
    (projHom 𝔸 v₀).mapV (baseVertex 𝔸 v₀) = v₀ :=
  (rfl)

@[simp] theorem projHom_mapE_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (projHom 𝔸 v₀).mapE (dartMk e p) = e :=
  (rfl)

@[simp] theorem projHom_mapE_arrowMk {a b : Γ.V} (f : a ⟶ b) (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    (projHom 𝔸 v₀).mapE (arrowMk f p) = f.1 := by
  rcases f with ⟨e, rfl, rfl⟩
  rfl

variable (𝔸 v₀) in
/-- Projection from `X(𝔸, v₀)` onto the connected component `Γ.component v₀` of `v₀` in `Γ`. -/
def projComponentHom : (𝔸.bassSerreTree v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV := vertexLift (fun {v} p => ⟨v, ⟨p.edgePath⟩⟩) (fun _ => rfl) (fun _ _ => rfl)
  mapE := dartLift (fun e p => ⟨e, ⟨p.edgePath⟩⟩) (fun _ => rfl) (fun _ _ _ => rfl)
  map_src := Quotient.ind fun ⟨_, _⟩ => rfl
  map_rev := Quotient.ind fun ⟨_, _⟩ => rfl

@[simp] theorem projComponentHom_mapV_vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ((projComponentHom 𝔸 v₀).mapV (vertexMk p)).1 = v :=
  (rfl)

@[simp] theorem projComponentHom_mapE_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ((projComponentHom 𝔸 v₀).mapE (dartMk e p)).1 = e :=
  (rfl)

@[simp] theorem componentInclusion_comp_projComponentHom :
    (Γ.componentInclusion v₀).comp (projComponentHom 𝔸 v₀) = projHom 𝔸 v₀ := by
  ext x
  · exact vertex_induction_on x fun _ => by
      rw [SerreGraph.Hom.comp_mapV, Function.comp_apply, Γ.subgraphInclusion_mapV]
      rfl
  · exact dart_induction_on x fun _ _ => by
      rw [SerreGraph.Hom.comp_mapE, Function.comp_apply, Γ.subgraphInclusion_mapE]
      rfl

/-- Every dart of `X(𝔸, v₀)` starting at `vertexMk r` has the form `arrowMk f (r · g)` for some
arrow `f` out of the endpoint of `r` and some vertex group element `g`. -/
theorem exists_eq_arrowMk_of_src_eq {b : Γ.V} (r : 𝔸.Path ⟨v₀⟩ ⟨b⟩)
    {δ : (𝔸.bassSerreTree v₀).E} (hsrc : (𝔸.bassSerreTree v₀).src δ = vertexMk r) :
    ∃ (c : Γ.V) (f : b ⟶ c) (g : 𝔸.vertexGroup b),
      δ = arrowMk f (r.cons (Letter.vertex g)) := by
  induction δ using dart_induction_on with
  | mk e p =>
    rw [src_dartMk] at hsrc
    have hb : Γ.src e = b := congrArg (projHom 𝔸 v₀).mapV hsrc
    subst hb
    obtain ⟨g, hg⟩ := vertexMk_eq_vertexMk_same_iff.mp hsrc
    exact ⟨Γ.tgt e, Γ.dart e, g, (dartMk_congr e hg).trans (arrowMk_dart e _).symm⟩

/-- Left concatenation by an `𝔸`-path `q` from `v₁` to `v₀` induces an isomorphism of Bass–Serre
trees (as Serre graphs) `X(𝔸, v₀) ≅ X(𝔸, v₁)`, with inverse induced by `q.reverse`. -/
def changeBaseIso (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) :
    (𝔸.bassSerreTree v₀).toSerreGraph.Iso (𝔸.bassSerreTree v₁).toSerreGraph :=
  rawChangeBaseIso q

@[simp] theorem changeBaseIso_equivV_vertexMk (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (changeBaseIso q).equivV (vertexMk p) = vertexMk (q.comp p) :=
  (rfl)

@[simp] theorem changeBaseIso_equivE_dartMk (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (changeBaseIso q).equivE (dartMk e p) = dartMk e (q.comp p) :=
  (rfl)

@[simp] theorem changeBaseIso_symm (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) :
    (changeBaseIso q).symm = changeBaseIso q.reverse :=
  SerreGraph.Iso.ext (fun _ => rfl) (fun _ => rfl)

/-- Homotopic `𝔸`-paths induce the same basepoint-change isomorphism. -/
theorem changeBaseIso_congr {q q' : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩} (h : q.Homotopic q') :
    changeBaseIso q = changeBaseIso q' :=
  rawChangeBaseIso_congr h

@[simp] theorem changeBaseIso_nil :
    changeBaseIso (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) =
      SerreGraph.Iso.refl (𝔸.bassSerreTree v₀).toSerreGraph :=
  rawChangeBaseIso_nil

/-- Composing basepoint-change isomorphisms corresponds to concatenating `𝔸`-paths. -/
theorem changeBaseIso_comp (r : 𝔸.Path ⟨v₂⟩ ⟨v₁⟩) (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) :
    (changeBaseIso q).trans (changeBaseIso r) = changeBaseIso (r.comp q) :=
  rawChangeBaseIso_comp r q

/-- Changing basepoint along `p.reverse` carries any vertex `vertexMk p` to `baseVertex 𝔸 v`. -/
@[simp] theorem changeBaseIso_reverse_vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (changeBaseIso p.reverse).equivV (vertexMk p) = baseVertex 𝔸 v :=
  vertexMk_congr (Path.Homotopic.reverse_comp p)

@[simp] theorem action_mk (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    action 𝔸 v₀ (π₁.mk γ) = changeBaseIso γ :=
  π₁.lift_mk _ _ γ

@[simp] theorem smul_vertexMk (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk γ • vertexMk p = vertexMk (γ.comp p) := by
  rw [GTree.smul_vertex_def]
  exact congrArg (fun φ : (𝔸.bassSerreGraph v₀).Aut => φ.equivV (vertexMk p)) (action_mk γ)

@[simp] theorem smul_baseVertex (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    π₁.mk γ • baseVertex 𝔸 v₀ = vertexMk γ := by
  rw [baseVertex, smul_vertexMk, Quiver.Path.comp_nil]

@[simp] theorem smul_dartMk (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk γ • dartMk e p = dartMk e (γ.comp p) := by
  rw [GTree.smul_dart_def]
  exact congrArg (fun φ : (𝔸.bassSerreGraph v₀).Aut => φ.equivE (dartMk e p)) (action_mk γ)

@[simp] theorem smul_arrowMk (γ : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {a b : Γ.V} (f : a ⟶ b)
    (p : 𝔸.Path ⟨v₀⟩ ⟨a⟩) :
    π₁.mk γ • arrowMk f p = arrowMk f (γ.comp p) := by
  rcases f with ⟨e, rfl, rfl⟩
  exact smul_dartMk γ e p

/-- Projection to `Γ` is invariant under the `π₁(𝔸, v₀)`-action on vertices. -/
@[simp] theorem projHom_mapV_smul (g : π₁ 𝔸 v₀) (x : (𝔸.bassSerreTree v₀).V) :
    (projHom 𝔸 v₀).mapV (g • x) = (projHom 𝔸 v₀).mapV x :=
  π₁.induction_on g fun γ => vertex_induction_on x fun p => by
    rw [smul_vertexMk, projHom_mapV_vertexMk, projHom_mapV_vertexMk]

/-- Projection to `Γ` is invariant under the `π₁(𝔸, v₀)`-action on darts. -/
@[simp] theorem projHom_mapE_smul (g : π₁ 𝔸 v₀) (δ : (𝔸.bassSerreTree v₀).E) :
    (projHom 𝔸 v₀).mapE (g • δ) = (projHom 𝔸 v₀).mapE δ :=
  π₁.induction_on g fun γ => dart_induction_on δ fun e p => by
    rw [smul_dartMk, projHom_mapE_dartMk, projHom_mapE_dartMk]

/-- Projection to `Γ.component v₀` is invariant under the `π₁(𝔸, v₀)`-action. -/
@[simp] theorem projComponentHom_comp_action (g : π₁ 𝔸 v₀) :
    (projComponentHom 𝔸 v₀).comp ((𝔸.bassSerreTree v₀).action g).toHom = projComponentHom 𝔸 v₀ :=
  π₁.induction_on g fun γ => by
    ext x
    · exact vertex_induction_on x fun p => Subtype.ext (by
        rw [SerreGraph.Hom.comp_mapV, Function.comp_apply, SerreGraph.Iso.toHom_mapV]
        exact congrArg
          (fun φ : (𝔸.bassSerreGraph v₀).Aut =>
            ((projComponentHom 𝔸 v₀).mapV (φ.equivV (vertexMk p))).1) (action_mk γ))
    · exact dart_induction_on x fun e p => Subtype.ext (by
        rw [SerreGraph.Hom.comp_mapE, Function.comp_apply, SerreGraph.Iso.toHom_mapE]
        exact congrArg
          (fun φ : (𝔸.bassSerreGraph v₀).Aut =>
            ((projComponentHom 𝔸 v₀).mapE (φ.equivE (dartMk e p))).1) (action_mk γ))

/-- Change of basepoint along `q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩` is semilinear on vertices with respect to
`π₁.mulEquivOfPath q.reverse : π₁(𝔸, v₀) ≃* π₁(𝔸, v₁)`. -/
theorem changeBaseIso_smul_vertex (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) (g : π₁ 𝔸 v₀)
    (x : (𝔸.bassSerreTree v₀).V) :
    (changeBaseIso q).equivV (g • x) =
      π₁.mulEquivOfPath q.reverse g • (changeBaseIso q).equivV x :=
  π₁.induction_on g fun γ => vertex_induction_on x fun p => by
    simp only [smul_vertexMk, changeBaseIso_equivV_vertexMk, π₁.mulEquivOfPath_mk,
      Quiver.Path.reverse_reverse, ← Quiver.Path.comp_assoc q γ p]
    exact vertexMk_congr (Path.Homotopic.comp_reverse_comp_comp (q.comp γ) q p).symm

/-- Change of basepoint along `q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩` is semilinear on darts with respect to
`π₁.mulEquivOfPath q.reverse : π₁(𝔸, v₀) ≃* π₁(𝔸, v₁)`. -/
theorem changeBaseIso_smul_dart (q : 𝔸.Path ⟨v₁⟩ ⟨v₀⟩) (g : π₁ 𝔸 v₀)
    (δ : (𝔸.bassSerreTree v₀).E) :
    (changeBaseIso q).equivE (g • δ) =
      π₁.mulEquivOfPath q.reverse g • (changeBaseIso q).equivE δ :=
  π₁.induction_on g fun γ => dart_induction_on δ fun e p => by
    simp only [smul_dartMk, changeBaseIso_equivE_dartMk, π₁.mulEquivOfPath_mk,
      Quiver.Path.reverse_reverse, ← Quiver.Path.comp_assoc q γ p]
    exact dartMk_congr e (Path.Homotopic.comp_reverse_comp_comp (q.comp γ) q p).symm

end BassSerreTree

end API

end GraphOfGroups
end TauCeti
