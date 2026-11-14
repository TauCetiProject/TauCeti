/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Component
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm

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

Stabilizers and the quotient graph isomorphism are established in
`TauCeti.GroupTheory.GraphOfGroups.BassSerre.Stabilizer`, local stars and vertex degrees in
`TauCeti.GroupTheory.GraphOfGroups.BassSerre.Star`, and canonical examples in
`TauCeti.GroupTheory.GraphOfGroups.BassSerre.Examples`.

## Main definitions

* `TauCeti.GraphOfGroups.BassSerreVertex`, `TauCeti.GraphOfGroups.BassSerreDart`: vertex and dart
  types of the Bass–Serre tree.
* `TauCeti.GraphOfGroups.bassSerreGraph`: the underlying `SerreGraph` of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTypeHom`, `TauCeti.GraphOfGroups.bassSerreComponentHom`:
  `π₁(𝔸, v₀)`-invariant projections from `X(𝔸, v₀)` to `Γ` and `Γ.component v₀`.
* `TauCeti.GraphOfGroups.bassSerreAction`: the left action of `π₁(𝔸, v₀)` by graph automorphisms.
* `TauCeti.GraphOfGroups.bassSerreTree`: `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreBaseVertex`,
  `TauCeti.GraphOfGroups.bassSerreDart`: path constructors for vertices and darts of
  `𝔸.bassSerreTree v₀`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreGraph_connected`: `X(𝔸, v₀)` is connected.
* `TauCeti.GraphOfGroups.bassSerreGraph_isAcyclic`: `X(𝔸, v₀)` is acyclic.
* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `X(𝔸, v₀)` is a tree.
* `TauCeti.GraphOfGroups.bassSerreVertex_eq_iff_setLast_eq`: normal-form criterion for equality of
  vertices in `X(𝔸, v₀)`.

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

/-- `X(𝔸, v₀)` is acyclic: a nonempty reduced closed path would lift to a reduced closed
alternating `𝔸`-path containing a dart and homotopic to a vertex group letter, contradicting
Britton's lemma. -/
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
@[expose] def bassSerreBaseVertex : (𝔸.bassSerreTree v₀).V :=
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

@[simp] theorem bassSerreComponentHom_mapV {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    ((𝔸.bassSerreComponentHom v₀).mapV (𝔸.bassSerreVertex v₀ p)).1 = v :=
  (rfl)

@[simp] theorem bassSerreComponentHom_mapE (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ((𝔸.bassSerreComponentHom v₀).mapE (𝔸.bassSerreDart v₀ e p)).1 = e :=
  (rfl)

@[simp] theorem mk_smul_bassSerreVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • 𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ (s.comp p) :=
  𝔸.smulVertex_mk v₀ s p

@[simp] theorem mk_smul_bassSerreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk s • 𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e (s.comp p) :=
  𝔸.smulDart_mk v₀ s e p

end TreeAPI

end GraphOfGroups

end TauCeti
