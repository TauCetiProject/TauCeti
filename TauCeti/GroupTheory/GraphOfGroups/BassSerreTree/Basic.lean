/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.OfParent
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# The Bass–Serre tree of a graph of groups: construction and `GTree` structure

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `v₀` of `Γ`, the Bass–Serre
covering tree `X(𝔸, v₀)` (`GraphOfGroups.bassSerreTree`) is constructed directly from `𝔸`-paths
starting at `v₀`:

* its vertices (`vertexMk p`) are classes `p A_v` of `𝔸`-paths `p` from `v₀` to `v`, where two
  paths `p, q` to `v` represent the same vertex when `p` is homotopic to `q a` for some `a ∈ A_v`;
* its darts (`dartMk e p`) are classes `p α_e(A_e)` of pairs of a dart `e` of `Γ` and an `𝔸`-path
  `p` from `v₀` to `src e`, joining `p A_{src e}` to `(p e) A_{tgt e}` with reverse `(p e, rev e)`;
* the fundamental group `π₁(𝔸, v₀)` acts on `X(𝔸, v₀)` on the left by path concatenation, without
  inversions because the underlying dart of `Γ` is preserved while `Γ.rev` has no fixed points.

Connectedness of `X(𝔸, v₀)` follows by induction along `𝔸`-paths from `v₀`. Absence of reduced
circuits follows from the normal form theorem (`GraphOfGroups.normalForm_eq_normalForm_iff`): fixing
a left transversal `d`, each vertex `p A_v` has a canonical normal-word representative ending in
`1`, and comparing normal-word dart lengths embeds `X(𝔸, v₀)` injectively on darts into the acyclic
graph of a parent map (`SerreGraph.ofParent`).

Vertex and edge stabilizers, the quotient graph `X(𝔸, v₀) / π₁(𝔸, v₀) ≅ Γ.component v₀`, outgoing
star coset bijections, and the edgeless boundary case are proved in
`TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Stabilizers`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreGraph`: the underlying Serre graph of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTree`: `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.vertexMk`, `TauCeti.GraphOfGroups.baseVertex`,
  `TauCeti.GraphOfGroups.dartMk`: constructors for vertices and darts of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreProj`: the `π₁(𝔸, v₀)`-invariant graph morphism `X(𝔸, v₀) → Γ`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_isTree`: `X(𝔸, v₀)` is a tree.
* `TauCeti.GraphOfGroups.bassSerreAction_smul_ne_rev`: the action of `π₁(𝔸, v₀)` has no inversions.
* `TauCeti.GraphOfGroups.vertexMk_eq_vertexMk_iff`,
  `TauCeti.GraphOfGroups.dartMk_eq_dartMk_iff`: characterizations of vertex and dart equality.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

/-! ### Path homotopy cancellation -/

namespace Path.Homotopic

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ}
  {x y z : 𝔸.LetterVertex}

/-- Left concatenation with a fixed `𝔸`-path preserves and reflects homotopy. -/
@[simp] theorem comp_left_iff {p : 𝔸.Path x y} {q r : 𝔸.Path y z} :
    Path.Homotopic (p.comp q) (p.comp r) ↔ Path.Homotopic q r := by
  refine ⟨fun h => ?_, fun h => h.comp_left p⟩
  have h₁ := ((reverse_comp p).comp_right q).symm
  have h₂ := (reverse_comp p).comp_right r
  rw [Quiver.Path.nil_comp, Quiver.Path.comp_assoc] at h₁ h₂
  exact (h₁.trans (h.comp_left p.reverse)).trans h₂

/-- Right concatenation with a fixed `𝔸`-path preserves and reflects homotopy. -/
@[simp] theorem comp_right_iff {p q : 𝔸.Path x y} {r : 𝔸.Path y z} :
    Path.Homotopic (p.comp r) (q.comp r) ↔ Path.Homotopic p q := by
  refine ⟨fun h => ?_, fun h => h.comp_right r⟩
  have h₁ := (comp_comp_reverse p r).symm
  have h₂ := comp_comp_reverse q r
  exact (h₁.trans (h.comp_right r.reverse)).trans h₂

/-- Appending `g` and then `g⁻¹` to an `𝔸`-path is homotopic to the original path. -/
theorem comp_ofVertex_inv_cancel {a : Γ.V} (p : 𝔸.Path x ⟨a⟩) (g : 𝔸.vertexGroup a) :
    Path.Homotopic ((p.comp (Path.ofVertex g)).comp (Path.ofVertex g⁻¹)) p := by
  rw [Path.comp_ofVertex, Path.comp_ofVertex]
  exact (Path.Homotopic.mul p g g⁻¹).trans (by rw [mul_inv_cancel]; exact .one p)

end Path.Homotopic

/-! ### Vertex and dart quotients -/

section Graph

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Equivalence of based `𝔸`-paths defining the vertices of `X(𝔸, v₀)`: `(v₁, p₁)` and `(v₂, p₂)`
are equivalent when `v₁ = v₂` and `p₁` is homotopic to `p₂ a` for some `a ∈ A_{v₂}`. -/
def VertexRel : (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) → (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) → Prop
  | ⟨v₁, p₁⟩, ⟨v₂, p₂⟩ =>
    ∃ h : v₁ = v₂, ∃ a : 𝔸.vertexGroup v₂,
      Path.Homotopic (p₁.cast rfl (congrArg LetterVertex.mk h)) (p₂.comp (Path.ofVertex a))

private theorem vertexRel_refl : ∀ x, VertexRel 𝔸 v₀ x x
  | ⟨_, p⟩ => ⟨rfl, 1, by
      rw [Quiver.Path.cast_rfl_rfl, Path.comp_ofVertex]
      exact (Path.Homotopic.one p).symm⟩

private theorem vertexRel_symm : ∀ {x y}, VertexRel 𝔸 v₀ x y → VertexRel 𝔸 v₀ y x
  | ⟨_, _⟩, ⟨_, p₂⟩, ⟨rfl, a, ha⟩ => by
      rw [Quiver.Path.cast_rfl_rfl] at ha
      exact ⟨rfl, a⁻¹, (Path.Homotopic.comp_ofVertex_inv_cancel p₂ a).symm.trans
        (ha.symm.comp_right (Path.ofVertex a⁻¹))⟩

private theorem vertexRel_trans :
    ∀ {x y z}, VertexRel 𝔸 v₀ x y → VertexRel 𝔸 v₀ y z → VertexRel 𝔸 v₀ x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, p₃⟩, ⟨rfl, a, ha⟩, ⟨rfl, b, hb⟩ => by
      rw [Quiver.Path.cast_rfl_rfl] at ha hb
      refine ⟨rfl, b * a, ?_⟩
      rw [Quiver.Path.cast_rfl_rfl, Path.comp_ofVertex]
      exact (ha.trans (hb.comp_right (Path.ofVertex a))).trans
        (by simpa [Path.comp_ofVertex] using Path.Homotopic.mul p₃ b a)

/-- Setoid of based `𝔸`-paths modulo right multiplication by the terminal vertex group. -/
def vertexSetoid : Setoid (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) where
  r := VertexRel 𝔸 v₀
  iseqv := ⟨vertexRel_refl 𝔸 v₀, vertexRel_symm 𝔸 v₀, vertexRel_trans 𝔸 v₀⟩

/-- Equivalence of dart-path pairs defining the darts of `X(𝔸, v₀)`: `(e₁, p₁)` and `(e₂, p₂)` are
equivalent when `e₁ = e₂` and `p₁` is homotopic to `p₂ α_e(c)` for some `c ∈ A_e`. -/
def DartRel :
    (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) → (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) → Prop
  | ⟨e₁, p₁⟩, ⟨e₂, p₂⟩ =>
    ∃ h : e₁ = e₂, ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e₂),
      Path.Homotopic (p₁.cast rfl (congrArg (fun e => LetterVertex.mk (Γ.src e)) h))
        (p₂.comp (Path.ofVertex (𝔸.α e₂ c)))

private theorem dartRel_refl : ∀ x, DartRel 𝔸 v₀ x x
  | ⟨_, p⟩ => ⟨rfl, 1, by
      rw [Quiver.Path.cast_rfl_rfl, map_one, Path.comp_ofVertex]
      exact (Path.Homotopic.one p).symm⟩

private theorem dartRel_symm : ∀ {x y}, DartRel 𝔸 v₀ x y → DartRel 𝔸 v₀ y x
  | ⟨e₁, _⟩, ⟨_, p₂⟩, ⟨rfl, c, hc⟩ => by
      rw [Quiver.Path.cast_rfl_rfl] at hc
      refine ⟨rfl, c⁻¹, ?_⟩
      rw [Quiver.Path.cast_rfl_rfl, map_inv]
      exact (Path.Homotopic.comp_ofVertex_inv_cancel p₂ (𝔸.α e₁ c)).symm.trans
        (hc.symm.comp_right (Path.ofVertex (𝔸.α e₁ c)⁻¹))

private theorem dartRel_trans :
    ∀ {x y z}, DartRel 𝔸 v₀ x y → DartRel 𝔸 v₀ y z → DartRel 𝔸 v₀ x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, p₃⟩, ⟨rfl, c₁, hc₁⟩, ⟨rfl, c₂, hc₂⟩ => by
      rw [Quiver.Path.cast_rfl_rfl] at hc₁ hc₂
      refine ⟨rfl, c₂ * c₁, ?_⟩
      rw [Quiver.Path.cast_rfl_rfl, map_mul, Path.comp_ofVertex]
      exact (hc₁.trans (hc₂.comp_right _)).trans
        (by simpa [Path.comp_ofVertex] using Path.Homotopic.mul p₃ _ _)

/-- Setoid of dart-path pairs modulo right multiplication by the boundary image `α_e(A_e)`. -/
def dartSetoid : Setoid (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) where
  r := DartRel 𝔸 v₀
  iseqv := ⟨dartRel_refl 𝔸 v₀, dartRel_symm 𝔸 v₀, dartRel_trans 𝔸 v₀⟩

private def rawRev : (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) → Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩
  | ⟨e, p⟩ => ⟨Γ.rev e, p.cons (Letter.dart (Γ.dart e))⟩

private theorem dartRel_rawRev :
    ∀ {x y}, DartRel 𝔸 v₀ x y → DartRel 𝔸 v₀ (rawRev 𝔸 v₀ x) (rawRev 𝔸 v₀ y)
  | ⟨e₁, p₁⟩, ⟨_, p₂⟩, ⟨rfl, c, hc⟩ => by
      rw [Quiver.Path.cast_rfl_rfl, Path.comp_ofVertex] at hc
      refine ⟨rfl, (MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e₁)).symm c, ?_⟩
      have hlhs : (rawRev 𝔸 v₀ ⟨e₁, p₁⟩).2.cast rfl rfl = p₁.cons (Letter.dart (Γ.dart e₁)) := rfl
      have hrhs : (rawRev 𝔸 v₀ ⟨e₁, p₂⟩).2.comp
          (Path.ofVertex (𝔸.α (Γ.rev e₁)
            ((MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e₁)).symm c))) =
          (p₂.cons (Letter.dart (Γ.dart e₁))).cons (Letter.vertex (𝔸.ω e₁ c)) := by
        dsimp only [rawRev]
        rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
        exact Path.comp_ofVertex (p₂.cons (Letter.dart (Γ.dart e₁))) (𝔸.ω e₁ c)
      exact hlhs.symm ▸ hrhs.symm ▸
        ((hc.cons (Letter.dart (Γ.dart e₁))).trans (Path.Homotopic.dart_ω e₁ c p₂).symm)

private theorem cast_cons_dart_homotopic {v w u : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (e₁ : v ⟶ w)
    (e₂ : w ⟶ u) (hu : u = v) (hrev : e₂.1 = Γ.rev e₁.1) :
    Path.Homotopic
      (((p.cons (Letter.dart e₁)).cons (Letter.dart e₂)).cast rfl (congrArg LetterVertex.mk hu))
      p := by
  subst hu
  rw [Quiver.Path.cast_rfl_rfl, Γ.eq_reverse_of_val_eq_rev hrev]
  exact Path.Homotopic.dart_reverse p e₁

private theorem dartRel_rawRev_rawRev :
    ∀ x, DartRel 𝔸 v₀ (rawRev 𝔸 v₀ (rawRev 𝔸 v₀ x)) x
  | ⟨e, p⟩ => by
      refine ⟨Γ.rev_rev e, 1, ?_⟩
      rw [map_one, Path.comp_ofVertex]
      exact (cast_cons_dart_homotopic 𝔸 v₀ p (Γ.dart e) (Γ.dart (Γ.rev e))
        (congrArg Γ.src (Γ.rev_rev e)) (by simp)).trans (Path.Homotopic.one p).symm

/-- The underlying Serre graph of the Bass–Serre tree `X(𝔸, v₀)`. -/
def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := Quotient (vertexSetoid 𝔸 v₀)
  E := Quotient (dartSetoid 𝔸 v₀)
  src := Quotient.map (fun x => ⟨Γ.src x.1, x.2⟩) fun ⟨_, _⟩ ⟨_, _⟩ ⟨h, c, hc⟩ =>
    ⟨congrArg Γ.src h, 𝔸.α _ c, hc⟩
  rev := Quotient.map (rawRev 𝔸 v₀) fun _ _ h => dartRel_rawRev 𝔸 v₀ h
  rev_rev := Quotient.ind fun x => Quotient.sound (dartRel_rawRev_rawRev 𝔸 v₀ x)
  rev_ne := Quotient.ind fun ⟨e, _⟩ h => Γ.rev_ne e (Quotient.exact h).1

/-- Projection of `bassSerreGraph 𝔸 v₀` onto `Γ`, sending `p A_v` to `v` and `(e, p)` to `e`. -/
def bassSerreGraphProj : (bassSerreGraph 𝔸 v₀).Hom Γ where
  mapV := Quotient.lift Sigma.fst fun ⟨_, _⟩ ⟨_, _⟩ h => h.1
  mapE := Quotient.lift Sigma.fst fun ⟨_, _⟩ ⟨_, _⟩ h => h.1
  map_src := Quotient.ind fun ⟨_, _⟩ => rfl
  map_rev := Quotient.ind fun ⟨_, _⟩ => rfl

end Graph

/-! ### Internal constructors on `bassSerreGraph` and tree property -/

section IsTree

namespace AlternatingPath

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

/-- Number of darts in an alternating `𝔸`-path. -/
def dartLength : ∀ {b : Γ.V}, 𝔸.AlternatingPath a b → ℕ
  | _, .single _ => 0
  | _, .cons p _ _ => p.dartLength + 1

@[simp] theorem dartLength_single (g : 𝔸.vertexGroup a) :
    (single g : 𝔸.AlternatingPath a a).dartLength = 0 := (rfl)

@[simp] theorem dartLength_cons {b c : Γ.V} (p : 𝔸.AlternatingPath a b) (e : b ⟶ c)
    (g : 𝔸.vertexGroup c) : (cons p e g).dartLength = p.dartLength + 1 := (rfl)

@[simp] theorem dartLength_setLast {b : Γ.V} (p : 𝔸.AlternatingPath a b) (g : 𝔸.vertexGroup b) :
    (p.setLast g).dartLength = p.dartLength := by
  cases p <;> simp

theorem dartLength_appendDart_of_not_cancels (d : 𝔸.Transversal) {b c : Γ.V}
    {p : 𝔸.AlternatingPath a b} {e : b ⟶ c} (h : ¬ p.Cancels e) :
    (p.appendDart d e).dartLength = p.dartLength + 1 := by
  rw [appendDart_of_not_cancels d h, dartLength_cons, dartLength_setLast]

theorem dartLength_eq_appendDart_add_one_of_cancels (d : 𝔸.Transversal) {b c : Γ.V}
    {p : 𝔸.AlternatingPath a b} {e : b ⟶ c} (h : p.Cancels e) :
    p.dartLength = (p.appendDart d e).dartLength + 1 := by
  obtain ⟨q, c₀, rfl⟩ := cancels_iff.1 h
  rw [appendDart_cons_of_eq d q rfl rfl, dartLength_setLast, dartLength_cons]

end AlternatingPath

section Acyclic

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

private def gVertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (bassSerreGraph 𝔸 v₀).V :=
  Quotient.mk (vertexSetoid 𝔸 v₀) ⟨v, p⟩

private def gDartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (bassSerreGraph 𝔸 v₀).E :=
  Quotient.mk (dartSetoid 𝔸 v₀) ⟨e, p⟩

@[elab_as_elim] private theorem gVertex_induction_on {P : (bassSerreGraph 𝔸 v₀).V → Prop}
    (x : (bassSerreGraph 𝔸 v₀).V) (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (gVertexMk p)) : P x :=
  Quotient.inductionOn x fun ⟨_, p⟩ => h p

@[elab_as_elim] private theorem gDart_induction_on {P : (bassSerreGraph 𝔸 v₀).E → Prop}
    (y : (bassSerreGraph 𝔸 v₀).E) (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (gDartMk e p)) :
    P y :=
  Quotient.inductionOn y fun ⟨e, p⟩ => h e p

private theorem gSrc_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreGraph 𝔸 v₀).src (gDartMk e p) = gVertexMk p := (rfl)

private theorem gRev_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreGraph 𝔸 v₀).rev (gDartMk e p) =
      gDartMk (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) := (rfl)

private theorem gTgt_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreGraph 𝔸 v₀).tgt (gDartMk e p) =
      gVertexMk (p.cons (Letter.dart (Γ.dart e))) := (rfl)

private theorem gVertexMk_eq_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    gVertexMk p = gVertexMk q ↔
      ∃ a : 𝔸.vertexGroup v, Path.Homotopic p (q.comp (Path.ofVertex a)) :=
  Quotient.eq.trans
    ⟨fun ⟨_, a, ha⟩ => ⟨a, by rwa [Quiver.Path.cast_rfl_rfl] at ha⟩,
      fun ⟨a, ha⟩ => ⟨rfl, a, by rwa [Quiver.Path.cast_rfl_rfl]⟩⟩

private theorem gDartMk_eq_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    gDartMk e p = gDartMk e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), Path.Homotopic p (q.comp (Path.ofVertex (𝔸.α e c))) :=
  Quotient.eq.trans
    ⟨fun ⟨_, c, hc⟩ => ⟨c, by rwa [Quiver.Path.cast_rfl_rfl] at hc⟩,
      fun ⟨c, hc⟩ => ⟨rfl, c, by rwa [Quiver.Path.cast_rfl_rfl]⟩⟩

private theorem gVertexMk_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    gVertexMk (p.cons (Letter.vertex a)) = gVertexMk p :=
  gVertexMk_eq_iff.mpr ⟨a, by rw [Path.comp_ofVertex]; exact .refl _⟩

private theorem bassSerreGraph_connected : (bassSerreGraph 𝔸 v₀).Connected := by
  let x₀ : (bassSerreGraph 𝔸 v₀).V := gVertexMk (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
  have key : ∀ (z : 𝔸.LetterVertex) (p : 𝔸.Path ⟨v₀⟩ z),
      Nonempty ((bassSerreGraph 𝔸 v₀).Path x₀ (gVertexMk (v := z.as) p)) := by
    intro z p
    induction p with
    | nil => exact ⟨.nil⟩
    | cons p l ih =>
      cases l with
      | vertex g =>
        rw [gVertexMk_cons_vertex]
        exact ih
      | dart e =>
        obtain ⟨e, rfl, rfl⟩ := e
        rw [← Γ.dart_def, ← gTgt_dartMk]
        exact ih.map fun q => q.cons ((bassSerreGraph 𝔸 v₀).dart (gDartMk e p))
  refine (bassSerreGraph 𝔸 v₀).connected_iff.mpr
    ⟨⟨x₀⟩, (bassSerreGraph 𝔸 v₀).preconnected_of_forall_nonempty_path x₀ ?_⟩
  exact fun x => gVertex_induction_on x fun {v} p => key ⟨v⟩ p

/-- Canonical normal-word representative of a vertex of `X(𝔸, v₀)` for a transversal `d`, obtained
by clearing the terminal vertex-group element to `1`. -/
private noncomputable def canonicalWord (d : 𝔸.Transversal) :
    (bassSerreGraph 𝔸 v₀).V → Σ v : Γ.V, NormalWord d v₀ v :=
  Quotient.lift (fun x => ⟨x.1, (normalForm d x.2).mulLast (normalForm d x.2).1.last⁻¹⟩)
    fun ⟨_, p₁⟩ ⟨_, p₂⟩ h => by
      obtain ⟨rfl, a, ha⟩ := h
      rw [Quiver.Path.cast_rfl_rfl] at ha
      have hnf : normalForm d p₁ = (normalForm d p₂).mulLast a := by
        simpa using normalForm_eq_of_homotopic d ha
      refine Sigma.ext rfl (heq_of_eq ?_)
      rw [hnf]
      ext1
      simp

private theorem canonicalWord_vertexMk (d : 𝔸.Transversal) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    canonicalWord d (gVertexMk p) =
      ⟨v, (normalForm d p).mulLast (normalForm d p).1.last⁻¹⟩ := (rfl)

private def dartLengthSigma {d : 𝔸.Transversal} : (Σ v : Γ.V, NormalWord d v₀ v) → ℕ
  | ⟨_, w⟩ => w.1.dartLength

private noncomputable def vertexDartLength (d : 𝔸.Transversal) (x : (bassSerreGraph 𝔸 v₀).V) : ℕ :=
  dartLengthSigma (canonicalWord d x)

private theorem vertexDartLength_vertexMk (d : 𝔸.Transversal) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    vertexDartLength d (gVertexMk p) = (normalForm d p).1.dartLength := by
  rw [vertexDartLength, canonicalWord_vertexMk]
  simp [dartLengthSigma]

private def bsParentAux {d : 𝔸.Transversal} :
    (Σ v : Γ.V, NormalWord d v₀ v) → (bassSerreGraph 𝔸 v₀).V ⊕ ℕ
  | ⟨_, ⟨.single _, _, _⟩⟩ => .inr 0
  | ⟨_, ⟨.cons q _ _, _, _⟩⟩ => .inl (gVertexMk q.toPath)

/-- Parent map on `(bassSerreGraph 𝔸 v₀).V ⊕ ℕ` stripping the last dart of the canonical normal
word and sending the base vertex into the ray `ℕ`. -/
private noncomputable def bsParent (v₀ : Γ.V) (d : 𝔸.Transversal) :
    (bassSerreGraph 𝔸 v₀).V ⊕ ℕ → (bassSerreGraph 𝔸 v₀).V ⊕ ℕ
  | .inr n => .inr (n + 1)
  | .inl x => bsParentAux (canonicalWord d x)

private noncomputable def bsHeight (v₀ : Γ.V) (d : 𝔸.Transversal) :
    (bassSerreGraph 𝔸 v₀).V ⊕ ℕ → ℤ
  | .inr n => n + 1
  | .inl x => -(vertexDartLength d x : ℤ)

private theorem bsHeight_bsParent (d : 𝔸.Transversal) (z : (bassSerreGraph 𝔸 v₀).V ⊕ ℕ) :
    bsHeight v₀ d (bsParent v₀ d z) = bsHeight v₀ d z + 1 := by
  cases z with
  | inr n =>
    simp only [bsParent, bsHeight]
    omega
  | inl x =>
    rw [bsParent]
    rcases hcw : canonicalWord d x with ⟨v, ⟨w, hr, hn⟩⟩
    cases w with
    | single g =>
      rw [bsHeight, vertexDartLength, hcw]
      simp [bsParentAux, bsHeight, dartLengthSigma]
    | cons q e g =>
      have hr' := ((AlternatingPath.isReduced_cons_iff q e g).mp hr).1
      have hn' := ((AlternatingPath.isNormalized_cons_iff d q e g).mp hn).1
      have hq : (normalForm d q.toPath).1 = q :=
        congrArg NormalWord.toAlternatingPath
          (by simpa [NormalWord.toPath_def] using normalForm_toPath d ⟨q, hr', hn'⟩)
      simp only [bsParentAux, bsHeight]
      rw [vertexDartLength_vertexMk, hq, vertexDartLength, hcw, dartLengthSigma,
        AlternatingPath.dartLength_cons]
      omega

private theorem bsParent_iterate_inj (d : 𝔸.Transversal) (z : (bassSerreGraph 𝔸 v₀).V ⊕ ℕ)
    (m n : ℕ) (h : (bsParent v₀ d)^[m] z = (bsParent v₀ d)^[n] z) : m = n := by
  have key : ∀ k, bsHeight v₀ d ((bsParent v₀ d)^[k] z) = bsHeight v₀ d z + k := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', bsHeight_bsParent, ih]
      omega
  have := congrArg (bsHeight v₀ d) h
  rw [key, key] at this
  omega

private theorem vertexDartLength_tgt_dartMk (d : 𝔸.Transversal) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt (gDartMk e p)) =
      ((normalForm d p).1.appendDart d (Γ.dart e)).dartLength := by
  rw [gTgt_dartMk, vertexDartLength_vertexMk, normalForm_cons, NormalWord.appendLetter_dart,
    NormalWord.toAlternatingPath_appendDart]

private theorem dartLength_src_tgt_step (d : 𝔸.Transversal) (y : (bassSerreGraph 𝔸 v₀).E) :
    vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) =
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) + 1 ∨
      vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) =
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) + 1 :=
  gDart_induction_on y fun e p => by
    rw [gSrc_dartMk, vertexDartLength_vertexMk, vertexDartLength_tgt_dartMk]
    by_cases hc : (normalForm d p).1.Cancels (Γ.dart e)
    · exact Or.inr ((normalForm d p).1.dartLength_eq_appendDart_add_one_of_cancels d hc)
    · exact Or.inl ((normalForm d p).1.dartLength_appendDart_of_not_cancels d hc)

private theorem bsParent_tgt_of_not_cancels (d : 𝔸.Transversal) {e : Γ.E}
    {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (hc : ¬ (normalForm d p).1.Cancels (Γ.dart e)) :
    bsParent v₀ d (.inl ((bassSerreGraph 𝔸 v₀).tgt (gDartMk e p))) =
      .inl ((bassSerreGraph 𝔸 v₀).src (gDartMk e p)) := by
  set u := normalForm d p
  let s := d.rep (Γ.dart e) u.1.last
  have hred : (AlternatingPath.cons (u.1.setLast s) (Γ.dart e) 1).IsReduced := by
    rw [AlternatingPath.isReduced_cons_iff, AlternatingPath.isReduced_setLast,
      AlternatingPath.cancels_setLast (d.rep_mem_range_iff _ _)]
    exact ⟨u.2, hc⟩
  have hnorm : (AlternatingPath.cons (u.1.setLast s) (Γ.dart e) 1).IsNormalized d := by
    rw [AlternatingPath.isNormalized_cons_iff, AlternatingPath.isNormalized_setLast,
      AlternatingPath.last_setLast]
    exact ⟨u.3, d.rep_mem (Γ.dart e) u.1.last⟩
  have hcw : canonicalWord d (gVertexMk (p.cons (Letter.dart (Γ.dart e)))) =
      ⟨Γ.tgt e, ⟨.cons (u.1.setLast s) (Γ.dart e) 1, hred, hnorm⟩⟩ := by
    rw [canonicalWord_vertexMk]
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext1
    simp [u, s, AlternatingPath.appendDart_of_not_cancels d hc]
  rw [gTgt_dartMk, gSrc_dartMk, bsParent, hcw]
  simp only [bsParentAux]
  congr 1
  refine gVertexMk_eq_iff.mpr ⟨u.1.last⁻¹ * s, ?_⟩
  have hset : u.1.setLast s = u.1.setLast (u.1.last * (u.1.last⁻¹ * s)) := by simp
  rw [hset, Path.comp_ofVertex]
  exact (u.1.toPath_setLast_mul_homotopic (u.1.last⁻¹ * s)).trans <| by
    rw [← NormalWord.toPath_def]
    exact (toPath_normalForm_homotopic d p).cons _

/-- Embedding of `bassSerreGraph 𝔸 v₀` into `ofParent (bsParent v₀ d)` orienting each dart by
whether normal-word dart length decreases or increases. -/
private noncomputable def toOfParent (v₀ : Γ.V) (d : 𝔸.Transversal) :
    (bassSerreGraph 𝔸 v₀).Hom (SerreGraph.ofParent (bsParent v₀ d)) where
  mapV := Sum.inl
  mapE y := by
    classical
    exact if vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) <
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) then
      (.inl ((bassSerreGraph 𝔸 v₀).src y), true)
    else
      (.inl ((bassSerreGraph 𝔸 v₀).tgt y), false)
  map_src y := by
    classical
    split_ifs with hlt
    · rfl
    · refine gDart_induction_on y (fun e p hlt' => ?_) hlt
      have hc : ¬ (normalForm d p).1.Cancels (Γ.dart e) := fun hc => hlt' <| by
        rw [vertexDartLength_tgt_dartMk, gSrc_dartMk, vertexDartLength_vertexMk,
          (normalForm d p).1.dartLength_eq_appendDart_add_one_of_cancels d hc]
        exact Nat.lt_succ_self _
      exact bsParent_tgt_of_not_cancels d hc
  map_rev y := by
    classical
    simp only [SerreGraph.src_rev, SerreGraph.tgt_rev, SerreGraph.ofParent_rev]
    rcases dartLength_src_tgt_step d y with hup | hdn
    · have h₁ : ¬ vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) <
          vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) := by omega
      have h₂ : vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) <
          vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) := by omega
      simp [h₁, h₂]
    · have h₁ : vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) <
          vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) := by omega
      have h₂ : ¬ vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y) <
          vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y) := by omega
      simp [h₁, h₂]

private theorem path_homotopic_setLast_rep_comp (d : 𝔸.Transversal) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    let f : Γ.src e ⟶ Γ.tgt e := ⟨e, rfl, rfl⟩
    Path.Homotopic p (((normalForm d p).1.setLast (d.rep f (normalForm d p).1.last)).toPath.comp
      (Path.ofVertex (𝔸.α e (d.edgePart f (normalForm d p).1.last)))) := by
  intro f
  have hmul := d.rep_mul_αArrow_edgePart f (normalForm d p).1.last
  rw [𝔸.αArrow_mk] at hmul
  refine (toPath_normalForm_homotopic d p).symm.trans ?_
  rw [NormalWord.toPath_def, Path.comp_ofVertex]
  simpa [hmul] using ((normalForm d p).1.setLast
    (d.rep f (normalForm d p).1.last)).toPath_setLast_mul_homotopic
      (𝔸.α e (d.edgePart f (normalForm d p).1.last))

private theorem normalForm_cons_mulLast_of_not_cancels (d : 𝔸.Transversal) {e : Γ.E}
    {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (hc : ¬ (normalForm d p).1.Cancels (Γ.dart e)) :
    ((normalForm d (p.cons (Letter.dart (Γ.dart e)))).mulLast
      (normalForm d (p.cons (Letter.dart (Γ.dart e)))).1.last⁻¹).1 =
      .cons ((normalForm d p).1.setLast (d.rep (Γ.dart e) (normalForm d p).1.last))
        (Γ.dart e) 1 := by
  simp [AlternatingPath.appendDart_of_not_cancels d hc]

private theorem up_dart_eq_of_tgt_eq (d : 𝔸.Transversal) {e₁ e₂ : Γ.E}
    {p₁ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₁⟩} {p₂ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₂⟩}
    (hc₁ : ¬ (normalForm d p₁).1.Cancels (Γ.dart e₁))
    (hc₂ : ¬ (normalForm d p₂).1.Cancels (Γ.dart e₂))
    (htgt : (bassSerreGraph 𝔸 v₀).tgt (gDartMk e₁ p₁) =
      (bassSerreGraph 𝔸 v₀).tgt (gDartMk e₂ p₂)) :
    gDartMk e₁ p₁ = gDartMk e₂ p₂ := by
  rw [gTgt_dartMk, gTgt_dartMk] at htgt
  have hcw := congrArg (canonicalWord d) htgt
  rw [canonicalWord_vertexMk, canonicalWord_vertexMk] at hcw
  have hfst : Γ.tgt e₁ = Γ.tgt e₂ := congrArg Sigma.fst hcw
  have hpath : HEq
      ((normalForm d (p₁.cons (Letter.dart (Γ.dart e₁)))).mulLast
        (normalForm d (p₁.cons (Letter.dart (Γ.dart e₁)))).1.last⁻¹).1
      ((normalForm d (p₂.cons (Letter.dart (Γ.dart e₂)))).mulLast
        (normalForm d (p₂.cons (Letter.dart (Γ.dart e₂)))).1.last⁻¹).1 :=
    congr_arg_heq (fun s : Σ v : Γ.V, NormalWord d v₀ v => s.2.1) hcw
  rw [normalForm_cons_mulLast_of_not_cancels d hc₁,
    normalForm_cons_mulLast_of_not_cancels d hc₂] at hpath
  have he : e₁ = e₂ := by
    have key : ∀ {b₁ c₁ b₂ c₂ : Γ.V} (q₁ : 𝔸.AlternatingPath v₀ b₁) (f₁ : b₁ ⟶ c₁)
        (g₁ : 𝔸.vertexGroup c₁) (q₂ : 𝔸.AlternatingPath v₀ b₂) (f₂ : b₂ ⟶ c₂)
        (g₂ : 𝔸.vertexGroup c₂), c₁ = c₂ →
        HEq (AlternatingPath.cons q₁ f₁ g₁) (AlternatingPath.cons q₂ f₂ g₂) → f₁.1 = f₂.1 := by
      rintro b₁ c₁ b₂ _ q₁ f₁ g₁ q₂ f₂ g₂ rfl h
      obtain ⟨rfl, -, rfl, -⟩ := AlternatingPath.cons.inj (eq_of_heq h)
      rfl
    simpa using key _ _ _ _ _ _ hfst hpath
  subst he
  obtain ⟨-, hpre, -, -⟩ := AlternatingPath.cons.inj (eq_of_heq hpath)
  let f : Γ.src e₁ ⟶ Γ.tgt e₁ := ⟨e₁, rfl, rfl⟩
  have hpre_eq : (normalForm d p₁).1.setLast (d.rep f (normalForm d p₁).1.last) =
      (normalForm d p₂).1.setLast (d.rep f (normalForm d p₂).1.last) := by
    simpa [f, ← Γ.dart_def] using eq_of_heq hpre
  set c₁ := d.edgePart f (normalForm d p₁).1.last
  set c₂ := d.edgePart f (normalForm d p₂).1.last
  refine gDartMk_eq_iff.mpr ⟨c₂⁻¹ * c₁, ?_⟩
  rw [map_mul, map_inv]
  refine (path_homotopic_setLast_rep_comp d e₁ p₁).trans ?_
  rw [hpre_eq]
  have h₂ := (path_homotopic_setLast_rep_comp d e₁ p₂).symm.comp_right
    (Path.ofVertex (𝔸.α e₁ c₂)⁻¹)
  have h₃ := (Path.Homotopic.comp_ofVertex_inv_cancel _ (𝔸.α e₁ c₂)).symm.trans h₂
  exact (h₃.comp_right (Path.ofVertex (𝔸.α e₁ c₁))).trans
    (by simpa [Path.comp_ofVertex] using Path.Homotopic.mul p₂ (𝔸.α e₁ c₂)⁻¹ (𝔸.α e₁ c₁))

private theorem eq_of_not_lt_of_tgt_eq (d : 𝔸.Transversal) {y₁ y₂ : (bassSerreGraph 𝔸 v₀).E}
    (h₁ : ¬ vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y₁) <
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y₁))
    (h₂ : ¬ vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y₂) <
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y₂))
    (htgt : (bassSerreGraph 𝔸 v₀).tgt y₁ = (bassSerreGraph 𝔸 v₀).tgt y₂) : y₁ = y₂ := by
  refine gDart_induction_on y₁ (fun e₁ p₁ h₁ htgt => ?_) h₁ htgt
  refine gDart_induction_on y₂ (fun e₂ p₂ h₂ htgt => ?_) h₂ htgt
  refine up_dart_eq_of_tgt_eq d (fun hc₁ => h₁ ?_) (fun hc₂ => h₂ ?_) htgt
  · rw [vertexDartLength_tgt_dartMk, gSrc_dartMk, vertexDartLength_vertexMk,
      (normalForm d p₁).1.dartLength_eq_appendDart_add_one_of_cancels d hc₁]
    exact Nat.lt_succ_self _
  · rw [vertexDartLength_tgt_dartMk, gSrc_dartMk, vertexDartLength_vertexMk,
      (normalForm d p₂).1.dartLength_eq_appendDart_add_one_of_cancels d hc₂]
    exact Nat.lt_succ_self _

private theorem toOfParent_mapE_injective (d : 𝔸.Transversal) :
    Function.Injective (toOfParent v₀ d).mapE := by
  classical
  intro y₁ y₂ h
  have hsnd : ((toOfParent v₀ d).mapE y₁).2 = ((toOfParent v₀ d).mapE y₂).2 :=
    congrArg Prod.snd h
  by_cases h₁ : vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y₁) <
      vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y₁)
  · have h₂ : vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y₂) <
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y₂) := by
      by_contra h₂
      simp [toOfParent, h₁, h₂] at hsnd
    -- Downward darts have the same source, so their reverses are upward darts with the same target.
    have hsrc : (bassSerreGraph 𝔸 v₀).src y₁ = (bassSerreGraph 𝔸 v₀).src y₂ := by
      simpa [toOfParent, h₁, h₂] using congrArg Prod.fst h
    exact (bassSerreGraph 𝔸 v₀).rev_injective (eq_of_not_lt_of_tgt_eq d
      (by simpa using Nat.not_lt.mpr h₁.le) (by simpa using Nat.not_lt.mpr h₂.le)
      (by simpa using hsrc))
  · have h₂ : ¬ vertexDartLength d ((bassSerreGraph 𝔸 v₀).tgt y₂) <
        vertexDartLength d ((bassSerreGraph 𝔸 v₀).src y₂) := by
      intro h₂
      simp [toOfParent, h₁, h₂] at hsnd
    have htgt : (bassSerreGraph 𝔸 v₀).tgt y₁ = (bassSerreGraph 𝔸 v₀).tgt y₂ := by
      simpa [toOfParent, h₁, h₂] using congrArg Prod.fst h
    exact eq_of_not_lt_of_tgt_eq d h₁ h₂ htgt

private theorem bassSerreGraph_isAcyclic : (bassSerreGraph 𝔸 v₀).IsAcyclic := by
  let d : 𝔸.Transversal := default
  have hacyc : (SerreGraph.ofParent (bsParent (𝔸 := 𝔸) v₀ d)).IsAcyclic :=
    SerreGraph.ofParent_isAcyclic (bsParent v₀ d) (bsParent_iterate_inj d)
  refine (bassSerreGraph 𝔸 v₀).isAcyclic_iff.mpr fun u p hp => ?_
  have hp' := (SerreGraph.Hom.isReduced_mapPath_iff (bassSerreGraph 𝔸 v₀) (toOfParent v₀ d)
    (toOfParent_mapE_injective d) p).mpr hp
  have hnil := (SerreGraph.isAcyclic_iff _).mp hacyc _ _ hp'
  exact Quiver.Path.eq_nil_of_length_zero p
    ((Prefunctor.length_mapPath (toOfParent v₀ d).toPrefunctor p).symm.trans
      (congrArg Quiver.Path.length hnil))

end Acyclic

/-- The Bass–Serre graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)
    (v₀ : Γ.V) : (bassSerreGraph 𝔸 v₀).IsTree :=
  (bassSerreGraph 𝔸 v₀).isTree_iff.mpr ⟨bassSerreGraph_connected, bassSerreGraph_isAcyclic⟩

end IsTree

/-! ### Action of `π₁(𝔸, v₀)` and the `GTree` structure -/

section Action

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

private def smulVAux (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (bassSerreGraph 𝔸 v₀).V → (bassSerreGraph 𝔸 v₀).V :=
  Quotient.map (fun x => ⟨x.1, s.comp x.2⟩) fun ⟨_, p₁⟩ ⟨_, p₂⟩ h => by
    obtain ⟨rfl, a, ha⟩ := h
    rw [Quiver.Path.cast_rfl_rfl] at ha
    exact ⟨rfl, a, by
      rw [Quiver.Path.cast_rfl_rfl, Quiver.Path.comp_assoc]
      exact ha.comp_left s⟩

private def smulEAux (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    (bassSerreGraph 𝔸 v₀).E → (bassSerreGraph 𝔸 v₀).E :=
  Quotient.map (fun x => ⟨x.1, s.comp x.2⟩) fun ⟨_, p₁⟩ ⟨_, p₂⟩ h => by
    obtain ⟨rfl, c, hc⟩ := h
    rw [Quiver.Path.cast_rfl_rfl] at hc
    exact ⟨rfl, c, by
      rw [Quiver.Path.cast_rfl_rfl, Quiver.Path.comp_assoc]
      exact hc.comp_left s⟩

private def smulV : π₁ 𝔸 v₀ → (bassSerreGraph 𝔸 v₀).V → (bassSerreGraph 𝔸 v₀).V :=
  π₁.lift (smulVAux 𝔸 v₀) fun _ s₂ hs => funext fun x =>
    gVertex_induction_on x fun p => gVertexMk_eq_iff.mpr
      ⟨1, by rw [Path.comp_ofVertex]; exact (hs.comp_right p).trans (Path.Homotopic.one _).symm⟩

private def smulE : π₁ 𝔸 v₀ → (bassSerreGraph 𝔸 v₀).E → (bassSerreGraph 𝔸 v₀).E :=
  π₁.lift (smulEAux 𝔸 v₀) fun _ s₂ hs => funext fun y =>
    gDart_induction_on y fun _ p => gDartMk_eq_iff.mpr ⟨1, by
      rw [map_one, Path.comp_ofVertex]
      exact (hs.comp_right p).trans (Path.Homotopic.one (s₂.comp p)).symm⟩

private theorem smulV_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    smulV 𝔸 v₀ (π₁.mk s) (gVertexMk p) = gVertexMk (s.comp p) := by
  rw [smulV, π₁.lift_mk]
  rfl

private theorem smulE_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    smulE 𝔸 v₀ (π₁.mk s) (gDartMk e p) = gDartMk e (s.comp p) := by
  rw [smulE, π₁.lift_mk]
  rfl

private theorem one_smulV (x : (bassSerreGraph 𝔸 v₀).V) : smulV 𝔸 v₀ 1 x = x :=
  gVertex_induction_on x fun p => by
    rw [← π₁.mk_nil, smulV_mk, Quiver.Path.nil_comp]

private theorem mul_smulV (g h : π₁ 𝔸 v₀) (x : (bassSerreGraph 𝔸 v₀).V) :
    smulV 𝔸 v₀ (g * h) x = smulV 𝔸 v₀ g (smulV 𝔸 v₀ h x) :=
  π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    gVertex_induction_on x fun p => by
      rw [← π₁.mk_comp, smulV_mk, smulV_mk, smulV_mk, Quiver.Path.comp_assoc]

private theorem one_smulE (y : (bassSerreGraph 𝔸 v₀).E) : smulE 𝔸 v₀ 1 y = y :=
  gDart_induction_on y fun e p => by
    rw [← π₁.mk_nil, smulE_mk, Quiver.Path.nil_comp]

private theorem mul_smulE (g h : π₁ 𝔸 v₀) (y : (bassSerreGraph 𝔸 v₀).E) :
    smulE 𝔸 v₀ (g * h) y = smulE 𝔸 v₀ g (smulE 𝔸 v₀ h y) :=
  π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    gDart_induction_on y fun e p => by
      rw [← π₁.mk_comp, smulE_mk, smulE_mk, smulE_mk, Quiver.Path.comp_assoc]

private theorem map_src_smulE (g : π₁ 𝔸 v₀) (y : (bassSerreGraph 𝔸 v₀).E) :
    (bassSerreGraph 𝔸 v₀).src (smulE 𝔸 v₀ g y) = smulV 𝔸 v₀ g ((bassSerreGraph 𝔸 v₀).src y) :=
  π₁.induction_on g fun s => gDart_induction_on y fun e p => by
    rw [smulE_mk, gSrc_dartMk, gSrc_dartMk, smulV_mk]

private theorem map_rev_smulE (g : π₁ 𝔸 v₀) (y : (bassSerreGraph 𝔸 v₀).E) :
    smulE 𝔸 v₀ g ((bassSerreGraph 𝔸 v₀).rev y) = (bassSerreGraph 𝔸 v₀).rev (smulE 𝔸 v₀ g y) :=
  π₁.induction_on g fun s => gDart_induction_on y fun e p => by
    rw [gRev_dartMk, smulE_mk, smulE_mk, gRev_dartMk]
    rfl

/-- Left concatenation action of `π₁(𝔸, v₀)` on `bassSerreGraph 𝔸 v₀` by graph automorphisms. -/
def bassSerreAction : π₁ 𝔸 v₀ →* (bassSerreGraph 𝔸 v₀).Aut where
  toFun g :=
    { equivV :=
        { toFun := smulV 𝔸 v₀ g
          invFun := smulV 𝔸 v₀ g⁻¹
          left_inv := fun x => by rw [← mul_smulV, inv_mul_cancel, one_smulV]
          right_inv := fun x => by rw [← mul_smulV, mul_inv_cancel, one_smulV] }
      equivE :=
        { toFun := smulE 𝔸 v₀ g
          invFun := smulE 𝔸 v₀ g⁻¹
          left_inv := fun y => by rw [← mul_smulE, inv_mul_cancel, one_smulE]
          right_inv := fun y => by rw [← mul_smulE, mul_inv_cancel, one_smulE] }
      map_src := map_src_smulE 𝔸 v₀ g
      map_rev := map_rev_smulE 𝔸 v₀ g }
  map_one' := SerreGraph.Iso.ext (one_smulV 𝔸 v₀) (one_smulE 𝔸 v₀)
  map_mul' g h := SerreGraph.Iso.ext (mul_smulV 𝔸 v₀ g h) (mul_smulE 𝔸 v₀ g h)

private theorem bassSerreAction_equivV_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V}
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreAction 𝔸 v₀ (π₁.mk s)).equivV (gVertexMk p) = gVertexMk (s.comp p) :=
  smulV_mk 𝔸 v₀ s p

private theorem bassSerreAction_equivE_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreAction 𝔸 v₀ (π₁.mk s)).equivE (gDartMk e p) = gDartMk e (s.comp p) :=
  smulE_mk 𝔸 v₀ s e p

/-- The projection `bassSerreGraphProj` to `Γ` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreGraphProj_comp_action (g : π₁ 𝔸 v₀) :
    SerreGraph.Hom.comp (bassSerreGraphProj 𝔸 v₀) (bassSerreAction 𝔸 v₀ g).toHom =
      bassSerreGraphProj 𝔸 v₀ := by
  refine π₁.induction_on g fun s => SerreGraph.Hom.ext _ (funext ?_) (funext ?_)
  · exact fun x => gVertex_induction_on x fun p => by
      rw [SerreGraph.Hom.comp_mapV, Function.comp_apply, SerreGraph.Iso.toHom_mapV,
        bassSerreAction_equivV_mk]
      rfl
  · exact fun y => gDart_induction_on y fun e p => by
      rw [SerreGraph.Hom.comp_mapE, Function.comp_apply, SerreGraph.Iso.toHom_mapE,
        bassSerreAction_equivE_mk]
      rfl

/-- The action of `π₁(𝔸, v₀)` on `bassSerreGraph 𝔸 v₀` has no inversions. -/
theorem bassSerreAction_smul_ne_rev (g : π₁ 𝔸 v₀) (y : (bassSerreGraph 𝔸 v₀).E) :
    (bassSerreAction 𝔸 v₀ g).equivE y ≠ (bassSerreGraph 𝔸 v₀).rev y :=
  SerreGraph.Aut.smul_ne_rev_of_comp_toHom_eq (bassSerreGraphProj 𝔸 v₀)
    (bassSerreAction 𝔸 v₀ g) (bassSerreGraphProj_comp_action 𝔸 v₀ g) y

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at a base vertex `v₀`, as a
`GTree (π₁ 𝔸 v₀)`. -/
def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := bassSerreGraph 𝔸 v₀
  isTree := bassSerreTree_isTree 𝔸 v₀
  action := bassSerreAction 𝔸 v₀
  action_smul_ne_rev := bassSerreAction_smul_ne_rev 𝔸 v₀

/-- Projection of `bassSerreTree 𝔸 v₀` onto `Γ`, sending `p A_v` to `v` and `(e, p)` to `e`. -/
def bassSerreProj : (bassSerreTree 𝔸 v₀).toSerreGraph.Hom Γ :=
  bassSerreGraphProj 𝔸 v₀

@[simp] theorem bassSerreProj_comp_action (g : π₁ 𝔸 v₀) :
    SerreGraph.Hom.comp (bassSerreProj 𝔸 v₀) ((bassSerreTree 𝔸 v₀).action g).toHom =
      bassSerreProj 𝔸 v₀ :=
  bassSerreGraphProj_comp_action 𝔸 v₀ g

end Action

/-! ### Constructors and basic API on `bassSerreTree` -/

section API

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

/-- The vertex `p A_v` of `bassSerreTree 𝔸 v₀` represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (bassSerreTree 𝔸 v₀).V :=
  gVertexMk p

variable (𝔸 v₀) in
/-- The distinguished base vertex `1 · A_{v₀}` of `bassSerreTree 𝔸 v₀`. -/
def baseVertex : (bassSerreTree 𝔸 v₀).V :=
  vertexMk Quiver.Path.nil

theorem baseVertex_def : baseVertex 𝔸 v₀ = vertexMk Quiver.Path.nil := (rfl)

/-- The dart of `bassSerreTree 𝔸 v₀` represented by a dart `e` of `Γ` and an `𝔸`-path `p` from
`v₀` to `src e`: it joins `p A_{src e}` to `(p e) A_{tgt e}`. -/
def dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (bassSerreTree 𝔸 v₀).E :=
  gDartMk e p

/-- Induction principle for vertices of `bassSerreTree 𝔸 v₀`. -/
@[elab_as_elim] theorem vertex_induction_on {P : (bassSerreTree 𝔸 v₀).V → Prop}
    (x : (bassSerreTree 𝔸 v₀).V) (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (vertexMk p)) : P x :=
  Quotient.inductionOn x fun ⟨_, p⟩ => h p

/-- Induction principle for darts of `bassSerreTree 𝔸 v₀`. -/
@[elab_as_elim] theorem dart_induction_on {P : (bassSerreTree 𝔸 v₀).E → Prop}
    (y : (bassSerreTree 𝔸 v₀).E) (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (dartMk e p)) :
    P y :=
  Quotient.inductionOn y fun ⟨e, p⟩ => h e p

@[simp] theorem src_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreTree 𝔸 v₀).src (dartMk e p) = vertexMk p := (rfl)

@[simp] theorem rev_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreTree 𝔸 v₀).rev (dartMk e p) =
      dartMk (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) := (rfl)

@[simp] theorem tgt_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreTree 𝔸 v₀).tgt (dartMk e p) =
      vertexMk (p.cons (Letter.dart (Γ.dart e))) := (rfl)

@[simp] theorem mk_smul_vertexMk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • vertexMk p = vertexMk (s.comp p) :=
  bassSerreAction_equivV_mk 𝔸 v₀ s p

@[simp] theorem mk_smul_dartMk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk s • dartMk e p = dartMk e (s.comp p) :=
  bassSerreAction_equivE_mk 𝔸 v₀ s e p

@[simp] theorem bassSerreProj_mapV_vertexMk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (bassSerreProj 𝔸 v₀).mapV (vertexMk p) = v := (rfl)

@[simp] theorem bassSerreProj_mapE_dartMk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (bassSerreProj 𝔸 v₀).mapE (dartMk e p) = e := (rfl)

/-- Two paths to the same vertex `v` represent the same vertex of `bassSerreTree 𝔸 v₀` iff they
differ on the right by an element of `A_v` up to homotopy. -/
theorem vertexMk_eq_vertexMk_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    vertexMk p = vertexMk q ↔
      ∃ a : 𝔸.vertexGroup v, Path.Homotopic p (q.comp (Path.ofVertex a)) :=
  gVertexMk_eq_iff

/-- Equal vertices of `bassSerreTree 𝔸 v₀` lie over the same vertex of `Γ`. -/
theorem eq_of_vertexMk_eq_vertexMk {v₁ v₂ : Γ.V} {p₁ : 𝔸.Path ⟨v₀⟩ ⟨v₁⟩} {p₂ : 𝔸.Path ⟨v₀⟩ ⟨v₂⟩}
    (h : vertexMk p₁ = vertexMk p₂) : v₁ = v₂ :=
  congrArg (bassSerreProj 𝔸 v₀).mapV h

/-- Two paths for the same dart `e` represent the same dart of `bassSerreTree 𝔸 v₀` iff they differ
on the right by an element of `α_e(A_e)` up to homotopy. -/
theorem dartMk_eq_dartMk_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    dartMk e p = dartMk e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e), Path.Homotopic p (q.comp (Path.ofVertex (𝔸.α e c))) :=
  gDartMk_eq_iff

/-- Equal darts of `bassSerreTree 𝔸 v₀` lie over the same dart of `Γ`. -/
theorem eq_of_dartMk_eq_dartMk {e₁ e₂ : Γ.E} {p₁ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₁⟩}
    {p₂ : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e₂⟩} (h : dartMk e₁ p₁ = dartMk e₂ p₂) : e₁ = e₂ :=
  congrArg (bassSerreProj 𝔸 v₀).mapE h

/-- Homotopic `𝔸`-paths represent the same vertex of `bassSerreTree 𝔸 v₀`. -/
theorem vertexMk_congr {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} (h : Path.Homotopic p q) :
    vertexMk p = vertexMk q :=
  vertexMk_eq_vertexMk_iff.mpr
    ⟨1, by rw [Path.comp_ofVertex]; exact h.trans (Path.Homotopic.one q).symm⟩

/-- Homotopic `𝔸`-paths represent the same dart of `bassSerreTree 𝔸 v₀`. -/
theorem dartMk_congr (e : Γ.E) {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : Path.Homotopic p q) :
    dartMk e p = dartMk e q :=
  dartMk_eq_dartMk_iff.mpr
    ⟨1, by rw [map_one, Path.comp_ofVertex]; exact h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem vertexMk_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    vertexMk (p.cons (Letter.vertex a)) = vertexMk p :=
  gVertexMk_cons_vertex p a

theorem vertexMk_comp_ofVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    vertexMk (p.comp (Path.ofVertex a)) = vertexMk p := by
  rw [Path.comp_ofVertex, vertexMk_cons_vertex]

@[simp] theorem vertexMk_ofVertex (a : 𝔸.vertexGroup v₀) :
    vertexMk (Path.ofVertex a) = baseVertex 𝔸 v₀ := by
  rw [Path.ofVertex_eq_nil_cons, vertexMk_cons_vertex]
  rfl

@[simp] theorem dartMk_cons_vertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    dartMk e (p.cons (Letter.vertex (𝔸.α e c))) = dartMk e p :=
  dartMk_eq_dartMk_iff.mpr ⟨c, by rw [Path.comp_ofVertex]; exact .refl _⟩

theorem dartMk_comp_ofVertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    dartMk e (p.comp (Path.ofVertex (𝔸.α e c))) = dartMk e p :=
  dartMk_eq_dartMk_iff.mpr ⟨c, .refl _⟩

end API

end GraphOfGroups

end TauCeti
