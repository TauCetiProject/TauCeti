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
`X(𝔸, v₀)` has:

* vertices `p A_v`: pairs `(v, p)` with `p : 𝔸.Path ⟨v₀⟩ ⟨v⟩`, modulo `(v, p) ≈ (v, q)` when `p` is
  homotopic to `q · a` for some `a ∈ A_v`;
* darts `[e, p]`: pairs `(e, p)` with `e : Γ.E` and `p : 𝔸.Path ⟨v₀⟩ ⟨src e⟩`, modulo
  `(e, p) ≈ (e, q)` when `p` is homotopic to `q · α_e(c)` for some `c ∈ A_e`, with source
  `p A_{src e}`, reversal `[rev e, p · e]`, and target `(p · e) A_{tgt e}`.

The fundamental group `π₁(𝔸, v₀)` acts on `X(𝔸, v₀)` on the left by path concatenation without
inversions (preserving the type projection to `Γ`), connectedness follows by induction on `𝔸`-paths,
and acyclicity follows from Britton's lemma
(`AlternatingPath.IsReduced.toPath_homotopic_ofVertex_iff`). Stabilizers and quotients are in
`BassSerre.Stabilizer`, stars and degrees in `BassSerre.Star`, and examples in `BassSerre.Examples`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTree`: `X(𝔸, v₀)` as a `GTree (π₁ 𝔸 v₀)`.
* `TauCeti.GraphOfGroups.bassSerreVertex`, `TauCeti.GraphOfGroups.bassSerreBaseVertex`,
  `TauCeti.GraphOfGroups.bassSerreDart`: path constructors for vertices and darts of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreVertexLift`, `TauCeti.GraphOfGroups.bassSerreDartLift`:
  `Sort*`-valued eliminators for invariant maps out of vertices and darts of `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.bassSerreTypeHom`, `TauCeti.GraphOfGroups.bassSerreComponentHom`:
  `π₁(𝔸, v₀)`-invariant projections from `X(𝔸, v₀)` to `Γ` and `Γ.component v₀`.

## Main results

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

/-- Left-coset equivalence on `Σ i : ι, 𝔸.Path ⟨v₀⟩ ⟨tgt i⟩` modulo right multiplication by
`H i ≤ A_{tgt i}` up to homotopy. -/
private def pathCosetRel {ι : Type*} (tgt : ι → Γ.V)
    (H : ∀ i, Subgroup (𝔸.vertexGroup (tgt i)))
    (x y : Σ i : ι, 𝔸.Path ⟨v₀⟩ ⟨tgt i⟩) : Prop :=
  ∃ (h : x.1 = y.1) (a : 𝔸.vertexGroup (tgt y.1)),
    a ∈ H y.1 ∧ Path.Homotopic (h ▸ x.2) (y.2.cons (Letter.vertex a))

private def pathCosetSetoid {ι : Type*} (tgt : ι → Γ.V)
    (H : ∀ i, Subgroup (𝔸.vertexGroup (tgt i))) :
    Setoid (Σ i : ι, 𝔸.Path ⟨v₀⟩ ⟨tgt i⟩) where
  r := 𝔸.pathCosetRel v₀ tgt H
  iseqv :=
    { refl := fun x => ⟨rfl, 1, one_mem _, (Path.Homotopic.one x.2).symm⟩
      symm := by
        rintro ⟨i, p⟩ ⟨j, q⟩ ⟨h, a, haH, ha⟩; dsimp only at h haH ha; subst h
        refine ⟨rfl, a⁻¹, inv_mem haH, (Path.Homotopic.one q).symm.trans ?_⟩
        rw [← mul_inv_cancel a]
        exact (Path.Homotopic.mul q a a⁻¹).symm.trans (ha.cons (Letter.vertex a⁻¹)).symm
      trans := by
        rintro ⟨i, p⟩ ⟨j, q⟩ ⟨k, r⟩ ⟨h₁, a, haH, ha⟩ ⟨h₂, b, hbH, hb⟩
        dsimp only at h₁ h₂ haH hbH ha hb; subst h₁ h₂
        exact ⟨rfl, b * a, mul_mem hbH haH,
          ha.trans ((hb.cons (Letter.vertex a)).trans (Path.Homotopic.mul r b a))⟩ }

private abbrev bassSerreVertexSetoid : Setoid (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  𝔸.pathCosetSetoid v₀ id fun _ => ⊤

private abbrev bassSerreDartSetoid : Setoid (Σ e : Γ.E, 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :=
  𝔸.pathCosetSetoid v₀ Γ.src fun e => (𝔸.α e).range

private def BassSerreVertex : Type (max u v w) := Quotient (𝔸.bassSerreVertexSetoid v₀)
private def BassSerreDart : Type (max u v w) := Quotient (𝔸.bassSerreDartSetoid v₀)

private def BassSerreVertex.mk {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : 𝔸.BassSerreVertex v₀ :=
  Quotient.mk (𝔸.bassSerreVertexSetoid v₀) ⟨v, p⟩

private def BassSerreDart.mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : 𝔸.BassSerreDart v₀ :=
  Quotient.mk (𝔸.bassSerreDartSetoid v₀) ⟨e, p⟩

section RawAPI

variable {𝔸 v₀}

@[elab_as_elim] private theorem BassSerreVertex.induction_on {P : 𝔸.BassSerreVertex v₀ → Prop}
    (u : 𝔸.BassSerreVertex v₀)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (BassSerreVertex.mk 𝔸 v₀ p)) : P u :=
  Quotient.ind (fun ⟨_, p⟩ => h p) u

private theorem BassSerreVertex.mk_eq_mk_iff_exists {v w : Γ.V} {p : 𝔸.Path ⟨v₀⟩ ⟨v⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨w⟩} :
    BassSerreVertex.mk 𝔸 v₀ p = BassSerreVertex.mk 𝔸 v₀ q ↔
      ∃ (h : v = w) (a : 𝔸.vertexGroup w), Path.Homotopic (h ▸ p) (q.cons (Letter.vertex a)) :=
  (Quotient.eq (r := 𝔸.bassSerreVertexSetoid v₀)).trans
    ⟨fun ⟨h, a, _, ha⟩ => ⟨h, a, ha⟩, fun ⟨h, a, ha⟩ => ⟨h, a, Subgroup.mem_top a, ha⟩⟩

private theorem BassSerreVertex.mk_eq_mk_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    BassSerreVertex.mk 𝔸 v₀ p = BassSerreVertex.mk 𝔸 v₀ q ↔
      ∃ a : 𝔸.vertexGroup v, Path.Homotopic p (q.cons (Letter.vertex a)) :=
  BassSerreVertex.mk_eq_mk_iff_exists.trans
    ⟨fun ⟨h, a, ha⟩ => ⟨a, by rwa [Subsingleton.elim h rfl] at ha⟩, fun ⟨a, ha⟩ => ⟨rfl, a, ha⟩⟩

@[simp] private theorem BassSerreVertex.mk_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    BassSerreVertex.mk 𝔸 v₀ (p.cons (Letter.vertex a)) = BassSerreVertex.mk 𝔸 v₀ p :=
  BassSerreVertex.mk_eq_mk_iff.mpr ⟨a, .refl _⟩

@[elab_as_elim] private theorem BassSerreDart.induction_on {P : 𝔸.BassSerreDart v₀ → Prop}
    (d : 𝔸.BassSerreDart v₀)
    (h : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩), P (BassSerreDart.mk 𝔸 v₀ e p)) : P d :=
  Quotient.ind (fun ⟨e, p⟩ => h e p) d

private theorem BassSerreDart.mk_eq_mk_iff_exists {e e' : Γ.E} {p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}
    {q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e'⟩} :
    BassSerreDart.mk 𝔸 v₀ e p = BassSerreDart.mk 𝔸 v₀ e' q ↔
      ∃ (h : e = e') (c : 𝔸.edgeGroup (Γ.toGeomEdge e')),
        Path.Homotopic (h ▸ p) (q.cons (Letter.vertex (𝔸.α e' c))) :=
  (Quotient.eq (r := 𝔸.bassSerreDartSetoid v₀)).trans
    ⟨fun ⟨h, _, ⟨c, rfl⟩, hc⟩ => ⟨h, c, hc⟩, fun ⟨h, c, hc⟩ => ⟨h, _, ⟨c, rfl⟩, hc⟩⟩

private theorem BassSerreDart.mk_eq_mk_iff {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} :
    BassSerreDart.mk 𝔸 v₀ e p = BassSerreDart.mk 𝔸 v₀ e q ↔
      ∃ c : 𝔸.edgeGroup (Γ.toGeomEdge e),
        Path.Homotopic p (q.cons (Letter.vertex (𝔸.α e c))) :=
  BassSerreDart.mk_eq_mk_iff_exists.trans
    ⟨fun ⟨h, c, hc⟩ => ⟨c, by rwa [Subsingleton.elim h rfl] at hc⟩, fun ⟨c, hc⟩ => ⟨rfl, c, hc⟩⟩

private theorem BassSerreDart.mk_congr {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩} (h : p.Homotopic q) :
    BassSerreDart.mk 𝔸 v₀ e p = BassSerreDart.mk 𝔸 v₀ e q :=
  BassSerreDart.mk_eq_mk_iff.mpr ⟨1, by rw [map_one]; exact h.trans (Path.Homotopic.one q).symm⟩

end RawAPI

private def BassSerreDart.src : 𝔸.BassSerreDart v₀ → 𝔸.BassSerreVertex v₀ :=
  Quotient.lift (fun x => BassSerreVertex.mk 𝔸 v₀ x.2) <| by
    rintro ⟨e, p⟩ ⟨e', q⟩ ⟨h, a, _, ha⟩; dsimp only at h ha; subst h
    exact BassSerreVertex.mk_eq_mk_iff.mpr ⟨a, ha⟩

private def BassSerreDart.rev : 𝔸.BassSerreDart v₀ → 𝔸.BassSerreDart v₀ :=
  Quotient.lift
    (fun x => BassSerreDart.mk 𝔸 v₀ (Γ.rev x.1) (x.2.cons (Letter.dart (Γ.dart x.1)))) <| by
    rintro ⟨e, p⟩ ⟨e', q⟩ ⟨h, a, haH, hc⟩; dsimp only at h haH hc; subst h
    obtain ⟨c, rfl⟩ := haH
    refine BassSerreDart.mk_eq_mk_iff.mpr
      ⟨(MulEquiv.cast (M := 𝔸.edgeGroup) (Γ.toGeomEdge_rev e)).symm c, ?_⟩
    rw [𝔸.α_rev_apply, MulEquiv.apply_symm_apply]
    exact (hc.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.dart_ω e c q).symm

private theorem bassSerreRev_aux {e' e : Γ.E} (he : Γ.rev e' = e) (q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e'⟩) :
    BassSerreDart.mk 𝔸 v₀ (Γ.rev e') (q.cons (Letter.dart (Γ.dart e'))) =
      BassSerreDart.mk 𝔸 v₀ e (q.cons (Letter.dart ⟨e', rfl, by rw [Γ.tgt_def, he]⟩)) := by
  subst he; rw [Γ.dart_def]; rfl

private theorem BassSerreDart.rev_rev (d : 𝔸.BassSerreDart v₀) :
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

private theorem BassSerreDart.rev_ne (d : 𝔸.BassSerreDart v₀) : BassSerreDart.rev 𝔸 v₀ d ≠ d :=
  BassSerreDart.induction_on d fun e _ h =>
    Γ.rev_ne e (BassSerreDart.mk_eq_mk_iff_exists.mp h).choose

private def bassSerreGraph : SerreGraph.{max u v w, max u v w} where
  V := 𝔸.BassSerreVertex v₀
  E := 𝔸.BassSerreDart v₀
  src := BassSerreDart.src 𝔸 v₀
  rev := BassSerreDart.rev 𝔸 v₀
  rev_rev := BassSerreDart.rev_rev 𝔸 v₀
  rev_ne := BassSerreDart.rev_ne 𝔸 v₀

@[simp] private theorem bassSerreGraph_src_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).src (BassSerreDart.mk 𝔸 v₀ e p) = BassSerreVertex.mk 𝔸 v₀ p := (rfl)

@[simp] private theorem bassSerreGraph_rev_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).rev (BassSerreDart.mk 𝔸 v₀ e p) =
      BassSerreDart.mk 𝔸 v₀ (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) := (rfl)

@[simp] private theorem bassSerreGraph_tgt_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreGraph v₀).tgt (BassSerreDart.mk 𝔸 v₀ e p) =
      BassSerreVertex.mk 𝔸 v₀ (p.cons (Letter.dart (Γ.dart e))) := (rfl)

/-! ### Connectedness and acyclicity of `X(𝔸, v₀)` -/

/-- Every vertex of `X(𝔸, v₀)` is reachable from the base vertex `1 · A_{v₀}`. -/
private theorem bassSerreGraph_reachable (u : (𝔸.bassSerreGraph v₀).V) :
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
      rcases y₁, y₂ with ⟨⟨w₁⟩, ⟨w₂⟩⟩
      cases l with
      | vertex a => simpa only [BassSerreVertex.mk_cons_vertex] using ih
      | dart f =>
        rcases f with ⟨e, rfl, rfl⟩
        exact ih.map fun P => P.cons ⟨BassSerreDart.mk 𝔸 v₀ e q, rfl, by rw [← Γ.dart_def]; rfl⟩
  exact aux p

/-- `X(𝔸, v₀)` is connected. -/
private theorem bassSerreGraph_connected : (𝔸.bassSerreGraph v₀).Connected :=
  ((𝔸.bassSerreGraph v₀).connected_iff).mpr
    ⟨⟨BassSerreVertex.mk 𝔸 v₀ (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)⟩,
      (𝔸.bassSerreGraph v₀).preconnected_of_forall_nonempty_path
        (BassSerreVertex.mk 𝔸 v₀ (.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) (𝔸.bassSerreGraph_reachable v₀)⟩

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
      exact BassSerreDart.mk_eq_mk_iff.mpr ⟨c', by rwa [hdart_eq, ← hc'] at hpe_p₀⟩
    · rw [AlternatingPath.toPath_cons, Quiver.Path.comp_cons, Quiver.Path.comp_cons]
      exact (hpe_comp.cons (Letter.dart (Γ.dart e))).trans (Path.Homotopic.one _).symm

private theorem not_closed_lift_of_isReduced (e : Γ.E) (p_e : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    ∀ (w : Γ.V), Γ.tgt e = w → ∀ (p_w : 𝔸.Path ⟨v₀⟩ ⟨w⟩) (q : 𝔸.AlternatingPath w (Γ.src e)),
      (AlternatingPath.cons q (Γ.dart e) 1).IsReduced →
      Path.Homotopic (p_e.cons (Letter.dart (Γ.dart e)))
        (p_w.comp (AlternatingPath.cons q (Γ.dart e) 1).toPath) →
      BassSerreVertex.mk 𝔸 v₀ (p_e.cons (Letter.dart (Γ.dart e))) =
        BassSerreVertex.mk 𝔸 v₀ p_w → False := by
  rintro w rfl p_w q hr hp_hom hv_eq
  obtain ⟨g, hg⟩ := BassSerreVertex.mk_eq_mk_iff.mp hv_eq
  rw [← Path.comp_ofVertex] at hg
  exact nomatch hr.toPath_homotopic_ofVertex_iff.mp
    ((Path.Homotopic.comp_left_iff p_w).mp (hp_hom.symm.trans hg))

/-- `X(𝔸, v₀)` is acyclic. -/
private theorem bassSerreGraph_isAcyclic : (𝔸.bassSerreGraph v₀).IsAcyclic := by
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
private theorem bassSerreGraph_isTree : (𝔸.bassSerreGraph v₀).IsTree :=
  (SerreGraph.isTree_iff _).mpr ⟨𝔸.bassSerreGraph_connected v₀, 𝔸.bassSerreGraph_isAcyclic v₀⟩

/-! ### Left action of `π₁(𝔸, v₀)` and the bundled `GTree` -/

section PathCosetSmul

variable {ι : Type*} (tgt : ι → Γ.V) (H : ∀ i, Subgroup (𝔸.vertexGroup (tgt i)))

private def pathCosetSmul :
    π₁ 𝔸 v₀ → Quotient (𝔸.pathCosetSetoid v₀ tgt H) → Quotient (𝔸.pathCosetSetoid v₀ tgt H) :=
  π₁.lift (fun s => Quotient.lift (fun x => Quotient.mk _ ⟨x.1, s.comp x.2⟩) <| by
      rintro ⟨i, p⟩ ⟨j, q⟩ ⟨h, a, haH, ha⟩; dsimp only at h haH ha; subst h
      exact Quotient.sound ⟨rfl, a, haH, ha.comp_left s⟩)
    fun _ _ hs => funext <| Quotient.ind fun ⟨_, p⟩ =>
      Quotient.sound ⟨rfl, 1, one_mem _, (hs.comp_right p).trans (Path.Homotopic.one _).symm⟩

private theorem pathCosetSmul_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (i : ι) (p : 𝔸.Path ⟨v₀⟩ ⟨tgt i⟩) :
    𝔸.pathCosetSmul v₀ tgt H (π₁.mk s) (Quotient.mk (𝔸.pathCosetSetoid v₀ tgt H) ⟨i, p⟩) =
      Quotient.mk (𝔸.pathCosetSetoid v₀ tgt H) ⟨i, s.comp p⟩ :=
  congrFun (π₁.lift_mk _ _ s) _

private theorem one_pathCosetSmul (u : Quotient (𝔸.pathCosetSetoid v₀ tgt H)) :
    𝔸.pathCosetSmul v₀ tgt H 1 u = u :=
  Quotient.inductionOn u fun ⟨_, _⟩ => by
    rw [← π₁.mk_nil, pathCosetSmul_mk, Quiver.Path.nil_comp]

private theorem mul_pathCosetSmul (g h : π₁ 𝔸 v₀) (u : Quotient (𝔸.pathCosetSetoid v₀ tgt H)) :
    𝔸.pathCosetSmul v₀ tgt H (g * h) u =
      𝔸.pathCosetSmul v₀ tgt H g (𝔸.pathCosetSmul v₀ tgt H h u) :=
  π₁.induction_on g fun _ => π₁.induction_on h fun _ => Quotient.inductionOn u fun ⟨_, _⟩ => by
    rw [← π₁.mk_comp, pathCosetSmul_mk, pathCosetSmul_mk, pathCosetSmul_mk, Quiver.Path.comp_assoc]

private def pathCosetSmulEquiv (g : π₁ 𝔸 v₀) :
    Quotient (𝔸.pathCosetSetoid v₀ tgt H) ≃ Quotient (𝔸.pathCosetSetoid v₀ tgt H) where
  toFun := 𝔸.pathCosetSmul v₀ tgt H g
  invFun := 𝔸.pathCosetSmul v₀ tgt H g⁻¹
  left_inv u := by rw [← mul_pathCosetSmul, inv_mul_cancel, one_pathCosetSmul]
  right_inv u := by rw [← mul_pathCosetSmul, mul_inv_cancel, one_pathCosetSmul]

end PathCosetSmul

private def bassSerreAction : π₁ 𝔸 v₀ →* (𝔸.bassSerreGraph v₀).Aut where
  toFun g :=
    { equivV := 𝔸.pathCosetSmulEquiv v₀ id (fun _ => ⊤) g
      equivE := 𝔸.pathCosetSmulEquiv v₀ Γ.src (fun e => (𝔸.α e).range) g
      map_src := fun d => π₁.induction_on g fun s => BassSerreDart.induction_on d fun e p =>
        (congrArg (𝔸.bassSerreGraph v₀).src
          (𝔸.pathCosetSmul_mk v₀ Γ.src (fun e => (𝔸.α e).range) s e p)).trans
          (𝔸.pathCosetSmul_mk v₀ id (fun _ => ⊤) s (Γ.src e) p).symm
      map_rev := fun d => π₁.induction_on g fun s => BassSerreDart.induction_on d fun e p =>
        ((𝔸.pathCosetSmul_mk v₀ Γ.src (fun e => (𝔸.α e).range) s (Γ.rev e)
          (p.cons (Letter.dart (Γ.dart e)))).trans
          (congrArg (BassSerreDart.mk 𝔸 v₀ (Γ.rev e)) (Quiver.Path.comp_cons ..))).trans
          (congrArg (𝔸.bassSerreGraph v₀).rev
            (𝔸.pathCosetSmul_mk v₀ Γ.src (fun e => (𝔸.α e).range) s e p)).symm }
  map_one' := SerreGraph.Iso.ext (𝔸.one_pathCosetSmul v₀ id _) (𝔸.one_pathCosetSmul v₀ Γ.src _)
  map_mul' g h := SerreGraph.Iso.ext (𝔸.mul_pathCosetSmul v₀ id _ g h)
    (𝔸.mul_pathCosetSmul v₀ Γ.src _ g h)

private theorem bassSerreAction_smul_ne_rev (g : π₁ 𝔸 v₀) (d : (𝔸.bassSerreGraph v₀).E) :
    (𝔸.bassSerreAction v₀ g).equivE d ≠ (𝔸.bassSerreGraph v₀).rev d :=
  π₁.induction_on g fun s => BassSerreDart.induction_on d fun e p h =>
    Γ.rev_ne e (BassSerreDart.mk_eq_mk_iff_exists.mp
      ((𝔸.pathCosetSmul_mk v₀ Γ.src (fun e => (𝔸.α e).range) s e p).symm.trans h)).choose.symm

/-- The Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` at base vertex `v₀`, as a `GTree` for
`π₁(𝔸, v₀)`. -/
def bassSerreTree : GTree.{max u v w, max u v w} (π₁ 𝔸 v₀) where
  toSerreGraph := 𝔸.bassSerreGraph v₀
  isTree := 𝔸.bassSerreGraph_isTree v₀
  action := 𝔸.bassSerreAction v₀
  action_smul_ne_rev := 𝔸.bassSerreAction_smul_ne_rev v₀

/-- The Bass–Serre graph `X(𝔸, v₀)` is a tree. -/
theorem bassSerreTree_isTree : (𝔸.bassSerreTree v₀).IsTree := (𝔸.bassSerreTree v₀).isTree

/-! ### Path constructors and basic API on `bassSerreTree` -/

/-- The vertex `p A_v` of `𝔸.bassSerreTree v₀` represented by an `𝔸`-path `p` from `v₀` to `v`. -/
def bassSerreVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : (𝔸.bassSerreTree v₀).V :=
  BassSerreVertex.mk 𝔸 v₀ p

/-- The base vertex `1 · A_{v₀}` of `𝔸.bassSerreTree v₀`, represented by the empty path at `v₀`. -/
def bassSerreBaseVertex : (𝔸.bassSerreTree v₀).V := 𝔸.bassSerreVertex v₀ .nil

theorem bassSerreBaseVertex_def : 𝔸.bassSerreBaseVertex v₀ = 𝔸.bassSerreVertex v₀ .nil := (rfl)

instance : Inhabited (𝔸.bassSerreTree v₀).V := ⟨𝔸.bassSerreBaseVertex v₀⟩

/-- The dart `[e, p]` of `𝔸.bassSerreTree v₀`, with source `p A_{src e}` and target
`(p · e) A_{tgt e}`. -/
def bassSerreDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) : (𝔸.bassSerreTree v₀).E :=
  BassSerreDart.mk 𝔸 v₀ e p

/-- Descend a homotopy-invariant function on `𝔸`-paths from `v₀`, invariant under right
multiplication by vertex groups, to `(𝔸.bassSerreTree v₀).V`. -/
def bassSerreVertexLift {β : Sort*} (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (h_hom : ∀ {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f p = f q)
    (h_vert : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v),
      f (p.cons (Letter.vertex a)) = f p) :
    (𝔸.bassSerreTree v₀).V → β :=
  Quotient.lift (fun x => f x.2) fun ⟨_, _⟩ ⟨_, q⟩ ⟨h, a, _, ha⟩ => by
    dsimp only at h ha; subst h; exact (h_hom ha).trans (h_vert q a)

/-- Descend a homotopy-invariant function on pairs `(e, p)`, invariant under right multiplication
by `α_e(A_e)`, to `(𝔸.bassSerreTree v₀).E`. -/
def bassSerreDartLift {β : Sort*} (f : ∀ (e : Γ.E), 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → β)
    (h_hom : ∀ {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}, p.Homotopic q → f e p = f e q)
    (h_α : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      f e (p.cons (Letter.vertex (𝔸.α e c))) = f e p) :
    (𝔸.bassSerreTree v₀).E → β :=
  Quotient.lift (fun x => f x.1 x.2) fun ⟨e, _⟩ ⟨_, q⟩ ⟨h, a, haH, hc⟩ => by
    dsimp only at h haH hc; subst h; obtain ⟨c, rfl⟩ := haH
    exact (h_hom (e := e) hc).trans (h_α e q c)

section TreeAPI

variable {𝔸 v₀}

@[simp] theorem bassSerreVertexLift_bassSerreVertex {β : Sort*}
    (f : ∀ {v : Γ.V}, 𝔸.Path ⟨v₀⟩ ⟨v⟩ → β)
    (h_hom : ∀ {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩}, p.Homotopic q → f p = f q)
    (h_vert : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v),
      f (p.cons (Letter.vertex a)) = f p) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    𝔸.bassSerreVertexLift v₀ f h_hom h_vert (𝔸.bassSerreVertex v₀ p) = f p := (rfl)

@[simp] theorem bassSerreDartLift_bassSerreDart {β : Sort*}
    (f : ∀ (e : Γ.E), 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩ → β)
    (h_hom : ∀ {e : Γ.E} {p q : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩}, p.Homotopic q → f e p = f e q)
    (h_α : ∀ (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)),
      f e (p.cons (Letter.vertex (𝔸.α e c))) = f e p) (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.bassSerreDartLift v₀ f h_hom h_α (𝔸.bassSerreDart v₀ e p) = f e p := (rfl)

/-- Prove a property of vertices of `𝔸.bassSerreTree v₀` by checking it on `𝔸`-paths from `v₀`. -/
@[elab_as_elim] theorem bassSerreVertex_induction_on {P : (𝔸.bassSerreTree v₀).V → Prop}
    (u : (𝔸.bassSerreTree v₀).V)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (𝔸.bassSerreVertex v₀ p)) : P u :=
  BassSerreVertex.induction_on u h

/-- Prove a property of darts of `𝔸.bassSerreTree v₀` by checking it on pairs `(e, p)`. -/
@[elab_as_elim] theorem bassSerreDart_induction_on {P : (𝔸.bassSerreTree v₀).E → Prop}
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
  bassSerreVertex_eq_iff.mpr ⟨1, h.trans (Path.Homotopic.one q).symm⟩

@[simp] theorem bassSerreVertex_cons_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (a : 𝔸.vertexGroup v) :
    𝔸.bassSerreVertex v₀ (p.cons (Letter.vertex a)) = 𝔸.bassSerreVertex v₀ p :=
  BassSerreVertex.mk_cons_vertex p a

theorem bassSerreVertex_comp_ofVertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a : 𝔸.vertexGroup v) :
    𝔸.bassSerreVertex v₀ (p.comp (Path.ofVertex a)) = 𝔸.bassSerreVertex v₀ p := by
  rw [Path.comp_ofVertex, bassSerreVertex_cons_vertex]

@[simp] theorem bassSerreVertex_ofVertex (a : 𝔸.vertexGroup v₀) :
    𝔸.bassSerreVertex v₀ (Path.ofVertex a) = 𝔸.bassSerreBaseVertex v₀ := by
  rw [Path.ofVertex_eq_nil_cons, bassSerreVertex_cons_vertex, bassSerreBaseVertex_def]

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
    𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e q := BassSerreDart.mk_congr h

@[simp] theorem bassSerreDart_cons_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex (𝔸.α e c))) = 𝔸.bassSerreDart v₀ e p :=
  bassSerreDart_eq_iff.mpr ⟨c, .refl _⟩

theorem bassSerreDart_comp_ofVertex_α (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) :
    𝔸.bassSerreDart v₀ e (p.comp (Path.ofVertex (𝔸.α e c))) = 𝔸.bassSerreDart v₀ e p := by
  rw [Path.comp_ofVertex, bassSerreDart_cons_α]

@[simp] theorem bassSerreTree_src_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDart v₀ e p) = 𝔸.bassSerreVertex v₀ p := (rfl)

@[simp] theorem bassSerreTree_rev_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).rev (𝔸.bassSerreDart v₀ e p) =
      𝔸.bassSerreDart v₀ (Γ.rev e) (p.cons (Letter.dart (Γ.dart e))) := (rfl)

@[simp] theorem bassSerreTree_tgt_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTree v₀).tgt (𝔸.bassSerreDart v₀ e p) =
      𝔸.bassSerreVertex v₀ (p.cons (Letter.dart (Γ.dart e))) := (rfl)

@[simp] theorem mk_smul_bassSerreVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • 𝔸.bassSerreVertex v₀ p = 𝔸.bassSerreVertex v₀ (s.comp p) :=
  𝔸.pathCosetSmul_mk v₀ id (fun _ => ⊤) s v p

@[simp] theorem mk_smul_bassSerreBaseVertex (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    π₁.mk s • 𝔸.bassSerreBaseVertex v₀ = 𝔸.bassSerreVertex v₀ s := by
  rw [bassSerreBaseVertex_def, mk_smul_bassSerreVertex, Quiver.Path.comp_nil]

@[simp] theorem mk_smul_bassSerreDart (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (e : Γ.E)
    (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    π₁.mk s • 𝔸.bassSerreDart v₀ e p = 𝔸.bassSerreDart v₀ e (s.comp p) :=
  𝔸.pathCosetSmul_mk v₀ Γ.src (fun e => (𝔸.α e).range) s e p

end TreeAPI

/-! ### Type projection to `Γ` and to `Γ.component v₀` -/

/-- The projection morphism from `X(𝔸, v₀)` to `Γ`, sending `p A_v` to `v` and `[e, p]` to `e`. -/
def bassSerreTypeHom : (𝔸.bassSerreTree v₀).toSerreGraph.Hom Γ where
  mapV := 𝔸.bassSerreVertexLift v₀ (fun {v} _ => v) (fun _ => rfl) (fun _ _ => rfl)
  mapE := 𝔸.bassSerreDartLift v₀ (fun e _ => e) (fun _ => rfl) (fun _ _ _ => rfl)
  map_src d := bassSerreDart_induction_on d fun _ _ => rfl
  map_rev d := bassSerreDart_induction_on d fun _ _ => rfl

/-- Every `𝔸`-path from `v₀` ends in `Γ.component v₀`, so the type projection factors through
`Γ.component v₀`. -/
def bassSerreComponentHom : (𝔸.bassSerreTree v₀).toSerreGraph.Hom (Γ.component v₀) where
  mapV := 𝔸.bassSerreVertexLift v₀
    (fun {v} p => ⟨v, (Γ.mem_componentVertices_iff v₀ v).mpr ⟨p.edgePath⟩⟩)
    (fun _ => rfl) (fun _ _ => rfl)
  mapE := 𝔸.bassSerreDartLift v₀
    (fun e p => ⟨e, (Γ.mem_componentDarts_iff v₀ e).mpr ⟨p.edgePath⟩⟩)
    (fun _ => rfl) (fun _ _ _ => rfl)
  map_src d := bassSerreDart_induction_on d fun _ _ => rfl
  map_rev d := bassSerreDart_induction_on d fun _ _ => rfl

section ProjectionAPI

variable {𝔸 v₀}

@[simp] theorem bassSerreTypeHom_mapV {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTypeHom v₀).mapV (𝔸.bassSerreVertex v₀ p) = v := (rfl)

@[simp] theorem bassSerreTypeHom_mapV_baseVertex :
    (𝔸.bassSerreTypeHom v₀).mapV (𝔸.bassSerreBaseVertex v₀) = v₀ := (rfl)

@[simp] theorem bassSerreTypeHom_mapE (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    (𝔸.bassSerreTypeHom v₀).mapE (𝔸.bassSerreDart v₀ e p) = e := (rfl)

@[simp] theorem bassSerreComponentHom_mapV_val (u : (𝔸.bassSerreTree v₀).V) :
    ((𝔸.bassSerreComponentHom v₀).mapV u).1 = (𝔸.bassSerreTypeHom v₀).mapV u :=
  bassSerreVertex_induction_on u fun _ => rfl

@[simp] theorem bassSerreComponentHom_mapV_baseVertex :
    (𝔸.bassSerreComponentHom v₀).mapV (𝔸.bassSerreBaseVertex v₀) = Γ.componentBase v₀ :=
  Subtype.ext (by simp)

@[simp] theorem bassSerreComponentHom_mapE_val (d : (𝔸.bassSerreTree v₀).E) :
    ((𝔸.bassSerreComponentHom v₀).mapE d).1 = (𝔸.bassSerreTypeHom v₀).mapE d :=
  bassSerreDart_induction_on d fun _ _ => rfl

end ProjectionAPI

@[simp] theorem componentInclusion_comp_bassSerreComponentHom :
    (Γ.componentInclusion v₀).comp (𝔸.bassSerreComponentHom v₀) = 𝔸.bassSerreTypeHom v₀ := by
  ext <;> simp

@[simp] theorem bassSerreComponentHom_mapV_smul (g : π₁ 𝔸 v₀) (u : (𝔸.bassSerreTree v₀).V) :
    (𝔸.bassSerreComponentHom v₀).mapV (g • u) = (𝔸.bassSerreComponentHom v₀).mapV u :=
  π₁.induction_on g fun _ => bassSerreVertex_induction_on u fun _ => Subtype.ext (by simp)

@[simp] theorem bassSerreComponentHom_mapE_smul (g : π₁ 𝔸 v₀) (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.bassSerreComponentHom v₀).mapE (g • d) = (𝔸.bassSerreComponentHom v₀).mapE d :=
  π₁.induction_on g fun _ => bassSerreDart_induction_on d fun _ _ => Subtype.ext (by simp)

/-- The component projection to `Γ.component v₀` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreComponentHom_comp_action (g : π₁ 𝔸 v₀) :
    (𝔸.bassSerreComponentHom v₀).comp ((𝔸.bassSerreTree v₀).action g).toHom =
      𝔸.bassSerreComponentHom v₀ := by
  ext x
  · simp [← SerreGraph.Aut.smul_vertex_def, ← GTree.smul_vertex_def]
  · simp [← SerreGraph.Aut.smul_dart_def, ← GTree.smul_dart_def]

/-- The type projection to `Γ` is invariant under the action of `π₁(𝔸, v₀)`. -/
@[simp] theorem bassSerreTypeHom_comp_action (g : π₁ 𝔸 v₀) :
    (𝔸.bassSerreTypeHom v₀).comp ((𝔸.bassSerreTree v₀).action g).toHom =
      𝔸.bassSerreTypeHom v₀ := by
  rw [← componentInclusion_comp_bassSerreComponentHom, ← SerreGraph.Hom.comp_assoc,
    bassSerreComponentHom_comp_action]

@[simp] theorem bassSerreTypeHom_mapV_smul (g : π₁ 𝔸 v₀) (u : (𝔸.bassSerreTree v₀).V) :
    (𝔸.bassSerreTypeHom v₀).mapV (g • u) = (𝔸.bassSerreTypeHom v₀).mapV u := by
  rw [← bassSerreComponentHom_mapV_val, bassSerreComponentHom_mapV_smul,
    bassSerreComponentHom_mapV_val]

@[simp] theorem bassSerreTypeHom_mapE_smul (g : π₁ 𝔸 v₀) (d : (𝔸.bassSerreTree v₀).E) :
    (𝔸.bassSerreTypeHom v₀).mapE (g • d) = (𝔸.bassSerreTypeHom v₀).mapE d := by
  rw [← bassSerreComponentHom_mapE_val, bassSerreComponentHom_mapE_smul,
    bassSerreComponentHom_mapE_val]

/-! ### Edgeless components and trees -/

instance [IsEmpty (Γ.component v₀).E] : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun d => isEmptyElim ((𝔸.bassSerreComponentHom v₀).mapE d)⟩

instance [IsEmpty (𝔸.bassSerreTree v₀).E] : Unique (𝔸.bassSerreTree v₀).V :=
  @uniqueOfSubsingleton _ (𝔸.bassSerreTree v₀).subsingleton_of_isEmpty_dart
    (𝔸.bassSerreBaseVertex v₀)

end GraphOfGroups

end TauCeti
