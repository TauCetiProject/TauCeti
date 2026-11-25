/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Tree

/-!
# Outgoing stars and vertex degrees of Bass–Serre trees

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `a : Γ.V`, the outgoing darts of
the Bass–Serre tree `X(𝔸, a) = bassSerreTree 𝔸 a` at a vertex `p A_b` decompose over the darts
`e : b ⟶ c` of `Γ` starting at `b`:

* The darts starting at `p A_b` that project to `e` correspond bijectively to the left cosets
  `A_b / α_e(A_e)`, via `g α_e(A_e) ↦ (p g) α_e(A_e)` (`bassSerreOutDartEquiv`).
* Summing over all outgoing darts of `Γ` at `b` identifies the full outgoing star of `p A_b` in
  `X(𝔸, a)` with `Σ e : {e : Γ.E // Γ.src e = b}, A_b / α_e(A_e)` (`bassSerreStarEquiv`).
* Passing to cardinals and `Nat.card` expresses the degree of any vertex `y` of `X(𝔸, a)` over
  `b = (bassSerreProjection 𝔸 a).mapV y` as the sum of the coset cardinals or subgroup indices
  `[A_b : α_e(A_e)]` (`mk_src_eq_bassSerreTree`, `card_src_eq_bassSerreTree`).
* Specializing to one-edge graphs of groups identifies outgoing stars for HNN loops `loop f g hf hg`
  with `(G ⧸ f.range) ⊕ (G ⧸ g.range)` (`loopStarEquiv`, giving finite degree
  `f.range.index + g.range.index` in `card_src_eq_bassSerreTree_loop`) and for amalgamated segments
  `segment f g hf hg` with `A ⧸ f.range` and `B ⧸ g.range` (`segmentStarEquivFalse`,
  `segmentStarEquivTrue`), simplifying to `A` and `B` for both outgoing stars and adjacent vertices
  when `[Subsingleton C]` (`segmentFreeStarEquivFalse`, `segmentFreeStarEquivTrue`,
  `segmentFreeAdjacentEquivFalse`, `segmentFreeAdjacentEquivTrue`).

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreOutDartEquiv`: bijection between `A_b / α_e(A_e)` and the
  outgoing darts of `X(𝔸, a)` at `p A_b` over `e`.
* `TauCeti.GraphOfGroups.bassSerreStarEquiv`: bijection between
  `Σ e : {e : Γ.E // Γ.src e = b}, A_b / α_e(A_e)` and the outgoing star at `p A_b`.
* `TauCeti.GraphOfGroups.loopStarEquiv`, `TauCeti.GraphOfGroups.segmentStarEquivFalse`,
  `TauCeti.GraphOfGroups.segmentStarEquivTrue`: outgoing star equivalences for loops and segments.
* `TauCeti.GraphOfGroups.segmentFreeStarEquivFalse`,
  `TauCeti.GraphOfGroups.segmentFreeStarEquivTrue`,
  `TauCeti.GraphOfGroups.segmentFreeAdjacentEquivFalse`,
  `TauCeti.GraphOfGroups.segmentFreeAdjacentEquivTrue`: star and adjacent-vertex equivalences for
  `A ∗ B`.

## Main results

* `TauCeti.GraphOfGroups.mk_src_eq_bassSerreTree`: cardinal formula for the outgoing star of any
  vertex of `X(𝔸, a)`.
* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree`: finite degree formula as the sum of subgroup
  indices `[A_b : α_e(A_e)]`.
* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_loop`: finite degree formula
  `f.range.index + g.range.index` for `loop f g hf hg`.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1 and §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

section General

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

/-- Every dart of `X(𝔸, a)` starting at `p A_b` is represented by extending `p` by an element of
`A_b`. -/
private theorem exists_bassSerreDart_of_src_eq {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    {d : (bassSerreTree 𝔸 a).E} (hd : (bassSerreTree 𝔸 a).src d = bassSerreVertex p) :
    ∃ (c : Γ.V) (e : b ⟶ c) (g : 𝔸.vertexGroup b),
      d = bassSerreDart (p.cons (.vertex g)) e := by
  obtain ⟨b', c, q, e, rfl⟩ := bassSerreDart_surjective d
  have hb : b' = b := by simpa using congrArg (bassSerreProjection 𝔸 a).mapV hd
  subst hb
  obtain ⟨g, hq⟩ := bassSerreVertex_eq_bassSerreVertex_iff.1 (by simpa using hd.symm)
  exact ⟨c, e, g, bassSerreDart_congr hq e⟩

private noncomputable def bassSerreOutDartMap {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (q : 𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range) :
    {d : (bassSerreTree 𝔸 a).E //
      (bassSerreTree 𝔸 a).src d = bassSerreVertex p ∧
        (bassSerreProjection 𝔸 a).mapE d = e.val} :=
  Quotient.liftOn' q
    (fun g : 𝔸.vertexGroup b ↦
      ⟨bassSerreDart (p.cons (.vertex g)) e,
        (src_bassSerreDart _ _).trans (bassSerreVertex_cons_vertex p g),
        bassSerreProjection_mapE_bassSerreDart _ _⟩)
    fun g₁ g₂ h ↦ by
      obtain ⟨c₀, hc₀⟩ : g₁⁻¹ * g₂ ∈ (𝔸.αArrow e).range := QuotientGroup.leftRel_apply.1 h
      apply Subtype.ext
      rw [eq_mul_of_inv_mul_eq hc₀.symm]
      exact bassSerreDart_eq_bassSerreDart_iff.2 ⟨c₀, (Path.Homotopic.mul p g₁ _).symm⟩

private theorem bassSerreOutDartMap_bijective {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    Function.Bijective (bassSerreOutDartMap p e) := by
  refine ⟨fun x₁ x₂ h ↦ ?_, fun ⟨d, hsrc, hproj⟩ ↦ ?_⟩
  · induction x₁ using QuotientGroup.induction_on with | H g₁
    induction x₂ using QuotientGroup.induction_on with | H g₂
    obtain ⟨c₀, hc₀⟩ := bassSerreDart_eq_bassSerreDart_iff.1 (congrArg Subtype.val h)
    have hhom : Path.Homotopic (Path.ofVertex g₂) (Path.ofVertex (g₁ * 𝔸.αArrow e c₀)) := by
      refine (Path.Homotopic.comp_left_iff (p := p)).1 ?_
      rw [Path.comp_ofVertex, Path.comp_ofVertex]
      exact hc₀.trans (Path.Homotopic.mul p g₁ _)
    have hg : g₂ = g₁ * 𝔸.αArrow e c₀ := Path.ofVertex_homotopic_ofVertex_iff.1 hhom
    exact QuotientGroup.eq.2 (MonoidHom.mem_range.2 ⟨c₀, by rw [hg, inv_mul_cancel_left]⟩)
  · obtain ⟨c', e', g, rfl⟩ := exists_bassSerreDart_of_src_eq p hsrc
    have he' : e'.val = e.val := (bassSerreProjection_mapE_bassSerreDart _ _).symm.trans hproj
    have hc' : c' = c := e'.property.2.symm.trans ((congrArg Γ.tgt he').trans e.property.2)
    subst hc'
    obtain rfl : e = e' := (Subtype.ext he').symm
    exact ⟨(g : 𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range), Subtype.ext (rfl)⟩

/-- Outgoing darts of `X(𝔸, a)` at `p A_b` lifting a fixed arrow `e : b ⟶ c` correspond to left
cosets `A_b / α_e(A_e)`, via `g α_e(A_e) ↦ (p g) α_e(A_e)`. -/
noncomputable def bassSerreOutDartEquiv {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range ≃
      {d : (bassSerreTree 𝔸 a).E //
        (bassSerreTree 𝔸 a).src d = bassSerreVertex p ∧
          (bassSerreProjection 𝔸 a).mapE d = e.val} :=
  Equiv.ofBijective (bassSerreOutDartMap p e) (bassSerreOutDartMap_bijective p e)

@[simp] theorem bassSerreOutDartEquiv_mk_val {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (g : 𝔸.vertexGroup b) :
    (bassSerreOutDartEquiv p e (g : 𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range)).val =
      bassSerreDart (p.cons (.vertex g)) e := by
  rw [bassSerreOutDartEquiv, Equiv.ofBijective_apply]
  rfl

/-- The outgoing star of `p A_b` in `X(𝔸, a)` decomposes over the darts of `Γ` starting at `b` into
the coset spaces `A_b / α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (Σ e : {e : Γ.E // Γ.src e = b},
      𝔸.vertexGroup b ⧸ (𝔸.αArrow (⟨e.val, e.property, rfl⟩ : b ⟶ Γ.tgt e.val)).range) ≃
      {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = bassSerreVertex p} :=
  (Equiv.sigmaCongrRight fun e : {e : Γ.E // Γ.src e = b} ↦
    ((bassSerreOutDartEquiv p (⟨e.val, e.property, rfl⟩ : b ⟶ Γ.tgt e.val)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun d : (bassSerreTree 𝔸 a).E ↦ (bassSerreTree 𝔸 a).src d = bassSerreVertex p)
        (fun d : (bassSerreTree 𝔸 a).E ↦ (bassSerreProjection 𝔸 a).mapE d = e.val)).symm).trans
      (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ Subtype.ext h, congrArg Subtype.val⟩)).trans
    (Equiv.sigmaFiberEquiv fun d : {d : (bassSerreTree 𝔸 a).E //
        (bassSerreTree 𝔸 a).src d = bassSerreVertex p} ↦
      (⟨(bassSerreProjection 𝔸 a).mapE d.val,
        ((bassSerreProjection 𝔸 a).map_src d.val).trans
          ((congrArg (bassSerreProjection 𝔸 a).mapV d.property).trans
            (bassSerreProjection_mapV_bassSerreVertex p))⟩ : {e : Γ.E // Γ.src e = b}))

@[simp] theorem bassSerreStarEquiv_mk_val {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : {e : Γ.E // Γ.src e = b}) (g : 𝔸.vertexGroup b) :
    (bassSerreStarEquiv p ⟨e, (g : 𝔸.vertexGroup b ⧸ _)⟩).val =
      bassSerreDart (p.cons (.vertex g)) (⟨e.val, e.property, rfl⟩ : b ⟶ Γ.tgt e.val) := by
  simp [bassSerreStarEquiv]

/-- Cardinality of the outgoing star of a vertex `y` in `X(𝔸, a)` with underlying vertex
`b = (bassSerreProjection 𝔸 a).mapV y`, as the sum of the coset cardinals `#(A_b / α_e(A_e))` over
outgoing darts `e` at `b`. -/
theorem mk_src_eq_bassSerreTree (y : (bassSerreTree 𝔸 a).V) :
    Cardinal.mk {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = y} =
      Cardinal.lift.{u} (Cardinal.sum
        fun e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y} ↦
          Cardinal.mk (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y) ⧸
            (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
              (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range)) := by
  induction y using bassSerreVertex_induction_on with | h p
  rw [bassSerreProjection_mapV_bassSerreVertex, ← Cardinal.mk_sigma, ← Cardinal.mk_uLift]
  exact Cardinal.mk_congr ((bassSerreStarEquiv p).symm.trans Equiv.ulift.symm)

/-- When `b = (bassSerreProjection 𝔸 a).mapV y` has finitely many outgoing darts in `Γ` and each
edge group image at `b` has finite index in `A_b`, the degree of `y` in `X(𝔸, a)` is the sum of the
subgroup indices `[A_b : α_e(A_e)]`. -/
theorem card_src_eq_bassSerreTree (y : (bassSerreTree 𝔸 a).V)
    [Fintype {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y}]
    [∀ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
      Finite (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y) ⧸
        (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
          (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range)] :
    Nat.card {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = y} =
      ∑ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
        (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
          (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range.index := by
  have h := @bassSerreVertex_induction_on _ _ _
    (fun y ↦
      ∀ [Fintype {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y}]
        [∀ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
          Finite (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y) ⧸
            (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
              (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range)],
        Nat.card {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = y} =
          ∑ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
            (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
              (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range.index)
    y fun p ↦ by
      rw [bassSerreProjection_mapV_bassSerreVertex]
      intro _ _
      rw [Nat.card_congr (bassSerreStarEquiv p).symm, Nat.card_sigma]
      simp_rw [Subgroup.index_eq_card]
  exact h

end General

/-! ### HNN loops -/

section Loop

variable {G : Type w} {C : Type x} [Group G] [Group C] (f g : C →* G)
  (hf : Function.Injective f) (hg : Function.Injective g)

private theorem loop_range_αArrow_true :
    ((loop f g hf hg).αArrow
      (⟨((), true), rfl, rfl⟩ :
        (SerreGraph.rose Unit).src ((), true) ⟶ (SerreGraph.rose Unit).tgt ((), true))).range =
      f.range :=
  congrArg MonoidHom.range (((loop f g hf hg).αArrow_mk ((), true)).trans (loop_α_true f g hf hg))

private theorem loop_range_αArrow_false :
    ((loop f g hf hg).αArrow
      (⟨((), false), rfl, rfl⟩ :
        (SerreGraph.rose Unit).src ((), false) ⟶ (SerreGraph.rose Unit).tgt ((), false))).range =
      g.range :=
  congrArg MonoidHom.range (((loop f g hf hg).αArrow_mk ((), false)).trans (loop_α_false f g hf hg))

private def roseUnitOutEquiv :
    Bool ≃ {e : (SerreGraph.rose Unit).E //
      (SerreGraph.rose Unit).src e = (default : (SerreGraph.rose Unit).V)} where
  toFun b := ⟨((), b), rfl⟩
  invFun e := e.val.2
  left_inv _ := rfl
  right_inv := fun ⟨⟨⟨⟩, _⟩, _⟩ ↦ rfl

/-- At a vertex `p G` of the Bass–Serre tree of `loop f g hf hg`, the outgoing darts decompose as
`(G ⧸ f.range) ⊕ (G ⧸ g.range)`, corresponding to the positive dart `((), true)` and negative dart
`((), false)` of the loop. -/
noncomputable def loopStarEquiv
    (p : (loop f g hf hg).Path
      ⟨(default : (SerreGraph.rose Unit).V)⟩ ⟨(default : (SerreGraph.rose Unit).V)⟩) :
    (G ⧸ f.range) ⊕ (G ⧸ g.range) ≃
      {d : (bassSerreTree (loop f g hf hg) default).E //
        (bassSerreTree (loop f g hf hg) default).src d = bassSerreVertex p} :=
  ((Equiv.sumComm (G ⧸ f.range) (G ⧸ g.range)).trans <|
    (Equiv.sumEquivSigmaBool (G ⧸ g.range) (G ⧸ f.range)).trans
      (Equiv.sigmaCongr roseUnitOutEquiv fun b ↦ by
        cases b
        · exact Subgroup.quotientEquivOfEq (loop_range_αArrow_false f g hf hg).symm
        · exact Subgroup.quotientEquivOfEq (loop_range_αArrow_true f g hf hg).symm)).trans
    (bassSerreStarEquiv p)

@[simp] theorem loopStarEquiv_inl_val
    (p : (loop f g hf hg).Path
      ⟨(default : (SerreGraph.rose Unit).V)⟩ ⟨(default : (SerreGraph.rose Unit).V)⟩) (x : G) :
    (loopStarEquiv f g hf hg p (Sum.inl (x : G ⧸ f.range))).val =
      bassSerreDart (p.cons (.vertex (x : (loop f g hf hg).vertexGroup default)))
        (⟨((), true), rfl, rfl⟩ :
          (default : (SerreGraph.rose Unit).V) ⟶ (SerreGraph.rose Unit).tgt ((), true)) :=
  (congrArg (fun q ↦ (bassSerreStarEquiv p ⟨roseUnitOutEquiv true, q⟩).val)
      (Subgroup.quotientEquivOfEq_mk (loop_range_αArrow_true f g hf hg).symm x)).trans
    (bassSerreStarEquiv_mk_val p (roseUnitOutEquiv true) x)

@[simp] theorem loopStarEquiv_inr_val
    (p : (loop f g hf hg).Path
      ⟨(default : (SerreGraph.rose Unit).V)⟩ ⟨(default : (SerreGraph.rose Unit).V)⟩) (x : G) :
    (loopStarEquiv f g hf hg p (Sum.inr (x : G ⧸ g.range))).val =
      bassSerreDart (p.cons (.vertex (x : (loop f g hf hg).vertexGroup default)))
        (⟨((), false), rfl, rfl⟩ :
          (default : (SerreGraph.rose Unit).V) ⟶ (SerreGraph.rose Unit).tgt ((), false)) :=
  (congrArg (fun q ↦ (bassSerreStarEquiv p ⟨roseUnitOutEquiv false, q⟩).val)
      (Subgroup.quotientEquivOfEq_mk (loop_range_αArrow_false f g hf hg).symm x)).trans
    (bassSerreStarEquiv_mk_val p (roseUnitOutEquiv false) x)

/-- When both boundary subgroups have finite index in `G`, every vertex of the Bass–Serre tree of
`loop f g hf hg` has degree `f.range.index + g.range.index`. -/
theorem card_src_eq_bassSerreTree_loop [Finite (G ⧸ f.range)] [Finite (G ⧸ g.range)]
    (x : (bassSerreTree (loop f g hf hg) default).V) :
    Nat.card {d : (bassSerreTree (loop f g hf hg) default).E //
        (bassSerreTree (loop f g hf hg) default).src d = x} =
      f.range.index + g.range.index := by
  induction x using bassSerreVertex_induction_on with | @h v p
  obtain rfl : v = default := Subsingleton.elim _ _
  rw [Nat.card_congr (loopStarEquiv f g hf hg p).symm, Nat.card_sum,
    Subgroup.index_eq_card, Subgroup.index_eq_card]

end Loop

/-! ### Amalgamated and free products over a segment -/

section Segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C]
  (f : C →* A) (g : C →* B) (hf : Function.Injective f) (hg : Function.Injective g)

private theorem segment_range_αArrow (b : SerreGraph.segment.V) :
    ((segment f g hf hg).αArrow (SerreGraph.segmentArrow b)).range =
      ((segment f g hf hg).α b).range := by
  -- `segmentArrow b` is the arrow `⟨b, rfl, rfl⟩` of the dart `b`, the argument of `αArrow_mk`.
  have h : SerreGraph.segmentArrow b = ⟨b, rfl, rfl⟩ := Subtype.ext (SerreGraph.segmentArrow_val b)
  rw [h]
  exact congrArg MonoidHom.range ((segment f g hf hg).αArrow_mk b)

private theorem segment_range_αArrow_false :
    ((segment f g hf hg).αArrow
      (SerreGraph.segmentArrow (SerreGraph.segment.src false))).range = f.range :=
  (segment_range_αArrow f g hf hg (SerreGraph.segment.src false)).trans
    (congrArg MonoidHom.range (segment_α_false f g hf hg))

private theorem segment_range_αArrow_true :
    ((segment f g hf hg).αArrow
      (SerreGraph.segmentArrow (SerreGraph.segment.src true))).range = g.range :=
  (segment_range_αArrow f g hf hg (SerreGraph.segment.src true)).trans
    (congrArg MonoidHom.range (segment_α_true f g hf hg))

private noncomputable def segmentOutStarEquiv (b : SerreGraph.segment.V)
    {v₀ : SerreGraph.segment.V} (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨b⟩) :
    (segment f g hf hg).vertexGroup b ⧸
      ((segment f g hf hg).αArrow (SerreGraph.segmentArrow b)).range ≃
      {d : (bassSerreTree (segment f g hf hg) v₀).E //
        (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} :=
  (bassSerreOutDartEquiv p (SerreGraph.segmentArrow b)).trans <|
    Equiv.subtypeEquivRight fun d ↦ and_iff_left_of_imp fun hd ↦ by
      rw [SerreGraph.segmentArrow_val]
      exact SerreGraph.segment_src_injective <|
        ((bassSerreProjection (segment f g hf hg) v₀).map_src d).trans
          ((congrArg (bassSerreProjection (segment f g hf hg) v₀).mapV hd).trans
            ((bassSerreProjection_mapV_bassSerreVertex p).trans (SerreGraph.segment_src b).symm))

private theorem segmentOutStarEquiv_mk_val (b : SerreGraph.segment.V) {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨b⟩) (x : (segment f g hf hg).vertexGroup b) :
    (segmentOutStarEquiv f g hf hg b p
      (x : (segment f g hf hg).vertexGroup b ⧸ _)).val =
      bassSerreDart (p.cons (.vertex x)) (SerreGraph.segmentArrow b) :=
  bassSerreOutDartEquiv_mk_val p (SerreGraph.segmentArrow b) x

/-- At a vertex `p A` over `false` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
correspond bijectively to the left cosets `A ⧸ f.range`. -/
noncomputable def segmentStarEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) :
    A ⧸ f.range ≃ {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} :=
  (Subgroup.quotientEquivOfEq (segment_range_αArrow_false f g hf hg).symm).trans
    (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src false) p)

@[simp] theorem segmentStarEquivFalse_mk_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) (x : A) :
    (segmentStarEquivFalse f g hf hg p (x : A ⧸ f.range)).val =
      bassSerreDart
        (p.cons (.vertex (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src false))))
        (SerreGraph.segmentArrow (SerreGraph.segment.src false)) :=
  (congrArg (fun q ↦ (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src false) p q).val)
      (Subgroup.quotientEquivOfEq_mk (segment_range_αArrow_false f g hf hg).symm x)).trans
    (segmentOutStarEquiv_mk_val f g hf hg (SerreGraph.segment.src false) p x)

/-- At a vertex `p B` over `true` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
correspond bijectively to the left cosets `B ⧸ g.range`. -/
noncomputable def segmentStarEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) :
    B ⧸ g.range ≃ {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} :=
  (Subgroup.quotientEquivOfEq (segment_range_αArrow_true f g hf hg).symm).trans
    (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src true) p)

@[simp] theorem segmentStarEquivTrue_mk_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) (x : B) :
    (segmentStarEquivTrue f g hf hg p (x : B ⧸ g.range)).val =
      bassSerreDart
        (p.cons (.vertex (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src true))))
        (SerreGraph.segmentArrow (SerreGraph.segment.src true)) :=
  (congrArg (fun q ↦ (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src true) p q).val)
      (Subgroup.quotientEquivOfEq_mk (segment_range_αArrow_true f g hf hg).symm x)).trans
    (segmentOutStarEquiv_mk_val f g hf hg (SerreGraph.segment.src true) p x)

section FreeProduct

variable [Subsingleton C]

/-- When the amalgamated subgroup `C` is trivial (`A ∗ B`), the outgoing darts at a vertex `p A`
over `false` correspond bijectively to `A`. -/
noncomputable def segmentFreeStarEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) :
    A ≃ {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} :=
  ((QuotientGroup.quotientEquivSelf A).symm.trans
    (Subgroup.quotientEquivOfEq (f.range_eq_bot_iff.mpr (Subsingleton.elim f 1)).symm)).trans
    (segmentStarEquivFalse f g hf hg p)

/-- Evaluating `segmentFreeStarEquivFalse` at `x : A` gives the dart `(p x) α_{false}(C)`. -/
@[simp] theorem segmentFreeStarEquivFalse_apply_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) (x : A) :
    (segmentFreeStarEquivFalse f g hf hg p x).val =
      bassSerreDart
        (p.cons (.vertex (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src false))))
        (SerreGraph.segmentArrow (SerreGraph.segment.src false)) :=
  (congrArg (fun q ↦ (segmentStarEquivFalse f g hf hg p q).val)
      (Subgroup.quotientEquivOfEq_mk
        (f.range_eq_bot_iff.mpr (Subsingleton.elim f 1)).symm x)).trans
    (segmentStarEquivFalse_mk_val f g hf hg p x)

/-- When the amalgamated subgroup `C` is trivial (`A ∗ B`), the outgoing darts at a vertex `p B`
over `true` correspond bijectively to `B`. -/
noncomputable def segmentFreeStarEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) :
    B ≃ {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} :=
  ((QuotientGroup.quotientEquivSelf B).symm.trans
    (Subgroup.quotientEquivOfEq (g.range_eq_bot_iff.mpr (Subsingleton.elim g 1)).symm)).trans
    (segmentStarEquivTrue f g hf hg p)

/-- Evaluating `segmentFreeStarEquivTrue` at `x : B` gives the dart `(p x) α_{true}(C)`. -/
@[simp] theorem segmentFreeStarEquivTrue_apply_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) (x : B) :
    (segmentFreeStarEquivTrue f g hf hg p x).val =
      bassSerreDart
        (p.cons (.vertex (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src true))))
        (SerreGraph.segmentArrow (SerreGraph.segment.src true)) :=
  (congrArg (fun q ↦ (segmentStarEquivTrue f g hf hg p q).val)
      (Subgroup.quotientEquivOfEq_mk
        (g.range_eq_bot_iff.mpr (Subsingleton.elim g 1)).symm x)).trans
    (segmentStarEquivTrue_mk_val f g hf hg p x)

/-- When the amalgamated subgroup `C` is trivial (`A ∗ B`), the adjacent vertices of `p A` over
`false` in the Bass–Serre tree correspond bijectively to `A`. -/
noncomputable def segmentFreeAdjacentEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) :
    A ≃ {y : (bassSerreTree (segment f g hf hg) v₀).V // Nonempty (bassSerreVertex p ⟶ y)} :=
  (segmentFreeStarEquivFalse f g hf hg p).trans
    ((bassSerreTree (segment f g hf hg) v₀).isAcyclic.starEquivAdjacent (bassSerreVertex p))

/-- Evaluating `segmentFreeAdjacentEquivFalse` at `x : A` gives `(π₁.vertexHom p x) • (p e B)`. -/
@[simp] theorem segmentFreeAdjacentEquivFalse_apply_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) (x : A) :
    (segmentFreeAdjacentEquivFalse f g hf hg p x).val =
      π₁.vertexHom p (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src false)) •
        bassSerreVertex
          (p.cons (.dart (SerreGraph.segmentArrow (SerreGraph.segment.src false)))) :=
  ((bassSerreTree (segment f g hf hg) v₀).isAcyclic.starEquivAdjacent_apply_val
      (bassSerreVertex p) (segmentFreeStarEquivFalse f g hf hg p x)).trans
    ((congrArg (bassSerreTree (segment f g hf hg) v₀).tgt
        (segmentFreeStarEquivFalse_apply_val f g hf hg p x)).trans
      ((tgt_bassSerreDart _ _).trans (vertexHom_smul_bassSerreVertex_cons_dart p _ _).symm))

/-- When the amalgamated subgroup `C` is trivial (`A ∗ B`), the adjacent vertices of `p B` over
`true` in the Bass–Serre tree correspond bijectively to `B`. -/
noncomputable def segmentFreeAdjacentEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) :
    B ≃ {y : (bassSerreTree (segment f g hf hg) v₀).V // Nonempty (bassSerreVertex p ⟶ y)} :=
  (segmentFreeStarEquivTrue f g hf hg p).trans
    ((bassSerreTree (segment f g hf hg) v₀).isAcyclic.starEquivAdjacent (bassSerreVertex p))

/-- Evaluating `segmentFreeAdjacentEquivTrue` at `x : B` gives `(π₁.vertexHom p x) • (p e A)`. -/
@[simp] theorem segmentFreeAdjacentEquivTrue_apply_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) (x : B) :
    (segmentFreeAdjacentEquivTrue f g hf hg p x).val =
      π₁.vertexHom p (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src true)) •
        bassSerreVertex
          (p.cons (.dart (SerreGraph.segmentArrow (SerreGraph.segment.src true)))) :=
  ((bassSerreTree (segment f g hf hg) v₀).isAcyclic.starEquivAdjacent_apply_val
      (bassSerreVertex p) (segmentFreeStarEquivTrue f g hf hg p x)).trans
    ((congrArg (bassSerreTree (segment f g hf hg) v₀).tgt
        (segmentFreeStarEquivTrue_apply_val f g hf hg p x)).trans
      ((tgt_bassSerreDart _ _).trans (vertexHom_smul_bassSerreVertex_cons_dart p _ _).symm))

end FreeProduct

end Segment

end TauCeti.GraphOfGroups
