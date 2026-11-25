/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Star
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index

/-!
# Concrete Bass–Serre trees

Calculations of vertex stars, adjacent vertices, degrees, and quotients of
`GraphOfGroups.bassSerreTree` on standard low-complexity graphs of groups:

* **HNN loops and Baumslag–Solitar groups (`loop`, `baumslagSolitar`)**: outgoing stars decompose
  as `(G ⧸ f.range) ⊕ (G ⧸ g.range)`, giving degree `f.range.index + g.range.index` (`|m| + |n|` for
  `baumslagSolitar m n hm hn`, and `3` for `BS(1, 2)`).
* **Amalgamated and free products (`segment`, `freeProductInt`)**: outgoing stars over `false` and
  `true` identify with `A ⧸ f.range` and `B ⧸ g.range` (with `A` and `B`, along with adjacent
  vertices, when `[Subsingleton C]`), giving cardinality `ℵ₀` at every vertex of `ℤ ∗ ℤ`.
* **Disconnected graphs (`SerreGraph.noEdge Bool`)**: `X(𝔸, false)` and its `π₁`-quotient each have
  `1` vertex while the ambient graph has `2`, witnessing recovery of `Γ.component a`.

## Main definitions

* `TauCeti.GraphOfGroups.loopStarEquiv`, `TauCeti.GraphOfGroups.segmentStarEquivFalse`,
  `TauCeti.GraphOfGroups.segmentStarEquivTrue`: outgoing star equivalences for loops and segments.
* `TauCeti.GraphOfGroups.segmentFreeStarEquivFalse`,
  `TauCeti.GraphOfGroups.segmentFreeStarEquivTrue`,
  `TauCeti.GraphOfGroups.segmentFreeAdjacentEquivFalse`,
  `TauCeti.GraphOfGroups.segmentFreeAdjacentEquivTrue`: star and adjacent-vertex equivalences for
  `A ∗ B`.
* `TauCeti.GraphOfGroups.freeProductInt`: the segment of groups for `ℤ ∗ ℤ`.

## Main results

* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_loop`,
  `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_baumslagSolitar`,
  `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_baumslagSolitar_one_two`: vertex degrees.
* `TauCeti.GraphOfGroups.mk_star_freeProductInt`,
  `TauCeti.GraphOfGroups.mk_adjacent_freeProductInt`: star and adjacent-vertex cardinalities in
  `ℤ ∗ ℤ`.
* `TauCeti.GraphOfGroups.card_bassSerreTree_noEdge_bool_V`,
  `TauCeti.GraphOfGroups.card_quotient_bassSerreTree_noEdge_bool_V`,
  `TauCeti.GraphOfGroups.isEmpty_quotient_bassSerreTree_iso_noEdge_bool`: disconnected example.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1 and §5.3.
-/

public section

universe w x

namespace TauCeti.GraphOfGroups

/-! ### HNN loops and Baumslag–Solitar groups -/

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

section BaumslagSolitar

/-- Every vertex of the Bass–Serre tree of the Baumslag–Solitar group `BS(m, n)` has degree
`|m| + |n|`. -/
theorem card_src_eq_bassSerreTree_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : (bassSerreTree (baumslagSolitar m n hm hn) default).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar m n hm hn) default).E //
        (bassSerreTree (baumslagSolitar m n hm hn) default).src d = x} =
      m.natAbs + n.natAbs := by
  have : Finite (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) m).range) :=
    Subgroup.index_ne_zero_iff_finite.1 (by simp [hm])
  have : Finite (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) n).range) :=
    Subgroup.index_ne_zero_iff_finite.1 (by simp [hn])
  exact (card_src_eq_bassSerreTree_loop
    (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom (α := Multiplicative ℤ) n)
    (zpow_left_injective hm) (zpow_left_injective hn) x).trans (by simp)

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has degree `3`. -/
theorem card_src_eq_bassSerreTree_baumslagSolitar_one_two
    (x : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero (by decide)) default).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero (by decide)) default).E //
        (bassSerreTree (baumslagSolitar 1 2 one_ne_zero (by decide)) default).src d = x} = 3 :=
  card_src_eq_bassSerreTree_baumslagSolitar 1 2 one_ne_zero (by decide) x

end BaumslagSolitar

/-! ### Amalgamated and free products over a segment -/

section Segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C]
  (f : C →* A) (g : C →* B) (hf : Function.Injective f) (hg : Function.Injective g)

private theorem segment_range_αArrow (b : SerreGraph.segment.V) :
    ((segment f g hf hg).αArrow (SerreGraph.segmentArrow b)).range =
      (segmentMaps f g hf hg b).range :=
  congrArg MonoidHom.range (αArrow_segmentArrow f g hf hg b)

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
  (Subgroup.quotientEquivOfEq <|
    ((segment_range_αArrow f g hf hg (SerreGraph.segment.src false)).trans
      (congrArg MonoidHom.range (segmentMaps_false f g hf hg))).symm).trans
    (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src false) p)

@[simp] theorem segmentStarEquivFalse_mk_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) (x : A) :
    (segmentStarEquivFalse f g hf hg p (x : A ⧸ f.range)).val =
      bassSerreDart
        (p.cons (.vertex (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src false))))
        (SerreGraph.segmentArrow (SerreGraph.segment.src false)) :=
  (congrArg (fun q ↦ (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src false) p q).val)
      (Subgroup.quotientEquivOfEq_mk
        ((segment_range_αArrow f g hf hg (SerreGraph.segment.src false)).trans
          (congrArg MonoidHom.range (segmentMaps_false f g hf hg))).symm x)).trans
    (segmentOutStarEquiv_mk_val f g hf hg (SerreGraph.segment.src false) p x)

/-- At a vertex `p B` over `true` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
correspond bijectively to the left cosets `B ⧸ g.range`. -/
noncomputable def segmentStarEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) :
    B ⧸ g.range ≃ {d : (bassSerreTree (segment f g hf hg) v₀).E //
      (bassSerreTree (segment f g hf hg) v₀).src d = bassSerreVertex p} :=
  (Subgroup.quotientEquivOfEq <|
    ((segment_range_αArrow f g hf hg (SerreGraph.segment.src true)).trans
      (congrArg MonoidHom.range (segmentMaps_true f g hf hg))).symm).trans
    (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src true) p)

@[simp] theorem segmentStarEquivTrue_mk_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) (x : B) :
    (segmentStarEquivTrue f g hf hg p (x : B ⧸ g.range)).val =
      bassSerreDart
        (p.cons (.vertex (x : (segment f g hf hg).vertexGroup (SerreGraph.segment.src true))))
        (SerreGraph.segmentArrow (SerreGraph.segment.src true)) :=
  (congrArg (fun q ↦ (segmentOutStarEquiv f g hf hg (SerreGraph.segment.src true) p q).val)
      (Subgroup.quotientEquivOfEq_mk
        ((segment_range_αArrow f g hf hg (SerreGraph.segment.src true)).trans
          (congrArg MonoidHom.range (segmentMaps_true f g hf hg))).symm x)).trans
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

section FreeProductInt

/-- The segment of groups for the free product `ℤ ∗ ℤ`, amalgamating two copies of
`Multiplicative ℤ` over the trivial group `PUnit`. -/
abbrev freeProductInt : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  segment (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the outgoing star of every vertex has cardinality `ℵ₀`. -/
theorem mk_star_freeProductInt (v₀ : SerreGraph.segment.V)
    (x : (bassSerreTree freeProductInt v₀).V) :
    Cardinal.mk {d : (bassSerreTree freeProductInt v₀).E //
        (bassSerreTree freeProductInt v₀).src d = x} = Cardinal.aleph0 := by
  induction x using bassSerreVertex_induction_on with | @h v p
  rw [← Cardinal.mk_int]
  cases v
  · exact Cardinal.mk_congr ((segmentFreeStarEquivFalse (1 : PUnit →* Multiplicative ℤ)
      (1 : PUnit →* Multiplicative ℤ) _ _ p).symm.trans Multiplicative.toAdd)
  · exact Cardinal.mk_congr ((segmentFreeStarEquivTrue (1 : PUnit →* Multiplicative ℤ)
      (1 : PUnit →* Multiplicative ℤ) _ _ p).symm.trans Multiplicative.toAdd)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the set of adjacent vertices of every vertex has cardinality
`ℵ₀`. -/
theorem mk_adjacent_freeProductInt (v₀ : SerreGraph.segment.V)
    (x : (bassSerreTree freeProductInt v₀).V) :
    Cardinal.mk {y : (bassSerreTree freeProductInt v₀).V // Nonempty (x ⟶ y)} =
      Cardinal.aleph0 :=
  (Cardinal.mk_congr
    ((bassSerreTree freeProductInt v₀).isAcyclic.starEquivAdjacent x).symm).trans
    (mk_star_freeProductInt v₀ x)

end FreeProductInt

/-! ### Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- On `SerreGraph.noEdge Bool`, the Bass–Serre tree at `false` has `1` vertex. -/
theorem card_bassSerreTree_noEdge_bool_V :
    Nat.card (bassSerreTree (trivial (SerreGraph.noEdge.{0, 0} Bool)) false).V = 1 :=
  Nat.card_unique

/-- On `SerreGraph.noEdge Bool`, the `π₁`-quotient of the Bass–Serre tree at `false` has `1`
vertex. -/
theorem card_quotient_bassSerreTree_noEdge_bool_V :
    Nat.card (bassSerreTree (trivial (SerreGraph.noEdge.{0, 0} Bool)) false).quotient.V = 1 :=
  Nat.card_unique

/-- On the disconnected graph `SerreGraph.noEdge Bool`, the quotient of the Bass–Serre tree by `π₁`
is not isomorphic to `SerreGraph.noEdge Bool`: it recovers only the connected component of the base
vertex. -/
theorem isEmpty_quotient_bassSerreTree_iso_noEdge_bool :
    IsEmpty ((bassSerreTree (trivial (SerreGraph.noEdge.{0, 0} Bool)) false).quotient.Iso
      (SerreGraph.noEdge.{0, 0} Bool)) :=
  ⟨fun φ ↦ by
    have h := Nat.card_congr φ.equivV
    rw [card_quotient_bassSerreTree_noEdge_bool_V] at h
    have h2 : Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_bool
    omega⟩

end Disconnected

end TauCeti.GraphOfGroups
