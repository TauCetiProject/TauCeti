/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.SetTheory.Cardinal.Basic
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic

/-!
# Concrete Bass–Serre trees

Calculations of vertex stars, degrees, and quotients of `GraphOfGroups.bassSerreTree` on standard
low-complexity graphs of groups:

* **HNN loops and Baumslag–Solitar groups (`GraphOfGroups.loop`, `GraphOfGroups.baumslagSolitar`)**:
  at any vertex of the Bass–Serre tree of `loop f g hf hg`, the outgoing star decomposes as
  `(G ⧸ f.range) ⊕ (G ⧸ g.range)`, so every vertex has degree `f.range.index + g.range.index` when
  both boundary subgroups have finite index. For `baumslagSolitar m n hm hn`, every vertex has
  degree `|m| + |n|`; in particular, the Bass–Serre tree of `BS(1, 2)` is `3`-regular.
* **Amalgamated and free products (`GraphOfGroups.segment`)**: at vertices projecting to `false`
  (respectively `true`), the outgoing star identifies with `A ⧸ f.range` (respectively
  `B ⧸ g.range`). When the amalgamated subgroup `C` is trivial (`A ∗ B`), the neighbour vertices of
  the base vertex `1 · A` correspond bijectively to `A` via `a ↦ a • (e · B)`. Specializing to
  `ℤ ∗ ℤ`, both the outgoing star and the neighbour set of `1 · ℤ` have countably infinite
  cardinality `ℵ₀`.
* **Disconnected graphs (`SerreGraph.noEdge Bool`)**: on two isolated vertices, the Bass–Serre tree
  at `false` and its `π₁`-quotient each have `1` vertex while the ambient graph has `2`, witnessing
  that `X(𝔸, v₀) / π₁(𝔸, v₀)` recovers `Γ.component v₀` rather than all of `Γ`.

## Main definitions

* `TauCeti.GraphOfGroups.loopStarEquiv`: outgoing star of a vertex in the Bass–Serre tree of an HNN
  loop as `(G ⧸ f.range) ⊕ (G ⧸ g.range)`.
* `TauCeti.GraphOfGroups.segmentStarEquivFalse`, `TauCeti.GraphOfGroups.segmentStarEquivTrue`:
  outgoing stars in the Bass–Serre tree of a segment of groups as `A ⧸ f.range` and `B ⧸ g.range`.
* `TauCeti.GraphOfGroups.segmentFreeStarEquivFalse`,
  `TauCeti.GraphOfGroups.segmentFreeNeighbourEquivFalse`: when `[Subsingleton C]`, the outgoing
  darts and adjacent vertices of `1 · A` in `A ∗ B` correspond bijectively to `A`.
* `TauCeti.GraphOfGroups.freeProductInt`: the segment of groups for `ℤ ∗ ℤ`.

## Main results

* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_loop`: finite vertex degree
  `f.range.index + g.range.index` for an HNN loop.
* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_baumslagSolitar`,
  `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_baumslagSolitar_one_two`: every vertex of the
  Bass–Serre tree of `BS(m, n)` has degree `|m| + |n|`, and `3` for `BS(1, 2)`.
* `TauCeti.GraphOfGroups.mk_star_freeProduct_int`,
  `TauCeti.GraphOfGroups.mk_neighbours_freeProduct_int`: in `ℤ ∗ ℤ`, the outgoing star and
  neighbour set of the base vertex have cardinality `ℵ₀`.
* `TauCeti.GraphOfGroups.isEmpty_quotient_bassSerreTree_iso_noEdge_bool`: the quotient of the
  Bass–Serre tree over `SerreGraph.noEdge Bool` is not isomorphic to `SerreGraph.noEdge Bool`.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1 and §5.3.
-/

public section

universe w x

namespace TauCeti

namespace GraphOfGroups

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
  invFun e := e.1.2
  left_inv _ := rfl
  right_inv := fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl

/-- At a vertex `p G` of the Bass–Serre tree of `loop f g hf hg`, the outgoing darts decompose as
`(G ⧸ f.range) ⊕ (G ⧸ g.range)`, corresponding to the positive dart `((), true)` and negative dart
`((), false)` of the loop. -/
noncomputable def loopStarEquiv
    (p : (loop f g hf hg).Path
      ⟨(default : (SerreGraph.rose Unit).V)⟩ ⟨(default : (SerreGraph.rose Unit).V)⟩) :
    (G ⧸ f.range) ⊕ (G ⧸ g.range) ≃
      {d : ((loop f g hf hg).bassSerreTree default).E //
        ((loop f g hf hg).bassSerreTree default).src d = bassSerreVertex p} :=
  ((Equiv.sumComm (G ⧸ f.range) (G ⧸ g.range)).trans <|
    (Equiv.sumEquivSigmaBool (G ⧸ g.range) (G ⧸ f.range)).trans
      (Equiv.sigmaCongr roseUnitOutEquiv fun b => by
        cases b
        · exact Subgroup.quotientEquivOfEq (loop_range_αArrow_false f g hf hg).symm
        · exact Subgroup.quotientEquivOfEq (loop_range_αArrow_true f g hf hg).symm)).trans
    (bassSerreStarEquiv p)

@[simp] theorem loopStarEquiv_inl_val
    (p : (loop f g hf hg).Path
      ⟨(default : (SerreGraph.rose Unit).V)⟩ ⟨(default : (SerreGraph.rose Unit).V)⟩) (x : G) :
    (loopStarEquiv f g hf hg p (Sum.inl (x : G ⧸ f.range))).1 =
      bassSerreDart
        (p.cons (Letter.vertex (x : (loop f g hf hg).vertexGroup default)))
        (⟨((), true), rfl, rfl⟩ :
          (default : (SerreGraph.rose Unit).V) ⟶ (SerreGraph.rose Unit).tgt ((), true)) :=
  (congrArg (fun q => (bassSerreStarEquiv p ⟨roseUnitOutEquiv true, q⟩).1)
      (Subgroup.quotientEquivOfEq_mk (loop_range_αArrow_true f g hf hg).symm x)).trans
    (bassSerreStarEquiv_mk_val p (roseUnitOutEquiv true) x)

@[simp] theorem loopStarEquiv_inr_val
    (p : (loop f g hf hg).Path
      ⟨(default : (SerreGraph.rose Unit).V)⟩ ⟨(default : (SerreGraph.rose Unit).V)⟩) (x : G) :
    (loopStarEquiv f g hf hg p (Sum.inr (x : G ⧸ g.range))).1 =
      bassSerreDart
        (p.cons (Letter.vertex (x : (loop f g hf hg).vertexGroup default)))
        (⟨((), false), rfl, rfl⟩ :
          (default : (SerreGraph.rose Unit).V) ⟶ (SerreGraph.rose Unit).tgt ((), false)) :=
  (congrArg (fun q => (bassSerreStarEquiv p ⟨roseUnitOutEquiv false, q⟩).1)
      (Subgroup.quotientEquivOfEq_mk (loop_range_αArrow_false f g hf hg).symm x)).trans
    (bassSerreStarEquiv_mk_val p (roseUnitOutEquiv false) x)

/-- When both boundary subgroups have finite index in `G`, every vertex of the Bass–Serre tree of
`loop f g hf hg` has degree `f.range.index + g.range.index`. -/
theorem card_src_eq_bassSerreTree_loop [Finite (G ⧸ f.range)] [Finite (G ⧸ g.range)]
    (x : ((loop f g hf hg).bassSerreTree default).V) :
    Nat.card {d : ((loop f g hf hg).bassSerreTree default).E //
        ((loop f g hf hg).bassSerreTree default).src d = x} =
      f.range.index + g.range.index := by
  induction x using bassSerreVertex_induction with | @h v p
  obtain rfl : v = default := Subsingleton.elim _ _
  rw [Nat.card_congr (loopStarEquiv f g hf hg p).symm, Nat.card_sum,
    Subgroup.index_eq_card, Subgroup.index_eq_card]

end Loop

section BaumslagSolitar

/-- Every vertex of the Bass–Serre tree of the Baumslag–Solitar group `BS(m, n)` has degree
`|m| + |n|`. -/
theorem card_src_eq_bassSerreTree_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : ((baumslagSolitar m n hm hn).bassSerreTree default).V) :
    Nat.card {d : ((baumslagSolitar m n hm hn).bassSerreTree default).E //
        ((baumslagSolitar m n hm hn).bassSerreTree default).src d = x} =
      m.natAbs + n.natAbs := by
  have hidx (k : ℤ) : (zpowGroupHom (α := Multiplicative ℤ) k).range.index = k.natAbs := by
    have hrange : (zpowGroupHom (α := Multiplicative ℤ) k).range =
        (AddSubgroup.zmultiples k).toSubgroup := by
      ext a
      rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
      refine ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, ?_⟩, fun ⟨j, hj⟩ => ⟨Multiplicative.ofAdd j, ?_⟩⟩
      · rw [← hc, zpowGroupHom_apply, toAdd_zpow]
        simpa only [zsmul_eq_mul, Int.cast_id] using Int.mul_comm c.toAdd k
      · apply Multiplicative.toAdd.injective
        rw [zpowGroupHom_apply, toAdd_zpow, toAdd_ofAdd, ← hj]
        simpa only [zsmul_eq_mul, Int.cast_id] using Int.mul_comm k j
    rw [hrange, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  have : Finite (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) m).range) :=
    Subgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; exact Int.natAbs_ne_zero.2 hm)
  have : Finite (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) n).range) :=
    Subgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; exact Int.natAbs_ne_zero.2 hn)
  exact (card_src_eq_bassSerreTree_loop
    (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom (α := Multiplicative ℤ) n)
    (zpow_left_injective hm) (zpow_left_injective hn) x).trans
    (by rw [hidx, hidx])

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has degree `3`. -/
theorem card_src_eq_bassSerreTree_baumslagSolitar_one_two
    (x : ((baumslagSolitar 1 2 one_ne_zero (by decide)).bassSerreTree default).V) :
    Nat.card {d : ((baumslagSolitar 1 2 one_ne_zero (by decide)).bassSerreTree default).E //
        ((baumslagSolitar 1 2 one_ne_zero (by decide)).bassSerreTree default).src d = x} = 3 :=
  card_src_eq_bassSerreTree_baumslagSolitar 1 2 one_ne_zero (by decide) x

end BaumslagSolitar

/-! ### Amalgamated and free products over a segment -/

section Segment

variable {A B : Type w} {C : Type x} [Group A] [Group B] [Group C]
  (f : C →* A) (g : C →* B) (hf : Function.Injective f) (hg : Function.Injective g)

private theorem segment_range_αArrow_false :
    ((segment f g hf hg).αArrow
      (⟨false, rfl, rfl⟩ :
        SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false)).range = f.range :=
  congrArg MonoidHom.range (((segment f g hf hg).αArrow_mk false).trans (segment_α_false f g hf hg))

private theorem segment_range_αArrow_true :
    ((segment f g hf hg).αArrow
      (⟨true, rfl, rfl⟩ :
        SerreGraph.segment.src true ⟶ SerreGraph.segment.tgt true)).range = g.range :=
  congrArg MonoidHom.range (((segment f g hf hg).αArrow_mk true).trans (segment_α_true f g hf hg))

/-- At a vertex `p A` over `false` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
correspond bijectively to the left cosets `A ⧸ f.range`. -/
noncomputable def segmentStarEquivFalse {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) :
    A ⧸ f.range ≃
      {d : ((segment f g hf hg).bassSerreTree v₀).E //
        ((segment f g hf hg).bassSerreTree v₀).src d = bassSerreVertex p} :=
  ((Subgroup.quotientEquivOfEq (segment_range_αArrow_false f g hf hg).symm).trans
    (bassSerreOutDartEquiv p
      (⟨false, rfl, rfl⟩ :
        SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false))).trans
    { toFun d := ⟨d.1, d.2.1⟩
      invFun d := ⟨d.1, d.2, by
        have h := bassSerreDartProj_src d.1
        rw [d.2, bassSerreVertexProj_bassSerreVertex] at h
        exact h⟩
      left_inv _ := rfl
      right_inv _ := rfl }

@[simp] theorem segmentStarEquivFalse_mk_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src false⟩) (x : A) :
    (segmentStarEquivFalse f g hf hg p (x : A ⧸ f.range)).1 =
      bassSerreDart
        (p.cons (Letter.vertex (x : (segment f g hf hg).vertexGroup
          (SerreGraph.segment.src false))))
        (⟨false, rfl, rfl⟩ : SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false) :=
  (congrArg (fun q => (bassSerreOutDartEquiv p
        (⟨false, rfl, rfl⟩ : SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false) q).1)
      (Subgroup.quotientEquivOfEq_mk (segment_range_αArrow_false f g hf hg).symm x)).trans
    (bassSerreOutDartEquiv_mk_val p _ x)

/-- At a vertex `p B` over `true` in the Bass–Serre tree of `segment f g hf hg`, the outgoing darts
correspond bijectively to the left cosets `B ⧸ g.range`. -/
noncomputable def segmentStarEquivTrue {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) :
    B ⧸ g.range ≃
      {d : ((segment f g hf hg).bassSerreTree v₀).E //
        ((segment f g hf hg).bassSerreTree v₀).src d = bassSerreVertex p} :=
  ((Subgroup.quotientEquivOfEq (segment_range_αArrow_true f g hf hg).symm).trans
    (bassSerreOutDartEquiv p
      (⟨true, rfl, rfl⟩ :
        SerreGraph.segment.src true ⟶ SerreGraph.segment.tgt true))).trans
    { toFun d := ⟨d.1, d.2.1⟩
      invFun d := ⟨d.1, d.2, by
        have h := bassSerreDartProj_src d.1
        rw [d.2, bassSerreVertexProj_bassSerreVertex] at h
        exact h⟩
      left_inv _ := rfl
      right_inv _ := rfl }

@[simp] theorem segmentStarEquivTrue_mk_val {v₀ : SerreGraph.segment.V}
    (p : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.src true⟩) (x : B) :
    (segmentStarEquivTrue f g hf hg p (x : B ⧸ g.range)).1 =
      bassSerreDart
        (p.cons (Letter.vertex (x : (segment f g hf hg).vertexGroup
          (SerreGraph.segment.src true))))
        (⟨true, rfl, rfl⟩ : SerreGraph.segment.src true ⟶ SerreGraph.segment.tgt true) :=
  (congrArg (fun q => (bassSerreOutDartEquiv p
        (⟨true, rfl, rfl⟩ : SerreGraph.segment.src true ⟶ SerreGraph.segment.tgt true) q).1)
      (Subgroup.quotientEquivOfEq_mk (segment_range_αArrow_true f g hf hg).symm x)).trans
    (bassSerreOutDartEquiv_mk_val p _ x)

section FreeProduct

variable [Subsingleton C]

/-- When the amalgamated subgroup `C` is trivial (`A ∗ B`), the outgoing darts at the base vertex
`1 · A` correspond bijectively to `A`. -/
noncomputable def segmentFreeStarEquivFalse :
    A ≃ {d : ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).E //
      ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).src d =
        (segment f g hf hg).bassSerreBase (SerreGraph.segment.src false)} :=
  ((Equiv.ofBijective (fun x : A => (x : A ⧸ f.range))
    ⟨fun x₁ x₂ h => by
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (QuotientGroup.eq.1 h)
      rw [Subsingleton.elim c 1, map_one] at hc
      exact inv_mul_eq_one.1 hc.symm,
    fun q => Quotient.inductionOn q fun x => ⟨x, rfl⟩⟩).trans
    (segmentStarEquivFalse f g hf hg .nil)).trans
    { toFun d := ⟨d.1, d.2.trans bassSerreVertex_nil⟩
      invFun d := ⟨d.1, d.2.trans bassSerreVertex_nil.symm⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- Evaluating `segmentFreeStarEquivFalse` at `x : A` gives the dart represented by `x` and the
positive edge of `segment`. -/
theorem segmentFreeStarEquivFalse_apply_val (x : A) :
    (segmentFreeStarEquivFalse f g hf hg x).1 =
      bassSerreDart
        (Path.ofVertex (𝔸 := segment f g hf hg) (a := SerreGraph.segment.src false) x)
        (⟨false, rfl, rfl⟩ : SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false) :=
  (segmentStarEquivFalse_mk_val f g hf hg .nil x).trans
    (congrArg (fun q => bassSerreDart q
        (⟨false, rfl, rfl⟩ : SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false))
      (Path.ofVertex_eq_nil_cons (𝔸 := segment f g hf hg)
        (a := SerreGraph.segment.src false) x).symm)

/-- When the amalgamated subgroup `C` is trivial (`A ∗ B`), the adjacent vertices of the base vertex
`1 · A` in the Bass–Serre tree are the translates `a • (e · B)` for `a : A`. -/
noncomputable def segmentFreeNeighbourEquivFalse :
    A ≃ {y : ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).V //
      ∃ d : ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).E,
        ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).src d =
          (segment f g hf hg).bassSerreBase (SerreGraph.segment.src false) ∧
          ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).tgt d = y} :=
  (segmentFreeStarEquivFalse f g hf hg).trans <|
    Equiv.ofBijective
      (fun d =>
        ⟨((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).tgt d.1,
          d.1, d.2, rfl⟩)
      ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ h => Subtype.ext <|
        ((segment f g hf hg).bassSerreTree (SerreGraph.segment.src false)).isAcyclic
          |>.eq_of_src_eq_of_tgt_eq (h₁.trans h₂.symm) (congrArg Subtype.val h),
      fun ⟨_, d, hsrc, htgt⟩ => ⟨⟨d, hsrc⟩, Subtype.ext htgt⟩⟩

/-- Evaluating `segmentFreeNeighbourEquivFalse` at `x : A` gives the translate `x • (e · B)`. -/
theorem segmentFreeNeighbourEquivFalse_apply_val (x : A) :
    (segmentFreeNeighbourEquivFalse f g hf hg x).1 =
      π₁.vertexHom (𝔸 := segment f g hf hg)
          (Quiver.Path.nil : (segment f g hf hg).Path
            ⟨SerreGraph.segment.src false⟩ ⟨SerreGraph.segment.src false⟩) x •
        bassSerreVertex (Path.ofDart (𝔸 := segment f g hf hg)
          (⟨false, rfl, rfl⟩ : SerreGraph.segment.src false ⟶ SerreGraph.segment.tgt false)) := by
  let v₀ : SerreGraph.segment.V := SerreGraph.segment.src false
  let e₀ : v₀ ⟶ SerreGraph.segment.tgt false := ⟨false, rfl, rfl⟩
  let px : (segment f g hf hg).Path ⟨v₀⟩ ⟨v₀⟩ :=
    Path.ofVertex (𝔸 := segment f g hf hg) (a := v₀) x
  let pe : (segment f g hf hg).Path ⟨v₀⟩ ⟨SerreGraph.segment.tgt false⟩ :=
    Path.ofDart (𝔸 := segment f g hf hg) e₀
  have hrhs :
      π₁.vertexHom (𝔸 := segment f g hf hg)
          (Quiver.Path.nil : (segment f g hf hg).Path ⟨v₀⟩ ⟨v₀⟩) x • bassSerreVertex pe =
        bassSerreVertex (px.cons (Letter.dart e₀)) :=
    (congrArg (· • bassSerreVertex pe)
      (π₁.vertexHom_nil_apply (𝔸 := segment f g hf hg) (a := v₀) x)).trans
      ((mk_smul_bassSerreVertex px pe).trans
        (congrArg bassSerreVertex (Path.comp_ofDart px e₀)))
  exact (congrArg ((segment f g hf hg).bassSerreTree v₀).tgt
      (segmentFreeStarEquivFalse_apply_val f g hf hg x)).trans
    ((tgt_bassSerreDart px e₀).trans hrhs.symm)

end FreeProduct

end Segment

section FreeProductInt

/-- The segment of groups for the free product `ℤ ∗ ℤ`, amalgamating two copies of
`Multiplicative ℤ` over the trivial group `PUnit`. -/
def freeProductInt : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  segment (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the outgoing star of the base vertex `1 · ℤ` has countably
infinite cardinality `ℵ₀`. -/
theorem mk_star_freeProduct_int :
    Cardinal.mk {d : (freeProductInt.bassSerreTree (SerreGraph.segment.src false)).E //
        (freeProductInt.bassSerreTree (SerreGraph.segment.src false)).src d =
          freeProductInt.bassSerreBase (SerreGraph.segment.src false)} = Cardinal.aleph0 := by
  rw [← Cardinal.mk_int]
  exact Cardinal.mk_congr
    ((segmentFreeStarEquivFalse (1 : PUnit →* Multiplicative ℤ)
      (1 : PUnit →* Multiplicative ℤ) _ _).symm.trans Multiplicative.toAdd)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the set of neighbour vertices `a ^ k • ⟨b⟩` of the base
vertex `⟨a⟩` has countably infinite cardinality `ℵ₀`. -/
theorem mk_neighbours_freeProduct_int :
    Cardinal.mk {y : (freeProductInt.bassSerreTree (SerreGraph.segment.src false)).V //
        ∃ d : (freeProductInt.bassSerreTree (SerreGraph.segment.src false)).E,
          (freeProductInt.bassSerreTree (SerreGraph.segment.src false)).src d =
            freeProductInt.bassSerreBase (SerreGraph.segment.src false) ∧
            (freeProductInt.bassSerreTree (SerreGraph.segment.src false)).tgt d = y} =
      Cardinal.aleph0 := by
  rw [← Cardinal.mk_int]
  exact Cardinal.mk_congr
    ((segmentFreeNeighbourEquivFalse (1 : PUnit →* Multiplicative ℤ)
      (1 : PUnit →* Multiplicative ℤ) _ _).symm.trans Multiplicative.toAdd)

end FreeProductInt

/-! ### Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- On the graph `SerreGraph.noEdge Bool` of two isolated vertices, the Bass–Serre tree at `false`
has `1` vertex. -/
theorem card_bassSerreTree_noEdge_bool :
    Nat.card ((trivial (SerreGraph.noEdge.{0, 0} Bool)).bassSerreTree false).V = 1 :=
  Nat.card_unique

/-- On `SerreGraph.noEdge Bool`, the `π₁`-quotient of the Bass–Serre tree at `false` has `1`
vertex, whereas the ambient graph has `2`. -/
theorem card_quotient_bassSerreTree_noEdge_bool :
    Nat.card ((trivial (SerreGraph.noEdge.{0, 0} Bool)).bassSerreTree false).quotient.V = 1 :=
  Nat.card_unique

/-- On the disconnected graph `SerreGraph.noEdge Bool`, the quotient of the Bass–Serre tree by `π₁`
is not isomorphic to `SerreGraph.noEdge Bool`: it recovers only the connected component of the base
vertex. -/
theorem isEmpty_quotient_bassSerreTree_iso_noEdge_bool :
    IsEmpty (((trivial (SerreGraph.noEdge.{0, 0} Bool)).bassSerreTree false).quotient.Iso
      (SerreGraph.noEdge.{0, 0} Bool)) :=
  ⟨fun φ => by
    have h := Nat.card_congr φ.equivV
    rw [card_quotient_bassSerreTree_noEdge_bool] at h
    have h2 : Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_bool
    omega⟩

end Disconnected

end GraphOfGroups

end TauCeti
