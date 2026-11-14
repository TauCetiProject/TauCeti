/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Stabilizers
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Concrete examples of Bass–Serre trees

This file specializes the Bass–Serre tree `GraphOfGroups.bassSerreTree` to concrete graphs of
groups and compares it with the naive quotient of paths by homotopy alone.

* **Free products** (`freeProduct A B`): over the segment with vertex groups `A`, `B` and trivial
  edge group, the star of `baseVertex` is in bijection with `A` (`freeProductBaseStarEquiv`). For
  `ℤ ∗ ℤ` (`freeProductZ`), the star and neighbour set of the base vertex have cardinal `ℵ₀`, with
  neighbours `(π₁.vertexHom .nil (ofAdd k)) • vertexMk (Path.ofDart _)` for `k : ℤ`
  (`bassSerreTree_free_product`).
* **Baumslag–Solitar groups** (`baumslagSolitar m n hm hn`): every vertex of the Bass–Serre tree
  has local degree `m.natAbs + n.natAbs` (`natCard_star_baumslagSolitar`). For `BS(1, 2)`
  (`baumslagSolitar12`) the two boundary indices are `1` and `2` and every vertex has degree `3`
  (`bassSerreTree_BS12`).
* **Disconnected edgeless graph** (`bassSerreTree_trivial_noEdge_bool`): over two isolated vertices
  with trivial groups, `bassSerreTree` and its quotient have `1` vertex while the ambient graph has
  `2`, and no `𝔸`-path joins the two vertices.
* **Why the right coset relation is essential** (`bassSerreTree_not_quotient_paths`): quotienting
  `𝔸`-paths by homotopy alone yields a `π₁(𝔸, v₀)`-set whose fibre over `baseVertex` is in
  bijection with `A_{v₀}` and all of whose stabilizers are trivial rather than `p A_v p⁻¹`.

## Main declarations

* `TauCeti.GraphOfGroups.freeProduct`, `TauCeti.GraphOfGroups.freeProductBaseStarEquiv`,
  `TauCeti.GraphOfGroups.bassSerreTree_free_product`.
* `TauCeti.GraphOfGroups.natCard_star_baumslagSolitar`,
  `TauCeti.GraphOfGroups.bassSerreTree_BS12`.
* `TauCeti.GraphOfGroups.bassSerreTree_trivial_noEdge_bool`.
* `TauCeti.GraphOfGroups.bassSerreTree_not_quotient_paths`.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1, §5.1, and §5.3.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

/-! ### Free products `A ∗ B` and `ℤ ∗ ℤ` -/

section FreeProduct

/-- The graph of groups of a free product `A ∗ B`: the segment with vertex groups `A` at `false`
and `B` at `true` and trivial edge group. -/
@[expose] def freeProduct (A B : Type w) [Group A] [Group B] :
    GraphOfGroups.{0, 0, w, 0} SerreGraph.segment :=
  segment (1 : PUnit →* A) (1 : PUnit →* B) (Function.injective_of_subsingleton _)
    (Function.injective_of_subsingleton _)

private instance : Unique {e : SerreGraph.segment.E // SerreGraph.segment.src e = false} where
  default := ⟨false, rfl⟩
  uniq := fun ⟨_, hb⟩ => Subtype.ext hb

/-- In `freeProduct A B`, the star of `baseVertex` (at `false`, with vertex group `A`) is in
bijection with `A`, with inverse sending `a : A` to `dartMk false (Path.ofVertex a)`. -/
noncomputable def freeProductBaseStarEquiv (A B : Type w) [Group A] [Group B] :
    {y : ((freeProduct A B).bassSerreTree (false : SerreGraph.segment.V)).E //
        ((freeProduct A B).bassSerreTree (false : SerreGraph.segment.V)).src y =
          baseVertex (freeProduct A B) (false : SerreGraph.segment.V)} ≃ A :=
  have hbase : baseVertex (freeProduct A B) (false : SerreGraph.segment.V) =
      vertexMk (𝔸 := freeProduct A B) (v₀ := (false : SerreGraph.segment.V)) Quiver.Path.nil :=
    baseVertex_def
  have hbot : ((freeProduct A B).α (false : SerreGraph.segment.E)).range = (⊥ : Subgroup A) := by
    have hα : (freeProduct A B).α (false : SerreGraph.segment.E) = (1 : PUnit →* A) :=
      segment_α_false _ _ _ _
    exact (congrArg MonoidHom.range hα).trans
      (eq_bot_iff.mpr fun _ ⟨_, hx⟩ => Subgroup.mem_bot.mpr hx.symm)
  ((Equiv.cast (congrArg
      (fun z => {y // ((freeProduct A B).bassSerreTree (false : SerreGraph.segment.V)).src y = z})
      hbase)).trans
    (starEquiv (𝔸 := freeProduct A B) (v₀ := (false : SerreGraph.segment.V))
      Quiver.Path.nil)).trans <|
      (Equiv.uniqueSigma _).trans <|
        (Equiv.cast (congrArg (fun H : Subgroup A => A ⧸ H) hbot)).trans
          (QuotientGroup.quotientBot (G := A)).toEquiv

private theorem tgt_injective_on_star {Γ : SerreGraph.{u, v}}
    {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V} (z : (𝔸.bassSerreTree v₀).V) :
    Function.Injective
      (fun y : {y : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src y = z} =>
        (𝔸.bassSerreTree v₀).tgt y.1) := by
  rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ht
  apply Subtype.ext
  let f₁ : Quiver.Hom ((𝔸.bassSerreTree v₀).src y₁) ((𝔸.bassSerreTree v₀).tgt y₁) :=
    ⟨y₁, rfl, rfl⟩
  let f₂ : Quiver.Hom ((𝔸.bassSerreTree v₀).src y₁) ((𝔸.bassSerreTree v₀).tgt y₁) :=
    ⟨y₂, hy₂.trans hy₁.symm, ht.symm⟩
  have hp := ((𝔸.bassSerreTree v₀).isTree.isAcyclic).eq_of_isReduced
    (SerreGraph.Path.isReduced_toPath _ f₁) (SerreGraph.Path.isReduced_toPath _ f₂)
  have hd := congrArg (SerreGraph.Path.darts (𝔸.bassSerreTree v₀).toSerreGraph) hp
  simpa [f₁, f₂] using hd

/-- The graph of groups of the free product `ℤ ∗ ℤ`. -/
abbrev freeProductZ : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  freeProduct (Multiplicative ℤ) (Multiplicative ℤ)

private theorem freeProductZ_smul_neighbour (k : ℤ) :
    π₁.vertexHom (𝔸 := freeProductZ) (a := false) (b := false) Quiver.Path.nil
        (Multiplicative.ofAdd k) •
      vertexMk (𝔸 := freeProductZ) (v₀ := false)
        (Path.ofDart (SerreGraph.segment.dart false)) =
      (freeProductZ.bassSerreTree false).tgt
        (dartMk (𝔸 := freeProductZ) (v₀ := false) false
          (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k))) :=
  (congrArg (· • _) (π₁.vertexHom_nil_apply _)).trans <|
    (mk_smul_vertexMk _ _).trans <|
      (congrArg vertexMk (Path.comp_ofDart _ _)).trans (tgt_dartMk _ _).symm

private theorem freeProductZ_neighbour_injective :
    Function.Injective
      (fun k : ℤ =>
        π₁.vertexHom (𝔸 := freeProductZ) (a := false) (b := false) Quiver.Path.nil
          (Multiplicative.ofAdd k) •
          vertexMk (𝔸 := freeProductZ) (v₀ := false)
            (Path.ofDart (SerreGraph.segment.dart false))) := by
  intro k₁ k₂ hk
  have hk' :=
    (freeProductZ_smul_neighbour k₁).symm.trans (hk.trans (freeProductZ_smul_neighbour k₂))
  have hsrc : ∀ k : ℤ,
      (freeProductZ.bassSerreTree false).src
        (dartMk (𝔸 := freeProductZ) (v₀ := false) false
          (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k))) =
        baseVertex freeProductZ false := fun _ =>
    (src_dartMk _ _).trans (vertexMk_ofVertex _)
  have hd : dartMk (𝔸 := freeProductZ) (v₀ := false) false
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k₁)) =
      dartMk (𝔸 := freeProductZ) (v₀ := false) false
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k₂)) :=
    congrArg Subtype.val <| tgt_injective_on_star (baseVertex freeProductZ false)
      (a₁ := ⟨_, hsrc k₁⟩) (a₂ := ⟨_, hsrc k₂⟩) hk'
  obtain ⟨c, hc⟩ := dartMk_eq_dartMk_iff.mp hd
  have hc1 : Path.ofVertex (𝔸 := freeProductZ) (a := false) ((freeProductZ.α false) c) =
      Path.ofVertex (𝔸 := freeProductZ) (a := false) (1 : Multiplicative ℤ) :=
    congrArg (Path.ofVertex (𝔸 := freeProductZ) (a := false))
      ((DFunLike.congr_fun (segment_α_false _ _ _ _) c).trans rfl)
  have hrhs : Quiver.Path.comp
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k₂))
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) ((freeProductZ.α false) c)) =
      Quiver.Path.cons
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k₂))
        (Letter.vertex (𝔸 := freeProductZ) (a := false) (1 : Multiplicative ℤ)) :=
    (congrArg _ hc1).trans (Path.comp_ofVertex _ _)
  have hmul : Path.Homotopic
      (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k₁))
      (Path.ofVertex (𝔸 := freeProductZ) (a := false) (Multiplicative.ofAdd k₂)) :=
    hc.trans (hrhs ▸ Path.Homotopic.one _)
  exact Multiplicative.ofAdd.injective (Path.ofVertex_homotopic_ofVertex_iff.mp hmul)

private theorem freeProductZ_exists_neighbour
    (y : {y : (freeProductZ.bassSerreTree false).E //
      (freeProductZ.bassSerreTree false).src y = baseVertex freeProductZ false}) :
    ∃ k : ℤ, (freeProductZ.bassSerreTree false).tgt y.1 =
      π₁.vertexHom (𝔸 := freeProductZ) (a := false) (b := false) Quiver.Path.nil
        (Multiplicative.ofAdd k) •
        vertexMk (𝔸 := freeProductZ) (v₀ := false)
          (Path.ofDart (SerreGraph.segment.dart false)) := by
  rcases y with ⟨y, hy⟩
  have hy' : (freeProductZ.bassSerreTree false).src y =
      vertexMk (𝔸 := freeProductZ) (v₀ := false) Quiver.Path.nil :=
    hy.trans baseVertex_def
  rcases hq : starEquiv (𝔸 := freeProductZ) (v₀ := false) Quiver.Path.nil ⟨y, hy'⟩ with
    ⟨⟨e, he⟩, q⟩
  have he' : e = false := he
  subst he'
  have hhe : he = rfl := Subsingleton.elim _ _
  subst hhe
  refine QuotientGroup.induction_on q
    (fun (a : freeProductZ.vertexGroup (SerreGraph.segment.src false)) hq => ?_) hq
  have hsymm := congrArg Subtype.val
    ((starEquiv (𝔸 := freeProductZ) (v₀ := false) Quiver.Path.nil).symm_apply_eq.mpr hq.symm)
  have hval : ((starEquiv (𝔸 := freeProductZ) (v₀ := false) Quiver.Path.nil).symm
      ⟨⟨false, rfl⟩, a⟩).1 =
      dartMk (𝔸 := freeProductZ) (v₀ := false) false
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) a) := by
    simpa using congrArg Subtype.val
      (starEquiv_symm_mk (𝔸 := freeProductZ) (v₀ := false) Quiver.Path.nil ⟨false, rfl⟩ a)
  have hy_eq : y = dartMk (𝔸 := freeProductZ) (v₀ := false) false
      (Path.ofVertex (𝔸 := freeProductZ) (a := false) a) := hsymm.symm.trans hval
  have ha : (a : Multiplicative ℤ) = Multiplicative.ofAdd (Multiplicative.toAdd a) :=
    (ofAdd_toAdd a).symm
  exact ⟨Multiplicative.toAdd a,
    (congrArg (freeProductZ.bassSerreTree false).tgt
      (hy_eq.trans (congrArg (fun x => dartMk (𝔸 := freeProductZ) (v₀ := false) false
        (Path.ofVertex (𝔸 := freeProductZ) (a := false) x)) ha))).trans
      (freeProductZ_smul_neighbour (Multiplicative.toAdd a)).symm⟩

/-- In the Bass–Serre tree of `ℤ ∗ ℤ` (`freeProductZ`), the base vertex `⟨a⟩` has star of cardinal
`ℵ₀`, and the targets of its incident darts are the pairwise distinct vertices `a^k ⟨b⟩` for
`k : ℤ`. -/
theorem bassSerreTree_free_product :
    Cardinal.mk {y : (freeProductZ.bassSerreTree false).E //
        (freeProductZ.bassSerreTree false).src y = baseVertex freeProductZ false} =
        Cardinal.aleph0 ∧
      Function.Injective
        (fun k : ℤ =>
          π₁.vertexHom (𝔸 := freeProductZ) (a := false) (b := false) Quiver.Path.nil
            (Multiplicative.ofAdd k) •
            vertexMk (𝔸 := freeProductZ) (v₀ := false)
              (Path.ofDart (SerreGraph.segment.dart false))) ∧
      ∀ y : {y : (freeProductZ.bassSerreTree false).E //
          (freeProductZ.bassSerreTree false).src y = baseVertex freeProductZ false},
        ∃ k : ℤ, (freeProductZ.bassSerreTree false).tgt y.1 =
          π₁.vertexHom (𝔸 := freeProductZ) (a := false) (b := false) Quiver.Path.nil
            (Multiplicative.ofAdd k) •
            vertexMk (𝔸 := freeProductZ) (v₀ := false)
              (Path.ofDart (SerreGraph.segment.dart false)) := by
  refine ⟨?_, freeProductZ_neighbour_injective, freeProductZ_exists_neighbour⟩
  rw [Cardinal.mk_congr ((freeProductBaseStarEquiv (Multiplicative ℤ) (Multiplicative ℤ)).trans
    Multiplicative.toAdd), Cardinal.mk_int]

end FreeProduct

/-! ### Baumslag–Solitar groups and `BS(1, 2)` -/

section BaumslagSolitar

private def quotientRangeZpowEquiv (k : ℤ) :
    Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) k).range ≃
      ℤ ⧸ AddSubgroup.zmultiples k where
  toFun := Quotient.map' Multiplicative.toAdd fun a b h => by
    obtain ⟨c, hc⟩ := QuotientGroup.leftRel_apply.mp h
    rw [QuotientAddGroup.leftRel_apply, Int.mem_zmultiples_iff]
    refine ⟨Multiplicative.toAdd c, ?_⟩
    have hadd := congrArg Multiplicative.toAdd hc
    simp only [zpowGroupHom_apply, toAdd_mul, toAdd_inv, toAdd_zpow, smul_eq_mul] at hadd
    omega
  invFun := Quotient.map' Multiplicative.ofAdd fun a b h => by
    rw [QuotientAddGroup.leftRel_apply, Int.mem_zmultiples_iff] at h
    obtain ⟨c, hc⟩ := h
    refine QuotientGroup.leftRel_apply.mpr ⟨Multiplicative.ofAdd c, ?_⟩
    apply Multiplicative.toAdd.injective
    simp only [zpowGroupHom_apply, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, smul_eq_mul]
    omega
  left_inv := Quotient.ind' fun _ => rfl
  right_inv := Quotient.ind' fun _ => rfl

private theorem index_range_zpowGroupHom (k : ℤ) :
    (zpowGroupHom (α := Multiplicative ℤ) k).range.index = k.natAbs := by
  rw [Subgroup.index, Nat.card_congr (quotientRangeZpowEquiv k), ← AddSubgroup.index,
    Int.index_zmultiples]

private theorem baumslagSolitar_index_α_true (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((baumslagSolitar m n hm hn).α ((), true)).range.index = m.natAbs :=
  (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
    (baumslagSolitar_α_true m n hm hn)).trans (index_range_zpowGroupHom m)

private theorem baumslagSolitar_index_ω_true (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((baumslagSolitar m n hm hn).ω ((), true)).range.index = n.natAbs :=
  (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
    (baumslagSolitar_ω_true m n hm hn)).trans (index_range_zpowGroupHom n)

private noncomputable def quotientZpowEquivZMod (k : ℤ) :
    Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) k).range ≃ ZMod k.natAbs :=
  (quotientRangeZpowEquiv k).trans (Int.quotientZMultiplesEquivZMod k).toEquiv

/-- In `baumslagSolitar m n hm hn`, the star of every vertex of the Bass–Serre tree is finite of
cardinal `m.natAbs + n.natAbs`. -/
theorem natCard_star_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : ((baumslagSolitar m n hm hn).bassSerreTree PUnit.unit).V) :
    Nat.card {y : ((baumslagSolitar m n hm hn).bassSerreTree PUnit.unit).E //
        ((baumslagSolitar m n hm hn).bassSerreTree PUnit.unit).src y = x} =
      m.natAbs + n.natAbs := by
  refine vertex_induction_on x fun {v} p => ?_
  cases v
  let 𝔸 := baumslagSolitar m n hm hn
  have : NeZero m.natAbs := ⟨Int.natAbs_ne_zero.mpr hm⟩
  have : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hn⟩
  have htrue : 𝔸.α ((), true) = zpowGroupHom (α := Multiplicative ℤ) m :=
    baumslagSolitar_α_true m n hm hn
  have hfalse : 𝔸.α ((), false) = zpowGroupHom (α := Multiplicative ℤ) n :=
    baumslagSolitar_α_false m n hm hn
  let eTrue : (Multiplicative ℤ ⧸ (𝔸.α ((), true)).range) ≃ ZMod m.natAbs :=
    (Equiv.cast (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ =>
      Multiplicative ℤ ⧸ f.range) htrue)).trans (quotientZpowEquivZMod m)
  let eFalse : (Multiplicative ℤ ⧸ (𝔸.α ((), false)).range) ≃ ZMod n.natAbs :=
    (Equiv.cast (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ =>
      Multiplicative ℤ ⧸ f.range) hfalse)).trans (quotientZpowEquivZMod n)
  let hsum :
      (Σ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = PUnit.unit},
          𝔸.vertexGroup ((SerreGraph.rose Unit).src e.1) ⧸ (𝔸.α e.1).range) ≃
        ZMod m.natAbs ⊕ ZMod n.natAbs :=
    { toFun := fun ⟨⟨⟨⟨⟩, b⟩, _⟩, q⟩ => match b, q with
        | true, q => .inl (eTrue q)
        | false, q => .inr (eFalse q)
      invFun := Sum.elim (fun q => ⟨⟨((), true), rfl⟩, eTrue.symm q⟩)
        (fun q => ⟨⟨((), false), rfl⟩, eFalse.symm q⟩)
      left_inv := fun ⟨⟨⟨⟨⟩, b⟩, _⟩, q⟩ => by
        cases b <;> refine Sigma.ext (Subtype.ext rfl) (heq_of_eq ?_)
        · exact eFalse.symm_apply_apply q
        · exact eTrue.symm_apply_apply q
      right_inv := fun s => by
        cases s with
        | inl q => exact congrArg Sum.inl (eTrue.apply_symm_apply q)
        | inr q => exact congrArg Sum.inr (eFalse.apply_symm_apply q) }
  rw [Nat.card_congr ((starEquiv p).trans hsum), Nat.card_sum, Nat.card_zmod, Nat.card_zmod]

/-- The graph of groups of the Baumslag–Solitar group `BS(1, 2)`. -/
abbrev baumslagSolitar12 : GraphOfGroups.{0, 0, 0, 0} (SerreGraph.rose Unit) :=
  baumslagSolitar 1 2 one_ne_zero two_ne_zero

/-- For `BS(1, 2)` (`baumslagSolitar12`), the boundary images have indices `[A_v : α(C)] = 1` and
`[A_v : ω(C)] = 2`, and every vertex of the Bass–Serre tree has degree `3`. -/
theorem bassSerreTree_BS12 :
    (baumslagSolitar12.α ((), true)).range.index = 1 ∧
      (baumslagSolitar12.ω ((), true)).range.index = 2 ∧
      ∀ x : (baumslagSolitar12.bassSerreTree PUnit.unit).V,
        Nat.card {y : (baumslagSolitar12.bassSerreTree PUnit.unit).E //
          (baumslagSolitar12.bassSerreTree PUnit.unit).src y = x} = 3 :=
  ⟨baumslagSolitar_index_α_true 1 2 one_ne_zero two_ne_zero,
    baumslagSolitar_index_ω_true 1 2 one_ne_zero two_ne_zero,
    fun x => natCard_star_baumslagSolitar 1 2 one_ne_zero two_ne_zero x⟩

end BaumslagSolitar

/-! ### Disconnected edgeless graph -/

section Disconnected

/-- Over two isolated vertices with trivial groups
(`GraphOfGroups.trivial (SerreGraph.noEdge Bool)`) based at `false`, both `bassSerreTree` and its
quotient graph have `1` vertex while the ambient graph has `2`, and no `𝔸`-path connects `false`
to `true`. -/
theorem bassSerreTree_trivial_noEdge_bool :
    Nat.card ((GraphOfGroups.trivial (SerreGraph.noEdge.{0, 0} Bool)).bassSerreTree false).V = 1 ∧
      Nat.card ((GraphOfGroups.trivial
        (SerreGraph.noEdge.{0, 0} Bool)).bassSerreTree false).quotient.V = 1 ∧
      Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 ∧
      IsEmpty ((GraphOfGroups.trivial (SerreGraph.noEdge.{0, 0} Bool)).Path ⟨false⟩ ⟨true⟩) := by
  let Γ := SerreGraph.noEdge.{0, 0} Bool
  let 𝔸 := GraphOfGroups.trivial Γ
  have _ : Unique (Γ.component false).V := inferInstance
  refine ⟨Nat.card_unique, ?_, Nat.card_eq_fintype_card.trans Fintype.card_bool, ⟨?_⟩⟩
  · rw [Nat.card_congr (quotientBassSerreTreeIso 𝔸 false).equivV]
    exact Nat.card_unique
  · intro p
    have heq := Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim p.edgePath
    exact Bool.false_ne_true heq

end Disconnected

/-! ### Why quotienting by homotopy alone fails -/

section NotQuotientPaths

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Homotopy equivalence on endpoint-indexed `𝔸`-paths starting at `v₀`, without quotienting on the
right by `A_v`. -/
def HomotopyPathRel :
    (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) → (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) → Prop
  | ⟨v₁, p₁⟩, ⟨v₂, p₂⟩ =>
    ∃ h : v₁ = v₂, Path.Homotopic (p₁.cast rfl (congrArg LetterVertex.mk h)) p₂

private theorem homotopyPathRel_equivalence : Equivalence (HomotopyPathRel 𝔸 v₀) where
  refl := fun ⟨_, p⟩ => ⟨rfl, by rw [Quiver.Path.cast_rfl_rfl]; exact .refl p⟩
  symm := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, hp⟩
    rw [Quiver.Path.cast_rfl_rfl] at hp
    exact ⟨rfl, by rw [Quiver.Path.cast_rfl_rfl]; exact hp.symm⟩
  trans := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, hp⟩ ⟨rfl, hq⟩
    rw [Quiver.Path.cast_rfl_rfl] at hp hq
    exact ⟨rfl, by rw [Quiver.Path.cast_rfl_rfl]; exact hp.trans hq⟩

/-- Setoid of `𝔸`-paths modulo homotopy alone (omitting the right `A_v`-coset relation). -/
def homotopyPathSetoid : Setoid (Σ v : Γ.V, 𝔸.Path ⟨v₀⟩ ⟨v⟩) :=
  ⟨HomotopyPathRel 𝔸 v₀, homotopyPathRel_equivalence 𝔸 v₀⟩

/-- The quotient of `𝔸`-paths starting at `v₀` by homotopy alone. -/
abbrev HomotopyPathVertex : Type (max u v w) :=
  Quotient (homotopyPathSetoid 𝔸 v₀)

/-- Left concatenation of a based loop onto a homotopy class of `𝔸`-paths. -/
def homotopySmulAux (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :
    HomotopyPathVertex 𝔸 v₀ → HomotopyPathVertex 𝔸 v₀ :=
  Quotient.map (fun x => ⟨x.1, s.comp x.2⟩) (by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, hp⟩
    rw [Quiver.Path.cast_rfl_rfl] at hp
    exact ⟨rfl, by rw [Quiver.Path.cast_rfl_rfl]; exact hp.comp_left s⟩)

/-- Scalar action map of `π₁(𝔸, v₀)` on `HomotopyPathVertex 𝔸 v₀`. -/
def homotopySmul : π₁ 𝔸 v₀ → HomotopyPathVertex 𝔸 v₀ → HomotopyPathVertex 𝔸 v₀ :=
  π₁.lift (homotopySmulAux 𝔸 v₀) fun _ _ hs => funext <|
    Quotient.ind fun ⟨_, p⟩ => Quotient.sound
      ⟨rfl, by rw [Quiver.Path.cast_rfl_rfl]; exact hs.comp_right p⟩

private theorem homotopySmul_mk (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    homotopySmul 𝔸 v₀ (π₁.mk s) (Quotient.mk (homotopyPathSetoid 𝔸 v₀) ⟨v, p⟩) =
      Quotient.mk (homotopyPathSetoid 𝔸 v₀) ⟨v, s.comp p⟩ := by
  rw [homotopySmul, π₁.lift_mk]
  rfl

/-- Left concatenation action of `π₁(𝔸, v₀)` on `HomotopyPathVertex 𝔸 v₀`. -/
instance : MulAction (π₁ 𝔸 v₀) (HomotopyPathVertex 𝔸 v₀) where
  smul := homotopySmul 𝔸 v₀
  one_smul := Quotient.ind fun ⟨_, p⟩ => by
    rw [← π₁.mk_nil]
    exact (homotopySmul_mk 𝔸 v₀ .nil p).trans (by rw [Quiver.Path.nil_comp])
  mul_smul g h := π₁.induction_on g fun s => π₁.induction_on h fun t =>
    Quotient.ind fun ⟨_, p⟩ => by
      simp only [HSMul.hSMul, SMul.smul]
      rw [← π₁.mk_comp, homotopySmul_mk, homotopySmul_mk, homotopySmul_mk, Quiver.Path.comp_assoc]

/-- The base class `⟦⟨v₀, nil⟩⟧` in `HomotopyPathVertex 𝔸 v₀`. -/
def homotopyPathBase : HomotopyPathVertex 𝔸 v₀ :=
  Quotient.mk (homotopyPathSetoid 𝔸 v₀) ⟨v₀, .nil⟩

/-- Canonical projection from homotopy classes of `𝔸`-paths to vertices of `bassSerreTree 𝔸 v₀`. -/
def homotopyPathToVertex : HomotopyPathVertex 𝔸 v₀ → (bassSerreTree 𝔸 v₀).V :=
  Quotient.lift (fun s => vertexMk s.2) (by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨rfl, hp⟩
    rw [Quiver.Path.cast_rfl_rfl] at hp
    exact vertexMk_congr hp)

/-- Embedding `A_{v₀}` into the fibre of `homotopyPathToVertex` over `baseVertex 𝔸 v₀`, sending
`a` to the homotopy class of `Path.ofVertex a`. -/
def vertexGroupToHomotopyFibre (a : 𝔸.vertexGroup v₀) :
    {z : HomotopyPathVertex 𝔸 v₀ // homotopyPathToVertex 𝔸 v₀ z = baseVertex 𝔸 v₀} :=
  ⟨Quotient.mk (homotopyPathSetoid 𝔸 v₀) ⟨v₀, Path.ofVertex a⟩,
    vertexMk_ofVertex a⟩

private theorem stabilizer_homotopyPathVertex_eq_bot (z : HomotopyPathVertex 𝔸 v₀) :
    MulAction.stabilizer (π₁ 𝔸 v₀) z = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  refine π₁.induction_on g (fun s hg => ?_) hg
  refine Quotient.inductionOn z (fun ⟨v, p⟩ hg => ?_) hg
  rw [MulAction.mem_stabilizer_iff] at hg
  have hg' : Quotient.mk (homotopyPathSetoid 𝔸 v₀) ⟨v, s.comp p⟩ =
      Quotient.mk (homotopyPathSetoid 𝔸 v₀) ⟨v, p⟩ :=
    (homotopySmul_mk 𝔸 v₀ s p).symm.trans hg
  obtain ⟨_, hp⟩ := Quotient.exact hg'
  rw [Quiver.Path.cast_rfl_rfl] at hp
  rw [Subgroup.mem_bot, ← π₁.mk_nil, π₁.mk_eq_mk_iff]
  exact Path.Homotopic.comp_right_iff.mp (by simpa using hp)

/-- Quotienting `𝔸`-paths by homotopy alone (without the right `A_v`-coset relation) embeds `A_{v₀}`
injectively into the fibre over `baseVertex` and gives every class trivial stabilizer, so whenever
`A_{v₀}` is nontrivial the naive quotient neither collapses the base vertex group nor has the
correct vertex stabilizers. -/
theorem bassSerreTree_not_quotient_paths :
    Function.Injective (vertexGroupToHomotopyFibre 𝔸 v₀) ∧
      (∀ z : HomotopyPathVertex 𝔸 v₀, MulAction.stabilizer (π₁ 𝔸 v₀) z = ⊥) ∧
      (Nontrivial (𝔸.vertexGroup v₀) →
        MulAction.stabilizer (π₁ 𝔸 v₀) (homotopyPathBase 𝔸 v₀) ≠
          MulAction.stabilizer (π₁ 𝔸 v₀) (baseVertex 𝔸 v₀)) := by
  refine ⟨?_, stabilizer_homotopyPathVertex_eq_bot 𝔸 v₀, ?_⟩
  · intro a₁ a₂ h
    have hrel : HomotopyPathRel 𝔸 v₀ ⟨v₀, Path.ofVertex a₁⟩ ⟨v₀, Path.ofVertex a₂⟩ :=
      Quotient.exact (congrArg Subtype.val h)
    obtain ⟨_, hp⟩ := hrel
    rw [Quiver.Path.cast_rfl_rfl] at hp
    exact Path.ofVertex_homotopic_ofVertex_iff.mp hp
  · intro _ hstab
    obtain ⟨a, ha⟩ := exists_ne (1 : 𝔸.vertexGroup v₀)
    have hmem : π₁.vertexHom (𝔸 := 𝔸) Quiver.Path.nil a ∈
        MulAction.stabilizer (π₁ 𝔸 v₀) (homotopyPathBase 𝔸 v₀) := by
      rw [hstab, stabilizer_baseVertex]
      exact ⟨a, rfl⟩
    rw [stabilizer_homotopyPathVertex_eq_bot, Subgroup.mem_bot] at hmem
    exact ha ((π₁.vertexHom_injective Quiver.Path.nil) (hmem.trans (map_one _).symm))

end NotQuotientPaths

end GraphOfGroups

end TauCeti
