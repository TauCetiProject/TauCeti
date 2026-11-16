/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Basic
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Star
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# Examples of Bass–Serre trees

Concrete computations of Bass–Serre trees for standard graphs of groups:

* **Edgeless graphs and one-vertex graphs**: when `Γ` has no darts, the Bass–Serre tree `X(𝔸, v₀)`
  is isomorphic to the one-vertex tree `GTree.point (π₁ 𝔸 v₀)`
  (`GraphOfGroups.bassSerreTreeIsoPointOfIsEmpty`, `GraphOfGroups.bassSerreTree_point`). On two
  isolated vertices (`SerreGraph.noEdge Bool`), both `X(𝔸, false)` and `X(𝔸, false) / π₁` have a
  single vertex while `Γ` has two, and there is no `𝔸`-path to the second vertex
  (`GraphOfGroups.bassSerreTree_noEdge_bool`).
* **Trivial groups**: when all vertex and edge groups are trivial, every vertex of `X(𝔸, v₀)` has
  trivial stabilizer (`GraphOfGroups.stabilizer_bassSerreVertex_trivial`), so `π₁(𝔸, v₀)` acts
  freely on vertices.
* **Free products**: for `A ∗ B` over `SerreGraph.segment`, the neighbours of a vertex over `false`
  (resp. `true`) biject with `A` (resp. `B`)
  (`GraphOfGroups.bassSerreTreeFreeProductNeighborEquiv`). For `ℤ ∗ ℤ`, the base vertex `⟨a⟩` has
  neighbours `a ^ k • b₀` for `k : ℤ`, pairwise distinct, and every vertex has degree `ℵ₀`
  (`GraphOfGroups.bassSerreTree_free_product`).
* **Baumslag–Solitar groups**: for `baumslagSolitar m n hm hn`, every vertex of the Bass–Serre tree
  has degree `|m| + |n|` (`GraphOfGroups.card_outgoing_bassSerreTree_baumslagSolitar`); in
  particular, for `BS(1, 2)` the boundary indices are `1` and `2`, and every vertex has degree `3`
  (`GraphOfGroups.bassSerreTree_BS12`).
* **Necessity of the vertex-coset quotient**: without quotienting `𝔸`-paths by right multiplication
  by vertex groups, distinct elements of `A_{v₀}` remain distinct in `π₁(𝔸, v₀)` with trivial base
  stabilizer, whereas in `X(𝔸, v₀)` they collapse to `bassSerreBaseVertex` with stabilizer
  `(π₁.vertexHom .nil).range` (`GraphOfGroups.bassSerreTree_not_quotient_paths`).

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2.
-/

public section

universe u v u' v' w x

namespace TauCeti

namespace GraphOfGroups

open SerreGraph _root_.MulAction
open scoped Cardinal

/-! ### Edgeless graphs, the one-vertex graph, and two isolated vertices -/

section Edgeless

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- The Bass–Serre tree of a graph of groups over an edgeless graph has no darts. -/
instance [IsEmpty Γ.E] : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun d => by
    induction d using bassSerreDart_induction_on with | h e _ =>
    exact isEmptyElim e⟩

/-- The Bass–Serre tree of a graph of groups over an edgeless graph has at most one vertex. -/
instance [IsEmpty Γ.E] : Subsingleton (𝔸.bassSerreTree v₀).V :=
  (𝔸.bassSerreTree v₀).subsingleton_of_isEmpty_dart

/-- When `Γ` has no darts, the underlying graph of the Bass–Serre tree `X(𝔸, v₀)` is isomorphic to
the one-vertex tree `GTree.point (π₁ 𝔸 v₀)`. -/
noncomputable def bassSerreTreeIsoPointOfIsEmpty [IsEmpty Γ.E] :
    (𝔸.bassSerreTree v₀).toSerreGraph.Iso (GTree.point.{u', v'} (π₁ 𝔸 v₀)).toSerreGraph where
  equivV :=
    { toFun := fun _ =>
        (((SerreGraph.connected_iff _).mp (GTree.point.{u', v'} (π₁ 𝔸 v₀)).isTree.connected).1).some
      invFun := fun _ => 𝔸.bassSerreBaseVertex v₀
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  equivE :=
    letI : IsEmpty (GTree.point.{u', v'} (π₁ 𝔸 v₀)).E :=
      (GTree.point.{u', v'} (π₁ 𝔸 v₀)).isEmpty_dart_of_subsingleton
    Equiv.equivOfIsEmpty _ _
  map_src e := isEmptyElim e
  map_rev e := isEmptyElim e

/-- For a one-vertex graph of groups without edges, the Bass–Serre tree is a single point fixed by
the entire fundamental group. -/
theorem bassSerreTree_point (𝔸 : GraphOfGroups.{0, 0, w, x} (SerreGraph.noEdge PUnit)) :
    Subsingleton (𝔸.bassSerreTree PUnit.unit).V ∧
      IsEmpty (𝔸.bassSerreTree PUnit.unit).E ∧
      stabilizer (π₁ 𝔸 PUnit.unit) (𝔸.bassSerreBaseVertex PUnit.unit) = ⊤ :=
  ⟨inferInstance, inferInstance,
    (𝔸.bassSerreTree PUnit.unit).stabilizer_eq_top_of_subsingleton _⟩

/-- For two isolated vertices with trivial groups and basepoint at `false`, both the Bass–Serre
tree and its quotient have one vertex while the underlying graph has two, and there is no
`𝔸`-path from `false` to `true`. -/
theorem bassSerreTree_noEdge_bool :
    let 𝔸 := trivial (SerreGraph.noEdge.{0, 0} Bool)
    Nat.card (𝔸.bassSerreTree false).V = 1 ∧
      Nat.card (𝔸.bassSerreTree false).quotient.V = 1 ∧
      Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 ∧
      IsEmpty (𝔸.Path ⟨false⟩ ⟨true⟩) := by
  intro 𝔸
  have : Unique (𝔸.bassSerreTree false).V := uniqueOfSubsingleton (𝔸.bassSerreBaseVertex false)
  have : Subsingleton (𝔸.bassSerreTree false).quotient.V :=
    (𝔸.bassSerreTree false).quotientMap_mapV_surjective.subsingleton
  have : Unique (𝔸.bassSerreTree false).quotient.V :=
    uniqueOfSubsingleton
      ((𝔸.bassSerreTree false).quotientMap.mapV (𝔸.bassSerreBaseVertex false))
  refine ⟨Nat.card_unique, Nat.card_unique, ?_, ⟨fun p => ?_⟩⟩
  · rw [Nat.card_eq_fintype_card]
    exact Fintype.card_bool
  · exact Bool.false_ne_true (SerreGraph.noEdge_nonempty_path_iff.mp ⟨p.edgePath⟩)

end Edgeless

/-! ### Trivial vertex and edge groups -/

section Trivial

/-- When all vertex and edge groups are trivial, every vertex stabilizer in the Bass–Serre tree is
trivial (so `π₁(𝔸, v₀)` acts freely on vertices). -/
theorem stabilizer_bassSerreVertex_trivial (Γ : SerreGraph.{u, v}) (v₀ : Γ.V)
    (x : ((trivial Γ).bassSerreTree v₀).V) :
    stabilizer (π₁ (trivial Γ) v₀) x = ⊥ := by
  induction x using bassSerreVertex_induction_on with | h p =>
  exact stabilizer_bassSerreVertex_eq_bot_of_subsingleton p

end Trivial

/-! ### Free products and `ℤ ∗ ℤ` -/

section FreeProduct

private theorem segment_trivial_α_range {A B : Type w} [Group A] [Group B]
    (e : SerreGraph.segment.E) :
    ((segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
      (Function.injective_of_subsingleton _)).α e).range = ⊥ := by
  ext g
  simp only [MonoidHom.mem_range, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨⟩, rfl⟩
    exact map_one _
  · rintro rfl
    exact ⟨(), map_one _⟩

private noncomputable def freeProductStarEquiv {A B : Type w} [Group A] [Group B]
    (b : SerreGraph.segment.V) :
    (Σ e : {e : SerreGraph.segment.E // SerreGraph.segment.src e = b},
      (segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).vertexGroup (SerreGraph.segment.src e.1) ⧸
        ((segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).α e.1).range) ≃
      (segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).vertexGroup b where
  toFun := fun ⟨⟨e, he⟩, q⟩ => by
    cases he
    exact QuotientGroup.quotientBot
      (Subgroup.quotientEquivOfEq (segment_trivial_α_range e) q)
  invFun g :=
    ⟨⟨(b : SerreGraph.segment.E), SerreGraph.segment_src b⟩, QuotientGroup.mk g⟩
  left_inv := fun ⟨⟨e, he⟩, q⟩ => by
    cases he
    induction q using QuotientGroup.induction_on with | H g =>
    rfl
  right_inv _ := rfl

/-- For the segment of a free product `A ∗ B` (trivial edge group), the neighbours of a vertex
`bassSerreVertex p` lying over `b` biject with the vertex group at `b`. -/
noncomputable def bassSerreTreeFreeProductNeighborEquiv {A B : Type w} [Group A] [Group B]
    {v₀ b : SerreGraph.segment.V}
    (p : (segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
      (Function.injective_of_subsingleton _)).Path ⟨v₀⟩ ⟨b⟩) :
    {y : ((segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).bassSerreTree v₀).V //
      ∃ d, ((segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).bassSerreTree v₀).src d = bassSerreVertex p ∧
        ((segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).bassSerreTree v₀).tgt d = y} ≃
      (segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
        (Function.injective_of_subsingleton _)).vertexGroup b :=
  (bassSerreTreeNeighborEquiv p).trans (freeProductStarEquiv b)

@[simp] theorem bassSerreTreeFreeProductNeighborEquiv_symm_val {A B : Type w} [Group A] [Group B]
    {v₀ : SerreGraph.segment.V} (e : SerreGraph.segment.E)
    (p : (segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
      (Function.injective_of_subsingleton _)).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (g : (segment (1 : Unit →* A) (1 : Unit →* B) (Function.injective_of_subsingleton _)
      (Function.injective_of_subsingleton _)).vertexGroup (SerreGraph.segment.src e)) :
    ((bassSerreTreeFreeProductNeighborEquiv p).symm g).1 =
      bassSerreVertex
        ((p.comp (Path.ofVertex g)).cons (Letter.dart (SerreGraph.segment.dart e))) := by
  rw [bassSerreTreeFreeProductNeighborEquiv, Equiv.symm_trans_apply]
  exact bassSerreTreeNeighborEquiv_symm_mk e p g

/-- In the Bass–Serre tree of the free product `ℤ ∗ ℤ`, the base vertex `⟨a⟩` has pairwise distinct
neighbours `a ^ k • b₀` for `k : ℤ`, and every vertex has degree `ℵ₀`. -/
theorem bassSerreTree_free_product :
    let 𝔸 := segment (1 : Unit →* Multiplicative ℤ) (1 : Unit →* Multiplicative ℤ)
      (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)
    let e₀ : SerreGraph.segment.E := false
    let v₀ : SerreGraph.segment.V := SerreGraph.segment.src e₀
    let X := 𝔸.bassSerreTree v₀
    let x₀ := 𝔸.bassSerreBaseVertex v₀
    let a : π₁ 𝔸 v₀ :=
      π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (Multiplicative.ofAdd (α := ℤ) 1)
    let b₀ : X.V :=
      bassSerreVertex
        ((Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩).cons (Letter.dart (SerreGraph.segment.dart e₀)))
    {y : X.V | ∃ d : X.E, X.src d = x₀ ∧ X.tgt d = y} = Set.range (fun k : ℤ => a ^ k • b₀) ∧
      Function.Injective (fun k : ℤ => a ^ k • b₀) ∧
      (∀ x : X.V, #{y : X.V // ∃ d : X.E, X.src d = x ∧ X.tgt d = y} = ℵ₀) ∧
      (∀ x : X.V, #{d : X.E // X.src d = x} = ℵ₀) := by
  intro 𝔸 e₀ v₀ X x₀ a b₀
  let φ := bassSerreTreeFreeProductNeighborEquiv (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
  let mkZ (k : ℤ) : 𝔸.vertexGroup v₀ := Multiplicative.ofAdd (α := ℤ) k
  have hx₀ : x₀ = bassSerreVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) :=
    𝔸.bassSerreBaseVertex_def v₀
  have hsymm : ∀ k : ℤ, (φ.symm (mkZ k)).1 = a ^ k • b₀ := by
    intro k
    have hval := bassSerreTreeFreeProductNeighborEquiv_symm_val e₀
      (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (mkZ k)
    have hpow : (mkZ 1) ^ k = mkZ k := by
      have h : (Multiplicative.ofAdd (α := ℤ) 1) ^ k = Multiplicative.ofAdd (α := ℤ) k := by
        rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one, Int.cast_id]
      exact h
    have ha : a ^ k = π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) (mkZ k) :=
      (map_zpow (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) (mkZ 1) k).symm.trans
        (congrArg (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)) hpow)
    refine hval.trans ?_
    rw [ha, π₁.vertexHom_nil_apply, smul_bassSerreVertex, Quiver.Path.nil_comp]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      rw [Set.mem_ofPred_eq, hx₀] at hy
      refine ⟨(φ ⟨y, hy⟩).toAdd, ?_⟩
      exact (hsymm _).symm.trans (congrArg Subtype.val (φ.symm_apply_apply ⟨y, hy⟩))
    · rintro ⟨k, rfl⟩
      dsimp only
      rw [hx₀, ← hsymm k]
      exact (φ.symm (mkZ k)).2
  · intro k₁ k₂ h
    have h' : φ.symm (mkZ k₁) = φ.symm (mkZ k₂) :=
      Subtype.ext ((hsymm k₁).trans (h.trans (hsymm k₂).symm))
    exact Multiplicative.ofAdd.injective (φ.symm.injective h')
  · intro x
    induction x using bassSerreVertex_induction_on with | @h b p =>
    rw [Cardinal.mk_congr (bassSerreTreeFreeProductNeighborEquiv p)]
    cases b <;> exact (Cardinal.mk_congr Multiplicative.toAdd).trans Cardinal.mk_int
  · intro x
    induction x using bassSerreVertex_induction_on with | @h b p =>
    let e := (bassSerreTreeOutgoingEquiv p).trans (bassSerreTreeNeighborEquiv p).symm
    rw [Cardinal.mk_congr (e.trans (bassSerreTreeFreeProductNeighborEquiv p))]
    cases b <;> exact (Cardinal.mk_congr Multiplicative.toAdd).trans Cardinal.mk_int

end FreeProduct

/-! ### Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)` -/

section BaumslagSolitar

variable (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)

/-- The image of the `α`-monomorphism of `baumslagSolitar m n hm hn` on the positive loop dart has
index `|m|` in the vertex group `ℤ`. -/
theorem baumslagSolitar_α_true_range_index :
    ((baumslagSolitar m n hm hn).α (((), true) : (SerreGraph.rose Unit).E)).range.index =
      m.natAbs := by
  let g : Multiplicative ℤ := Multiplicative.ofAdd (1 : ℤ)
  have hg : Subgroup.zpowers g = ⊤ :=
    eq_top_iff.mpr fun x _ => ⟨x.toAdd, by simp [g, ← ofAdd_zsmul]⟩
  have hrange : (zpowGroupHom (α := Multiplicative ℤ) m).range = Subgroup.zpowers (g ^ m) := by
    ext x
    simp only [MonoidHom.mem_range, zpowGroupHom_apply, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, ?_⟩, fun ⟨k, hk⟩ => ⟨Multiplicative.ofAdd k, ?_⟩⟩
    · rw [← hc, ← zpow_mul, mul_comm m, zpow_mul]
      simp [g, ← ofAdd_zsmul]
    · rw [← hk, ← zpow_mul, mul_comm m, zpow_mul]
      simp [g, ← ofAdd_zsmul]
  have ho : orderOf g = 0 := by
    rw [orderOf_ofAdd_eq_addOrderOf, addOrderOf_eq_zero_iff, isOfFinAddOrder_iff_nsmul_eq_zero]
    rintro ⟨k, hk, hzero⟩
    exact hk.ne' (by simpa [nsmul_eq_mul] using hzero)
  have h : (zpowGroupHom (α := Multiplicative ℤ) m).range.index = m.natAbs := by
    rw [hrange, Subgroup.index_zpowers_zpow hg, ho]
    exact Int.gcd_zero_right m
  rw [baumslagSolitar_α_true]
  exact h

/-- The image of the `ω`-monomorphism of `baumslagSolitar m n hm hn` on the positive loop dart has
index `|n|` in the vertex group `ℤ`. -/
theorem baumslagSolitar_ω_true_range_index :
    ((baumslagSolitar m n hm hn).ω (((), true) : (SerreGraph.rose Unit).E)).range.index =
      n.natAbs := by
  rw [baumslagSolitar_ω_true, ← baumslagSolitar_α_true n m hn hm]
  exact baumslagSolitar_α_true_range_index n m hn hm

/-- Every vertex of the Bass–Serre tree of `BS(m, n)` has degree `|m| + |n|`. -/
theorem card_outgoing_bassSerreTree_baumslagSolitar
    (x : ((baumslagSolitar m n hm hn).bassSerreTree PUnit.unit).V) :
    Nat.card {d : ((baumslagSolitar m n hm hn).bassSerreTree PUnit.unit).E //
      ((baumslagSolitar m n hm hn).bassSerreTree PUnit.unit).src d = x} =
      m.natAbs + n.natAbs := by
  induction x using bassSerreVertex_induction_on with | @h v p =>
  cases v
  let 𝔸 := baumslagSolitar m n hm hn
  let eT : (SerreGraph.rose Unit).E := ((), true)
  let eF : (SerreGraph.rose Unit).E := ((), false)
  let e :
      (Σ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = PUnit.unit},
        𝔸.vertexGroup ((SerreGraph.rose Unit).src e.1) ⧸ (𝔸.α e.1).range) ≃
      (𝔸.vertexGroup ((SerreGraph.rose Unit).src eT) ⧸ (𝔸.α eT).range) ⊕
        (𝔸.vertexGroup ((SerreGraph.rose Unit).src eF) ⧸ (𝔸.α eF).range) :=
    { toFun := fun ⟨⟨⟨⟨⟩, b⟩, _⟩, q⟩ => match b, q with
        | true, q => Sum.inl q
        | false, q => Sum.inr q
      invFun := fun s => match s with
        | Sum.inl q => ⟨⟨eT, rfl⟩, q⟩
        | Sum.inr q => ⟨⟨eF, rfl⟩, q⟩
      left_inv := fun ⟨⟨⟨⟨⟩, b⟩, _⟩, q⟩ => by cases b <;> rfl
      right_inv := fun s => by cases s <;> rfl }
  have hcard_t : Nat.card (𝔸.vertexGroup ((SerreGraph.rose Unit).src eT) ⧸ (𝔸.α eT).range) =
      m.natAbs := by
    rw [← Subgroup.index_eq_card]
    exact baumslagSolitar_α_true_range_index m n hm hn
  have hcard_f : Nat.card (𝔸.vertexGroup ((SerreGraph.rose Unit).src eF) ⧸ (𝔸.α eF).range) =
      n.natAbs := by
    rw [← Subgroup.index_eq_card]
    have hα : 𝔸.α eF = 𝔸.ω eT := (baumslagSolitar_α_false m n hm hn).trans
      (baumslagSolitar_ω_true m n hm hn).symm
    rw [hα]
    exact baumslagSolitar_ω_true_range_index m n hm hn
  have : Finite (𝔸.vertexGroup ((SerreGraph.rose Unit).src eT) ⧸ (𝔸.α eT).range) :=
    Nat.finite_of_card_ne_zero (hcard_t.symm ▸ Int.natAbs_ne_zero.mpr hm)
  have : Finite (𝔸.vertexGroup ((SerreGraph.rose Unit).src eF) ⧸ (𝔸.α eF).range) :=
    Nat.finite_of_card_ne_zero (hcard_f.symm ▸ Int.natAbs_ne_zero.mpr hn)
  rw [Nat.card_congr ((bassSerreTreeOutgoingEquiv p).trans e), Nat.card_sum, hcard_t, hcard_f]

/-- For the Baumslag–Solitar group `BS(1, 2)`, the boundary subgroups have indices `1` and `2`, and
every vertex of the Bass–Serre tree has degree `3`. -/
theorem bassSerreTree_BS12 :
    let 𝔸 := baumslagSolitar 1 2 one_ne_zero two_ne_zero
    (𝔸.α (((), true) : (SerreGraph.rose Unit).E)).range.index = 1 ∧
      (𝔸.ω (((), true) : (SerreGraph.rose Unit).E)).range.index = 2 ∧
      ∀ x : (𝔸.bassSerreTree PUnit.unit).V,
        Nat.card {d : (𝔸.bassSerreTree PUnit.unit).E // (𝔸.bassSerreTree PUnit.unit).src d = x} =
          3 :=
  ⟨baumslagSolitar_α_true_range_index 1 2 one_ne_zero two_ne_zero,
    baumslagSolitar_ω_true_range_index 1 2 one_ne_zero two_ne_zero,
    card_outgoing_bassSerreTree_baumslagSolitar 1 2 one_ne_zero two_ne_zero⟩

end BaumslagSolitar

/-! ### Necessity of quotienting by vertex groups -/

section UnquotientedPaths

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Without quotienting `𝔸`-paths by right multiplication by vertex groups, distinct elements of
`A_{v₀}` represent distinct closed paths in `π₁(𝔸, v₀)` and the left-multiplication stabilizer of
the base class `1` is trivial. Passing to the Bass–Serre tree collapses every `Path.ofVertex g` to
the base vertex, whose stabilizer is `(π₁.vertexHom .nil).range`. -/
theorem bassSerreTree_not_quotient_paths :
    Function.Injective (fun g : 𝔸.vertexGroup v₀ => π₁.mk (Path.ofVertex g)) ∧
      stabilizer (π₁ 𝔸 v₀) (1 : π₁ 𝔸 v₀) = ⊥ ∧
      (∀ g : 𝔸.vertexGroup v₀, bassSerreVertex (Path.ofVertex g) = 𝔸.bassSerreBaseVertex v₀) ∧
      stabilizer (π₁ 𝔸 v₀) (𝔸.bassSerreBaseVertex v₀) =
        (π₁.vertexHom (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)).range := by
  refine ⟨?_, ?_, ?_, stabilizer_bassSerreBaseVertex 𝔸 v₀⟩
  · intro g₁ g₂ h
    exact π₁.vertexHom_injective (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩)
      (by simpa only [π₁.vertexHom_nil_apply] using h)
  · ext g
    simp
  · intro g
    rw [bassSerreBaseVertex_def]
    simpa only [Quiver.Path.nil_comp] using
      bassSerreVertex_comp_ofVertex (Quiver.Path.nil : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) g

end UnquotientedPaths

end GraphOfGroups

end TauCeti
