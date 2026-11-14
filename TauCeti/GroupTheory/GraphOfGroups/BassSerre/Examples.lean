/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Stabilizer
public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Star
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Canonical examples and checks for the Bass–Serre tree

This file verifies the Bass–Serre tree construction (`GraphOfGroups.bassSerreTree`) on five
canonical families and boundary cases:

1. **Edgeless graphs** (`GraphOfGroups.bassSerreTreeIsoPoint`, `GraphOfGroups.bassSerreTree_point`):
   when `Γ` has no darts, `X(𝔸, v₀)` has a single vertex `1 · A_{v₀}` and is isomorphic as a
   Serre graph to `SerreGraph.noEdge PUnit`.
2. **Free products and `ℤ ∗ ℤ`** (`GraphOfGroups.freeProductGraph`,
   `GraphOfGroups.bassSerreTree_free_product`): for `A ∗ B` over the segment with trivial edge
   group, the neighbours of the base vertex `1 · A` correspond bijectively to `A` via
   `a ↦ (a · e) B`; for `ℤ ∗ ℤ` the base vertex has countably infinitely many neighbours `a^k ⟨b⟩`
   and degree `ℵ₀`.
3. **Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)`** (`GraphOfGroups.card_star_baumslagSolitar`,
   `GraphOfGroups.bassSerreTree_BS12`): for `GraphOfGroups.baumslagSolitar m n hm hn`, every vertex
   of `X` has degree `|m| + |n|`; for `BS(1, 2)`, the boundary indices are `1` and `2` and every
   vertex has degree `3`.
4. **Unquotiented homotopy classes of based `𝔸`-paths** (`GraphOfGroups.HomotopyPathFrom`,
   `GraphOfGroups.bassSerreTree_not_quotient_paths`): without the right-coset equivalence `p ≈ p a`,
   homotopy classes of based paths have a distinct point at `v₀` for every `a ∈ A_{v₀}` and trivial
   basepoint stabilizer.
5. **Disconnected underlying graphs** (`GraphOfGroups.twoIsolated`,
   `GraphOfGroups.bassSerreTree_two_isolated`): over two isolated vertices, both `X(𝔸, v₀)` and
   its quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` have a single vertex while the ambient graph has two.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTreeIsoPoint`: isomorphism of `X(𝔸, v₀)` with
  `SerreGraph.noEdge PUnit` when `Γ.E` is empty.
* `TauCeti.GraphOfGroups.freeProductGraph`, `TauCeti.GraphOfGroups.freeProductStarEquiv`,
  `TauCeti.GraphOfGroups.freeProductAdjacentEquiv`: the segment graph of groups of `A ∗ B` and its
  basepoint star and neighbour bijections with `A`.
* `TauCeti.GraphOfGroups.HomotopyPathFrom`: based `𝔸`-paths from `v₀` modulo homotopy only.
* `TauCeti.GraphOfGroups.twoIsolated`: the graph of groups on two isolated vertices with trivial
  vertex groups.

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_point`,
  `TauCeti.GraphOfGroups.bassSerreTree_free_product`,
  `TauCeti.GraphOfGroups.card_star_baumslagSolitar`,
  `TauCeti.GraphOfGroups.bassSerreTree_BS12`,
  `TauCeti.GraphOfGroups.bassSerreTree_not_quotient_paths`,
  `TauCeti.GraphOfGroups.bassSerreTree_two_isolated`.

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

/-! ### 1. Graphs without edges (`bassSerreTree_point`) -/

section Edgeless

instance [IsEmpty Γ.E] : IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨fun d => bassSerreDart_induction d fun e _ => isEmptyElim e⟩

instance [IsEmpty Γ.E] : Unique (𝔸.bassSerreTree v₀).V where
  default := 𝔸.bassSerreBaseVertex v₀
  uniq u := bassSerreVertex_induction u fun {v} p => by
    have aux : ∀ {y : 𝔸.LetterVertex} (q : 𝔸.Path ⟨v₀⟩ y),
        𝔸.bassSerreVertex v₀ (v := y.as) q = 𝔸.bassSerreBaseVertex v₀ := by
      intro y q
      induction q with
      | nil => rfl
      | @cons y₁ y₂ q l ih =>
        cases y₁ with | mk _ =>
        cases y₂ with | mk _ =>
        cases l with
        | vertex a => exact (bassSerreVertex_cons_vertex q a).trans ih
        | dart e => exact isEmptyElim e.1
    exact aux p

/-- Over a graph without edges, `X(𝔸, v₀)` is isomorphic as a Serre graph to
`SerreGraph.noEdge PUnit`. -/
def bassSerreTreeIsoPoint [IsEmpty Γ.E] :
    (𝔸.bassSerreTree v₀).toSerreGraph.Iso (SerreGraph.noEdge.{u, v} PUnit) where
  equivV := Equiv.ofUnique _ _
  equivE := Equiv.equivOfIsEmpty _ _
  map_src d := isEmptyElim d
  map_rev d := isEmptyElim d

/-- For any graph of groups over the one-vertex edgeless graph `SerreGraph.noEdge PUnit`, the
Bass–Serre tree is a single point without darts. -/
theorem bassSerreTree_point (𝔸 : GraphOfGroups.{0, 0, w, x} (SerreGraph.noEdge PUnit)) :
    Nonempty ((𝔸.bassSerreTree PUnit.unit).toSerreGraph.Iso (SerreGraph.noEdge.{0, 0} PUnit)) ∧
      Subsingleton (𝔸.bassSerreTree PUnit.unit).V ∧
      IsEmpty (𝔸.bassSerreTree PUnit.unit).E :=
  ⟨⟨𝔸.bassSerreTreeIsoPoint PUnit.unit⟩, inferInstance, inferInstance⟩

end Edgeless

/-! ### 2. Free products and `ℤ ∗ ℤ` (`bassSerreTree_free_product`) -/

section FreeProduct

/-- The one-edge graph of groups of a free product `A ∗ B`: the segment with vertex groups `A` at
`false` and `B` at `true` and trivial edge group `PUnit`. -/
@[expose] def freeProductGraph (A B : Type w) [Group A] [Group B] :
    GraphOfGroups.{0, 0, w, 0} SerreGraph.segment :=
  segment (1 : PUnit →* A) (1 : PUnit →* B) (Function.injective_of_subsingleton _)
    (Function.injective_of_subsingleton _)

@[instance_reducible]
private def segmentStarFalseUnique (v₀ : SerreGraph.segment.V) (hv₀ : v₀ = false) :
    Unique {e : SerreGraph.segment.E // SerreGraph.segment.src e = v₀} where
  default := ⟨false, hv₀.symm⟩
  uniq := by
    subst hv₀
    rintro ⟨b, hb⟩
    cases b
    · rfl
    · cases hb

private theorem freeProductGraph_αArrow_range (A B : Type w) [Group A] [Group B] :
    let v₀ : SerreGraph.segment.V := false
    let v₁ : SerreGraph.segment.V := true
    let e₀ : SerreGraph.segment.E := false
    ((freeProductGraph A B).αArrow (⟨e₀, rfl, rfl⟩ : v₀ ⟶ v₁)).range =
      (⊥ : Subgroup A) :=
  (congrArg (fun f : PUnit →* A => f.range)
    (((freeProductGraph A B).αArrow_mk (false : SerreGraph.segment.E)).trans
      (segment_α_false (1 : PUnit →* A) (1 : PUnit →* B) _ _))).trans
    MonoidHom.range_one

/-- In the Bass–Serre tree of `A ∗ B`, the outgoing darts at the base vertex `1 · A` correspond
bijectively to the elements of `A`. -/
noncomputable def freeProductStarEquiv (A B : Type w) [Group A] [Group B] :
    {E : ((freeProductGraph A B).bassSerreTree false).E //
      ((freeProductGraph A B).bassSerreTree false).src E =
        (freeProductGraph A B).bassSerreBaseVertex false} ≃ A :=
  let v₀ : SerreGraph.segment.V := false
  (((freeProductGraph A B).bassSerreStarEquiv v₀ .nil).trans
    (@Equiv.uniqueSigma _ _ (segmentStarFalseUnique v₀ rfl))).trans
    ((Subgroup.quotientEquivOfEq (α := A) (freeProductGraph_αArrow_range A B)).trans
      (QuotientGroup.quotientEquivSelf A))

@[simp] theorem freeProductStarEquiv_symm_apply (A B : Type w) [Group A] [Group B] (a : A) :
    ((freeProductStarEquiv A B).symm a).1 =
      (freeProductGraph A B).bassSerreDart false (false : SerreGraph.segment.E)
        (Path.ofVertex a) := by
  let v₀ : SerreGraph.segment.V := false
  let e₀ : SerreGraph.segment.E := false
  let a' : (freeProductGraph A B).vertexGroup v₀ := a
  have hq :
      (((Subgroup.quotientEquivOfEq (α := A) (freeProductGraph_αArrow_range A B)).trans
        (QuotientGroup.quotientEquivSelf A)).symm a) =
      (@QuotientGroup.mk A _
        (((freeProductGraph A B).αArrow (⟨e₀, rfl, rfl⟩ : v₀ ⟶ true)).range) a) :=
    Equiv.symm_apply_eq _ |>.mpr rfl
  have h1 : ((freeProductStarEquiv A B).symm a).1 =
      (freeProductGraph A B).bassSerreDartOfSrcEq v₀ e₀
        (segmentStarFalseUnique v₀ rfl).default.2 (Quiver.Path.nil.cons (Letter.vertex a')) := by
    change (((freeProductGraph A B).bassSerreStarEquiv v₀ .nil).symm
      ⟨(segmentStarFalseUnique v₀ rfl).default,
        ((Subgroup.quotientEquivOfEq (α := A) (freeProductGraph_αArrow_range A B)).trans
          (QuotientGroup.quotientEquivSelf A)).symm a⟩).1 = _
    rw [hq]
    exact bassSerreStarEquiv_symm_apply (𝔸 := freeProductGraph A B) (v₀ := v₀) .nil
      (segmentStarFalseUnique v₀ rfl).default a'
  have h2 : (segmentStarFalseUnique v₀ rfl).default.2 = (rfl : SerreGraph.segment.src e₀ = v₀) :=
    Subsingleton.elim _ _
  refine h1.trans ?_
  rw [h2]
  exact (bassSerreDartOfSrcEq_rfl e₀ (Quiver.Path.nil.cons (Letter.vertex a'))).trans
    (congrArg ((freeProductGraph A B).bassSerreDart v₀ e₀) (Path.ofVertex_eq_nil_cons a').symm)

/-- In the Bass–Serre tree of `A ∗ B`, the neighbours of the base vertex `1 · A` correspond
bijectively to `A` via `a ↦ (a · e) B`. -/
noncomputable def freeProductAdjacentEquiv (A B : Type w) [Group A] [Group B] :
    A ≃ {w : ((freeProductGraph A B).bassSerreTree false).V //
      Nonempty ((freeProductGraph A B).bassSerreBaseVertex false ⟶ w)} :=
  (freeProductStarEquiv A B).symm.trans ((freeProductGraph A B).bassSerreStarEquivAdjacent false _)

@[simp] theorem freeProductAdjacentEquiv_apply (A B : Type w) [Group A] [Group B] (a : A) :
    (freeProductAdjacentEquiv A B a).1 =
      (freeProductGraph A B).bassSerreVertex false
        ((Path.ofVertex a).cons (Letter.dart (SerreGraph.segment.dart false))) := by
  refine (bassSerreStarEquivAdjacent_apply (𝔸 := freeProductGraph A B)
    (v₀ := (false : SerreGraph.segment.V))
    ((freeProductGraph A B).bassSerreBaseVertex (false : SerreGraph.segment.V))
    ((freeProductStarEquiv A B).symm a)).trans ?_
  exact (congrArg ((freeProductGraph A B).bassSerreTree (false : SerreGraph.segment.V)).tgt
    (freeProductStarEquiv_symm_apply A B a)).trans
    (bassSerreTree_tgt_dart (𝔸 := freeProductGraph A B) (v₀ := (false : SerreGraph.segment.V))
      (false : SerreGraph.segment.E)
      (Path.ofVertex (a : (freeProductGraph A B).vertexGroup (false : SerreGraph.segment.V))))

/-- For `ℤ ∗ ℤ`, the base vertex `⟨a⟩` in the Bass–Serre tree has neighbours `a^k ⟨b⟩` indexed
bijectively by `k ∈ ℤ`, and its degree is `ℵ₀`. -/
theorem bassSerreTree_free_product :
    let F2 := freeProductGraph (Multiplicative ℤ) (Multiplicative ℤ)
    (∃ equiv : ℤ ≃ {w : (F2.bassSerreTree false).V //
          Nonempty (F2.bassSerreBaseVertex false ⟶ w)},
      ∀ k : ℤ, (equiv k).1 = F2.bassSerreVertex false
        ((Path.ofVertex (Multiplicative.ofAdd k)).cons
          (Letter.dart (SerreGraph.segment.dart false)))) ∧
    Cardinal.mk {E : (F2.bassSerreTree false).E //
      (F2.bassSerreTree false).src E = F2.bassSerreBaseVertex false} =
      Cardinal.aleph0 := by
  refine ⟨⟨Multiplicative.ofAdd.trans
      (freeProductAdjacentEquiv (Multiplicative ℤ) (Multiplicative ℤ)), fun k =>
      freeProductAdjacentEquiv_apply (Multiplicative ℤ) (Multiplicative ℤ)
        (Multiplicative.ofAdd k)⟩, ?_⟩
  rw [Cardinal.mk_congr ((freeProductStarEquiv (Multiplicative ℤ) (Multiplicative ℤ)).trans
    Multiplicative.toAdd), Cardinal.mk_int]

end FreeProduct

/-! ### 3. Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)` (`bassSerreTree_BS12`) -/

section BaumslagSolitar

private theorem index_range_zpowGroupHom_int (m : ℤ) :
    (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range.index = m.natAbs := by
  let g : Multiplicative ℤ := Multiplicative.ofAdd 1
  have hg_top : Subgroup.zpowers g = ⊤ := eq_top_iff.mpr fun x _ =>
    ⟨Multiplicative.toAdd x, by
      apply Multiplicative.toAdd.injective
      simp [g, toAdd_zpow]⟩
  have hrange : (zpowGroupHom m : Multiplicative ℤ →* Multiplicative ℤ).range =
      Subgroup.zpowers (g ^ m) := by
    ext x
    simp only [MonoidHom.mem_range, zpowGroupHom_apply, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨y, hy⟩ => ⟨Multiplicative.toAdd y, ?_⟩,
      fun ⟨k, hk⟩ => ⟨Multiplicative.ofAdd k, ?_⟩⟩
    · rw [← hy, ← zpow_mul]
      apply Multiplicative.toAdd.injective
      simp [g, toAdd_zpow, mul_comm]
    · rw [← hk, ← zpow_mul]
      apply Multiplicative.toAdd.injective
      simp [g, toAdd_zpow]
  have hord : orderOf g = 0 := orderOf_eq_zero_iff'.mpr fun n hn hgn => by
    have h0 : (n : ℤ) = 0 := by simpa [g, toAdd_pow] using congrArg Multiplicative.toAdd hgn
    omega
  rw [hrange, Subgroup.index_zpowers_zpow hg_top m, hord]
  simp

private def roseDartSign (e : (SerreGraph.rose Unit).E) : Bool := e.2

private theorem index_range_α_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (v₀ : (SerreGraph.rose Unit).V) (e : (SerreGraph.rose Unit).E)
    (hsrc : (SerreGraph.rose Unit).src e = v₀) :
    ((baumslagSolitar m n hm hn).αArrow
      (⟨e, hsrc, rfl⟩ : v₀ ⟶ (SerreGraph.rose Unit).tgt e)).range.index =
      cond (roseDartSign e) m.natAbs n.natAbs := by
  obtain ⟨⟨⟩, b⟩ := e
  cases v₀
  obtain rfl : hsrc = rfl := Subsingleton.elim _ _
  cases b
  · let e₀ : (SerreGraph.rose Unit).E := ((), false)
    exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (((baumslagSolitar m n hm hn).αArrow_mk e₀).trans
        (baumslagSolitar_α_false m n hm hn))).trans
      (index_range_zpowGroupHom_int n)
  · let e₁ : (SerreGraph.rose Unit).E := ((), true)
    exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (((baumslagSolitar m n hm hn).αArrow_mk e₁).trans
        (baumslagSolitar_α_true m n hm hn))).trans
      (index_range_zpowGroupHom_int m)

/-- Every vertex of the Bass–Serre tree of `BS(m, n)` has finite degree `|m| + |n|`. -/
theorem card_star_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (u : ((baumslagSolitar m n hm hn).bassSerreTree ()).V) :
    Nat.card {E : ((baumslagSolitar m n hm hn).bassSerreTree ()).E //
      ((baumslagSolitar m n hm hn).bassSerreTree ()).src E = u} =
      m.natAbs + n.natAbs := by
  let v₀ : (SerreGraph.rose Unit).V := ()
  refine bassSerreVertex_induction u fun {v} p => ?_
  obtain rfl : v = v₀ := rfl
  let starRoseEquivBool :
      {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀} ≃ Bool :=
    { toFun := fun e => roseDartSign e.1
      invFun := fun b => ⟨((), b), rfl⟩
      left_inv := fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl
      right_inv := fun _ => rfl }
  let instFintype : Fintype {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀} :=
    Fintype.ofEquiv Bool starRoseEquivBool.symm
  have instFinite : ∀ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀},
      Finite ((baumslagSolitar m n hm hn).vertexGroup v₀ ⧸
        ((baumslagSolitar m n hm hn).αArrow ⟨e.1, e.2, rfl⟩).range) := by
    intro e
    refine Nat.finite_of_card_ne_zero ?_
    rw [← Subgroup.index_eq_card, index_range_α_baumslagSolitar m n hm hn v₀ e.1 e.2]
    cases roseDartSign e.1
    · exact Int.natAbs_ne_zero.mpr hn
    · exact Int.natAbs_ne_zero.mpr hm
  rw [@card_bassSerreStar _ (baumslagSolitar m n hm hn) v₀ v₀ instFintype instFinite p]
  have hcongr : ∀ e : {e : (SerreGraph.rose Unit).E // (SerreGraph.rose Unit).src e = v₀},
      ((baumslagSolitar m n hm hn).αArrow ⟨e.1, e.2, rfl⟩).range.index =
        cond (starRoseEquivBool e) m.natAbs n.natAbs :=
    fun e => index_range_α_baumslagSolitar m n hm hn v₀ e.1 e.2
  simp_rw [hcongr]
  exact (Equiv.sum_comp starRoseEquivBool (fun b => cond b m.natAbs n.natAbs)).trans
    (Fintype.sum_bool _)

/-- For `BS(1, 2)`, the boundary images have indices `[A : α(C)] = 1` and `[A : ω(C)] = 2`, and
every vertex of the Bass–Serre tree has degree `3`. -/
theorem bassSerreTree_BS12 :
    let BS := baumslagSolitar 1 2 one_ne_zero two_ne_zero
    (BS.α (((), true) : (SerreGraph.rose Unit).E)).range.index = 1 ∧
      (BS.ω (((), true) : (SerreGraph.rose Unit).E)).range.index = 2 ∧
      ∀ u : (BS.bassSerreTree ()).V,
        Nat.card {E : (BS.bassSerreTree ()).E // (BS.bassSerreTree ()).src E = u} = 3 := by
  refine ⟨?_, ?_, fun u => card_star_baumslagSolitar 1 2 one_ne_zero two_ne_zero u⟩
  · exact (congrArg MonoidHom.range (baumslagSolitar_α_true 1 2 one_ne_zero two_ne_zero) ▸
      index_range_zpowGroupHom_int 1)
  · exact (congrArg MonoidHom.range (baumslagSolitar_ω_true 1 2 one_ne_zero two_ne_zero) ▸
      index_range_zpowGroupHom_int 2)

end BaumslagSolitar

/-! ### 4. Unquotiented homotopy classes of based `𝔸`-paths (`bassSerreTree_not_quotient_paths`) -/

section UnquotientedPaths

/-- A based `𝔸`-path starting at `v₀` up to homotopy, without quotienting on the right by the
terminal vertex group `A_v`. -/
structure HomotopyPathFrom : Type (max u v w) where
  /-- The endpoint vertex in `Γ`. -/
  vertex : Γ.V
  /-- The homotopy class of the `𝔸`-path from `v₀` to `vertex`. -/
  pathClass : Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨vertex⟩)

noncomputable instance : MulAction (π₁ 𝔸 v₀) (𝔸.HomotopyPathFrom v₀) where
  smul g x := ⟨x.vertex, π₁.lift (fun s => Quotient.lift (fun p => Quotient.mk _ (s.comp p))
      fun _ _ hp => Quotient.sound (Path.Homotopic.comp_left hp s))
    (fun _ _ hs => funext fun q => Quotient.inductionOn q fun p =>
      Quotient.sound (Path.Homotopic.comp_right hs p)) g x.pathClass⟩
  one_smul := fun ⟨v, q⟩ => Quotient.inductionOn q fun p => by
    simp [HSMul.hSMul, SMul.smul, ← π₁.mk_nil]
  mul_smul g h := fun ⟨v, q⟩ => π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    Quotient.inductionOn q fun p => by
      simp [HSMul.hSMul, SMul.smul, ← π₁.mk_comp]

/-- Without the right-coset relation `≈`, homotopy classes of based `𝔸`-paths carry a distinct
point `⟦ofVertex a⟧` at `v₀` for every `a ∈ A_{v₀}`, and the empty path has trivial stabilizer
under `π₁(𝔸, v₀)` instead of `(π₁.vertexHom nil).range ≅ A_{v₀}`. -/
theorem bassSerreTree_not_quotient_paths :
    Function.Injective (fun a : 𝔸.vertexGroup v₀ =>
      (⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex a)⟩ :
        𝔸.HomotopyPathFrom v₀)) ∧
    stabilizer (π₁ 𝔸 v₀)
      (⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil⟩ :
        𝔸.HomotopyPathFrom v₀) = ⊥ := by
  refine ⟨fun a b hab => ?_, eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_⟩
  · have hq : Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex a) =
        Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (Path.ofVertex b) := by
      injection hab
    exact Path.ofVertex_homotopic_ofVertex_iff.mp (Quotient.exact hq)
  · refine π₁.induction_on (P := fun g => g ∈ stabilizer (π₁ 𝔸 v₀) _ → g = 1) g (fun s hs => ?_) hg
    rw [mem_stabilizer_iff] at hs
    have hq : Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (s.comp Quiver.Path.nil) =
        Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil := by
      have hs' : (⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) (s.comp Quiver.Path.nil)⟩ :
          𝔸.HomotopyPathFrom v₀) = ⟨v₀, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v₀⟩) Quiver.Path.nil⟩ := by
        simpa [HSMul.hSMul, SMul.smul] using hs
      injection hs'
    rw [Quiver.Path.comp_nil] at hq
    exact π₁.mk_eq_mk_iff.mpr (Quotient.exact hq)

end UnquotientedPaths

/-! ### 5. Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- The graph of groups on two isolated vertices (`false` and `true`) with trivial vertex groups. -/
@[expose] def twoIsolated :
    GraphOfGroups.{0, 0, 0, 0} (SerreGraph.segment.restrict ∅ fun _ h => h.elim) :=
  (freeProductGraph PUnit PUnit).restrict ∅ (fun _ h => h.elim)

private instance : IsEmpty (SerreGraph.segment.restrict ∅ fun _ h => h.elim).E :=
  ⟨fun e => e.2.elim⟩

/-- Over two isolated vertices with basepoint at `false`, both the Bass–Serre tree `X` and its
quotient `X / π₁` have a single vertex, whereas the ambient graph has two vertices and no `𝔸`-path
connects `false` to `true` (so §4.2 supplies no based `π₁.vertexHom` for `true`). -/
theorem bassSerreTree_two_isolated :
    Nat.card (twoIsolated.bassSerreTree false).V = 1 ∧
      Nat.card (twoIsolated.bassSerreQuotient false).V = 1 ∧
      Nat.card (SerreGraph.segment.restrict ∅ fun _ h => h.elim).V = 2 ∧
      IsEmpty (twoIsolated.Path ⟨false⟩ ⟨true⟩) := by
  let Γ₀ := SerreGraph.segment.restrict ∅ fun _ h => h.elim
  let b₀ : Γ₀.V := false
  have hTreeCard : Nat.card (twoIsolated.bassSerreTree b₀).V = 1 := Nat.card_unique
  have hCompCard : Nat.card (Γ₀.component b₀).V = 1 := Nat.card_unique
  have hQuotCard : Nat.card (twoIsolated.bassSerreQuotient b₀).V = 1 :=
    (Nat.card_congr (twoIsolated.bassSerreQuotientIso b₀).equivV).trans hCompCard
  have hAmbCard : Nat.card Bool = 2 := by simp
  have hempty : IsEmpty (twoIsolated.Path ⟨false⟩ ⟨true⟩) := by
    refine ⟨fun p => ?_⟩
    have aux : ∀ {y : twoIsolated.LetterVertex}, twoIsolated.Path ⟨false⟩ y → y = ⟨false⟩ := by
      intro y q
      induction q with
      | nil => rfl
      | cons _ l ih =>
        cases l with
        | vertex _ => exact ih
        | dart e => exact e.1.2.elim
    cases aux p
  exact ⟨hTreeCard, hQuotCard, hAmbCard, hempty⟩

end Disconnected

end GraphOfGroups

end TauCeti
