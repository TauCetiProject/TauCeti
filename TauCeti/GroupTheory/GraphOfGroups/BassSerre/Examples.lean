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
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Canonical examples and checks for the Bass–Serre tree

This file verifies the Bass–Serre tree construction (`GraphOfGroups.bassSerreTree`) on five
canonical families and boundary cases:

1. **Edgeless graphs** (`GraphOfGroups.bassSerreTree_point`): over `SerreGraph.noEdge PUnit`,
   `X(𝔸, ())` has a single vertex `1 · A_{()}` without darts and is isomorphic as a Serre graph to
   `SerreGraph.noEdge PUnit`.
2. **Free products and `ℤ ∗ ℤ`** (`GraphOfGroups.freeProductStarEquiv`,
   `GraphOfGroups.freeProductAdjacentEquiv`, `GraphOfGroups.bassSerreTree_free_product`): for
   `A ∗ B` (`GraphOfGroups.freeProductGraph A B`), the neighbours of the base vertex `1 · A`
   correspond bijectively to `A` via `a ↦ (a · e) B`; for `ℤ ∗ ℤ` the base vertex has countably
   infinitely many neighbours `a^k ⟨b⟩` and degree `ℵ₀`.
3. **Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)`** (`GraphOfGroups.card_star_baumslagSolitar`,
   `GraphOfGroups.bassSerreTree_BS12`): for `GraphOfGroups.baumslagSolitar m n hm hn`, every vertex
   of `X` has degree `|m| + |n|`; for `BS(1, 2)`, the boundary indices are `1` and `2` and every
   vertex has degree `3`.
4. **Unquotiented homotopy classes of based `𝔸`-paths** (`GraphOfGroups.HomotopyPathFrom`,
   `GraphOfGroups.bassSerreTree_not_quotient_paths`): without the left-coset equivalence `p ≈ p a`,
   homotopy classes of based paths have a distinct point at `v₀` for every `a ∈ A_{v₀}` and trivial
   basepoint stabilizer.
5. **Disconnected underlying graphs** (`GraphOfGroups.twoIsolated`,
   `GraphOfGroups.bassSerreTree_two_isolated`): over two isolated vertices, both `X(𝔸, v₀)` and
   its quotient `X(𝔸, v₀) / π₁(𝔸, v₀)` have a single vertex while the ambient graph has two.

## Main definitions

* `TauCeti.GraphOfGroups.freeProductStarEquiv`, `TauCeti.GraphOfGroups.freeProductAdjacentEquiv`:
  basepoint star and neighbour bijections with `A` for `GraphOfGroups.freeProductGraph A B`.
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

universe u v w x u' v'

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-! ### 1. Graphs without edges (`bassSerreTree_point`) -/

section Edgeless

/-- For any graph of groups over the one-vertex edgeless graph `SerreGraph.noEdge PUnit`, the
Bass–Serre tree is a single point without darts. -/
theorem bassSerreTree_point (𝔸 : GraphOfGroups.{u, v, w, x} (SerreGraph.noEdge.{u, v} PUnit)) :
    Nonempty ((𝔸.bassSerreTree PUnit.unit).toSerreGraph.Iso (SerreGraph.noEdge.{u', v'} PUnit)) ∧
      Subsingleton (𝔸.bassSerreTree PUnit.unit).V ∧
      IsEmpty (𝔸.bassSerreTree PUnit.unit).E :=
  ⟨⟨𝔸.bassSerreTreeIsoPoint PUnit.unit⟩, inferInstance, inferInstance⟩

end Edgeless

/-! ### 2. Free products and `ℤ ∗ ℤ` (`bassSerreTree_free_product`) -/

section FreeProduct

private theorem freeProductGraph_αArrow_range (A B : Type w) [Group A] [Group B]
    (v₀ : SerreGraph.segment.V) (hv₀ : v₀ = false) :
    let e : {e : SerreGraph.segment.E // SerreGraph.segment.src e = v₀} := default
    ((freeProductGraph A B).αArrow (⟨e.1, e.2, rfl⟩ : v₀ ⟶ SerreGraph.segment.tgt e.1)).range =
      (⊥ : Subgroup ((freeProductGraph A B).vertexGroup v₀)) := by
  subst hv₀
  intro e
  obtain ⟨b, hb⟩ := e
  obtain rfl : b = false := (SerreGraph.segment_src b).symm.trans hb
  obtain rfl : hb = rfl := Subsingleton.elim _ _
  exact (congrArg (fun f : PUnit →* A => f.range)
    (((freeProductGraph A B).αArrow_mk (false : SerreGraph.segment.E)).trans
      (freeProductGraph_α_false A B))).trans
    MonoidHom.range_one

/-- In the Bass–Serre tree of `A ∗ B`, the outgoing darts at the base vertex `1 · A` correspond
bijectively to the elements of `A`. -/
noncomputable def freeProductStarEquiv (A B : Type w) [Group A] [Group B] :
    {E : ((freeProductGraph A B).bassSerreTree false).E //
      ((freeProductGraph A B).bassSerreTree false).src E =
        (freeProductGraph A B).bassSerreBaseVertex false} ≃ A :=
  let v₀ : SerreGraph.segment.V := false
  ((((Equiv.subtypeEquivRight fun _ =>
      Iff.of_eq (congrArg _ (bassSerreBaseVertex_def (freeProductGraph A B) v₀))).trans
    ((freeProductGraph A B).bassSerreStarEquiv v₀ .nil)).trans
    (Equiv.uniqueSigma _)).trans
    (Subgroup.quotientEquivOfEq (freeProductGraph_αArrow_range A B v₀ rfl))).trans
    (QuotientGroup.quotientBot (G := (freeProductGraph A B).vertexGroup v₀)).toEquiv

@[simp] theorem freeProductStarEquiv_symm_apply_val (A B : Type w) [Group A] [Group B] (a : A) :
    ((freeProductStarEquiv A B).symm a).1 =
      (freeProductGraph A B).bassSerreDart false (false : SerreGraph.segment.E)
        (Path.ofVertex a) := by
  let v₀ : SerreGraph.segment.V := false
  let a' : (freeProductGraph A B).vertexGroup v₀ := a
  let d : {e : SerreGraph.segment.E // SerreGraph.segment.src e = v₀} := default
  let e₁ := Equiv.subtypeEquivRight fun (E : ((freeProductGraph A B).bassSerreTree v₀).E) =>
    Iff.of_eq (congrArg (((freeProductGraph A B).bassSerreTree v₀).src E = ·)
      (bassSerreBaseVertex_def (freeProductGraph A B) v₀))
  let e₂ := (freeProductGraph A B).bassSerreStarEquiv v₀ .nil
  let e₃ := Equiv.uniqueSigma fun e : {e : SerreGraph.segment.E // SerreGraph.segment.src e = v₀} =>
    (freeProductGraph A B).vertexGroup v₀ ⧸ ((freeProductGraph A B).αArrow ⟨e.1, e.2, rfl⟩).range
  let e₄ := Subgroup.quotientEquivOfEq (freeProductGraph_αArrow_range A B v₀ rfl)
  let e₅ := (QuotientGroup.quotientBot (G := (freeProductGraph A B).vertexGroup v₀)).toEquiv
  have h5 : e₅.symm a' = (a' : (freeProductGraph A B).vertexGroup v₀ ⧸ ⊥) :=
    QuotientGroup.quotientBot_symm_apply a'
  have hq : e₄.symm (e₅.symm a') =
      (a' : (freeProductGraph A B).vertexGroup v₀ ⧸
        ((freeProductGraph A B).αArrow ⟨d.1, d.2, rfl⟩).range) :=
    (congrArg e₄.symm h5).trans
      ((Equiv.symm_apply_eq e₄).mpr (Subgroup.quotientEquivOfEq_mk _ a').symm)
  have hsymm : (freeProductStarEquiv A B).symm a =
      e₁.symm (e₂.symm ⟨d, (a' : (freeProductGraph A B).vertexGroup v₀ ⧸
        ((freeProductGraph A B).αArrow ⟨d.1, d.2, rfl⟩).range)⟩) :=
    (Equiv.symm_trans_apply (((e₁.trans e₂).trans e₃).trans e₄) e₅ a').trans <|
      (Equiv.symm_trans_apply ((e₁.trans e₂).trans e₃) e₄ (e₅.symm a')).trans <|
      (Equiv.symm_trans_apply (e₁.trans e₂) e₃ (e₄.symm (e₅.symm a'))).trans <|
      (congrArg (e₁.trans e₂).symm
        ((Equiv.uniqueSigma_symm_apply _).trans (congrArg (Sigma.mk d) hq))).trans
      (Equiv.symm_trans_apply e₁ e₂ _)
  have h1 : ((freeProductStarEquiv A B).symm a).1 =
      (e₂.symm ⟨d, (a' : (freeProductGraph A B).vertexGroup v₀ ⧸
        ((freeProductGraph A B).αArrow ⟨d.1, d.2, rfl⟩).range)⟩).1 :=
    (congrArg Subtype.val hsymm).trans (Equiv.subtypeEquivRight_symm_apply_coe _ _)
  have hd : ∀ x : {e : SerreGraph.segment.E // SerreGraph.segment.src e = v₀},
      (freeProductGraph A B).bassSerreDartOfSrcEq v₀ x.1 x.2
        (Quiver.Path.nil.cons (Letter.vertex a')) =
      (freeProductGraph A B).bassSerreDart v₀ false (Path.ofVertex a') := by
    intro x
    obtain rfl : x = ⟨false, rfl⟩ := Subsingleton.elim _ _
    exact (bassSerreDartOfSrcEq_rfl (𝔸 := freeProductGraph A B) (false : SerreGraph.segment.E)
      (Quiver.Path.nil.cons (Letter.vertex a'))).trans
      (congrArg ((freeProductGraph A B).bassSerreDart v₀ false) (Path.ofVertex_eq_nil_cons a').symm)
  exact h1.trans ((bassSerreStarEquiv_symm_apply_val .nil d a').trans (hd d))

/-- In the Bass–Serre tree of `A ∗ B`, the neighbours of the base vertex `1 · A` correspond
bijectively to `A` via `a ↦ (a · e) B`. -/
noncomputable def freeProductAdjacentEquiv (A B : Type w) [Group A] [Group B] :
    A ≃ {w : ((freeProductGraph A B).bassSerreTree false).V //
      Nonempty ((freeProductGraph A B).bassSerreBaseVertex false ⟶ w)} :=
  let v₀ : SerreGraph.segment.V := false
  (freeProductStarEquiv A B).symm.trans
    (((freeProductGraph A B).bassSerreTree v₀).isTree.isAcyclic.starEquivAdjacent
      ((freeProductGraph A B).bassSerreBaseVertex v₀))

@[simp] theorem freeProductAdjacentEquiv_apply_val (A B : Type w) [Group A] [Group B] (a : A) :
    (freeProductAdjacentEquiv A B a).1 =
      (freeProductGraph A B).bassSerreVertex false
        ((Path.ofVertex a).cons (Letter.dart (SerreGraph.segment.dart false))) := by
  rw [freeProductAdjacentEquiv, Equiv.trans_apply, SerreGraph.IsAcyclic.starEquivAdjacent_apply_val,
    freeProductStarEquiv_symm_apply_val]
  exact bassSerreTree_tgt_dart (𝔸 := freeProductGraph A B) (v₀ := (false : SerreGraph.segment.V))
    (false : SerreGraph.segment.E) (Path.ofVertex a)

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
      freeProductAdjacentEquiv_apply_val (Multiplicative ℤ) (Multiplicative ℤ)
        (Multiplicative.ofAdd k)⟩, ?_⟩
  rw [Cardinal.mk_congr ((freeProductStarEquiv (Multiplicative ℤ) (Multiplicative ℤ)).trans
    Multiplicative.toAdd), Cardinal.mk_int]

end FreeProduct

/-! ### 3. Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)` (`bassSerreTree_BS12`) -/

section BaumslagSolitar

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
      (Subgroup.index_range_zpowGroupHom_int n)
  · let e₁ : (SerreGraph.rose Unit).E := ((), true)
    exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (((baumslagSolitar m n hm hn).αArrow_mk e₁).trans
        (baumslagSolitar_α_true m n hm hn))).trans
      (Subgroup.index_range_zpowGroupHom_int m)

/-- Every vertex of the Bass–Serre tree of `BS(m, n)` has finite degree `|m| + |n|`. -/
theorem card_star_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (u : ((baumslagSolitar m n hm hn).bassSerreTree ()).V) :
    Nat.card {E : ((baumslagSolitar m n hm hn).bassSerreTree ()).E //
      ((baumslagSolitar m n hm hn).bassSerreTree ()).src E = u} =
      m.natAbs + n.natAbs := by
  let v₀ : (SerreGraph.rose Unit).V := ()
  refine bassSerreVertex_induction_on u fun {v} p => ?_
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
  · exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (baumslagSolitar_α_true 1 2 one_ne_zero two_ne_zero)).trans
      (Subgroup.index_range_zpowGroupHom_int 1)
  · exact (congrArg (fun f : Multiplicative ℤ →* Multiplicative ℤ => f.range.index)
      (baumslagSolitar_ω_true 1 2 one_ne_zero two_ne_zero)).trans
      (Subgroup.index_range_zpowGroupHom_int 2)

end BaumslagSolitar

/-! ### 4. Unquotiented homotopy classes of based `𝔸`-paths (`bassSerreTree_not_quotient_paths`) -/

section UnquotientedPaths

/-- A based `𝔸`-path starting at `v₀` up to homotopy, without quotienting on the right by the
terminal vertex group `A_v`. -/
@[ext] structure HomotopyPathFrom : Type (max u v w) where
  /-- The endpoint vertex in `Γ`. -/
  vertex : Γ.V
  /-- The homotopy class of the `𝔸`-path from `v₀` to `vertex`. -/
  pathClass : Quotient (Path.setoid 𝔸 ⟨v₀⟩ ⟨vertex⟩)

namespace HomotopyPathFrom

variable {𝔸 v₀}

/-- The homotopy class of an `𝔸`-path `p` from `v₀` to `v` in `𝔸.HomotopyPathFrom v₀`. -/
@[expose] def ofPath {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) : 𝔸.HomotopyPathFrom v₀ :=
  ⟨v, Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) p⟩

@[simp] theorem ofPath_vertex {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (ofPath p).vertex = v :=
  (rfl)

@[simp] theorem ofPath_pathClass {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (ofPath p).pathClass = Quotient.mk (Path.setoid 𝔸 ⟨v₀⟩ ⟨v⟩) p :=
  (rfl)

/-- Prove a property of `𝔸.HomotopyPathFrom v₀` by checking it on `𝔸`-paths starting at `v₀`. -/
@[elab_as_elim] theorem induction_on {P : 𝔸.HomotopyPathFrom v₀ → Prop}
    (x : 𝔸.HomotopyPathFrom v₀)
    (h : ∀ {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), P (ofPath p)) : P x := by
  rcases x with ⟨v, q⟩
  exact Quotient.inductionOn q fun p => h p

@[simp] theorem ofPath_eq_ofPath_iff {v : Γ.V} {p q : 𝔸.Path ⟨v₀⟩ ⟨v⟩} :
    ofPath p = ofPath q ↔ p.Homotopic q := by
  refine ⟨fun h => ?_, fun h => congrArg (HomotopyPathFrom.mk v) (Quotient.sound h)⟩
  injection h with _ hq
  exact Quotient.exact hq

/-- `π₁(𝔸, v₀)` acts on `𝔸.HomotopyPathFrom v₀` on the left by concatenating closed `𝔸`-paths at
`v₀`. -/
noncomputable instance : SMul (π₁ 𝔸 v₀) (𝔸.HomotopyPathFrom v₀) where
  smul g x := ⟨x.vertex, π₁.lift (fun s => Quotient.lift (fun p => Quotient.mk _ (s.comp p))
      fun _ _ hp => Quotient.sound (Path.Homotopic.comp_left hp s))
    (fun _ _ hs => funext fun q => Quotient.inductionOn q fun p =>
      Quotient.sound (Path.Homotopic.comp_right hs p)) g x.pathClass⟩

@[simp] theorem smul_vertex (g : π₁ 𝔸 v₀) (x : 𝔸.HomotopyPathFrom v₀) :
    (g • x).vertex = x.vertex :=
  (rfl)

@[simp] theorem mk_smul_ofPath (s : 𝔸.Path ⟨v₀⟩ ⟨v₀⟩) {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    π₁.mk s • ofPath p = ofPath (s.comp p) :=
  HomotopyPathFrom.ext rfl (heq_of_eq (congrFun (π₁.lift_mk _ _ s) _))

/-- `π₁(𝔸, v₀)` acts on `𝔸.HomotopyPathFrom v₀` on the left by concatenating closed `𝔸`-paths at
`v₀`. -/
noncomputable instance : MulAction (π₁ 𝔸 v₀) (𝔸.HomotopyPathFrom v₀) where
  one_smul x := induction_on x fun p => by
    rw [← π₁.mk_nil, mk_smul_ofPath, Quiver.Path.nil_comp]
  mul_smul g h x := π₁.induction_on g fun s₁ => π₁.induction_on h fun s₂ =>
    induction_on x fun p => by
      rw [← π₁.mk_comp, mk_smul_ofPath, mk_smul_ofPath, mk_smul_ofPath, Quiver.Path.comp_assoc]

end HomotopyPathFrom

/-- Without the left-coset relation `≈`, homotopy classes of based `𝔸`-paths carry a distinct
point `ofPath (ofVertex a)` at `v₀` for every `a ∈ A_{v₀}`, and the empty path has trivial
stabilizer under `π₁(𝔸, v₀)` instead of `(π₁.vertexHom nil).range ≅ A_{v₀}`. -/
theorem bassSerreTree_not_quotient_paths :
    Function.Injective (fun a : 𝔸.vertexGroup v₀ =>
      HomotopyPathFrom.ofPath (v₀ := v₀) (Path.ofVertex a)) ∧
    stabilizer (π₁ 𝔸 v₀)
      (HomotopyPathFrom.ofPath (𝔸 := 𝔸) (v₀ := v₀) Quiver.Path.nil) = ⊥ := by
  refine ⟨fun a b hab => ?_, eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_⟩
  · exact Path.ofVertex_homotopic_ofVertex_iff.mp (HomotopyPathFrom.ofPath_eq_ofPath_iff.mp hab)
  · refine π₁.induction_on (P := fun g => g ∈ stabilizer (π₁ 𝔸 v₀) _ → g = 1) g (fun s hs => ?_) hg
    rw [mem_stabilizer_iff, HomotopyPathFrom.mk_smul_ofPath, Quiver.Path.comp_nil,
      HomotopyPathFrom.ofPath_eq_ofPath_iff] at hs
    rw [← π₁.mk_nil, π₁.mk_eq_mk_iff]
    exact hs

end UnquotientedPaths

/-! ### 5. Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- The graph of groups on two isolated vertices (`false` and `true`) with trivial vertex groups. -/
def twoIsolated : GraphOfGroups.{0, 0, 0, 0} (SerreGraph.noEdge.{0, 0} Bool) :=
  GraphOfGroups.trivial (SerreGraph.noEdge.{0, 0} Bool)

theorem twoIsolated_def :
    twoIsolated = GraphOfGroups.trivial (SerreGraph.noEdge.{0, 0} Bool) :=
  (rfl)

/-- Over two isolated vertices with basepoint at `false`, both the Bass–Serre tree `X` and its
quotient `X / π₁` have a single vertex, whereas the ambient graph has two vertices and no `𝔸`-path
connects `false` to `true` (so there is no based homomorphism `π₁.vertexHom p` from the vertex group
at `true` into `π₁(𝔸, false)`). -/
theorem bassSerreTree_two_isolated :
    Nat.card (twoIsolated.bassSerreTree false).V = 1 ∧
      Nat.card (twoIsolated.bassSerreQuotient false).V = 1 ∧
      Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 ∧
      IsEmpty (twoIsolated.Path ⟨false⟩ ⟨true⟩) :=
  ⟨Nat.card_unique,
    (Nat.card_congr (twoIsolated.bassSerreQuotientIso false).equivV).trans Nat.card_unique,
    Nat.card_eq_fintype_card.trans Fintype.card_bool,
    ⟨fun p => Bool.false_ne_true (SerreGraph.noEdge_nonempty_path_iff.mp ⟨p.edgePath⟩)⟩⟩

end Disconnected

end GraphOfGroups

end TauCeti
