/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import TauCeti.AlgebraicTopology.SimplicialObject.Cylinder

/-!
# Simplicial homotopies and chain homotopies across the Dold–Kan correspondence

In an idempotent-complete preadditive category `C` with finite coproducts, the Dold–Kan
correspondence identifies simplicial objects in `C` with non-negatively graded chain complexes in
`C` via `CategoryTheory.Idempotents.DoldKan.equivalence`. By Satz 3.31 of Dold and Puppe's
*Homologie nicht-additiver Funktoren*, this equivalence also identifies combinatorial simplicial
homotopies `CategoryTheory.SimplicialObject.Homotopy f g` with chain homotopies between the induced
chain maps on alternating face map complexes or normalized chain complexes.

While the forward direction (`SimplicialObject.Homotopy.toChainHomotopy`) holds in any preadditive
category, the converse requires producing a simplicial morphism `(cylinder C).obj X ⟶ Y` out of a
chain homotopy between `(alternatingFaceMapComplex C).map f` and
`(alternatingFaceMapComplex C).map g`. We construct an explicit chain map
`cylinderChainMap H : K[(cylinder C).obj X] ⟶ K[Y]` whose restrictions along `cylinderι₀` and
`cylinderι₁` equal `K.map f` and `K.map g`, restrict it to the normalized summand
`Idempotents.DoldKan.N`, transport it across the full faithfulness of `N` to obtain a morphism
`(cylinder C).obj X ⟶ Y`, and apply `Homotopy.ofCylinderHom`.

## Main definitions and results

* `CategoryTheory.Idempotents.DoldKan.homotopyEquivNAlternatingFaceMapComplex`: the homotopy
  equivalence `HomotopyEquiv (N.obj X) ((alternatingFaceMapComplex C).obj X)` in any
  idempotent-complete preadditive category with finite coproducts.
* `CategoryTheory.SimplicialObject.cylinderChainMap`: explicit chain map
  `K[(cylinder C).obj X] ⟶ K[Y]` lifting a chain homotopy between `K.map f` and `K.map g`.
* `CategoryTheory.SimplicialObject.Homotopy.ofAlternatingFaceMapComplexHomotopy`,
  `CategoryTheory.SimplicialObject.Homotopy.ofNHomotopy`,
  `CategoryTheory.SimplicialObject.Homotopy.ofNormalizedMooreComplexHomotopy`: constructs a
  simplicial homotopy `Homotopy f g` from a chain homotopy on alternating face map complexes,
  pseudoabelian normalized chains `N`, or abelian normalized Moore complexes.
* `CategoryTheory.SimplicialObject.Homotopy.symm`,
  `CategoryTheory.SimplicialObject.Homotopy.trans`: symmetry and transitivity of simplicial
  homotopies in an idempotent-complete preadditive category with finite coproducts.
* `CategoryTheory.SimplicialObject.nonempty_homotopy_iff_alternatingFaceMapComplex`,
  `CategoryTheory.SimplicialObject.nonempty_homotopy_iff_N`,
  `CategoryTheory.SimplicialObject.nonempty_homotopy_iff_normalizedMooreComplex`: two simplicial
  morphisms are simplicially homotopic if and only if their induced chain maps are chain homotopic
  (Dold–Puppe, Satz 3.31).
* `CategoryTheory.SimplicialObject.HomotopyEquiv.ofAlternatingFaceMapComplexHomotopyEquiv`,
  `CategoryTheory.SimplicialObject.homotopyEquivalences_alternatingFaceMapComplex_map_iff`: a
  simplicial morphism induces a chain homotopy equivalence on alternating face map complexes if and
  only if it is a simplicial homotopy equivalence.
* `CategoryTheory.Idempotents.DoldKan.Γ.mapHomotopy`,
  `CategoryTheory.Idempotents.DoldKan.Γ.mapHomotopyEquiv`: the inverse Dold–Kan functor `Γ` carries
  chain homotopies to simplicial homotopies and chain homotopy equivalences to simplicial homotopy
  equivalences.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §3.31.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter III, Corollary 2.16.
-/

public noncomputable section

universe v u

open CategoryTheory Limits Opposite SimplexCategory AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial DoldKan

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

/-- In an idempotent-complete preadditive category with finite coproducts, the inclusion
`inclusionN.app X` and projection `PInftyToN.app X` form a chain homotopy equivalence between the
normalized chains `N.obj X` and the alternating face map complex `K[X]`. -/
def homotopyEquivNAlternatingFaceMapComplex (X : SimplicialObject C) :
    HomotopyEquiv (N.obj X) ((alternatingFaceMapComplex C).obj X) where
  hom := inclusionN.app X
  inv := PInftyToN.app X
  homotopyHomInvId := Homotopy.ofEq (inclusionN_app_comp_PInftyToN_app X)
  homotopyInvHomId :=
    (Homotopy.ofEq (PInftyToN_app_comp_inclusionN_app X)).trans (homotopyPInftyToId X)

@[simp]
lemma homotopyEquivNAlternatingFaceMapComplex_hom (X : SimplicialObject C) :
    (homotopyEquivNAlternatingFaceMapComplex X).hom = inclusionN.app X :=
  (rfl)

@[simp]
lemma homotopyEquivNAlternatingFaceMapComplex_inv (X : SimplicialObject C) :
    (homotopyEquivNAlternatingFaceMapComplex X).inv = PInftyToN.app X :=
  (rfl)

end CategoryTheory.Idempotents.DoldKan

namespace CategoryTheory.SimplicialObject

section CylinderChainMap

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Degree-`m` component of a chain homotopy on alternating face map complexes, typed directly as a
morphism `X _⦋m⦌ ⟶ Y _⦋m + 1⦌`. -/
private def homotopyHom {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g))
    (m : ℕ) : X _⦋m⦌ ⟶ Y _⦋m + 1⦌ :=
  H.hom m (m + 1)

/-- Component of `cylinderChainMap H` on the summand of `((cylinder C).obj X) _⦋n⦌` indexed by
`α : ⦋n⦌ ⟶ ⦋1⦌`. In positive degree `m + 1`, it evaluates `g` when `α 0 = 1`, `f` when `α 0 = 0`
and `α 1 = 0`, and `f - X.δ 0 ≫ H.hom m (m + 1)` when `α` jumps from `0` to `1` between vertices
`0` and `1`. -/
private def cylinderChainMapTerm {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    ∀ n : ℕ, (⦋n⦌ ⟶ ⦋1⦌) → (X _⦋n⦌ ⟶ Y _⦋n⦌)
  | 0, α => if α.toOrderHom 0 = 0 then f.app (op ⦋0⦌) else g.app (op ⦋0⦌)
  | m + 1, α =>
      if α.toOrderHom 0 = 1 then g.app (op ⦋m + 1⦌)
      else if α.toOrderHom 1 = 0 then f.app (op ⦋m + 1⦌)
      else f.app (op ⦋m + 1⦌) - X.δ 0 ≫ homotopyHom H m

private lemma δ_comp_toOrderHom_apply {n : ℕ} (i : Fin (n + 2)) (α : ⦋n + 1⦌ ⟶ ⦋1⦌)
    (k : Fin (n + 1)) :
    (SimplexCategory.δ i ≫ α).toOrderHom k = α.toOrderHom (i.succAbove k) :=
  rfl

private lemma fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

private lemma orderHom_one_of_zero_eq_one {n : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋1⦌)
    (h0 : α.toOrderHom 0 = 1) (k : Fin (n + 2)) :
    α.toOrderHom k = 1 := by
  have hk : (1 : Fin 2) ≤ α.toOrderHom k := h0 ▸ α.toOrderHom.monotone (Fin.zero_le k)
  rcases fin2_eq_zero_or_one (α.toOrderHom k) with h | h
  · rw [h] at hk
    exact absurd hk (by decide)
  · exact h

private lemma cylinderChainMapTerm_comm_zero {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g))
    (α : ⦋1⦌ ⟶ ⦋1⦌) :
    cylinderChainMapTerm H 1 α ≫ AlternatingFaceMapComplex.objD Y 0 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
        (X.δ i ≫ cylinderChainMapTerm H 0 (SimplexCategory.δ i ≫ α)) := by
  have hf := ((alternatingFaceMapComplex C).map f).comm (0 + 1) 0
  have hg := ((alternatingFaceMapComplex C).map g).comm (0 + 1) 0
  simp only [alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d] at hf hg
  have hH := H.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at hH
  simp only [alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d] at hH
  have ht0 : cylinderChainMapTerm H 0 (SimplexCategory.δ 0 ≫ α) =
      if α.toOrderHom 1 = 0 then f.app (op ⦋0⦌) else g.app (op ⦋0⦌) := by
    rw [cylinderChainMapTerm, δ_comp_toOrderHom_apply]; rfl
  have ht1 : cylinderChainMapTerm H 0 (SimplexCategory.δ 1 ≫ α) =
      if α.toOrderHom 0 = 0 then f.app (op ⦋0⦌) else g.app (op ⦋0⦌) := by
    rw [cylinderChainMapTerm, δ_comp_toOrderHom_apply]; rfl
  rw [Fin.sum_univ_two, ht0, ht1]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
  rcases fin2_eq_zero_or_one (α.toOrderHom 0) with h0 | h0
  · rcases fin2_eq_zero_or_one (α.toOrderHom 1) with h1 | h1
    · have h0' : α.toOrderHom 0 ≠ 1 := by rw [h0]; decide
      rw [cylinderChainMapTerm, ite_eq_right h0', ite_eq_left h1, ite_eq_left h1, ite_eq_left h0,
        hf, AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Fin.sum_univ_two]
      simp
    · have h0' : α.toOrderHom 0 ≠ 1 := by rw [h0]; decide
      have h1' : α.toOrderHom 1 ≠ 0 := by rw [h1]; decide
      have hH' : homotopyHom H 0 ≫ AlternatingFaceMapComplex.objD Y 0 =
          f.app (op ⦋0⦌) - g.app (op ⦋0⦌) := eq_sub_of_add_eq hH.symm
      rw [cylinderChainMapTerm, ite_eq_right h0', ite_eq_right h1', ite_eq_right h1',
        ite_eq_left h0, Preadditive.sub_comp, Category.assoc, hH', hf,
        AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Fin.sum_univ_two,
        Preadditive.comp_sub]
      simp
      abel
  · have h1 : α.toOrderHom 1 = 1 := orderHom_one_of_zero_eq_one α h0 1
    have h1' : α.toOrderHom 1 ≠ 0 := by rw [h1]; decide
    have h0' : α.toOrderHom 0 ≠ 0 := by rw [h0]; decide
    rw [cylinderChainMapTerm, ite_eq_left h0, ite_eq_right h1', ite_eq_right h0', hg,
      AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Fin.sum_univ_two]
    simp

private lemma cylinderChainMapTerm_δ_succ_succ {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g))
    (m : ℕ) (α : ⦋m + 2⦌ ⟶ ⦋1⦌) (k : Fin (m + 1)) :
    cylinderChainMapTerm H (m + 1) (SimplexCategory.δ k.succ.succ ≫ α) =
      if α.toOrderHom 0 = 1 then g.app (op ⦋m + 1⦌)
      else if α.toOrderHom 1 = 0 then f.app (op ⦋m + 1⦌)
      else f.app (op ⦋m + 1⦌) - X.δ 0 ≫ homotopyHom H m := by
  have hk0 : (SimplexCategory.δ k.succ.succ ≫ α).toOrderHom 0 = α.toOrderHom 0 := rfl
  have hk1 : (SimplexCategory.δ k.succ.succ ≫ α).toOrderHom 1 = α.toOrderHom 1 := by
    rw [δ_comp_toOrderHom_apply, Fin.succAbove_of_castSucc_lt _ _ (Fin.one_lt_succ_succ k)]
    rfl
  rw [cylinderChainMapTerm, hk0, hk1]

private lemma cylinderChainMapTerm_comm_succ_jump {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g))
    (m : ℕ) (α : ⦋m + 2⦌ ⟶ ⦋1⦌)
    (h0 : α.toOrderHom 0 = 0) (h1 : α.toOrderHom 1 = 1) :
    cylinderChainMapTerm H (m + 2) α ≫ AlternatingFaceMapComplex.objD Y (m + 1) =
      ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) •
        (X.δ i ≫ cylinderChainMapTerm H (m + 1) (SimplexCategory.δ i ≫ α)) := by
  have h12 : (1 : Fin (m + 3)) ≤ (1 : Fin (m + 2)).succ := by
    rw [← Fin.succ_zero_eq_one, Fin.succ_le_succ_iff]
    exact Fin.zero_le 1
  have h2 : α.toOrderHom ((1 : Fin (m + 2)).succ) = 1 := by
    have hm : (1 : Fin 2) ≤ α.toOrderHom ((1 : Fin (m + 2)).succ) :=
      h1 ▸ α.toOrderHom.monotone h12
    rcases fin2_eq_zero_or_one (α.toOrderHom ((1 : Fin (m + 2)).succ)) with h | h
    · rw [h] at hm; exact absurd hm (by decide)
    · exact h
  have hf := ((alternatingFaceMapComplex C).map f).comm (m + 1 + 1) (m + 1)
  have hH := H.comm (m + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hH
  simp only [alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d] at hf hH
  -- Rewrite `hH` in terms of `homotopyHom` so all summands share the syntactic hom-type
  -- `X _⦋m + 1⦌ ⟶ Y _⦋m + 1⦌`.
  change f.app (op ⦋m + 1⦌) =
    AlternatingFaceMapComplex.objD X m ≫ homotopyHom H m +
      homotopyHom H (m + 1) ≫ AlternatingFaceMapComplex.objD Y (m + 1) +
      g.app (op ⦋m + 1⦌) at hH
  have h0' : α.toOrderHom 0 ≠ 1 := by rw [h0]; decide
  have h1' : α.toOrderHom 1 ≠ 0 := by rw [h1]; decide
  have h2' : α.toOrderHom ((1 : Fin (m + 2)).succ) ≠ 0 := by rw [h2]; decide
  have ht0 : cylinderChainMapTerm H (m + 1) (SimplexCategory.δ 0 ≫ α) = g.app (op ⦋m + 1⦌) := by
    have hd0 : (SimplexCategory.δ (0 : Fin (m + 3)) ≫ α).toOrderHom 0 = α.toOrderHom 1 := rfl
    rw [cylinderChainMapTerm, hd0, ite_eq_left h1]
  have ht_succ : ∀ j : Fin (m + 2),
      cylinderChainMapTerm H (m + 1) (SimplexCategory.δ j.succ ≫ α) =
        f.app (op ⦋m + 1⦌) - X.δ 0 ≫ homotopyHom H m := by
    refine Fin.cases ?_ (fun k ↦ ?_)
    · have hd10 : (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α).toOrderHom 0 =
          α.toOrderHom 0 := rfl
      have hd11 : (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α).toOrderHom 1 =
          α.toOrderHom ((1 : Fin (m + 2)).succ) := rfl
      rw [cylinderChainMapTerm, hd10, hd11, ite_eq_right h0', ite_eq_right h2']
    · rw [cylinderChainMapTerm_δ_succ_succ, ite_eq_right h0', ite_eq_right h1']
  have hLHS : cylinderChainMapTerm H (m + 2) α =
      f.app (op ⦋m + 1 + 1⦌) - X.δ 0 ≫ homotopyHom H (m + 1) := by
    rw [cylinderChainMapTerm, ite_eq_right h0', ite_eq_right h1']
  rw [hLHS, Preadditive.sub_comp, hf, Category.assoc, Fin.sum_univ_succ, ht0]
  simp only [Fin.val_zero, pow_zero, one_smul, ht_succ, Preadditive.comp_sub, smul_sub,
    Finset.sum_sub_distrib]
  have hf_sum : AlternatingFaceMapComplex.objD X (m + 1) ≫ f.app (op ⦋m + 1⦌) =
      X.δ 0 ≫ f.app (op ⦋m + 1⦌) +
        ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j.succ : ℕ) • (X.δ j.succ ≫ f.app (op ⦋m + 1⦌)) := by
    rw [AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Fin.sum_univ_succ]
    simp
  have hδ_sum : ∑ j : Fin (m + 2),
        (-1 : ℤ) ^ (j.succ : ℕ) • (X.δ j.succ ≫ X.δ 0 ≫ homotopyHom H m) =
      -(X.δ 0 ≫ AlternatingFaceMapComplex.objD X m ≫ homotopyHom H m) := by
    rw [AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Preadditive.comp_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [X.δ_comp_δ_assoc (Fin.zero_le j), Fin.castSucc_zero, Fin.val_succ, pow_succ, mul_neg,
      mul_one, neg_smul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  have hH0 : homotopyHom H (m + 1) ≫ AlternatingFaceMapComplex.objD Y (m + 1) =
      f.app (op ⦋m + 1⦌) - AlternatingFaceMapComplex.objD X m ≫ homotopyHom H m -
        g.app (op ⦋m + 1⦌) := by
    rw [hH]
    abel
  have hH' : X.δ 0 ≫ homotopyHom H (m + 1) ≫ AlternatingFaceMapComplex.objD Y (m + 1) =
      X.δ 0 ≫ f.app (op ⦋m + 1⦌) -
        X.δ 0 ≫ AlternatingFaceMapComplex.objD X m ≫ homotopyHom H m -
        X.δ 0 ≫ g.app (op ⦋m + 1⦌) := by
    rw [hH0, Preadditive.comp_sub, Preadditive.comp_sub]
  rw [hf_sum, hδ_sum, hH']
  abel

private lemma cylinderChainMapTerm_comm_succ {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g))
    (m : ℕ) (α : ⦋m + 2⦌ ⟶ ⦋1⦌) :
    cylinderChainMapTerm H (m + 2) α ≫ AlternatingFaceMapComplex.objD Y (m + 1) =
      ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) •
        (X.δ i ≫ cylinderChainMapTerm H (m + 1) (SimplexCategory.δ i ≫ α)) := by
  have hf := ((alternatingFaceMapComplex C).map f).comm (m + 1 + 1) (m + 1)
  have hg := ((alternatingFaceMapComplex C).map g).comm (m + 1 + 1) (m + 1)
  simp only [alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d] at hf hg
  rcases fin2_eq_zero_or_one (α.toOrderHom 0) with h0 | h0
  · rcases fin2_eq_zero_or_one (α.toOrderHom 1) with h1 | h1
    · rcases fin2_eq_zero_or_one (α.toOrderHom ((1 : Fin (m + 2)).succ)) with h2 | h2
      · have h0' : α.toOrderHom 0 ≠ 1 := by rw [h0]; decide
        have h1' : α.toOrderHom 1 ≠ 1 := by rw [h1]; decide
        have ht : ∀ i : Fin (m + 3),
            cylinderChainMapTerm H (m + 1) (SimplexCategory.δ i ≫ α) = f.app (op ⦋m + 1⦌) := by
          refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j)
          · have hd00 : (SimplexCategory.δ (0 : Fin (m + 3)) ≫ α).toOrderHom 0 = α.toOrderHom 1 :=
              rfl
            have hd01 : (SimplexCategory.δ (0 : Fin (m + 3)) ≫ α).toOrderHom 1 =
                α.toOrderHom ((1 : Fin (m + 2)).succ) := rfl
            rw [cylinderChainMapTerm, hd00, hd01, ite_eq_right h1', ite_eq_left h2]
          · have hd10 : (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α).toOrderHom 0 =
                α.toOrderHom 0 := rfl
            have hd11 : (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α).toOrderHom 1 =
                α.toOrderHom ((1 : Fin (m + 2)).succ) := rfl
            rw [cylinderChainMapTerm, hd10, hd11, ite_eq_right h0', ite_eq_left h2]
          · rw [cylinderChainMapTerm_δ_succ_succ, ite_eq_right h0', ite_eq_left h1]
        have hLHS : cylinderChainMapTerm H (m + 2) α = f.app (op ⦋m + 1 + 1⦌) := by
          rw [cylinderChainMapTerm, ite_eq_right h0', ite_eq_left h1]
        rw [hLHS, hf, AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ht i, Preadditive.zsmul_comp]
      · -- Case `(α 0, α 1, α 2) = (0, 0, 1)`: the extra `H.hom` terms in `i = 0` and `i = 1`
        -- cancel via `X.δ (0 : Fin (m + 2)).succ ≫ X.δ 0 = X.δ 0 ≫ X.δ 0`.
        have h0' : α.toOrderHom 0 ≠ 1 := by rw [h0]; decide
        have h1' : α.toOrderHom 1 ≠ 1 := by rw [h1]; decide
        have h2' : α.toOrderHom ((1 : Fin (m + 2)).succ) ≠ 0 := by rw [h2]; decide
        have ht0 : cylinderChainMapTerm H (m + 1) (SimplexCategory.δ 0 ≫ α) =
            f.app (op ⦋m + 1⦌) - X.δ 0 ≫ homotopyHom H m := by
          have hd00 : (SimplexCategory.δ (0 : Fin (m + 3)) ≫ α).toOrderHom 0 = α.toOrderHom 1 := rfl
          have hd01 : (SimplexCategory.δ (0 : Fin (m + 3)) ≫ α).toOrderHom 1 =
              α.toOrderHom ((1 : Fin (m + 2)).succ) := rfl
          rw [cylinderChainMapTerm, hd00, hd01, ite_eq_right h1', ite_eq_right h2']
        have ht1 : cylinderChainMapTerm H (m + 1) (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α) =
            f.app (op ⦋m + 1⦌) - X.δ 0 ≫ homotopyHom H m := by
          have hd10 : (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α).toOrderHom 0 =
              α.toOrderHom 0 := rfl
          have hd11 : (SimplexCategory.δ (0 : Fin (m + 2)).succ ≫ α).toOrderHom 1 =
              α.toOrderHom ((1 : Fin (m + 2)).succ) := rfl
          rw [cylinderChainMapTerm, hd10, hd11, ite_eq_right h0', ite_eq_right h2']
        have ht2 : ∀ k : Fin (m + 1),
            cylinderChainMapTerm H (m + 1) (SimplexCategory.δ k.succ.succ ≫ α) =
              f.app (op ⦋m + 1⦌) := by
          intro k
          rw [cylinderChainMapTerm_δ_succ_succ, ite_eq_right h0', ite_eq_left h1]
        have hLHS : cylinderChainMapTerm H (m + 2) α = f.app (op ⦋m + 1 + 1⦌) := by
          rw [cylinderChainMapTerm, ite_eq_right h0', ite_eq_left h1]
        have hLHS_sum :
            cylinderChainMapTerm H (m + 2) α ≫ AlternatingFaceMapComplex.objD Y (m + 1) =
              X.δ 0 ≫ f.app (op ⦋m + 1⦌) - X.δ (0 : Fin (m + 2)).succ ≫ f.app (op ⦋m + 1⦌) +
                ∑ k : Fin (m + 1),
                  (-1 : ℤ) ^ (k.succ.succ : ℕ) • (X.δ k.succ.succ ≫ f.app (op ⦋m + 1⦌)) := by
          rw [hLHS, hf, AlternatingFaceMapComplex.objD, Preadditive.sum_comp,
            Fin.sum_univ_succ, Fin.sum_univ_succ]
          simp only [Fin.val_zero, pow_zero, Fin.val_succ, zero_add, pow_one,
            neg_smul, one_smul, Preadditive.zsmul_comp, Preadditive.neg_comp]
          abel
        have hRHS_sum : ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) •
              (X.δ i ≫ cylinderChainMapTerm H (m + 1) (SimplexCategory.δ i ≫ α)) =
            (X.δ 0 ≫ f.app (op ⦋m + 1⦌) - X.δ 0 ≫ X.δ 0 ≫ homotopyHom H m) -
              (X.δ (0 : Fin (m + 2)).succ ≫ f.app (op ⦋m + 1⦌) -
                X.δ (0 : Fin (m + 2)).succ ≫ X.δ 0 ≫ homotopyHom H m) +
              ∑ k : Fin (m + 1),
                (-1 : ℤ) ^ (k.succ.succ : ℕ) • (X.δ k.succ.succ ≫ f.app (op ⦋m + 1⦌)) := by
          rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
          simp only [ht0, ht1, ht2, Fin.val_zero, pow_zero, one_smul, Preadditive.comp_sub]
          have h1_neg : (-1 : ℤ) ^ ((0 : Fin (m + 2)).succ : ℕ) = -1 := by simp
          rw [h1_neg, neg_smul, one_smul]
          abel
        have hδ01 : X.δ (0 : Fin (m + 2)).succ ≫ X.δ 0 ≫ homotopyHom H m =
            X.δ 0 ≫ X.δ 0 ≫ homotopyHom H m := by
          have h := (X.δ_comp_δ_self_assoc (i := 0) (homotopyHom H m)).symm
          rwa [Fin.castSucc_zero] at h
        rw [hLHS_sum, hRHS_sum, hδ01]
        abel
    · exact cylinderChainMapTerm_comm_succ_jump H m α h0 h1
  · have ht : ∀ i : Fin (m + 3),
        cylinderChainMapTerm H (m + 1) (SimplexCategory.δ i ≫ α) = g.app (op ⦋m + 1⦌) := by
      intro i
      have hi : (SimplexCategory.δ i ≫ α).toOrderHom 0 = 1 :=
        orderHom_one_of_zero_eq_one α h0 (i.succAbove 0)
      rw [cylinderChainMapTerm, ite_eq_left hi]
    have hLHS : cylinderChainMapTerm H (m + 2) α = g.app (op ⦋m + 1 + 1⦌) := by
      rw [cylinderChainMapTerm, ite_eq_left h0]
    rw [hLHS, hg, AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ht i, Preadditive.zsmul_comp]

variable [HasFiniteCoproducts C]

/-- Explicit chain map `K[(cylinder C).obj X] ⟶ K[Y]` associated to a chain homotopy
`H : Homotopy ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map g)`. Its
restrictions along `cylinderι₀` and `cylinderι₁` recover `K.map f` and `K.map g`. -/
def cylinderChainMap {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    (alternatingFaceMapComplex C).obj ((cylinder C).obj X) ⟶
      (alternatingFaceMapComplex C).obj Y :=
  ChainComplex.ofHom
    (fun n ↦ cylinderDesc (cylinderChainMapTerm H n))
    (fun n ↦ cylinder_hom_ext fun α ↦ by
      simp only [alternatingFaceMapComplex_obj_d]
      rw [cylinderι_desc_assoc]
      conv_rhs => rw [AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Preadditive.comp_sum]
      have hRHS : ∑ i : Fin (n + 2),
            cylinderι X α ≫ ((-1 : ℤ) ^ (i : ℕ) • ((cylinder C).obj X).δ i) ≫
              cylinderDesc (cylinderChainMapTerm H n) =
          ∑ i : Fin (n + 2),
            (-1 : ℤ) ^ (i : ℕ) •
              (X.δ i ≫ cylinderChainMapTerm H n (SimplexCategory.δ i ≫ α)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, cylinderι_δ_assoc, cylinderι_desc]
      rw [hRHS]
      cases n with
      | zero => exact cylinderChainMapTerm_comm_zero H α
      | succ m => exact cylinderChainMapTerm_comm_succ H m α)

private lemma cylinderChainMap_f {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) (n : ℕ) :
    (cylinderChainMap H).f n = cylinderDesc (cylinderChainMapTerm H n) :=
  rfl

@[reassoc (attr := simp)]
lemma alternatingFaceMapComplex_map_cylinderι₀_comp_cylinderChainMap
    {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    (alternatingFaceMapComplex C).map ((cylinderι₀ C).app X) ≫ cylinderChainMap H =
      (alternatingFaceMapComplex C).map f := by
  ext (_ | m)
  · simp [cylinderChainMap_f, cylinderChainMapTerm]
  · simp only [HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f, cylinderι₀_app_app,
      cylinderChainMap_f, cylinderι_desc]
    have h0 : (SimplexCategory.const ⦋m + 1⦌ ⦋1⦌ 0).toOrderHom 0 ≠ 1 := by
      rw [SimplexCategory.const_apply]; decide
    have h1 : (SimplexCategory.const ⦋m + 1⦌ ⦋1⦌ 0).toOrderHom 1 = 0 :=
      SimplexCategory.const_apply _ _ _ _
    rw [cylinderChainMapTerm, ite_eq_right h0, ite_eq_left h1]

@[reassoc (attr := simp)]
lemma alternatingFaceMapComplex_map_cylinderι₁_comp_cylinderChainMap
    {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    (alternatingFaceMapComplex C).map ((cylinderι₁ C).app X) ≫ cylinderChainMap H =
      (alternatingFaceMapComplex C).map g := by
  ext (_ | m)
  · simp only [HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f, cylinderι₁_app_app,
      cylinderChainMap_f, cylinderι_desc]
    have h0 : (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).toOrderHom 0 ≠ 0 := by
      rw [SimplexCategory.const_apply]; decide
    rw [cylinderChainMapTerm, ite_eq_right h0]
  · simp only [HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f, cylinderι₁_app_app,
      cylinderChainMap_f, cylinderι_desc]
    have h0 : (SimplexCategory.const ⦋m + 1⦌ ⦋1⦌ 1).toOrderHom 0 = 1 :=
      SimplexCategory.const_apply _ _ _ _
    rw [cylinderChainMapTerm, ite_eq_left h0]

end CylinderChainMap

section Pseudoabelian

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

namespace Homotopy

/-- In an idempotent-complete preadditive category with finite coproducts, any chain homotopy
between `(alternatingFaceMapComplex C).map f` and `(alternatingFaceMapComplex C).map g` lifts to a
combinatorial simplicial homotopy `Homotopy f g` (Dold–Puppe, Satz 3.31). -/
def ofAlternatingFaceMapComplexHomotopy {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      ((alternatingFaceMapComplex C).map g)) :
    Homotopy f g := by
  let Ψ : Idempotents.DoldKan.N.obj ((cylinder C).obj X) ⟶ Idempotents.DoldKan.N.obj Y :=
    Idempotents.DoldKan.inclusionN.app ((cylinder C).obj X) ≫
      cylinderChainMap H ≫ Idempotents.DoldKan.PInftyToN.app Y
  let Φ : (cylinder C).obj X ⟶ Y :=
    (Idempotents.DoldKan.equivalence (C := C)).fullyFaithfulFunctor.preimage Ψ
  have hΦ : Idempotents.DoldKan.N.map Φ = Ψ :=
    (Idempotents.DoldKan.equivalence (C := C)).fullyFaithfulFunctor.map_preimage Ψ
  refine ofCylinderHom Φ ?_ ?_
  · apply (Idempotents.DoldKan.equivalence (C := C)).fullyFaithfulFunctor.map_injective
    -- `(Idempotents.DoldKan.equivalence).functor` is definitionally `Idempotents.DoldKan.N`.
    change Idempotents.DoldKan.N.map ((cylinderι₀ C).app X ≫ Φ) = Idempotents.DoldKan.N.map f
    rw [Functor.map_comp, hΦ]
    dsimp [Ψ]
    rw [Idempotents.DoldKan.inclusionN.naturality_assoc,
      alternatingFaceMapComplex_map_cylinderι₀_comp_cylinderChainMap_assoc,
      Idempotents.DoldKan.PInftyToN.naturality,
      Idempotents.DoldKan.inclusionN_app_comp_PInftyToN_app_assoc]
  · apply (Idempotents.DoldKan.equivalence (C := C)).fullyFaithfulFunctor.map_injective
    -- `(Idempotents.DoldKan.equivalence).functor` is definitionally `Idempotents.DoldKan.N`.
    change Idempotents.DoldKan.N.map ((cylinderι₁ C).app X ≫ Φ) = Idempotents.DoldKan.N.map g
    rw [Functor.map_comp, hΦ]
    dsimp [Ψ]
    rw [Idempotents.DoldKan.inclusionN.naturality_assoc,
      alternatingFaceMapComplex_map_cylinderι₁_comp_cylinderChainMap_assoc,
      Idempotents.DoldKan.PInftyToN.naturality,
      Idempotents.DoldKan.inclusionN_app_comp_PInftyToN_app_assoc]

/-- Symmetry of combinatorial simplicial homotopies in an idempotent-complete preadditive category
with finite coproducts. -/
@[symm]
def symm {X Y : SimplicialObject C} {f g : X ⟶ Y} (h : Homotopy f g) : Homotopy g f :=
  ofAlternatingFaceMapComplexHomotopy h.toChainHomotopy.symm

/-- Transitivity of combinatorial simplicial homotopies in an idempotent-complete preadditive
category with finite coproducts. -/
@[trans]
def trans {X Y : SimplicialObject C} {e f g : X ⟶ Y}
    (h₁ : Homotopy e f) (h₂ : Homotopy f g) : Homotopy e g :=
  ofAlternatingFaceMapComplexHomotopy (h₁.toChainHomotopy.trans h₂.toChainHomotopy)

/-- A simplicial homotopy `Homotopy f g` induces a chain homotopy between `N.map f` and `N.map g`
for the pseudoabelian normalized chain functor `Idempotents.DoldKan.N`. -/
def toNHomotopy {X Y : SimplicialObject C} {f g : X ⟶ Y} (h : Homotopy f g) :
    _root_.Homotopy (Idempotents.DoldKan.N.map f) (Idempotents.DoldKan.N.map g) := by
  have hf : Idempotents.DoldKan.N.map f =
      (Idempotents.DoldKan.inclusionN.app X ≫ (alternatingFaceMapComplex C).map f) ≫
        Idempotents.DoldKan.PInftyToN.app Y := by
    rw [Category.assoc, Idempotents.DoldKan.PInftyToN.naturality,
      Idempotents.DoldKan.inclusionN_app_comp_PInftyToN_app_assoc]
  have hg : Idempotents.DoldKan.N.map g =
      (Idempotents.DoldKan.inclusionN.app X ≫ (alternatingFaceMapComplex C).map g) ≫
        Idempotents.DoldKan.PInftyToN.app Y := by
    rw [Category.assoc, Idempotents.DoldKan.PInftyToN.naturality,
      Idempotents.DoldKan.inclusionN_app_comp_PInftyToN_app_assoc]
  exact (_root_.Homotopy.ofEq hf).trans
    (((h.toChainHomotopy.compLeft (Idempotents.DoldKan.inclusionN.app X)).compRight
      (Idempotents.DoldKan.PInftyToN.app Y)).trans (_root_.Homotopy.ofEq hg.symm))

/-- Any chain homotopy between `N.map f` and `N.map g` lifts to a simplicial homotopy
`Homotopy f g`. -/
def ofNHomotopy {X Y : SimplicialObject C} {f g : X ⟶ Y}
    (H : _root_.Homotopy (Idempotents.DoldKan.N.map f) (Idempotents.DoldKan.N.map g)) :
    Homotopy f g := by
  have hf : (Idempotents.DoldKan.PInftyToN.app X ≫ Idempotents.DoldKan.N.map f) ≫
        Idempotents.DoldKan.inclusionN.app Y =
      PInfty ≫ (alternatingFaceMapComplex C).map f := by
    rw [Category.assoc, Idempotents.DoldKan.inclusionN.naturality,
      Idempotents.DoldKan.PInftyToN_app_comp_inclusionN_app_assoc]
  have hg : (Idempotents.DoldKan.PInftyToN.app X ≫ Idempotents.DoldKan.N.map g) ≫
        Idempotents.DoldKan.inclusionN.app Y =
      PInfty ≫ (alternatingFaceMapComplex C).map g := by
    rw [Category.assoc, Idempotents.DoldKan.inclusionN.naturality,
      Idempotents.DoldKan.PInftyToN_app_comp_inclusionN_app_assoc]
  have hKf : _root_.Homotopy ((alternatingFaceMapComplex C).map f)
      (PInfty ≫ (alternatingFaceMapComplex C).map f) :=
    (_root_.Homotopy.ofEq (Category.id_comp _).symm).trans
      ((homotopyPInftyToId X).symm.compRight ((alternatingFaceMapComplex C).map f))
  have hKg : _root_.Homotopy (PInfty ≫ (alternatingFaceMapComplex C).map g)
      ((alternatingFaceMapComplex C).map g) :=
    ((homotopyPInftyToId X).compRight ((alternatingFaceMapComplex C).map g)).trans
      (_root_.Homotopy.ofEq (Category.id_comp _))
  exact ofAlternatingFaceMapComplexHomotopy
    (hKf.trans ((_root_.Homotopy.ofEq hf.symm).trans
      (((H.compLeft (Idempotents.DoldKan.PInftyToN.app X)).compRight
        (Idempotents.DoldKan.inclusionN.app Y)).trans
          ((_root_.Homotopy.ofEq hg).trans hKg))))

end Homotopy

/-- **Dold–Puppe, Satz 3.31** (alternating face map complex form): two morphisms `f, g : X ⟶ Y` of
simplicial objects in an idempotent-complete preadditive category with finite coproducts are
simplicially homotopic if and only if their alternating face map complex morphisms are chain
homotopic. -/
theorem nonempty_homotopy_iff_alternatingFaceMapComplex {X Y : SimplicialObject C}
    (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      Nonempty (_root_.Homotopy ((alternatingFaceMapComplex C).map f)
        ((alternatingFaceMapComplex C).map g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toChainHomotopy⟩, fun ⟨H⟩ ↦ ⟨Homotopy.ofAlternatingFaceMapComplexHomotopy H⟩⟩

/-- **Dold–Puppe, Satz 3.31** (normalized chain complex form): two morphisms `f, g : X ⟶ Y` of
simplicial objects in an idempotent-complete preadditive category with finite coproducts are
simplicially homotopic if and only if their normalized chain morphisms `N.map f` and `N.map g` are
chain homotopic. -/
theorem nonempty_homotopy_iff_N {X Y : SimplicialObject C} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      Nonempty (_root_.Homotopy (Idempotents.DoldKan.N.map f) (Idempotents.DoldKan.N.map g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toNHomotopy⟩, fun ⟨H⟩ ↦ ⟨Homotopy.ofNHomotopy H⟩⟩

namespace HomotopyEquiv

/-- A chain homotopy equivalence `e` between `K[X]` and `K[Y]` whose forward morphism is `K.map f`
lifts to a simplicial homotopy equivalence `HomotopyEquiv X Y` with forward morphism `f`. -/
def ofAlternatingFaceMapComplexHomotopyEquiv {X Y : SimplicialObject C} (f : X ⟶ Y)
    (e : _root_.HomotopyEquiv ((alternatingFaceMapComplex C).obj X)
      ((alternatingFaceMapComplex C).obj Y))
    (he : e.hom = (alternatingFaceMapComplex C).map f) :
    HomotopyEquiv X Y := by
  let gN : Idempotents.DoldKan.N.obj Y ⟶ Idempotents.DoldKan.N.obj X :=
    Idempotents.DoldKan.inclusionN.app Y ≫ e.inv ≫ Idempotents.DoldKan.PInftyToN.app X
  let g : Y ⟶ X :=
    (Idempotents.DoldKan.equivalence (C := C)).fullyFaithfulFunctor.preimage gN
  have hg : Idempotents.DoldKan.N.map g = gN :=
    (Idempotents.DoldKan.equivalence (C := C)).fullyFaithfulFunctor.map_preimage gN
  refine
    { hom := f
      inv := g
      homotopyHomInvId := Homotopy.ofNHomotopy ?_
      homotopyInvHomId := Homotopy.ofNHomotopy ?_ }
  · have hfg : Idempotents.DoldKan.N.map (f ≫ g) =
        (Idempotents.DoldKan.inclusionN.app X ≫ (e.hom ≫ e.inv)) ≫
          Idempotents.DoldKan.PInftyToN.app X := by
      rw [Functor.map_comp, hg]
      dsimp [gN]
      rw [Idempotents.DoldKan.inclusionN.naturality_assoc, ← he, Category.assoc, Category.assoc]
    have hid : (Idempotents.DoldKan.inclusionN.app X ≫ 𝟙 _) ≫
          Idempotents.DoldKan.PInftyToN.app X =
        Idempotents.DoldKan.N.map (𝟙 X) := by
      rw [Category.comp_id, Idempotents.DoldKan.inclusionN_app_comp_PInftyToN_app, Functor.map_id]
    exact (_root_.Homotopy.ofEq hfg).trans
      (((e.homotopyHomInvId.compLeft (Idempotents.DoldKan.inclusionN.app X)).compRight
        (Idempotents.DoldKan.PInftyToN.app X)).trans (_root_.Homotopy.ofEq hid))
  · have hgf : Idempotents.DoldKan.N.map (g ≫ f) =
        (Idempotents.DoldKan.inclusionN.app Y ≫ (e.inv ≫ e.hom)) ≫
          Idempotents.DoldKan.PInftyToN.app Y := by
      rw [Functor.map_comp, hg]
      dsimp [gN]
      rw [Category.assoc, Category.assoc, ← Idempotents.DoldKan.PInftyToN.naturality, ← he,
        Category.assoc, Category.assoc]
    have hid : (Idempotents.DoldKan.inclusionN.app Y ≫ 𝟙 _) ≫
          Idempotents.DoldKan.PInftyToN.app Y =
        Idempotents.DoldKan.N.map (𝟙 Y) := by
      rw [Category.comp_id, Idempotents.DoldKan.inclusionN_app_comp_PInftyToN_app, Functor.map_id]
    exact (_root_.Homotopy.ofEq hgf).trans
      (((e.homotopyInvHomId.compLeft (Idempotents.DoldKan.inclusionN.app Y)).compRight
        (Idempotents.DoldKan.PInftyToN.app Y)).trans (_root_.Homotopy.ofEq hid))

@[simp]
lemma ofAlternatingFaceMapComplexHomotopyEquiv_hom {X Y : SimplicialObject C} (f : X ⟶ Y)
    (e : _root_.HomotopyEquiv ((alternatingFaceMapComplex C).obj X)
      ((alternatingFaceMapComplex C).obj Y))
    (he : e.hom = (alternatingFaceMapComplex C).map f) :
    (ofAlternatingFaceMapComplexHomotopyEquiv f e he).hom = f :=
  (rfl)

/-- Transitivity of combinatorial simplicial homotopy equivalences in an idempotent-complete
preadditive category with finite coproducts. -/
@[trans]
def trans {X Y Z : SimplicialObject C} (e₁ : HomotopyEquiv X Y) (e₂ : HomotopyEquiv Y Z) :
    HomotopyEquiv X Z :=
  ofAlternatingFaceMapComplexHomotopyEquiv (e₁.hom ≫ e₂.hom)
    (e₁.toChainHomotopyEquiv.trans e₂.toChainHomotopyEquiv) (by simp)

@[simp]
lemma trans_hom {X Y Z : SimplicialObject C} (e₁ : HomotopyEquiv X Y) (e₂ : HomotopyEquiv Y Z) :
    (e₁.trans e₂).hom = e₁.hom ≫ e₂.hom :=
  (rfl)

end HomotopyEquiv

/-- A morphism `f : X ⟶ Y` of simplicial objects in an idempotent-complete preadditive category
with finite coproducts induces a chain homotopy equivalence on alternating face map complexes if
and only if `f` is the forward morphism of a simplicial homotopy equivalence. -/
theorem homotopyEquivalences_alternatingFaceMapComplex_map_iff
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    HomologicalComplex.homotopyEquivalences C (.down ℕ) ((alternatingFaceMapComplex C).map f) ↔
      ∃ e : HomotopyEquiv X Y, e.hom = f := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨HomotopyEquiv.ofAlternatingFaceMapComplexHomotopyEquiv f e he, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.homotopyEquivalences_alternatingFaceMapComplex_map

end Pseudoabelian

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Homotopy

/-- A simplicial homotopy `Homotopy f g` in an abelian category induces a chain homotopy on
normalized Moore complexes. -/
def toNormalizedMooreComplexHomotopy {X Y : SimplicialObject A} {f g : X ⟶ Y} (h : Homotopy f g) :
    _root_.Homotopy ((normalizedMooreComplex A).map f) ((normalizedMooreComplex A).map g) := by
  let cIso : normalizedMooreComplex A ≅ Idempotents.DoldKan.N := Abelian.DoldKan.comparisonN
  have hf : (normalizedMooreComplex A).map f =
      (cIso.hom.app X ≫ Idempotents.DoldKan.N.map f) ≫ cIso.inv.app Y := by
    rw [← cancel_mono (cIso.hom.app Y), Category.assoc, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, cIso.hom.naturality]
  have hg : (normalizedMooreComplex A).map g =
      (cIso.hom.app X ≫ Idempotents.DoldKan.N.map g) ≫ cIso.inv.app Y := by
    rw [← cancel_mono (cIso.hom.app Y), Category.assoc, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, cIso.hom.naturality]
  exact (_root_.Homotopy.ofEq hf).trans
    (((h.toNHomotopy.compLeft (cIso.hom.app X)).compRight
      (cIso.inv.app Y)).trans (_root_.Homotopy.ofEq hg.symm))

/-- A chain homotopy on normalized Moore complexes lifts to a simplicial homotopy `Homotopy f g`. -/
def ofNormalizedMooreComplexHomotopy {X Y : SimplicialObject A} {f g : X ⟶ Y}
    (H : _root_.Homotopy ((normalizedMooreComplex A).map f) ((normalizedMooreComplex A).map g)) :
    Homotopy f g := by
  let cIso : normalizedMooreComplex A ≅ Idempotents.DoldKan.N := Abelian.DoldKan.comparisonN
  have hf : Idempotents.DoldKan.N.map f =
      (cIso.inv.app X ≫ (normalizedMooreComplex A).map f) ≫ cIso.hom.app Y := by
    rw [← cancel_epi (cIso.hom.app X), ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, ← cIso.hom.naturality]
  have hg : Idempotents.DoldKan.N.map g =
      (cIso.inv.app X ≫ (normalizedMooreComplex A).map g) ≫ cIso.hom.app Y := by
    rw [← cancel_epi (cIso.hom.app X), ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp, ← cIso.hom.naturality]
  exact ofNHomotopy ((_root_.Homotopy.ofEq hf).trans
    (((H.compLeft (cIso.inv.app X)).compRight
      (cIso.hom.app Y)).trans (_root_.Homotopy.ofEq hg.symm)))

end Homotopy

/-- **Dold–Puppe, Satz 3.31** (abelian normalized Moore complex form): two morphisms of simplicial
objects in an abelian category are simplicially homotopic if and only if their normalized Moore
complex morphisms are chain homotopic. -/
theorem nonempty_homotopy_iff_normalizedMooreComplex {X Y : SimplicialObject A} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      Nonempty (_root_.Homotopy ((normalizedMooreComplex A).map f)
        ((normalizedMooreComplex A).map g)) :=
  ⟨fun ⟨h⟩ ↦ ⟨h.toNormalizedMooreComplexHomotopy⟩,
    fun ⟨H⟩ ↦ ⟨Homotopy.ofNormalizedMooreComplexHomotopy H⟩⟩

end Abelian

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Idempotents.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

/-- The inverse Dold–Kan functor `Γ : ChainComplex C ℕ ⥤ SimplicialObject C` carries chain
homotopies to combinatorial simplicial homotopies. -/
def Γ.mapHomotopy {K L : ChainComplex C ℕ} {φ ψ : K ⟶ L} (H : Homotopy φ ψ) :
    SimplicialObject.Homotopy (Γ.map φ) (Γ.map ψ) := by
  have hφ : N.map (Γ.map φ) =
      ((η (C := C)).hom.app K ≫ φ) ≫ (η (C := C)).inv.app L := by
    have hn := (η (C := C)).hom.naturality φ
    dsimp at hn
    rw [← cancel_mono ((η (C := C)).hom.app L), hn, Category.assoc, Category.assoc]
    simp
  have hψ : N.map (Γ.map ψ) =
      ((η (C := C)).hom.app K ≫ ψ) ≫ (η (C := C)).inv.app L := by
    have hn := (η (C := C)).hom.naturality ψ
    dsimp at hn
    rw [← cancel_mono ((η (C := C)).hom.app L), hn, Category.assoc, Category.assoc]
    simp
  exact SimplicialObject.Homotopy.ofNHomotopy ((Homotopy.ofEq hφ).trans
    (((H.compLeft ((η (C := C)).hom.app K)).compRight
      ((η (C := C)).inv.app L)).trans (Homotopy.ofEq hψ.symm)))

/-- Two chain maps `φ, ψ : K ⟶ L` are chain homotopic if and only if `Γ.map φ` and `Γ.map ψ` are
simplicially homotopic. -/
theorem nonempty_homotopy_Γ_map_iff {K L : ChainComplex C ℕ} (φ ψ : K ⟶ L) :
    Nonempty (SimplicialObject.Homotopy (Γ.map φ) (Γ.map ψ)) ↔ Nonempty (Homotopy φ ψ) := by
  constructor
  · rintro ⟨h⟩
    have hφ : φ = ((η (C := C)).inv.app K ≫ N.map (Γ.map φ)) ≫ (η (C := C)).hom.app L := by
      have hn := (η (C := C)).hom.naturality φ
      dsimp at hn
      rw [Category.assoc, hn, Iso.inv_hom_id_app_assoc]
    have hψ : ψ = ((η (C := C)).inv.app K ≫ N.map (Γ.map ψ)) ≫ (η (C := C)).hom.app L := by
      have hn := (η (C := C)).hom.naturality ψ
      dsimp at hn
      rw [Category.assoc, hn, Iso.inv_hom_id_app_assoc]
    exact ⟨(Homotopy.ofEq hφ).trans
      (((h.toNHomotopy.compLeft ((η (C := C)).inv.app K)).compRight
        ((η (C := C)).hom.app L)).trans (Homotopy.ofEq hψ.symm))⟩
  · rintro ⟨H⟩
    exact ⟨Γ.mapHomotopy H⟩

/-- The inverse Dold–Kan functor `Γ` carries chain homotopy equivalences to simplicial homotopy
equivalences. -/
def Γ.mapHomotopyEquiv {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    SimplicialObject.HomotopyEquiv (Γ.obj K) (Γ.obj L) where
  hom := Γ.map e.hom
  inv := Γ.map e.inv
  homotopyHomInvId :=
    (SimplicialObject.Homotopy.ofEq (Γ.map_comp e.hom e.inv).symm).trans
      ((Γ.mapHomotopy e.homotopyHomInvId).trans (SimplicialObject.Homotopy.ofEq (Γ.map_id K)))
  homotopyInvHomId :=
    (SimplicialObject.Homotopy.ofEq (Γ.map_comp e.inv e.hom).symm).trans
      ((Γ.mapHomotopy e.homotopyInvHomId).trans (SimplicialObject.Homotopy.ofEq (Γ.map_id L)))

@[simp]
lemma Γ.mapHomotopyEquiv_hom {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    (Γ.mapHomotopyEquiv e).hom = Γ.map e.hom :=
  (rfl)

@[simp]
lemma Γ.mapHomotopyEquiv_inv {K L : ChainComplex C ℕ} (e : HomotopyEquiv K L) :
    (Γ.mapHomotopyEquiv e).inv = Γ.map e.inv :=
  (rfl)

end CategoryTheory.Idempotents.DoldKan
