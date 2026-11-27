/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DoldKan.SimplexChainMap.Functor
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import TauCeti.Data.Finset.Basic

/-!
# Reversal of simplex chain maps

Reversing the vertices of a simplex reverses the orientation of each of its faces.
For a face with vertex set `J`, the orientation sign is `(-1)^(#J * (#J - 1) / 2)`.
With this sign, reversal preserves the chain-map equation and commutes with all
simplicial operators, including those that collapse vertices.

The resulting isomorphism `CochainComplex.simplexChainMapsOpIso` identifies the
simplicial opposite of the normalized-chain model of Dold–Kan with the same model.
This is the chain-level reversal used when comparing left and right mapping spaces
of differential graded nerves.

We use the normalized-chain description `CochainComplex.SimplexChainMap` and
Mathlib's simplex reversal `SimplexCategory.rev` (Joël Riou).

## References

* J. Lurie, *Higher Algebra*, Remark 1.3.1.12.
* P. Goerss and J. Jardine, *Simplicial Homotopy Theory*, Chapter III, §2.
-/

public noncomputable section

open CategoryTheory Finset Simplicial

universe v u

namespace CochainComplex

variable {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}

namespace SimplexChainMap

variable {n m : ℕ}

private lemma reverse_d_val (g : K.SimplexChainMap n)
    (J : Finset (Fin (n + 1))) (d : ℤ) :
    (K.d d (d + 1)).hom (((#J).choose 2 : ℤ).negOnePow • g.val (J.image Fin.rev) d) =
      ∑ j ∈ J, (#{s ∈ J | s < j} : ℤ).negOnePow •
        (((#(J.erase j)).choose 2 : ℤ).negOnePow •
          g.val ((J.erase j).image Fin.rev) (d + 1)) := by
  simp only [Units.smul_def, map_zsmul, g.d_val, smul_sum]
  rw [sum_image (fun _ _ _ _ h ↦ Fin.rev_injective h)]
  refine sum_congr rfl fun j hj ↦ ?_
  have hcount : #{s ∈ J.image Fin.rev | s < j.rev} = #{s ∈ J | j < s} := by
    rw [filter_image, card_image_of_injective _ Fin.rev_injective]
    simp only [Fin.rev_lt_rev]
  rw [hcount, ← image_erase Fin.rev_injective]
  have hc := card_filter_lt_add_card_filter_gt_add_one hj
  have he := card_erase_add_one hj
  have hchoose : (#J).choose 2 = #(J.erase j) + (#(J.erase j)).choose 2 := by
    rw [← he, Nat.choose_succ_succ, Nat.choose_one_right]
  have hs : ((#J).choose 2 : ℤ).negOnePow * (#{s ∈ J | j < s} : ℤ).negOnePow =
      (#{s ∈ J | s < j} : ℤ).negOnePow * ((#(J.erase j)).choose 2 : ℤ).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    refine ⟨(#{s ∈ J | j < s} : ℤ), ?_⟩
    push_cast [hchoose]
    omega
  simpa only [Units.smul_def, smul_smul, ← Units.val_mul] using
    congrArg (fun a : ℤˣ ↦ a • g.val ((J.erase j).image Fin.rev) (d + 1)) hs

/-- Reverse the vertices of a normalized simplex chain map, with the orientation
sign of the reversal on each face. -/
def reverse (g : K.SimplexChainMap n) : K.SimplexChainMap n where
  val J d := ((#J).choose 2 : ℤ).negOnePow • g.val (J.image Fin.rev) d
  val_eq_zero_of_ne J d h := by
    rw [g.val_eq_zero_of_ne _ _ (by
      simpa only [card_image_of_injective _ Fin.rev_injective] using h), smul_zero]
  val_empty := by simp
  d_val := reverse_d_val g

/-- Reversal acts on a face by reversing its vertex set and its orientation. -/
@[simp]
lemma reverse_val (g : K.SimplexChainMap n) (J : Finset (Fin (n + 1))) (d : ℤ) :
    g.reverse.val J d = ((#J).choose 2 : ℤ).negOnePow • g.val (J.image Fin.rev) d :=
  (rfl)

/-- Reversing twice restores the original simplex chain map. -/
@[simp]
lemma reverse_reverse (g : K.SimplexChainMap n) : g.reverse.reverse = g := by
  ext J d
  simp [image_image, smul_smul, card_image_of_injective _ Fin.rev_injective,
    Function.comp_def]

/-- Reversal intertwines pullback along a simplex map with pullback along its
reversal. This includes simplex maps that collapse vertices. -/
lemma reverse_map (g : K.SimplexChainMap n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (g.map (SimplexCategory.rev.map θ).toOrderHom).reverse =
      g.reverse.map θ.toOrderHom := by
  ext J d
  have himage : (J.image Fin.rev).image (SimplexCategory.rev.map θ).toOrderHom =
      (J.image θ.toOrderHom).image Fin.rev := by
    simp only [image_image]
    congr 1
    ext j
    simp [SimplexCategory.rev_map_apply]
  simp only [reverse_val, map_val, himage, card_image_of_injective _ Fin.rev_injective]
  split_ifs with h
  · rw [h]
  · exact smul_zero _

/-- Reversal fixes the value on a vertex, apart from reversing its index. -/
lemma reverse_val_singleton (g : K.SimplexChainMap n) (j : Fin (n + 1)) (d : ℤ) :
    g.reverse.val {j} d = g.val {j.rev} d := by
  simp

/-- Reversal negates the value on an edge. -/
lemma reverse_val_pair (g : K.SimplexChainMap n) {i j : Fin (n + 1)} (h : i ≠ j) (d : ℤ) :
    g.reverse.val {i, j} d = -g.val {i.rev, j.rev} d := by
  simp [h, Units.smul_def]

/-- Signed vertex reversal is natural in the coefficient complex. -/
@[simp]
lemma reverse_postcomp {L : CochainComplex (ModuleCat.{v} R) ℤ}
    (g : K.SimplexChainMap n) (f : K ⟶ L) :
    (g.postcomp f).reverse = g.reverse.postcomp f := by
  ext J d
  simp [Units.smul_def]

end SimplexChainMap

variable (K)

/-- The normalized-chain model of Dold–Kan is isomorphic to its simplicial
opposite by signed vertex reversal. -/
def simplexChainMapsOpIso : K.simplexChainMaps.op ≅ K.simplexChainMaps :=
  NatIso.ofComponents (fun Δ ↦
    (Equiv.mk (fun g : K.simplexChainMaps.op.obj Δ ↦
      SimplexChainMap.reverse (SSet.opObjEquiv g))
      (fun g : K.simplexChainMaps.obj Δ ↦ SSet.opObjEquiv.symm g.reverse)
      (fun _ ↦ SimplexChainMap.reverse_reverse _)
      (fun _ ↦ SimplexChainMap.reverse_reverse _)).toIso)
    (fun {Δ Δ'} θ ↦ by
      ext g
      exact SimplexChainMap.reverse_map (SSet.opObjEquiv g) θ.unop)

/-- The opposite comparison sends a simplex to its signed vertex reversal. -/
@[simp]
lemma simplexChainMapsOpIso_hom_app_apply (Δ : SimplexCategoryᵒᵖ)
    (g : K.simplexChainMaps.op.obj Δ) :
    (K.simplexChainMapsOpIso.hom.app Δ) g =
      SimplexChainMap.reverse (SSet.opObjEquiv g) :=
  (rfl)

/-- The inverse opposite comparison is the same signed reversal. -/
@[simp]
lemma simplexChainMapsOpIso_inv_app_apply (Δ : SimplexCategoryᵒᵖ)
    (g : K.simplexChainMaps.obj Δ) :
    (K.simplexChainMapsOpIso.inv.app Δ) g = SSet.opObjEquiv.symm g.reverse :=
  (rfl)

/-- Applying the opposite comparison twice is the canonical double-opposite
identification. -/
@[simp]
lemma simplexChainMapsOpIso_op_trans :
    SSet.opFunctor.mapIso K.simplexChainMapsOpIso ≪≫ K.simplexChainMapsOpIso =
      SSet.opFunctorCompOpFunctorIso.app K.simplexChainMaps := by
  ext Δ g
  exact SimplexChainMap.reverse_reverse (SSet.opObjEquiv (SSet.opObjEquiv g))

variable (R) in
/-- Signed vertex reversal gives a natural isomorphism from the opposite of the
normalized-chain model functor to that functor. -/
def simplexChainMapsOpNatIso :
    simplexChainMapsFunctor R ⋙ SSet.opFunctor ≅ simplexChainMapsFunctor R :=
  NatIso.ofComponents (fun K ↦ K.simplexChainMapsOpIso) fun f ↦ by
    ext Δ g
    exact SimplexChainMap.reverse_postcomp (SSet.opObjEquiv g) f

/-- The component of the natural opposite comparison is signed vertex reversal. -/
@[simp]
lemma simplexChainMapsOpNatIso_app :
    (simplexChainMapsOpNatIso R).app K = K.simplexChainMapsOpIso :=
  (rfl)

end CochainComplex
