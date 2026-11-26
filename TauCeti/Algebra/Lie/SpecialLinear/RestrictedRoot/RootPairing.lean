/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.RootPairing
public import TauCeti.Algebra.Lie.SpecialLinear.RestrictedRoot.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.Algebra.Lie.Sl2.Basic
import TauCeti.LinearAlgebra.RootSystem.ConsecutiveDifferenceBase

/-!
# The restricted root system of `𝔰𝔩_n(ℝ)` has type `A`

On `𝔰𝔩_{r+1}(ℝ)` with the Cartan involution `θ X = -Xᵀ` and the maximal abelian subspace
`𝔞 ⊆ 𝔭` of trace-zero diagonal matrices, the restricted roots are the `e_i - e_j`, `i ≠ j`, with
root spaces the lines `ℝ E_ij` (`TauCeti.mem_restrictedRoots_specialLinearDiagonal_iff`,
`TauCeti.restrictedRootSpace_specialLinearRestrictedRoot`). This file reads off the restricted
root pairing `LieEquiv.IsCartanInvolution.restrictedRootPairing` of this example:

* the restricted coroot of `e_i - e_j` is `E_ii - E_jj`, so the pairing of `e_i - e_j` with the
  coroot of `e_k - e_l` is `δ_ik - δ_il - δ_jk + δ_jl`;
* the simple roots `e_k - e_{k+1}`, `k < r`, form a base, whose Cartan matrix is
  `CartanMatrix.A r`: the restricted root system has Cartan type `A_r`;
* every restricted root has multiplicity `1`.

The base is built in the same way as the standard base `TauCeti.specialLinearPositiveBase` of
`TauCeti.Algebra.Lie.SpecialLinear.Root.Base`, through the consecutive-difference lemmas
`RootPairing.root_mem_or_neg_mem_closure_of_forall_exists_eq_sub` and
`RootPairing.linearIndepOn_root_range_of_root_mem_or_neg_mem_closure`.

## Main definitions

* `TauCeti.specialLinearRestrictedRootPairing`: the restricted root pairing of `𝔰𝔩_{r+1}(ℝ)`.
* `TauCeti.specialLinearRestrictedRootIndex`: the restricted root `e_i - e_j` as an index.
* `TauCeti.specialLinearRestrictedRootBase`: the base of simple roots `e_k - e_{k+1}`.

## Main results

* `TauCeti.specialLinearRestrictedRootPairing_coroot`: the coroot of `e_i - e_j` is `E_ii - E_jj`.
* `TauCeti.hasCartanType_specialLinearRestrictedRootPairing`: the restricted root system of
  `𝔰𝔩_{r+1}(ℝ)` has Cartan type `A_r`.
* `TauCeti.finrank_restrictedRootSpace_specialLinearDiagonal`: every restricted root of
  `𝔰𝔩_{r+1}(ℝ)` has multiplicity `1`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra LieAlgebra.SpecialLinear Module Submodule Set

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {r : ℕ}

variable (r) in
/-- **The restricted root pairing of `𝔰𝔩_{r+1}(ℝ)`**, for the Cartan involution `X ↦ -Xᵀ` and the
trace-zero diagonal matrices `𝔞`. -/
noncomputable abbrev specialLinearRestrictedRootPairing :
    RootPairing (specialLinearDiagonal r ℝ).restrictedRoots ℝ
      (Dual ℝ (specialLinearDiagonal r ℝ)) (specialLinearDiagonal r ℝ) :=
  (isCartanInvolution_specialLinearNegTranspose r).restrictedRootPairing
    isMaximalAbelianInP_specialLinearDiagonal

variable (r) in
/-- The restricted root `e_i - e_j`, for `i ≠ j`, as an index of the restricted root pairing. -/
def specialLinearRestrictedRootIndex (i j : Fin (r + 1)) (hij : i ≠ j) :
    (specialLinearDiagonal r ℝ).restrictedRoots :=
  ⟨specialLinearRestrictedRoot r ℝ i j,
    mem_restrictedRoots_specialLinearDiagonal_iff.mpr ⟨i, j, hij, rfl⟩⟩

@[simp]
theorem coe_specialLinearRestrictedRootIndex {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearRestrictedRootIndex r i j hij : Dual ℝ (specialLinearDiagonal r ℝ)) =
      specialLinearRestrictedRoot r ℝ i j :=
  (rfl)

/-- Every restricted root of `𝔰𝔩_{r+1}(ℝ)` is some `e_i - e_j`. -/
theorem exists_eq_specialLinearRestrictedRootIndex
    (μ : (specialLinearDiagonal r ℝ).restrictedRoots) :
    ∃ i j, ∃ hij : i ≠ j, μ = specialLinearRestrictedRootIndex r i j hij := by
  obtain ⟨i, j, hij, h⟩ := mem_restrictedRoots_specialLinearDiagonal_iff.mp μ.property
  exact ⟨i, j, hij, Subtype.ext h⟩

/-- **The restricted coroot of `e_i - e_j` is `E_ii - E_jj`.** -/
theorem specialLinearRestrictedRootPairing_coroot {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearRestrictedRootPairing r).coroot (specialLinearRestrictedRootIndex r i j hij) =
      ⟨singleSubSingle i j 1, singleSubSingle_mem_specialLinearDiagonal r ℝ i j 1⟩ := by
  -- `E_ij` spans `𝔤_{e_i - e_j}`, so the `𝔰𝔩₂` triple `(H', E_ij, F)` of the restricted root
  -- has `F = c E_ji`, hence `H' = [E_ij, F] = c (E_ii - E_jj)`, and `(e_i - e_j)(H') = 2`
  -- forces `c = 1`.
  have hθ := isCartanInvolution_specialLinearNegTranspose r
  have h𝔞 := isMaximalAbelianInP_specialLinearDiagonal (r := r)
  have hμ : specialLinearRestrictedRoot r ℝ i j ≠ 0 :=
    (Submodule.mem_restrictedRoots.mp (specialLinearRestrictedRootIndex r i j hij).property).1
  have hE : single i j hij (1 : ℝ) ∈
      (specialLinearDiagonal r ℝ).restrictedRootSpace (specialLinearRestrictedRoot r ℝ i j) := by
    rw [restrictedRootSpace_specialLinearRestrictedRoot hij]
    exact mem_span_singleton_self _
  obtain ⟨F, hF, hT⟩ := hθ.exists_isSl2Triple_restrictedCoroot h𝔞 hμ hE
    (isSl2Triple_single (R := ℝ) hij).e_ne_zero
  rw [neg_specialLinearRestrictedRoot, restrictedRootSpace_specialLinearRestrictedRoot hij.symm,
    mem_span_singleton] at hF
  obtain ⟨c, rfl⟩ := hF
  have hH := hT.lie_e_f
  rw [lie_smul, lie_single_single_eq_singleSubSingle hij 1] at hH
  have h2 := hθ.apply_restrictedCoroot h𝔞.le_cartanP hμ
  rw [specialLinearRestrictedRoot_apply, ← hH] at h2
  simp only [SetLike.val_smul, Matrix.smul_apply, val_singleSubSingle, Matrix.sub_apply,
    Matrix.single_apply, hij, hij.symm, and_self, ite_true, ite_false, smul_eq_mul] at h2
  have hc : c = 1 := by linarith
  subst hc
  rw [LieEquiv.IsCartanInvolution.restrictedRootPairing_coroot]
  exact Subtype.ext (hH.symm.trans (one_smul ℝ _))

/-- The pairing of `e_i - e_j` with the coroot of `e_k - e_l` is `δ_ik - δ_il - δ_jk + δ_jl`. -/
theorem specialLinearRestrictedRootPairing_pairing {i j k l : Fin (r + 1)} (hij : i ≠ j)
    (hkl : k ≠ l) :
    (specialLinearRestrictedRootPairing r).pairing (specialLinearRestrictedRootIndex r i j hij)
        (specialLinearRestrictedRootIndex r k l hkl) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) - (if j = k then 1 else 0) +
        (if j = l then 1 else 0) := by
  rw [← RootPairing.root_coroot_eq_pairing, specialLinearRestrictedRootPairing_coroot,
    LieEquiv.IsCartanInvolution.restrictedRootPairing_toLinearMap_apply,
    LieEquiv.IsCartanInvolution.restrictedRootPairing_root, coe_specialLinearRestrictedRootIndex,
    specialLinearRestrictedRoot_apply]
  simp only [val_singleSubSingle, Matrix.sub_apply, Matrix.single_apply, and_self]
  split_ifs <;> subst_vars <;> simp_all

/-- The restricted roots of `𝔰𝔩_{r+1}(ℝ)` form a finite set. -/
instance finite_restrictedRoots_specialLinearDiagonal :
    Finite (specialLinearDiagonal r ℝ).restrictedRoots :=
  ((isCartanInvolution_specialLinearNegTranspose r).finite_restrictedRoots _).to_subtype

/-- **The restricted root system of `𝔰𝔩_{r+1}(ℝ)` is reduced**: the only restricted roots
proportional to a restricted root `α` are `±α`. -/
instance isReduced_specialLinearRestrictedRootPairing :
    (specialLinearRestrictedRootPairing r).IsReduced := by
  refine ⟨fun μ ν h ↦ ?_⟩
  rw [← RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent,
    RootPairing.coxeterWeight] at h
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_specialLinearRestrictedRootIndex μ
  obtain ⟨k, l, hkl, rfl⟩ := exists_eq_specialLinearRestrictedRootIndex ν
  rw [specialLinearRestrictedRootPairing_pairing, specialLinearRestrictedRootPairing_pairing] at h
  simp only [LieEquiv.IsCartanInvolution.restrictedRootPairing_root,
    coe_specialLinearRestrictedRootIndex, neg_specialLinearRestrictedRoot]
  split_ifs at h <;> subst_vars <;> simp_all

/-! ### The base of simple roots -/

variable (r) in
/-- The simple restricted root `e_k - e_{k+1}` of `𝔰𝔩_{r+1}(ℝ)`, for `k < r`. -/
def specialLinearSimpleRestrictedRootIndex (k : Fin r) :
    (specialLinearDiagonal r ℝ).restrictedRoots :=
  specialLinearRestrictedRootIndex r k.castSucc k.succ Fin.castSucc_lt_succ.ne

theorem specialLinearSimpleRestrictedRootIndex_def (k : Fin r) :
    specialLinearSimpleRestrictedRootIndex r k =
      specialLinearRestrictedRootIndex r k.castSucc k.succ Fin.castSucc_lt_succ.ne :=
  (rfl)

/-- Distinct indices give distinct simple restricted roots. -/
theorem specialLinearSimpleRestrictedRootIndex_injective :
    Function.Injective (specialLinearSimpleRestrictedRootIndex r) := fun k l h ↦ by
  have h' := congrArg (fun μ : (specialLinearDiagonal r ℝ).restrictedRoots ↦
    (μ : Dual ℝ (specialLinearDiagonal r ℝ))) h
  simp only [specialLinearSimpleRestrictedRootIndex_def, coe_specialLinearRestrictedRootIndex] at h'
  exact Fin.castSucc_injective _ ((specialLinearRestrictedRoot_inj Fin.castSucc_lt_succ.ne).mp h').1

/-- Every restricted root is a sum of simple roots or the negative of one. -/
private theorem root_mem_or_neg_mem_closure (μ : (specialLinearDiagonal r ℝ).restrictedRoots) :
    (specialLinearRestrictedRootPairing r).root μ ∈
        AddSubmonoid.closure ((specialLinearRestrictedRootPairing r).root ''
          range (specialLinearSimpleRestrictedRootIndex r)) ∨
      -(specialLinearRestrictedRootPairing r).root μ ∈
        AddSubmonoid.closure ((specialLinearRestrictedRootPairing r).root ''
          range (specialLinearSimpleRestrictedRootIndex r)) := by
  have hroot (i j : Fin (r + 1)) (hij : i ≠ j) :
      (specialLinearRestrictedRootPairing r).root (specialLinearRestrictedRootIndex r i j hij) =
        specialLinearRestrictedRoot r ℝ i 0 - specialLinearRestrictedRoot r ℝ j 0 := by
    rw [LieEquiv.IsCartanInvolution.restrictedRootPairing_root,
      coe_specialLinearRestrictedRootIndex,
      specialLinearRestrictedRoot_sub_specialLinearRestrictedRoot]
  refine RootPairing.root_mem_or_neg_mem_closure_of_forall_exists_eq_sub
    (fun a ↦ specialLinearRestrictedRoot r ℝ a 0) (fun k ↦ hroot _ _ _) (fun ν ↦ ?_) μ
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_specialLinearRestrictedRootIndex ν
  exact ⟨i, j, hroot i j hij⟩

variable (r) in
/-- **The base of simple restricted roots** `e_k - e_{k+1}`, `k < r`, of `𝔰𝔩_{r+1}(ℝ)`. -/
noncomputable def specialLinearRestrictedRootBase :
    (specialLinearRestrictedRootPairing r).Base :=
  RootPairing.Base.mk' _ (range (specialLinearSimpleRestrictedRootIndex r))
    (RootPairing.linearIndepOn_root_range_of_root_mem_or_neg_mem_closure
      specialLinearSimpleRestrictedRootIndex_injective root_mem_or_neg_mem_closure <| by
        rw [Subspace.dual_finrank_eq, finrank_eq_card_basis (specialLinearCorootBasis r ℝ),
          Fintype.card_fin])
    root_mem_or_neg_mem_closure

/-- The simple roots of `TauCeti.specialLinearRestrictedRootBase` are the `e_k - e_{k+1}`. -/
theorem specialLinearRestrictedRootBase_support :
    (specialLinearRestrictedRootBase r).support =
      simpleSupport (specialLinearSimpleRestrictedRootIndex_injective (r := r)) := by
  ext μ
  simp [specialLinearRestrictedRootBase, RootPairing.Base.mk']

/-- The pairing of the simple roots `e_a - e_{a+1}` and `e_b - e_{b+1}` is the `(a, b)` entry of
the Cartan matrix of type `A_r`. -/
theorem specialLinearRestrictedRootPairing_pairing_simple (a b : Fin r) :
    (specialLinearRestrictedRootPairing r).pairing (specialLinearSimpleRestrictedRootIndex r a)
        (specialLinearSimpleRestrictedRootIndex r b) =
      (CartanMatrix.A r a b : ℝ) := by
  rw [specialLinearSimpleRestrictedRootIndex_def, specialLinearSimpleRestrictedRootIndex_def,
    specialLinearRestrictedRootPairing_pairing]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

/-- **The restricted root system of `𝔰𝔩_{r+1}(ℝ)` has Cartan type `A_r`**: relative to the base
of simple roots `e_k - e_{k+1}` its Cartan matrix is `CartanMatrix.A r`. In particular the
restricted root system of `𝔰𝔩₃(ℝ)` has type `A₂`. -/
theorem hasCartanType_specialLinearRestrictedRootPairing :
    HasCartanType (specialLinearRestrictedRootPairing r) (specialLinearRestrictedRootBase r)
      (.A r) :=
  hasCartanType_of_pairing_eq (t := .A r)
    (specialLinearSimpleRestrictedRootIndex_injective (r := r))
    specialLinearRestrictedRootBase_support fun a b ↦
      (specialLinearRestrictedRootPairing_pairing_simple (r := r) a b).trans (by simp)

/-- **Every restricted root of `𝔰𝔩_{r+1}(ℝ)` has multiplicity `1`**: its root space is the line
`ℝ E_ij`. -/
theorem finrank_restrictedRootSpace_specialLinearDiagonal
    (μ : (specialLinearDiagonal r ℝ).restrictedRoots) :
    finrank ℝ ((specialLinearDiagonal r ℝ).restrictedRootSpace μ) = 1 := by
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_specialLinearRestrictedRootIndex μ
  rw [coe_specialLinearRestrictedRootIndex, restrictedRootSpace_specialLinearRestrictedRoot hij,
    finrank_span_singleton (isSl2Triple_single (R := ℝ) hij).e_ne_zero]

end TauCeti
