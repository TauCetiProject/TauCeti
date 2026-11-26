/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.RootPairing
public import TauCeti.Algebra.Lie.SpecialLinear.Diagonal
public import TauCeti.Algebra.Lie.SpecialLinear.RestrictedRoot.Complex
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.LinearAlgebra.RootSystem.ConsecutiveDifferenceBase

/-!
# The restricted root system of `𝔰𝔩_n(ℂ)` viewed as real has type `A`

On `𝔰𝔩_n(ℂ)` viewed as a real Lie algebra, with the Cartan involution `θ X = -Xᴴ` and the
maximal abelian subspace `𝔞 ⊆ 𝔭` of real trace-zero diagonal matrices, the restricted roots are
the `e_i - e_j`, `i ≠ j`, with root spaces the complex lines `ℂ E_ij`
(`TauCeti.mem_restrictedRoots_slComplexRealDiagonal_iff`,
`TauCeti.mem_restrictedRootSpace_slComplexRestrictedRoot_iff`). This file reads off the restricted
root pairing `LieEquiv.IsCartanInvolution.restrictedRootPairing` of this example:

* the restricted coroot of `e_i - e_j` is `E_ii - E_jj`, so the pairing of `e_i - e_j` with the
  coroot of `e_k - e_l` is `δ_ik - δ_il - δ_jk + δ_jl`, as for `𝔰𝔩_n(ℝ)`
  (`TauCeti.specialLinearRestrictedRootPairing_pairing`);
* for `n = r + 1`, `𝔞` has dimension `r` (`TauCeti.slComplexRealDiagonalEquiv` identifies it with
  the trace-zero real diagonal matrices), and the simple roots `e_k - e_{k+1}`, `k < r`, form a
  base whose Cartan matrix is `CartanMatrix.A r`: the restricted root system has Cartan type
  `A_r`, in particular `A₂` for `𝔰𝔩₃(ℂ)`;
* every restricted root has multiplicity `2`
  (`TauCeti.finrank_restrictedRootSpace_slComplexRestrictedRoot`).

So `𝔰𝔩_{r+1}(ℂ)` viewed as real and its split real form `𝔰𝔩_{r+1}(ℝ)`
(`TauCeti.hasCartanType_specialLinearRestrictedRootPairing`) have the same restricted root system,
with multiplicities `2` and `1`.

## Main definitions

* `TauCeti.slComplexRestrictedRootPairing`: the restricted root pairing of `𝔰𝔩_n(ℂ)` as real.
* `TauCeti.slComplexRestrictedRootBase`: the base of simple roots `e_k - e_{k+1}`.

## Main results

* `TauCeti.slComplexRestrictedRootPairing_coroot`: the coroot of `e_i - e_j` is `E_ii - E_jj`.
* `TauCeti.hasCartanType_slComplexRestrictedRootPairing`: the restricted root system of
  `𝔰𝔩_{r+1}(ℂ)` viewed as real has Cartan type `A_r`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra LieAlgebra.SpecialLinear Matrix Module Submodule Set

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `-(e_i - e_j) = e_j - e_i`. -/
theorem neg_slComplexRestrictedRoot (i j : n) :
    -slComplexRestrictedRoot n i j = slComplexRestrictedRoot n j i :=
  LinearMap.ext fun H ↦ by simp

/-- `(e_i - e_k) - (e_j - e_k) = e_i - e_j`. -/
theorem slComplexRestrictedRoot_sub_slComplexRestrictedRoot (i j k : n) :
    slComplexRestrictedRoot n i k - slComplexRestrictedRoot n j k = slComplexRestrictedRoot n i j :=
  LinearMap.ext fun H ↦ by simp

variable (n) in
/-- **The restricted root pairing of `𝔰𝔩_n(ℂ)` viewed as real**, for the Cartan involution
`X ↦ -Xᴴ` and the real trace-zero diagonal matrices `𝔞`. -/
noncomputable abbrev slComplexRestrictedRootPairing :
    RootPairing (slComplexRealDiagonal n).restrictedRoots ℝ
      (Dual ℝ (slComplexRealDiagonal n)) (slComplexRealDiagonal n) :=
  isCartanInvolution_slComplexNegConjTranspose.restrictedRootPairing
    isMaximalAbelianInP_slComplexRealDiagonal

variable (n) in
/-- The restricted root `e_i - e_j`, for `i ≠ j`, as an index of the restricted root pairing. -/
noncomputable def slComplexRestrictedRootIndex (i j : n) (hij : i ≠ j) :
    (slComplexRealDiagonal n).restrictedRoots :=
  ⟨slComplexRestrictedRoot n i j,
    mem_restrictedRoots_slComplexRealDiagonal_iff.mpr ⟨i, j, hij, rfl⟩⟩

@[simp]
theorem coe_slComplexRestrictedRootIndex {i j : n} (hij : i ≠ j) :
    (slComplexRestrictedRootIndex n i j hij : Dual ℝ (slComplexRealDiagonal n)) =
      slComplexRestrictedRoot n i j :=
  (rfl)

/-- Every restricted root of `𝔰𝔩_n(ℂ)` viewed as real is some `e_i - e_j`. -/
theorem exists_eq_slComplexRestrictedRootIndex (μ : (slComplexRealDiagonal n).restrictedRoots) :
    ∃ i j, ∃ hij : i ≠ j, μ = slComplexRestrictedRootIndex n i j hij := by
  obtain ⟨i, j, hij, h⟩ := mem_restrictedRoots_slComplexRealDiagonal_iff.mp μ.property
  exact ⟨i, j, hij, Subtype.ext h⟩

/-- In `𝔰𝔩_n(ℂ)`, `[E_ij, c E_ji] = c (E_ii - E_jj)` for `i ≠ j`. -/
private theorem coe_lie_single_single {i j : n} (hij : i ≠ j) (c : ℂ) :
    ((⁅(⟨single i j 1, single_mem_slComplexReal hij 1⟩ : slComplexReal n),
        (⟨single j i c, single_mem_slComplexReal hij.symm c⟩ : slComplexReal n)⁆ :
          slComplexReal n) : Matrix n n ℂ) = c • (single i i 1 - single j j 1) := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, single_mul_single_same,
    single_mul_single_same, smul_sub, smul_single, smul_single]
  simp

/-- **The restricted coroot of `e_i - e_j` is `E_ii - E_jj`.** -/
theorem slComplexRestrictedRootPairing_coroot {i j : n} (hij : i ≠ j) :
    (slComplexRestrictedRootPairing n).coroot (slComplexRestrictedRootIndex n i j hij) =
      slComplexRealDiagonalSingleSubSingle n i j := by
  -- `E_ij` lies in `𝔤_{e_i - e_j}`, so the `𝔰𝔩₂` triple `(H', E_ij, F)` of the restricted root
  -- has `F = c E_ji`, hence `H' = [E_ij, F] = c (E_ii - E_jj)`; `H' ∈ 𝔞` forces `c` real, and
  -- `(e_i - e_j)(H') = 2` forces `c = 1`.
  have hθ := isCartanInvolution_slComplexNegConjTranspose (n := n)
  have h𝔞 := isMaximalAbelianInP_slComplexRealDiagonal (n := n)
  have hμ : slComplexRestrictedRoot n i j ≠ 0 := slComplexRestrictedRoot_ne_zero hij
  set E : slComplexReal n := ⟨single i j 1, single_mem_slComplexReal hij 1⟩
  have hE : E ∈ (slComplexRealDiagonal n).restrictedRootSpace (slComplexRestrictedRoot n i j) :=
    (mem_restrictedRootSpace_slComplexRestrictedRoot_iff hij).mpr (by simp [E])
  have hE0 : E ≠ 0 := fun h ↦ by
    simpa [E] using congrFun (congrFun (congrArg Subtype.val h) i) j
  obtain ⟨F, hF, hT⟩ := hθ.exists_isSl2Triple_restrictedCoroot h𝔞 hμ hE hE0
  rw [neg_slComplexRestrictedRoot, mem_restrictedRootSpace_slComplexRestrictedRoot_iff hij.symm]
    at hF
  set c := (F : Matrix n n ℂ) j i
  have hFc : F = ⟨single j i c, single_mem_slComplexReal hij.symm c⟩ := Subtype.ext hF
  set H := hθ.restrictedCoroot h𝔞.le_cartanP (slComplexRestrictedRoot n i j)
  have hH : (((H : slComplexRealDiagonal n) : slComplexReal n) : Matrix n n ℂ) =
      c • (single i i 1 - single j j 1) := by
    rw [← hT.lie_e_f, hFc, coe_lie_single_single hij]
  have him : c.im = 0 := by
    simpa [hH, Matrix.sub_apply, Matrix.single_apply, hij, hij.symm] using
      (mem_slComplexRealDiagonal.mp H.property).2 i
  have h2 := hθ.apply_restrictedCoroot h𝔞.le_cartanP hμ
  rw [slComplexRestrictedRoot_apply, hH] at h2
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, hij, hij.symm, and_self,
    ite_true, ite_false, smul_eq_mul, mul_one, sub_zero, zero_sub, mul_neg,
    Complex.neg_re] at h2
  have hc : c = 1 := Complex.ext (by simp; linarith) (by simpa using him)
  rw [LieEquiv.IsCartanInvolution.restrictedRootPairing_coroot]
  refine Subtype.ext (Subtype.ext ?_)
  change (((H : slComplexRealDiagonal n) : slComplexReal n) : Matrix n n ℂ) = _
  rw [hH, hc, one_smul, coe_slComplexRealDiagonalSingleSubSingle]

/-- The pairing of `e_i - e_j` with the coroot of `e_k - e_l` is `δ_ik - δ_il - δ_jk + δ_jl`. -/
theorem slComplexRestrictedRootPairing_pairing {i j k l : n} (hij : i ≠ j) (hkl : k ≠ l) :
    (slComplexRestrictedRootPairing n).pairing (slComplexRestrictedRootIndex n i j hij)
        (slComplexRestrictedRootIndex n k l hkl) =
      (if i = k then 1 else 0) - (if i = l then 1 else 0) - (if j = k then 1 else 0) +
        (if j = l then 1 else 0) := by
  rw [← RootPairing.root_coroot_eq_pairing, slComplexRestrictedRootPairing_coroot,
    LieEquiv.IsCartanInvolution.restrictedRootPairing_toLinearMap_apply,
    LieEquiv.IsCartanInvolution.restrictedRootPairing_root, coe_slComplexRestrictedRootIndex,
    slComplexRestrictedRoot_slComplexRealDiagonalSingleSubSingle]
  split_ifs <;> subst_vars <;> simp_all

/-- The restricted roots of `𝔰𝔩_n(ℂ)` viewed as real form a finite set. -/
instance finite_restrictedRoots_slComplexRealDiagonal :
    Finite (slComplexRealDiagonal n).restrictedRoots :=
  (isCartanInvolution_slComplexNegConjTranspose.finite_restrictedRoots _).to_subtype

/-- **The restricted root system of `𝔰𝔩_n(ℂ)` viewed as real is reduced**: although every
restricted root space has dimension `2`, the only restricted roots proportional to `α` are
`±α`. -/
instance isReduced_slComplexRestrictedRootPairing :
    (slComplexRestrictedRootPairing n).IsReduced := by
  refine ⟨fun μ ν h ↦ ?_⟩
  rw [← RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent,
    RootPairing.coxeterWeight] at h
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_slComplexRestrictedRootIndex μ
  obtain ⟨k, l, hkl, rfl⟩ := exists_eq_slComplexRestrictedRootIndex ν
  rw [slComplexRestrictedRootPairing_pairing, slComplexRestrictedRootPairing_pairing] at h
  simp only [LieEquiv.IsCartanInvolution.restrictedRootPairing_root,
    coe_slComplexRestrictedRootIndex, neg_slComplexRestrictedRoot]
  split_ifs at h <;> subst_vars <;> simp_all

end General

/-! ### The dimension of `𝔞` and the base of simple roots -/

variable {r : ℕ}

variable (r) in
/-- The real trace-zero diagonal matrices in `𝔰𝔩_{r+1}(ℂ)` are the trace-zero diagonal matrices
of `𝔰𝔩_{r+1}(ℝ)`, through the real parts of the entries. -/
noncomputable def slComplexRealDiagonalEquiv :
    slComplexRealDiagonal (Fin (r + 1)) ≃ₗ[ℝ] specialLinearDiagonal r ℝ where
  toFun H := ⟨⟨(H : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).map Complex.re, by
      rw [mem_sl_iff, trace]
      simp only [diag_apply, map_apply]
      rw [← Complex.re_sum]
      exact congrArg Complex.re (mem_slComplexReal_iff.mp H.val.property)⟩,
    (mem_specialLinearDiagonal_iff r ℝ _).mpr
      ((mem_slComplexRealDiagonal.mp H.property).1.map Complex.zero_re)⟩
  invFun X := ⟨⟨(X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ).map Complex.ofReal, by
      rw [mem_slComplexReal_iff, trace]
      simp only [diag_apply, map_apply]
      rw [← Complex.ofReal_sum]
      exact congrArg Complex.ofReal (mem_sl_iff.mp X.val.property)⟩,
    mem_slComplexRealDiagonal.mpr
      ⟨((mem_specialLinearDiagonal_iff r ℝ _).mp X.property).map Complex.ofReal_zero,
        fun _ ↦ by simp⟩⟩
  left_inv H := by
    refine Subtype.ext (Subtype.ext (Matrix.ext fun k l ↦ ?_))
    by_cases hkl : k = l
    · subst hkl
      simpa using ofReal_re_apply_self_of_mem_slComplexRealDiagonal H.property k
    · simp [(mem_slComplexRealDiagonal.mp H.property).1 hkl]
  right_inv X := Subtype.ext (Subtype.ext (Matrix.ext fun k l ↦ by simp))
  map_add' _ _ := Subtype.ext (Subtype.ext (Matrix.ext fun _ _ ↦ by simp))
  map_smul' _ _ := Subtype.ext (Subtype.ext (Matrix.ext fun _ _ ↦ by simp))

/-- `𝔞` has dimension `r` in `𝔰𝔩_{r+1}(ℂ)` viewed as real. -/
theorem finrank_slComplexRealDiagonal :
    finrank ℝ (slComplexRealDiagonal (Fin (r + 1))) = r := by
  rw [(slComplexRealDiagonalEquiv r).finrank_eq,
    finrank_eq_card_basis (specialLinearCorootBasis r ℝ), Fintype.card_fin]

variable (r) in
/-- The simple restricted root `e_k - e_{k+1}` of `𝔰𝔩_{r+1}(ℂ)` viewed as real, for `k < r`. -/
noncomputable def slComplexSimpleRestrictedRootIndex (k : Fin r) :
    (slComplexRealDiagonal (Fin (r + 1))).restrictedRoots :=
  slComplexRestrictedRootIndex (Fin (r + 1)) k.castSucc k.succ Fin.castSucc_lt_succ.ne

theorem slComplexSimpleRestrictedRootIndex_def (k : Fin r) :
    slComplexSimpleRestrictedRootIndex r k =
      slComplexRestrictedRootIndex (Fin (r + 1)) k.castSucc k.succ Fin.castSucc_lt_succ.ne :=
  (rfl)

/-- Distinct indices give distinct simple restricted roots. -/
theorem slComplexSimpleRestrictedRootIndex_injective :
    Function.Injective (slComplexSimpleRestrictedRootIndex r) := fun k l h ↦ by
  have h' := congrArg (fun μ : (slComplexRealDiagonal (Fin (r + 1))).restrictedRoots ↦
    (μ : Dual ℝ (slComplexRealDiagonal (Fin (r + 1))))) h
  simp only [slComplexSimpleRestrictedRootIndex_def, coe_slComplexRestrictedRootIndex] at h'
  exact Fin.castSucc_injective _ ((slComplexRestrictedRoot_inj Fin.castSucc_lt_succ.ne).mp h').1

/-- Every restricted root is a sum of simple roots or the negative of one. -/
private theorem root_mem_or_neg_mem_closure
    (μ : (slComplexRealDiagonal (Fin (r + 1))).restrictedRoots) :
    (slComplexRestrictedRootPairing (Fin (r + 1))).root μ ∈
        AddSubmonoid.closure ((slComplexRestrictedRootPairing (Fin (r + 1))).root ''
          range (slComplexSimpleRestrictedRootIndex r)) ∨
      -(slComplexRestrictedRootPairing (Fin (r + 1))).root μ ∈
        AddSubmonoid.closure ((slComplexRestrictedRootPairing (Fin (r + 1))).root ''
          range (slComplexSimpleRestrictedRootIndex r)) := by
  have hroot (i j : Fin (r + 1)) (hij : i ≠ j) :
      (slComplexRestrictedRootPairing (Fin (r + 1))).root
          (slComplexRestrictedRootIndex (Fin (r + 1)) i j hij) =
        slComplexRestrictedRoot (Fin (r + 1)) i 0 - slComplexRestrictedRoot (Fin (r + 1)) j 0 := by
    rw [LieEquiv.IsCartanInvolution.restrictedRootPairing_root,
      coe_slComplexRestrictedRootIndex, slComplexRestrictedRoot_sub_slComplexRestrictedRoot]
  refine RootPairing.root_mem_or_neg_mem_closure_of_forall_exists_eq_sub
    (fun a ↦ slComplexRestrictedRoot (Fin (r + 1)) a 0) (fun k ↦ hroot _ _ _) (fun ν ↦ ?_) μ
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_slComplexRestrictedRootIndex ν
  exact ⟨i, j, hroot i j hij⟩

variable (r) in
/-- **The base of simple restricted roots** `e_k - e_{k+1}`, `k < r`, of `𝔰𝔩_{r+1}(ℂ)` viewed as
real. -/
noncomputable def slComplexRestrictedRootBase :
    (slComplexRestrictedRootPairing (Fin (r + 1))).Base :=
  RootPairing.Base.mk' _ (range (slComplexSimpleRestrictedRootIndex r))
    (RootPairing.linearIndepOn_root_range_of_root_mem_or_neg_mem_closure
      slComplexSimpleRestrictedRootIndex_injective root_mem_or_neg_mem_closure <| by
        rw [Subspace.dual_finrank_eq, finrank_slComplexRealDiagonal])
    root_mem_or_neg_mem_closure

/-- The simple roots of `TauCeti.slComplexRestrictedRootBase` are the `e_k - e_{k+1}`. -/
theorem slComplexRestrictedRootBase_support :
    (slComplexRestrictedRootBase r).support =
      simpleSupport (slComplexSimpleRestrictedRootIndex_injective (r := r)) := by
  ext μ
  simp [slComplexRestrictedRootBase, RootPairing.Base.mk']

/-- The pairing of the simple roots `e_a - e_{a+1}` and `e_b - e_{b+1}` is the `(a, b)` entry of
the Cartan matrix of type `A_r`. -/
theorem slComplexRestrictedRootPairing_pairing_simple (a b : Fin r) :
    (slComplexRestrictedRootPairing (Fin (r + 1))).pairing
        (slComplexSimpleRestrictedRootIndex r a) (slComplexSimpleRestrictedRootIndex r b) =
      (CartanMatrix.A r a b : ℝ) := by
  rw [slComplexSimpleRestrictedRootIndex_def, slComplexSimpleRestrictedRootIndex_def,
    slComplexRestrictedRootPairing_pairing]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> omega

/-- **The restricted root system of `𝔰𝔩_{r+1}(ℂ)` viewed as real has Cartan type `A_r`**: relative
to the base of simple roots `e_k - e_{k+1}` its Cartan matrix is `CartanMatrix.A r`. In particular
the restricted root system of `𝔰𝔩₃(ℂ)` viewed as real has type `A₂`, with every restricted root of
multiplicity `2` (`TauCeti.finrank_restrictedRootSpace_slComplexRestrictedRoot`). -/
theorem hasCartanType_slComplexRestrictedRootPairing :
    HasCartanType (slComplexRestrictedRootPairing (Fin (r + 1))) (slComplexRestrictedRootBase r)
      (.A r) :=
  hasCartanType_of_pairing_eq (t := .A r)
    (slComplexSimpleRestrictedRootIndex_injective (r := r))
    slComplexRestrictedRootBase_support fun a b ↦
      (slComplexRestrictedRootPairing_pairing_simple (r := r) a b).trans (by simp)

/-- **Every restricted root of `𝔰𝔩_n(ℂ)` viewed as real has multiplicity `2`.** -/
theorem finrank_restrictedRootSpace_slComplexRealDiagonal {n : Type*} [Fintype n] [DecidableEq n]
    (μ : (slComplexRealDiagonal n).restrictedRoots) :
    finrank ℝ ((slComplexRealDiagonal n).restrictedRootSpace μ) = 2 := by
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_slComplexRestrictedRootIndex μ
  exact finrank_restrictedRootSpace_slComplexRestrictedRoot hij

end TauCeti
