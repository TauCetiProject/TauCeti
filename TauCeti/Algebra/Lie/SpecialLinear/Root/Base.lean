/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Base
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.SpecialLinear.Character
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.Algebra.Group.Submonoid.Telescoping
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# The roots and the standard base of `sl (Fin (r + 1))`

Let `H = TauCeti.specialLinearDiagonalCartan r K` be the trace-zero diagonal matrices of
`L = sl (Fin (r + 1)) K` over a field `K`, and let `εₖ` be the coordinate weights
`TauCeti.specialLinearEpsilon`. This file computes the roots of `L` relative to `H` and, in
characteristic zero, where `L` has a non-degenerate Killing form, equips its root system with the
standard base. These are the data `(H, b)` over which the general highest-weight theory is stated,
so that it can be evaluated on `sl (Fin (r + 1))`.

* The signed matrix units together with the simple coroots form a basis of `H`-weight vectors
  (`TauCeti.lie_specialLinearDiagonalCartan_specialLinearRootBasis`), so `L` is triangularizable
  over `H` over every field, with no algebraic closure assumed.
* The roots are the weights `εᵢ - εⱼ` for `i ≠ j` (`TauCeti.specialLinearRoot`), with root vector
  the matrix unit `Eᵢⱼ`, and every nonzero weight is one of them. The coroot of `εᵢ - εⱼ` is
  `Eᵢᵢ - Eⱼⱼ`, the `h` of the standard `sl₂` triple `TauCeti.isSl2Triple_single`.
* The simple roots `αₖ = εₖ - εₖ₊₁`, `k < r`, form a base `TauCeti.specialLinearPositiveBase` of the
  root system. Relative to it `εᵢ - εⱼ` has height `j - i`, so it is positive exactly when `i < j`:
  the positive root vectors are the strictly upper triangular matrix units, and the simple coroots
  are the basis `TauCeti.specialLinearDiagonalCartanBasis` of `H`.

## Main definitions

* `TauCeti.specialLinearRoot`: the root `εᵢ - εⱼ`, for `i ≠ j`, as a weight of `L`.
* `TauCeti.specialLinearRootIndex`: the same root as an index of the root system.
* `TauCeti.specialLinearSimpleRootIndex`: the simple root `αₖ = εₖ - εₖ₊₁`.
* `TauCeti.specialLinearPositiveBase`: the base of simple roots.

## Main results

* `TauCeti.exists_eq_specialLinearRoot`: every nonzero weight of `L` is a root `εᵢ - εⱼ`.
* `TauCeti.coe_coroot_specialLinearRoot`: the coroot of `εᵢ - εⱼ` is `Eᵢᵢ - Eⱼⱼ`.
* `TauCeti.mem_specialLinearPositiveBase_support_iff`: the simple roots are the `αₖ`.
* `TauCeti.height_specialLinearRootIndex`: the root `εᵢ - εⱼ` has height `j - i`.
* `TauCeti.isPos_specialLinearRootIndex_iff`: the root `εᵢ - εⱼ` is positive iff `i < j`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8.1 and §10.1.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §15.1.
-/

public section

open LieAlgebra LieModule Module LieAlgebra.SpecialLinear

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The roots -/

section Field

variable {r : ℕ} {K : Type*} [Field K]

variable (r K) in
/-- **The root `εᵢ - εⱼ`** of `sl (Fin (r + 1)) K`, for `i ≠ j`, as a weight of the diagonal Cartan
subalgebra. Its root space contains the matrix unit `Eᵢⱼ`
(`TauCeti.single_mem_rootSpace_specialLinearRoot`). -/
def specialLinearRoot (i j : Fin (r + 1)) (hij : i ≠ j) :
    Weight K (specialLinearDiagonalCartan r K) (sl (Fin (r + 1)) K) where
  toFun := specialLinearEpsilon r K i - specialLinearEpsilon r K j
  genWeightSpace_ne_bot' := (genWeightSpace_specialLinear_ne_bot_iff _).mpr
    ⟨.inr ⟨(i, j), hij⟩, by
      rw [specialLinearRootBasisWeight_inr]
      exact funext (LinearMap.sub_apply _ _)⟩

/-- The root `εᵢ - εⱼ` evaluates as the difference of two diagonal entries. -/
@[simp]
theorem specialLinearRoot_apply {i j : Fin (r + 1)} (hij : i ≠ j)
    (h : specialLinearDiagonalCartan r K) :
    specialLinearRoot r K i j hij h = specialLinearEpsilon r K i h - specialLinearEpsilon r K j h :=
  (rfl)

/-- The matrix unit `Eᵢⱼ` is a root vector for the root `εᵢ - εⱼ`. -/
theorem single_mem_rootSpace_specialLinearRoot {i j : Fin (r + 1)} (hij : i ≠ j) (c : K) :
    single i j hij c ∈
      rootSpace (specialLinearDiagonalCartan r K) (specialLinearRoot r K i j hij) :=
  weightSpace_le_genWeightSpace _ _ ((mem_weightSpace _ _).mpr fun h =>
    lie_specialLinearDiagonalCartan_single h hij c)

/-- The root `εᵢ - εⱼ` as a linear form on the diagonal Cartan subalgebra. -/
@[simp]
theorem toLinear_specialLinearRoot {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearRoot r K i j hij).toLinear =
      specialLinearEpsilon r K i - specialLinearEpsilon r K j :=
  LinearMap.ext fun _ => by simp

/-- The weight `εᵢ - εⱼ` is a root: it is nonzero, as it takes the value `2` on `Eᵢᵢ - Eⱼⱼ`. -/
theorem specialLinearRoot_isNonZero [NeZero (2 : K)] {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearRoot r K i j hij).IsNonZero := fun h => two_ne_zero (α := K) <| by
  have h2 := congrFun h ⟨_, singleSubSingle_mem_specialLinearDiagonalCartan i j 1⟩
  simp [val_singleSubSingle, hij, hij.symm] at h2
  linear_combination h2

/-- **Every nonzero weight of `sl (Fin (r + 1)) K` is a root `εᵢ - εⱼ`.** -/
theorem exists_eq_specialLinearRoot
    {χ : Weight K (specialLinearDiagonalCartan r K) (sl (Fin (r + 1)) K)} (hχ : χ.IsNonZero) :
    ∃ i j, ∃ hij : i ≠ j, χ = specialLinearRoot r K i j hij := by
  obtain ⟨p | ⟨⟨i, j⟩, hij⟩, hp⟩ :=
    (genWeightSpace_specialLinear_ne_bot_iff χ).mp χ.genWeightSpace_ne_bot
  · exact absurd (funext fun h => by simpa using (congrFun hp h).symm) hχ
  · refine ⟨i, j, hij, Weight.ext fun h => ?_⟩
    rw [← congrFun hp h, specialLinearRootBasisWeight_inr, specialLinearRoot_apply,
      LinearMap.sub_apply]

variable [CharZero K]

/-- The negative of the root `εᵢ - εⱼ` is the root `εⱼ - εᵢ`. -/
@[simp]
theorem neg_specialLinearRoot {i j : Fin (r + 1)} (hij : i ≠ j) :
    -specialLinearRoot r K i j hij = specialLinearRoot r K j i hij.symm :=
  Weight.ext fun h => by simp

/-- **The coroot of `εᵢ - εⱼ` is `Eᵢᵢ - Eⱼⱼ`**, the `h` of the standard `sl₂` triple
`(Eᵢᵢ - Eⱼⱼ, Eᵢⱼ, Eⱼᵢ)`. -/
@[simp]
theorem coe_coroot_specialLinearRoot {i j : Fin (r + 1)} (hij : i ≠ j) :
    ((IsKilling.coroot (specialLinearRoot r K i j hij) : specialLinearDiagonalCartan r K) :
      sl (Fin (r + 1)) K) = singleSubSingle i j 1 :=
  ((isSl2Triple_single (R := K) hij).h_eq_coroot (specialLinearRoot_isNonZero hij)
    (single_mem_rootSpace_specialLinearRoot hij 1)
    (by
      rw [← Weight.coe_neg, neg_specialLinearRoot]
      exact single_mem_rootSpace_specialLinearRoot hij.symm 1)).symm

/-- The roots `εᵢ - εⱼ` and `εₖ - εₗ` coincide exactly when `i = k` and `j = l`: their coroots
`Eᵢᵢ - Eⱼⱼ` and `Eₖₖ - Eₗₗ` must agree. -/
@[simp]
theorem specialLinearRoot_inj {i j k l : Fin (r + 1)} (hij : i ≠ j) (hkl : k ≠ l) :
    specialLinearRoot r K i j hij = specialLinearRoot r K k l hkl ↔ i = k ∧ j = l := by
  refine ⟨fun h => ?_, fun ⟨hik, hjl⟩ => by subst hik hjl; rfl⟩
  have hc := congrArg (fun α => ((IsKilling.coroot α : specialLinearDiagonalCartan r K) :
    sl (Fin (r + 1)) K)) h
  simp only [coe_coroot_specialLinearRoot] at hc
  have hii := congrArg (fun X : sl (Fin (r + 1)) K => (X : Matrix _ _ K) i i) hc
  have hjj := congrArg (fun X : sl (Fin (r + 1)) K => (X : Matrix _ _ K) j j) hc
  simp [val_singleSubSingle, Matrix.single_apply, hij, hij.symm] at hii hjj
  by_cases hki : k = i
  · by_cases hlj : l = j
    · exact ⟨hki.symm, hlj.symm⟩
    · simp [hki, hij, hlj] at hjj
  · by_cases hli : l = i
    · simp [hki, hli] at hii
      norm_num at hii
    · simp [hki, hli] at hii

variable (r K) in
/-- The root `εᵢ - εⱼ`, for `i ≠ j`, as an index of the root system of `sl (Fin (r + 1)) K`. -/
def specialLinearRootIndex (i j : Fin (r + 1)) (hij : i ≠ j) :
    (specialLinearDiagonalCartan r K).root :=
  ⟨specialLinearRoot r K i j hij, by
    simpa [LieSubalgebra.root] using specialLinearRoot_isNonZero hij⟩

/-- The weight underlying `TauCeti.specialLinearRootIndex` is the root `εᵢ - εⱼ`. -/
@[simp]
theorem coe_specialLinearRootIndex {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearRootIndex r K i j hij :
      Weight K (specialLinearDiagonalCartan r K) (sl (Fin (r + 1)) K)) =
      specialLinearRoot r K i j hij :=
  (rfl)

/-- The roots `εᵢ - εⱼ` and `εₖ - εₗ` are the same index exactly when `i = k` and `j = l`. -/
@[simp]
theorem specialLinearRootIndex_inj {i j k l : Fin (r + 1)} (hij : i ≠ j) (hkl : k ≠ l) :
    specialLinearRootIndex r K i j hij = specialLinearRootIndex r K k l hkl ↔ i = k ∧ j = l := by
  rw [Subtype.ext_iff, coe_specialLinearRootIndex, coe_specialLinearRootIndex,
    specialLinearRoot_inj]

/-- The root `εᵢ - εⱼ` of the root system, as a linear form on the diagonal Cartan subalgebra. -/
theorem rootSystem_root_specialLinearRootIndex {i j : Fin (r + 1)} (hij : i ≠ j) :
    (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root
        (specialLinearRootIndex r K i j hij) =
      specialLinearEpsilon r K i - specialLinearEpsilon r K j := by
  rw [IsKilling.rootSystem_root_apply, coe_specialLinearRootIndex, toLinear_specialLinearRoot]

/-- Every index of the root system of `sl (Fin (r + 1)) K` is a root `εᵢ - εⱼ`. -/
theorem exists_eq_specialLinearRootIndex (α : (specialLinearDiagonalCartan r K).root) :
    ∃ i j, ∃ hij : i ≠ j, α = specialLinearRootIndex r K i j hij := by
  obtain ⟨i, j, hij, h⟩ := exists_eq_specialLinearRoot (LieSubalgebra.isNonZero_coe_root α)
  exact ⟨i, j, hij, Subtype.ext h⟩

/-- The reflection of `εᵢ - εⱼ` in itself is `εⱼ - εᵢ`. -/
theorem reflectionPerm_specialLinearRootIndex_self {i j : Fin (r + 1)} (hij : i ≠ j) :
    (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).reflectionPerm
        (specialLinearRootIndex r K i j hij) (specialLinearRootIndex r K i j hij) =
      specialLinearRootIndex r K j i hij.symm :=
  (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root.injective <| by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      rootSystem_root_specialLinearRootIndex, rootSystem_root_specialLinearRootIndex, neg_sub]

/-! ### The standard base -/

variable (r K) in
/-- The simple root `αₖ = εₖ - εₖ₊₁` of `sl (Fin (r + 1)) K`, for `k < r`. -/
def specialLinearSimpleRootIndex (k : Fin r) : (specialLinearDiagonalCartan r K).root :=
  specialLinearRootIndex r K k.castSucc k.succ Fin.castSucc_lt_succ.ne

/-- The simple root `αₖ` is the root `εₖ - εₖ₊₁`. -/
theorem specialLinearSimpleRootIndex_def (k : Fin r) :
    specialLinearSimpleRootIndex r K k =
      specialLinearRootIndex r K k.castSucc k.succ Fin.castSucc_lt_succ.ne :=
  (rfl)

/-- The coroot of the simple root `αₖ` is the simple coroot `hₖ = Eₖₖ - Eₖ₊₁,ₖ₊₁`, the `k`-th
vector of `TauCeti.specialLinearDiagonalCartanBasis`. -/
theorem rootSystem_coroot_specialLinearSimpleRootIndex (k : Fin r) :
    (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).coroot
        (specialLinearSimpleRootIndex r K k) =
      specialLinearDiagonalCartanBasis r K k :=
  Subtype.ext <| by
    rw [IsKilling.rootSystem_coroot_apply, specialLinearSimpleRootIndex_def,
      coe_specialLinearRootIndex, coe_coroot_specialLinearRoot,
      specialLinearDiagonalCartanBasis_apply]

/-- Distinct indices give distinct simple roots. -/
theorem specialLinearSimpleRootIndex_injective :
    Function.Injective (specialLinearSimpleRootIndex r K) := fun k l hkl => by
  have h := congrArg (fun α => (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).coroot α)
    hkl
  simpa only [rootSystem_coroot_specialLinearSimpleRootIndex,
    (specialLinearDiagonalCartanBasis r K).injective.eq_iff] using h

/-- The images of the simple roots under the root map of the root system. -/
private theorem image_root_range_specialLinearSimpleRootIndex :
    (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root ''
        Set.range (specialLinearSimpleRootIndex r K) =
      Set.range fun k : Fin r =>
        specialLinearEpsilon r K k.castSucc - specialLinearEpsilon r K k.succ := by
  simp_rw [← Set.range_comp, Function.comp_def, specialLinearSimpleRootIndex_def,
    rootSystem_root_specialLinearRootIndex]

/-- Every root is a sum of simple roots or the negative of one. -/
private theorem root_mem_or_neg_mem_closure (α : (specialLinearDiagonalCartan r K).root) :
    (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root α ∈
        AddSubmonoid.closure ((IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root ''
          Set.range (specialLinearSimpleRootIndex r K)) ∨
      -(IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root α ∈
        AddSubmonoid.closure ((IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root ''
          Set.range (specialLinearSimpleRootIndex r K)) := by
  obtain ⟨i, j, hij, rfl⟩ := exists_eq_specialLinearRootIndex α
  rw [image_root_range_specialLinearSimpleRootIndex, rootSystem_root_specialLinearRootIndex,
    neg_sub]
  have hs (a b : Fin (r + 1)) (hab : (a : ℕ) + 1 = b) :
      specialLinearEpsilon r K a - specialLinearEpsilon r K b ∈
        AddSubmonoid.closure (Set.range fun k : Fin r =>
          specialLinearEpsilon r K k.castSucc - specialLinearEpsilon r K k.succ) := by
    have ha : (a : ℕ) < r := by omega
    obtain rfl : b = (⟨a, ha⟩ : Fin r).succ := Fin.ext (by simp; omega)
    exact AddSubmonoid.subset_closure ⟨⟨a, ha⟩, rfl⟩
  rcases le_total i j with h | h
  · exact .inl (sub_mem_of_consecutive_sub_mem_fin _ hs h)
  · exact .inr (sub_mem_of_consecutive_sub_mem_fin _ hs h)

/-- The simple roots are linearly independent: they span the dual of the diagonal Cartan
subalgebra, since every root is a combination of them, and there are `r` of them. -/
private theorem linearIndepOn_root_range_specialLinearSimpleRootIndex :
    LinearIndepOn K (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root
      (Set.range (specialLinearSimpleRootIndex r K)) := by
  set P := IsKilling.rootSystem (specialLinearDiagonalCartan r K)
  rw [linearIndepOn_range_iff specialLinearSimpleRootIndex_injective]
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [← RootPairing.IsRootSystem.span_root_eq_top (P := P), Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    have hsub : AddSubmonoid.closure (P.root '' Set.range (specialLinearSimpleRootIndex r K)) ≤
        (Submodule.span K
          (Set.range (P.root ∘ specialLinearSimpleRootIndex r K))).toAddSubmonoid := by
      rw [AddSubmonoid.closure_le, Set.range_comp]
      exact Submodule.subset_span
    rcases root_mem_or_neg_mem_closure α with h | h
    · exact hsub h
    · exact (Submodule.neg_mem_iff _).mp (hsub h)
  · rw [Fintype.card_fin, Subspace.dual_finrank_eq, finrank_eq_card_basis
      (specialLinearDiagonalCartanBasis r K), Fintype.card_fin]

variable (r K) in
/-- **The standard base of `sl (Fin (r + 1)) K`**: the simple roots `αₖ = εₖ - εₖ₊₁`, `k < r`, whose
root vectors are the matrix units `Eₖ,ₖ₊₁` just above the diagonal. -/
noncomputable def specialLinearPositiveBase :
    (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).Base :=
  RootPairing.Base.mk' _ (Set.range (specialLinearSimpleRootIndex r K))
    linearIndepOn_root_range_specialLinearSimpleRootIndex root_mem_or_neg_mem_closure

/-- The simple roots of the standard base are the `αₖ = εₖ - εₖ₊₁`. -/
@[simp]
theorem mem_specialLinearPositiveBase_support_iff {α : (specialLinearDiagonalCartan r K).root} :
    α ∈ (specialLinearPositiveBase r K).support ↔ ∃ k, specialLinearSimpleRootIndex r K k = α := by
  simp [specialLinearPositiveBase, RootPairing.Base.mk']

/-- Each `αₖ` is a simple root of the standard base. -/
theorem specialLinearSimpleRootIndex_mem_support (k : Fin r) :
    specialLinearSimpleRootIndex r K k ∈ (specialLinearPositiveBase r K).support :=
  mem_specialLinearPositiveBase_support_iff.mpr ⟨k, rfl⟩

/-- For `i < j`, the root `εᵢ - εⱼ` has height `j - i`. -/
private theorem height_specialLinearRootIndex_of_lt {i j : Fin (r + 1)} (hij : i < j) :
    (specialLinearPositiveBase r K).height (specialLinearRootIndex r K i j hij.ne) = j - i := by
  obtain ⟨n, hn⟩ : ∃ n, (j : ℕ) = i + (n + 1) := ⟨j - i - 1, by omega⟩
  induction n generalizing j with
  | zero =>
    have hk : (i : ℕ) < r := by omega
    have hi : (⟨i, hk⟩ : Fin r).castSucc = i := rfl
    have hj : (⟨i, hk⟩ : Fin r).succ = j := Fin.ext (by simp; omega)
    obtain rfl := hj
    have h := RootPairing.Base.height_one_of_mem_support
      (specialLinearSimpleRootIndex_mem_support (K := K) ⟨i, hk⟩)
    rw [specialLinearSimpleRootIndex_def] at h
    simp only [hi] at h
    rw [h]
    simp
  | succ n ih =>
    have hk : (i : ℕ) + (n + 1) < r := by omega
    have hm : i < ⟨i + (n + 1), by omega⟩ := Fin.mk_lt_mk.mpr (by simp)
    have hj : (⟨i + (n + 1), hk⟩ : Fin r).succ = j := Fin.ext (by simp; omega)
    have hroot : (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root
          (specialLinearRootIndex r K i j hij.ne) =
        (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root
            (specialLinearRootIndex r K i _ hm.ne) +
          (IsKilling.rootSystem (specialLinearDiagonalCartan r K)).root
            (specialLinearSimpleRootIndex r K ⟨i + (n + 1), hk⟩) := by
      rw [specialLinearSimpleRootIndex_def, rootSystem_root_specialLinearRootIndex,
        rootSystem_root_specialLinearRootIndex, rootSystem_root_specialLinearRootIndex, hj]
      have hc : (⟨i + (n + 1), hk⟩ : Fin r).castSucc = ⟨i + (n + 1), by omega⟩ := rfl
      rw [hc]
      abel
    rw [RootPairing.Base.height_add _ hroot, ih hm rfl,
      RootPairing.Base.height_one_of_mem_support (specialLinearSimpleRootIndex_mem_support _)]
    dsimp only
    omega

/-- **The height of the root `εᵢ - εⱼ`** relative to the standard base is `j - i`. -/
@[simp]
theorem height_specialLinearRootIndex {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearPositiveBase r K).height (specialLinearRootIndex r K i j hij) =
      (j : ℤ) - i := by
  rcases hij.lt_or_gt with h | h
  · exact height_specialLinearRootIndex_of_lt h
  · have := (specialLinearPositiveBase r K).height_reflectionPerm_self
      (specialLinearRootIndex r K j i h.ne)
    rw [RootPairing.indexNeg_neg, reflectionPerm_specialLinearRootIndex_self,
      height_specialLinearRootIndex_of_lt h] at this
    rw [this]
    ring

/-- **The root `εᵢ - εⱼ` is positive exactly when `i < j`**: the positive root vectors are the
strictly upper triangular matrix units. -/
@[simp]
theorem isPos_specialLinearRootIndex_iff {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearPositiveBase r K).IsPos (specialLinearRootIndex r K i j hij) ↔ i < j := by
  rw [RootPairing.Base.isPos_iff, height_specialLinearRootIndex, sub_pos, Nat.cast_lt,
    Fin.val_fin_lt]

end Field

end TauCeti
