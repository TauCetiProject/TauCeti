/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Basic
public import TauCeti.RepresentationTheory.Coinvariants

/-!
# The element `Tₙ^∞` of the group ring `ℛₙ`

Popa and Zagier write `Tₙ^∞` for the formal sum of the upper-triangular representatives
`ℳₙ^∞ = TauCeti.TraceFormulaMatrixModule.upperTriangularReps n` of `Γ \ ℳₙ`, an element of the
group ring `ℛₙ = ℚ[ℳₙ]`. This file defines it, over an arbitrary coefficient semiring `k`, as the
element `TauCeti.TraceFormulaMatrixModule.upperTriangularSum k n` of `k[ℳₙ]`.

Since `ℳₙ^∞` is a set of orbit representatives for `n ≠ 0`, every `SL(2, ℤ)`-orbit sum of the
coefficients of `Tₙ^∞` equals `1`. Right multiplication by `g ∈ PSL(2, ℤ)` commutes with the left
action, so it permutes the `SL(2, ℤ)`-orbits, and the orbit sums of the right translate `Tₙ^∞ · g`
are those of `Tₙ^∞` permuted; so they equal `1` too. Hence `Tₙ^∞ (1 - g)` lies in the
coinvariant kernel of the left action, which is the input for the existence of a solution of
Popa–Zagier's period relation (A). For `g = T ^ j` more is true: right multiplication by `T ^ j`
keeps matrices upper-triangular, so it permutes the `⟨T⟩`-orbits that meet `ℳₙ^∞`, and
`Tₙ^∞ (1 - T ^ j)` lies in `(1 - T)·k[ℳₙ]`.

## Main definitions

* `TauCeti.TraceFormulaMatrixModule.upperTriangularSum k n`: the element `Tₙ^∞` of `k[ℳₙ]`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.coeff_upperTriangularSum`: `Tₙ^∞` is the indicator function
  of `ℳₙ^∞`.
* `TauCeti.TraceFormulaMatrixModule.upperTriangularSum_zero`: `T₀^∞ = 0`.
* `TauCeti.TraceFormulaMatrixModule.mapDomain_coeff_upperTriangularSum_apply`: for `n ≠ 0`,
  every `SL(2, ℤ)`-orbit sum of `Tₙ^∞` is `1`.
* `TauCeti.TraceFormulaMatrixModule.one_sub_ofMulAction_op_upperTriangularSum_mem`:
  `Tₙ^∞ (1 - g)` lies in the coinvariant kernel of the left action of `SL(2, ℤ)`.
* `TauCeti.TraceFormulaMatrixModule.one_sub_ofMulAction_op_T_zpow_upperTriangularSum_mem_range`:
  `Tₙ^∞ (1 - T ^ j)` lies in `(1 - T)·k[ℳₙ]`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327. The element `Tₙ^∞` enters
  the period relation (A) of §1; that `Tₙ^∞ (1 - T)` lies in `(1 - T)·ℛₙ` is used in §3.
-/

public section

open MonoidAlgebra Representation
open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

section Semiring

variable [Semiring k]

variable (k) in
/-- Popa–Zagier's element `Tₙ^∞` of the group ring `k[ℳₙ]`: the formal sum of the
upper-triangular representatives `ℳₙ^∞` of `Γ \ ℳₙ`. -/
noncomputable def upperTriangularSum (n : ℤ) : k[TraceFormulaMatrixModule n] :=
  ∑ x ∈ (upperTriangularReps n).toFinite.toFinset, single x 1

/-- The coefficients of `Tₙ^∞` are the indicator function of `ℳₙ^∞`. -/
@[simp]
theorem coeff_upperTriangularSum (x : TraceFormulaMatrixModule n) :
    (upperTriangularSum k n).coeff x = (upperTriangularReps n).indicator 1 x := by
  classical
  simp [upperTriangularSum, Finsupp.single_apply, Set.indicator_apply]

/-- `T₀^∞ = 0`. -/
@[simp]
theorem upperTriangularSum_zero : upperTriangularSum k 0 = 0 := by
  simp [upperTriangularSum]

/-- For `n ≠ 0`, every `SL(2, ℤ)`-orbit sum of the coefficients of `Tₙ^∞` is `1`. -/
@[simp]
theorem mapDomain_coeff_upperTriangularSum_apply (hn : n ≠ 0)
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) :
    (upperTriangularSum k n).coeff.mapDomain (Quotient.mk (MulAction.orbitRel SL(2, ℤ) _)) q =
      1 := by
  rw [← coeff_mapDomainLinearMap (R := k), upperTriangularSum]
  -- `ℳₙ^∞` meets every orbit exactly once
  exact coeff_mapDomainLinearMap_orbitRel_sum_single
    (fun x ↦ (exists_smul_mem_upperTriangularReps hn x).imp fun _ ↦ (Set.Finite.mem_toFinset _).2)
    (by simpa using fun _ hx _ ↦ smul_eq_self_of_mem_upperTriangularReps hx) 1 q

/-- For `n ≠ 0` and `g ∈ PSL(2, ℤ)`, every `SL(2, ℤ)`-orbit sum of the coefficients of the right
translate `Tₙ^∞ · g` is `1`. -/
@[simp]
theorem mapDomain_coeff_ofMulAction_op_upperTriangularSum_apply (hn : n ≠ 0) (g : PSL(2, ℤ))
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) :
    (ofMulAction k PSL(2, ℤ)ᵐᵒᵖ _ (.op g) (upperTriangularSum k n)).coeff.mapDomain
      (Quotient.mk (MulAction.orbitRel SL(2, ℤ) _)) q = 1 := by
  -- right multiplication by `g` commutes with the left action, so permutes the orbits via `e`
  let e := MulAction.orbitRelQuotientCongr (.refl SL(2, ℤ))
    (MulAction.toPerm (MulOpposite.op g) : Equiv.Perm (TraceFormulaMatrixModule n))
    fun γ x ↦ by simpa using (smul_comm γ (MulOpposite.op g) x).symm
  have he : mapDomainLinearMap k k (Quotient.mk (MulAction.orbitRel SL(2, ℤ) _)) ∘ₗ
      ofMulAction k PSL(2, ℤ)ᵐᵒᵖ _ (.op g) =
      mapDomainLinearMap k k e ∘ₗ mapDomainLinearMap k k (Quotient.mk _) := by
    ext x : 2
    simp [e]
  rw [← coeff_mapDomainLinearMap (R := k), ← LinearMap.comp_apply, he, LinearMap.comp_apply,
    coeff_mapDomainLinearMap, Finsupp.mapDomain_equiv_apply, coeff_mapDomainLinearMap,
    mapDomain_coeff_upperTriangularSum_apply hn]

end Semiring

/-- **The right translates of `Tₙ^∞` have the same orbit sums.** For `g ∈ PSL(2, ℤ)`, the element
`Tₙ^∞ (1 - g)` of `k[ℳₙ]` lies in the coinvariant kernel of the left action of `SL(2, ℤ)`. -/
theorem one_sub_ofMulAction_op_upperTriangularSum_mem [CommRing k] (g : PSL(2, ℤ)) :
    (1 - ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (.op g)) (upperTriangularSum k n) ∈
      Coinvariants.ker (ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- `Tₙ^∞` and `Tₙ^∞ · g` have the same orbit sums, all equal to `1`
  simp only [coinvariantsKer_ofMulAction_eq_ker, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.sub_mem_ker_iff]
  ext q
  simp [hn]

open ModularGroup MulOpposite in
/-- **The right translates of `Tₙ^∞` by powers of `T`.** For `j ∈ ℤ`, the element
`Tₙ^∞ (1 - T ^ j)` of `k[ℳₙ]` lies in `(1 - T)·k[ℳₙ]`, the range of left multiplication by
`1 - T`. Popa–Zagier use the case `j = 1` in §3. -/
theorem one_sub_ofMulAction_op_T_zpow_upperTriangularSum_mem_range [CommRing k] (j : ℤ) :
    (1 - ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (op (T : PSL(2, ℤ)) ^ j))
        (upperTriangularSum k n) ∈
      LinearMap.range (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) T) := by
  classical
  -- right multiplication by `T ^ i` keeps matrices upper-triangular, so for `x ∈ ℳₙ^∞` some
  -- `γ i x ∈ ⟨T⟩` moves `x • T ^ i` back into `ℳₙ^∞`
  have key (i : ℤ) : ∀ x ∈ upperTriangularReps n,
      ∃ γ : Subgroup.zpowers T, γ • op (T : PSL(2, ℤ)) ^ i • x ∈ upperTriangularReps n := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_upperTriangularReps.1 hx
    rw [← op_zpow, ← QuotientGroup.mk_zpow, op_smul_mk]
    exact (exists_T_zpow_smul_mk_mem_upperTriangularReps (by rintro rfl; simp at hA)
      (by simp [coe_T_zpow, Matrix.mul_apply, hA.1])).imp'
        (fun m ↦ ⟨T ^ m, Subgroup.zpow_mem_zpowers T m⟩) fun _ ↦ id
  choose! γ hγ using key
  -- as `ℳₙ^∞` meets each orbit at most once, `x ↦ γ i x • x • T ^ i` permutes `ℳₙ^∞`, with
  -- inverse `x ↦ γ (-i) x • x • T ^ (-i)`
  have inv (i i' : ℤ) (hi : i' + i = 0) (x : TraceFormulaMatrixModule n)
      (hx : x ∈ upperTriangularReps n) :
      γ i' (γ i x • op (T : PSL(2, ℤ)) ^ i • x) • op (T : PSL(2, ℤ)) ^ i' •
        γ i x • op (T : PSL(2, ℤ)) ^ i • x = x := by
    have h := hγ i' _ (hγ i x hx)
    simp only [← smul_comm (γ i x), smul_smul, ← zpow_add, hi, zpow_zero, one_smul] at h ⊢
    exact smul_eq_self_of_mem_upperTriangularReps hx h
  -- so `Tₙ^∞` and `Tₙ^∞ T ^ j` have the same `⟨T⟩`-orbit sums
  rw [← neg_sub (ofMulAction k SL(2, ℤ) _ T), LinearMap.range_neg, Module.End.one_eq_id,
    mem_range_ofMulAction_sub_id_iff]
  simp only [upperTriangularSum, map_sum, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    ofMulAction_single, mapDomainLinearMap_single, Finset.sum_sub_distrib, sub_eq_zero]
  refine (Finset.sum_nbij' (fun x ↦ γ j x • op (T : PSL(2, ℤ)) ^ j • x)
    (fun x ↦ γ (-j) x • op (T : PSL(2, ℤ)) ^ (-j) • x) ?_ ?_ ?_ ?_ fun x _ ↦ ?_).symm
  · simpa using hγ j
  · simpa using hγ (-j)
  · simpa using inv j (-j) (neg_add_cancel j)
  · simpa using inv (-j) j (add_neg_cancel j)
  · simp

end TauCeti.TraceFormulaMatrixModule
