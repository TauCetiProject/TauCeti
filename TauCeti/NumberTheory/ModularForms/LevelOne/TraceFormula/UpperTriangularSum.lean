/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular
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
Popa–Zagier's period relation (A).

## Main definitions

* `TauCeti.TraceFormulaMatrixModule.upperTriangularSum k n`: the element `Tₙ^∞` of `k[ℳₙ]`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.coeff_upperTriangularSum`: `Tₙ^∞` is the indicator function
  of `ℳₙ^∞`.
* `TauCeti.TraceFormulaMatrixModule.upperTriangularSum_zero`: `T₀^∞ = 0`.
* `TauCeti.TraceFormulaMatrixModule.coeff_mapDomainLinearMap_upperTriangularSum`: for `n ≠ 0`,
  every `SL(2, ℤ)`-orbit sum of `Tₙ^∞` is `1`.
* `TauCeti.TraceFormulaMatrixModule.one_sub_ofMulAction_op_upperTriangularSum_mem`:
  `Tₙ^∞ (1 - g)` lies in the coinvariant kernel of the left action of `SL(2, ℤ)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327. The element `Tₙ^∞` enters
  the period relation (A) of §1.
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
theorem coeff_mapDomainLinearMap_upperTriangularSum (hn : n ≠ 0)
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) :
    (mapDomainLinearMap k k (Quotient.mk (MulAction.orbitRel SL(2, ℤ) _))
      (upperTriangularSum k n)).coeff q = 1 := by
  rw [upperTriangularSum]
  -- `ℳₙ^∞` meets every orbit exactly once
  exact coeff_mapDomainLinearMap_orbitRel_sum_single
    (fun x ↦ (exists_smul_mem_upperTriangularReps hn x).imp fun _ ↦ (Set.Finite.mem_toFinset _).2)
    (by simpa using fun _ hx _ ↦ smul_eq_self_of_mem_upperTriangularReps hx) 1 q

/-- For `n ≠ 0` and `g ∈ PSL(2, ℤ)`, every `SL(2, ℤ)`-orbit sum of the coefficients of the right
translate `Tₙ^∞ · g` is `1`. -/
theorem coeff_mapDomainLinearMap_ofMulAction_op_upperTriangularSum (hn : n ≠ 0) (g : PSL(2, ℤ))
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) :
    (mapDomainLinearMap k k (Quotient.mk (MulAction.orbitRel SL(2, ℤ) _))
      (ofMulAction k PSL(2, ℤ)ᵐᵒᵖ _ (.op g) (upperTriangularSum k n))).coeff q = 1 := by
  -- right multiplication by `g` commutes with the left action, so permutes the orbits via `e`
  let e := MulAction.orbitRelQuotientCongr (.refl SL(2, ℤ))
    (MulAction.toPerm (MulOpposite.op g) : Equiv.Perm (TraceFormulaMatrixModule n))
    fun γ x ↦ by simpa using (smul_comm γ (MulOpposite.op g) x).symm
  have he : mapDomainLinearMap k k (Quotient.mk (MulAction.orbitRel SL(2, ℤ) _)) ∘ₗ
      ofMulAction k PSL(2, ℤ)ᵐᵒᵖ _ (.op g) =
      mapDomainLinearMap k k e ∘ₗ mapDomainLinearMap k k (Quotient.mk _) := by
    ext x : 2
    simp [e]
  rw [← LinearMap.comp_apply, he, LinearMap.comp_apply, coeff_mapDomainLinearMap,
    Finsupp.mapDomain_equiv_apply, coeff_mapDomainLinearMap_upperTriangularSum hn]

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
  rw [coeff_mapDomainLinearMap_upperTriangularSum hn,
    coeff_mapDomainLinearMap_ofMulAction_op_upperTriangularSum hn]

end TauCeti.TraceFormulaMatrixModule
