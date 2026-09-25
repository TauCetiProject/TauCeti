/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PermutationModule
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.RepresentationTheory.Coinvariants

/-!
# The exchange relations of Popa and Zagier

Let `ℛₙ = k[ℳₙ]` be the free `k`-module on the projective determinant-`n` matrix module
`ℳₙ = TauCeti.TraceFormulaMatrixModule n`, with the left and right actions of `Γ = PSL(2, ℤ)`.
Write `S = [0, -1; 1, 0]`, `T = [1, 1; 0, 1]` and `U = T S = [1, -1; 1, 0]`, so that
`S² = U³ = 1` in `Γ`. An element `ξ ∈ ℛₙ` satisfies Popa and Zagier's *exchange relations* (B) if

  `ξ (1 + S) ∈ (1 + U + U²) ℛₙ`  and  `ξ (1 + U + U²) ∈ (1 + S) ℛₙ`,

where `ξ γ` and `γ ξ` denote the right and left actions of `γ ∈ k[Γ]` on `ℛₙ`, induced by the
right and left actions of `Γ` on `ℳₙ`. Over `ℚ`, (B) says that `ξ` lies in the set `ℬ` of §3,
eq. (6).

For a right coset `K = M Γ` of a matrix `M ∈ ℳₙ` and `ξ = ∑ c_M M`, let `⟨ξ, K⟩ = ∑_{M ∈ K} c_M`.
Left multiplication by `g ∈ Γ` permutes the right cosets. §3 Theorem 2(a) states that if `ξ`
satisfies (B), then `⟨ξ, g K⟩ = ⟨ξ, K⟩` for every `g ∈ Γ` and every right coset `K`; hence
`⟨ξ, K⟩` is the same for all right cosets `K` in a double coset `Γ M Γ`.

## Main definitions and results

* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations`: the exchange relations (B).
* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations.mapDomain_orbitRel_mk_coeff_smul`:
  §3 Theorem 2(a), the right coset sums of a solution of (B) are invariant under left
  multiplication.
* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations.mapDomain_orbitRel_mk_coeff_smul_op_smul`:
  they are constant on every double coset.

## Implementation notes

Right multiplication by `g ∈ Γ` on `ℛₙ` is `Representation.ofMulAction k PSL(2, ℤ)ᵐᵒᵖ ℳₙ` at
`MulOpposite.op g`; `U` is written `(T : PSL(2, ℤ)) * S` there. Left multiplication by the class of
`g ∈ SL(2, ℤ)` is `Representation.ofMulAction k SL(2, ℤ) ℳₙ g`, the simp-normal form given by
`TauCeti.TraceFormulaMatrixModule.ofMulAction_coe`.

The right coset `M Γ` is the orbit of `M` under `PSL(2, ℤ)ᵐᵒᵖ`, that is, its class in the
quotient by `MulAction.orbitRel PSL(2, ℤ)ᵐᵒᵖ ℳₙ`. The coset sums `K ↦ ⟨ξ, K⟩` form the finitely
supported function `ξ.coeff.mapDomain (Quotient.mk (MulAction.orbitRel PSL(2, ℤ)ᵐᵒᵖ ℳₙ))`, the
coefficients of the orbit-sum map `MonoidAlgebra.mapDomainLinearMap` of
`TauCeti.RepresentationTheory.Coinvariants` in simp-normal form.

Popa and Zagier work over `ℚ`. Theorem 2(a) only needs `2` and `3` to be cancellable in `k`,
which is assumed as `IsSMulRegular k 2` and `IsSMulRegular k 3`; this holds, for instance, if `k`
is torsion-free or if `2` and `3` are invertible in `k`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327: the relations (B) and the
  coset sums `⟨ξ, K⟩` in §1; the set `ℬ`, eq. (6), and Theorem 2(a) in §3.
-/

public section

open MonoidAlgebra MulAction Representation ModularGroup TauCeti.Matrix.SpecialLinearGroup
open scoped MatrixGroups RightActions

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} [Semiring k] {n : ℤ}

local notation "ℳ" => TraceFormulaMatrixModule
local notation "ρL" => ofMulAction k SL(2, ℤ) (ℳ n)
local notation "ρR" => ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (ℳ n)

variable (k n) in
/-- The **exchange relations** (B) of Popa and Zagier for `ξ ∈ k[ℳₙ]`:
`ξ (1 + S) ∈ (1 + U + U²) k[ℳₙ]` and `ξ (1 + U + U²) ∈ (1 + S) k[ℳₙ]`, where `U = T S` and the
products are right multiplication by `1 + S`, `1 + U + U²` and left multiplication by
`1 + U + U²`, `1 + S`. -/
structure ExchangeRelations (ξ : k[ℳ n]) : Prop where
  /-- `ξ (1 + S) ∈ (1 + U + U²) k[ℳₙ]`. -/
  one_add_S : (1 + ρR (.op ↑S)) ξ ∈ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2)
  /-- `ξ (1 + U + U²) ∈ (1 + S) k[ℳₙ]`. -/
  one_add_U_add_U_sq : (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 :
    Module.End k k[ℳ n]) ξ ∈ LinearMap.range (1 + ρL S)

private theorem ExchangeRelations.mapDomain_orbitRel_mk_coeff_S_smul {ξ : k[ℳ n]}
    (hξ : ExchangeRelations k n ξ) (h3 : IsSMulRegular k 3) (x : ℳ n) :
    ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦S • x⟧ =
      ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦x⟧ := by
  -- by the second relation, `ξ (1 + U + U²) = (1 + S) η` is fixed by `S` on the left, as
  -- `S (1 + S) = 1 + S`; right multiplication preserves every right coset, so the right coset
  -- sums of `ξ (1 + U + U²)` are three times those of `ξ`
  obtain ⟨η, hη⟩ := hξ.one_add_U_add_U_sq
  refine mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum (s := Finset.range 3)
    (h := fun i ↦ .op ((T : PSL(2, ℤ)) * S) ^ i) (by simpa using h3) ?_ x
  have hsum : ∑ i ∈ Finset.range 3, ρR (.op ((T : PSL(2, ℤ)) * S) ^ i) ξ = (1 + ρL S) η := by
    simp [Finset.sum_range_succ, hη]
  rw [hsum]
  simp [← Module.End.mul_apply, ← sq, add_comm]

private theorem ExchangeRelations.mapDomain_orbitRel_mk_coeff_T_mul_S_smul {ξ : k[ℳ n]}
    (hξ : ExchangeRelations k n ξ) (h2 : IsSMulRegular k 2) (x : ℳ n) :
    ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦(T * S) • x⟧ =
      ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦x⟧ := by
  -- by the first relation, `ξ (1 + S) = (1 + U + U²) η` is fixed by `U` on the left, as
  -- `U (1 + U + U²) = U + U² + U³ = 1 + U + U²`; right multiplication preserves every right
  -- coset, so the right coset sums of `ξ (1 + S)` are twice those of `ξ`
  obtain ⟨η, hη⟩ := hξ.one_add_S
  refine mapDomain_orbitRel_mk_coeff_smul_of_ofMulAction_sum (s := Finset.range 2)
    (h := fun i ↦ .op (S : PSL(2, ℤ)) ^ i) (by simpa using h2) ?_ x
  have hsum : ∑ i ∈ Finset.range 2, ρR (.op (S : PSL(2, ℤ)) ^ i) ξ =
      (1 + ρL (T * S) + ρL (T * S) ^ 2 : Module.End k k[ℳ n]) η := by
    rw [hη]
    simp [Finset.sum_range_succ]
  rw [hsum, ← Module.End.mul_apply, mul_add, mul_add, mul_one, ← sq, ← pow_succ',
    ofMulAction_T_mul_S_pow_three, ← add_rotate]

/-- **Popa–Zagier, §3 Theorem 2(a).** If `ξ` satisfies the exchange relations (B) and `2`, `3` are
cancellable in `k`, then the right coset sums of `ξ` are invariant under left multiplication:
`⟨ξ, g K⟩ = ⟨ξ, K⟩` for every `g ∈ SL(2, ℤ)` and every right coset `K`. -/
theorem ExchangeRelations.mapDomain_orbitRel_mk_coeff_smul {ξ : k[ℳ n]}
    (hξ : ExchangeRelations k n ξ) (h2 : IsSMulRegular k 2) (h3 : IsSMulRegular k 3) (g : SL(2, ℤ))
    (x : ℳ n) :
    ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦g • x⟧ =
      ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦x⟧ := by
  set f := ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n)))
  -- the elements of `SL(2, ℤ)` under which the right coset sums of `ξ` are invariant
  let P : Subgroup SL(2, ℤ) :=
    { carrier := {g | ∀ x, f ⟦g • x⟧ = f ⟦x⟧}
      mul_mem' := fun {a b} ha hb x ↦ by rw [mul_smul, ha, hb]
      one_mem' := fun x ↦ by rw [one_smul]
      inv_mem' := fun {a} ha x ↦ by simpa using (ha (a⁻¹ • x)).symm }
  -- `P` contains `S` and `U = T S`, which generate `SL(2, ℤ)`
  have hP : Subgroup.closure {S, T * S} ≤ P := (Subgroup.closure_le P).2 <| Set.pair_subset
    (hξ.mapDomain_orbitRel_mk_coeff_S_smul h3) (hξ.mapDomain_orbitRel_mk_coeff_T_mul_S_smul h2)
  exact hP (closure_S_T_mul_S ▸ Subgroup.mem_top g) x

/-- The right coset sums of a solution `ξ` of the exchange relations (B) are constant on every
double coset: `⟨ξ, g M h Γ⟩ = ⟨ξ, M Γ⟩` for `g ∈ SL(2, ℤ)` and `h ∈ PSL(2, ℤ)`, if `2` and `3`
are cancellable in `k`. -/
theorem ExchangeRelations.mapDomain_orbitRel_mk_coeff_smul_op_smul {ξ : k[ℳ n]}
    (hξ : ExchangeRelations k n ξ) (h2 : IsSMulRegular k 2) (h3 : IsSMulRegular k 3) (g : SL(2, ℤ))
    (h : PSL(2, ℤ)) (x : ℳ n) :
    ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦g • x <• h⟧ =
      ξ.coeff.mapDomain (Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))) ⟦x⟧ := by
  -- right multiplication by `h` preserves the right coset of `g • x`
  rw [smul_comm, orbitRel.Quotient.quotient_smul_eq, hξ.mapDomain_orbitRel_mk_coeff_smul h2 h3]

end TauCeti.TraceFormulaMatrixModule
