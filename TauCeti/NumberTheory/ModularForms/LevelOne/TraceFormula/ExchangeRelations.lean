/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodRelation
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PermutationModule
import TauCeti.LinearAlgebra.End.OrderTwoThree
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.Modular.Relations
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Acyclicity

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

Solutions of (B) that also satisfy the period relation (A) exist (§1, proved in §3). Let
`𝓘 = (1 + S) ℛₙ + (1 + U + U²) ℛₙ`, the right ideal of §3, eq. (5), and
`𝒜 = {ξ | ξ (1 + S) ∈ 𝓘, ξ (1 + U + U²) ∈ 𝓘}`. For `n ≠ 0`, every solution of (A) lies in `𝒜`,
by the Choie–Zagier criterion (§3, Lemma 1); Lemma 3 then corrects it by an element of `𝓘` to a
solution of both (A) and (B).

## Main definitions and results

* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations`: the exchange relations (B).
* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations.mapDomain_orbitRel_mk_coeff_smul`:
  §3 Theorem 2(a), the right coset sums of a solution of (B) are invariant under left
  multiplication.
* `TauCeti.TraceFormulaMatrixModule.ExchangeRelations.mapDomain_orbitRel_mk_coeff_smul_op_smul`:
  they are constant on every double coset.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.one_add_S_mem_sup`,
  `TauCeti.TraceFormulaMatrixModule.PeriodRelation.one_add_U_add_U_sq_mem_sup`: for `n ≠ 0`,
  every solution of the period relation (A) lies in `𝒜`.
* `TauCeti.TraceFormulaMatrixModule.exists_periodRelation_and_exchangeRelations`: some
  `ξ ∈ ℛₙ` satisfies both (A) and (B).

## Implementation notes

Right multiplication by `g ∈ Γ` on `ℛₙ` is `Representation.ofMulAction k PSL(2, ℤ)ᵐᵒᵖ ℳₙ` at
`MulOpposite.op g`; `U` is written `(T : PSL(2, ℤ)) * S` there. Left multiplication by the class of
`g ∈ SL(2, ℤ)` is `Representation.ofMulAction k SL(2, ℤ) ℳₙ g`, the simp-normal form given by
`TauCeti.TraceFormulaMatrixModule.ofMulAction_coe`.

The right coset `M Γ` is the orbit of `M` under `PSL(2, ℤ)ᵐᵒᵖ`, that is, its class in the
quotient by `MulAction.orbitRel PSL(2, ℤ)ᵐᵒᵖ ℳₙ`. The coset sums `K ↦ ⟨ξ, K⟩` form the finitely
supported function `ξ.coeff.mapDomain (Quotient.mk (MulAction.orbitRel PSL(2, ℤ)ᵐᵒᵖ ℳₙ))`, the
coefficients of the orbit-sum map `MonoidAlgebra.mapDomainLinearMap` in simp-normal form.

Popa and Zagier work over `ℚ`. Theorem 2(a) only needs `2` and `3` to be cancellable in `k`,
which is assumed as `IsSMulRegular k 2` and `IsSMulRegular k 3`; this holds, for instance, if `k`
is torsion-free or if `2` and `3` are invertible in `k`.

The ideal `𝓘` is the sum of the ranges of left multiplication by `1 + S` and by `1 + U + U²`, with
`U` written `T * S` in `SL(2, ℤ)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327: the relations (A) and (B), the
  coset sums `⟨ξ, K⟩` and the existence of solutions of (A) and (B) in §1; the ideal `𝓘`,
  eq. (5), the set `𝒜`, the set `ℬ`, eq. (6), Lemmas 1–3 and Theorem 2(a) in §3.
-/

public section

open MonoidAlgebra MulAction Representation ModularGroup TauCeti.Matrix.SpecialLinearGroup
open scoped MatrixGroups RightActions

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

local notation "ℳ" => TraceFormulaMatrixModule
local notation "ρL" => ofMulAction k SL(2, ℤ) (ℳ n)
local notation "ρR" => ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (ℳ n)

section Semiring

variable [Semiring k]

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
    (h := fun i ↦ MulOpposite.op ((T : PSL(2, ℤ)) * S) ^ i) (by simpa using h3) ?_ x
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
    (h := fun i ↦ MulOpposite.op (S : PSL(2, ℤ)) ^ i) (by simpa using h2) ?_ x
  have hsum : ∑ i ∈ Finset.range 2, ρR (.op (S : PSL(2, ℤ)) ^ i) ξ =
      (1 + ρL (T * S) + ρL (T * S) ^ 2 : Module.End k k[ℳ n]) η := by
    rw [hη]
    simp [Finset.sum_range_succ]
  have hU : ρL (T * S) ^ 3 = 1 := by simp
  rw [hsum, ← Module.End.mul_apply, mul_add, mul_add, mul_one, ← sq, ← pow_succ', hU,
    ← add_rotate]

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

end Semiring

section CommRing

/-! ### Solutions of the period relation and the exchange relations -/

variable [CommRing k]

-- left multiplications commute with right multiplications, hence with the right multiplications
-- by `1 + h` and `1 + h + h²`
private theorem commute_ofMulAction_one_add (g : SL(2, ℤ)) (h : PSL(2, ℤ)) :
    Commute (ρL g) (1 + ρR (.op h)) :=
  (Commute.one_right _).add_right (commute_ofMulAction _ _)

private theorem commute_ofMulAction_one_add_add_sq (g : SL(2, ℤ)) (h : PSL(2, ℤ)) :
    Commute (ρL g) (1 + ρR (.op h) + ρR (.op h) ^ 2) :=
  (commute_ofMulAction_one_add g h).add_right ((commute_ofMulAction _ _).pow_right 2)

-- applying `f` to (A), `(1 - S) f ξ ∈ (1 - T) k[ℳₙ]`, so `f ξ ∈ 𝓘` by the Choie–Zagier criterion
private theorem PeriodRelation.apply_mem_sup [Invertible (2 : k)] [Invertible (3 : k)] (hn : n ≠ 0)
    {ξ : k[ℳ n]} (h : PeriodRelation k n ξ) {f : Module.End k k[ℳ n]}
    (hf : ∀ g, Commute (ρL g) f)
    (hfT : f ((1 - ρR (.op ↑S)) (upperTriangularSum k n)) ∈ LinearMap.range (1 - ρL T)) :
    f ξ ∈ LinearMap.range (1 + ρL S) ⊔ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2) := by
  have hr : LinearMap.range (1 - ρL T) ∈ f.invtSubmodule :=
    Function.Semiconj.mapsTo_range (LinearMap.congr_fun ((Commute.one_left f).sub_left (hf T)).eq)
  rw [← one_sub_S_apply_mem_range_one_sub_T_iff hn, ← Module.End.mul_apply,
    ((Commute.one_left f).sub_left (hf S)).eq, Module.End.mul_apply]
  simpa using add_mem (hr (periodRelation_iff.1 h)) hfT

/-- **Solutions of (A) lie in `𝒜`, the relation for `S`** (Popa–Zagier, §3): for `n ≠ 0` and `2`,
`3` invertible in `k`, if `ξ` satisfies the period relation (A), then
`ξ (1 + S) ∈ (1 + S) k[ℳₙ] + (1 + U + U²) k[ℳₙ]`. -/
theorem PeriodRelation.one_add_S_mem_sup [Invertible (2 : k)] [Invertible (3 : k)] (hn : n ≠ 0)
    {ξ : k[ℳ n]} (h : PeriodRelation k n ξ) :
    (1 + ρR (.op ↑S)) ξ ∈
      LinearMap.range (1 + ρL S) ⊔ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2) :=
  -- on the right, `(1 + S) (1 - S) = 1 - S² = 0`
  h.apply_mem_sup hn (commute_ofMulAction_one_add · _)
    (by rw [← Module.End.mul_apply, one_add_mul_one_sub_of_sq_eq_one ofMulAction_op_S_sq,
      LinearMap.zero_apply]; exact zero_mem _)

/-- **Solutions of (A) lie in `𝒜`, the relation for `U`** (Popa–Zagier, §3): for `n ≠ 0` and `2`,
`3` invertible in `k`, if `ξ` satisfies the period relation (A), then
`ξ (1 + U + U²) ∈ (1 + S) k[ℳₙ] + (1 + U + U²) k[ℳₙ]`. -/
theorem PeriodRelation.one_add_U_add_U_sq_mem_sup [Invertible (2 : k)] [Invertible (3 : k)]
    (hn : n ≠ 0) {ξ : k[ℳ n]} (h : PeriodRelation k n ξ) :
    (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 :
      Module.End k k[ℳ n]) ξ ∈
      LinearMap.range (1 + ρL S) ⊔ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2) := by
  have hc (g : SL(2, ℤ)) : Commute (ρL g) _ := commute_ofMulAction_one_add_add_sq g (↑T * ↑S)
  refine h.apply_mem_sup hn hc ?_
  -- on the right, `(1 + U + U²) (1 - S) = -((1 + U + U²) S) (1 - T)`, as `S U = T`
  rw [← Module.End.mul_apply, one_add_add_sq_mul_one_sub ofMulAction_op_S_sq
    (by simp : ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 3 = 1), ← map_mul, ← MulOpposite.op_mul,
    mul_assoc, ← sq, ModularGroup.coe_S_sq, mul_one, Module.End.mul_apply]
  have hr {f g : Module.End k k[ℳ n]} (h : Commute f g) : LinearMap.range f ∈ g.invtSubmodule :=
    Function.Semiconj.mapsTo_range (LinearMap.congr_fun h.eq)
  refine hr (((Commute.one_left _).sub_left (hc T)).mul_right ((Commute.one_left _).sub_left
    (commute_ofMulAction _ _))).neg_right ?_
  simpa using one_sub_ofMulAction_op_T_zpow_upperTriangularSum_mem_range (k := k) (n := n) 1

variable (k n) in
/-- **Solutions of both (A) and (B) exist** (Popa–Zagier, §1; proved in §3 after Lemma 3): if `2`
and `3` are invertible in `k`, then for every `n` some `ξ ∈ k[ℳₙ]` satisfies both the period
relation (A) and the exchange relations (B). -/
theorem exists_periodRelation_and_exchangeRelations [Invertible (2 : k)] [Invertible (3 : k)] :
    ∃ ξ, PeriodRelation k n ξ ∧ ExchangeRelations k n ξ := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- `T₀^∞ = 0`, so `ξ = 0` is a solution
    exact ⟨0, by simp [periodRelation_iff], by constructor <;> simp⟩
  have hr {f g : Module.End k k[ℳ n]} (h : Commute f g) : LinearMap.range f ∈ g.invtSubmodule :=
    Function.Semiconj.mapsTo_range (LinearMap.congr_fun h.eq)
  -- Lemma 3 corrects `ξ` by some `ι ∈ 𝓘` to a solution of (B); by Lemma 1, `ξ - ι` satisfies (A)
  obtain ⟨ξ, hξ⟩ := exists_periodRelation k n
  obtain ⟨ι, hι, h₁, h₂⟩ := End.exists_mem_sup_one_add_apply_sub_mem ofMulAction_op_S_sq
    (by simp) (hr <| (Commute.one_left _).add_left (commute_ofMulAction_one_add_add_sq _ _))
    (hr <| ((Commute.one_left _).add_left (commute_ofMulAction_one_add _ _)).add_left
      ((commute_ofMulAction_one_add _ _).pow_left 2))
    (hξ.one_add_S_mem_sup hn) (hξ.one_add_U_add_U_sq_mem_sup hn)
  refine ⟨ξ - ι, sub_eq_add_neg ξ ι ▸ hξ.add ?_, h₁, h₂⟩
  exact map_neg (1 - ρL S) ι ▸ neg_mem ((one_sub_S_apply_mem_range_one_sub_T_iff hn).2 hι)

end CommRing

end TauCeti.TraceFormulaMatrixModule
