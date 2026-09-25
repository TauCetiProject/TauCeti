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
`𝒜 = {ξ | ξ (1 + S) ∈ 𝓘, ξ (1 + U + U²) ∈ 𝓘}`. By the Choie–Zagier criterion (§3, Lemma 1),
`ξ ∈ 𝓘` if and only if `(1 - S) ξ ∈ (1 - T) ℛₙ`; the reverse direction uses the acyclicity of
`ℛₙ` (§3, Lemma 2), which holds for `n ≠ 0`. Multiplying (A) on the right by `1 + S` and by
`1 + U + U²` then shows that every solution of (A) lies in `𝒜`. Lemma 3 corrects an element
`ξ ∈ 𝒜` by some `ι ∈ 𝓘` so that `ξ - ι` satisfies (B), and `ξ - ι` still satisfies (A), since
`(1 - S) ι ∈ (1 - T) ℛₙ` by the Choie–Zagier criterion.

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
`U` written `T * S` in `SL(2, ℤ)`: the unnormalised operators replace Popa and Zagier's idempotents
`π_S = (1 + S) / 2` and `π_U = (1 + U + U²) / 3`, which have the same ranges when `2` and `3` are
invertible in `k`, as assumed here. For `n = 0` the existence of solutions of (A) and (B) is
immediate, as `T₀^∞ = 0` and `ξ = 0` is a solution.

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

/-- Popa and Zagier's argument that solutions of (A) lie in `𝒜`: let `g` and `M` be endomorphisms
of `k[ℳₙ]` commuting with the left multiplications by `S` and `T`, such as right multiplications,
with `g (1 - S) = M (1 - T)` on the right. Applying `g` to (A) and using
`Tₙ^∞ (1 - T) ∈ (1 - T) k[ℳₙ]` gives `(1 - S) g ξ ∈ (1 - T) k[ℳₙ]`, hence
`g ξ ∈ (1 + S) k[ℳₙ] + (1 + U + U²) k[ℳₙ]` by the Choie–Zagier criterion. -/
private theorem PeriodRelation.apply_mem_sup [Invertible (2 : k)] [Invertible (3 : k)]
    (hn : n ≠ 0) {ξ : k[ℳ n]} (h : PeriodRelation k n ξ) {g M : Module.End k k[ℳ n]}
    (hS : Commute (ρL S) g) (hT : Commute (ρL T) g) (hM : Commute (ρL T) M)
    (hgM : g * (1 - ρR (.op ↑S)) = M * (1 - ρR (.op ↑T))) :
    g ξ ∈ LinearMap.range (1 + ρL S) ⊔ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2) := by
  rw [← End.one_sub_apply_mem_range_one_sub_mul_iff ofMulAction_S_sq (by simp)
    (disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq hn),
    show ρL (T * S) * ρL S = ρL T by simp [mul_assoc, ← sq]]
  -- `(1 - S) ξ - Tₙ^∞ (1 - S) = (1 - T) y` and `Tₙ^∞ (1 - T) = (1 - T) z`
  obtain ⟨y, hy⟩ := periodRelation_iff.1 h
  obtain ⟨z, hz⟩ := one_sub_ofMulAction_op_T_zpow_upperTriangularSum_mem_range (k := k) (n := n) 1
  rw [zpow_one] at hz
  have hSξ := LinearMap.congr_fun ((Commute.one_left g).sub_left hS).eq ξ
  have hTy := LinearMap.congr_fun ((Commute.one_left g).sub_left hT).eq y
  have hTz := LinearMap.congr_fun ((Commute.one_left M).sub_left hM).eq z
  have hgM' := LinearMap.congr_fun hgM (upperTriangularSum k n)
  simp only [Module.End.mul_apply] at hSξ hTy hTz hgM'
  -- `(1 - T) (g y + M z) = g ((1 - S) ξ - Tₙ^∞ (1 - S)) + g (Tₙ^∞ (1 - S)) = g ((1 - S) ξ)`
  refine ⟨g y + M z, ?_⟩
  rw [map_add, hTy, hTz, hy, hz, map_sub, ← hgM', sub_add_cancel, hSξ]

/-- **Solutions of (A) lie in `𝒜`, the relation for `S`** (Popa–Zagier, §3): for `n ≠ 0` and `2`,
`3` invertible in `k`, if `ξ` satisfies the period relation (A), then
`ξ (1 + S) ∈ (1 + S) k[ℳₙ] + (1 + U + U²) k[ℳₙ]`. -/
theorem PeriodRelation.one_add_S_mem_sup [Invertible (2 : k)] [Invertible (3 : k)] (hn : n ≠ 0)
    {ξ : k[ℳ n]} (h : PeriodRelation k n ξ) :
    (1 + ρR (.op ↑S)) ξ ∈
      LinearMap.range (1 + ρL S) ⊔ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2) := by
  -- on the right, `(1 + S) (1 - S) = 1 - S² = 0`
  refine h.apply_mem_sup hn (M := 0) ((Commute.one_right _).add_right (commute_ofMulAction _ _))
    ((Commute.one_right _).add_right (commute_ofMulAction _ _)) (Commute.zero_right _) ?_
  rw [one_add_mul_one_sub_of_sq_eq_one (by simp [← map_pow, ← MulOpposite.op_pow]), zero_mul]

/-- **Solutions of (A) lie in `𝒜`, the relation for `U`** (Popa–Zagier, §3): for `n ≠ 0` and `2`,
`3` invertible in `k`, if `ξ` satisfies the period relation (A), then
`ξ (1 + U + U²) ∈ (1 + S) k[ℳₙ] + (1 + U + U²) k[ℳₙ]`. -/
theorem PeriodRelation.one_add_U_add_U_sq_mem_sup [Invertible (2 : k)] [Invertible (3 : k)]
    (hn : n ≠ 0) {ξ : k[ℳ n]} (h : PeriodRelation k n ξ) :
    (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 :
      Module.End k k[ℳ n]) ξ ∈
      LinearMap.range (1 + ρL S) ⊔ LinearMap.range (1 + ρL (T * S) + ρL (T * S) ^ 2) := by
  have hc (g : SL(2, ℤ)) :
      Commute (ρL g) (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2) :=
    ((Commute.one_right _).add_right (commute_ofMulAction _ _)).add_right
      ((commute_ofMulAction _ _).pow_right 2)
  -- on the right, `(1 + U + U²) (1 - S) = -((1 + U + U²) S) (1 - T)`, as `S U = T`
  refine h.apply_mem_sup hn (hc S) (hc T)
    ((hc T).mul_right (commute_ofMulAction _ (MulOpposite.op (S : PSL(2, ℤ))))).neg_right ?_
  rw [one_add_add_sq_mul_one_sub (by simp [← map_pow, ← MulOpposite.op_pow])
    (by simp [← map_pow, ← MulOpposite.op_pow, -MulOpposite.op_mul]), ← map_mul,
    ← MulOpposite.op_mul, Matrix.ProjectiveSpecialLinearGroup.mul_coe_S_mul_coe_S]

variable (k n) in
/-- **Solutions of both (A) and (B) exist** (Popa–Zagier, §1; proved in §3 after Lemma 3): if `2`
and `3` are invertible in `k`, then for every `n` some `ξ ∈ k[ℳₙ]` satisfies both the period
relation (A) and the exchange relations (B). -/
theorem exists_periodRelation_and_exchangeRelations [Invertible (2 : k)] [Invertible (3 : k)] :
    ∃ ξ, PeriodRelation k n ξ ∧ ExchangeRelations k n ξ := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- `T₀^∞ = 0`, so `ξ = 0` is a solution
    exact ⟨0, by simp [periodRelation_iff], by constructor <;> simp⟩
  -- a solution `ξ` of (A) lies in `𝒜`, so by Lemma 3 some `ι ∈ 𝓘` has `ξ - ι ∈ ℬ`; by the
  -- Choie–Zagier criterion, `(1 - S) ι ∈ (1 - T) k[ℳₙ]`, so `ξ - ι` still satisfies (A)
  obtain ⟨ξ, hξ⟩ := exists_periodRelation k n
  -- left and right multiplications commute, so the ranges of left multiplications are stable
  -- under right multiplications
  have hP : Commute (1 + ρL S)
      (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2) :=
    (Commute.one_left _).add_left <|
      ((Commute.one_right _).add_right (commute_ofMulAction _ _)).add_right
        ((commute_ofMulAction _ _).pow_right 2)
  have hU : Commute (ρL (T * S)) (1 + ρR (.op ↑S)) :=
    (Commute.one_right _).add_right (commute_ofMulAction _ _)
  have hQ : Commute (1 + ρL (T * S) + ρL (T * S) ^ 2) (1 + ρR (.op ↑S)) :=
    ((Commute.one_left _).add_left hU).add_left (hU.pow_left 2)
  obtain ⟨ι, hι, h₁, h₂⟩ := End.exists_mem_sup_one_add_apply_sub_mem
    (by simp [← map_pow, ← MulOpposite.op_pow])
    (by simp [← map_pow, ← MulOpposite.op_pow, -MulOpposite.op_mul])
    (Function.Semiconj.mapsTo_range (f := ⇑(1 + ρL S)) fun x ↦ LinearMap.congr_fun hP.eq x)
    (Function.Semiconj.mapsTo_range
      (f := ⇑(1 + ρL (T * S) + ρL (T * S) ^ 2 : Module.End k k[ℳ n])) fun x ↦
        LinearMap.congr_fun hQ.eq x)
    (hξ.one_add_S_mem_sup hn) (hξ.one_add_U_add_U_sq_mem_sup hn)
  refine ⟨ξ - ι, ?_, h₁, h₂⟩
  rw [sub_eq_add_neg]
  refine hξ.add ?_
  rw [map_neg, ← show ρL (T * S) * ρL S = ρL T by simp [mul_assoc, ← sq]]
  exact neg_mem (End.one_sub_apply_mem_range_one_sub_mul_of_mem_sup ofMulAction_S_sq (by simp) hι)

end CommRing

end TauCeti.TraceFormulaMatrixModule
