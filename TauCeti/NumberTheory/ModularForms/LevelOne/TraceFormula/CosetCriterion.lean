/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExchangeRelations
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangular.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import TauCeti.LinearAlgebra.End.OrderTwoThree
import TauCeti.NumberTheory.Modular.Relations
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Acyclicity

/-!
# The coset-sum criterion for the period relation

Let `ℛₙ = k[ℳₙ]`, with `ℳₙ` the projective determinant-`n` matrix module and `Γ = PSL(2, ℤ)`
acting on it on both sides. For `ξ ∈ ℛₙ` and a right coset `K = M Γ`, write
`⟨ξ, K⟩ = ∑_{M ∈ K} c_M`. Popa and Zagier's §3 Theorem 2(b) says that a solution `ξ` of the
exchange relations (B) satisfies the period relation

  (A)  `(1 - S) ξ - Tₙ^∞ (1 - S) ∈ (1 - T) ℛₙ`

if and only if `⟨ξ, K⟩ = -1` for every right coset `K`. This is how they deduce (A) for their
explicit element from (B) and its coset identity.

## Proof

Put `X = (1 - S) ξ - Tₙ^∞ (1 - S)`, `U = T S`, and let `S` and `U` also act on the right.

* By the first exchange relation, `ξ (1 + S) = (1 + U + U²) y` for some `y`, and
  `(1 - S) (1 + U + U²) = (1 - T) (-S (1 + U + U²))` in `k[Γ]`, so `X (1 + S) = (1 - T) a` with
  `a = -S (1 + U + U²) y`. Since `ξ (1 + S)` has coset sums `2 ⟨ξ, K⟩`, the coset sums of `a` are
  `⟨a, K⟩ = -2 ⟨ξ, S⁻¹ K⟩`.
* By the second exchange relation `(1 - S) ξ (1 + U + U²) = 0`. On the right,
  `(1 - S) (1 + U + U²) = -(1 - T) S (1 + U + U²)`, and `Tₙ^∞ (1 - T) = (1 - T) ν`, where `ν` is
  the sum of the classes of the matrices `(a b; 0 d)` with `ad = n`, `a > 0` and `0 ≤ b < a`.
  Hence `X (1 + U + U²) = (1 - T) b` with `b = ν S (1 + U + U²)`. The matrices in `ν` represent
  the right cosets, each once, so `⟨b, K⟩ = 3`.
* Left multiplication by `1 - T` is injective on `ℛₙ`, as `⟨T⟩` acts on `ℳₙ` with infinite
  orbits. If `X = (1 - T) m`, then `m (1 + S) = a` and `m (1 + U + U²) = b`, so
  `2 ⟨m, K⟩ = -2 ⟨ξ, S⁻¹ K⟩` and `3 ⟨m, K⟩ = 3`; hence `⟨ξ, K⟩ = -1`.
* Conversely, if `⟨ξ, K⟩ = -1`, then `-a / 2 + b / 3` has vanishing coset sums, so it lies in
  `ℛₙ (S - 1) + ℛₙ (U - 1)`, as `S` and `U` generate `Γ`. This produces `m` with `m (1 + S) = -a`
  and `m (1 + U + U²) = -b`. Then `X + (1 - T) m` is killed by `1 + S` and by `1 + U + U²` on the
  right, so it vanishes by the acyclicity of `ℛₙ` (Popa–Zagier, Lemma 2), and `X = (1 - T) (-m)`.

The matrices of `ν` are the images of the upper-triangular representatives `ℳₙ^∞` under the
anti-involution `(a b; c d) ↦ (d b; c a)`, which exchanges the left and right actions and fixes
`T`. This gives both the identity `Tₙ^∞ (1 - T) = (1 - T) ν` and the coset sums of `ν`.

## Main results

* `ExchangeRelations.periodRelation_iff_mapDomain_orbitRel_mk_coeff_eq_neg_one`: §3 Theorem 2(b),
  for `n > 0` and `2`, `3` invertible in `k`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §3, Lemma 2 and Theorem 2.
-/

public section

open MonoidAlgebra MulAction Representation ModularGroup
open scoped MatrixGroups RightActions

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

local notation "ℳ" => TraceFormulaMatrixModule
local notation "ρL" => ofMulAction k SL(2, ℤ) (ℳ n)
local notation "ρR" => ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (ℳ n)
local notation "qR" => Quotient.mk (orbitRel PSL(2, ℤ)ᵐᵒᵖ (ℳ n))

/-! ### The anti-involution `(a b; c d) ↦ (d b; c a)` -/

/-- The matrix `(d b; c a)` of `(a b; c d)`. -/
private def flipMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

private theorem flipMatrix_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    flipMatrix (A * B) = flipMatrix B * flipMatrix A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem det_flipMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) : (flipMatrix A).det = A.det := by
  simp [flipMatrix, Matrix.det_fin_two]
  ring

private theorem flipMatrix_flipMatrix (A : Matrix (Fin 2) (Fin 2) ℤ) :
    flipMatrix (flipMatrix A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The anti-involution on `SL(2, ℤ)`. -/
private def flipSL (g : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨flipMatrix g, by rw [det_flipMatrix, g.2]⟩

private theorem flipSL_flipSL (g : SL(2, ℤ)) : flipSL (flipSL g) = g :=
  Subtype.ext (flipMatrix_flipMatrix _)

private theorem flipSL_T : flipSL T = T := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The anti-involution on determinant-`n` matrices. -/
private def flipFixedDet (A : TraceFormulaMatrix n) : TraceFormulaMatrix n :=
  ⟨flipMatrix A.1, by rw [det_flipMatrix, A.2]⟩

private theorem val_flipFixedDet (A : TraceFormulaMatrix n) : (flipFixedDet A).1 = flipMatrix A.1 :=
  (rfl)

/-- The anti-involution on `ℳₙ`. -/
private def flip : ℳ n → ℳ n :=
  Quotient.lift (fun A ↦ mk (flipFixedDet A)) fun A B h ↦ by
    rcases h with rfl | rfl
    · rfl
    · refine (congrArg mk (Subtype.ext ?_ : flipFixedDet (-B) = -flipFixedDet B)).trans (mk_neg _)
      rw [TraceFormulaMatrix.val_neg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [flipFixedDet, flipMatrix]

private theorem flip_mk (A : TraceFormulaMatrix n) : flip (mk A) = mk (flipFixedDet A) :=
  lift_mk _ _ A

private theorem flip_flip (x : ℳ n) : flip (flip x) = x := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  rw [flip_mk, flip_mk]
  exact congrArg mk (Subtype.ext (flipMatrix_flipMatrix A.1) : flipFixedDet (flipFixedDet A) = A)

/-- The anti-involution turns left multiplication by `g` into right multiplication by its image. -/
private theorem flip_smul (g : SL(2, ℤ)) (x : ℳ n) :
    flip (g • x) = flip x <• (flipSL g : PSL(2, ℤ)) := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  rw [smul_mk, flip_mk, flip_mk, op_smul_mk]
  refine congrArg mk (Subtype.ext ?_)
  rw [val_traceFormulaMatrixRight, inv_inv]
  simp [flipFixedDet, flipSL, FixedDetMatrices.smul_coe, flipMatrix_mul]

/-! ### The right coset representatives `ν` -/

open scoped Classical in
variable (k n) in
/-- The sum `ν` of the images of `ℳₙ^∞` under the anti-involution: the classes of the matrices
`(a b; 0 d)` with `ad = n`, `a > 0` and `0 ≤ b < a`, which represent the right cosets. -/
private noncomputable def flipSum [Semiring k] : k[ℳ n] :=
  ∑ x ∈ (upperTriangularReps n).toFinite.toFinset.image flip, single x 1

open scoped Classical in
private theorem mem_image_flip_iff {y : ℳ n} :
    y ∈ (upperTriangularReps n).toFinite.toFinset.image flip ↔ flip y ∈ upperTriangularReps n := by
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]
  exact ⟨by rintro ⟨x, hx, rfl⟩; rwa [flip_flip], fun h ↦ ⟨flip y, h, flip_flip y⟩⟩

private theorem coeff_flipSum [Semiring k] (y : ℳ n) :
    (flipSum k n).coeff y = (upperTriangularReps n).indicator 1 (flip y) := by
  classical
  simp [flipSum, Finsupp.single_apply, Set.indicator_apply, ← mem_image_flip_iff]

/-- Every right coset sum of `ν` is `1`. -/
private theorem mapDomain_coeff_flipSum_apply [Semiring k] (hn : n ≠ 0) (x : ℳ n) :
    (flipSum k n).coeff.mapDomain qR ⟦x⟧ = 1 := by
  rw [← coeff_mapDomainLinearMap (R := k), flipSum]
  refine coeff_mapDomainLinearMap_orbitRel_sum_single (fun x ↦ ?_) (fun x hx g hg ↦ ?_) 1 _
  · obtain ⟨g, hg⟩ := exists_smul_mem_upperTriangularReps hn (flip x)
    refine ⟨MulOpposite.op (flipSL g : PSL(2, ℤ)), mem_image_flip_iff.2 ?_⟩
    have h : x <• (flipSL g : PSL(2, ℤ)) = flip (g • flip x) := by rw [flip_smul, flip_flip]
    rwa [h, flip_flip]
  · -- write `g` as right multiplication by the image of some `h`; then `g • x = flip (h • flip x)`
    obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective g.unop
    have key : g • x = flip (flipSL g' • flip x) := by
      rw [flip_smul, flipSL_flipSL, flip_flip, hg', MulOpposite.op_unop]
    rw [mem_image_flip_iff] at hx hg
    rw [key, flip_flip] at hg
    rw [key, smul_eq_self_of_mem_upperTriangularReps hx hg, flip_flip]

/-- **`Tₙ^∞ (1 - T) = (1 - T) ν`**: for `n > 0` the right translate of `Tₙ^∞` by `T` differs from
`Tₙ^∞` by the left multiple of `ν` by `1 - T`. -/
private theorem one_sub_ofMulAction_T_flipSum [CommRing k] (hn : 0 < n) :
    (1 - ρL T) (flipSum k n) =
      (1 - ρR (.op (T : PSL(2, ℤ)))) (upperTriangularSum k n) := by
  classical
  ext x
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = n := by
    simpa [Matrix.det_fin_two] using A.2
  simp only [LinearMap.sub_apply, Module.End.one_apply, coeff_sub, Finsupp.coe_sub, Pi.sub_apply,
    coeff_ofMulAction, coeff_flipSum, coeff_upperTriangularSum, smul_mk, flip_mk,
    ← MulOpposite.op_inv, ← QuotientGroup.mk_inv, op_smul_mk]
  simp only [Set.indicator_apply, mk_mem_upperTriangularReps, Pi.one_apply,
    FixedDetMatrices.reps, Set.mem_ofPred_eq,
    TraceFormulaMatrix.val_neg, val_flipFixedDet, FixedDetMatrices.smul_coe,
    val_traceFormulaMatrixRight, inv_inv, flipMatrix, coe_T_inv, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.neg_apply, zero_mul,
    one_mul, mul_one, mul_zero, add_zero, zero_add, mul_neg, neg_mul, abs_neg]
  generalize A.1 0 0 = a, A.1 0 1 = b, A.1 1 0 = c, A.1 1 1 = d at hdet ⊢
  rcases eq_or_ne c 0 with rfl | hc
  · -- the four indicators are those of `0 ≤ b < a`, `d ≤ b < a + d`, `0 ≤ b < d` and
    -- `a ≤ b < a + d` (up to sign), and `[0, a) + [a, a + d) = [0, d) + [d, a + d)`
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos (show 0 < a * d by linarith) with
      ⟨ha, hd⟩ | ⟨ha, hd⟩ <;>
    simp only [neg_zero, add_zero, zero_add, abs_of_pos, abs_of_neg, ha, hd, abs_lt, true_and] <;>
    split_ifs <;> first | (exfalso; omega) | norm_num
  · simp [hc]

/-! ### Left multiplication by `1 - T` is injective -/

/-- For `n ≠ 0`, the only element of `k[ℳₙ]` fixed by left multiplication by `T` is `0`: the
orbits of `⟨T⟩` on `ℳₙ` are infinite, and elements of `k[ℳₙ]` are finitely supported. -/
private theorem eq_zero_of_ofMulAction_T_eq [Semiring k] (hn : n ≠ 0) {v : k[ℳ n]}
    (hv : ρL T v = v) : v = 0 := by
  have hinv (x : ℳ n) : v.coeff (T⁻¹ • x) = v.coeff x := by
    rw [← coeff_ofMulAction, hv]
  have hzpow (m : ℤ) (x : ℳ n) : v.coeff (T ^ m • x) = v.coeff x := by
    induction m using Int.induction_on generalizing x with
    | zero => simp
    | succ m ih => rw [zpow_add_one, mul_smul, ih, ← hinv, inv_smul_smul]
    | pred m ih => rw [zpow_sub_one, mul_smul, ih, hinv]
  ext x
  by_contra hx
  -- `m ↦ T ^ m • x` is injective, with values in the finite support of `v`
  refine v.coeff.support.finite_toSet.not_infinite (Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ ↦ T ^ m • x) (fun m m' h ↦ ?_) fun m ↦ by simpa [hzpow] using hx)
  have h' : T ^ (m - m') • T ^ m' • x = T ^ m' • x := by
    rw [← mul_smul, ← zpow_add, sub_add_cancel]
    exact h
  rcases eq_one_or_eq_neg_one_of_smul_eq hn h' with h1 | h1
  · have := congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h1
    simp only [coe_T_zpow] at this
    simp at this
    omega
  · have := congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp [coe_T_zpow] at this

/-! ### The two halves of the period defect -/

section CommRing

variable [CommRing k]

/-- Right multiplication by `1 + S` sends coset sums to twice themselves. -/
private theorem mapDomain_coeff_one_add_op_S (v : k[ℳ n]) :
    ((1 + ρR (.op ↑S)) v).coeff.mapDomain qR = 2 • v.coeff.mapDomain qR := by
  rw [LinearMap.add_apply, Module.End.one_apply, coeff_add, Finsupp.mapDomain_add,
    mapDomain_orbitRel_mk_coeff_ofMulAction, two_smul]

/-- Right multiplication by `1 + U + U²` sends coset sums to three times themselves. -/
private theorem mapDomain_coeff_one_add_op_U_add_op_U_sq (v : k[ℳ n]) :
    ((1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 :
      Module.End k k[ℳ n]) v).coeff.mapDomain qR = 3 • v.coeff.mapDomain qR := by
  rw [← map_pow, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, coeff_add,
    coeff_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add,
    mapDomain_orbitRel_mk_coeff_ofMulAction, mapDomain_orbitRel_mk_coeff_ofMulAction]
  module

/-- If `ξ (1 + S) = (1 + U + U²) y`, then right multiplication by `1 + S` sends the period defect
`X = (1 - S) ξ - Tₙ^∞ (1 - S)` to `(1 - T) a` with `a = -S (1 + U + U²) y`. -/
private theorem one_add_op_S_apply_periodDefect {ξ y : k[ℳ n]}
    (hy : (1 + ρL (T * S) + ρL (T * S) ^ 2 : Module.End k k[ℳ n]) y = (1 + ρR (.op ↑S)) ξ) :
    (1 + ρR (.op ↑S)) ((1 - ρL S) ξ - (1 - ρR (.op ↑S)) (upperTriangularSum k n)) =
      (1 - ρL T) (-ρL S ((1 + ρL (T * S) + ρL (T * S) ^ 2 : Module.End k k[ℳ n]) y)) := by
  -- `U S = T` on `k[ℳₙ]`, as `S² = -1` acts trivially
  have hUS : ρL (T * S) * ρL S = ρL T := by
    rw [← map_mul, mul_assoc, show S * S = -1 from Subtype.ext S_mul_S_eq, mul_neg_one,
      ofMulAction_neg]
  -- right multiplication by `1 + S` commutes with left multiplication by `1 - S`
  have h₁ : (1 + ρR (.op ↑S)) ((1 - ρL S) ξ) = (1 - ρL S) ((1 + ρR (.op ↑S)) ξ) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ((Commute.one_left _).sub_left
      ((Commute.one_right _).add_right (commute_ofMulAction (S : SL(2, ℤ)) _))).symm.eq]
  rw [map_sub, h₁, ← Module.End.mul_apply (1 + _), one_add_mul_one_sub_of_sq_eq_one
    ofMulAction_op_S_sq, LinearMap.zero_apply, sub_zero, ← hy, ← Module.End.mul_apply,
    one_sub_mul_one_add_add_sq ofMulAction_S_sq (by simp), hUS]
  simp only [Module.End.mul_apply, LinearMap.neg_apply]

/-- If `(1 - S) ξ (1 + U + U²) = 0`, then right multiplication by `1 + U + U²` sends the period
defect `X = (1 - S) ξ - Tₙ^∞ (1 - S)` to `(1 - T) b` with `b = ν S (1 + U + U²)`. -/
private theorem one_add_op_U_add_op_U_sq_apply_periodDefect (hn : 0 < n) {ξ z : k[ℳ n]}
    (hz : (1 + ρL S) z = (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) +
      ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 : Module.End k k[ℳ n]) ξ) :
    (1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 :
      Module.End k k[ℳ n]) ((1 - ρL S) ξ - (1 - ρR (.op ↑S)) (upperTriangularSum k n)) =
      (1 - ρL T) ((1 + ρR (.op ((T : PSL(2, ℤ)) * S)) + ρR (.op ((T : PSL(2, ℤ)) * S)) ^ 2 :
      Module.End k k[ℳ n]) (ρR (.op ↑S) (flipSum k n))) := by
  set υ' : Module.End k k[ℳ n] := ρR (.op ((T : PSL(2, ℤ)) * S))
  -- `S U = T` on the right, as `S² = 1` in `PSL(2, ℤ)`
  have hSU : ρR (.op ↑S) * υ' = ρR (.op ↑T) := by
    rw [← map_mul, ← MulOpposite.op_mul, mul_assoc, ← sq, TauCeti.ModularGroup.coe_S_sq, mul_one]
  -- right multiplications commute with left multiplications
  have hc (g : SL(2, ℤ)) : Commute (ρL g) (1 + υ' + υ' ^ 2) :=
    ((Commute.one_right _).add_right (commute_ofMulAction _ _)).add_right
      ((commute_ofMulAction _ _).pow_right 2)
  have h₁ : (1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) ((1 - ρL S) ξ) =
      (1 - ρL S) ((1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) ξ) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ((Commute.one_left _).sub_left (hc S)).symm.eq]
  rw [map_sub, h₁, ← hz, ← Module.End.mul_apply (1 - _), one_sub_mul_one_add_of_sq_eq_one
    ofMulAction_S_sq, ← Module.End.mul_apply (1 + υ' + υ' ^ 2), one_add_add_sq_mul_one_sub
    ofMulAction_op_S_sq (by simp [υ']), hSU, LinearMap.zero_apply, zero_sub]
  simp only [LinearMap.neg_apply, neg_neg, Module.End.mul_apply]
  rw [← one_sub_ofMulAction_T_flipSum hn]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, mul_assoc (1 - ρL T),
    ((Commute.one_left _).sub_left ((hc T).mul_right (commute_ofMulAction _ _))).eq]

/-! ### Popa–Zagier's Theorem 2(b) -/

/-- **Popa–Zagier, §3 Theorem 2(b).** For `n > 0` and `2`, `3` invertible in `k`, a solution
`ξ ∈ k[ℳₙ]` of the exchange relations (B) satisfies the period relation (A),
`(1 - S) ξ - Tₙ^∞ (1 - S) ∈ (1 - T) k[ℳₙ]`, if and only if its coefficients sum to `-1` over every
right coset of `PSL(2, ℤ)` in `ℳₙ`: `⟨ξ, K⟩ = -1` for all `K`. -/
theorem ExchangeRelations.periodRelation_iff_mapDomain_orbitRel_mk_coeff_eq_neg_one
    [Invertible (2 : k)] [Invertible (3 : k)] {ξ : k[ℳ n]} (hξ : ExchangeRelations k n ξ)
    (hn : 0 < n) :
    PeriodRelation k n ξ ↔ ∀ x : ℳ n, ξ.coeff.mapDomain qR ⟦x⟧ = -1 := by
  obtain ⟨y, hy⟩ := hξ.one_add_S
  obtain ⟨z, hz⟩ := hξ.one_add_U_add_U_sq
  set σ' : Module.End k k[ℳ n] := ρR (.op ↑S)
  set υ' : Module.End k k[ℳ n] := ρR (.op ((T : PSL(2, ℤ)) * S))
  set τ : Module.End k k[ℳ n] := ρL T
  have hσ' : σ' ^ 2 = 1 := ofMulAction_op_S_sq
  have hυ' : υ' ^ 3 = 1 := by simp [υ']
  -- right multiplications commute with `1 - T`, which is injective
  have hτ (f : Module.End k k[ℳ n]) (hf : Commute τ f) : Commute (1 - τ) f :=
    (Commute.one_left f).sub_left hf
  have hcσ' : Commute (1 - τ) (1 + σ') :=
    hτ _ ((Commute.one_right _).add_right (commute_ofMulAction _ _))
  have hcυ' : Commute (1 - τ) (1 + υ' + υ' ^ 2) := hτ _
    (((Commute.one_right _).add_right (commute_ofMulAction _ _)).add_right
      ((commute_ofMulAction _ _).pow_right 2))
  have hinj (v : k[ℳ n]) (hv : (1 - τ) v = 0) : v = 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact eq_zero_of_ofMulAction_T_eq hn.ne' hv.symm
  -- `X (1 + S) = (1 - T) a` and `X (1 + U + U²) = (1 - T) b` for the period defect `X`
  set X := (1 - ρL S) ξ - (1 - σ') (upperTriangularSum k n)
  obtain ⟨a, ha⟩ : ∃ a, a = -ρL S ((1 + ρL (T * S) + ρL (T * S) ^ 2 : Module.End k k[ℳ n]) y) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) (σ' (flipSum k n)) :=
    ⟨_, rfl⟩
  have hXa : (1 + σ') X = (1 - τ) a := ha ▸ one_add_op_S_apply_periodDefect hy
  have hXb : (1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) X = (1 - τ) b :=
    hb ▸ one_add_op_U_add_op_U_sq_apply_periodDefect hn hz
  -- their coset sums: `⟨a, S K⟩ = -2 ⟨ξ, K⟩` and `⟨b, K⟩ = 3`
  have hca (x : ℳ n) : a.coeff.mapDomain qR ⟦S • x⟧ = -(2 * ξ.coeff.mapDomain qR ⟦x⟧) := by
    have h := congr($(mapDomain_coeff_one_add_op_S (k := k) ξ) ⟦x⟧)
    rw [← hy] at h
    rw [ha, ← coeff_mapDomainLinearMap (R := k), map_neg, coeff_neg, Finsupp.neg_apply,
      coeff_mapDomainLinearMap, mapDomain_orbitRel_mk_coeff_ofMulAction_smul, h,
      Finsupp.smul_apply, two_smul, two_mul]
  have hcb (x : ℳ n) : b.coeff.mapDomain qR ⟦x⟧ = 3 := by
    rw [hb, mapDomain_coeff_one_add_op_U_add_op_U_sq, Finsupp.smul_apply,
      mapDomain_orbitRel_mk_coeff_ofMulAction, mapDomain_coeff_flipSum_apply hn.ne', nsmul_eq_mul,
      Nat.cast_ofNat, mul_one]
  constructor
  · -- if `X = (1 - T) m`, then `m (1 + S) = a` and `m (1 + U + U²) = b`, so `⟨m, K⟩` is both
    -- `-⟨ξ, S⁻¹ K⟩` and `1`
    intro h
    obtain ⟨m, hm⟩ := TraceFormulaMatrixModule.periodRelation_iff.1 h
    have hma : (1 + σ') m = a := sub_eq_zero.1 <| hinj _ <| by
      rw [map_sub, ← Module.End.mul_apply, hcσ'.eq, Module.End.mul_apply, hm, hXa, sub_self]
    have hmb : (1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) m = b := sub_eq_zero.1 <| hinj _ <| by
      rw [map_sub, ← Module.End.mul_apply, hcυ'.eq, Module.End.mul_apply, hm, hXb, sub_self]
    intro x
    have e₁ := congr($(mapDomain_coeff_one_add_op_S (k := k) m) ⟦S • x⟧)
    have e₂ := congr($(mapDomain_coeff_one_add_op_U_add_op_U_sq (k := k) m) ⟦S • x⟧)
    rw [hma, hca, Finsupp.smul_apply, two_smul] at e₁
    rw [hmb, hcb, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at e₂
    have hm1 : m.coeff.mapDomain qR ⟦S • x⟧ = 1 := by
      have := congrArg ((⅟3 : k) * ·) e₂
      simp only [invOf_mul_self, invOf_mul_cancel_left] at this
      exact this.symm
    rw [hm1] at e₁
    linear_combination -(⅟2 : k) * e₁ - (ξ.coeff.mapDomain qR ⟦x⟧ + 1) * invOf_mul_self (2 : k)
  · -- conversely, `m = -a / 2 - (S - 1) u = -b / 3 + (U - 1) v` has `m (1 + S) = -a` and
    -- `m (1 + U + U²) = -b`, so `X + (1 - T) m` is killed by `1 + S` and by `1 + U + U²` on
    -- the right, and vanishes by acyclicity
    intro hc
    have hσ'a : σ' a = a := sub_eq_zero.1 <| hinj _ <| by
      rw [map_sub, ← Module.End.mul_apply, (hτ σ' (commute_ofMulAction _ _)).eq,
        Module.End.mul_apply, ← hXa, ← Module.End.mul_apply,
        show σ' * (1 + σ') = 1 + σ' from by linear_combination (norm := noncomm_ring) hσ',
        sub_self]
    have hυ'b : υ' b = b := by
      rw [hb, ← Module.End.mul_apply,
        show υ' * (1 + υ' + υ' ^ 2) = 1 + υ' + υ' ^ 2 from by
          linear_combination (norm := noncomm_ring) hυ']
    -- `-a / 2 + b / 3` has vanishing coset sums, so it lies in `ℛₙ (S - 1) + ℛₙ (U - 1)`
    have hw : (⅟2 : k) • (-a) - (⅟3 : k) • (-b) ∈ Coinvariants.ker ρR := by
      rw [coinvariantsKer_ofMulAction_eq_ker, LinearMap.mem_ker]
      ext K
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective K
      have hx := hca (S⁻¹ • x)
      rw [smul_inv_smul, hc] at hx
      rw [coeff_mapDomainLinearMap, coeff_sub, coeff_smul, coeff_smul, Finsupp.mapDomain_sub,
        Finsupp.mapDomain_smul, Finsupp.mapDomain_smul, Finsupp.sub_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, ← coeff_mapDomainLinearMap (R := k),
        ← coeff_mapDomainLinearMap (R := k), map_neg, map_neg, coeff_neg, coeff_neg,
        Finsupp.neg_apply, Finsupp.neg_apply, coeff_mapDomainLinearMap, coeff_mapDomainLinearMap,
        hx, hcb, coeff_zero, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul, smul_eq_mul]
      linear_combination (invOf_mul_self (3 : k)) - (invOf_mul_self (2 : k))
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, huv⟩ := Submodule.mem_sup.1 <|
      ((coinvariantsKer_eq_iSup_range _
        TauCeti.ModularGroup.closure_op_coe_S_op_coe_T_mul_coe_S).trans iSup_pair).le hw
    set m := (⅟2 : k) • (-a) - (σ' - LinearMap.id : Module.End k k[ℳ n]) u
    have hm' : m = (⅟3 : k) • (-b) + (υ' - LinearMap.id : Module.End k k[ℳ n]) v := by
      simp only [m]
      linear_combination (norm := module) -huv
    have hma : (1 + σ') m = -a := by
      have h₀ : (1 + σ') * (σ' - LinearMap.id) = 0 := by
        rw [← Module.End.one_eq_id, add_mul, one_mul, mul_sub, mul_one, ← sq, hσ']
        abel
      rw [map_sub, ← Module.End.mul_apply _ (σ' - LinearMap.id), h₀, LinearMap.zero_apply,
        sub_zero, map_smul, LinearMap.add_apply, Module.End.one_apply, map_neg, hσ'a,
        ← two_smul k (-a), smul_smul, invOf_mul_self, one_smul]
    have hmb : (1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) m = -b := by
      have h₀ : (1 + υ' + υ' ^ 2) * (υ' - LinearMap.id) = 0 := by
        rw [← Module.End.one_eq_id, add_mul, add_mul, one_mul, mul_sub, mul_sub, mul_one, mul_one,
          ← sq, ← pow_succ, hυ']
        abel
      have hb2 : (υ' ^ 2) b = b := by rw [sq, Module.End.mul_apply, hυ'b, hυ'b]
      rw [hm', map_add, ← Module.End.mul_apply _ (υ' - LinearMap.id), h₀, LinearMap.zero_apply,
        add_zero, map_smul, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
        map_neg, map_neg, hυ'b, hb2, show -b + -b + -b = (3 : k) • -b by module, smul_smul,
        invOf_mul_self, one_smul]
    have e₁ : (1 + σ') ((1 - τ) m) = (1 - τ) ((1 + σ') m) :=
      LinearMap.congr_fun hcσ'.eq.symm m
    have e₂ : (1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) ((1 - τ) m) =
        (1 - τ) ((1 + υ' + υ' ^ 2 : Module.End k k[ℳ n]) m) :=
      LinearMap.congr_fun hcυ'.eq.symm m
    have hZ : X + (1 - τ) m = 0 := Submodule.disjoint_def.1
      (disjoint_ker_one_add_op_S_ker_one_add_op_T_mul_S_add_sq (k := k) hn.ne') _
      (by rw [LinearMap.mem_ker, map_add, hXa, e₁, hma, map_neg, add_neg_cancel])
      (by rw [LinearMap.mem_ker, map_add, hXb, e₂, hmb, map_neg, add_neg_cancel])
    refine TraceFormulaMatrixModule.periodRelation_iff.2 ⟨-m, ?_⟩
    rw [map_neg, eq_neg_of_add_eq_zero_right hZ, neg_neg]

end CommRing

end TauCeti.TraceFormulaMatrixModule
