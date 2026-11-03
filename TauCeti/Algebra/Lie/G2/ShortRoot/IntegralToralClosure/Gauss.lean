/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Opposite short-root multiplication in the seven-dimensional G₂ carrier

The short simple-root subgroup has quadratic, rather than linear, matrices. We prove its
rank-one Gauss relation over every commutative ring: when `u = 1 + ab` is a unit,
`x₁(a)x₋₁(b) = x₋₁(b/u) h₁(u) x₁(a/u)`. Here `h₁(u)` is the value of the first coordinate
cocharacter of the weight torus. We also prove uniqueness of the lower–torus–upper parameters.
These identities retain the integral divided-square terms and hence apply in characteristic
three and over nonreduced rings.

The carrier is the integral toral closure of the seven-dimensional module, not an independently
identified pinned simply connected group scheme. The identities transfer to such a group only
along an identification matching the numbered root subgroups and torus.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3, for the rank-one relations.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4, for opposite-root collection.

The matrices and numbering are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.G2ShortRoot.IntegralToralClosure

variable {A : Type v} [CommRing A]

/-- The first coordinate cocharacter acts with weights `1,-1,2,0,-2,1,-1` on the
seven-dimensional short-root module. -/
theorem coe_weightTorusPoints_mulSingle_zero (u : Aˣ) :
    ((weightTorusPoints A (Pi.mulSingle 0 u) : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      Matrix.diagonal ![(u : A), ↑(u⁻¹), (u : A) ^ 2, 1, (↑(u⁻¹) : A) ^ 2, u, ↑(u⁻¹)] := by
  rw [coe_weightTorusPoints_eq_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [torusCharacter_mulSingle, weight_apply, zpow_neg, zpow_ofNat]

/-- **Gauss factorization for the short simple root.** The invertibility assumption is on
`1 + ab`, not on either root parameter. Division is multiplication by the specified unit inverse. -/
theorem rootSubgroupPoints_inl_zero_mul_inr_zero (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd (b * ↑(u⁻¹))) *
        weightTorusPoints A (Pi.mulSingle 0 u) *
        rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd (a * ↑(u⁻¹))) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_rootSubgroupPoints_inl_zero, coe_rootSubgroupPoints_inr_zero,
    coe_weightTorusPoints_mulSingle_zero]
  have hinv : (u : A) * ↑(u⁻¹) = 1 := Units.mul_inv u
  -- After expanding the integral matrices, every entry is a polynomial consequence of
  -- u = 1 + ab and u u⁻¹ = 1, including the middle three-dimensional root string.
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul_diagonal,
      Matrix.cons_val_zero, Matrix.cons_val_succ] <;> grind

/-- A lower–torus–upper expression equals the product of the two opposite short-root points
exactly at the Gauss parameters. In particular the factorization exists only when `1 + ab` is a
unit, and all three factors are uniquely determined. -/
@[simp↓]
theorem rootSubgroupPoints_inl_zero_mul_inr_zero_eq_iff (a b c d : A) (u : Aˣ) :
    rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd c) *
        weightTorusPoints A (Pi.mulSingle 0 u) *
        rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd d) ↔
      (u : A) = 1 + a * b ∧ c = b * ↑(u⁻¹) ∧ d = a * ↑(u⁻¹) := by
  constructor
  · intro h
    -- The entries (0,0), (0,1), (1,0) form the faithful two-dimensional root string.
    have hentries : ![1 + a * b, a, b] = ![(u : A), (u : A) * d, c * (u : A)] := by
      simpa [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        coe_rootSubgroupPoints_inl_zero, coe_rootSubgroupPoints_inr_zero,
        coe_weightTorusPoints_mulSingle_zero, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.one_apply, Matrix.vecMul_diagonal, Matrix.cons_val_zero,
        Matrix.cons_val_succ] using
        congrArg (fun g : points A =>
          let M := ((g : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)
          ![M 0 0, M 0 1, M 1 0]) h
    have h00 : 1 + a * b = (u : A) := congrFun hentries 0
    have h01 : a = (u : A) * d := congrFun hentries 1
    have h10 : b = c * (u : A) := congrFun hentries 2
    have hinv : (u : A) * ↑(u⁻¹) = 1 := Units.mul_inv u
    exact ⟨h00.symm, by grind, by grind⟩
  · rintro ⟨hu, rfl, rfl⟩
    exact rootSubgroupPoints_inl_zero_mul_inr_zero a b u hu

end TauCeti.G2ShortRoot.IntegralToralClosure
