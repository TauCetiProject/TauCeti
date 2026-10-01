/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.DedekindCubic.Index
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import TauCeti.NumberTheory.NumberField.Index.Basic
import TauCeti.NumberTheory.NumberField.Discriminant.OfIntegralBasis
import Mathlib.Tactic.NormNum.Prime

/-!
# The ring of integers of Dedekind's cubic field

Let `θ` be an algebraic integer with minimal polynomial
`X³ - X² - 2X - 8` which generates a number field.  The order with basis
`(1, θ, (θ² - θ) / 2)` is the full ring of integers.  In particular, the displayed basis
is an integral basis, `TauCeti.NumberField.dedekindIntegralBasis`, for computing the field
discriminant and studying the splitting of prime ideals, including the primes above `2` in
Dedekind's classical example.

The result follows Neukirch, *Algebraic Number Theory*, Chapter III, §2, Exercise 1.
-/

public section
noncomputable section

open Polynomial NumberField Module Matrix
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

private noncomputable def dedekindCubicFieldBasis
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Basis (Fin 3) ℚ K := by
  let hrel := dedekindCubic_relation hmin
  let u : Fin 3 → K := fun i ↦
    (![1, θ, dedekindBeta hrel] i : 𝓞 K)
  have hliℤ : LinearIndependent ℤ u := by
    have hli := linearIndependent_dedekindOrder hmin
    apply hli.map' (IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    exact Subtype.ext hxy
  have hliℚ : LinearIndependent ℚ u :=
    hliℤ.localization ℚ (nonZeroDivisors ℤ)
  exact basisOfLinearIndependentOfCardEqFinrank' u hliℚ (by
    rw [dedekindCubic_finrank_eq_three hmin hgen]
    simp)

private theorem coe_dedekindCubicFieldBasis
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (i : Fin 3) :
    dedekindCubicFieldBasis hmin hgen i =
      (![1, θ, dedekindBeta (dedekindCubic_relation hmin)] i : 𝓞 K) := by
  simp [dedekindCubicFieldBasis]

private theorem discr_dedekindCubicFieldBasis
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ (dedekindCubicFieldBasis hmin hgen) = -503 := by
  let b := dedekindCubicFieldBasis hmin hgen
  let hrel := dedekindCubic_relation hmin
  let Mℤ : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ :=
    ![1, !![0, 0, 4; 1, 1, 1; 0, 2, 0], !![0, 4, -2; 0, 1, 2; 1, 0, 1]]
  let M : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := fun i ↦ (Mℤ i).map (algebraMap ℤ ℚ)
  have hmulℤ (i j : Fin 3) :
      (![1, θ, dedekindBeta hrel] i : 𝓞 K) * ![1, θ, dedekindBeta hrel] j =
        ∑ k, (Mℤ i k j) • ![1, θ, dedekindBeta hrel] k := by
    fin_cases i <;> fin_cases j <;>
      simp [Mℤ, Matrix.one_apply, Fin.sum_univ_succ, zsmul_eq_mul, ← pow_two,
        dedekindCubic_theta_sq hrel, dedekindCubic_beta_sq, mul_comm] <;> ring
  have hmul (i j : Fin 3) : b i * b j = b.equivFun.symm (fun k ↦ M i k j) := by
    have h := congrArg (algebraMap (𝓞 K) K) (hmulℤ i j)
    simp only [map_mul, map_sum, map_zsmul] at h
    simpa [Basis.equivFun_symm_apply, b, coe_dedekindCubicFieldBasis, M,
      RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.smul_def, algebraMap_int_eq,
      map_intCast] using h
  have hM (i : Fin 3) : Algebra.leftMulMatrix b (b i) = M i := by
    ext j k
    rw [Algebra.leftMulMatrix_eq_repr_mul, hmul]
    exact congrFun (b.equivFun.apply_symm_apply _) j
  have htrace : Algebra.traceMatrix ℚ b = !![3, 1, 2; 1, 5, 13; 2, 13, -2] := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Algebra.trace_eq_matrix_trace b, map_mul, hM, hM]
    fin_cases i <;> fin_cases j <;>
      norm_num [M, Mℤ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [Algebra.discr_def, htrace]
  norm_num [Matrix.det_fin_three]

/-- The discriminant of Dedekind's order is its squared index times the field discriminant. -/
theorem index_dedekindOrder_sq_mul_discr
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (-503 : ℤ) =
      (dedekindOrderIndex (dedekindCubic_relation hmin) : ℤ) ^ 2 *
        NumberField.discr K := by
  classical
  let hrel := dedekindCubic_relation hmin
  let c := dedekindOrderBasis hmin
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (Fin 3) := by
    rw [Fintype.card_fin, ← finrank_eq_card_chooseBasisIndex,
      _root_.NumberField.RingOfIntegers.rank K, dedekindCubic_finrank_eq_three hmin hgen]
  let b : Basis (Fin 3) ℤ (𝓞 K) :=
    (_root_.NumberField.RingOfIntegers.basis K).reindex (Fintype.equivOfCardEq hcard)
  let u : Fin 3 → 𝓞 K := fun i ↦ c i
  let P : Matrix (Fin 3) (Fin 3) ℤ := b.toMatrix u
  -- `natAbs_det_basis_change` is stated using the basis's alternating determinant,
  -- while the discriminant calculation below uses its coordinate matrix.
  have hdet_toMatrix : P.det = b.det u := by rfl
  have hdet : P.det.natAbs = dedekindOrderIndex hrel := by
    rw [hdet_toMatrix]
    rw [dedekindOrderIndex_def]
    have h := Submodule.natAbs_det_basis_change b (dedekindOrder hrel).toSubmodule
      (c.map (Subalgebra.toSubmoduleEquiv _).symm)
    have hcoe : (Subtype.val ∘ ⇑(c.map (Subalgebra.toSubmoduleEquiv _).symm)) = u := by
      funext i
      simp only [Function.comp_apply, Basis.map_apply, u, c, Subalgebra.toSubmoduleEquiv]
      rw [LinearEquiv.ofEq_symm]
      exact LinearEquiv.coe_ofEq_apply _ _
    rw [hcoe] at h
    exact h
  let q : Basis (Fin 3) ℚ K := dedekindCubicFieldBasis hmin hgen
  let w : Fin 3 → K := fun i ↦ algebraMap (𝓞 K) K (b i)
  have hw_discr : Algebra.discr ℚ w = (NumberField.discr K : ℚ) :=
    _root_.NumberField.discr_eq_of_integralBasis b
  have hv : (fun i ↦ algebraMap (𝓞 K) K (u i)) =
      w ᵥ* (P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K) := by
    have h := b.toMatrix_map_vecMul u
    have hP : b.toMatrix u = P := rfl
    rw [hP] at h
    funext j
    rw [← congrFun h j]
    simp [P, Matrix.vecMul, dotProduct, w, map_sum, algebraMap_int_eq, map_intCast]
  have hdiscr_u : Algebra.discr ℚ (fun i ↦ algebraMap (𝓞 K) K (u i)) =
      ((P.det : ℤ) : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by
    rw [hv, Algebra.discr_of_matrix_vecMul, hw_discr, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, algebraMap_int_eq, eq_intCast]
  have hqu : ⇑q = (fun i ↦ algebraMap (𝓞 K) K (u i)) := by
    funext i
    simp only [q, coe_dedekindCubicFieldBasis, u, c, coe_dedekindOrderBasis]
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_neg, Int.cast_ofNat, ← discr_dedekindCubicFieldBasis hmin hgen, hqu,
    hdiscr_u, ← hdet]
  push_cast
  rw [sq_abs]

/-- Dedekind's cubic order has index one in the full ring of integers. -/
@[simp] theorem dedekindOrderIndex_eq_one
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    dedekindOrderIndex (dedekindCubic_relation hmin) = 1 := by
  have hformula := index_dedekindOrder_sq_mul_discr hmin hgen
  have hsf : Squarefree (-503 : ℤ) := by
    apply Int.squarefree_natAbs.mp
    exact (by norm_num : Nat.Prime 503).squarefree
  have hu : IsUnit (dedekindOrderIndex (dedekindCubic_relation hmin) : ℤ) :=
    hsf _ (by rw [← sq]; exact ⟨_, hformula⟩)
  exact_mod_cast Int.isUnit_iff_natAbs_eq.mp hu

/-- The order with basis `(1, θ, (θ² - θ) / 2)` is the full ring of integers. -/
@[simp] theorem dedekindOrder_eq_ringOfIntegers
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    dedekindOrder (dedekindCubic_relation hmin) = ⊤ :=
  (dedekindOrderIndex_eq_one_iff _).mp (dedekindOrderIndex_eq_one hmin hgen)

/-- The integral basis `(1, θ, (θ² - θ) / 2)` of the full ring of integers of Dedekind's cubic
field. -/
def dedekindIntegralBasis
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Basis (Fin 3) ℤ (𝓞 K) :=
  (dedekindOrderBasis hmin).map
    ((Subalgebra.equivOfEq _ _ (dedekindOrder_eq_ringOfIntegers hmin hgen)).trans
      Subalgebra.topEquiv).toLinearEquiv

/-- The vectors of the integral basis are `1`, `θ`, and `(θ² - θ) / 2`. -/
@[simp] theorem dedekindIntegralBasis_apply
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (i : Fin 3) :
    dedekindIntegralBasis hmin hgen i =
      ![1, θ, dedekindBeta (dedekindCubic_relation hmin)] i := by
  simp [dedekindIntegralBasis]

end TauCeti.NumberField

end
end
