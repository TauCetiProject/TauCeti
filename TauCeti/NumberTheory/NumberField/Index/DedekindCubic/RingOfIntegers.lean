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
  have hcard : Fintype.card (Fin 3) = finrank ℤ (𝓞 K) := by
    rw [Fintype.card_fin, _root_.NumberField.RingOfIntegers.rank K,
      dedekindCubic_finrank_eq_three hmin hgen]
  have h := (dedekindOrder hrel).toSubmodule.discr_eq_cardQuot_sq_mul_discr
    (c.map (Subalgebra.toSubmoduleEquiv _).symm) hcard
  have hqu : (fun i ↦ algebraMap (𝓞 K) K
      ((c.map (Subalgebra.toSubmoduleEquiv _).symm i : (dedekindOrder hrel).toSubmodule) : 𝓞 K)) =
      ⇑(dedekindCubicFieldBasis hmin hgen) := by
    funext i
    rw [coe_dedekindCubicFieldBasis]
    exact congrArg (algebraMap (𝓞 K) K) (coe_dedekindOrderBasis hmin i)
  have hidx : dedekindOrderIndex hrel = (dedekindOrder hrel).toSubmodule.cardQuot :=
    (dedekindOrderIndex_def hrel).trans (Submodule.cardQuot_apply _).symm
  rw [hqu, discr_dedekindCubicFieldBasis hmin hgen] at h
  rw [hidx]
  exact_mod_cast h

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
