/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

import TauCeti.Analysis.Normed.Module.Finite.Basic
import TauCeti.FieldTheory.Minpoly.TorsionFree
import TauCeti.RingTheory.Huber.Normed

/-!
# Coefficient bounds for remainders modulo minimal polynomials

Let `B` be a Noetherian integrally closed ultrametric Banach domain over a nontrivially normed
field `K`, and let `A` be a finite torsion-free Banach `B`-algebra with continuous structure map
`B → A`. For any `a : A` with minimal polynomial `p = minpoly B a` of degree `d`, the truncated
evaluation map `(Fin d → B) →ₗ[B] A` is injective into a Noetherian Banach `B`-module, hence
bounded below (`LinearMap.antilipschitz_of_injective_of_isNoetherian`). Consequently there is a
constant `C > 0` such that for every polynomial `q : B[X]`, every coefficient of the remainder
`q %ₘ minpoly B a` has norm at most `C * ‖aeval a q‖`.

## Main results

* `TauCeti.exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval`: linear coefficient bound for
  remainders `q %ₘ minpoly B a` in terms of `‖aeval a q‖`.
-/

public section

open Polynomial

namespace TauCeti

/-- For an element `a` of a finite torsion-free Banach algebra `A` over a Noetherian integrally
closed ultrametric Banach domain `B` (over a nontrivially normed field `K`), there is a constant
`C > 0` such that every coefficient of `q %ₘ minpoly B a` satisfies
`‖(q %ₘ minpoly B a).coeff i‖ ≤ C * ‖aeval a q‖` for all `q : B[X]` and `i : ℕ`. -/
theorem exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval (K : Type*) [NontriviallyNormedField K]
    {B A : Type*} [NormedCommRing B] [IsDomain B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedAlgebra K B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [NormedRing A] [CompleteSpace A] [NormedAlgebra K A]
    [Algebra B A] [IsScalarTower K B A] [Module.Finite B A] [Module.IsTorsionFree B A]
    (hBA : Continuous (algebraMap B A)) (a : A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : B[X]) (i : ℕ),
      ‖(q %ₘ minpoly B a).coeff i‖ ≤ C * ‖aeval a q‖ := by
  have ha_int : IsIntegral B a := Algebra.IsIntegral.isIntegral a
  set p := minpoly B a
  have hp_monic : p.Monic := minpoly.monic ha_int
  rcases subsingleton_or_nontrivial A with _ | _
  · refine ⟨1, zero_lt_one, fun q i ↦ ?_⟩
    simp [p, minpoly.subsingleton, norm_nonneg]
  set d := p.natDegree
  have hd : 0 < d := minpoly.natDegree_pos ha_int
  have hp_ne_one : p ≠ 1 := minpoly.ne_one B a
  have : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
  have : ContinuousSMul B A := continuousSMul_of_algebraMap B A hBA
  let Φ : (Fin d → B) →ₗ[B] A :=
    { toFun := fun c ↦ ∑ i : Fin d, c i • a ^ (i : ℕ)
      map_add' := fun c₁ c₂ ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun b c ↦ by simp [Finset.smul_sum, smul_smul] }
  have hΦ_inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    let q : B[X] := ∑ i : Fin d, C (c i) * X ^ (i : ℕ)
    have hq_aeval : aeval a q = 0 := by
      simpa [q, Φ, map_sum, aeval_C, Algebra.smul_def] using hc
    have hdvd : p ∣ q := TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree ha_int hq_aeval
    have hq0 : q = 0 := by
      by_contra hq_ne
      have hlt : q.natDegree < d := by
        refine (natDegree_sum_le Finset.univ _).trans_lt ?_
        rw [Finset.fold_max_lt]
        refine ⟨hd, fun i _ ↦ ?_⟩
        exact (natDegree_C_mul_X_pow_le (c i) (i : ℕ)).trans_lt i.isLt
      exact hlt.not_ge (Polynomial.natDegree_le_of_dvd hdvd hq_ne)
    ext i
    have hci : q.coeff (i : ℕ) = c i := by
      simp [q, coeff_C_mul, coeff_X_pow, Fin.val_inj]
    rw [Pi.zero_apply, ← hci, hq0, coeff_zero]
  obtain ⟨C, hC⟩ := Φ.antilipschitz_of_injective_of_isNoetherian K hΦ_inj
  refine ⟨(C : ℝ) + 1, by positivity, fun q i ↦ ?_⟩
  set r : B[X] := q %ₘ p
  have hr_deg : r.natDegree < d := natDegree_modByMonic_lt q hp_monic hp_ne_one
  by_cases hi : i < d
  · let c : Fin d → B := fun j ↦ r.coeff j
    have hΦ_c : Φ c = aeval a q := by
      have haeval : aeval a r = aeval a q := minpoly.aeval_modByMonic_minpoly q a
      rw [← haeval, aeval_eq_sum_range' hr_deg, ← Fin.sum_univ_eq_sum_range]
      simp [Φ, c, Algebra.smul_def]
    calc
      ‖r.coeff i‖ ≤ ‖c‖ := norm_le_pi_norm c ⟨i, hi⟩
      _ ≤ (C : ℝ) * ‖Φ c‖ := hC.le_mul_norm (map_zero Φ) c
      _ ≤ ((C : ℝ) + 1) * ‖aeval a q‖ := by
        rw [hΦ_c]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · have hcoeff0 : r.coeff i = 0 := by
      by_cases hr0 : r = 0
      · simp [hr0]
      · exact coeff_eq_zero_of_natDegree_lt (hr_deg.trans_le (not_lt.mp hi))
    rw [hcoeff0, norm_zero]
    positivity

end TauCeti
