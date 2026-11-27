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

import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Analysis.Normed.Module.Finite.Basic
import TauCeti.FieldTheory.Minpoly.TorsionFree
import TauCeti.RingTheory.Huber.Normed

/-!
# Coefficient bounds for remainders modulo minimal polynomials

Let `B` be a Noetherian integrally closed ultrametric Banach domain over a nontrivially normed
field `K`, and let `A` be a Banach `K`-algebra that is finite and torsion-free over `B` with
continuous structure map `B → A`. For any `a : A` with minimal polynomial `p = minpoly B a` of
degree `d`, the evaluation map `Polynomial.degreeLT B d →ₗ[B] A` is injective into a Noetherian
Banach `B`-module, hence bounded below via `Polynomial.degreeLTEquiv B d` and
`LinearMap.antilipschitz_of_injective_of_isNoetherian`. Consequently there is a constant `C > 0`
such that for every polynomial `q : B[X]`, every coefficient of the remainder `q %ₘ minpoly B a` has
norm at most `C * ‖aeval a q‖`.

## Main results

* `TauCeti.exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval`: linear coefficient bound for
  remainders `q %ₘ minpoly B a` in terms of `‖aeval a q‖`.
-/

public section

open Polynomial

namespace TauCeti

private theorem degreeLTEquiv_apply {R : Type*} [Semiring R] (n : ℕ) (p : degreeLT R n)
    (i : Fin n) : degreeLTEquiv R n p i = (p : R[X]).coeff i :=
  (rfl)

/-- For an element `a` of a Banach `K`-algebra `A` that is finite and torsion-free over a Noetherian
integrally closed ultrametric Banach domain `B` (with continuous structure map `B → A`, where `K` is
a nontrivially normed field), there is a constant `C > 0` such that every coefficient of
`q %ₘ minpoly B a` satisfies `‖(q %ₘ minpoly B a).coeff i‖ ≤ C * ‖aeval a q‖` for all
`q : B[X]` and `i : ℕ`. -/
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
  have hp_deg : p.degree = (d : WithBot ℕ) := degree_eq_natDegree hp_monic.ne_zero
  have : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
  have : ContinuousSMul B A := continuousSMul_of_algebraMap B A hBA
  let ev : degreeLT B d →ₗ[B] A := (aeval a).toLinearMap.comp (degreeLT B d).subtype
  have hev_inj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨q, hq⟩ hq0
    rw [Subtype.ext_iff, ZeroMemClass.coe_zero]
    by_contra hq_ne
    have hdvd : p ∣ q := TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree ha_int hq0
    have hlt : q.natDegree < d :=
      (natDegree_lt_iff_degree_lt hq_ne).mpr (mem_degreeLT.mp hq)
    exact hlt.not_ge (Polynomial.natDegree_le_of_dvd hdvd hq_ne)
  let Φ : (Fin d → B) →ₗ[B] A := ev.comp (degreeLTEquiv B d).symm.toLinearMap
  have hΦ_inj : Function.Injective Φ := hev_inj.comp (degreeLTEquiv B d).symm.injective
  obtain ⟨C, hC⟩ := Φ.antilipschitz_of_injective_of_isNoetherian K hΦ_inj
  refine ⟨(C : ℝ) + 1, by positivity, fun q i ↦ ?_⟩
  set r : B[X] := q %ₘ p
  have hr_lt : r ∈ degreeLT B d :=
    mem_degreeLT.mpr (hp_deg ▸ degree_modByMonic_lt q hp_monic)
  by_cases hi : i < d
  · let c : Fin d → B := degreeLTEquiv B d ⟨r, hr_lt⟩
    have hΦ_c : Φ c = aeval a q := by
      change ev ((degreeLTEquiv B d).symm (degreeLTEquiv B d ⟨r, hr_lt⟩)) = aeval a q
      rw [LinearEquiv.symm_apply_apply]
      exact _root_.minpoly.aeval_modByMonic_minpoly q a
    calc
      ‖r.coeff i‖ = ‖c ⟨i, hi⟩‖ := by dsimp only [c]; rw [degreeLTEquiv_apply]
      _ ≤ ‖c‖ := norm_le_pi_norm c ⟨i, hi⟩
      _ ≤ (C : ℝ) * ‖Φ c‖ := hC.le_mul_norm (map_zero Φ) c
      _ ≤ ((C : ℝ) + 1) * ‖aeval a q‖ := by
        rw [hΦ_c]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · have hcoeff0 : r.coeff i = 0 := by
      by_cases hr0 : r = 0
      · simp [hr0]
      · have hr_deg : r.natDegree < d :=
          (natDegree_lt_iff_degree_lt hr0).mpr (mem_degreeLT.mp hr_lt)
        exact coeff_eq_zero_of_natDegree_lt (hr_deg.trans_le (not_lt.mp hi))
    rw [hcoeff0, norm_zero]
    positivity

end TauCeti
