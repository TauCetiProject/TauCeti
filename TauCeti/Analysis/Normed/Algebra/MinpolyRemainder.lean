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
public import TauCeti.RingTheory.Polynomial.DegreeLT

import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Analysis.Normed.Module.Finite.Basic
import TauCeti.FieldTheory.Minpoly.TorsionFree
import TauCeti.RingTheory.Huber.Normed

/-!
# Coefficient bounds for remainders modulo monic polynomials

Let `B` be an ultrametric Banach `K`-algebra over a nontrivially normed field `K`, and let `A` be
a Banach `K`-algebra that is a Noetherian `B`-module with continuous structure map `B → A`.
Whenever `a : A` satisfies a monic polynomial `p : B[X]` whose evaluation map
`Polynomial.degreeLT B p.natDegree →ₗ[B] A` is injective, that evaluation map is bounded below via
`Polynomial.degreeLTEquiv B p.natDegree` and `LinearMap.antilipschitz_of_injective_of_isNoetherian`.
Consequently there is a constant `C > 0` such that for every polynomial `q : B[X]`, every
coefficient of the remainder `q %ₘ p` has norm at most `C * ‖aeval a q‖`.

In particular, when `B` is a Noetherian integrally closed domain and `A` is finite and
torsion-free over `B`, this applies to `p = minpoly B a`.

## Main results

* `TauCeti.exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval_of_aeval_eq_zero_of_injective`:
  linear coefficient bound for remainders `q %ₘ p` in terms of `‖aeval a q‖` for any monic
  polynomial `p` vanishing at `a` with injective evaluation on `degreeLT B p.natDegree`.
* `TauCeti.exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval`: the specialization to
  `p = minpoly B a` for finite torsion-free extensions of Noetherian integrally closed domains.
-/

public section

open Polynomial

namespace TauCeti

/-- If `a` is a root of a monic polynomial `p : B[X]` in a Banach `K`-algebra `A` that is
Noetherian over an ultrametric Banach `K`-algebra `B` (with continuous structure map `B → A`, where
`K` is a nontrivially normed field), and evaluation at `a` is injective on `degreeLT B p.natDegree`,
then there is a constant `C > 0` such that every coefficient of `q %ₘ p` satisfies
`‖(q %ₘ p).coeff i‖ ≤ C * ‖aeval a q‖` for all `q : B[X]` and `i : ℕ`. -/
theorem exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval_of_aeval_eq_zero_of_injective
    (K : Type*) [NontriviallyNormedField K]
    {B A : Type*} [NormedCommRing B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedAlgebra K B] [NormedRing A] [CompleteSpace A] [NormedAlgebra K A]
    [Algebra B A] [IsScalarTower K B A] [IsNoetherian B A]
    (hBA : Continuous (algebraMap B A)) (a : A) {p : B[X]} (hp : p.Monic) (hap : aeval a p = 0)
    (hinj : Function.Injective ((aeval a).toLinearMap.comp (degreeLT B p.natDegree).subtype)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : B[X]) (i : ℕ),
      ‖(q %ₘ p).coeff i‖ ≤ C * ‖aeval a q‖ := by
  rcases subsingleton_or_nontrivial B with _ | _
  · refine ⟨1, zero_lt_one, fun q i ↦ ?_⟩
    rw [Subsingleton.elim (q %ₘ p) 0, coeff_zero, norm_zero]
    positivity
  set d := p.natDegree
  have hp_deg : p.degree = (d : WithBot ℕ) := degree_eq_natDegree hp.ne_zero
  have : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
  have : ContinuousSMul B A := continuousSMul_of_algebraMap B A hBA
  let Φ : (Fin d → B) →ₗ[B] A :=
    ((aeval a).toLinearMap.comp (degreeLT B d).subtype).comp (degreeLTEquiv B d).symm.toLinearMap
  have hΦ_inj : Function.Injective Φ := hinj.comp (degreeLTEquiv B d).symm.injective
  obtain ⟨C, hC⟩ := Φ.antilipschitz_of_injective_of_isNoetherian K hΦ_inj
  refine ⟨(C : ℝ) + 1, by positivity, fun q i ↦ ?_⟩
  set r : B[X] := q %ₘ p
  have hr_lt : r ∈ degreeLT B d :=
    mem_degreeLT.mpr (hp_deg ▸ degree_modByMonic_lt q hp)
  by_cases hi : i < d
  · let c : Fin d → B := degreeLTEquiv B d ⟨r, hr_lt⟩
    have hΦ_c : Φ c = aeval a q := by
      simp only [Φ, c, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]
      have hdiv := congr_arg (aeval a) (Polynomial.modByMonic_add_div q p)
      rwa [map_add, map_mul, hap, zero_mul, add_zero] at hdiv
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
  refine exists_pos_norm_coeff_modByMonic_le_mul_norm_aeval_of_aeval_eq_zero_of_injective
    K hBA a (minpoly.monic ha_int) (minpoly.aeval B a) ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨q, hq⟩ hq0
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero]
  by_contra hq_ne
  have hdvd : minpoly B a ∣ q := TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree ha_int hq0
  have hlt : q.natDegree < (minpoly B a).natDegree :=
    (natDegree_lt_iff_degree_lt hq_ne).mpr (mem_degreeLT.mp hq)
  exact hlt.not_ge (Polynomial.natDegree_le_of_dvd hdvd hq_ne)

end TauCeti
