/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Projectivization

/-!
# Examples of transition probabilities between rays

Concrete values of `Projectivization.rayTransitionProbability`:

* on `ℂ²` the rays of the orthogonal basis vectors `e₀` and `e₁` have transition probability `0`
  (`rayTransitionProbability_single_zero_single_one`);
* on `ℂ²` the rays of `e₀` and `e₀ + e₁` have transition probability `1 / 2`
  (`rayTransitionProbability_single_zero_single_zero_add_single_one`); the representatives
  `2 • e₀` and `I • (e₀ + e₁)` give the same value, as the transition probability only depends on
  the rays;
* on `ℂ` there is a single ray, so every transition probability is `1`
  (`rayTransitionProbability_complex`).
-/

public section

open Complex Projectivization
open scoped InnerProductSpace LinearAlgebra.Projectivization

namespace TauCeti.RayTransitionProbabilityExample

/-- The basis vector `e i` of `ℂ²`. -/
noncomputable abbrev e (i : Fin 2) : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single i 1

theorem e_ne_zero (i : Fin 2) : e i ≠ 0 := by simp [e]

theorem e_zero_add_e_one_ne_zero : e 0 + e 1 ≠ 0 := by
  intro h
  simpa [e] using congr($h 0)

/-- The rays of the orthogonal basis vectors of `ℂ²` have transition probability `0`. -/
theorem rayTransitionProbability_single_zero_single_one :
    (mk ℂ (e 0) (e_ne_zero 0)).rayTransitionProbability (mk ℂ (e 1) (e_ne_zero 1)) = 0 := by
  rw [rayTransitionProbability_mk_eq_zero_iff, EuclideanSpace.inner_single_left]
  simp

/-- The rays of `e₀` and `e₀ + e₁` in `ℂ²` have transition probability `1 / 2`. -/
theorem rayTransitionProbability_single_zero_single_zero_add_single_one :
    (mk ℂ (e 0) (e_ne_zero 0)).rayTransitionProbability
      (mk ℂ (e 0 + e 1) e_zero_add_e_one_ne_zero) = 1 / 2 := by
  rw [rayTransitionProbability_mk, EuclideanSpace.inner_single_left, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_two]

/-- The rescaled representatives `2 • e₀` and `I • (e₀ + e₁)` give the same transition
probability `4 / (4 · 2) = 1 / 2`. -/
theorem rayTransitionProbability_two_smul_single_zero_I_smul :
    (mk ℂ ((2 : ℂ) • e 0) (by simp)).rayTransitionProbability
      (mk ℂ (I • (e 0 + e 1)) (smul_ne_zero I_ne_zero e_zero_add_e_one_ne_zero)) = 1 / 2 := by
  rw [rayTransitionProbability_mk, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_two, inner_smul_left, EuclideanSpace.inner_single_left]

/-- The complex line has a single ray, so every transition probability on it is `1`. -/
theorem rayTransitionProbability_complex (p q : ℙ ℂ ℂ) : p.rayTransitionProbability q = 1 := by
  rw [rayTransitionProbability_eq_one_iff]
  induction p using ind with | h v hv =>
  induction q using ind with | h w hw =>
  exact (mk_eq_mk_iff' ℂ v w hv hw).2 ⟨v / w, by simp [hw]⟩

end TauCeti.RayTransitionProbabilityExample
