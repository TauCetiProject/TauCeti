/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Local persistence of a direction detecting polynomial order

The coefficients of the restriction of a polynomial to an affine line vary continuously
with its base point and direction. On a set of constant finite ambient order, a direction
that detects the order at one point therefore continues to detect it nearby. This is the
uniformity step needed to apply analytic preparation along a parametrized base; it does not
require the base to be smooth or connected.
-/

public section

open Filter Topology

namespace MvPolynomial

variable {σ R : Type*}

section Topology

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Each coefficient of an affine-line restriction depends continuously on its base point
and direction. -/
theorem continuous_coeff_aeval_C_add_C_mul_X (p : MvPolynomial σ R) (m : ℕ) :
    Continuous fun av : (σ → R) × (σ → R) ↦
      (aeval (fun i ↦ Polynomial.C (av.1 i) + Polynomial.C (av.2 i) * Polynomial.X) p).coeff m := by
  induction p using MvPolynomial.induction_on generalizing m with
  | C r =>
    simp only [aeval_C, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact continuous_const
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add]
    fun_prop
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, mul_add, ← mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_mul_C]
    cases m with
    | zero =>
      simp only [Polynomial.coeff_mul_X_zero, add_zero]
      fun_prop
    | succ m =>
      simp only [Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
      fun_prop

/-- On a set of constant finite ambient order, a direction detecting the order at one
point continues to detect it locally, with nonzero line restrictions. -/
theorem eventually_natTrailingDegree_aeval_C_add_C_mul_X_eq (p : MvPolynomial σ R)
    {S : Set (σ → R)} {a : σ → R} {v : σ → R} {m : ℕ}
    [T1Space R] (horder : ∀ x ∈ S, p.orderAt x = m)
    (hv : (aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) p).coeff m ≠ 0) :
    ∀ᶠ x in nhdsWithin a S,
      aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p ≠ 0 ∧
      Polynomial.natTrailingDegree
        (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p) = m := by
  have hc : Continuous fun x : σ → R ↦
      (aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p).coeff m := by
    simpa only [Function.comp_def, id_eq] using
      (continuous_coeff_aeval_C_add_C_mul_X p m).comp
        (continuous_id.prodMk (continuous_const (y := v)))
  have hev := hc.continuousAt.eventually_ne hv
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxS
  have hn : aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p ≠ 0 :=
    fun hzero ↦ hx (by simp [hzero])
  refine ⟨hn, le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hx) ?_⟩
  exact Polynomial.le_natTrailingDegree hn fun k hk ↦
    coeff_aeval_C_add_C_mul_X_eq_zero p x v (by simpa [horder x hxS] using hk)

end Topology

end MvPolynomial
