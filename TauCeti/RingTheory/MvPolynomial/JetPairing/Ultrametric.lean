/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import TauCeti.RingTheory.MvPolynomial.JetPairing
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Ultrametric bounds on the jet pairing for derivative-stable sets

Let K be a normed commutative ring with an ultrametric distance, and let S be a set of formal
power series over K that is closed under all formal partial derivatives MvPowerSeries.pderiv x
and whose elements have constant term of norm at most C. Then for every polynomial Q over R
and every ring homomorphism φ : R →+* K with ‖φ a‖ ≤ 1 for all , the jet pairing
MvPolynomial.jetPairing (Q.map φ) F has norm at most C for every F ∈ S.

## Main results

* TauCeti.norm_jetPairing_monomial_le_of_pderiv_mem: monomial bound
  ‖jetPairing (monomial d a) F‖ ≤ C when ‖a‖ ≤ 1 (no ultrametric assumption needed).
* TauCeti.norm_jetPairing_map_le_of_pderiv_mem: ultrametric bound ‖jetPairing (Q.map φ) F‖ ≤ C
  for F ∈ S when S is closed under partial derivatives and ‖constantCoeff F‖ ≤ C on S.
* TauCeti.norm_jetPairing_le_of_pderiv_mem: direct bound ‖jetPairing Q F‖ ≤ C for any
  Q : MvPolynomial σ K with ∀ d, ‖Q.coeff d‖ ≤ 1.
* TauCeti.norm_jetPairing_map_le_one_of_pderiv_mem: specialization to C = 1.

## References

* Provenance: adapted from New.norm_jet_le_one_of_pderiv_mem in
  grh/src/New/Derivatives/Vacuum/JetIntegrality.lean of grh-lean
  (https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ K : Type*} [NormedCommRing K]

/-- If S is closed under partial derivatives and ‖constantCoeff F‖ ≤ C for all F ∈ S, then
‖jetPairing (monomial d a) F‖ ≤ C whenever ‖a‖ ≤ 1 and F ∈ S. -/
theorem norm_jetPairing_monomial_le_of_pderiv_mem {S : Set (MvPowerSeries σ K)} {C : ℝ}
    (h_const : ∀ F ∈ S, ‖MvPowerSeries.constantCoeff F‖ ≤ C)
    (h_deriv : ∀ F ∈ S, ∀ x : σ, MvPowerSeries.pderiv x F ∈ S)
    {d : σ →₀ ℕ} {a : K} (ha : ‖a‖ ≤ 1) {F : MvPowerSeries σ K} (hF : F ∈ S) :
    ‖jetPairing (monomial d a) F‖ ≤ C := by
  classical
  induction d using Finsupp.induction generalizing F with
  | zero =>
    rw [monomial_zero', jetPairing_C]
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) ha).trans (h_const F hF))
  | single_add x n e hx hn ihe =>
    clear hx hn
    induction n generalizing F with
    | zero => simpa using ihe hF
    | succ n ihn =>
      have h_eq : monomial (Finsupp.single x (n + 1) + e) a =
          monomial (Finsupp.single x n + e) a * X x := by
        rw [X, monomial_mul_monomial, mul_one, add_right_comm, Finsupp.single_add]
      rw [h_eq, jetPairing_mul_X]
      exact ihn (h_deriv F hF x)

variable [IsUltrametricDist K]

/-- Let S be a set of formal power series over an ultrametric normed commutative ring K that is
closed under all partial derivatives and whose elements have constant term of norm at most C.
If φ : R →+* K satisfies ‖φ a‖ ≤ 1 for all  : R, then ‖jetPairing (Q.map φ) F‖ ≤ C for
every Q : MvPolynomial σ R and every F ∈ S. -/
theorem norm_jetPairing_map_le_of_pderiv_mem {R : Type*} [CommSemiring R]
    {S : Set (MvPowerSeries σ K)} {C : ℝ}
    (h_const : ∀ F ∈ S, ‖MvPowerSeries.constantCoeff F‖ ≤ C)
    (h_deriv : ∀ F ∈ S, ∀ x : σ, MvPowerSeries.pderiv x F ∈ S)
    {φ : R →+* K} (hφ : ∀ a : R, ‖φ a‖ ≤ 1)
    (Q : MvPolynomial σ R) {F : MvPowerSeries σ K} (hF : F ∈ S) :
    ‖jetPairing (Q.map φ) F‖ ≤ C := by
  induction Q using MvPolynomial.induction_on generalizing F with
  | C a =>
    rw [MvPolynomial.map_C, jetPairing_C]
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans (h_const F hF))
  | add Q₁ Q₂ hQ₁ hQ₂ =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hQ₁ hF) (hQ₂ hF))
  | mul_X Q x hQ =>
    rw [map_mul, MvPolynomial.map_X, jetPairing_mul_X]
    exact hQ (h_deriv F hF x)

/-- If S is closed under partial derivatives and ‖constantCoeff F‖ ≤ C for all F ∈ S, then
‖jetPairing Q F‖ ≤ C for every F ∈ S and every polynomial Q : MvPolynomial σ K whose
coefficients all have norm at most 1. -/
theorem norm_jetPairing_le_of_pderiv_mem {S : Set (MvPowerSeries σ K)} {C : ℝ}
    (h_const : ∀ F ∈ S, ‖MvPowerSeries.constantCoeff F‖ ≤ C)
    (h_deriv : ∀ F ∈ S, ∀ x : σ, MvPowerSeries.pderiv x F ∈ S)
    {Q : MvPolynomial σ K} (hQ : ∀ d : σ →₀ ℕ, ‖Q.coeff d‖ ≤ 1)
    {F : MvPowerSeries σ K} (hF : F ∈ S) :
    ‖jetPairing Q F‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (h_const F hF)
  rw [Q.as_sum, map_sum, LinearMap.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun d _ ↦
    norm_jetPairing_monomial_le_of_pderiv_mem h_const h_deriv (hQ d) hF

/-- Specialization of 
orm_jetPairing_map_le_of_pderiv_mem to C = 1. -/
theorem norm_jetPairing_map_le_one_of_pderiv_mem {R : Type*} [CommSemiring R]
    {S : Set (MvPowerSeries σ K)}
    (h_const : ∀ F ∈ S, ‖MvPowerSeries.constantCoeff F‖ ≤ 1)
    (h_deriv : ∀ F ∈ S, ∀ x : σ, MvPowerSeries.pderiv x F ∈ S)
    {φ : R →+* K} (hφ : ∀ a : R, ‖φ a‖ ≤ 1)
    (Q : MvPolynomial σ R) {F : MvPowerSeries σ K} (hF : F ∈ S) :
    ‖jetPairing (Q.map φ) F‖ ≤ 1 :=
  norm_jetPairing_map_le_of_pderiv_mem h_const h_deriv hφ Q hF

end TauCeti
