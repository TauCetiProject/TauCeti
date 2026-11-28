/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Induction for multivariate polynomials killed by mixed second partial derivatives

Let `R` be a commutative `ℚ`-algebra (so every positive natural number acts invertibly), and let
`r : ι → ι → Prop` be a relation on a finite type `ι`. A polynomial `P : MvPolynomial ι R` is
*`r`-harmonic* if `∂_i ∂_j P = 0` whenever `r i j`.

The main theorem `TauCeti.MvPolynomial.mem_of_pderiv_pderiv_eq_zero` proves that an `R`-submodule
`S` of `MvPolynomial ι R` contains every `r`-harmonic polynomial `P` as soon as `1 ∈ S` and
`X j * Q ∈ S` whenever `Q ∈ S` and `∂_i Q = 0` for all `i` with `r i j`. The proof decomposes `P`
into homogeneous components and applies Euler's identity
`n • P = ∑ j, X j * ∂_j P` (`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`) together with the
commutation of `pderiv` and `homogeneousComponent`
(`TauCeti.MvPolynomial.pderiv_homogeneousComponent_succ`).

## Main results

* `TauCeti.MvPolynomial.pderiv_homogeneousComponent_succ`: `∂_j` shifts the `(m + 1)`-st
  homogeneous component to the `m`-th homogeneous component of `∂_j P`.
* `TauCeti.MvPolynomial.pderiv_homogeneousComponent_zero`: `∂_j` kills the degree-0 homogeneous
  component.
* `TauCeti.MvPolynomial.mem_of_pderiv_pderiv_eq_zero`: degree induction via Euler's identity for
  polynomials killed by `∂_i ∂_j` whenever `r i j`.

## Provenance

Adapted from `New.Fock.harmonic_induction` (file `src/Lib/Weil/Fock/OscillatorPair.lean`) in
grh-lean (https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open MvPolynomial

namespace TauCeti.MvPolynomial

variable {ι R : Type*} [CommRing R]

/-- Taking the `j`-th partial derivative of the `(m + 1)`-st homogeneous component gives the `m`-th
homogeneous component of the `j`-th partial derivative. -/
theorem pderiv_homogeneousComponent_succ (j : ι) (m : ℕ) (P : MvPolynomial ι R) :
    pderiv j (homogeneousComponent (m + 1) P) = homogeneousComponent m (pderiv j P) := by
  classical
  ext d
  simp [coeff_pderiv, coeff_homogeneousComponent]

/-- The `j`-th partial derivative of the degree-0 homogeneous component is zero. -/
theorem pderiv_homogeneousComponent_zero (j : ι) (P : MvPolynomial ι R) :
    pderiv j (homogeneousComponent 0 P) = 0 := by
  rw [homogeneousComponent_zero, pderiv_C]

/-- **Harmonic polynomial induction.** Over a commutative `ℚ`-algebra `R`, let `r : ι → ι → Prop`
be a relation on a finite type `ι`. An `R`-submodule `S` of `MvPolynomial ι R` contains every
polynomial `P` satisfying `∂_i (∂_j P) = 0` for all `i, j` with `r i j`, provided `1 ∈ S` and
`X j * Q ∈ S` whenever `Q ∈ S` and `∂_i Q = 0` for all `i` with `r i j`. -/
theorem mem_of_pderiv_pderiv_eq_zero [Finite ι] [Algebra ℚ R] {r : ι → ι → Prop}
    (S : Submodule R (MvPolynomial ι R)) (h_one : 1 ∈ S)
    (h_mul : ∀ j : ι, ∀ Q ∈ S, (∀ i : ι, r i j → pderiv i Q = 0) → X j * Q ∈ S)
    (P : MvPolynomial ι R) (hP : ∀ i j : ι, r i j → pderiv i (pderiv j P) = 0) :
    P ∈ S := by
  cases nonempty_fintype ι
  have h_comp (n : ℕ) : ∀ Q : MvPolynomial ι R,
      (∀ i j : ι, r i j → pderiv i (pderiv j Q) = 0) → homogeneousComponent n Q ∈ S := by
    induction n with
    | zero =>
      intro Q _
      simpa [homogeneousComponent_zero, C_eq_smul_one] using S.smul_mem (Q.coeff 0) h_one
    | succ n ih =>
      intro Q hQ
      have h_euler : ((n + 1 : ℕ) : R) • homogeneousComponent (n + 1) Q =
          ∑ j : ι, X j * homogeneousComponent n (pderiv j Q) := by
        simp [← pderiv_homogeneousComponent_succ,
          (homogeneousComponent_isHomogeneous (n + 1) Q).sum_X_mul_pderiv,
          ← Nat.cast_smul_eq_nsmul R]
      have h_inv : algebraMap ℚ R (((n + 1 : ℕ) : ℚ)⁻¹) •
          (((n + 1 : ℕ) : R) • homogeneousComponent (n + 1) Q) =
          homogeneousComponent (n + 1) Q := by
        rw [smul_smul, ← map_natCast (algebraMap ℚ R), ← map_mul,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), map_one, one_smul]
      rw [← h_inv, h_euler]
      refine S.smul_mem _ (Submodule.sum_mem S fun j _ ↦
        h_mul j _ (ih (pderiv j Q) fun i k hik ↦ ?_) ?_)
      · rw [pderiv_comm k j, pderiv_comm i j, hQ i k hik, map_zero]
      · intro i hij
        cases n with
        | zero => exact pderiv_homogeneousComponent_zero i _
        | succ m => rw [pderiv_homogeneousComponent_succ, hQ i j hij, map_zero]
  rw [← P.sum_homogeneousComponent]
  exact Submodule.sum_mem S fun n _ ↦ h_comp n P hP

end TauCeti.MvPolynomial
