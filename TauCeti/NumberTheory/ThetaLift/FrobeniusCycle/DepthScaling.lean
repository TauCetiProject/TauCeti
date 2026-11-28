/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms

import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Depth scaling matrices and Levi commutation on Frobenius cycles

For a Frobenius cycle `T` with square root `T.w` of `T.p` and a split `r ≤ k` of the variables,
the depth scaling matrix `T.depthScaling n r` is the diagonal matrix multiplying each monomial
coefficient `β : Exponent N k n` by `T.w ^ T.depth r β.val`. This file proves that block-diagonal
elements in `leviSubgroup W (twoBlockLabel r)` preserve depth and hence commute with
`T.depthScaling n r`:

* `TauCeti.FrobeniusCycle.depthScaling`: the diagonal matrix `diag (T.w ^ T.depth r β.val)`.
* `TauCeti.FrobeniusCycle.depthScaling_mulVec_apply`: entrywise formula for
  `T.depthScaling n r *ᵥ h`.
* `TauCeti.FrobeniusCycle.letterMatrix_eq_zero_of_mem_leviSubgroup`: letter matrices of elements
  of `leviSubgroup W τ` vanish off the `τ`-blocks.
* `TauCeti.FrobeniusCycle.commute_depthScaling_letterRep`: `T.depthScaling n r` commutes with
  `T.letterRep n g` for every `g ∈ leviSubgroup W (twoBlockLabel r)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/ElementaryDivisors/Edges.lean` (`New.FrobeniusCycle.depthScaling`,
`New.FrobeniusCycle.depthScaling_mulVec_apply`,
`New.FrobeniusCycle.letterMatrix_eq_zero_of_mem_levi`,
`New.FrobeniusCycle.commute_depthScaling_letterRep`).
-/

public section

open MvPolynomial Matrix TauCeti.GeneralLinear

namespace TauCeti.FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k : ℕ}
  (T : FrobeniusCycle W R N)

/-- The diagonal matrix on forms of degree `n` in each letter that multiplies the coefficient at
`β` by `T.w ^ T.depth r β.val`. -/
noncomputable def depthScaling (n r : ℕ) : Matrix (Exponent N k n) (Exponent N k n) R :=
  Matrix.diagonal fun β : Exponent N k n ↦ T.w ^ T.depth r β.val

/-- Entrywise action of `T.depthScaling n r` on a coefficient vector `h`. -/
theorem depthScaling_mulVec_apply {n : ℕ} (r : ℕ) (h : Exponent N k n → R) (β : Exponent N k n) :
    (T.depthScaling n r *ᵥ h) β = T.w ^ T.depth r β.val * h β :=
  Matrix.mulVec_diagonal _ h β

/-- If `g` lies in the Levi subgroup of the labelling `τ`, then `T.letterMatrix s g` vanishes at
`(i, j)` whenever `τ i ≠ τ j`. -/
theorem letterMatrix_eq_zero_of_mem_leviSubgroup {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ leviSubgroup W τ) (s : ZMod N) {i j : Fin k} (hij : τ i ≠ τ j) :
    T.letterMatrix s g i j = 0 := by
  have h_inv : (↑g⁻¹ : Matrix (Fin k) (Fin k) W) j i = 0 :=
    (mem_leviSubgroup_iff τ g⁻¹).mp ((leviSubgroup W τ).inv_mem hg) j i hij.symm
  cases hs : T.isEven s
  · rw [T.letterMatrix_of_not_isEven hs, Matrix.map_apply, Matrix.transpose_apply, h_inv, map_zero]
  · rw [T.letterMatrix_of_isEven hs, Matrix.map_apply,
      (mem_leviSubgroup_iff τ g).mp hg i j hij, map_zero]

/-- Elements of the two-block Levi subgroup `leviSubgroup W (twoBlockLabel r)` preserve depth, so
their representation matrices `T.letterRep n g` commute with `T.depthScaling n r`. -/
theorem commute_depthScaling_letterRep (n r : ℕ) {g : GL (Fin k) W}
    (hg : g ∈ leviSubgroup W (twoBlockLabel r)) :
    Commute (T.depthScaling n r) (T.letterRep n g) := by
  classical
  let wt : Fin k × ZMod N → ℕ := fun x ↦ if T.IsDeep r x then 1 else 0
  have h_var (x : Fin k × ZMod N) :
      (T.twistedAction g (X x)).IsWeightedHomogeneous wt (wt x) := by
    rw [T.twistedAction_X]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ ↦ ?_
    by_cases hblock : twoBlockLabel r b = twoBlockLabel r x.fst
    · have hlt : (b : ℕ) < r ↔ (x.fst : ℕ) < r := by
        rw [← twoBlockLabel_eq_zero_iff, ← twoBlockLabel_eq_zero_iff, hblock]
      have hdeep : T.IsDeep r (b, x.snd) ↔ T.IsDeep r x := by
        simp only [isDeep_iff, not_lt.symm]
        cases T.isEven x.snd <;> simp [hlt]
      have hwt : wt (b, x.snd) = wt x := by simp only [wt, hdeep]
      rw [← hwt, smul_eq_C_mul]
      simpa using
        (isWeightedHomogeneous_C wt (T.letterMatrix x.snd g b x.fst)).mul
          (isWeightedHomogeneous_X R wt (b, x.snd))
    · rw [T.letterMatrix_eq_zero_of_mem_leviSubgroup hg x.snd hblock, zero_smul]
      exact isWeightedHomogeneous_zero _ _ _
  have h_hom (β : Exponent N k n) :
      (T.twistedAction g (monomial β.val 1)).IsWeightedHomogeneous wt (T.depth r β.val) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
    have h_eq : T.depth r β.val = ∑ x ∈ β.val.support, β.val x * wt x := by
      simp [depth_apply, wt, Finsupp.sum]
    rw [h_eq]
    exact IsWeightedHomogeneous.prod β.val.support _ _ fun x _ ↦ by
      simpa [map_pow, mul_comm] using (h_var x).pow (β.val x)
  ext α β
  rw [depthScaling, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h_coeff : T.letterRep n g α β = 0
  · simp [h_coeff]
  · have h_deg : T.depth r α.val = T.depth r β.val := by
      have hne : (T.twistedAction g (monomial β.val 1)).coeff α.val ≠ 0 := by
        rwa [← T.letterRep_apply]
      have hwt := (h_hom β) hne
      simpa [depth_apply, wt, Finsupp.weight_apply, Finsupp.sum] using hwt
    rw [h_deg, mul_comm]

end TauCeti.FrobeniusCycle
