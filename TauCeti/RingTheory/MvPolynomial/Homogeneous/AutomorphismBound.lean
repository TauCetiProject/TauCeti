/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Polydisc scaling bounds for homogeneous multivariate polynomials under ring equivalences

If `Q : MvPolynomial ι K` is homogeneous of degree `d` and `σ : K ≃+* L` is a ring equivalence
into a normed field `L`, then any upper bound `‖σ (Q.eval z)‖ ≤ B` on a polydisc
`∀ i, ‖σ (z i)‖ ≤ ρ i` scales by `‖c‖ ^ d` on the dilated polydisc `∀ i, ‖σ (z i)‖ ≤ ‖c‖ * ρ i`
for every nonzero `c : L`, by substituting `z i ↦ σ.symm c⁻¹ * z i` and applying
`MvPolynomial.IsHomogeneous.eval_smul`.

When `L` is a normed `ℝ`-algebra (for instance `L = ℂ` or `L = ℝ`), taking `c = algebraMap ℝ L t`
gives the scaling bound `B * t ^ d` for any real dilation factor `t > 0`.

## Main results

* `TauCeti.norm_map_eval_le_of_isHomogeneous_norm_mul`: polydisc dilation bound by `‖c‖ ^ d` for
  any nonzero `c : L` in a normed field `L`.
* `TauCeti.norm_map_eval_le_of_isHomogeneous`: real dilation bound `B * t ^ d` for `0 < t` when `L`
  is a normed `ℝ`-algebra.
* `TauCeti.norm_eval_le_of_isHomogeneous`: specialization to `σ = RingEquiv.refl L`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/UpperBound/Kernels/DefiniteKernelSize.lean`, declaration
`New.norm_map_eval_le_of_isHomogeneous`. Here the statement is generalized from `ℂ` with uniform
radius `ρ` to any ring equivalence `σ : K ≃+* L` into a normed field `L` and coordinate-dependent
radii `ρ : ι → ℝ`.
-/

public section

namespace TauCeti

/-- **Polydisc scaling bound for homogeneous polynomials under a ring equivalence.** If `Q` is
homogeneous of degree `d` and `‖σ (Q.eval z)‖ ≤ B` whenever `‖σ (z i)‖ ≤ ρ i`, then for any
nonzero `c : L` we have `‖σ (Q.eval z)‖ ≤ B * ‖c‖ ^ d` whenever `‖σ (z i)‖ ≤ ‖c‖ * ρ i`. -/
theorem norm_map_eval_le_of_isHomogeneous_norm_mul {ι K L : Type*} [CommRing K] [NormedField L]
    {Q : MvPolynomial ι K} {d : ℕ} (hQ : Q.IsHomogeneous d) (σ : K ≃+* L) {ρ : ι → ℝ} {B : ℝ}
    (hB : ∀ z : ι → K, (∀ i : ι, ‖σ (z i)‖ ≤ ρ i) → ‖σ (Q.eval z)‖ ≤ B) {c : L} (hc : c ≠ 0)
    {z : ι → K} (hz : ∀ i : ι, ‖σ (z i)‖ ≤ ‖c‖ * ρ i) :
    ‖σ (Q.eval z)‖ ≤ B * ‖c‖ ^ d := by
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let u : K := σ.symm c⁻¹
  have h_eval : Q.eval (fun i ↦ u * z i) = u ^ d * Q.eval z := by
    simpa only [Pi.smul_def, smul_eq_mul] using hQ.eval_smul u z
  have h_scaled : ‖σ (Q.eval fun i ↦ u * z i)‖ ≤ B := by
    refine hB _ fun i ↦ ?_
    rw [map_mul, norm_mul, σ.apply_symm_apply, norm_inv]
    exact (inv_mul_le_iff₀ hc_pos).mpr (hz i)
  rw [h_eval, map_mul, map_pow, norm_mul, norm_pow, σ.apply_symm_apply, norm_inv,
    inv_pow] at h_scaled
  rw [mul_comm B]
  exact (inv_mul_le_iff₀ (pow_pos hc_pos d)).mp h_scaled

/-- **Real polydisc dilation bound for homogeneous polynomials.** For a normed `ℝ`-algebra `L` and
`0 < t`, a bound `‖σ (Q.eval z)‖ ≤ B` on `∀ i, ‖σ (z i)‖ ≤ ρ i` implies `‖σ (Q.eval z)‖ ≤ B * t ^ d`
on `∀ i, ‖σ (z i)‖ ≤ t * ρ i`. -/
theorem norm_map_eval_le_of_isHomogeneous {ι K L : Type*} [CommRing K] [NormedField L]
    [NormedAlgebra ℝ L] {Q : MvPolynomial ι K} {d : ℕ} (hQ : Q.IsHomogeneous d) (σ : K ≃+* L)
    {ρ : ι → ℝ} {B : ℝ}
    (hB : ∀ z : ι → K, (∀ i : ι, ‖σ (z i)‖ ≤ ρ i) → ‖σ (Q.eval z)‖ ≤ B) {t : ℝ} (ht : 0 < t)
    {z : ι → K} (hz : ∀ i : ι, ‖σ (z i)‖ ≤ t * ρ i) :
    ‖σ (Q.eval z)‖ ≤ B * t ^ d := by
  have hc_norm : ‖algebraMap ℝ L t‖ = t := by
    rw [norm_algebraMap', Real.norm_of_nonneg ht.le]
  have hc : algebraMap ℝ L t ≠ 0 := by
    rw [← norm_ne_zero_iff, hc_norm]
    exact ht.ne'
  simpa only [hc_norm] using
    norm_map_eval_le_of_isHomogeneous_norm_mul hQ σ hB hc (by simpa only [hc_norm] using hz)

/-- Specialization of `TauCeti.norm_map_eval_le_of_isHomogeneous` to `σ = RingEquiv.refl L`: a
bound `‖Q.eval z‖ ≤ B` on `∀ i, ‖z i‖ ≤ ρ i` scales to `B * t ^ d` on `∀ i, ‖z i‖ ≤ t * ρ i`. -/
theorem norm_eval_le_of_isHomogeneous {ι L : Type*} [NormedField L] [NormedAlgebra ℝ L]
    {Q : MvPolynomial ι L} {d : ℕ} (hQ : Q.IsHomogeneous d) {ρ : ι → ℝ} {B : ℝ}
    (hB : ∀ z : ι → L, (∀ i : ι, ‖z i‖ ≤ ρ i) → ‖Q.eval z‖ ≤ B) {t : ℝ} (ht : 0 < t)
    {z : ι → L} (hz : ∀ i : ι, ‖z i‖ ≤ t * ρ i) :
    ‖Q.eval z‖ ≤ B * t ^ d :=
  norm_map_eval_le_of_isHomogeneous hQ (RingEquiv.refl L) hB ht hz

end TauCeti
