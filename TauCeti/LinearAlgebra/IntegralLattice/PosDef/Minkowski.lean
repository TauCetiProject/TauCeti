/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum

/-!
# Minkowski's bound for the minimum of a positive definite lattice

Let `L` be a positive definite integral lattice of rank `n`. Minkowski's convex body theorem,
applied to a Euclidean ball around the origin and to a realization of `L` in `ℝⁿ`, bounds the
minimum `min L` (the least norm `B(x, x)` of a nonzero lattice vector) by the determinant:

```text
min L ≤ (4 / π) · Γ(n / 2 + 1) ^ (2 / n) · (det L) ^ (1 / n).
```

Indeed a realization of `L` has covolume `√(det L)`, and the open ball of radius `√(min L)`
contains no nonzero lattice vector, so its volume `π^(n/2) (min L)^(n/2) / Γ(n/2 + 1)` is at most
`2ⁿ √(det L)`. The constant `(4 / π) Γ(n/2 + 1)^(2/n)` is therefore an upper bound for the Hermite
constant `γₙ`; it is the explicit constant of the convex body theorem for the Euclidean ball.

The bound is stated twice: once without real powers, as
`(min L)ⁿ · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`, and once in the root form displayed above. Neither
needs a rank hypothesis: in rank zero the minimum is `0` and both statements hold trivially.

## Main results

* `TauCeti.IntegralLattice.IsPosDef.minimum_pow_mul_pi_pow_le`:
  `(min L)ⁿ · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`.
* `TauCeti.IntegralLattice.IsPosDef.minimum_le_mul_determinant_rpow`:
  `min L ≤ (4 / π) · Γ(n/2 + 1) ^ (2/n) · (det L) ^ (1/n)`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Chapter III, §2, and Chapter X.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.5.
-/

public section

open Module MeasureTheory
open scoped InnerProductSpace

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **Minkowski's bound for the minimum, without roots.** A positive definite integral lattice of
rank `n` satisfies `(min L)ⁿ · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`. -/
theorem IsPosDef.minimum_pow_mul_pi_pow_le (hL : L.IsPosDef) :
    (L.minimum : ℝ) ^ finrank ℤ L * Real.pi ^ finrank ℤ L ≤
      4 ^ finrank ℤ L * Real.Gamma (finrank ℤ L / 2 + 1) ^ 2 * L.determinant := by
  set n := finrank ℤ L
  have hdet₀ : (1 : ℝ) ≤ L.determinant := by exact_mod_cast hL.determinant_pos
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · have hn : n = 0 := finrank_zero_of_subsingleton
    simpa [hn, Real.Gamma_one] using hdet₀
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  obtain ⟨φ, hφ, hspan⟩ := hL.exists_realization
  set E := EuclideanSpace ℝ (Fin n)
  have hE : finrank ℝ E = n := by simp [E]
  have : Nontrivial E := by
    rw [← finrank_pos_iff (R := ℝ), hE]
    exact finrank_pos
  have := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  rw [← covolume_range_sq_eq_determinant hφ hspan]
  set Λ := LinearMap.range φ
  set c := ZLattice.covolume Λ
  have hc : 0 < c := ZLattice.covolume_pos Λ volume
  set Γ := Real.Gamma (n / 2 + 1)
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos (by positivity)
  set m := (L.minimum : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  by_contra! h
  -- Suppose the bound fails. Then the open ball of radius `√(min L)` has volume larger than
  -- `2ⁿ` times the covolume of the realized lattice.
  have hball : 2 ^ n * c < √m ^ n * (√Real.pi ^ n / Γ) := by
    rw [← mul_div_assoc, lt_div_iff₀ hΓ]
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    have hr : (√m ^ n * √Real.pi ^ n) ^ 2 = m ^ n * Real.pi ^ n := by
      calc (√m ^ n * √Real.pi ^ n) ^ 2 = (√m ^ 2) ^ n * (√Real.pi ^ 2) ^ n := by ring
        _ = m ^ n * Real.pi ^ n := by rw [Real.sq_sqrt hm, Real.sq_sqrt Real.pi_pos.le]
    have hl : (2 ^ n * c * Γ) ^ 2 = 4 ^ n * Γ ^ 2 * c ^ 2 := by
      have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
      rw [h4]
      ring
    rw [hr, hl]
    exact h
  let b := Free.chooseBasis ℤ Λ
  have hfund := ZLattice.isAddFundamentalDomain b volume
  have : Countable Λ.toAddSubgroup := (inferInstance : Countable Λ)
  have hvol : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ E <
      volume (Metric.ball (0 : E) √m) := by
    rw [InnerProductSpace.volume_ball, hE, ← ofReal_measureReal
      (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne,
      ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp [ENNReal.ofReal_pow],
      ← ENNReal.ofReal_mul hc.le,
      ENNReal.ofReal_lt_ofReal_iff ((by positivity : (0 : ℝ) ≤ 2 ^ n * c).trans_lt hball)]
    linarith
  -- The convex body theorem then gives a nonzero lattice vector of norm below `min L`.
  obtain ⟨⟨x, ⟨y, rfl⟩⟩, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := Λ.toAddSubgroup) hfund (fun x hx ↦ by simpa using hx) (convex_ball 0 _) hvol
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx0 (by simp)
  have hlt : ‖φ y‖ ^ 2 < m := by
    have : ‖φ y‖ < √m := by simpa using hx
    calc ‖φ y‖ ^ 2 < √m ^ 2 := by gcongr
      _ = m := Real.sq_sqrt hm
  rw [← real_inner_self_eq_norm_sq, hφ, ← integralNorm_apply] at hlt
  have hle := (Int.cast_le (R := ℝ)).mpr (hL.isPosSemidef.minimum_le_integralNorm hy)
  rw [Int.cast_natCast] at hle
  linarith

/-- **Minkowski's bound for the minimum.** A positive definite integral lattice of rank `n`
satisfies `min L ≤ (4 / π) · Γ(n/2 + 1) ^ (2/n) · (det L) ^ (1/n)`. -/
theorem IsPosDef.minimum_le_mul_determinant_rpow (hL : L.IsPosDef) :
    (L.minimum : ℝ) ≤ 4 / Real.pi * Real.Gamma (finrank ℤ L / 2 + 1) ^ (2 / finrank ℤ L : ℝ) *
      (L.determinant : ℝ) ^ (1 / finrank ℤ L : ℝ) := by
  set n := finrank ℤ L
  have hdet : (0 : ℝ) ≤ L.determinant := by exact_mod_cast hL.determinant_pos.le
  have key := hL.minimum_pow_mul_pi_pow_le
  set Γ := Real.Gamma (n / 2 + 1)
  have hΓ : 0 ≤ Γ := (Real.Gamma_pos_of_pos (by positivity)).le
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · rw [minimum_eq_zero_of_subsingleton, Nat.cast_zero]
    positivity
  have hn : n ≠ 0 := finrank_pos.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- The analytic identities: the `n`-th powers of the two real powers.
  have hΓn : (Γ ^ (2 / n : ℝ)) ^ n = Γ ^ 2 := by
    rw [← Real.rpow_mul_natCast hΓ, div_mul_cancel₀ _ hn', Real.rpow_two]
  have hdetn : ((L.determinant : ℝ) ^ (1 / n : ℝ)) ^ n = L.determinant := by
    rw [← Real.rpow_mul_natCast hdet, div_mul_cancel₀ _ hn', Real.rpow_one]
  refine le_of_pow_le_pow_left₀ hn (by positivity) ?_
  rw [mul_pow, mul_pow, div_pow, hΓn, hdetn]
  field_simp
  exact key

end TauCeti.IntegralLattice
