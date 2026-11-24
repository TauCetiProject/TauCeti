/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Euler's product formula for the cosine

For every complex `z`,

`cos (π z) = ∏_{n ≥ 0} (1 - 4 z² / (2 n + 1)²)`,

and the partial products converge locally uniformly on `ℂ` (DLMF, eq. 4.22.2, at the argument
`π z`). The factors vanish exactly at the half-integers `± (2 n + 1) / 2`, the zeros of
`cos (π z)`.

The formula is derived from Mathlib's sine product `Complex.tendsto_euler_sin_prod`,
`sin (π z) = π z ∏_{n ≥ 1} (1 - z² / n²)`, by splitting the factors of the product for
`sin (2 π z)` into odd and even indices: the even ones form the product for `sin (π z)`, so
`sin (2 π z) = 2 sin (π z) cos (π z)` identifies the limit of the odd ones with `cos (π z)` at
every non-integer `z`. The factor deviations `4 z² / (2 n + 1)²` are summable uniformly on compact
sets, so the product converges locally uniformly to a continuous function, which therefore agrees
with `cos (π z)` at the integers too.

## Main results

* `Complex.tendsto_euler_cos_prod`: the partial products tend to `cos (π z)` for every `z`.
* `Complex.hasProd_euler_cos_prod`: the same statement as an unconditional infinite product.
* `Complex.hasProdLocallyUniformly_euler_cos_prod`: the product converges locally uniformly on
  `ℂ`.

## References

* [NIST DLMF, equation 4.22.2](https://dlmf.nist.gov/4.22.E2).
-/

public section

open Filter Finset
open scoped Real Topology

namespace Complex

/-- The factors of the sine product for `sin (2 π z)`, split into odd and even indices: the even
ones form the sine product for `sin (π z)`. -/
private theorem sin_prod_two_mul_eq (z : ℂ) (n : ℕ) :
    π * (2 * z) * ∏ j ∈ range (2 * n), (1 - (2 * z) ^ 2 / ((j : ℂ) + 1) ^ 2) =
      2 * (∏ j ∈ range n, (1 - 4 * z ^ 2 / (2 * (j : ℂ) + 1) ^ 2)) *
        (π * z * ∏ j ∈ range n, (1 - z ^ 2 / ((j : ℂ) + 1) ^ 2)) := by
  induction n with
  | zero => simp only [mul_zero, range_zero, prod_empty]; ring
  | succ n ih =>
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hodd : (1 : ℂ) - (2 * z) ^ 2 / (((2 * n : ℕ) : ℂ) + 1) ^ 2 =
        1 - 4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2 := by push_cast; ring
    have heven : (1 : ℂ) - (2 * z) ^ 2 / (((2 * n + 1 : ℕ) : ℂ) + 1) ^ 2 =
        1 - z ^ 2 / ((n : ℂ) + 1) ^ 2 := by
      rw [show ((2 * n + 1 : ℕ) : ℂ) + 1 = 2 * ((n : ℂ) + 1) by push_cast; ring]
      field_simp
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, prod_range_succ _ (2 * n + 1),
      prod_range_succ _ (2 * n), hodd, heven, prod_range_succ _ n, prod_range_succ _ n]
    linear_combination
      (1 - 4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2) * (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2) * ih

/-- The cosine product at a point where `sin (π z) ≠ 0`, from the sine products for `sin (2 π z)`
and `sin (π z)`. -/
private theorem tendsto_euler_cos_prod_of_sin_ne_zero {z : ℂ} (hz : sin (π * z) ≠ 0) :
    Tendsto (fun n : ℕ ↦ ∏ j ∈ range n, (1 - 4 * z ^ 2 / (2 * (j : ℂ) + 1) ^ 2)) atTop
      (𝓝 (cos (π * z))) := by
  have hS := tendsto_euler_sin_prod z
  have h₂ := (tendsto_euler_sin_prod (2 * z)).comp
    (tendsto_atTop_mono (fun n ↦ Nat.le_mul_of_pos_left n two_pos) tendsto_id :
      Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop)
  have hq := h₂.div (hS.const_mul 2) (mul_ne_zero two_ne_zero hz)
  have hlim : sin (π * (2 * z)) / (2 * sin (π * z)) = cos (π * z) := by
    rw [show (π : ℂ) * (2 * z) = 2 * (π * z) by ring, sin_two_mul]
    field_simp
  rw [hlim] at hq
  refine hq.congr' ?_
  filter_upwards [hS.eventually_ne hz] with n hn
  rw [Pi.div_apply, Function.comp_apply, sin_prod_two_mul_eq,
    div_eq_iff (mul_ne_zero two_ne_zero hn)]
  ring

/-- **Euler's cosine product**, locally uniformly: the partial products of
`∏_{n ≥ 0} (1 - 4 z² / (2 n + 1)²)` converge to `cos (π z)` locally uniformly on `ℂ`. -/
theorem hasProdLocallyUniformly_euler_cos_prod :
    HasProdLocallyUniformly (fun (n : ℕ) (z : ℂ) ↦ 1 - 4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2)
      (fun z ↦ cos (π * z)) := by
  set f : ℕ → ℂ → ℂ := fun n z ↦ 1 - 4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2 with hf
  -- The factor deviations are summable uniformly on every compact set.
  have hloc : HasProdLocallyUniformly f (fun z ↦ ∏' n, f n z) :=
    hasProdLocallyUniformly_of_forall_compact fun K hK ↦ by
      obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
      have hu : Summable fun n : ℕ ↦ 4 * R ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ :=
        (((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)).mul_left
          (4 * R ^ 2)).congr fun n ↦ by push_cast; ring
      have hbound : ∀ᶠ n : ℕ in atTop, ∀ z ∈ K,
          ‖-(4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2)‖ ≤ 4 * R ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
        refine Eventually.of_forall fun n z hz ↦ ?_
        have hnorm : ‖2 * (n : ℂ) + 1‖ = 2 * n + 1 := by exact_mod_cast norm_natCast (2 * n + 1)
        rw [norm_neg, norm_div, norm_mul, norm_pow, norm_pow, hnorm, ← div_eq_mul_inv,
          RCLike.norm_ofNat]
        have hz' : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg z) (hR z hz) 2
        gcongr
        linarith
      have h := Summable.hasProdUniformlyOn_nat_one_add
        (f := fun n z ↦ -(4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2)) hK hu hbound fun n ↦ by fun_prop
      simpa only [← sub_eq_add_neg] using h
  -- The limit is continuous and equals `cos (π z)` off the integers, hence everywhere.
  have hcont : Continuous fun z ↦ ∏' n, f n z :=
    hloc.continuous (Frequently.of_forall fun s ↦ by simp only [hf]; fun_prop)
  have heq : (fun z ↦ ∏' n, f n z) = fun z ↦ cos (π * z) := by
    refine hcont.ext_on ((Set.countable_range ((↑) : ℤ → ℂ)).dense_compl ℝ) (by fun_prop) ?_
    intro z hz
    have hz' : z ∈ integerComplement := mem_integerComplement_iff.mpr (by simpa using hz)
    exact tendsto_nhds_unique hloc.hasProd.tendsto_prod_nat
      (tendsto_euler_cos_prod_of_sin_ne_zero (sin_pi_mul_ne_zero hz'))
  rwa [heq] at hloc

/-- **Euler's cosine product**: for every `z`, the partial products of
`∏_{n ≥ 0} (1 - 4 z² / (2 n + 1)²)` tend to `cos (π z)`. -/
theorem tendsto_euler_cos_prod (z : ℂ) :
    Tendsto (fun n : ℕ ↦ ∏ j ∈ range n, (1 - 4 * z ^ 2 / (2 * (j : ℂ) + 1) ^ 2)) atTop
      (𝓝 (cos (π * z))) :=
  hasProdLocallyUniformly_euler_cos_prod.hasProd.tendsto_prod_nat

/-- **Euler's cosine product** as an unconditional infinite product:
`cos (π z) = ∏_{n ≥ 0} (1 - 4 z² / (2 n + 1)²)` for every `z`. -/
theorem hasProd_euler_cos_prod (z : ℂ) :
    HasProd (fun n : ℕ ↦ 1 - 4 * z ^ 2 / (2 * (n : ℂ) + 1) ^ 2) (cos (π * z)) :=
  hasProdLocallyUniformly_euler_cos_prod.hasProd

end Complex
