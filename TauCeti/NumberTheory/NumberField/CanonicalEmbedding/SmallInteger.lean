/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# Algebraic integers of prescribed size at the infinite places

Let `K` be a number field of degree `d` and discriminant `D_K`. Minkowski's convex body theorem,
applied to the lattice `𝓞 K` and the box of the mixed space cut out by `‖x w‖ < f w`, produces a
nonzero algebraic integer `a` with `w a < f w` at every infinite place `w` as soon as the volume
`∏ w, f w ^ mult w` of the box, up to the factor `convexBodyLTFactor K`, exceeds the Minkowski
bound of `𝓞 K`. This file fixes the explicit threshold
`TauCeti.NumberField.unitConst K = 2 ^ d · √|D_K|`, which is at least that bound. A box with
`unitConst K ≤ ∏ w, f w ^ mult w` therefore suffices: the strict inequality that Minkowski's
theorem needs comes from `2 ≤ convexBodyLTFactor K`.

The balanced form moves size from all infinite places to one. Given an infinite place `w₀` and a
positive real `t`, it produces a nonzero algebraic integer `a` with `w a · t` bounded at every
`w ≠ w₀` and `w₀ a · t` bounded by a constant times `t ^ (d / mult w₀)`. Multiplying a vector by `a`
therefore turns a bound `t` at every infinite place into a bound at `w₀` alone, while keeping the
vector in every `𝓞 K`-module it belonged to. This is how Evertse and Schlickewei concentrate the
successive minima of a parallelepiped at one infinite place.

## Main results

* `TauCeti.NumberField.unitConst`: the threshold `2 ^ d · √|D_K|`, with `2 ≤ unitConst K` and
  `unitConst ℚ = 2`.
* `TauCeti.NumberField.minkowskiBound_one_le_ofReal_unitConst`: the Minkowski bound of `𝓞 K` is at
  most `unitConst K`.
* `TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_lt`: if `f ≥ 0` and
  `unitConst K ≤ ∏ w, f w ^ mult w`, some nonzero `a : 𝓞 K` has `w a < f w` at every infinite
  place `w`.
* `TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_mul_le`: the balanced form at one
  infinite place `w₀`.

## References

* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  J. reine angew. Math. 548 (2002), 21–127, §9.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Appendix C.2.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal NNReal

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **The Minkowski threshold for one algebraic integer**: `2 ^ [K : ℚ] · √|D_K|`. A box of the
mixed space whose nonnegative radii `f w` have `∏ w, f w ^ mult w` at least this value holds a
nonzero algebraic integer (`TauCeti.NumberField.exists_ne_zero_forall_infinitePlace_lt`). -/
noncomputable def unitConst : ℝ :=
  2 ^ finrank ℚ K * √|(discr K : ℝ)|

/-- `unitConst K` unfolded. -/
theorem unitConst_def : unitConst K = 2 ^ finrank ℚ K * √|(discr K : ℝ)| := (rfl)

/-- `unitConst K` is positive, since the discriminant of a number field is nonzero. -/
theorem unitConst_pos : 0 < unitConst K := by
  have : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  rw [unitConst_def]
  positivity

/-- `unitConst K` is at least `2`, since `[K : ℚ] ≥ 1` and `|D_K| ≥ 1`. -/
theorem two_le_unitConst : 2 ≤ unitConst K := by
  have hd : 2 ≤ (2 : ℝ) ^ finrank ℚ K := le_self_pow₀ one_le_two finrank_pos.ne'
  have hD : 1 ≤ √|(discr K : ℝ)| :=
    Real.one_le_sqrt.2 (by exact_mod_cast Int.one_le_abs (discr_ne_zero K))
  rw [unitConst_def]
  nlinarith

/-- `unitConst K` is at least `1`. -/
theorem one_le_unitConst : 1 ≤ unitConst K :=
  one_le_two.trans (two_le_unitConst K)

/-- The threshold of `ℚ` is `2`, since `[ℚ : ℚ] = 1` and `D_ℚ = 1`. -/
@[simp]
theorem unitConst_rat : unitConst ℚ = 2 := by
  simp [unitConst_def]

/-- The Minkowski bound of `𝓞 K` is at most `unitConst K`. -/
theorem minkowskiBound_one_le_ofReal_unitConst :
    minkowskiBound K ↑1 ≤ ENNReal.ofReal (unitConst K) := by
  classical
  -- The Minkowski bound is `2⁻¹ ^ r₂ · √|D_K| · 2 ^ d`, and `2⁻¹ ^ r₂ ≤ 1`.
  have hmb : minkowskiBound K ↑1 =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * NNReal.sqrt ‖discr K‖₊ * 2 ^ finrank ℚ K := by
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, mixedEmbedding.finrank]
    simp
  have hu : ENNReal.ofReal (unitConst K) = NNReal.sqrt ‖discr K‖₊ * 2 ^ finrank ℚ K := by
    rw [unitConst_def, mul_comm, ENNReal.ofReal_mul (by positivity)]
    simp [← Int.norm_eq_abs, ← coe_nnNorm, ← Real.coe_sqrt]
  rw [hmb, hu, mul_assoc]
  exact mul_le_of_le_one_left bot_le (pow_le_one₀ bot_le (ENNReal.inv_le_one.2 one_le_two))

variable {K}

/-- **Minkowski's theorem for one algebraic integer**: if the radii `f w ≥ 0` at the infinite
places have `unitConst K ≤ ∏ w, f w ^ mult w`, some nonzero algebraic integer `a` has `w a < f w`
at every infinite place `w`. -/
theorem exists_ne_zero_forall_infinitePlace_lt {f : InfinitePlace K → ℝ} (hf : ∀ w, 0 ≤ f w)
    (h : unitConst K ≤ ∏ w, f w ^ mult w) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : InfinitePlace K, w (a : K) < f w := by
  classical
  let g : InfinitePlace K → ℝ≥0 := fun w ↦ (f w).toNNReal
  have hprod : ENNReal.ofReal (unitConst K) ≤ ((∏ w, g w ^ mult w : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal (h.trans_eq ?_)
    simp only [g, NNReal.coe_prod, NNReal.coe_pow, Real.coe_toNNReal _ (hf _)]
  have hfin : ENNReal.ofReal (unitConst K) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne : ENNReal.ofReal (unitConst K) ≠ 0 := by
    simpa using unitConst_pos K
  obtain ⟨a, ha, hlt⟩ := exists_ne_zero_mem_ringOfIntegers_lt K (f := g) <| by
    rw [convexBodyLT_volume]
    calc minkowskiBound K ↑1 ≤ ENNReal.ofReal (unitConst K) :=
          minkowskiBound_one_le_ofReal_unitConst K
      _ < 2 * ENNReal.ofReal (unitConst K) := by
        rw [two_mul]
        exact ENNReal.lt_add_right hfin hne
      _ ≤ (convexBodyLTFactor K : ℝ≥0∞) * ((∏ w, g w ^ mult w : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast two_le_convexBodyLTFactor K
  exact ⟨a, ha, fun w ↦ (hlt w).trans_eq (Real.coe_toNNReal _ (hf w))⟩

/-- **Balancing one algebraic integer at an infinite place** (after Evertse–Schlickewei 2002, §9):
for an infinite place `w₀` and `t > 0` there is a nonzero algebraic integer `a` with
`w a · t ≤ C` at every infinite place `w ≠ w₀` and `w₀ a · t ≤ C · t ^ (d / mult w₀)`, where
`d = [K : ℚ]` and `C = unitConst K ^ (1 / d)`. -/
theorem exists_ne_zero_forall_infinitePlace_mul_le (w₀ : InfinitePlace K) {t : ℝ} (ht : 0 < t) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      (∀ w : InfinitePlace K, w ≠ w₀ →
        w (a : K) * t ≤ unitConst K ^ ((finrank ℚ K : ℝ)⁻¹)) ∧
      w₀ (a : K) * t ≤
        unitConst K ^ ((finrank ℚ K : ℝ)⁻¹) * t ^ ((finrank ℚ K : ℝ) / mult w₀) := by
  classical
  set d := finrank ℚ K
  set C := unitConst K ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos (unitConst_pos K) _
  have hm : (mult w₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 mult_ne_zero
  -- The exponent of `t` at each place: `d / mult w₀ - 1` at `w₀` and `-1` elsewhere. Its sum
  -- weighted by the multiplicities vanishes, so the box has volume `C ^ d = unitConst K`.
  set e : InfinitePlace K → ℝ := fun w ↦ (if w = w₀ then (d : ℝ) / mult w₀ else 0) - 1
  have he : ∑ w, (mult w : ℝ) * e w = 0 := by
    simp only [e, mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [mul_div_cancel₀ _ hm, ← Nat.cast_sum, sum_mult_eq, sub_self]
  have hvol : ∏ w, (C * t ^ e w) ^ mult w = unitConst K :=
    calc ∏ w, (C * t ^ e w) ^ mult w = ∏ w, C ^ mult w * t ^ ((mult w : ℝ) * e w) :=
          Finset.prod_congr rfl fun w _ ↦ by
            rw [mul_pow, ← Real.rpow_mul_natCast ht.le, mul_comm (e w)]
      _ = C ^ d * t ^ ∑ w, (mult w : ℝ) * e w := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq,
            Real.rpow_sum_of_pos ht]
      _ = unitConst K := by
          rw [he, Real.rpow_zero, mul_one,
            Real.rpow_inv_natCast_pow (unitConst_pos K).le finrank_pos.ne']
  obtain ⟨a, ha, hlt⟩ := exists_ne_zero_forall_infinitePlace_lt (f := fun w ↦ C * t ^ e w)
    (fun w ↦ by positivity) hvol.ge
  have hbound (w : InfinitePlace K) : w (a : K) * t ≤ C * t ^ (e w + 1) := by
    rw [Real.rpow_add ht, Real.rpow_one, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hlt w).le ht.le
  refine ⟨a, ha, fun w hw ↦ ?_, ?_⟩
  · simpa [e, hw] using hbound w
  · simpa [e] using hbound w₀

end TauCeti.NumberField
