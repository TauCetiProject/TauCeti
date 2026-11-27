/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.Sobolev.Dilation
public import TauCeti.Analysis.Sobolev.Wkp.Algebra
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Calculus.BumpFunction.Translates
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Semiclassical Sobolev norms on the whole space

Let `E` be a finite-dimensional real inner product space of dimension `n`, and let `h > 0` be a
length scale. The **semiclassical Sobolev norm** of order `k` of a function `f` on `E` measures
its derivatives in units of `h`, against the volume normalized by `h⁻ⁿ`:

`‖f‖_{k,h} = h^(-n/2) ∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂`

(`TauCeti.semiclassicalSobolevNorm`). At `h = 1` it is the sum of the `L²` norms of the
derivatives through order `k` (`TauCeti.semiclassicalSobolevNorm_one`), and for `f` of class `Cᵏ`
and every `h > 0` it is that sum for the dilated function `f (h • ·)`
(`TauCeti.semiclassicalSobolevNorm_eq_comp_smul`): the norm reads `f` in coordinates in which the
scale `h` has unit size. It is invariant under translations
(`TauCeti.semiclassicalSobolevNorm_comp_sub`), so a fixed profile `g` placed at scale `h` about
any centre `x` has the unit-scale norm of `g`, `‖g (h⁻¹ • (· - x))‖_{k,h} = ‖g‖_{k,1}`
(`TauCeti.semiclassicalSobolevNorm_comp_inv_smul_sub`). The weights are those of the natural
norms of fields concentrating at scale `h`, such as the rescaled Seiberg–Witten fields of Taubes's
large-parameter analysis, whose profiles vary on the scale `h = (2r)^(-1/2)` and whose deviation
from the vacuum lives in tubes of volume comparable to `h²`.

Since the dilation commutes with products and does not change sup norms, the two basic estimates
of the unscaled norm, the Sobolev embedding and the algebra property for `2k > n`
(`TauCeti.exists_norm_le_mul_sum_lpNorm_iteratedFDeriv`,
`TauCeti.exists_sum_lpNorm_iteratedFDeriv_mul_le`), hold for the semiclassical norms **with
constants independent of `h`**:

* `|f(x)| ≤ C ‖f‖_{k,h}` (`TauCeti.exists_norm_le_mul_semiclassicalSobolevNorm`);
* `‖f g‖_{k,h} ≤ C ‖f‖_{k,h} ‖g‖_{k,h}` (`TauCeti.exists_semiclassicalSobolevNorm_mul_le`).

These give pointwise control of nonlinear terms at the microscopic scale without any loss in `h`.
The unscaled norms behave quite differently: on a function concentrated at scale `h`, the sum of
the unscaled `L²` norms of the derivatives through order `k > n / 2` grows like `h^(n/2 - k)`
relative to its sup norm.

**Multipliers.** Multiplication by a scalar function `g` whose derivatives obey the semiclassical
bounds `hⁱ ‖Dⁱ g‖ ≤ B` for `i ≤ k`, such as a gauge transformation or a cutoff varying on the scale
`h`, is bounded on the semiclassical norms, with a constant depending only on `k` and `B`:
`‖g • f‖_{k,h} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h}`
(`TauCeti.semiclassicalSobolevNorm_smul_le_of_le_left`). The same bound holds with the roles
reversed, for a vector-valued `f` with these bounds and a square-integrable scalar `g`
(`TauCeti.semiclassicalSobolevNorm_smul_le_of_le_right`). Both follow from the Leibniz rule, in
which each derivative is weighted by the power of `h` matching its order
(`ContDiff.pow_mul_norm_iteratedFDeriv_smul_le_of_le_left`,
`ContDiff.pow_mul_norm_iteratedFDeriv_smul_le_of_le_right`). Unlike the algebra estimate they need
no Sobolev embedding, so they hold for every order `k` and in every dimension. The same bound holds
for an operator-valued multiplier `A : E → F →L[ℝ] G`, such as a change of frame of a vector
bundle, acting by `y ↦ A y (f y)` (`TauCeti.semiclassicalSobolevNorm_clm_apply_le_of_le_left`,
from `ContDiff.pow_mul_norm_iteratedFDeriv_clm_apply_le_of_le_left`).

**Square sums.** The norm is a sum of the scaled `L²` norms `hⁱ ‖Dⁱ f‖₂`; the Hilbert-type
square sum `∑_{i ≤ k} (hⁱ ‖Dⁱ f‖₂)²` lies between `hⁿ ‖f‖_{k,h}² / (k + 1)` and `hⁿ ‖f‖_{k,h}²`
(`TauCeti.sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq`,
`TauCeti.rpow_mul_semiclassicalSobolevNorm_sq_le`), so every bound
`‖φ‖_{k,h} ≤ C ‖u‖_{k,h}` gives one between square sums with the constant `(k + 1) C²`
(`TauCeti.sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le`).

The norms at different scales compare as follows. A derivative costs one factor of `h`:
`h ‖Df‖_{k,h} ≤ ‖f‖_{k+1,h}` (`TauCeti.mul_semiclassicalSobolevNorm_fderiv_le`). For `0 < h ≤ 1`
the semiclassical and unscaled norms satisfy
`hᵏ ‖f‖_{k,1} ≤ h^(n/2) ‖f‖_{k,h} ≤ ‖f‖_{k,1}`
(`TauCeti.pow_mul_semiclassicalSobolevNorm_one_le`,
`TauCeti.rpow_mul_semiclassicalSobolevNorm_le_semiclassicalSobolevNorm_one`).

## Main definitions

* `TauCeti.semiclassicalSobolevNorm k h f`: the norm `h^(-n/2) ∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂`.

## Main results

* `TauCeti.semiclassicalSobolevNorm_eq_comp_smul`: the semiclassical norm is the unscaled norm of
  the dilated function.
* `TauCeti.semiclassicalSobolevNorm_comp_inv_smul_sub`: a profile placed at scale `h` has the
  unit-scale norm of the profile.
* `TauCeti.semiclassicalSobolevNorm_sum_le`: the triangle inequality for finite sums.
* `TauCeti.exists_norm_le_mul_semiclassicalSobolevNorm`: the Sobolev embedding, uniformly in `h`.
* `TauCeti.exists_semiclassicalSobolevNorm_mul_le`: the algebra estimate, uniformly in `h`.
* `TauCeti.mul_semiclassicalSobolevNorm_fderiv_le`: `h D` is bounded from order `k + 1` to
  order `k`.
* `TauCeti.semiclassicalSobolevNorm_smul_le_of_le_left`: multipliers with semiclassical `Cᵏ`
  bounds are bounded, uniformly in `h`.
* `TauCeti.semiclassicalSobolevNorm_clm_apply_le_of_le_left`: the same for operator-valued
  multipliers.
* `TauCeti.sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq`,
  `TauCeti.rpow_mul_semiclassicalSobolevNorm_sq_le`: comparison with the square sums.

## References

* M. Zworski, *Semiclassical Analysis*, Graduate Studies in Mathematics 138, American
  Mathematical Society, 2012 (semiclassical Sobolev spaces).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **semiclassical Sobolev norm** of order `k` at scale `h` of a function `f` on `E`,
`‖f‖_{k,h} = h^(-n/2) ∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂` with `n = dim E`: the `L²` norms of the derivatives
through order `k`, each weighted by the power of `h` matching its order, against the volume
normalized by `h⁻ⁿ`. For a function `f` of class `Cᵏ` and `h > 0` it is the sum of the `L²` norms of
the derivatives of `f (h • ·)` (`TauCeti.semiclassicalSobolevNorm_eq_comp_smul`).

The value is meaningful only when `Dⁱ f ∈ L²` for all `i ≤ k`: `lpNorm` is `0` on a function
outside `L²` (`MeasureTheory.lpNorm_of_not_memLp`), so such a derivative contributes `0`. -/
def semiclassicalSobolevNorm (k : ℕ) (h : ℝ) (f : E → F) : ℝ :=
  h ^ (-(finrank ℝ E : ℝ) / 2) *
    ∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume

/-- The defining formula of the semiclassical norm,
`‖f‖_{k,h} = h^(-n/2) ∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂`, valid at every scale `h`. -/
theorem semiclassicalSobolevNorm_def (k : ℕ) (h : ℝ) (f : E → F) :
    semiclassicalSobolevNorm k h f =
      h ^ (-(finrank ℝ E : ℝ) / 2) *
        ∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume :=
  (rfl)

/-- At scale one the semiclassical norm is the sum of the `L²` norms of the derivatives through
order `k`. -/
@[simp]
theorem semiclassicalSobolevNorm_one (k : ℕ) (f : E → F) :
    semiclassicalSobolevNorm k 1 f =
      ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i f) 2 volume := by
  simp [semiclassicalSobolevNorm]

/-- The semiclassical norm of the zero function vanishes. -/
@[simp]
theorem semiclassicalSobolevNorm_zero (k : ℕ) (h : ℝ) :
    semiclassicalSobolevNorm k h (0 : E → F) = 0 := by
  simp [semiclassicalSobolevNorm]

/-- The semiclassical norm is invariant under negation. -/
@[simp]
theorem semiclassicalSobolevNorm_neg (k : ℕ) (h : ℝ) (f : E → F) :
    semiclassicalSobolevNorm k h (-f) = semiclassicalSobolevNorm k h f := by
  simp [semiclassicalSobolevNorm, iteratedFDeriv_neg]

/-- **Homogeneity of the semiclassical norm.** `‖c f‖_{k,h} = |c| ‖f‖_{k,h}`. -/
theorem semiclassicalSobolevNorm_const_smul (k : ℕ) (h c : ℝ) (f : E → F) :
    semiclassicalSobolevNorm k h (c • f) = |c| * semiclassicalSobolevNorm k h f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [semiclassicalSobolevNorm, semiclassicalSobolevNorm, mul_left_comm |c|]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hD : iteratedFDeriv ℝ i (c • f) = c • iteratedFDeriv ℝ i f :=
    funext fun _ ↦
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc)).iteratedFDeriv_comp_left
  rw [hD, lpNorm_const_smul, coe_nnNorm, Real.norm_eq_abs, mul_left_comm]

/-- **The triangle inequality for the semiclassical norm.** For `f` and `g` of class `Cᵏ`, with
`Dⁱ f ∈ L²` for `i ≤ k`, and `h ≥ 0`, `‖f + g‖_{k,h} ≤ ‖f‖_{k,h} + ‖g‖_{k,h}`. -/
theorem semiclassicalSobolevNorm_add_le {k : ℕ} {f g : E → F} (hf : ContDiff ℝ k f)
    (hg : ContDiff ℝ k g) (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) {h : ℝ} (hh : 0 ≤ h) :
    semiclassicalSobolevNorm k h (f + g) ≤
      semiclassicalSobolevNorm k h f + semiclassicalSobolevNorm k h g := by
  rw [semiclassicalSobolevNorm, semiclassicalSobolevNorm, semiclassicalSobolevNorm, ← mul_add,
    ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ ?_) (Real.rpow_nonneg hh _)
  have hi : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [← mul_add, iteratedFDeriv_add (hf.of_le (by exact_mod_cast hi))
    (hg.of_le (by exact_mod_cast hi))]
  exact mul_le_mul_of_nonneg_left (lpNorm_add_le (hfm i hi) one_le_two) (pow_nonneg hh i)

theorem semiclassicalSobolevNorm_nonneg (k : ℕ) {h : ℝ} (hh : 0 ≤ h) (f : E → F) :
    0 ≤ semiclassicalSobolevNorm k h f :=
  mul_nonneg (Real.rpow_nonneg hh _)
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (pow_nonneg hh i) lpNorm_nonneg)

/-- **The triangle inequality for finite sums.** For functions `fⱼ` of class `Cᵏ`, with
`Dⁱ fⱼ ∈ L²` for `i ≤ k`, and `h ≥ 0`, `‖∑ⱼ fⱼ‖_{k,h} ≤ ∑ⱼ ‖fⱼ‖_{k,h}`. -/
theorem semiclassicalSobolevNorm_sum_le {ι : Type*} (s : Finset ι) {k : ℕ} {f : ι → E → F}
    (hf : ∀ j ∈ s, ContDiff ℝ k (f j))
    (hfm : ∀ j ∈ s, ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (f j)) 2) {h : ℝ} (hh : 0 ≤ h) :
    semiclassicalSobolevNorm k h (fun x ↦ ∑ j ∈ s, f j x) ≤
      ∑ j ∈ s, semiclassicalSobolevNorm k h (f j) := by
  simp only [semiclassicalSobolevNorm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh _)
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [← Finset.mul_sum, iteratedFDeriv_sum fun j hj ↦ (hf j hj).of_le (by exact_mod_cast hi)]
  exact mul_le_mul_of_nonneg_left (lpNorm_sum_le (fun j hj ↦ hfm j hj i hi) one_le_two)
    (pow_nonneg hh i)

/-- **Translation invariance of the semiclassical norm.** `‖f (· - a)‖_{k,h} = ‖f‖_{k,h}`. -/
@[simp]
theorem semiclassicalSobolevNorm_comp_sub (k : ℕ) (h : ℝ) (f : E → F) (a : E) :
    semiclassicalSobolevNorm k h (fun x ↦ f (x - a)) = semiclassicalSobolevNorm k h f := by
  simp only [semiclassicalSobolevNorm, iteratedFDeriv_comp_sub', ← toReal_eLpNorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← (measurePreserving_sub_right volume a).map_eq]
  rw [(measurableEmbedding_subRight a).eLpNorm_map_measure]
  rfl

/-- Multiplying the semiclassical norm by `h^(n/2)` removes the volume normalization:
`h^(n/2) ‖f‖_{k,h} = ∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂`. -/
theorem rpow_mul_semiclassicalSobolevNorm (k : ℕ) {h : ℝ} (hh : 0 < h) (f : E → F) :
    h ^ ((finrank ℝ E : ℝ) / 2) * semiclassicalSobolevNorm k h f =
      ∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume := by
  rw [semiclassicalSobolevNorm, ← mul_assoc, ← Real.rpow_add hh]
  simp [neg_div]

/-- **The semiclassical norm is the norm of the dilated function.** For `f` of class `Cᵏ` and
`h > 0`, `‖f‖_{k,h} = ∑_{i ≤ k} ‖Dⁱ(f (h • ·))‖₂`. -/
theorem semiclassicalSobolevNorm_eq_comp_smul {k : ℕ} {f : E → F} (hf : ContDiff ℝ k f) {h : ℝ}
    (hh : 0 < h) :
    semiclassicalSobolevNorm k h f = semiclassicalSobolevNorm k 1 fun x ↦ f (h • x) := by
  rw [semiclassicalSobolevNorm_one, semiclassicalSobolevNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : (i : ℕ∞) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Measure.lpNorm_iteratedFDeriv_comp_smul volume (hf.of_le (by exact_mod_cast hi)) hh.ne',
    abs_of_pos hh, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hh]
  congr 2
  simp only [ENNReal.toReal_ofNat]
  ring

/-- **A profile placed at scale `h` has the unit-scale norm of the profile.** For `g` of class `Cᵏ`,
`h > 0` and any centre `x`, `‖g (h⁻¹ • (· - x))‖_{k,h} = ‖g‖_{k,1}`. -/
theorem semiclassicalSobolevNorm_comp_inv_smul_sub {k : ℕ} {g : E → F} (hg : ContDiff ℝ k g)
    {h : ℝ} (hh : 0 < h) (x : E) :
    semiclassicalSobolevNorm k h (fun y ↦ g (h⁻¹ • (y - x))) = semiclassicalSobolevNorm k 1 g := by
  rw [semiclassicalSobolevNorm_eq_comp_smul (hg.comp_inv_smul_sub h x) hh]
  have : (fun z ↦ g (h⁻¹ • (h • z - x))) = fun z ↦ g (z - h⁻¹ • x) := by
    ext z
    rw [smul_sub, inv_smul_smul₀ hh.ne']
  rw [this, semiclassicalSobolevNorm_comp_sub]

/-- For `f` of class `Cᵏ` with square-integrable derivatives through order `k`, the dilated
function `f (h • ·)`, `h ≠ 0`, is of class `Cᵏ` with square-integrable derivatives through
order `k`. -/
private theorem contDiff_comp_smul_and_memLp {k : ℕ} {f : E → F} (hf : ContDiff ℝ k f)
    (hm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ k (fun x ↦ f (h • x)) ∧
      ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun x ↦ f (h • x)) 2 :=
  ⟨hf.comp (contDiff_const_smul h), fun i hi ↦
    (hm i hi).iteratedFDeriv_comp_smul (hf.of_le (by exact_mod_cast hi)) hh⟩

/-- **The Sobolev embedding, uniformly in the scale.** If `2k > dim E`, there is a constant `C ≥ 0`
such that for every `h > 0` and every function `f` of class `Cᵏ` with square-integrable
derivatives through order `k`, `|f(x)| ≤ C ‖f‖_{k,h}` at every point. -/
theorem exists_norm_le_mul_semiclassicalSobolevNorm {k : ℕ} (hk : finrank ℝ E < 2 * k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f : E → ℝ, ContDiff ℝ k f →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) →
        ∀ x, ‖f x‖ ≤ C * semiclassicalSobolevNorm k h f := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_sum_lpNorm_iteratedFDeriv (E := E) hk
  refine ⟨max C 0, le_max_right C 0, fun h hh f hf hm x ↦ ?_⟩
  obtain ⟨hf', hm'⟩ := contDiff_comp_smul_and_memLp hf hm hh.ne'
  have := hC _ hf' hm' (h⁻¹ • x)
  rw [smul_inv_smul₀ hh.ne', ← semiclassicalSobolevNorm_one,
    ← semiclassicalSobolevNorm_eq_comp_smul hf hh] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left C 0)
    (semiclassicalSobolevNorm_nonneg k hh.le f))

/-- **The algebra estimate, uniformly in the scale.** If `2k > dim E`, there is a constant `C ≥ 0`
such that for every `h > 0` and all functions `f` and `g` of class `Cᵏ` with square-integrable
derivatives through order `k`, the derivatives of `f g` through order `k` are square integrable
and `‖f g‖_{k,h} ≤ C ‖f‖_{k,h} ‖g‖_{k,h}`. -/
theorem exists_semiclassicalSobolevNorm_mul_le {k : ℕ} (hk : finrank ℝ E < 2 * k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ f g : E → ℝ, ContDiff ℝ k f → ContDiff ℝ k g →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (f * g)) 2) ∧
        semiclassicalSobolevNorm k h (f * g) ≤
          C * semiclassicalSobolevNorm k h f * semiclassicalSobolevNorm k h g := by
  obtain ⟨C, hC⟩ := exists_sum_lpNorm_iteratedFDeriv_mul_le (E := E) le_rfl
    (by rw [ENNReal.toReal_ofNat, mul_comm]; exact_mod_cast hk)
  refine ⟨max C 0, le_max_right C 0, fun h hh f g hf hg hfm hgm ↦ ?_⟩
  obtain ⟨hf', hfm'⟩ := contDiff_comp_smul_and_memLp hf hfm hh.ne'
  obtain ⟨hg', hgm'⟩ := contDiff_comp_smul_and_memLp hg hgm hh.ne'
  -- The product of the dilations is the dilation of the product.
  have hcomp : (fun x ↦ (f * g) (h • x)) = (fun x ↦ f (h • x)) * fun x ↦ g (h • x) :=
    funext fun _ ↦ by simp only [Pi.mul_apply]
  have hEq : semiclassicalSobolevNorm k h (f * g) =
      semiclassicalSobolevNorm k 1 ((fun x ↦ f (h • x)) * fun x ↦ g (h • x)) := by
    rw [← hcomp]
    exact semiclassicalSobolevNorm_eq_comp_smul (hf.mul hg) hh
  refine ⟨(hC f g hf hg hfm hgm).1, ?_⟩
  rw [hEq, semiclassicalSobolevNorm_eq_comp_smul hf hh, semiclassicalSobolevNorm_eq_comp_smul hg hh]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
    (semiclassicalSobolevNorm_nonneg k zero_le_one _))
    (semiclassicalSobolevNorm_nonneg k zero_le_one _))
  simpa only [semiclassicalSobolevNorm_one] using (hC _ _ hf' hg' hfm' hgm').2

/-- **A derivative costs one factor of the scale.** For `h ≥ 0`,
`h ‖Df‖_{k,h} ≤ ‖f‖_{k+1,h}`: the operator `h D` is bounded, with norm at most one, from order
`k + 1` to order `k`. -/
theorem mul_semiclassicalSobolevNorm_fderiv_le {k : ℕ} {f : E → F} {h : ℝ} (hh : 0 ≤ h) :
    h * semiclassicalSobolevNorm k h (fderiv ℝ f) ≤ semiclassicalSobolevNorm (k + 1) h f := by
  -- The derivatives of `Df` have the norms of the derivatives of `f` of one order higher: the
  -- latter are the former followed by a linear isometry equivalence.
  have hD : ∀ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (fderiv ℝ f)) 2 volume =
      lpNorm (iteratedFDeriv ℝ (i + 1) f) 2 volume := fun i _ ↦ by
    rw [iteratedFDeriv_succ_eq_comp_right' f]
    set L := (continuousMultilinearCurryRightEquiv' ℝ i E F).symm
    by_cases hm : AEStronglyMeasurable (iteratedFDeriv ℝ i (fderiv ℝ f)) volume
    · rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_norm_ae (g := L ∘ _) hm
        (L.continuous.comp_aestronglyMeasurable hm) (.of_forall fun x ↦ (L.norm_map _).symm)]
    · rw [lpNorm_of_not_aestronglyMeasurable hm, lpNorm_of_not_aestronglyMeasurable (f := L ∘ _)
        fun hL ↦ hm (L.isometry.isEmbedding.aestronglyMeasurable_comp_iff.1 hL)]
  unfold semiclassicalSobolevNorm
  rw [Finset.sum_range_succ' _ (k + 1)]
  have hsum : h * ∑ i ∈ Finset.range (k + 1),
        h ^ i * lpNorm (iteratedFDeriv ℝ i (fderiv ℝ f)) 2 volume =
      ∑ i ∈ Finset.range (k + 1), h ^ (i + 1) * lpNorm (iteratedFDeriv ℝ (i + 1) f) 2 volume := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hD i hi, pow_succ]
    ring
  calc h * (h ^ (-(finrank ℝ E : ℝ) / 2) * ∑ i ∈ Finset.range (k + 1),
          h ^ i * lpNorm (iteratedFDeriv ℝ i (fderiv ℝ f)) 2 volume)
      = h ^ (-(finrank ℝ E : ℝ) / 2) * ∑ i ∈ Finset.range (k + 1),
          h ^ (i + 1) * lpNorm (iteratedFDeriv ℝ (i + 1) f) 2 volume := by
        rw [← hsum]
        ring
    _ ≤ h ^ (-(finrank ℝ E : ℝ) / 2) * (∑ i ∈ Finset.range (k + 1),
          h ^ (i + 1) * lpNorm (iteratedFDeriv ℝ (i + 1) f) 2 volume +
          h ^ 0 * lpNorm (iteratedFDeriv ℝ 0 f) 2 volume) := by
        refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ?_) (Real.rpow_nonneg hh _)
        exact mul_nonneg (pow_nonneg hh 0) lpNorm_nonneg

/-- **Comparison with the unscaled norm from above.** For `0 ≤ h ≤ 1`,
`h^(n/2) ‖f‖_{k,h} ≤ ‖f‖_{k,1}`. -/
theorem rpow_mul_semiclassicalSobolevNorm_le_semiclassicalSobolevNorm_one (k : ℕ) {h : ℝ}
    (hh : 0 ≤ h) (hh₁ : h ≤ 1) (f : E → F) :
    h ^ ((finrank ℝ E : ℝ) / 2) * semiclassicalSobolevNorm k h f ≤
      semiclassicalSobolevNorm k 1 f := by
  have hle : ∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume ≤
      semiclassicalSobolevNorm k 1 f := by
    rw [semiclassicalSobolevNorm_one]
    exact Finset.sum_le_sum fun i _ ↦
      mul_le_of_le_one_left lpNorm_nonneg (pow_le_one₀ hh hh₁)
  rcases hh.lt_or_eq with hh | rfl
  · rwa [rpow_mul_semiclassicalSobolevNorm k hh]
  -- At scale zero the left side vanishes, unless `E` is zero dimensional.
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · simpa [semiclassicalSobolevNorm_def, hn] using hle
  · rw [Real.zero_rpow (by positivity), zero_mul, semiclassicalSobolevNorm_one]
    exact Finset.sum_nonneg fun i _ ↦ lpNorm_nonneg

/-- **Comparison with the unscaled norm from below.** For `0 < h ≤ 1`,
`hᵏ ‖f‖_{k,1} ≤ h^(n/2) ‖f‖_{k,h}`: the derivative of order `i ≤ k` loses at most `hᵏ⁻ⁱ ≤ 1`
relative to the top order. -/
theorem pow_mul_semiclassicalSobolevNorm_one_le (k : ℕ) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (f : E → F) :
    h ^ k * semiclassicalSobolevNorm k 1 f ≤
      h ^ ((finrank ℝ E : ℝ) / 2) * semiclassicalSobolevNorm k h f := by
  rw [rpow_mul_semiclassicalSobolevNorm k hh, semiclassicalSobolevNorm_one, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one hh.le hh₁ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) lpNorm_nonneg

/-- The square of the semiclassical norm, with the volume normalization removed, is the square of
the sum `∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂`: `hⁿ ‖f‖_{k,h}² = (∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂)²`. -/
theorem rpow_mul_semiclassicalSobolevNorm_sq (k : ℕ) {h : ℝ} (hh : 0 < h) (f : E → F) :
    h ^ (finrank ℝ E : ℝ) * semiclassicalSobolevNorm k h f ^ 2 =
      (∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume) ^ 2 := by
  rw [← rpow_mul_semiclassicalSobolevNorm k hh, mul_pow]
  congr 1
  rw [← Real.rpow_natCast (h ^ _) 2, ← Real.rpow_mul hh.le]
  norm_num

/-- **The Hilbert sum below the semiclassical norm.** The sum of squares
`∑_{i ≤ k} (hⁱ ‖Dⁱ f‖₂)²` is at most `hⁿ ‖f‖_{k,h}²`. -/
theorem sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq (k : ℕ) {h : ℝ} (hh : 0 < h)
    (f : E → F) :
    ∑ i ∈ Finset.range (k + 1), (h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume) ^ 2 ≤
      h ^ (finrank ℝ E : ℝ) * semiclassicalSobolevNorm k h f ^ 2 := by
  rw [rpow_mul_semiclassicalSobolevNorm_sq k hh]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ mul_nonneg (pow_nonneg hh.le i) lpNorm_nonneg

/-- **The Hilbert sum above the semiclassical norm.** `hⁿ ‖f‖_{k,h}²` is at most `k + 1` times
the sum of squares `∑_{i ≤ k} (hⁱ ‖Dⁱ f‖₂)²`, by the Cauchy–Schwarz inequality. -/
theorem rpow_mul_semiclassicalSobolevNorm_sq_le (k : ℕ) {h : ℝ} (hh : 0 < h) (f : E → F) :
    h ^ (finrank ℝ E : ℝ) * semiclassicalSobolevNorm k h f ^ 2 ≤
      (k + 1) * ∑ i ∈ Finset.range (k + 1),
        (h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume) ^ 2 := by
  rw [rpow_mul_semiclassicalSobolevNorm_sq k hh]
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (k + 1))
    (f := fun i ↦ h ^ i * lpNorm (iteratedFDeriv ℝ i f) 2 volume)

/-- **Square sums under a semiclassical bound.** If `‖φ‖_{k,h} ≤ C ‖u‖_{k,h}` and `h > 0`, then the
square sum `∑_{j ≤ k} (hʲ ‖Dʲ φ‖₂)²` is at most `(k + 1) C²` times that of `u`. -/
theorem sum_sq_le_mul_sum_sq_of_semiclassicalSobolevNorm_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (k : ℕ) {h C : ℝ} (hh : 0 < h) {φ : E → G} {u : E → F}
    (hle : semiclassicalSobolevNorm k h φ ≤ C * semiclassicalSobolevNorm k h u) :
    ∑ j ∈ Finset.range (k + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j φ) 2 volume) ^ 2 ≤
      (k + 1) * C ^ 2 *
        ∑ j ∈ Finset.range (k + 1), (h ^ j * lpNorm (iteratedFDeriv ℝ j u) 2 volume) ^ 2 := by
  have hsq : semiclassicalSobolevNorm k h φ ^ 2 ≤ C ^ 2 * semiclassicalSobolevNorm k h u ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (semiclassicalSobolevNorm_nonneg k hh.le φ) hle 2
  have hn : 0 ≤ h ^ (finrank ℝ E : ℝ) := Real.rpow_nonneg hh.le _
  calc _ ≤ h ^ (finrank ℝ E : ℝ) * semiclassicalSobolevNorm k h φ ^ 2 :=
        sum_sq_le_rpow_mul_semiclassicalSobolevNorm_sq k hh φ
    _ ≤ C ^ 2 * (h ^ (finrank ℝ E : ℝ) * semiclassicalSobolevNorm k h u ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hn]
    _ ≤ C ^ 2 * ((k + 1) * ∑ j ∈ Finset.range (k + 1),
          (h ^ j * lpNorm (iteratedFDeriv ℝ j u) 2 volume) ^ 2) :=
        mul_le_mul_of_nonneg_left (rpow_mul_semiclassicalSobolevNorm_sq_le k hh u) (sq_nonneg C)
    _ = _ := by ring

/-! ### Multipliers with semiclassical `Cᵏ` bounds -/

section Multiplier

variable {k : ℕ} {h B : ℝ}

/-- If the pointwise bound `hⁿ ‖Dⁿ φ‖ ≤ 2ᵏ B ∑_{j ≤ k} hʲ ‖Dʲ u‖` holds for `n ≤ k` and
`Dʲ u ∈ L²` for `j ≤ k`, then the derivatives of `φ` through order `k` are square integrable
and `‖φ‖_{k,h} ≤ (k + 1) 2ᵏ B ‖u‖_{k,h}`. -/
private theorem memLp_and_semiclassicalSobolevNorm_le_of_le {G G' : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G'] {u : E → G} {φ : E → G'}
    (hφ : ContDiff ℝ k φ) (hum : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i u) 2) (hh : 0 < h)
    (hB0 : 0 ≤ B)
    (hle : ∀ n ≤ k, ∀ x, h ^ n * ‖iteratedFDeriv ℝ n φ x‖ ≤
      2 ^ k * B * ∑ j ∈ Finset.range (k + 1), h ^ j * ‖iteratedFDeriv ℝ j u x‖) :
    (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i φ) 2) ∧
      semiclassicalSobolevNorm k h φ ≤ (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k h u := by
  have hum' (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      MemLp (fun x ↦ ‖iteratedFDeriv ℝ j u x‖) 2 :=
    (hum j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).norm
  -- The pointwise bound, integrated: `Dⁿ φ ∈ L²` with
  -- `hⁿ ‖Dⁿ φ‖₂ ≤ 2ᵏ B ∑_{j ≤ k} hʲ ‖‖Dʲ u‖‖₂`.
  set Ψ : E → ℝ := (2 ^ k * B) • ∑ j ∈ Finset.range (k + 1),
    h ^ j • fun x ↦ ‖iteratedFDeriv ℝ j u x‖ with hΨ
  have hΨm : MemLp Ψ 2 :=
    (memLp_finsetSum' _ fun j hj ↦ (hum' j hj).const_smul (h ^ j)).const_smul _
  have key (n : ℕ) (hn : n ≤ k) :
      MemLp (iteratedFDeriv ℝ n φ) 2 ∧
        h ^ n * lpNorm (iteratedFDeriv ℝ n φ) 2 volume ≤
          2 ^ k * B * ∑ j ∈ Finset.range (k + 1),
            h ^ j * lpNorm (fun x ↦ ‖iteratedFDeriv ℝ j u x‖) 2 volume := by
    have hle' (x : E) : ‖(h ^ n • iteratedFDeriv ℝ n φ) x‖ ≤ Ψ x := by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pow_nonneg hh.le n)]
      simpa [hΨ, Finset.sum_apply] using hle n hn x
    have hm : MemLp (h ^ n • iteratedFDeriv ℝ n φ) 2 :=
      hΨm.of_le ((hφ.continuous_iteratedFDeriv (by exact_mod_cast hn)).const_smul _
        |>.aestronglyMeasurable) (.of_forall fun x ↦ (hle' x).trans (le_abs_self _))
    refine ⟨by simpa [(pow_pos hh n).ne'] using hm.const_smul (h ^ n)⁻¹, ?_⟩
    rw [← lpNorm_const_smul_of_nonneg (pow_nonneg hh.le n)]
    refine (lpNorm_mono_real hΨm hle').trans ?_
    rw [hΨ, lpNorm_const_smul_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((lpNorm_sum_le (fun j hj ↦ (hum' j hj).const_smul _)
      one_le_two).trans (Finset.sum_le_sum fun j _ ↦ ?_)) (by positivity)
    rw [lpNorm_const_smul_of_nonneg (pow_nonneg hh.le j)]
  refine ⟨fun i hi ↦ (key i hi).1, ?_⟩
  have hsum : ∑ j ∈ Finset.range (k + 1), h ^ j * lpNorm (fun x ↦ ‖iteratedFDeriv ℝ j u x‖) 2
      volume = ∑ j ∈ Finset.range (k + 1), h ^ j * lpNorm (iteratedFDeriv ℝ j u) 2 volume :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [lpNorm_norm (hum j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).aestronglyMeasurable]
  rw [semiclassicalSobolevNorm, semiclassicalSobolevNorm, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh.le _)
  calc ∑ n ∈ Finset.range (k + 1), h ^ n * lpNorm (iteratedFDeriv ℝ n φ) 2 volume
      ≤ ∑ _n ∈ Finset.range (k + 1), 2 ^ k * B *
          ∑ j ∈ Finset.range (k + 1), h ^ j * lpNorm (iteratedFDeriv ℝ j u) 2 volume :=
        Finset.sum_le_sum fun n hn ↦ hsum ▸ (key n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))).2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F]
  {g : E → 𝕜} {f : E → F}

/-- **Multipliers with semiclassical `Cᵏ` bounds.** Let `g` be a scalar function of class `Cᵏ`
with `hⁱ ‖Dⁱ g‖ ≤ B` everywhere for `i ≤ k`, such as a gauge transformation or a cutoff varying on
the scale `h`. For `h > 0` and `f` of class `Cᵏ` with square-integrable derivatives through
order `k`, the derivatives of `g • f` through order `k` are square integrable and

`‖g • f‖_{k,h} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h}`.

The constant depends only on `k` and `B`, not on `h`, the dimension or the target. -/
theorem semiclassicalSobolevNorm_smul_le_of_le_left (hg : ContDiff ℝ k g) (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun y ↦ g y • f y) 2) ∧
      semiclassicalSobolevNorm k h (fun y ↦ g y • f y) ≤
        (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k h f :=
  memLp_and_semiclassicalSobolevNorm_le_of_le (hg.smul hf) hfm hh
    (nonneg_of_forall_pow_mul_norm_iteratedFDeriv_le hB 0)
    fun _n hn ↦ hg.pow_mul_norm_iteratedFDeriv_smul_le_of_le_left hf hh.le hB hn

/-- **Multiplication by a function with semiclassical `Cᵏ` bounds.** Let `f` be of class `Cᵏ` with
`hⁱ ‖Dⁱ f‖ ≤ B` everywhere for `i ≤ k`. For `h > 0` and a scalar function `g` of class `Cᵏ` with
square-integrable derivatives through order `k`, the derivatives of `g • f` through order `k` are
square integrable and `‖g • f‖_{k,h} ≤ (k + 1) 2ᵏ B ‖g‖_{k,h}`. -/
theorem semiclassicalSobolevNorm_smul_le_of_le_right (hg : ContDiff ℝ k g) (hf : ContDiff ℝ k f)
    (hgm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun y ↦ g y • f y) 2) ∧
      semiclassicalSobolevNorm k h (fun y ↦ g y • f y) ≤
        (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k h g :=
  memLp_and_semiclassicalSobolevNorm_le_of_le (hg.smul hf) hgm hh
    (nonneg_of_forall_pow_mul_norm_iteratedFDeriv_le hB 0)
    fun _n hn ↦ hg.pow_mul_norm_iteratedFDeriv_smul_le_of_le_right hf hh.le hB hn

/-- **Operator-valued multipliers with semiclassical `Cᵏ` bounds.** Let `A : E → F →L[ℝ] G` be of
class `Cᵏ` with `hⁱ ‖Dⁱ A‖ ≤ B` everywhere for `i ≤ k`, such as a change of frame of a vector
bundle varying on the scale `h`. For `h > 0` and `f` of class `Cᵏ` with square-integrable
derivatives through order `k`, the derivatives of `y ↦ A y (f y)` through order `k` are square
integrable and

`‖A f‖_{k,h} ≤ (k + 1) 2ᵏ B ‖f‖_{k,h}`.

The constant depends only on `k` and `B`, not on `h`, the dimension or the spaces. -/
theorem semiclassicalSobolevNorm_clm_apply_le_of_le_left {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {A : E → F →L[ℝ] G} {f : E → F} (hA : ContDiff ℝ k A)
    (hf : ContDiff ℝ k f) (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hh : 0 < h)
    (hB : ∀ i ≤ k, ∀ x, h ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ B) :
    (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun y ↦ A y (f y)) 2) ∧
      semiclassicalSobolevNorm k h (fun y ↦ A y (f y)) ≤
        (k + 1) * 2 ^ k * B * semiclassicalSobolevNorm k h f :=
  memLp_and_semiclassicalSobolevNorm_le_of_le (hA.clm_apply hf) hfm hh
    (nonneg_of_forall_pow_mul_norm_iteratedFDeriv_le hB 0)
    fun _n hn ↦ hA.pow_mul_norm_iteratedFDeriv_clm_apply_le_of_le_left hf hh.le hB hn

end Multiplier

end TauCeti
