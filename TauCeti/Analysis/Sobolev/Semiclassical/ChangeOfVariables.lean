/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.UniformlyLocal
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Calculus.BumpFunction.Translates
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.Calculus.ContDiff.Scaling
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp

/-!
# Changes of chart in the semiclassical Sobolev norms

Let `E` be a finite-dimensional real inner product space and `h > 0` a length scale. The
semiclassical Sobolev norm `‖f‖_{k,h} = h^(-n/2) ∑_{i ≤ k} hⁱ ‖Dⁱ f‖₂`
(`TauCeti.semiclassicalSobolevNorm`) measures the derivatives of `f` in units of `h`. This file
proves that it is stable under changes of chart **with constants independent of `h`**, provided
the chart is controlled at the same scale.

A *chart at scale `h`* is a `Cᵏ` injective map `Φ : E → E` with

* `h ^ (i - 1) * ‖Dⁱ Φ x‖ ≤ L` for `1 ≤ i ≤ k` and every `x`, and
* `c ≤ |det DΦ x|` for every `x`, with `c > 0`.

The first condition says that `x ↦ h⁻¹ • Φ (h • x)`, the chart read in coordinates in which the
scale `h` has unit size, has derivatives of orders `1` through `k` bounded by `L`. It allows charts
that vary on the scale `h`, such as `x ↦ h • ψ (h⁻¹ • x)` for a fixed `ψ` with bounded derivatives,
and, when `h ≤ 1`, it holds for every fixed chart with bounded derivatives. For such a chart and `f`
of class `Cᵏ` with square-integrable derivatives through order `k`:

* the derivatives of `f ∘ Φ` through order `k` are square integrable; for a chart with unweighted
  bounds `‖Dⁱ Φ‖ ≤ L` this is `TauCeti.memLp_iteratedFDeriv_comp`;
* `‖f ∘ Φ‖_{k,h} ≤ K ‖f‖_{k,h}`, where `K = TauCeti.Wkp.compLBound 2 k L c` depends only on `k`,
  `L` and `c` (`TauCeti.semiclassicalSobolevNorm_comp_le`), the constant of the unscaled change of
  variables in `W^{k,2}` (`TauCeti.Wkp.compL`);
* the same holds for a fixed chart with `‖Dⁱ Φ‖ ≤ L` when `h ≤ 1`
  (`TauCeti.semiclassicalSobolevNorm_comp_le_of_le_one`);
* if `Φ` has a right inverse `Ψ` that is also a chart at scale `h`, with constants `L'` and `c'`,
  the two norms are equivalent: `‖f‖_{k,h} ≤ K' ‖f ∘ Φ‖_{k,h}` with
  `K' = TauCeti.Wkp.compLBound 2 k L' c'`
  (`TauCeti.semiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm_comp`).

These are the norm-transfer estimates needed to patch the local semiclassical norms of a manifold
from bounded-overlap charts at scale `h`, with comparison constants that do not degenerate as
`h → 0`.

**The uniformly local norms.** The uniformly local norm
`‖f‖_{k,h,η} = sup_x ‖η (h⁻¹ • (· - x)) f‖_{k,h}`
(`TauCeti.uniformlyLocalSemiclassicalSobolevNorm`) localizes `f` about every centre `x`. A chart
moves these centres: the localization of `f ∘ Φ` about `x` is `g • f` read through `Φ`, where
`g = η (h⁻¹ • (Ψ · - x))` is the cutoff read through the inverse chart `Ψ`. If `Ψ` is also
controlled at scale `h`, with `h ^ (i - 1) ‖Dⁱ Ψ‖ ≤ L'`, then `g` has the semiclassical bounds
`hⁱ ‖Dⁱ g‖ ≤ max 1 L' ^ i #{ordered partitions of i} A` whenever `‖Dⁱ η‖ ≤ A`
(`TauCeti.pow_mul_norm_iteratedFDeriv_comp_inv_smul_sub`,
`ContDiffAt.pow_mul_norm_iteratedFDeriv_comp_le`). If `η` is supported in the
ball of radius `R`, then `g` is supported in the ball of radius `L h R` about `Φ x`, since
`‖DΦ‖ ≤ L`. So for a cutoff `χ` equal to one on the ball of radius `L R`, `g • f` is `g` times the
localization of `f` about `Φ x` by `χ`. Multiplication by `g` and the change of chart are bounded
on the semiclassical norm, so

`‖f ∘ Φ‖_{k,h,η} ≤ K ‖f‖_{k,h,χ}`

with `K = TauCeti.uniformlyLocalCompBound k L L' c A` depending only on `k`, `L`, `L'`, `c` and
`A` (`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_comp_le`), for functions with values in any
real normed space. For `2k > n` and real-valued functions the uniformly local norms of all nonzero
compactly supported cutoffs are equivalent, so the same cutoff can be used on both sides:
`‖f ∘ Φ‖_{k,h,η} ≤ C ‖f‖_{k,h,η}`, where `C` depends only on `η`, `k`, `L`, `L'` and `c`
(`TauCeti.exists_uniformlyLocalSemiclassicalSobolevNorm_comp_le`). If instead the inverse chart
satisfies `c' ≤ |det DΨ|` for some `c' > 0`, then `‖f‖_{k,h,η} ≤ C' ‖f ∘ Φ‖_{k,h,η}`, where `C'`
depends only on `η`, `k`, `L`, `L'` and `c'`
(`TauCeti.exists_uniformlyLocalSemiclassicalSobolevNorm_le_mul_comp`). Neither constant depends on
`h` or on the particular charts `Φ` and `Ψ`.

The proof differentiates `f ∘ Φ` by Faà di Bruno's formula. Weighted by the scale, the
`i`-th derivative obeys
`hⁱ ‖Dⁱ (f ∘ Φ) x‖ ≤ max 1 L ^ i ∑_π h^(|π|) ‖D^(|π|) f (Φ x)‖`, the sum running over the ordered
partitions `π` of `i` (`ContDiffAt.pow_mul_norm_iteratedFDeriv_comp_le_sum`), since the block sizes
of `π` add up to `i`. Each term is then pulled back in `L²` by the change of variables formula,
which costs the factor `c^(-1/2)`
(`TauCeti.Wkp.IsChangeOfVariables.ofReal_pow_mul_eLpNorm_iteratedFDeriv_comp_le`), and is bounded
by the whole sum `∑_{j ≤ k} hʲ ‖Dʲ f‖₂`
(`TauCeti.Wkp.IsChangeOfVariables.ofReal_pow_mul_eLpNorm_iteratedFDeriv_comp_le_of_le`).

## References

* M. Zworski, *Semiclassical Analysis*, Graduate Studies in Mathematics 138, American
  Mathematical Society, 2012 (semiclassical Sobolev spaces and their invariance under changes of
  coordinates).
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open MeasureTheory Module Function TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ} {h L c : ℝ} {f : E → F} {Φ : E → E}

/-- The derivatives of order `i ≤ k` of `f ∘ Φ`, for a chart `Φ` at scale `h`, are square
integrable, and `hⁱ ‖Dⁱ (f ∘ Φ)‖₂` is bounded by
`max 1 L ^ i #{ordered partitions of i} c^(-1/2) ∑_{j ≤ k} hʲ ‖Dʲ f‖₂`. -/
private theorem memLp_and_pow_mul_lpNorm_iteratedFDeriv_comp_le (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hΦ : ContDiff ℝ k Φ)
    (hΦd : Differentiable ℝ Φ) (hinj : Injective Φ) (hh : 0 < h)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) {i : ℕ} (hi : i ≤ k) :
    MemLp (iteratedFDeriv ℝ i (f ∘ Φ)) 2 ∧
      h ^ i * lpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) 2 volume ≤
        max 1 L ^ i * Fintype.card (OrderedFinpartition i) * c⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal *
          ∑ j ∈ Finset.range (k + 1), h ^ j * lpNorm (iteratedFDeriv ℝ j f) 2 volume := by
  -- `Φ` is a change of variables of order `0` of the whole space.
  have hcv : Wkp.IsChangeOfVariables 0 ⊤ ⊤ Φ 0 c :=
    { contDiffOn := contDiffOn_zero.2 hΦd.continuous.continuousOn
      differentiableOn := hΦd.differentiableOn
      injOn := hinj.injOn
      mapsTo := Set.mapsTo_univ _ _
      norm_iteratedFDeriv_le := fun _ h1 h0 ↦ by omega
      pos := hc
      le_abs_det := fun x _ ↦ hdet x }
  have hS : 0 ≤ ∑ j ∈ Finset.range (k + 1), h ^ j * lpNorm (iteratedFDeriv ℝ j f) 2 volume :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (pow_nonneg hh.le j) lpNorm_nonneg
  -- Each weighted derivative `hʲ ‖Dʲ f‖₂` with `j ≤ i` is one term of the sum.
  have hle := hcv.ofReal_pow_mul_eLpNorm_iteratedFDeriv_comp_le_of_le (mu := volume) (p := 2)
    hΦ.contDiffOn hh.le (fun j hj1 hjk x _ ↦ hL j hj1 hjk x) hf.contDiffOn hi
    (fun j hj ↦ by
      rw [Opens.coe_top, Measure.restrict_univ]
      exact hfm j (hj.trans hi))
    (fun j hj ↦ by
      rw [Opens.coe_top, Measure.restrict_univ]
      exact Finset.single_le_sum (f := fun j ↦ h ^ j * lpNorm (iteratedFDeriv ℝ j f) 2 volume)
        (fun j _ ↦ mul_nonneg (pow_nonneg hh.le j) lpNorm_nonneg)
        (Finset.mem_range.2 (Nat.lt_succ_of_le (hj.trans hi))))
  simp only [Opens.coe_top, Measure.restrict_univ] at hle
  have hfin : eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) 2 volume < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (hle.trans_lt ENNReal.ofReal_lt_top).ne
      (ENNReal.ofReal_pos.2 (pow_pos hh i)).ne'
  refine ⟨hfin, ?_⟩
  rw [← toReal_eLpNorm, ← ENNReal.toReal_ofReal (pow_nonneg hh.le i), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by positivity) hS) hle

/-- **Pullbacks along charts stay square integrable.** Let `Φ : E → E` be `Cᵏ`, differentiable and
injective, with derivatives of orders `1` through `k` bounded by `L` and Jacobian determinant at
least `c > 0`. If `f` is `Cᵏ` with square-integrable derivatives through order `k`, then
`Dⁱ (f ∘ Φ)` is square integrable for each `i ≤ k`. -/
theorem memLp_iteratedFDeriv_comp (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hΦ : ContDiff ℝ k Φ)
    (hΦd : Differentiable ℝ Φ) (hinj : Injective Φ)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) {i : ℕ} (hi : i ≤ k) :
    MemLp (iteratedFDeriv ℝ i (f ∘ Φ)) 2 :=
  (memLp_and_pow_mul_lpNorm_iteratedFDeriv_comp_le hf hfm hΦ hΦd hinj one_pos
    (by simpa using hL) hc hdet hi).1

/-- **Change of chart in the semiclassical norm.** Let `h > 0` and let `Φ : E → E` be a chart at
scale `h`: `Cᵏ`, differentiable and injective, with `h ^ (i - 1) * ‖Dⁱ Φ x‖ ≤ L` for
`1 ≤ i ≤ k` and Jacobian determinant at least `c > 0`. For `f` of class `Cᵏ` with
square-integrable derivatives through order `k`,
`‖f ∘ Φ‖_{k,h} ≤ K ‖f‖_{k,h}` with `K = TauCeti.Wkp.compLBound 2 k L c`, a constant depending
only on `k`, `L` and `c`, not on `h`. -/
theorem semiclassicalSobolevNorm_comp_le (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hΦ : ContDiff ℝ k Φ)
    (hΦd : Differentiable ℝ Φ) (hinj : Injective Φ) (hh : 0 < h)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) :
    semiclassicalSobolevNorm k h (f ∘ Φ) ≤
      Wkp.compLBound 2 k L c * semiclassicalSobolevNorm k h f := by
  rw [semiclassicalSobolevNorm_def, semiclassicalSobolevNorm_def, Wkp.compLBound_def,
    mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hh.le _)
  calc ∑ i ∈ Finset.range (k + 1), h ^ i * lpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) 2 volume
      ≤ ∑ i ∈ Finset.range (k + 1),
          max 1 L ^ i * Fintype.card (OrderedFinpartition i) * c⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal *
            ∑ j ∈ Finset.range (k + 1), h ^ j * lpNorm (iteratedFDeriv ℝ j f) 2 volume :=
        Finset.sum_le_sum fun i hi ↦ (memLp_and_pow_mul_lpNorm_iteratedFDeriv_comp_le hf hfm hΦ
          hΦd hinj hh hL hc hdet (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).2
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm (∑ i ∈ _, _)]

/-- **Change of a fixed chart in the semiclassical norm.** For `0 < h ≤ 1` and a `Cᵏ`,
differentiable, injective `Φ : E → E` with derivatives of orders `1` through `k` bounded by `L`
and Jacobian determinant at least `c > 0`, `‖f ∘ Φ‖_{k,h} ≤ K ‖f‖_{k,h}` with
`K = TauCeti.Wkp.compLBound 2 k L c`, uniformly in `h`. -/
theorem semiclassicalSobolevNorm_comp_le_of_le_one (hf : ContDiff ℝ k f)
    (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) (hΦ : ContDiff ℝ k Φ)
    (hΦd : Differentiable ℝ Φ) (hinj : Injective Φ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) :
    semiclassicalSobolevNorm k h (f ∘ Φ) ≤
      Wkp.compLBound 2 k L c * semiclassicalSobolevNorm k h f :=
  semiclassicalSobolevNorm_comp_le hf hfm hΦ hΦd hinj hh
    (fun i hi1 hik x ↦ (mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ hh.le hh1)).trans (hL i hi1 hik x)) hc hdet

/-- **Equivalence of the semiclassical norms under a change of chart.** If `Φ` is a chart at
scale `h` as in `TauCeti.semiclassicalSobolevNorm_comp_le`, and `Ψ` is a right inverse of `Φ`
(`Φ (Ψ y) = y`) which is itself a chart at scale `h`, with constants `L'` and `c'`, then
`‖f‖_{k,h} ≤ K' ‖f ∘ Φ‖_{k,h}` with `K' = TauCeti.Wkp.compLBound 2 k L' c'`. Together with
`TauCeti.semiclassicalSobolevNorm_comp_le`, the norms of `f` and `f ∘ Φ` are equivalent with
constants independent of `h`. -/
theorem semiclassicalSobolevNorm_le_mul_semiclassicalSobolevNorm_comp {Ψ : E → E} {L' c' : ℝ}
    (hf : ContDiff ℝ k f) (hfm : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2)
    (hΦ : ContDiff ℝ k Φ) (hΦd : Differentiable ℝ Φ) (hinj : Injective Φ) (hh : 0 < h)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) (hΨ : ContDiff ℝ k Ψ) (hΨd : Differentiable ℝ Ψ)
    (hΦΨ : RightInverse Ψ Φ)
    (hL' : ∀ i, 1 ≤ i → i ≤ k → ∀ y, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Ψ y‖ ≤ L') (hc' : 0 < c')
    (hdet' : ∀ y, c' ≤ |(fderiv ℝ Ψ y).det|) :
    semiclassicalSobolevNorm k h f ≤
      Wkp.compLBound 2 k L' c' * semiclassicalSobolevNorm k h (f ∘ Φ) := by
  have hfΦ : (f ∘ Φ) ∘ Ψ = f := funext fun y ↦ congrArg f (hΦΨ y)
  have hle := semiclassicalSobolevNorm_comp_le (hf.comp hΦ)
    (fun i hi ↦ (memLp_and_pow_mul_lpNorm_iteratedFDeriv_comp_le hf hfm hΦ hΦd hinj hh hL hc
      hdet hi).1) hΨ hΨd hΦΨ.injective hh hL' hc' hdet'
  rwa [hfΦ] at hle

/-! ### Changes of chart in the uniformly local norms -/

section UniformlyLocal

variable {Ψ : E → E} {L' A R : ℝ}

/-- The constant `K (k + 1) 2ᵏ B` in the change of chart for the uniformly local semiclassical
Sobolev norms (`TauCeti.uniformlyLocalSemiclassicalSobolevNorm_comp_le`), for a chart with
constants `L` and `c` whose inverse has constant `L'`, and a cutoff whose derivatives of order at
most `k` are bounded by `A`. Here `K = TauCeti.Wkp.compLBound 2 k L c` and
`B = A ∑_{i ≤ k} max 1 L' ^ i #{ordered partitions of i}`. -/
def uniformlyLocalCompBound (k : ℕ) (L L' c A : ℝ) : ℝ :=
  Wkp.compLBound 2 k L c * ((k + 1) * 2 ^ k * (A * ∑ i ∈ Finset.range (k + 1),
    max 1 L' ^ i * (Fintype.card (OrderedFinpartition i) : ℝ)))

/-- The formula for the constant `TauCeti.uniformlyLocalCompBound k L L' c A`. -/
theorem uniformlyLocalCompBound_def (k : ℕ) (L L' c A : ℝ) :
    uniformlyLocalCompBound k L L' c A =
      Wkp.compLBound 2 k L c * ((k + 1) * 2 ^ k * (A * ∑ i ∈ Finset.range (k + 1),
        max 1 L' ^ i * (Fintype.card (OrderedFinpartition i) : ℝ))) :=
  (rfl)

/-- The constant `TauCeti.uniformlyLocalCompBound k L L' c A` is nonnegative when `0 < c` and
`0 ≤ A`. -/
theorem uniformlyLocalCompBound_nonneg (k : ℕ) (L L' : ℝ) {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    0 ≤ uniformlyLocalCompBound k L L' c A :=
  mul_nonneg (Wkp.compLBound_nonneg 2 k L hc) (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Where the cutoff `η` about `x` is nonzero, the chart `Φ` keeps the point within `L h R` of
`Φ x`, where a cutoff `χ` equal to one on the ball of radius `L R` is one about `Φ x`. So the
localization of `f ∘ Φ` about `x` by `η` is the localization of `f` about `Φ x` by `χ`, multiplied
by the cutoff read through the inverse chart, and read through `Φ`. -/
private theorem smul_comp_eq_comp {η χ : E → ℝ} (hk : 1 ≤ k) (hΦ : ContDiff ℝ k Φ)
    (hinj : Injective Φ)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hΦΨ : RightInverse Ψ Φ) (hηR : support η ⊆ Metric.closedBall 0 R)
    (hχ1 : Set.EqOn χ 1 (Metric.closedBall 0 (L * R))) (x : E) :
    (fun y ↦ η (h⁻¹ • (y - x)) • (f ∘ Φ) y) =
      (fun z ↦ η (h⁻¹ • (Ψ z - x)) • χ (h⁻¹ • (z - Φ x)) • f z) ∘ Φ := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by exact_mod_cast (by omega : k ≠ 0))
  have hL1 (z : E) : ‖fderiv ℝ Φ z‖ ≤ L := by simpa [norm_iteratedFDeriv_one] using hL 1 le_rfl hk z
  ext y
  simp only [Function.comp_apply, hinj (hΦΨ (Φ y))]
  by_cases hy : η (h⁻¹ • (y - x)) = 0
  · simp [hy]
  rw [hχ1 ?_, Pi.one_apply, one_smul]
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖h⁻¹ • (Φ y - Φ x)‖ = ‖h⁻¹‖ * ‖Φ y - Φ x‖ := norm_smul _ _
    _ ≤ ‖h⁻¹‖ * (L * ‖y - x‖) := by
        gcongr
        exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hΦd z)
          (fun z _ ↦ hL1 z) (Set.mem_univ x) (Set.mem_univ y)
    _ = L * ‖h⁻¹ • (y - x)‖ := by rw [norm_smul]; ring
    _ ≤ L * R := by
        gcongr
        · exact (norm_nonneg _).trans (hL1 0)
        · simpa [Metric.mem_closedBall, dist_zero_right] using hηR hy

/-- **Moving a localization through a chart.** Let `h > 0`, `k ≥ 1`, and let `Φ : E → E` be a chart
at scale `h` as in `TauCeti.semiclassicalSobolevNorm_comp_le`, with constants `L` and `c`, whose
inverse `Ψ` is of class `Cᵏ` with `h ^ (i - 1) * ‖Dⁱ Ψ‖ ≤ L'` for `1 ≤ i ≤ k`. Let `η` be a cutoff
of class `Cᵏ` supported in the closed ball of radius `R`, with `‖Dⁱ η‖ ≤ A` for `i ≤ k`, and let `χ`
be a compactly supported cutoff of class `Cᵏ` equal to one on the closed ball of radius `L R`. For
`f` of class `Cᵏ` and every centre `x`, the localization of `f ∘ Φ` about `x` is bounded by the
localization of `f` about `Φ x`:

`‖η (h⁻¹ • (· - x)) (f ∘ Φ)‖_{k,h} ≤ K ‖χ (h⁻¹ • (· - Φ x)) f‖_{k,h}`,

where `K = TauCeti.uniformlyLocalCompBound k L L' c A` depends only on `k`, `L`, `L'`, `c` and
`A`, not on `h` or `x`. -/
theorem semiclassicalSobolevNorm_smul_comp_le {η χ : E → ℝ} (hk : 1 ≤ k) (hh : 0 < h)
    (hΦ : ContDiff ℝ k Φ) (hinj : Injective Φ)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) (hΨ : ContDiff ℝ k Ψ) (hΦΨ : RightInverse Ψ Φ)
    (hL' : ∀ i, 1 ≤ i → i ≤ k → ∀ y, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Ψ y‖ ≤ L')
    (hη : ContDiff ℝ k η) (hA : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i η y‖ ≤ A)
    (hηR : support η ⊆ Metric.closedBall 0 R) (hχ : ContDiff ℝ k χ) (hχc : HasCompactSupport χ)
    (hχ1 : Set.EqOn χ 1 (Metric.closedBall 0 (L * R))) (hf : ContDiff ℝ k f) (x : E) :
    semiclassicalSobolevNorm k h (fun y ↦ η (h⁻¹ • (y - x)) • (f ∘ Φ) y) ≤
      uniformlyLocalCompBound k L L' c A *
        semiclassicalSobolevNorm k h (fun z ↦ χ (h⁻¹ • (z - Φ x)) • f z) := by
  set g : E → ℝ := fun z ↦ η (h⁻¹ • (Ψ z - x))
  set v : E → F := fun z ↦ χ (h⁻¹ • (z - Φ x)) • f z
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 k.zero_le 0)
  have hterm (i : ℕ) : 0 ≤ max 1 L' ^ i * (Fintype.card (OrderedFinpartition i) : ℝ) :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (Nat.cast_nonneg _)
  -- The cutoff read through `Ψ` has semiclassical bounds independent of `h` and `x`.
  have hB (i : ℕ) (hi : i ≤ k) (z : E) : h ^ i * ‖iteratedFDeriv ℝ i g z‖ ≤
      A * ∑ j ∈ Finset.range (k + 1),
        max 1 L' ^ j * (Fintype.card (OrderedFinpartition j) : ℝ) := by
    refine ((hη.comp_inv_smul_sub h x).contDiffAt.of_le (by exact_mod_cast hi)
      |>.pow_mul_norm_iteratedFDeriv_comp_le (hΨ.contDiffAt.of_le (by exact_mod_cast hi)) hh.le
      (fun j hj1 hji ↦ hL' j hj1 (hji.trans hi) z) fun j hj ↦
        (pow_mul_norm_iteratedFDeriv_comp_inv_smul_sub η hh x j _).trans_le
          (hA j (hj.trans hi) _)).trans ?_
    rw [mul_comm _ A]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ ↦ hterm j)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) hA0
  have hg : ContDiff ℝ k g := (hη.comp_inv_smul_sub h x).comp hΨ
  have hv : ContDiff ℝ k v := (hχ.comp_inv_smul_sub h (Φ x)).smul hf
  have hvm (i : ℕ) (hi : i ≤ k) : MemLp (iteratedFDeriv ℝ i v) 2 :=
    hv.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hi)
      (hχc.comp_inv_smul_sub hh.ne' (Φ x)).smul_right
  obtain ⟨hgvm, hgv⟩ := semiclassicalSobolevNorm_smul_le_of_le_left hg hv hvm hh hB
  rw [smul_comp_eq_comp hk hΦ hinj hL hΦΨ hηR hχ1 x, uniformlyLocalCompBound_def, mul_assoc]
  exact (semiclassicalSobolevNorm_comp_le (hg.smul hv) hgvm hΦ
    (hΦ.differentiable (by exact_mod_cast (by omega : k ≠ 0))) hinj hh hL hc hdet).trans
    (mul_le_mul_of_nonneg_left hgv (Wkp.compLBound_nonneg 2 k L hc))

/-- **Change of chart in the uniformly local norm.** Let `h > 0`, `k ≥ 1`, and let `Φ : E → E` be
a chart at scale `h` as in `TauCeti.semiclassicalSobolevNorm_comp_le`, with constants `L` and `c`,
whose inverse `Ψ` is of class `Cᵏ` with `h ^ (i - 1) * ‖Dⁱ Ψ‖ ≤ L'` for `1 ≤ i ≤ k`. Let `η` be a
cutoff of class `Cᵏ` supported in the closed ball of radius `R`, with `‖Dⁱ η‖ ≤ A` for `i ≤ k`,
and let `χ` be a compactly supported cutoff of class `Cᵏ` equal to one on the closed ball of radius
`L R`. For `f` of class `Cᵏ` whose localizations by `χ` are bounded above, the localizations of
`f ∘ Φ` by `η` are bounded above and

`‖f ∘ Φ‖_{k,h,η} ≤ K ‖f‖_{k,h,χ}`,

where `K = TauCeti.uniformlyLocalCompBound k L L' c A` depends only on `k`, `L`, `L'`, `c` and
`A`, not on `h`. -/
theorem uniformlyLocalSemiclassicalSobolevNorm_comp_le {η χ : E → ℝ} (hk : 1 ≤ k) (hh : 0 < h)
    (hΦ : ContDiff ℝ k Φ) (hinj : Injective Φ)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ Φ x).det|) (hΨ : ContDiff ℝ k Ψ) (hΦΨ : RightInverse Ψ Φ)
    (hL' : ∀ i, 1 ≤ i → i ≤ k → ∀ y, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Ψ y‖ ≤ L')
    (hη : ContDiff ℝ k η) (hA : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i η y‖ ≤ A)
    (hηR : support η ⊆ Metric.closedBall 0 R) (hχ : ContDiff ℝ k χ) (hχc : HasCompactSupport χ)
    (hχ1 : Set.EqOn χ 1 (Metric.closedBall 0 (L * R))) (hf : ContDiff ℝ k f)
    (hb : BddAbove (Set.range fun x ↦
      semiclassicalSobolevNorm k h fun y ↦ χ (h⁻¹ • (y - x)) • f y)) :
    BddAbove (Set.range fun x ↦
        semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • (f ∘ Φ) y) ∧
      uniformlyLocalSemiclassicalSobolevNorm k h η (f ∘ Φ) ≤
        uniformlyLocalCompBound k L L' c A * uniformlyLocalSemiclassicalSobolevNorm k h χ f := by
  have hle (x : E) := (semiclassicalSobolevNorm_smul_comp_le hk hh hΦ hinj hL hc hdet hΨ hΦΨ hL'
    hη hA hηR hχ hχc hχ1 hf x).trans (mul_le_mul_of_nonneg_left
      (semiclassicalSobolevNorm_le_uniformlyLocalSemiclassicalSobolevNorm hb (Φ x))
      (uniformlyLocalCompBound_nonneg k L L' hc ((norm_nonneg _).trans (hA 0 k.zero_le 0))))
  exact ⟨⟨_, Set.forall_mem_range.2 hle⟩, uniformlyLocalSemiclassicalSobolevNorm_le hle⟩

/-- **The uniformly local norm under a change of chart, with one cutoff.** Let `2k > dim E`, let
`η ≠ 0` be a compactly supported cutoff of class `Cᵏ`, and let `L`, `L'` and `c > 0` be constants.
There is a constant `C ≥ 0` such that for every `h > 0`, every chart `Φ` at scale `h` with constants
`L` and `c` (as in `TauCeti.semiclassicalSobolevNorm_comp_le`) whose inverse `Ψ` is of class `Cᵏ`
with `h ^ (i - 1) * ‖Dⁱ Ψ‖ ≤ L'` for `1 ≤ i ≤ k`, and every real `f` of class `Cᵏ` whose
localizations by `η` are bounded above, the localizations of `f ∘ Φ` are bounded above and
`‖f ∘ Φ‖_{k,h,η} ≤ C ‖f‖_{k,h,η}`. -/
theorem exists_uniformlyLocalSemiclassicalSobolevNorm_comp_le (hk : finrank ℝ E < 2 * k)
    {η : E → ℝ} (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) (hη0 : η ≠ 0) (L L' : ℝ)
    (hc : 0 < c) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ Φ Ψ : E → E, ContDiff ℝ k Φ → Injective Φ →
      (∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
      (∀ x, c ≤ |(fderiv ℝ Φ x).det|) → ContDiff ℝ k Ψ → RightInverse Ψ Φ →
      (∀ i, 1 ≤ i → i ≤ k → ∀ y, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Ψ y‖ ≤ L') →
      ∀ f : E → ℝ, ContDiff ℝ k f →
        BddAbove (Set.range fun x ↦
          semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) →
        BddAbove (Set.range fun x ↦
            semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • (f ∘ Φ) y) ∧
          uniformlyLocalSemiclassicalSobolevNorm k h η (f ∘ Φ) ≤
            C * uniformlyLocalSemiclassicalSobolevNorm k h η f := by
  obtain ⟨A, hA0, hA⟩ := hηc.exists_bound_iteratedFDeriv_of_contDiff hη
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hηc.isCompact.isBounded
  -- A smooth cutoff equal to one on the ball of radius `L R`, which contains the supports of the
  -- cutoffs read through the inverse charts.
  let χ : ContDiffBump (0 : E) :=
    ⟨max (L * R) 0 + 1, max (L * R) 0 + 2, by positivity, by linarith⟩
  have hχ1 : Set.EqOn χ 1 (Metric.closedBall 0 (L * R)) := fun y hy ↦
    χ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall
      (by simp only [χ]; linarith [le_max_left (L * R) 0]) hy)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_uniformlyLocalSemiclassicalSobolevNorm_le_mul hk hη hηc hη0
    χ.contDiff χ.hasCompactSupport
  have hK0 := uniformlyLocalCompBound_nonneg k L L' hc hA0
  refine ⟨uniformlyLocalCompBound k L L' c A * C₁, mul_nonneg hK0 hC₁0,
    fun h hh Φ Ψ hΦ hinj hL hdet hΨ hΦΨ hL' f hf hb ↦ ?_⟩
  obtain ⟨hbχ, hχle⟩ := hC₁ h hh f hf hb
  obtain ⟨hb', hle⟩ := uniformlyLocalSemiclassicalSobolevNorm_comp_le (by omega) hh hΦ hinj hL hc
    hdet hΨ hΦΨ hL' hη hA ((subset_tsupport η).trans hR) χ.contDiff χ.hasCompactSupport hχ1 hf hbχ
  refine ⟨hb', hle.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hχle hK0

/-- **The uniformly local norm under the inverse of a change of chart.** Let `2k > dim E`, let
`η ≠ 0` be a compactly supported cutoff of class `Cᵏ`, and let `L`, `L'` and `c' > 0` be constants.
There is a constant `C ≥ 0` such that for every `h > 0`, every `Cᵏ` injective `Φ` with
`h ^ (i - 1) * ‖Dⁱ Φ‖ ≤ L` for `1 ≤ i ≤ k` whose inverse `Ψ` is a chart at scale `h` with constants
`L'` and `c'`, and every real `f` of class `Cᵏ` such that the localizations of `f ∘ Φ` by `η` are
bounded above, the localizations of `f` are bounded above and `‖f‖_{k,h,η} ≤ C ‖f ∘ Φ‖_{k,h,η}`.
Together with `TauCeti.exists_uniformlyLocalSemiclassicalSobolevNorm_comp_le`, the uniformly local
norms of `f` and `f ∘ Φ` are equivalent, with constants independent of `h`. -/
theorem exists_uniformlyLocalSemiclassicalSobolevNorm_le_mul_comp (hk : finrank ℝ E < 2 * k)
    {η : E → ℝ} (hη : ContDiff ℝ k η) (hηc : HasCompactSupport η) (hη0 : η ≠ 0) (L L' : ℝ)
    {c' : ℝ} (hc' : 0 < c') :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ Φ Ψ : E → E, ContDiff ℝ k Φ → Injective Φ →
      (∀ i, 1 ≤ i → i ≤ k → ∀ x, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
      ContDiff ℝ k Ψ → RightInverse Ψ Φ →
      (∀ i, 1 ≤ i → i ≤ k → ∀ y, h ^ (i - 1) * ‖iteratedFDeriv ℝ i Ψ y‖ ≤ L') →
      (∀ y, c' ≤ |(fderiv ℝ Ψ y).det|) →
      ∀ f : E → ℝ, ContDiff ℝ k f →
        BddAbove (Set.range fun x ↦
          semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • (f ∘ Φ) y) →
        BddAbove (Set.range fun x ↦
            semiclassicalSobolevNorm k h fun y ↦ η (h⁻¹ • (y - x)) • f y) ∧
          uniformlyLocalSemiclassicalSobolevNorm k h η f ≤
            C * uniformlyLocalSemiclassicalSobolevNorm k h η (f ∘ Φ) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniformlyLocalSemiclassicalSobolevNorm_comp_le hk hη hηc hη0 L' L hc'
  refine ⟨C, hC0, fun h hh Φ Ψ hΦ hinj hL hΨ hΦΨ hL' hdet' f hf hb ↦ ?_⟩
  -- `Ψ` is a chart at scale `h` with inverse `Φ`, and `(f ∘ Φ) ∘ Ψ = f`.
  have hΨΦ : RightInverse Φ Ψ := fun y ↦ hinj (hΦΨ (Φ y))
  have hfΦΨ : (f ∘ Φ) ∘ Ψ = f := funext fun y ↦ congrArg f (hΦΨ y)
  simpa only [hfΦΨ] using
    hC h hh Ψ Φ hΨ hΦΨ.injective hL' hdet' hΦ hΨΦ hL (f ∘ Φ) (hf.comp hΦ) hb

end UniformlyLocal

end TauCeti
