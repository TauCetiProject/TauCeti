/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Semiclassical.Basic
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno

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

end TauCeti
