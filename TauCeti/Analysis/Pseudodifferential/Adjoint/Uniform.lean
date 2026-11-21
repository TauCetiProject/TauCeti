/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Pseudodifferential.LatticeDecomposition
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Adjoints of quantizations of uniform symbols

Let `c` be a symbol of order `m` on `ℝⁿ` whose estimates hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Its right quantization
`Op_R(c) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ`
(`TauCeti.Symbol.quantizeRightUniformCLM`) is the left quantization of a symbol of order `m` with
estimates uniform in the position (`TauCeti.Symbol.IsUniform.exists_quantizeRightUniformCLM_eq`).
For a symbol with compact spatial support this left symbol is `TauCeti.Symbol.ofRight`, which is
built from the Fourier transforms of the position slices of `c`; a uniform symbol such as `c = 1`
has no such Fourier transforms, and here no support condition is assumed.

Since the formal adjoint of the left quantization `Op(a)` of a uniform symbol `a` is the right
quantization of the pointwise adjoint `a(y, ξ)†`
(`TauCeti.Symbol.integral_inner_quantizeUniformCLM`), the formal adjoint of `Op(a)` is again the
quantization of a uniform symbol of order `m`
(`TauCeti.Symbol.IsUniform.exists_integral_inner_quantizeUniformCLM_eq`). Together with the
composition of uniform symbols (`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`), this
shows that the quantizations of uniform symbols are closed under composition and formal adjoints,
with no compact support condition in the position. When `a` has compact spatial support, the
symbol is the adjoint symbol `TauCeti.Symbol.adjoint`, by uniqueness of symbols
(`TauCeti.Symbol.quantizeSchwartzValue_injective`).

## The construction

Cut `c` into the pieces `cⱼ(y, ξ) = χ(y - j) c(y, ξ)`, `j ∈ ℤⁿ`, by the integer translates of the
bump `χ = TauCeti.latticeBump n` (`TauCeti.Symbol.isBallFamily_latticeBump_comp`). Each piece has
compact spatial support, so it has the left symbol `bⱼ = cⱼ.ofRight`,

`bⱼ(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) 𝓕cⱼ(θ, ξ + 2πθ) dθ`,

where `𝓕cⱼ(θ, ξ)` is the Fourier transform at `θ` of the position slice `y ↦ cⱼ(y, ξ)`. The
estimates of `bⱼ` are uniform in `j`, since the Fourier transforms `𝓕cⱼ` of the slices decay
uniformly in `j` (`TauCeti.Symbol.IsBallFamily.exists_norm_fourier_le_rpow`). Away from `j`, `bⱼ`
decays faster than every power of the distance, by the commutator identity

`(x - z)ₖ cᵒ = ((y - z)ₖ c)ᵒ + i (∂_{ξₖ} c)ᵒ`

for the left symbols `cᵒ = c.ofRight` (`TauCeti.Symbol.coordSub_smul_coefficient_ofRight`), which
trades a factor `(x - j)ₖ` for a frequency derivative of `cⱼ` or a factor bounded on its support.
Every mixed derivative of `bⱼ` is the left symbol of the corresponding derivative of `cⱼ`, so it
is bounded by `C ⟨x - j⟩ ^ (-2n) ⟨ξ⟩ ^ (m - |β|)`, and the series `b = ∑ⱼ bⱼ` converges to a
symbol of order `m` with uniform estimates
(`TauCeti.Symbol.exists_isUniform_hasSum_coefficient`).

Finally `Op(b) = Op_R(c)`: on a Schwartz function `u`,
`Op(bⱼ) u = Op_R(cⱼ) u = Op_R(c) (χ(· - j) u)`, and `∑ⱼ χ(· - j) u` converges to `u` in Schwartz
space (`SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub`), on which `Op_R(c)` is continuous.

## Main results

* `TauCeti.Symbol.coordSub_smul_coefficient_ofRight`: **commutator with a coordinate function**,
  `(x - z)ⱼ cᵒ = ((y - z)ⱼ c)ᵒ + i (∂_{ξⱼ} c)ᵒ` for a symbol `c` with compact spatial support.
* `TauCeti.Symbol.IsUniform.exists_quantizeRightUniformCLM_eq`: the right quantization of a
  uniform symbol of order `m` is the quantization of a uniform symbol of order `m`.
* `TauCeti.Symbol.IsUniform.exists_integral_inner_quantizeUniformCLM_eq`: **adjoints of uniform
  symbols**. For a uniform symbol `a` of order `m` with values in operators between complex
  Hilbert spaces, there is a uniform symbol `b` of order `m` with `∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(b) v⟫`
  for all Schwartz functions `u` and `v`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.7 (adjoints in the symbol classes with estimates uniform on `ℝⁿ`).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Metric
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Commutator with a coordinate function -/

section Commutator

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {c : Symbol n V W m}

/-- Multiplying a symbol with compact spatial support by `(y - z)ⱼ` before passing to the left
symbol of its right quantization multiplies the input of that quantization by `(y - z)ⱼ`. -/
private theorem quantizeSchwartzValue_ofRight_coordSubSymbol_comp
    (hc : c.HasCompactSpatialSupport) (z : CoordinateSpace n) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (((coordSubSymbol z j).comp c).ofRight (hc.comp_left _)).coefficient u x =
      quantizeSchwartzValue (c.ofRight hc).coefficient
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u - ((z j : ℝ) : ℂ) • u) x
    := by
  have hg : (fun y : CoordinateSpace n ↦ y j).HasTemperateGrowth :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  have h := congrArg (· x) <| quantizeRightUniformCLM_eq_of_coefficient_apply_eq
    (hc.comp_left (coordSubSymbol z j)).isUniform hc.isUniform (u := u)
    (u' := SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u - ((z j : ℝ) : ℂ) • u)
    fun y ξ ↦ by
      simp [coefficient_comp, SchwartzMap.smulLeftCLM_apply_apply hg,
        ContinuousLinearMap.map_smul_of_tower, sub_smul, Complex.coe_smul]
  rwa [quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight (hc.comp_left _),
    quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight hc, quantizeUniformCLM_apply,
    quantizeUniformCLM_apply] at h

/-- **Commutator with a coordinate function.** For a symbol `c` with compact spatial support and
the left symbol `cᵒ = c.ofRight` of its right quantization,
`(x - z)ⱼ cᵒ = ((y - z)ⱼ c)ᵒ + i (∂_{ξⱼ} c)ᵒ`: multiplying `Op_R(c) u` by `(x - z)ⱼ` either falls
on the input `u` or differentiates `c` in the frequency. -/
theorem coordSub_smul_coefficient_ofRight (hc : c.HasCompactSpatialSupport)
    (z : CoordinateSpace n) (j : Fin n) (x ξ : CoordinateSpace n) :
    ((x - z) j : ℂ) • (c.ofRight hc).coefficient (x, ξ) =
      (((coordSubSymbol z j).comp c).ofRight (hc.comp_left _)).coefficient (x, ξ) +
        Complex.I • ((frequencyDeriv j c).ofRight (hc.frequencyDeriv j)).coefficient (x, ξ) := by
  set b := c.ofRight hc
  set L := (coordSubSymbol z j).comp b
  set R := ((coordSubSymbol z j).comp c).ofRight (hc.comp_left _) +
    Complex.I • inclusion (by linarith) ((frequencyDeriv j c).ofRight (hc.frequencyDeriv j))
  have hLR : L.coefficient = R.coefficient := by
    refine coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦ funext fun y ↦ ?_
    -- Both sides are expressed through `Op(b)` applied to `u` and to `yⱼ u`, and `Op(∂_{ξⱼ} b)`.
    set yu := SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u
    -- `Op(b) (yⱼ u - zⱼ u) = Op(b) (yⱼ u) - zⱼ Op(b) u`, by linearity in the input.
    have hsub : quantizeSchwartzValue b.coefficient (yu - ((z j : ℝ) : ℂ) • u) y =
        quantizeSchwartzValue b.coefficient yu y -
          ((z j : ℝ) : ℂ) • quantizeSchwartzValue b.coefficient u y := by
      obtain ⟨C, -, hC⟩ := b.exists_bound_coefficient_slice y
      rw [sub_eq_add_neg, ← neg_smul,
        quantizeSchwartzValue_add_right (b.continuous_coefficient_slice y).aestronglyMeasurable hC,
        quantizeSchwartzValue_smul_right, neg_smul, ← sub_eq_add_neg]
    -- `yⱼ Op(b) u = Op(b) (yⱼ u) + i Op(∂_{ξⱼ} b) u`, and `∂_{ξⱼ} b` is the left symbol of
    -- `∂_{ξⱼ} c`.
    have hb := b.ofLp_smul_quantizeSchwartzValue j u y
    rw [frequencyDeriv_ofRight hc] at hb
    calc quantizeSchwartzValue L.coefficient u y
        = y j • quantizeSchwartzValue b.coefficient u y -
            ((z j : ℝ) : ℂ) • quantizeSchwartzValue b.coefficient u y := by
          rw [quantizeSchwartzValue_coordSubSymbol_comp, PiLp.sub_apply, Complex.ofReal_sub,
            sub_smul, Complex.coe_smul]
      _ = quantizeSchwartzValue
            (((coordSubSymbol z j).comp c).ofRight (hc.comp_left _)).coefficient u y +
          Complex.I •
            quantizeSchwartzValue ((frequencyDeriv j c).ofRight (hc.frequencyDeriv j)).coefficient
              u y := by
          rw [quantizeSchwartzValue_ofRight_coordSubSymbol_comp hc, hsub, hb]
          abel
      _ = quantizeSchwartzValue R.coefficient u y := by
          rw [coefficient_add, quantizeSchwartzValue_coefficient_add, coefficient_smul,
            quantizeSchwartzValue_smul_left, coefficient_inclusion]
  calc ((x - z) j : ℂ) • b.coefficient (x, ξ) = L.coefficient (x, ξ) := by
        simp [L, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    _ = R.coefficient (x, ξ) := congrFun hLR _
    _ = _ := by simp [R]

end Commutator

/-! ### The left symbols of the members of a ball family -/

section BallFamily

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {ι : Type*} {z : ι → CoordinateSpace n} {r : ℝ}

/-- **The left symbols are bounded uniformly in the family.** If `c` is a ball family of order
`m`, then `‖cᵢᵒ(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` with `C` independent of `i` and `x`. -/
private theorem IsBallFamily.exists_norm_ofRight_le {c : ι → Symbol n V W m}
    (hc : IsBallFamily z r c) :
    ∃ C, ∀ i x ξ, ‖((c i).ofRight (hc.hasCompactSpatialSupport i)).coefficient (x, ξ)‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨D, hD⟩ := hc.exists_norm_fourier_le_rpow (|m| + n + 1)
  set K := max D 0 * 2 ^ (|m| / 2) * (2 * π) ^ |m|
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  refine ⟨K * I, fun i x ξ ↦ ?_⟩
  have hbound (θ : CoordinateSpace n) : ‖(𝐞 ⟪θ, x⟫ : ℂ) •
      𝓕 (fun y ↦ (c i).coefficient (y, ξ + (2 * π) • θ)) θ‖ ≤
        K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [norm_smul, Circle.norm_coe, one_mul]
    have hθ : (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + n + 1) / 2) =
        (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    calc ‖𝓕 (fun y ↦ (c i).coefficient (y, ξ + (2 * π) • θ)) θ‖
        ≤ max D 0 * (1 + ‖ξ + (2 * π) • θ‖ ^ 2) ^ (m / 2) *
            (1 + ‖θ‖ ^ 2) ^ (-(|m| + n + 1) / 2) :=
          (hD i θ _).trans (by gcongr; exact le_max_left _ _)
      _ ≤ max D 0 * (2 ^ (|m| / 2) * (2 * π) ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
            (1 + ‖θ‖ ^ 2) ^ (|m| / 2)) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + n + 1) / 2) := by
          gcongr
          exact one_add_norm_add_smul_sq_rpow_le (by linarith [Real.two_le_pi]) m ξ θ
      _ = K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
            ((1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + n + 1) / 2)) := by ring
      _ = _ := by rw [hθ]
  rw [coefficient_ofRight]
  refine (norm_integral_le_of_norm_le (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (K * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) (.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul]
  ring

variable [CompleteSpace V] [CompleteSpace W]

/-- Applying the commutator with a coordinate function twice bounds
`(x - z)ⱼ² ‖cᵒ(x, ξ)‖` by the norms of the left symbols of `(y - z)ⱼ² c`, `∂_{ξⱼ} ((y - z)ⱼ c)`,
`(y - z)ⱼ ∂_{ξⱼ} c` and `∂_{ξⱼ}² c`. -/
private theorem sq_coordSub_mul_norm_coefficient_ofRight_le {c : Symbol n V W m}
    (hc : c.HasCompactSpatialSupport) (z : CoordinateSpace n) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    ((x - z) j) ^ 2 * ‖(c.ofRight hc).coefficient (x, ξ)‖ ≤
      ‖(((coordSubSymbol z j).comp ((coordSubSymbol z j).comp c)).ofRight
          ((hc.comp_left _).comp_left _)).coefficient (x, ξ)‖ +
        ‖((frequencyDeriv j ((coordSubSymbol z j).comp c)).ofRight
          ((hc.comp_left _).frequencyDeriv j)).coefficient (x, ξ)‖ +
        ‖(((coordSubSymbol z j).comp (frequencyDeriv j c)).ofRight
          ((hc.frequencyDeriv j).comp_left _)).coefficient (x, ξ)‖ +
        ‖((frequencyDeriv j (frequencyDeriv j c)).ofRight
          ((hc.frequencyDeriv j).frequencyDeriv j)).coefficient (x, ξ)‖ := by
  set a : ℂ := ((x - z) j : ℂ)
  have e₁ := coordSub_smul_coefficient_ofRight hc z j x ξ
  have e₂ := coordSub_smul_coefficient_ofRight (hc.comp_left (coordSubSymbol z j)) z j x ξ
  have e₃ := coordSub_smul_coefficient_ofRight (hc.frequencyDeriv j) z j x ξ
  have hsq : a • a • (c.ofRight hc).coefficient (x, ξ) =
      (((coordSubSymbol z j).comp ((coordSubSymbol z j).comp c)).ofRight
          ((hc.comp_left _).comp_left _)).coefficient (x, ξ) +
        Complex.I • ((frequencyDeriv j ((coordSubSymbol z j).comp c)).ofRight
          ((hc.comp_left _).frequencyDeriv j)).coefficient (x, ξ) +
        Complex.I • (((coordSubSymbol z j).comp (frequencyDeriv j c)).ofRight
          ((hc.frequencyDeriv j).comp_left _)).coefficient (x, ξ) -
        ((frequencyDeriv j (frequencyDeriv j c)).ofRight
          ((hc.frequencyDeriv j).frequencyDeriv j)).coefficient (x, ξ) := by
    rw [e₁, smul_add, e₂, smul_comm a Complex.I, e₃, smul_add, smul_smul Complex.I Complex.I,
      Complex.I_mul_I, neg_one_smul]
    abel
  have hnorm : ‖a • a • (c.ofRight hc).coefficient (x, ξ)‖ =
      ((x - z) j) ^ 2 * ‖(c.ofRight hc).coefficient (x, ξ)‖ := by
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc, ← sq, sq_abs]
  rw [← hnorm, hsq]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans_eq ?_) ?_)) le_rfl)
  · rw [norm_smul, Complex.norm_I, one_mul]
  · rw [norm_smul, Complex.norm_I, one_mul]

/-- **Decay away from the centres.** If `c` is a ball family of order `m`, then the left symbol
`cᵢᵒ(x, ξ)` decays in the distance from `x` to the centre `zᵢ` faster than every power, uniformly
in `i`: `‖x - zᵢ‖ ^ (2N) ‖cᵢᵒ(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m`. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_ofRight_le (N : ℕ) :
    ∀ {m : ℝ} {c : ι → Symbol n V W m} (hc : IsBallFamily z r c), ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖x - z i‖ ^ (2 * N) *
        ‖((c i).ofRight (hc.hasCompactSpatialSupport i)).coefficient (x, ξ)‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  induction N with
  | zero =>
    intro m c hc
    obtain ⟨C, hC⟩ := hc.exists_norm_ofRight_le
    refine ⟨max C 0, le_max_right _ _, fun i x ξ ↦ ?_⟩
    rw [mul_zero, pow_zero, one_mul]
    exact (hC i x ξ).trans (by gcongr; exact le_max_left _ _)
  | succ N ih =>
    intro m c hc
    have hc' (j : Fin n) := hc.comp_coordSubSymbol j
    have hc'' (j : Fin n) := hc.map_frequencyDeriv j
    choose A hA0 hA using fun j ↦ ih ((hc' j).comp_coordSubSymbol j)
    choose B hB0 hB using fun j ↦ ih ((hc' j).map_frequencyDeriv j)
    choose C hC0 hC using fun j ↦ ih ((hc'' j).comp_coordSubSymbol j)
    choose D hD0 hD using fun j ↦ ih ((hc'' j).map_frequencyDeriv j)
    refine ⟨∑ j, (A j + B j + C j + D j), Finset.sum_nonneg fun j _ ↦ by
      linarith [hA0 j, hB0 j, hC0 j, hD0 j], fun i x ξ ↦ ?_⟩
    set w := (1 + ‖ξ‖ ^ 2) ^ (m / 2)
    have hci := hc.hasCompactSpatialSupport i
    have hj (j : Fin n) : ‖x - z i‖ ^ (2 * N) * (((x - z i) j) ^ 2 *
        ‖((c i).ofRight hci).coefficient (x, ξ)‖) ≤ (A j + B j + C j + D j) * w := by
      have hA' := hA j i x ξ
      have hB' := hB j i x ξ
      have hC' := hC j i x ξ
      rw [show (0 + (0 + m)) / 2 = m / 2 by ring] at hA'
      have hwB : (1 + ‖ξ‖ ^ 2) ^ ((0 + m - 1) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      have hwC : (1 + ‖ξ‖ ^ 2) ^ ((0 + (m - 1)) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      have hwD : (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - 1) / 2) ≤ w :=
        rpow_weight_le_rpow_weight ξ (by linarith)
      refine (mul_le_mul_of_nonneg_left (sq_coordSub_mul_norm_coefficient_ofRight_le hci (z i) j
        x ξ) (by positivity)).trans ?_
      rw [mul_add, mul_add, mul_add]
      exact (add_le_add (add_le_add (add_le_add hA'
        (hB'.trans (mul_le_mul_of_nonneg_left hwB (hB0 j))))
        (hC'.trans (mul_le_mul_of_nonneg_left hwC (hC0 j))))
        ((hD j i x ξ).trans (mul_le_mul_of_nonneg_left hwD (hD0 j)))).trans_eq (by ring)
    calc ‖x - z i‖ ^ (2 * (N + 1)) * ‖((c i).ofRight hci).coefficient (x, ξ)‖
        = ∑ j, ‖x - z i‖ ^ (2 * N) * (((x - z i) j) ^ 2 *
            ‖((c i).ofRight hci).coefficient (x, ξ)‖) :=
          norm_pow_two_mul_succ_mul_eq_sum (x - z i) N _
      _ ≤ ∑ j, (A j + B j + C j + D j) * w := Finset.sum_le_sum fun j _ ↦ hj j
      _ = _ := by rw [Finset.sum_mul]

/-- **Decay of the derivatives away from the centres.** Every mixed derivative
`∂ₓ^α ∂_ξ^β cᵢᵒ` satisfies `‖x - zᵢ‖ ^ (2N) ‖∂ₓ^α ∂_ξ^β cᵢᵒ(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m - |β|)`, uniformly
in `i`: it is the left symbol of the corresponding derivative of `cᵢ`. -/
private theorem IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_ofRight_le (N : ℕ)
    (α β : List (Fin n)) :
    ∀ {m : ℝ} {c : ι → Symbol n V W m} (hc : IsBallFamily z r c), ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖x - z i‖ ^ (2 * N) *
        ‖mixedDeriv α β ((c i).ofRight (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by simpa [List.length_eq_zero_iff] using hD
    intro m c hc
    simpa using IsBallFamily.exists_norm_sub_pow_mul_norm_ofRight_le N hc
  | succ D ih =>
    intro m c hc
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C, hC0, hC⟩ := ih α' [] (by simpa using hD) (hc.map_spatialDeriv j)
        refine ⟨C, hC0, fun i x ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv, spatialDeriv_ofRight]
        exact hC i x ξ
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C, hC0, hC⟩ := ih α β' hlen (hc.map_frequencyDeriv j)
      refine ⟨C, hC0, fun i x ξ ↦ ?_⟩
      rw [← mixedDeriv_frequencyDeriv, frequencyDeriv_ofRight, ← order_sub_one_sub_length]
      exact hC i x ξ

/-- The derivative estimates of `cᵢᵒ` with the weight `(1 + ‖x - zᵢ‖²) ^ (-n)` in the position. -/
private theorem IsBallFamily.exists_norm_mixedDeriv_ofRight_le {c : ι → Symbol n V W m}
    (hc : IsBallFamily z r c) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ i x ξ,
      ‖mixedDeriv α β ((c i).ofRight (hc.hasCompactSpatialSupport i)).coefficient x ξ‖ ≤
        C * ((1 + ‖x - z i‖ ^ 2) ^ n)⁻¹ * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_ofRight_le 0 α β hc
  obtain ⟨C₁, hC₁0, hC₁⟩ := IsBallFamily.exists_norm_sub_pow_mul_norm_mixedDeriv_ofRight_le n α β hc
  refine ⟨2 ^ (n - 1) * (C₀ + C₁), by positivity, fun i x ξ ↦ ?_⟩
  have h₀ := hC₀ i x ξ
  rw [mul_zero, pow_zero, one_mul] at h₀
  exact (le_mul_one_add_norm_sq_pow_inv (norm_nonneg _) h₀ (hC₁ i x ξ)).trans_eq (by ring)

end BallFamily

/-! ### The right quantization of a uniform symbol -/

section Uniform

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The right quantization of `χ(y - j) c(y, ξ)` is the right quantization of `c` applied to
`χ(· - j) u`. -/
private theorem quantizeRightUniformCLM_latticeBump_comp {c : Symbol n V W m} (hc : c.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (j : Fin n → ℤ) :
    quantizeRightUniformCLM _ ((isBallFamily_latticeBump_comp hc).hasCompactSpatialSupport
      j).isUniform u =
      quantizeRightUniformCLM c hc (SchwartzMap.smulLeftCLM V
        (fun y ↦ latticeBump n (y - latticePoint j)) u) := by
  refine quantizeRightUniformCLM_eq_of_coefficient_apply_eq _ hc fun y ξ ↦ ?_
  simp [coefficient_comp,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_latticeBump_sub j),
    ContinuousLinearMap.map_smul_of_tower]

/-- **The right quantization of a uniform symbol is a left quantization.** If `c` is a symbol of
order `m` whose estimates hold uniformly in the position, then its right quantization `Op_R(c)` is
the quantization of a symbol of order `m` whose estimates hold uniformly in the position. No
compact spatial support is assumed. The symbol is unique
(`TauCeti.Symbol.quantizeSchwartzValue_injective`); when `c` has compact spatial support it is
`c.ofRight`. -/
theorem IsUniform.exists_quantizeRightUniformCLM_eq {c : Symbol n V W m} (hc : c.IsUniform) :
    ∃ (b : Symbol n V W m) (hb : b.IsUniform),
      quantizeRightUniformCLM c hc = quantizeUniformCLM b hb := by
  have hfam := isBallFamily_latticeBump_comp hc
  set F : (Fin n → ℤ) → Symbol n V W (0 + m) := fun j ↦
    ofRight _ (hfam.hasCompactSpatialSupport j)
  set w : (Fin n → ℤ) → CoordinateSpace n → ℝ := fun j x ↦
    ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹
  obtain ⟨b, hb, hbsum⟩ := exists_isUniform_hasSum_coefficient F w (fun _ _ ↦ by positivity)
    exists_summable_forall_one_add_norm_sub_latticePoint_sq_pow_inv_le
    tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le
    (hfam.exists_norm_mixedDeriv_ofRight_le)
  have hord : 0 + m = m := zero_add m
  refine ⟨Symbol.inclusion hord.le b, hb.inclusion hord.le, ?_⟩
  ext u x
  rw [quantizeUniformCLM_apply, coefficient_inclusion]
  -- Both sides are the sum of the series `∑ⱼ Op(cⱼᵒ) u (x) = ∑ⱼ Op_R(c) (χ(· - j) u) (x)`.
  obtain ⟨C, -, hC⟩ := hfam.exists_norm_mixedDeriv_ofRight_le [] []
  simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero] at hC
  refine ((hasSum_quantizeSchwartzValue_of_hasSum_coefficient hbsum
    (summable_one_add_norm_sub_latticePoint_sq_pow_inv x) (hC · x) u).unique ?_).symm
  have hF (j : Fin n → ℤ) : quantizeSchwartzValue (F j).coefficient u x =
      quantizeRightUniformCLM c hc (SchwartzMap.smulLeftCLM V
        (fun y ↦ latticeBump n (y - latticePoint j)) u) x := by
    rw [← quantizeRightUniformCLM_latticeBump_comp hc u j,
      quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight, quantizeUniformCLM_apply]
  simp only [hF]
  -- The lattice partition of unity converges in Schwartz space, on which `Op_R(c)` is continuous.
  have h := (SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub (F := V) u).mapL
    ((BoundedContinuousFunction.evalCLM ℂ x) ∘L
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (CoordinateSpace n) W) ∘L
        quantizeRightUniformCLM c hc)
  simp only [ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    SchwartzMap.toBoundedContinuousFunctionCLM_apply] at h
  exact h

end Uniform

/-! ### The adjoint of a uniform symbol -/

section Adjoint

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Adjoints of uniform symbols.** For a symbol `a` of order `m` whose estimates hold uniformly
in the position, with values in operators between complex Hilbert spaces, the formal adjoint of
its quantization is the quantization of a symbol `b` of order `m` whose estimates hold uniformly in
the position: `∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(b) v⟫` for all Schwartz functions `u` and `v`. No compact
spatial support is assumed. When `a` has compact spatial support, `b` is the adjoint symbol
`TauCeti.Symbol.adjoint`. -/
theorem IsUniform.exists_integral_inner_quantizeUniformCLM_eq {a : Symbol n V W m}
    (ha : a.IsUniform) :
    ∃ (b : Symbol n W V m) (hb : b.IsUniform), ∀ (u : 𝓢(CoordinateSpace n, V))
      (v : 𝓢(CoordinateSpace n, W)),
        ∫ x, inner ℂ (quantizeUniformCLM a ha u x) (v x) =
          ∫ x, inner ℂ (u x) (quantizeUniformCLM b hb v x) := by
  obtain ⟨b, hb, hbq⟩ :=
    (ha.map ContinuousLinearMap.adjointRealCLM).exists_quantizeRightUniformCLM_eq
  exact ⟨b, hb, fun u v ↦ by rw [integral_inner_quantizeUniformCLM, hbq]⟩

end Adjoint

end Symbol

end TauCeti
