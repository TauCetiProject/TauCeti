/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency

/-!
# Quantizations of uniform symbols map Schwartz space to itself

For a symbol `a ∈ S^m_{1,0}` whose estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α β} ⟨ξ⟩^(m - |β|)` hold
uniformly in the position `x` (`TauCeti.Symbol.IsUniform`), the Kohn–Nirenberg quantization
`Op(a) u (x) = ∫ exp(2πi ⟪x, ζ⟫) a(x, 2πζ) (𝓕 u ζ) dζ` sends Schwartz functions to Schwartz
functions, continuously (`TauCeti.Symbol.quantizeUniformCLM`). Quantizations of uniform symbols
can therefore be composed as operators on Schwartz space, which is the setting of the uniform
symbol calculus.

The proof rests on two commutator formulas. A derivative of `Op(a) u` falls either on the input or
on the position variable of the symbol, `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u`
(`TauCeti.Symbol.coordinateDeriv_quantizeSchwartzValue`). Dually, multiplying by a coordinate
function falls either on the input or on the frequency variable of the symbol:

`x_j Op(a) u = Op(a) (x_j u) + i Op(∂_{ξ_j} a) u`

(`TauCeti.Symbol.ofLp_smul_quantizeSchwartzValue`). It comes from an integration by parts in the
frequency, since `x_j exp(2πi ⟪x, ζ⟫)` is a frequency derivative of `exp(2πi ⟪x, ζ⟫)` and
multiplication by `x_j` is a frequency derivative on the Fourier side. The general form, for a
direction `v` and a coefficient differentiable in the frequency, is
`TauCeti.inner_smul_quantizeSchwartzValue`.

Both formulas keep the class of uniform symbols, with spatial derivatives keeping the order and
frequency derivatives lowering it. Iterating them writes every `x^γ ∂^α (Op(a) u)` as a finite sum
of terms `Op(b) (L u)`, with `b` a uniform symbol and `L` a continuous operator on Schwartz space,
and each such term is bounded by a continuous seminorm of `u`
(`TauCeti.quantizeSchwartzCLM`).

The same holds for the right quantization
`Op_R(c) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ` of a uniform symbol
(`TauCeti.Symbol.quantizeRightUniformCLM`), the form taken by formal adjoints of quantizations
(`TauCeti.Symbol.integral_inner_quantizeUniformCLM`). It is constructed on the Fourier side: the
Fourier transform of `Op_R(c) u` at `ζ` is

`𝓕 (y ↦ c(y, 2πζ) u(y)) (ζ) = ∫ exp(-2πi ⟪y, ζ⟫) c(y, 2πζ) u(y) dy`,

and this function of `ζ` is a Schwartz function depending continuously on `u`. The two commutator
formulas exchange their roles. Multiplying by a frequency coordinate `ζ_j` is an integration by
parts in the position, giving the position derivative of the symbol or of the input, which keeps
the order. Differentiating in `ζ_j` gives the frequency derivative of the symbol, of one order
lower, or multiplies the input by `y_j`. Since multiplying by `ζ_j` does not lower the order, the
uniform bound on the profile itself needs one more step for symbols of positive order: writing
`c = ⟨ξ / 2π⟩ ^ (-2) c + ∑ⱼ (ξ_j / 2π)² ⟨ξ / 2π⟩ ^ (-2) c` trades each factor `ξ_j` for a
multiplication by `ζ_j` and lowers the order of the remaining symbols by one, down to order `0`,
where the profile is bounded by `‖u‖_{L¹}`.

## Main results

* `TauCeti.Symbol.quantizeUniformCLM`: the quantization of a uniform symbol as a continuous linear
  map `𝓢(ℝⁿ, V) →L[ℂ] 𝓢(ℝⁿ, W)`.
* `TauCeti.Symbol.quantizeUniformCLM_add`, `TauCeti.Symbol.quantizeUniformCLM_smul`,
  `TauCeti.Symbol.quantizeUniformCLM_zero`, `TauCeti.Symbol.quantizeUniformCLM_inclusion`: the
  quantization is linear in the symbol and does not depend on the order.
* `TauCeti.Symbol.lineDerivOp_quantizeUniformCLM`,
  `TauCeti.Symbol.smulLeftCLM_quantizeUniformCLM`: the two commutator formulas in Schwartz space.
* `TauCeti.Symbol.quantizeUniformCLM_const`: a constant symbol `T` quantizes to the composition
  with `T`.
* `TauCeti.Symbol.quantizeRightUniformCLM`: the right quantization of a uniform symbol as a
  continuous linear map `𝓢(ℝⁿ, V) →L[ℂ] 𝓢(ℝⁿ, W)`, with its formula
  `TauCeti.Symbol.quantizeRightUniformCLM_apply`, its Fourier transform
  `TauCeti.Symbol.fourier_quantizeRightUniformCLM` and its linearity in the symbol
  (`TauCeti.Symbol.quantizeRightUniformCLM_add` and its companions).
* `TauCeti.Symbol.IsUniform.integrable_coefficient_apply`: `y ↦ c(y, ξ) u(y)` is integrable for a
  uniform symbol `c` and a Schwartz function `u`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.6.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ContDiff
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Seminorm bounds -/

/-- A family `Φ u x` of reals, indexed by Schwartz functions `u` and points `x`, is bounded by a
continuous seminorm of `u`, uniformly in `x`. -/
private def IsControlled (Φ : 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ) : Prop :=
  ∃ q : Seminorm ℂ 𝓢(CoordinateSpace n, V), Continuous q ∧ ∀ u x, Φ u x ≤ q u

variable {Φ Ψ : 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ}

private lemma IsControlled.mono (h : IsControlled Ψ) (hle : ∀ u x, Φ u x ≤ Ψ u x) :
    IsControlled Φ :=
  let ⟨q, hq, hΨ⟩ := h
  ⟨q, hq, fun u x ↦ (hle u x).trans (hΨ u x)⟩

private lemma IsControlled.add (hΦ : IsControlled Φ) (hΨ : IsControlled Ψ) :
    IsControlled fun u x ↦ Φ u x + Ψ u x :=
  let ⟨q, hq, hqΦ⟩ := hΦ
  let ⟨q', hq', hqΨ⟩ := hΨ
  ⟨q + q', hq.add hq', fun u x ↦ add_le_add (hqΦ u x) (hqΨ u x)⟩

private lemma IsControlled.const_mul (h : IsControlled Φ) (C : ℝ) (hC : 0 ≤ C) :
    IsControlled fun u x ↦ C * Φ u x :=
  let ⟨q, hq, hqΦ⟩ := h
  ⟨C.toNNReal • q, hq.const_smul _, fun u x ↦ by
    rw [smul_apply, NNReal.smul_def, Real.coe_toNNReal C hC, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hqΦ u x) hC⟩

private lemma IsControlled.sum {ι : Type*} (s : Finset ι)
    {Φ : ι → 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ}
    (h : ∀ i ∈ s, IsControlled (Φ i)) :
    IsControlled fun u x ↦ ∑ i ∈ s, Φ i u x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, continuous_const, fun u _ ↦ by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun i' hi' ↦ h i' (Finset.mem_insert_of_mem hi'))

private lemma IsControlled.comp (h : IsControlled Φ)
    (L : 𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, V)) :
    IsControlled fun u x ↦ Φ (L u) x :=
  let ⟨q, hq, hqΦ⟩ := h
  ⟨q.comp L.toLinearMap, hq.comp L.continuous, fun u x ↦ hqΦ (L u) x⟩

/-- The quantization of a uniform symbol is bounded by a continuous seminorm of the input. -/
private lemma isControlled_norm_quantizeSchwartzValue {a : Symbol n V W m} (ha : a.IsUniform) :
    IsControlled fun u x ↦ ‖quantizeSchwartzValue a.coefficient u x‖ := by
  obtain ⟨C, -, hC⟩ := isUniform_iff.1 ha [] []
  let L := quantizeSchwartzCLM a.contDiff_coefficient.continuous
    ⟨C, m, fun x ξ ↦ by simpa [mixedDeriv_nil_nil] using hC x ξ⟩
  exact ⟨(normSeminorm ℂ _).comp L.toLinearMap, continuous_norm.comp L.continuous,
    fun u x ↦ by simpa [L] using (L u).norm_coe_le_norm x⟩

/-- **The main estimate.** For a uniform symbol `a`, a word `w` of coordinate indices and an
order `N`, `|∏ᵢ x_{w i}| ‖D^N (Op(a) u) (x)‖` is bounded by a continuous seminorm of `u`. -/
private lemma isControlled_prod_mul_norm_iteratedFDeriv (N : ℕ) :
    ∀ (k : ℕ) (w : Fin k → Fin n) {m : ℝ} {a : Symbol n V W m}, a.IsUniform →
      IsControlled fun u x ↦
        |∏ i, x (w i)| * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ := by
  induction N with
  | zero =>
    intro k
    induction k with
    | zero =>
      intro w m a ha
      simpa using isControlled_norm_quantizeSchwartzValue ha
    | succ k ih =>
      -- move one coordinate factor inside, using the commutator with `x_{w 0}`
      intro w m a ha
      refine (((ih (w ∘ Fin.succ) ha).comp (SchwartzMap.smulLeftCLM V
        (fun y : CoordinateSpace n ↦ RCLike.ofReal (K := ℂ) (y (w 0))))).add
        (ih (w ∘ Fin.succ) (ha.frequencyDeriv (w 0)))).mono fun u x ↦ ?_
      simp only [norm_iteratedFDeriv_zero, Fin.prod_univ_succ, abs_mul, Function.comp_apply,
        SchwartzMap.smulLeftCLM_ofReal (g := fun y : CoordinateSpace n ↦ y (w 0)) ℂ
          (EuclideanSpace.proj (w 0)).hasTemperateGrowth]
      rw [mul_comm |x (w 0)|, mul_assoc, ← Real.norm_eq_abs (x (w 0)), ← norm_smul,
        ofLp_smul_quantizeSchwartzValue, ← mul_add]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (abs_nonneg _)
      rw [norm_smul, Complex.norm_I, one_mul]
  | succ N ih =>
    -- differentiate once, using the commutator with `∂_j`
    intro k w m a ha
    refine (IsControlled.sum Finset.univ fun j _ ↦
      ((ih k w ha).comp (LineDeriv.lineDerivOpCLM ℂ 𝓢(CoordinateSpace n, V)
        (EuclideanSpace.single j (1 : ℝ)))).add (ih k w (ha.spatialDeriv j))).mono fun u x ↦ ?_
    simp only [LineDeriv.lineDerivOpCLM_apply, ← mul_add, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left
      ((norm_iteratedFDeriv_succ_le_sum_coordinateDeriv
        ((a.contDiff_quantizeSchwartzValue u).of_le (by exact_mod_cast le_top)) x).trans
        (Finset.sum_le_sum fun j _ ↦ ?_)) (abs_nonneg _)
    rw [a.coordinateDeriv_quantizeSchwartzValue j u, iteratedFDeriv_add_apply
      ((a.contDiff_quantizeSchwartzValue _).contDiffAt.of_le (by exact_mod_cast le_top))
      (((spatialDeriv j a).contDiff_quantizeSchwartzValue _).contDiffAt.of_le
        (by exact_mod_cast le_top))]
    exact norm_add_le _ _

/-- **Schwartz seminorm estimates.** If, for every word `w` of coordinate indices of length `k`,
`|∏ᵢ x_{w i}| ‖D^N (F u) (x)‖` is bounded by a continuous seminorm of `u`, then so is
`‖x‖ ^ k ‖D^N (F u) (x)‖`, in the form required by `SchwartzMap.mkCLM`. -/
private lemma exists_bound_of_isControlled {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : 𝓢(CoordinateSpace n, V) → CoordinateSpace n → X} (k N : ℕ)
    (h : ∀ w : Fin k → Fin n,
      IsControlled fun u x ↦ |∏ i, x (w i)| * ‖iteratedFDeriv ℝ N (F u) x‖) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (u : 𝓢(CoordinateSpace n, V)) x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (F u) x‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ (CoordinateSpace n) V) u := by
  obtain ⟨q, hq, hle⟩ := IsControlled.sum (Finset.univ : Finset (Fin k → Fin n)) fun w _ ↦ h w
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ _ _) q hq
  refine ⟨s, C, C.2, fun u x ↦ ?_⟩
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (F u) x‖ ≤
        (∑ j, |x j|) ^ k * ‖iteratedFDeriv ℝ N (F u) x‖ := by
        gcongr
        -- expand `x` in the standard basis
        set b := EuclideanSpace.basisFun (Fin n) ℝ
        calc ‖x‖ = ‖∑ j, x j • b j‖ := by
              congr 1
              exact (b.sum_repr x).symm
          _ ≤ ∑ j, ‖x j • b j‖ := norm_sum_le _ _
          _ = ∑ j, |x j| := by simp [norm_smul, b.orthonormal.1]
    _ = ∑ w : Fin k → Fin n, |∏ i, x (w i)| * ‖iteratedFDeriv ℝ N (F u) x‖ := by
        simp [Fintype.sum_pow, Finset.sum_mul, Finset.abs_prod]
    _ ≤ q u := hle u x
    _ ≤ C * s.sup (schwartzSeminormFamily ℂ (CoordinateSpace n) V) u := hqC u

/-! ### The quantization as an operator on Schwartz space -/

/-- **Schwartz mapping.** The Kohn–Nirenberg quantization `u ↦ Op(a) u` of a symbol `a` whose
estimates are uniform in the position, as a continuous linear map from Schwartz space to Schwartz
space. -/
def quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) :
    𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, W) :=
  SchwartzMap.mkCLM (fun u ↦ quantizeSchwartzValue a.coefficient u)
    (fun u v x ↦ by
      obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
      exact quantizeSchwartzValue_add_right
        (a.continuous_coefficient_slice x).aestronglyMeasurable hC u v)
    (fun c u _ ↦ quantizeSchwartzValue_smul_right c u)
    (fun u ↦ a.contDiff_quantizeSchwartzValue u)
    (fun p ↦ exists_bound_of_isControlled p.1 p.2 fun w ↦
      isControlled_prod_mul_norm_iteratedFDeriv p.2 p.1 w ha)

theorem coe_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) :
    ⇑(quantizeUniformCLM a ha u) = quantizeSchwartzValue a.coefficient u :=
  (rfl)

@[simp]
theorem quantizeUniformCLM_apply (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeUniformCLM a ha u x = quantizeSchwartzValue a.coefficient u x :=
  (rfl)

/-- The quantization is additive in the symbol. -/
theorem quantizeUniformCLM_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeUniformCLM (a + b) (ha.add hb) = quantizeUniformCLM a ha + quantizeUniformCLM b hb := by
  ext u x
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  obtain ⟨C', -, hC'⟩ := b.exists_bound_coefficient_slice x
  simpa using quantizeSchwartzValue_add_left
    (a.continuous_coefficient_slice x).aestronglyMeasurable hC
    (b.continuous_coefficient_slice x).aestronglyMeasurable hC' u

/-- The quantization is homogeneous in the symbol. -/
theorem quantizeUniformCLM_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) :
    quantizeUniformCLM (c • a) (ha.smul c) = c • quantizeUniformCLM a ha := by
  ext u x
  simp

/-- The zero symbol quantizes to zero. -/
@[simp]
theorem quantizeUniformCLM_zero (h : (0 : Symbol n V W m).IsUniform) :
    quantizeUniformCLM 0 h = 0 := by
  ext u x
  simp

/-- The quantization does not depend on the order at which a symbol is considered. -/
theorem quantizeUniformCLM_inclusion {m' : ℝ} {a : Symbol n V W m} (ha : a.IsUniform)
    (h : m ≤ m') :
    quantizeUniformCLM (inclusion h a) (ha.inclusion h) = quantizeUniformCLM a ha := by
  ext u x
  simp

/-- **Commutator with a derivative.** `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u` in
Schwartz space. -/
theorem lineDerivOp_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) :
    ∂_{EuclideanSpace.single j (1 : ℝ)} (quantizeUniformCLM a ha u) =
      quantizeUniformCLM a ha (∂_{EuclideanSpace.single j (1 : ℝ)} u) +
        quantizeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) u := by
  ext x
  have h := congrFun (a.coordinateDeriv_quantizeSchwartzValue j u) x
  rw [coordinateDeriv_cons, coordinateDeriv_nil, ← coe_quantizeUniformCLM a ha] at h
  simpa [SchwartzMap.lineDerivOp_apply_eq_fderiv] using h

/-- **Commutator with a coordinate function.** `x_j Op(a) u = Op(a) (x_j u) + i Op(∂_{ξ_j} a) u` in
Schwartz space. -/
theorem smulLeftCLM_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) :
    SchwartzMap.smulLeftCLM W (fun y : CoordinateSpace n ↦ y j) (quantizeUniformCLM a ha u) =
      quantizeUniformCLM a ha (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u) +
        Complex.I • quantizeUniformCLM (frequencyDeriv j a) (ha.frequencyDeriv j) u := by
  have hg : (fun y : CoordinateSpace n ↦ y j).HasTemperateGrowth :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simpa using a.ofLp_smul_quantizeSchwartzValue j u x

/-- A constant symbol `T` quantizes to the composition with `T`. -/
theorem quantizeUniformCLM_const [CompleteSpace V] [CompleteSpace W] (T : V →L[ℂ] W) :
    quantizeUniformCLM (const T) (isUniform_const T) =
      SchwartzMap.postcompCLM (E := CoordinateSpace n) T := by
  have hT : (const T : Symbol n V W 0).coefficient = fun _ ↦ T := funext (coefficient_const T)
  ext u x
  simpa [hT] using quantizeSchwartzValue_comp_fst (fun _ ↦ T) u x

/-! ### The Fourier profile of the right quantization -/

section Profile

/-- The Fourier transform `ζ ↦ 𝓕 (y ↦ c(y, 2πζ) u(y)) (ζ)` of the right quantization of `c` on `u`,
written as the integral `∫ exp(-2πi ⟪y, ζ⟫) c(y, 2πζ) u(y) dy`. -/
private def profile (c : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) : W :=
  ∫ y, 𝐞 (-⟪y, ζ⟫) • c.coefficient (y, (2 * π) • ζ) (u y)

/-- The frequency derivative of a uniform symbol is bounded on bounded sets of frequencies,
uniformly in the position. -/
private lemma IsUniform.exists_norm_fderiv_slice_le {c : Symbol n V W m} (hc : c.IsUniform)
    (R : ℝ) : ∃ C, 0 ≤ C ∧ ∀ y ξ, ‖ξ‖ ≤ R → ‖fderiv ℝ (fun η ↦ c.coefficient (y, η)) ξ‖ ≤ C := by
  choose C hC0 hC using fun j ↦ (hc.frequencyDeriv j).exists_bound_coefficient
  obtain ⟨D, hD0, hD⟩ :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.exists_opNorm_le (F := V →L[ℂ] W)
  set B := (1 + R ^ 2) ^ (|m - 1| / 2)
  have hS : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ ↦ hC0 j
  refine ⟨D * ((∑ j, C j) * B), by positivity, fun y ξ hξ ↦ ?_⟩
  have hB : (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) ≤ B := by
    have h1 : 1 ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
    calc (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ (|m - 1| / 2) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith [le_abs_self (m - 1)])
      _ ≤ B := by
          have hR : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg ξ) hξ 2
          exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  refine hD (mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)) fun j ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    fderiv_coefficient_slice_single]
  calc ‖(Symbol.frequencyDeriv j c).coefficient (y, ξ)‖ ≤ C j * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) :=
        hC j y ξ
    _ ≤ (∑ j, C j) * B :=
        mul_le_mul (Finset.single_le_sum (fun i _ ↦ hC0 i) (Finset.mem_univ j)) hB
          (by positivity) (Finset.sum_nonneg fun i _ ↦ hC0 i)

variable {c : Symbol n V W m}

private lemma continuous_integrand (c : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) :
    Continuous fun y : CoordinateSpace n ↦ 𝐞 (-⟪y, ζ⟫) • c.coefficient (y, (2 * π) • ζ) (u y) :=
  (Real.continuous_fourierChar.comp (by fun_prop)).smul
    ((c.contDiff_coefficient_slice _).continuous.clm_apply u.continuous)

/-- For a symbol `c` with estimates uniform in the position, a frequency `ξ` and a Schwartz function
`u`, the function `y ↦ c(y, ξ) u(y)` is integrable: `‖c(y, ξ)‖` is bounded in `y`. -/
theorem IsUniform.integrable_coefficient_apply (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (ξ : CoordinateSpace n) : Integrable fun y ↦ c.coefficient (y, ξ) (u y) := by
  obtain ⟨C, -, hC⟩ := hc.exists_bound_coefficient
  refine (u.integrable.norm.const_mul (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono'
    ((c.contDiff_coefficient_slice _).continuous.clm_apply u.continuous).aestronglyMeasurable
    (.of_forall fun y ↦ ((c.coefficient _).le_opNorm _).trans (by gcongr; exact hC _ _))

private lemma integrable_integrand (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) :
    Integrable fun y : CoordinateSpace n ↦ 𝐞 (-⟪y, ζ⟫) • c.coefficient (y, (2 * π) • ζ) (u y) :=
  (Real.fourierIntegral_convergent_iff ζ).2 (hc.integrable_coefficient_apply u _)

/-- `‖𝓕 (y ↦ c(y, 2πζ) u(y)) (ζ)‖ ≤ C ⟨2πζ⟩ ^ m ‖u‖_{L¹}`. -/
private lemma norm_profile_le {C : ℝ} (hC : ∀ y ξ, ‖c.coefficient (y, ξ)‖ ≤
    C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (u : 𝓢(CoordinateSpace n, V)) (ζ : CoordinateSpace n) :
    ‖profile c u ζ‖ ≤ C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖u.toLp 1‖ := by
  rw [SchwartzMap.norm_toLp_one, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (u.integrable.norm.const_mul _) (.of_forall fun y ↦ ?_)
  rw [Circle.norm_smul]
  exact ((c.coefficient _).le_opNorm _).trans (by gcongr; exact hC _ _)

private lemma profile_add_right (hc : c.IsUniform) (u v : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) : profile c (u + v) ζ = profile c u ζ + profile c v ζ := by
  simp only [profile, add_apply, map_add, smul_add]
  exact integral_add (integrable_integrand hc u ζ) (integrable_integrand hc v ζ)

private lemma profile_smul_right (c' : ℂ) (u : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) : profile c (c' • u) ζ = c' • profile c u ζ := by
  simp only [profile, smul_apply, map_smul, smul_comm (𝐞 _) c']
  exact integral_smul c' _

private lemma profile_add_left {c' : Symbol n V W m} (hc : c.IsUniform) (hc' : c'.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (ζ : CoordinateSpace n) :
    profile (c + c') u ζ = profile c u ζ + profile c' u ζ := by
  simp only [profile, coefficient_add, Pi.add_apply, add_apply, smul_add]
  exact integral_add (integrable_integrand hc u ζ) (integrable_integrand hc' u ζ)

private lemma profile_smul_left (a : ℂ) (u : 𝓢(CoordinateSpace n, V)) (ζ : CoordinateSpace n) :
    profile (a • c) u ζ = a • profile c u ζ := by
  simp only [profile, coefficient_smul, Pi.smul_apply, smul_apply, smul_comm (𝐞 _) a]
  exact integral_smul a _

/-! ### Differentiation in the frequency -/

open ContinuousLinearMap in
/-- The derivative in `ζ` of the integrand `exp(-2πi ⟪y, ζ⟫) c(y, 2πζ) u(y)`. -/
private def integrandFDeriv (c : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (ζ y : CoordinateSpace n) : CoordinateSpace n →L[ℝ] W :=
  (𝐞 (-⟪y, ζ⟫) : ℂ) • ((apply ℂ W (u y)).restrictScalars ℝ).comp
      ((fderiv ℝ (fun η ↦ c.coefficient (y, η)) ((2 * π) • ζ)).comp
        ((2 * π) • ContinuousLinearMap.id ℝ (CoordinateSpace n))) +
    ((-2 * π * Complex.I * 𝐞 (-⟪y, ζ⟫)) • (Complex.ofRealCLM ∘L innerSL ℝ y)).smulRight
      (c.coefficient (y, (2 * π) • ζ) (u y))

private lemma integrandFDeriv_apply (c : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (ζ y h : CoordinateSpace n) :
    integrandFDeriv c u ζ y h =
      𝐞 (-⟪y, ζ⟫) • fderiv ℝ (fun η ↦ c.coefficient (y, η)) ((2 * π) • ζ) ((2 * π) • h) (u y) +
        (-2 * π * Complex.I * ⟪y, h⟫ * 𝐞 (-⟪y, ζ⟫)) • c.coefficient (y, (2 * π) • ζ) (u y) := by
  simp only [integrandFDeriv, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.coe_id', id_eq, Circle.smul_def, smul_eq_mul]
  ring_nf

private lemma hasFDerivAt_integrand (c : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (y ζ : CoordinateSpace n) :
    HasFDerivAt (fun ζ ↦ 𝐞 (-⟪y, ζ⟫) • c.coefficient (y, (2 * π) • ζ) (u y))
      (integrandFDeriv c u ζ y) ζ := by
  have he : HasFDerivAt (fun ζ ↦ (𝐞 (-⟪y, ζ⟫) : ℂ))
      ((-2 * π * Complex.I * 𝐞 (-⟪y, ζ⟫)) • (Complex.ofRealCLM ∘L innerSL ℝ y)) ζ :=
    hasFDerivAt_fourierChar_neg_bilinear_right (innerSL ℝ) y ζ
  have hg : HasFDerivAt (fun ζ : CoordinateSpace n ↦ c.coefficient (y, (2 * π) • ζ))
      ((fderiv ℝ (fun η ↦ c.coefficient (y, η)) ((2 * π) • ζ)).comp
        ((2 * π) • ContinuousLinearMap.id ℝ (CoordinateSpace n))) ζ :=
    (((c.contDiff_coefficient.comp (contDiff_prodMk_right y)).differentiable (by simp)
      _).hasFDerivAt).comp ζ ((hasFDerivAt_id ζ).const_smul (2 * π))
  have hg' := ((ContinuousLinearMap.apply ℂ W (u y)).restrictScalars ℝ).hasFDerivAt.comp ζ hg
  simp only [Circle.smul_def]
  exact he.smul hg'

/-- The derivative of the integrand is dominated by `‖u(y)‖ + ‖y‖ ‖u(y)‖` for bounded `ζ`. -/
private lemma exists_norm_integrandFDeriv_le (hc : c.IsUniform) (R : ℝ) :
    ∃ K, ∀ (u : 𝓢(CoordinateSpace n, V)) (ζ y : CoordinateSpace n), ‖ζ‖ ≤ R →
      ‖integrandFDeriv c u ζ y‖ ≤ K * (‖u y‖ + ‖y‖ ^ 1 * ‖u y‖) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_bound_coefficient
  obtain ⟨D, hD0, hD⟩ := hc.exists_norm_fderiv_slice_le (2 * π * R)
  set B := (1 + (2 * π * R) ^ 2) ^ (|m| / 2)
  refine ⟨2 * π * D + 2 * π * C * B, fun u ζ y hζ ↦ ?_⟩
  have hξ : ‖(2 * π) • ζ‖ ≤ 2 * π * R := by
    rw [norm_smul, Real.norm_of_nonneg two_pi_pos.le]
    exact mul_le_mul_of_nonneg_left hζ two_pi_pos.le
  have hB : (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) ≤ B := by
    have h1 : 1 ≤ 1 + ‖(2 * π) • ζ‖ ^ 2 := by nlinarith [sq_nonneg ‖(2 * π) • ζ‖]
    calc (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) ≤ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (|m| / 2) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith [le_abs_self m])
      _ ≤ B := Real.rpow_le_rpow (by positivity)
          (by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hξ 2]) (by positivity)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [integrandFDeriv_apply]
  refine (norm_add_le _ _).trans ?_
  rw [Circle.norm_smul, norm_smul]
  have h₁ : ‖fderiv ℝ (fun η ↦ c.coefficient (y, η)) ((2 * π) • ζ) ((2 * π) • h) (u y)‖ ≤
      2 * π * D * ‖u y‖ * ‖h‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _)
      (norm_nonneg _)).trans ?_
    rw [norm_smul, Real.norm_of_nonneg two_pi_pos.le]
    calc ‖fderiv ℝ (fun η ↦ c.coefficient (y, η)) ((2 * π) • ζ)‖ * (2 * π * ‖h‖) * ‖u y‖
        ≤ D * (2 * π * ‖h‖) * ‖u y‖ := by gcongr; exact hD y _ hξ
      _ = 2 * π * D * ‖u y‖ * ‖h‖ := by ring
  have h₂ : ‖(-2 * π * Complex.I * ⟪y, h⟫ * 𝐞 (-⟪y, ζ⟫) : ℂ)‖ *
      ‖c.coefficient (y, (2 * π) • ζ) (u y)‖ ≤ 2 * π * C * B * (‖y‖ * ‖u y‖) * ‖h‖ := by
    have hi : |⟪y, h⟫| ≤ ‖y‖ * ‖h‖ := abs_real_inner_le_norm y h
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg pi_pos.le, Complex.norm_I, Circle.norm_coe,
      mul_one, mul_one, Real.norm_eq_abs]
    calc 2 * π * |⟪y, h⟫| * ‖c.coefficient (y, (2 * π) • ζ) (u y)‖
        ≤ 2 * π * (‖y‖ * ‖h‖) * (C * B * ‖u y‖) := by
          gcongr
          refine ((c.coefficient _).le_opNorm _).trans ?_
          gcongr
          exact (hC _ _).trans (mul_le_mul_of_nonneg_left hB hC0)
      _ = 2 * π * C * B * (‖y‖ * ‖u y‖) * ‖h‖ := by ring
  calc _ ≤ 2 * π * D * ‖u y‖ * ‖h‖ + 2 * π * C * B * (‖y‖ * ‖u y‖) * ‖h‖ := add_le_add h₁ h₂
    _ ≤ (2 * π * D + 2 * π * C * B) * (‖u y‖ + ‖y‖ ^ 1 * ‖u y‖) * ‖h‖ := by
        have hexp : (2 * π * D + 2 * π * C * B) * (‖u y‖ + ‖y‖ ^ 1 * ‖u y‖) * ‖h‖ =
            2 * π * D * ‖u y‖ * ‖h‖ + 2 * π * C * B * (‖y‖ * ‖u y‖) * ‖h‖ +
              (2 * π * D * (‖y‖ * ‖u y‖) * ‖h‖ + 2 * π * C * B * ‖u y‖ * ‖h‖) := by ring
        rw [hexp]
        exact le_add_of_nonneg_right (by positivity)

private lemma continuous_integrandFDeriv (c : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) : Continuous (integrandFDeriv c u ζ) := by
  have hD : Continuous fun y ↦ fderiv ℝ (fun η ↦ c.coefficient (y, η)) ((2 * π) • ζ) :=
    (ContDiff.fderiv (f := fun y η ↦ c.coefficient (y, η)) (m := ∞) (n := 0)
      (by exact c.contDiff_coefficient) contDiff_const (by simp)).continuous
  have hc : Continuous fun y ↦ c.coefficient (y, (2 * π) • ζ) :=
    (c.contDiff_coefficient_slice _).continuous
  refine continuous_clm_apply.2 fun h ↦ ?_
  simp only [integrandFDeriv_apply]
  have he : Continuous fun y : CoordinateSpace n ↦ (𝐞 (-⟪y, ζ⟫) : ℂ) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).subtype_val
  refine (he.smul ((hD.clm_apply continuous_const).clm_apply u.continuous)).add ?_
  exact (((continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))).mul he).smul
    (hc.clm_apply u.continuous))

/-- The derivative of the profile, by differentiation under the integral sign. -/
private lemma hasFDerivAt_profile (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (ζ₀ : CoordinateSpace n) :
    HasFDerivAt (profile c u) (∫ y, integrandFDeriv c u ζ₀ y) ζ₀ := by
  obtain ⟨K, hK⟩ := exists_norm_integrandFDeriv_le hc (‖ζ₀‖ + 1)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds ζ₀ one_pos)
    (.of_forall fun ζ ↦ (continuous_integrand c u ζ).aestronglyMeasurable)
    (integrable_integrand hc u ζ₀) (continuous_integrandFDeriv c u ζ₀).aestronglyMeasurable
    (ae_of_all _ fun y ζ hζ ↦ hK u ζ y ?_)
    ((u.integrable.norm.add (u.integrable_pow_mul volume 1)).const_mul K)
    (ae_of_all _ fun y ζ _ ↦ hasFDerivAt_integrand c u y ζ)
  have := norm_le_norm_add_norm_sub' ζ ζ₀
  rw [Metric.mem_ball, dist_eq_norm] at hζ
  linarith

/-- **Leibniz rule in the frequency.** The partial derivative `∂_{ζ_j}` of the profile falls either
on the phase, multiplying the input by `-2πi y_j`, or on the frequency variable of the symbol. -/
private lemma coordinateDeriv_profile (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (j : Fin n) (ζ : CoordinateSpace n) :
    coordinateDeriv [j] (profile c u) ζ =
      (2 * π : ℂ) • profile (Symbol.frequencyDeriv j c) u ζ +
        (-2 * π * Complex.I) • profile c
          (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u) ζ := by
  have hint₁ := integrable_integrand (hc.frequencyDeriv j) u ζ
  have hint₂ := integrable_integrand hc
    (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u) ζ
  have hint : Integrable (integrandFDeriv c u ζ) := by
    obtain ⟨K, hK⟩ := exists_norm_integrandFDeriv_le hc ‖ζ‖
    exact ((u.integrable.norm.add (u.integrable_pow_mul volume 1)).const_mul K).mono'
      (continuous_integrandFDeriv c u ζ).aestronglyMeasurable
      (.of_forall fun y ↦ hK u ζ y le_rfl)
  have hpt (y : CoordinateSpace n) : integrandFDeriv c u ζ y (EuclideanSpace.single j 1) =
      (2 * π : ℂ) • (𝐞 (-⟪y, ζ⟫) • (Symbol.frequencyDeriv j c).coefficient (y, (2 * π) • ζ) (u y)) +
        (-2 * π * Complex.I) • (𝐞 (-⟪y, ζ⟫) • c.coefficient (y, (2 * π) • ζ)
          (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u y)) := by
    rw [integrandFDeriv_apply, SchwartzMap.smulLeftCLM_apply_apply
        (g := fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasTemperateGrowth,
      ← fderiv_coefficient_slice_single, map_smul, EuclideanSpace.inner_single_right]
    simp only [one_mul, conj_trivial, smul_apply, map_smul, Circle.smul_def,
      smul_smul]
    rw [← Complex.coe_smul, smul_smul]
    congr 2 <;> push_cast <;> ring
  rw [coordinateDeriv_cons, coordinateDeriv_nil, (hasFDerivAt_profile hc u ζ).fderiv,
    ContinuousLinearMap.integral_apply hint, integral_congr_ae (.of_forall hpt),
    integral_add ?_ ?_, integral_smul, integral_smul, profile, profile]
  · exact hint₁.smul _
  · exact hint₂.smul _

/-- **Smoothness.** The profile of a uniform symbol is smooth. -/
private lemma contDiff_profile (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V)) :
    ContDiff ℝ ∞ (profile c u) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m c u with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun ζ ↦
      (hasFDerivAt_profile hc u ζ).continuousAt)
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun ζ ↦ (hasFDerivAt_profile hc u ζ).differentiableAt, by simp,
      contDiff_clm_apply_iff.2 fun h ↦ ?_⟩
    have hj (j : Fin n) : ContDiff ℝ k fun ζ ↦
        fderiv ℝ (profile c u) ζ (EuclideanSpace.single j 1) := by
      have hd : (fun ζ ↦ fderiv ℝ (profile c u) ζ (EuclideanSpace.single j 1)) =
          coordinateDeriv [j] (profile c u) := by
        funext ζ
        rw [coordinateDeriv_cons, coordinateDeriv_nil]
      rw [hd, funext (coordinateDeriv_profile hc u j)]
      exact ((ih (hc.frequencyDeriv j) u).const_smul _).add ((ih hc _).const_smul _)
    have hsum : (fun ζ ↦ fderiv ℝ (profile c u) ζ h) = fun ζ ↦
        ∑ j, h j • fderiv ℝ (profile c u) ζ (EuclideanSpace.single j 1) := by
      funext ζ
      exact (fderiv ℝ (profile c u) ζ).apply_eq_sum_single h
    rw [hsum]
    exact ContDiff.sum fun j _ ↦ (hj j).const_smul (h j)

/-- The derivative of `y ↦ c(y, ξ) u(y)` in the direction `y_j` falls either on the symbol or on
the input. -/
private lemma hasLineDerivAt_coefficient_apply (c : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) (j : Fin n) (y : CoordinateSpace n) :
    HasLineDerivAt ℝ (fun y ↦ c.coefficient (y, ξ) (u y))
      ((Symbol.spatialDeriv j c).coefficient (y, ξ) (u y) +
        c.coefficient (y, ξ) (∂_{EuclideanSpace.single j (1 : ℝ)} u y)) y
      (EuclideanSpace.single j 1) := by
  have hc : HasFDerivAt (fun y ↦ c.coefficient (y, ξ))
      (fderiv ℝ (fun y ↦ c.coefficient (y, ξ)) y) y :=
    ((c.contDiff_coefficient_slice _).differentiable (by simp) y).hasFDerivAt
  have hu : HasFDerivAt (fun y ↦ u y) (fderiv ℝ u y) y := u.differentiableAt.hasFDerivAt
  convert ((((ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).hasFDerivAt).comp y hc).clm_apply
    hu).hasLineDerivAt (EuclideanSpace.single j 1) using 1
  · simp
  · simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_coefficient_single, add_comm]

/-- **Multiplication by a frequency coordinate.** `2πi ζ_j` times the profile is the profile of
`∂_{x_j} c` plus the profile of `c` on `∂_j u`: an integration by parts in the position, since
`2πi ζ_j exp(-2πi ⟪y, ζ⟫)` is minus the derivative of the phase in `y_j`. -/
private lemma smul_profile (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V)) (j : Fin n)
    (ζ : CoordinateSpace n) :
    (2 * π * Complex.I * (ζ j : ℂ)) • profile c u ζ =
      profile (Symbol.spatialDeriv j c) u ζ +
        profile c (∂_{EuclideanSpace.single j (1 : ℝ)} u) ζ := by
  have hint := integrable_integrand hc u ζ
  have hint₁ := integrable_integrand (hc.spatialDeriv j) u ζ
  have hint₂ := integrable_integrand hc (∂_{EuclideanSpace.single j (1 : ℝ)} u) ζ
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℂ (E := W))
    (f := fun y ↦ (𝐞 (-⟪y, ζ⟫) : ℂ)) (f' := fun y ↦ (-2 * π * Complex.I * (ζ j : ℂ)) * 𝐞 (-⟪y, ζ⟫))
    (g := fun y ↦ c.coefficient (y, (2 * π) • ζ) (u y))
    (v := EuclideanSpace.single j 1)
    (g' := fun y ↦ (Symbol.spatialDeriv j c).coefficient (y, (2 * π) • ζ) (u y) +
      c.coefficient (y, (2 * π) • ζ) (∂_{EuclideanSpace.single j (1 : ℝ)} u y))
    ((hint.smul (-2 * π * Complex.I * (ζ j : ℂ))).congr (.of_forall fun y ↦ by
      simp [Circle.smul_def, mul_smul]))
    ((hint₁.add hint₂).congr (.of_forall fun y ↦ by simp [Circle.smul_def, smul_add]))
    (hint.congr (.of_forall fun y ↦ by simp [Circle.smul_def]))
    (fun y _ ↦ by simpa [EuclideanSpace.inner_single_left] using
      Real.hasLineDerivAt_fourierChar_neg_inner ζ (EuclideanSpace.single j 1) y)
    (fun y _ ↦ hasLineDerivAt_coefficient_apply c u ((2 * π) • ζ) j y)
  have h₁ : ∫ y, ContinuousLinearMap.lsmul ℝ ℂ (𝐞 (-⟪y, ζ⟫) : ℂ)
      ((Symbol.spatialDeriv j c).coefficient (y, (2 * π) • ζ) (u y) +
        c.coefficient (y, (2 * π) • ζ) (∂_{EuclideanSpace.single j (1 : ℝ)} u y)) =
      profile (Symbol.spatialDeriv j c) u ζ +
        profile c (∂_{EuclideanSpace.single j (1 : ℝ)} u) ζ := by
    rw [profile, profile, ← integral_add hint₁ hint₂]
    exact integral_congr_ae (.of_forall fun y ↦ by simp [Circle.smul_def, smul_add])
  have h₂ : ∫ y, ContinuousLinearMap.lsmul ℝ ℂ ((-2 * π * Complex.I * (ζ j : ℂ)) * 𝐞 (-⟪y, ζ⟫))
      (c.coefficient (y, (2 * π) • ζ) (u y)) =
      (-2 * π * Complex.I * (ζ j : ℂ)) • profile c u ζ := by
    rw [profile, ← integral_smul]
    exact integral_congr_ae (.of_forall fun y ↦ by simp [Circle.smul_def, mul_smul])
  rw [h₁, h₂] at hibp
  rw [hibp, ← neg_smul]
  congr 1
  ring

/-- The bound behind `smul_profile`: `|ζ_j| ‖𝓕 (y ↦ c(y, 2πζ) u(y)) (ζ)‖` is at most the sum of the
norms of the profiles of `∂_{x_j} c` on `u` and of `c` on `∂_j u`. -/
private lemma abs_mul_norm_profile_le (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V)) (j : Fin n)
    (ζ : CoordinateSpace n) :
    |ζ j| * ‖profile c u ζ‖ ≤ ‖profile (Symbol.spatialDeriv j c) u ζ‖ +
      ‖profile c (∂_{EuclideanSpace.single j (1 : ℝ)} u) ζ‖ := by
  have h : ‖(2 * π * Complex.I * (ζ j : ℂ))‖ = 2 * π * |ζ j| := by simp [abs_of_pos pi_pos]
  calc |ζ j| * ‖profile c u ζ‖ ≤ ‖(2 * π * Complex.I * (ζ j : ℂ))‖ * ‖profile c u ζ‖ := by
        rw [h]
        gcongr
        exact le_mul_of_one_le_left (abs_nonneg _) (by linarith [Real.two_le_pi])
    _ = _ := by rw [← norm_smul, smul_profile hc]
    _ ≤ _ := norm_add_le _ _

/-- The profile of `c` is the profile of `⟨ξ / 2π⟩ ^ (-2) c` plus the sum over `j` of `ζ_j / 2π`
times the profile of `ξ_j ⟨ξ / 2π⟩ ^ (-2) c`: at `ξ = 2πζ` the weight is `(1 + ‖ζ‖²)⁻¹` and
`1 + ∑ⱼ ζ_j² = 1 + ‖ζ‖²`. This lowers the order by one, at the cost of a factor `ζ_j`. -/
private lemma profile_eq_add_sum (hc : c.IsUniform) (u : 𝓢(CoordinateSpace n, V))
    (ζ : CoordinateSpace n) :
    profile c u ζ = profile ((besselPotential (-2) : Symbol n W W (-2)).comp c) u ζ +
      ∑ j, (((2 * π)⁻¹ * ζ j : ℝ) : ℂ) •
        profile ((ofInner (EuclideanSpace.single j 1) : Symbol n W W 1).comp
          ((besselPotential (-2) : Symbol n W W (-2)).comp c)) u ζ := by
  set c₂ := (besselPotential (-2) : Symbol n W W (-2)).comp c
  have hc₂ : c₂.IsUniform := (isUniform_besselPotential _).comp hc
  have hb (j : Fin n) := (isUniform_ofInner (V := W) (EuclideanSpace.single j 1)).comp hc₂
  have hw : (2 * π)⁻¹ • (2 * π) • ζ = ζ := by
    rw [smul_smul, inv_mul_cancel₀ two_pi_pos.ne', one_smul]
  have hpt (y : CoordinateSpace n) : c.coefficient (y, (2 * π) • ζ) =
      c₂.coefficient (y, (2 * π) • ζ) + ∑ j, (((2 * π)⁻¹ * ζ j : ℝ) : ℂ) •
        ((ofInner (EuclideanSpace.single j 1) : Symbol n W W 1).comp c₂).coefficient
          (y, (2 * π) • ζ) := by
    simp only [c₂, coefficient_comp, coefficient_besselPotential, coefficient_ofInner, hw,
      EuclideanSpace.inner_single_right, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.id_comp, smul_smul, ← Finset.sum_smul, ← add_smul]
    conv_lhs => rw [← one_smul ℂ (c.coefficient (y, (2 * π) • ζ))]
    congr 1
    have hpos : 0 < 1 + ‖ζ‖ ^ 2 := by positivity
    have hsum : ∑ i, (2 * π)⁻¹ * ζ i * 2 * π * ζ i = ‖ζ‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    have h2 : (-2 : ℝ) / 2 = -1 := by norm_num
    rw [h2, Real.rpow_neg_one]
    simp only [conj_trivial, one_mul, PiLp.smul_apply, smul_eq_mul]
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_add]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hsum, ← one_add_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]
  have hint₂ := integrable_integrand hc₂ u ζ
  have hintb (j : Fin n) : Integrable fun y : CoordinateSpace n ↦ (((2 * π)⁻¹ * ζ j : ℝ) : ℂ) •
      (𝐞 (-⟪y, ζ⟫) • ((ofInner (EuclideanSpace.single j 1) : Symbol n W W 1).comp c₂).coefficient
        (y, (2 * π) • ζ) (u y)) :=
    (integrable_integrand (hb j) u ζ).smul _
  have key (y : CoordinateSpace n) : 𝐞 (-⟪y, ζ⟫) • c.coefficient (y, (2 * π) • ζ) (u y) =
      𝐞 (-⟪y, ζ⟫) • c₂.coefficient (y, (2 * π) • ζ) (u y) + ∑ j, (((2 * π)⁻¹ * ζ j : ℝ) : ℂ) •
        (𝐞 (-⟪y, ζ⟫) • ((ofInner (EuclideanSpace.single j 1) : Symbol n W W 1).comp c₂).coefficient
          (y, (2 * π) • ζ) (u y)) := by
    rw [hpt]
    simp only [add_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_add,
      Finset.smul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _)
  simp only [profile]
  rw [integral_congr_ae (.of_forall key), integral_add hint₂ (integrable_finsetSum _ fun j _ ↦
    hintb j), integral_finsetSum _ fun j _ ↦ hintb j]
  simp_rw [integral_smul]

end Profile

/-! ### Seminorm bounds for the right quantization -/

section Bounds

/-- **The bound on the profile.** For a uniform symbol of any order, `‖𝓕 (y ↦ c(y, 2πζ) u(y)) (ζ)‖`
is bounded by a continuous seminorm of `u`, uniformly in `ζ`. For order at most `0` this is the
`L¹` bound; a symbol of order at most `k + 1` is reduced to symbols of order at most `k` by
`profile_eq_add_sum` and `smul_profile`. -/
private lemma isControlled_norm_profile (k : ℕ) :
    ∀ {m : ℝ}, m ≤ k → ∀ {c : Symbol n V W m}, c.IsUniform →
      IsControlled fun u ζ ↦ ‖profile c u ζ‖ := by
  induction k with
  | zero =>
    intro m hm c hc
    obtain ⟨C, hC0, hC⟩ := hc.exists_bound_coefficient
    refine ⟨C.toNNReal • (normSeminorm ℂ _).comp
      (SchwartzMap.toLpCLM ℂ V 1 volume).toLinearMap,
      (continuous_norm.comp (SchwartzMap.toLpCLM ℂ V 1 volume).continuous).const_smul _,
      fun u ζ ↦ ?_⟩
    rw [smul_apply, NNReal.smul_def, Real.coe_toNNReal C hC0, smul_eq_mul]
    refine (norm_profile_le hC u ζ).trans ?_
    simp only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
      SchwartzMap.toLpCLM_apply]
    have h1 : 1 ≤ 1 + ‖(2 * π) • ζ‖ ^ 2 := by nlinarith [sq_nonneg ‖(2 * π) • ζ‖]
    have hm0 : m / 2 ≤ 0 := by simp only [CharP.cast_eq_zero] at hm; linarith
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos h1 hm0)) hC0
  | succ k ih =>
    intro m hm c hc
    set c₂ := (besselPotential (-2) : Symbol n W W (-2)).comp c
    have hc₂ : c₂.IsUniform := (isUniform_besselPotential _).comp hc
    have hb (j : Fin n) := (isUniform_ofInner (V := W) (EuclideanSpace.single j 1)).comp hc₂
    have hm₂ : -2 + m ≤ k := by push_cast at hm; linarith
    have hmb : 1 + (-2 + m) ≤ k := by push_cast at hm; linarith
    refine ((ih hm₂ hc₂).add (IsControlled.sum Finset.univ fun j _ ↦
      ((ih hmb ((hb j).spatialDeriv j)).add ((ih hmb (hb j)).comp
        (LineDeriv.lineDerivOpCLM ℂ 𝓢(CoordinateSpace n, V)
          (EuclideanSpace.single j (1 : ℝ))))))).mono fun u ζ ↦ ?_
    rw [profile_eq_add_sum hc u ζ]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ ↦ ?_)))
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (inv_pos.2 two_pi_pos), mul_assoc]
    refine (mul_le_of_le_one_left (by positivity) ?_).trans (abs_mul_norm_profile_le (hb j) u j ζ)
    exact inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])

/-- One derivative of the profile: `‖D^(N+1) P_c u (ζ)‖` is at most `2π` times the sum over `j` of
`‖D^N P_{∂_{ξ_j} c} u (ζ)‖ + ‖D^N P_c (y_j u) (ζ)‖`, by `coordinateDeriv_profile`. -/
private lemma norm_iteratedFDeriv_succ_profile_le {c : Symbol n V W m} (hc : c.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (N : ℕ) (ζ : CoordinateSpace n) :
    ‖iteratedFDeriv ℝ (N + 1) (profile c u) ζ‖ ≤
      2 * π * ∑ j, (‖iteratedFDeriv ℝ N (profile (Symbol.frequencyDeriv j c) u) ζ‖ +
        ‖iteratedFDeriv ℝ N (profile c
          (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u)) ζ‖) := by
  rw [Finset.mul_sum]
  refine (norm_iteratedFDeriv_succ_le_sum_coordinateDeriv
    ((contDiff_profile hc u).of_le (by exact_mod_cast le_top)) ζ).trans
    (Finset.sum_le_sum fun j _ ↦ ?_)
  have hP := contDiff_profile (hc.frequencyDeriv j) u
  have hQ := contDiff_profile hc
    (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u)
  have hd : coordinateDeriv [j] (profile c u) =
      (2 * π : ℂ) • profile (Symbol.frequencyDeriv j c) u + (-2 * π * Complex.I) •
        profile c (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u) :=
    funext (coordinateDeriv_profile hc u j)
  rw [hd]
  have hP' : ContDiffAt ℝ N ((2 * π : ℂ) • profile (Symbol.frequencyDeriv j c) u) ζ :=
    (hP.const_smul (2 * π : ℂ)).contDiffAt.of_le (by exact_mod_cast le_top)
  have hQ' : ContDiffAt ℝ N ((-2 * π * Complex.I) • profile c
      (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ)) u)) ζ :=
    (hQ.const_smul (-2 * π * Complex.I)).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_add_apply hP' hQ',
    iteratedFDeriv_const_smul_apply (hP.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_const_smul_apply (hQ.contDiffAt.of_le (by exact_mod_cast le_top))]
  refine (norm_add_le _ _).trans ?_
  have h₁ : ‖(2 * π : ℂ)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  have h₂ : ‖(-2 * π * Complex.I : ℂ)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  rw [norm_smul, norm_smul, h₁, h₂, mul_add]

/-- **The main estimate.** For a uniform symbol `c`, a word `w` of coordinate indices and an
order `N`, `|∏ᵢ ζ_{w i}| ‖D^N (𝓕 (y ↦ c(y, 2πζ) u(y))) (ζ)‖` is bounded by a continuous seminorm
of `u`, uniformly in `ζ`. -/
private lemma isControlled_prod_mul_norm_iteratedFDeriv_profile (N : ℕ) :
    ∀ (k : ℕ) (w : Fin k → Fin n) {m : ℝ} {c : Symbol n V W m}, c.IsUniform →
      IsControlled fun u ζ ↦ |∏ i, ζ (w i)| * ‖iteratedFDeriv ℝ N (profile c u) ζ‖ := by
  induction N with
  | zero =>
    intro k
    induction k with
    | zero =>
      intro w m c hc
      simpa using isControlled_norm_profile ⌈m⌉₊ (Nat.le_ceil m) hc
    | succ k ih =>
      -- move one frequency factor inside, using `smul_profile`
      intro w m c hc
      refine ((ih (w ∘ Fin.succ) (hc.spatialDeriv (w 0))).add ((ih (w ∘ Fin.succ) hc).comp
        (LineDeriv.lineDerivOpCLM ℂ 𝓢(CoordinateSpace n, V)
          (EuclideanSpace.single (w 0) (1 : ℝ))))).mono fun u ζ ↦ ?_
      simp only [norm_iteratedFDeriv_zero, Fin.prod_univ_succ, abs_mul, Function.comp_apply,
        LineDeriv.lineDerivOpCLM_apply]
      rw [mul_comm |ζ (w 0)|, mul_assoc, ← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_mul_norm_profile_le hc u (w 0) ζ) (abs_nonneg _)
  | succ N ih =>
    -- differentiate once, using `coordinateDeriv_profile`
    intro k w m c hc
    refine (IsControlled.sum Finset.univ fun j _ ↦
      (((ih k w (hc.frequencyDeriv j)).add ((ih k w hc).comp
        (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ ((y j : ℝ) : ℂ))))).const_mul
        (2 * π) two_pi_pos.le)).mono fun u ζ ↦ ?_
    simp only [← mul_add, ← Finset.mul_sum, mul_left_comm (2 * π)]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_succ_profile_le hc u N ζ) (abs_nonneg _)

/-- The profile of a uniform symbol, as a continuous linear map on Schwartz space. -/
private def profileCLM (c : Symbol n V W m) (hc : c.IsUniform) :
    𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, W) :=
  SchwartzMap.mkCLM (fun u ↦ profile c u) (fun u v ζ ↦ profile_add_right hc u v ζ)
    (fun c' u _ ↦ profile_smul_right c' u _) (fun u ↦ contDiff_profile hc u)
    (fun p ↦ exists_bound_of_isControlled p.1 p.2 fun w ↦
      isControlled_prod_mul_norm_iteratedFDeriv_profile p.2 p.1 w hc)

private lemma profileCLM_apply (c : Symbol n V W m) (hc : c.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (ζ : CoordinateSpace n) :
    profileCLM c hc u ζ = 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (u y)) ζ := by
  -- `SchwartzMap.mkCLM` evaluates to the function it is built from
  rw [Real.fourier_eq]
  rfl

end Bounds

/-! ### The right quantization on Schwartz space -/

section CLM

/-- **Schwartz mapping of the right quantization.** The right quantization
`u ↦ (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ` of a symbol `c` whose estimates are uniform
in the position, as a continuous linear map from Schwartz space to Schwartz space. It is defined
on the Fourier side: the Fourier transform of `Op_R(c) u` at `ζ` is that of `y ↦ c(y, 2πζ) u(y)`
(`TauCeti.Symbol.fourier_quantizeRightUniformCLM`). -/
def quantizeRightUniformCLM (c : Symbol n V W m) (hc : c.IsUniform) :
    𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, W) :=
  FourierTransform.fourierInvCLM ℂ 𝓢(CoordinateSpace n, W) ∘L profileCLM c hc

/-- The Fourier transform of `Op_R(c) u` at `ζ` is the Fourier transform of `y ↦ c(y, 2πζ) u(y)`
at `ζ`. -/
theorem fourier_quantizeRightUniformCLM [CompleteSpace W] (c : Symbol n V W m) (hc : c.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (ζ : CoordinateSpace n) :
    𝓕 (quantizeRightUniformCLM c hc u) ζ = 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (u y)) ζ := by
  rw [quantizeRightUniformCLM, ContinuousLinearMap.comp_apply,
    FourierTransform.fourierInvCLM_apply, FourierTransform.fourier_fourierInv_eq,
    profileCLM_apply]

/-- **The right quantization.** `Op_R(c) u (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) u(y)) (ζ) dζ`,
which in angular frequency is `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ`. -/
theorem quantizeRightUniformCLM_apply (c : Symbol n V W m) (hc : c.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeRightUniformCLM c hc u x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (u y)) ζ := by
  rw [quantizeRightUniformCLM, ContinuousLinearMap.comp_apply,
    FourierTransform.fourierInvCLM_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp_rw [profileCLM_apply]

/-- The right quantization is additive in the symbol. -/
theorem quantizeRightUniformCLM_add {c c' : Symbol n V W m} (hc : c.IsUniform)
    (hc' : c'.IsUniform) :
    quantizeRightUniformCLM (c + c') (hc.add hc') =
      quantizeRightUniformCLM c hc + quantizeRightUniformCLM c' hc' := by
  have h : profileCLM (c + c') (hc.add hc') = profileCLM c hc + profileCLM c' hc' := by
    ext u ζ
    exact profile_add_left hc hc' u ζ
  rw [quantizeRightUniformCLM, quantizeRightUniformCLM, quantizeRightUniformCLM, h,
    ContinuousLinearMap.comp_add]

/-- The right quantization is homogeneous in the symbol. -/
theorem quantizeRightUniformCLM_smul {c : Symbol n V W m} (hc : c.IsUniform) (a : ℂ) :
    quantizeRightUniformCLM (a • c) (hc.smul a) = a • quantizeRightUniformCLM c hc := by
  have h : profileCLM (a • c) (hc.smul a) = a • profileCLM c hc := by
    ext u ζ
    exact profile_smul_left a u ζ
  rw [quantizeRightUniformCLM, quantizeRightUniformCLM, h, ContinuousLinearMap.comp_smul]

/-- The zero symbol right quantizes to zero. -/
@[simp]
theorem quantizeRightUniformCLM_zero (h : (0 : Symbol n V W m).IsUniform) :
    quantizeRightUniformCLM 0 h = 0 := by
  simpa using quantizeRightUniformCLM_smul h 0

/-- The right quantization does not depend on the order at which a symbol is considered. -/
theorem quantizeRightUniformCLM_inclusion {m' : ℝ} {c : Symbol n V W m} (hc : c.IsUniform)
    (h : m ≤ m') :
    quantizeRightUniformCLM (inclusion h c) (hc.inclusion h) = quantizeRightUniformCLM c hc := by
  ext u x
  simp [quantizeRightUniformCLM_apply]

end CLM

end Symbol

end TauCeti
