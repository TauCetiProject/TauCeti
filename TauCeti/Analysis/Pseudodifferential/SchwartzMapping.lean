/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization

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

private lemma IsControlled.sum {ι : Type*} (s : Finset ι)
    {Φ : ι → 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ}
    (h : ∀ i ∈ s, IsControlled (Φ i)) :
    IsControlled fun u x ↦ ∑ i ∈ s, Φ i u x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, continuous_const, fun u x ↦ by simp⟩
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

/-- The Schwartz seminorm estimates for the quantization of a uniform symbol. -/
private lemma exists_bound_quantizeSchwartzValue {a : Symbol n V W m} (ha : a.IsUniform)
    (k N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (u : 𝓢(CoordinateSpace n, V)) x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ (CoordinateSpace n) V) u := by
  obtain ⟨q, hq, hle⟩ := IsControlled.sum (Finset.univ : Finset (Fin k → Fin n))
    fun w _ ↦ isControlled_prod_mul_norm_iteratedFDeriv N k w ha
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ _ _) q hq
  refine ⟨s, C, C.2, fun u x ↦ ?_⟩
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ ≤
        (∑ j, |x j|) ^ k * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ := by
        gcongr
        -- expand `x` in the standard basis
        set b := EuclideanSpace.basisFun (Fin n) ℝ
        calc ‖x‖ = ‖∑ j, x j • b j‖ := by
              congr 1
              exact (b.sum_repr x).symm
          _ ≤ ∑ j, ‖x j • b j‖ := norm_sum_le _ _
          _ = ∑ j, |x j| := by simp [norm_smul, b.orthonormal.1]
    _ = ∑ w : Fin k → Fin n,
          |∏ i, x (w i)| * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ := by
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
      obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
      exact quantizeSchwartzValue_add_right
        (a.continuous_coefficient_slice x).aestronglyMeasurable (hC x rfl) u v)
    (fun c u _ ↦ quantizeSchwartzValue_smul_right c u)
    (fun u ↦ a.contDiff_quantizeSchwartzValue u)
    (fun p ↦ exists_bound_quantizeSchwartzValue ha p.1 p.2)

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
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  obtain ⟨C', -, hC'⟩ := b.exists_bound_coefficient {x} isCompact_singleton
  simpa using quantizeSchwartzValue_add_left
    (a.continuous_coefficient_slice x).aestronglyMeasurable (hC x rfl)
    (b.continuous_coefficient_slice x).aestronglyMeasurable (hC' x rfl) u

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

end Symbol

end TauCeti
