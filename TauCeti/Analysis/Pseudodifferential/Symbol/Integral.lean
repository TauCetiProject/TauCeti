/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Integrals of continuous families of symbols

Let `T` be a compact space with a finite Borel measure `μ`, and let `t ↦ a_t` be a family of
symbols of order `m` that is continuous for the symbol topology of
`TauCeti.Symbol.instTopologicalSpace`. Its integral

`(∫ a dμ)(x, ξ) = ∫ a_t(x, ξ) dμ(t)`

is again a symbol of order `m` (`TauCeti.Symbol.integral`). Since `T` is compact, every symbol
seminorm `p_{K,α,β}(a_t)` is bounded independently of `t`, so the mixed derivatives of the
coefficients are dominated uniformly in `t`; the coefficient integral may then be differentiated
under the integral sign to every order, and

`∂_x^α ∂_ξ^β (∫ a dμ)(x, ξ) = ∫ ∂_x^α ∂_ξ^β a_t(x, ξ) dμ(t)`

(`TauCeti.Symbol.mixedDeriv_coefficient_integral`). The seminorms of the integral satisfy
`p_{K,α,β}(∫ a dμ) ≤ μ(T) sup_t p_{K,α,β}(a_t)` (`TauCeti.Symbol.seminorm_integral_le`).

The main application is averaging over a compact group `G` with a finite left-invariant measure,
such as the normalized Haar measure. If `G` acts on the fibres `V` and `W` by continuous
representations `σ_V` and `σ_W`, the average `TauCeti.Symbol.average μ σ_V σ_W a` of a symbol `a`
has coefficient `∫ σ_W(g) ∘ a(x, ξ) ∘ σ_V(g)⁻¹ dμ(g)`. It is a symbol of the same order whose
seminorms are controlled by those of `a` and the bounds of the representations
(`TauCeti.Symbol.seminorm_average_le`). Its coefficients are invariant under conjugation by the
action (`TauCeti.Symbol.comp_coefficient_average_comp`), and for a probability measure it fixes
the invariant symbols (`TauCeti.Symbol.average_eq_self`), so it is a linear projection onto them
(`TauCeti.Symbol.average_average`). Here the group acts only on the fibres; it acts trivially on
the positions and frequencies.

The conjugates `g ↦ σ_W(g) ∘ a ∘ σ_V(g)⁻¹` form a continuous family of symbols because
composition of symbols is jointly continuous (`TauCeti.Symbol.continuous_comp`) and the constant
symbol `σ(g)` depends continuously on `σ(g)` (`TauCeti.Symbol.constCLM`).

## Main declarations

* `TauCeti.Symbol.integral`: the integral of a continuous family of symbols of order `m`, with its
  coefficient `TauCeti.Symbol.coefficient_integral` and mixed derivatives
  `TauCeti.Symbol.mixedDeriv_coefficient_integral`;
* `TauCeti.Symbol.seminorm_integral_le`: the uniform seminorm bound;
* `TauCeti.Symbol.spatialDeriv_integral`, `TauCeti.Symbol.frequencyDeriv_integral`: derivatives
  commute with the integral;
* `TauCeti.Symbol.integral_add`, `TauCeti.Symbol.integral_smul`, `TauCeti.Symbol.integral_const`:
  linearity, and the integral of a constant family;
* `TauCeti.Symbol.average`, with `TauCeti.Symbol.coefficient_average`,
  `TauCeti.Symbol.average_add`, `TauCeti.Symbol.average_smul`,
  `TauCeti.Symbol.seminorm_average_le`, `TauCeti.Symbol.comp_coefficient_average_comp`,
  `TauCeti.Symbol.average_eq_smul`, `TauCeti.Symbol.average_eq_self` and
  `TauCeti.Symbol.average_average`: averaging over a compact group.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5, (5.5)–(5.6): averaging pseudodifferential operators over a compact group.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Definition 7.8.1, for
  the symbol seminorms.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open TopologicalSpace (Compacts)
open scoped ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### First derivatives of the coefficients -/

/-- The value `a ↦ a(p)` of a symbol at a point is continuous in the symbol. -/
private theorem continuous_coefficient_apply (p : CoordinateSpace n × CoordinateSpace n) :
    Continuous fun a : Symbol n V W m => a.coefficient p := by
  simpa using continuous_mixedDeriv (n := n) (V := V) (W := W) (m := m) [] [] p.1 p.2

/-- The `j`-th position coordinate `(x, ξ) ↦ x_j`. -/
private def coordFst (j : Fin n) : CoordinateSpace n × CoordinateSpace n →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The `j`-th frequency coordinate `(x, ξ) ↦ ξ_j`. -/
private def coordSnd (j : Fin n) : CoordinateSpace n × CoordinateSpace n →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The derivative with the coordinate derivatives `X j` in position and `Ξ j` in frequency. -/
private def coordDeriv (X Ξ : Fin n → V →L[ℂ] W) :
    CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W :=
  ∑ j, (coordFst j).smulRight (X j) + ∑ j, (coordSnd j).smulRight (Ξ j)

private theorem coordDeriv_apply (X Ξ : Fin n → V →L[ℂ] W)
    (v : CoordinateSpace n × CoordinateSpace n) :
    coordDeriv X Ξ v = ∑ j, v.1 j • X j + ∑ j, v.2 j • Ξ j := by
  simp [coordDeriv, coordFst, coordSnd]

/-- The derivative of the coefficient of a symbol in terms of its first spatial and frequency
derivatives. -/
private theorem fderiv_coefficient (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ a.coefficient p = coordDeriv (fun j => (spatialDeriv j a).coefficient p)
      (fun j => (frequencyDeriv j a).coefficient p) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [fderiv_apply_eq_sum_coordinateDeriv
    (a.contDiff_coefficient.differentiable (by simp) p) v, coordDeriv_apply]
  obtain ⟨x, ξ⟩ := p
  simp only [coefficient_spatialDeriv, coefficient_frequencyDeriv]

section Integral

variable {T : Type*} [TopologicalSpace T]

/-- The family of spatial derivatives `t ↦ ∂_{x_j} a_t`. -/
private def spatialDerivFamily (j : Fin n) (f : C(T, Symbol n V W m)) :
    C(T, Symbol n V W m) :=
  ⟨fun t => spatialDeriv j (f t), (continuous_spatialDeriv j).comp f.continuous⟩

@[simp]
private theorem spatialDerivFamily_apply (j : Fin n) (f : C(T, Symbol n V W m)) (t : T) :
    spatialDerivFamily j f t = spatialDeriv j (f t) := (rfl)

/-- The family of frequency derivatives `t ↦ ∂_{ξ_j} a_t`. -/
private def frequencyDerivFamily (j : Fin n) (f : C(T, Symbol n V W m)) :
    C(T, Symbol n V W (m - 1)) :=
  ⟨fun t => frequencyDeriv j (f t), (continuous_frequencyDeriv j).comp f.continuous⟩

@[simp]
private theorem frequencyDerivFamily_apply (j : Fin n) (f : C(T, Symbol n V W m)) (t : T) :
    frequencyDerivFamily j f t = frequencyDeriv j (f t) := (rfl)

variable [CompactSpace T]

/-- On a compact parameter space each seminorm of a continuous family of symbols is bounded. -/
private theorem exists_seminorm_le (f : C(T, Symbol n V W m)) (K : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) : ∃ C, ∀ t, Symbol.seminorm K α β (f t) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((withSeminorms.continuous_seminorm (K, α, β)).comp f.continuous).continuousOn
  exact ⟨C, fun t => (le_abs_self _).trans (by simpa using hC t (mem_univ t))⟩

/-- The coefficients of a continuous family of symbols are bounded on compact sets, uniformly in
the parameter. -/
private theorem exists_norm_coefficient_le_of_continuous (f : C(T, Symbol n V W m))
    {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, ∀ t, ∀ p ∈ K, ‖(f t).coefficient p‖ ≤ C := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    ((continuous_const.add (continuous_snd.norm.pow 2)).rpow_const
      (p := m / 2) fun _ =>
        Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').continuousOn
  let K₁ : Compacts (CoordinateSpace n) := ⟨_, hK.image continuous_fst⟩
  obtain ⟨C, hC⟩ := exists_seminorm_le f K₁ [] []
  refine ⟨max C 0 * R, fun t p hp => ?_⟩
  calc ‖(f t).coefficient p‖ ≤ Symbol.seminorm K₁ [] [] (f t) * (1 + ‖p.2‖ ^ 2) ^ (m / 2) :=
        norm_coefficient_le_seminorm K₁ (f t) (mem_image_of_mem _ hp) p.2
    _ ≤ max C 0 * R := by
        gcongr
        · exact (hC t).trans (le_max_left _ _)
        · exact (le_abs_self _).trans (hR p hp)

variable [MeasurableSpace T] [OpensMeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ]

/-- A continuous function on the compact space `T` is integrable. Stating this for the norm
topology of `E` lets unification identify it with `ContinuousLinearMap.topologicalSpace` for the
derivative families below, where instance search on those spaces of maps fails. -/
private theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {g : T → E}
    (hg : Continuous g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport (.of_compactSpace g)

variable [CompleteSpace W]

/-- The integral of the coefficients of a family of symbols. -/
private def integralCoeff (f : C(T, Symbol n V W m))
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∫ t, (f t).coefficient p ∂μ

/-- **Differentiation under the integral sign.** The coefficient integral of a continuous family
of symbols is differentiable, with the integrals of the first derivatives as partial
derivatives. -/
private theorem hasFDerivAt_integralCoeff (f : C(T, Symbol n V W m))
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (integralCoeff μ f)
      (coordDeriv (fun j => integralCoeff μ (spatialDerivFamily j f) p₀)
        (fun j => integralCoeff μ (frequencyDerivFamily j f) p₀)) p₀ := by
  -- Bounds for the first derivatives on the unit ball around `p₀`, uniform in `t`, dominate the
  -- derivatives of the integrand; the integral of the derivative is then rewritten in terms of
  -- the coefficient integrals of the derivative families.
  have hK : IsCompact (Metric.closedBall p₀ 1) := isCompact_closedBall p₀ 1
  choose X hX using fun j => exists_norm_coefficient_le_of_continuous (spatialDerivFamily j f) hK
  choose Ξ hΞ using fun j => exists_norm_coefficient_le_of_continuous (frequencyDerivFamily j f) hK
  have hcont (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun t => (f t).coefficient p :=
    (continuous_coefficient_apply p).comp f.continuous
  have cX (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun t => (spatialDeriv j (f t)).coefficient p :=
    (continuous_coefficient_apply p).comp (spatialDerivFamily j f).continuous
  have cΞ (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun t => (frequencyDeriv j (f t)).coefficient p :=
    (continuous_coefficient_apply p).comp (frequencyDerivFamily j f).continuous
  have hD (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous fun t => fderiv ℝ (f t).coefficient p := by
    simp_rw [fderiv_coefficient]
    refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun j _ => ?_)
    · exact (ContinuousLinearMap.smulRightL ℝ _ _ (coordFst j)).continuous.comp (cX j p)
    · exact (ContinuousLinearMap.smulRightL ℝ _ _ (coordSnd j)).continuous.comp (cΞ j p)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun p t => (f t).coefficient p) (F' := fun p t => fderiv ℝ (f t).coefficient p)
    (bound := fun _ => ∑ j, X j + ∑ j, Ξ j) (Metric.closedBall_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p => (hcont p).aestronglyMeasurable_of_compactSpace)
    (integrable_of_continuous μ (hcont p₀))
    (integrable_of_continuous μ (hD p₀)).aestronglyMeasurable
    (ae_of_all _ fun t p hp => ?_) (integrable_const _) (ae_of_all _ fun t p _ =>
      ((f t).contDiff_coefficient.differentiable (by simp) p).hasFDerivAt)
  · refine key.congr_fderiv ?_
    simp_rw [fderiv_coefficient, coordDeriv]
    rw [integral_add (integrable_finsetSum _ fun j _ => integrable_of_continuous μ
        ((ContinuousLinearMap.smulRightL ℝ _ _ (coordFst j)).continuous.comp (cX j p₀)))
      (integrable_finsetSum _ fun j _ => integrable_of_continuous μ
        ((ContinuousLinearMap.smulRightL ℝ _ _ (coordSnd j)).continuous.comp (cΞ j p₀))),
      integral_finsetSum _ fun j _ => integrable_of_continuous μ
        ((ContinuousLinearMap.smulRightL ℝ _ _ (coordFst j)).continuous.comp (cX j p₀)),
      integral_finsetSum _ fun j _ => integrable_of_continuous μ
        ((ContinuousLinearMap.smulRightL ℝ _ _ (coordSnd j)).continuous.comp (cΞ j p₀))]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_
    · exact (ContinuousLinearMap.smulRightL ℝ _ _ (coordFst j)).integral_comp_comm
        (integrable_of_continuous μ (cX j p₀))
    · exact (ContinuousLinearMap.smulRightL ℝ _ _ (coordSnd j)).integral_comp_comm
        (integrable_of_continuous μ (cΞ j p₀))
  · rw [fderiv_coefficient]
    refine (ContinuousLinearMap.opNorm_le_of_apply_eq_sum _ _ _
      fun v => coordDeriv_apply _ _ v).trans (add_le_add ?_ ?_) <;>
      exact Finset.sum_le_sum fun j _ => by first | exact hX j t p hp | exact hΞ j t p hp

private theorem contDiff_integralCoeff_nat (k : ℕ) :
    ∀ {m : ℝ} (f : C(T, Symbol n V W m)), ContDiff ℝ k (integralCoeff μ f) := by
  induction k with
  | zero =>
      intro m f
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p =>
        (hasFDerivAt_integralCoeff μ f p).continuousAt)
  | succ k ih =>
      intro m f
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, hasFDerivAt_integralCoeff μ f⟩
      refine (ContDiff.sum fun j _ => ?_).add (ContDiff.sum fun j _ => ?_)
      · exact (ContinuousLinearMap.smulRightL ℝ _ _ (coordFst j)).contDiff.comp
          (ih (spatialDerivFamily j f))
      · exact (ContinuousLinearMap.smulRightL ℝ _ _ (coordSnd j)).contDiff.comp
          (ih (frequencyDerivFamily j f))

private theorem contDiff_integralCoeff (f : C(T, Symbol n V W m)) :
    ContDiff ℝ ∞ (integralCoeff μ f) :=
  contDiff_infty.2 fun k => contDiff_integralCoeff_nat μ k f

private theorem coordinateDeriv_fst_integralCoeff (f : C(T, Symbol n V W m)) (j : Fin n) :
    (fun p : CoordinateSpace n × CoordinateSpace n =>
      coordinateDeriv [j] (fun y => integralCoeff μ f (y, p.2)) p.1) =
      integralCoeff μ (spatialDerivFamily j f) := by
  funext p
  have h := hasFDerivAt_integralCoeff μ f p
  rw [coordinateDeriv_fst_eq_fderiv h.differentiableAt, h.fderiv, coordDeriv_apply]
  simp [PiLp.single_apply]

private theorem coordinateDeriv_snd_integralCoeff (f : C(T, Symbol n V W m)) (j : Fin n) :
    (fun p : CoordinateSpace n × CoordinateSpace n =>
      coordinateDeriv [j] (fun η => integralCoeff μ f (p.1, η)) p.2) =
      integralCoeff μ (frequencyDerivFamily j f) := by
  funext p
  have h := hasFDerivAt_integralCoeff μ f p
  rw [coordinateDeriv_snd_eq_fderiv h.differentiableAt, h.fderiv, coordDeriv_apply]
  simp [PiLp.single_apply]

private theorem mixedDeriv_nil_integralCoeff (α : List (Fin n)) :
    ∀ {m : ℝ} (f : C(T, Symbol n V W m)) (x ξ : CoordinateSpace n),
      mixedDeriv α [] (integralCoeff μ f) x ξ = ∫ t, mixedDeriv α [] (f t).coefficient x ξ ∂μ := by
  induction α using List.reverseRecOn with
  | nil => intro m f x ξ; simp [integralCoeff]
  | append_singleton α j ih =>
      intro m f x ξ
      rw [← mixedDeriv_coordinateDeriv_fst (contDiff_integralCoeff μ f),
        coordinateDeriv_fst_integralCoeff, ih]
      simp

private theorem mixedDeriv_integralCoeff (α β : List (Fin n)) :
    ∀ {m : ℝ} (f : C(T, Symbol n V W m)) (x ξ : CoordinateSpace n),
      mixedDeriv α β (integralCoeff μ f) x ξ = ∫ t, mixedDeriv α β (f t).coefficient x ξ ∂μ := by
  induction β using List.reverseRecOn with
  | nil => exact mixedDeriv_nil_integralCoeff μ α
  | append_singleton β j ih =>
      intro m f x ξ
      rw [← mixedDeriv_coordinateDeriv_snd, coordinateDeriv_snd_integralCoeff, ih]
      simp [mixedDeriv_frequencyDeriv]

/-- The integral `∫ a_t dμ(t)` of a continuous family `t ↦ a_t` of symbols of order `m` over a
compact space with a finite measure, again a symbol of order `m`, with coefficient
`(x, ξ) ↦ ∫ a_t(x, ξ) dμ(t)`. -/
def integral (f : C(T, Symbol n V W m)) : Symbol n V W m where
  coefficient := integralCoeff μ f
  contDiff_coefficient := contDiff_integralCoeff μ f
  exists_bound K hK α β := by
    obtain ⟨C, hC⟩ := exists_seminorm_le f ⟨K, hK⟩ α β
    refine ⟨max C 0 * μ.real univ, by positivity, fun x hx ξ => ?_⟩
    rw [mixedDeriv_integralCoeff, mul_right_comm]
    refine norm_integral_le_of_norm_le_const (ae_of_all _ fun t => ?_)
    refine (le_seminorm ⟨K, hK⟩ α β (f t) hx ξ).trans ?_
    gcongr
    exact (hC t).trans (le_max_left _ _)

@[simp]
theorem coefficient_integral (f : C(T, Symbol n V W m))
    (p : CoordinateSpace n × CoordinateSpace n) :
    (integral μ f).coefficient p = ∫ t, (f t).coefficient p ∂μ := (rfl)

/-- The mixed derivatives of the integral of a family of symbols are the integrals of the mixed
derivatives. -/
theorem mixedDeriv_coefficient_integral (f : C(T, Symbol n V W m)) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (integral μ f).coefficient x ξ =
      ∫ t, mixedDeriv α β (f t).coefficient x ξ ∂μ :=
  mixedDeriv_integralCoeff μ α β f x ξ

/-- **Uniform seminorm bound.** If every member of the family satisfies `p_{K,α,β}(a_t) ≤ C`, then
`p_{K,α,β}(∫ a dμ) ≤ μ(T) C`. -/
theorem seminorm_integral_le (f : C(T, Symbol n V W m)) {K : Compacts (CoordinateSpace n)}
    {α β : List (Fin n)} {C : ℝ} (hC : ∀ t, Symbol.seminorm K α β (f t) ≤ C) :
    Symbol.seminorm K α β (integral μ f) ≤ μ.real univ * C := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · have h0 : integral μ f = 0 := by
      refine Symbol.ext (funext fun p => ?_)
      simp [Measure.eq_zero_of_isEmpty μ]
    rw [h0, map_zero, Measure.eq_zero_of_isEmpty μ]
    simp
  · have hC0 : 0 ≤ C := (apply_nonneg _ _).trans (hC t₀)
    refine seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_
    rw [mixedDeriv_coefficient_integral]
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ fun t =>
      (le_seminorm K α β (f t) hx ξ).trans (mul_le_mul_of_nonneg_right (hC t)
        (rpow_weight_pos ξ _).le))).trans_eq ?_
    ring

/-- The spatial derivative of the integral of a family of symbols is the integral of the spatial
derivatives. -/
theorem spatialDeriv_integral (f : C(T, Symbol n V W m)) (j : Fin n) :
    spatialDeriv j (integral μ f) =
      integral μ ⟨fun t => spatialDeriv j (f t),
        (continuous_spatialDeriv j).comp f.continuous⟩ := by
  refine Symbol.ext (funext fun ⟨x, ξ⟩ => ?_)
  rw [coefficient_spatialDeriv]
  exact congrFun (coordinateDeriv_fst_integralCoeff μ f j) (x, ξ)

/-- The frequency derivative of the integral of a family of symbols is the integral of the
frequency derivatives. -/
theorem frequencyDeriv_integral (f : C(T, Symbol n V W m)) (j : Fin n) :
    frequencyDeriv j (integral μ f) =
      integral μ ⟨fun t => frequencyDeriv j (f t),
        (continuous_frequencyDeriv j).comp f.continuous⟩ := by
  refine Symbol.ext (funext fun ⟨x, ξ⟩ => ?_)
  rw [coefficient_frequencyDeriv]
  exact congrFun (coordinateDeriv_snd_integralCoeff μ f j) (x, ξ)

theorem integral_add (f g : C(T, Symbol n V W m)) :
    integral μ (f + g) = integral μ f + integral μ g := by
  refine Symbol.ext (funext fun p => ?_)
  simpa using MeasureTheory.integral_add
    (integrable_of_continuous μ ((continuous_coefficient_apply p).comp f.continuous))
    (integrable_of_continuous μ ((continuous_coefficient_apply p).comp g.continuous))

theorem integral_smul (c : ℂ) (f : C(T, Symbol n V W m)) :
    integral μ (c • f) = c • integral μ f := by
  refine Symbol.ext (funext fun p => ?_)
  simpa using MeasureTheory.integral_smul c fun t => (f t).coefficient p

/-- The integral of a constant family is the symbol multiplied by the total mass. -/
theorem integral_const (a : Symbol n V W m) :
    integral μ (ContinuousMap.const T a) = (μ.real univ : ℂ) • a := by
  refine Symbol.ext (funext fun p => ?_)
  rw [coefficient_integral]
  simp only [ContinuousMap.const_apply]
  rw [MeasureTheory.integral_const, coefficient_smul, Pi.smul_apply, Complex.coe_smul]

end Integral

section Average

/-! ### Averaging over a compact group -/

/-- Conjugation `T ↦ S ∘ T ∘ R` of the coefficients. -/
private def conjCLM (S : W →L[ℂ] W) (R : V →L[ℂ] V) : (V →L[ℂ] W) →L[ℂ] V →L[ℂ] W :=
  (ContinuousLinearMap.compL ℂ V W W S).comp ((ContinuousLinearMap.compL ℂ V V W).flip R)

@[simp]
private theorem conjCLM_apply (S : W →L[ℂ] W) (R : V →L[ℂ] V) (T : V →L[ℂ] W) :
    conjCLM S R T = S ∘L T ∘L R := (rfl)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]
  (σV : G →ₜ* (V →L[ℂ] V)) (σW : G →ₜ* (W →L[ℂ] W))

/-- The family of conjugates `g ↦ σ_W(g) ∘ a ∘ σ_V(g)⁻¹` of a symbol. -/
private def conjFamily (a : Symbol n V W m) : C(G, Symbol n V W m) :=
  ⟨fun g => inclusion (by simp) ((const (σW g)).comp (a.comp (const (σV g⁻¹)))), by
    refine (continuous_inclusion _).comp ?_
    exact Continuous.symbol_comp (b := fun g => const (σW g))
      (((constCLM n W W).continuous.comp σW.continuous).congr fun g => constCLM_apply _)
      (Continuous.symbol_comp (b := fun _ => a) continuous_const
        (((constCLM n V V).continuous.comp (σV.continuous.comp continuous_inv)).congr
          fun g => constCLM_apply _))⟩

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem coefficient_conjFamily (a : Symbol n V W m) (g : G) :
    (conjFamily σV σW a g).coefficient = conjCLM (σW g) (σV g⁻¹) ∘ a.coefficient := by
  funext p
  simp [conjFamily]

private theorem integrable_conj (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) μ :=
  integrable_of_continuous μ ((continuous_coefficient_apply p).comp (conjFamily σV σW a).continuous
    |>.congr fun g => by simp [coefficient_conjFamily])

variable [CompleteSpace W]

/-- The average `∫ σ_W(g) ∘ a ∘ σ_V(g)⁻¹ dμ(g)` of a symbol over a compact group `G` acting on the
fibres `V` and `W` by continuous representations `σ_V` and `σ_W`, a symbol of the same order. -/
def average (a : Symbol n V W m) : Symbol n V W m :=
  integral μ (conjFamily σV σW a)

@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ σV σW a).coefficient p = ∫ g, σW g ∘L a.coefficient p ∘L σV g⁻¹ ∂μ := by
  simp [average, coefficient_conjFamily]

theorem average_add (a b : Symbol n V W m) :
    average μ σV σW (a + b) = average μ σV σW a + average μ σV σW b := by
  refine Symbol.ext (funext fun p => ?_)
  simpa [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using
    MeasureTheory.integral_add (integrable_conj μ σV σW a p) (integrable_conj μ σV σW b p)

theorem average_smul (c : ℂ) (a : Symbol n V W m) :
    average μ σV σW (c • a) = c • average μ σV σW a := by
  refine Symbol.ext (funext fun p => ?_)
  simpa [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
    MeasureTheory.integral_smul c fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹

/-- If the representations are bounded by `A` and `B`, then
`p_{K,α,β}(average a) ≤ μ(G) A B p_{K,α,β}(a)`. -/
theorem seminorm_average_le (a : Symbol n V W m) {K : Compacts (CoordinateSpace n)}
    {α β : List (Fin n)} {A B : ℝ} (hA : ∀ g, ‖σW g‖ ≤ A) (hB : ∀ g, ‖σV g‖ ≤ B) :
    Symbol.seminorm K α β (average μ σV σW a) ≤
      μ.real univ * (A * B * Symbol.seminorm K α β a) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  refine seminorm_integral_le μ _ fun g => seminorm_le_bound K α β _ (by positivity)
    fun x hx ξ => ?_
  rw [coefficient_conjFamily, show conjCLM (σW g) (σV g⁻¹) ∘ a.coefficient =
      (conjCLM (σW g) (σV g⁻¹)).restrictScalars ℝ ∘ a.coefficient from rfl,
    ContinuousLinearMap.mixedDeriv_comp_left _ a.contDiff_coefficient,
    ContinuousLinearMap.coe_restrictScalars', conjCLM_apply]
  calc ‖σW g ∘L mixedDeriv α β a.coefficient x ξ ∘L σV g⁻¹‖
      ≤ ‖σW g‖ * (‖mixedDeriv α β a.coefficient x ξ‖ * ‖σV g⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ A * ((Symbol.seminorm K α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) * B) := by
        gcongr
        exacts [hA g, le_seminorm K α β a hx ξ, hB g⁻¹]
    _ = A * B * Symbol.seminorm K α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by ring

/-- **The average is invariant.** For a left-invariant measure, conjugating the coefficients of the
average by the action of any `h ∈ G` returns them. -/
theorem comp_coefficient_average_comp [μ.IsMulLeftInvariant] (a : Symbol n V W m) (h : G)
    (p : CoordinateSpace n × CoordinateSpace n) :
    σW h ∘L (average μ σV σW a).coefficient p ∘L σV h⁻¹ = (average μ σV σW a).coefficient p := by
  rw [coefficient_average, ← conjCLM_apply,
    ← (conjCLM (σW h) (σV h⁻¹)).integral_comp_comm (integrable_conj μ σV σW a p)]
  have hg (g : G) : conjCLM (σW h) (σV h⁻¹) (σW g ∘L a.coefficient p ∘L σV g⁻¹) =
      σW (h * g) ∘L a.coefficient p ∘L σV (h * g)⁻¹ := by
    simp only [conjCLM_apply, map_mul, mul_inv_rev, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  simp_rw [hg]
  exact integral_mul_left_eq_self (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) h

/-- The average of an invariant symbol is the symbol multiplied by the total mass. -/
theorem average_eq_smul (a : Symbol n V W m)
    (ha : ∀ g p, σW g ∘L a.coefficient p ∘L σV g⁻¹ = a.coefficient p) :
    average μ σV σW a = (μ.real univ : ℂ) • a := by
  refine Symbol.ext (funext fun p => ?_)
  simp only [coefficient_average, ha]
  rw [MeasureTheory.integral_const, coefficient_smul, Pi.smul_apply, Complex.coe_smul]

/-- For a probability measure the average fixes the invariant symbols. -/
theorem average_eq_self [IsProbabilityMeasure μ] (a : Symbol n V W m)
    (ha : ∀ g p, σW g ∘L a.coefficient p ∘L σV g⁻¹ = a.coefficient p) :
    average μ σV σW a = a := by
  simp [average_eq_smul μ σV σW a ha]

/-- For a left-invariant probability measure, such as the normalized Haar measure, averaging is a
projection onto the invariant symbols. -/
theorem average_average [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (a : Symbol n V W m) :
    average μ σV σW (average μ σV σW a) = average μ σV σW a :=
  average_eq_self μ σV σW _ (comp_coefficient_average_comp μ σV σW a)

end Average

end Symbol

end TauCeti
