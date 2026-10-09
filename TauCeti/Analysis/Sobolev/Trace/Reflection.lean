/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.HalfSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Even reflection across a hyperplane preserves weak differentiability

Let `H = normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, and let
`ρ (t, y) = (2a - t, y)` be the reflection in its boundary hyperplane `{a} × E`. If `w` is weakly
differentiable on `H` with weak gradient `G`, and `w` and `G` are locally integrable up to the
boundary (we extend them by zero off `H`), then the even reflection

`x ↦ w x + w (ρ x)`

is weakly differentiable on the whole space, with weak gradient `x ↦ G x + R (G (ρ x))`, where
`R (s, z) = (-s, z)` is the linear part of `ρ`. No boundary condition on `w` is needed: the
reflection is what makes the two one-sided traces match. This is the analytic content of the
extension operator `W^{1,p}(H) → W^{1,p}(ℝ × E)` constructed in
`TauCeti.Analysis.Sobolev.Trace.Extension`.

The proof follows H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Lemma 9.2. A test function `φ` on the whole space is tested against the even
reflection; after the change of variables `x ↦ ρ x` this becomes the pairing of `w` on `H` with
`χ = φ ± φ ∘ ρ`, where the sign is `+` for directions tangent to the boundary and `-` for the
normal direction. Such a `χ` is not supported inside `H`, so it is multiplied by cutoffs
`η_n (x.fst)` vanishing near the boundary. In tangential directions the cutoff commutes with
differentiation. In the normal direction `χ` vanishes on the boundary, so `|χ| ≤ M (x.fst - a)`
there, which exactly compensates the size `O(n)` of `η_n'` on its support of width `O(1/n)`.
Dominated convergence then passes to the limit.

## Main declarations

* `TauCeti.normalLinearReflection`: the linear reflection `(t, y) ↦ (-t, y)`, which is Mathlib's
  `Submodule.reflection` in the hyperplane `{0} × E`.
* `TauCeti.normalReflection`: the affine reflection `(t, y) ↦ (2a - t, y)` in `{a} × E`, with
  its measure preservation and derivative.
* `TauCeti.HasWeakFDerivOn.add_comp_normalReflection`: the even reflection of a weakly
  differentiable function on the half-space is weakly differentiable on the whole space.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 9.2.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ContDiff Topology Distributions

namespace TauCeti

/-! ### The reflection in the boundary hyperplane -/

section Reflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- The linear reflection `(t, y) ↦ (-t, y)` of the Euclidean product `ℝ × E` in the hyperplane
`{0} × E`, the kernel of the normal coordinate. It transforms the gradient of a function under
`TauCeti.normalReflection`. -/
def normalLinearReflection : WithLp 2 (ℝ × E) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) :=
  (LinearMap.ker (WithLp.fstₗ 2 ℝ ℝ E)).reflection

/-- The linear normal reflection negates the normal coordinate. -/
@[simp]
theorem normalLinearReflection_apply (x : WithLp 2 (ℝ × E)) :
    normalLinearReflection E x = WithLp.toLp 2 (-x.fst, x.snd) := by
  have h : (LinearMap.ker (WithLp.fstₗ 2 ℝ ℝ E)).starProjection x =
      WithLp.toLp 2 (0, x.snd) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · simp
    · intro w hw
      simp only [LinearMap.mem_ker, WithLp.fstₗ_apply] at hw
      cases x
      simp [← WithLp.toLp_sub, WithLp.prod_inner_apply, hw]
  rw [normalLinearReflection, Submodule.reflection_apply, h]
  obtain ⟨⟨t, y⟩⟩ := x
  rw [two_smul, ← WithLp.toLp_add, ← WithLp.toLp_sub]
  simp

/-- The linear normal reflection is an involution. -/
theorem normalLinearReflection_normalLinearReflection (x : WithLp 2 (ℝ × E)) :
    normalLinearReflection E (normalLinearReflection E x) = x :=
  Submodule.reflection_reflection _ x

/-- The linear normal reflection is its own inverse. -/
@[simp]
theorem normalLinearReflection_symm : (normalLinearReflection E).symm = normalLinearReflection E :=
  Submodule.reflection_symm

/-- The linear normal reflection is self-adjoint. -/
theorem inner_normalLinearReflection_left (x y : WithLp 2 (ℝ × E)) :
    inner ℝ (normalLinearReflection E x) y = inner ℝ x (normalLinearReflection E y) := by
  rw [← (normalLinearReflection E).inner_map_map, normalLinearReflection_normalLinearReflection]

variable (E) in
/-- The reflection `(t, y) ↦ (2a - t, y)` of the Euclidean product `ℝ × E` in the hyperplane
`{a} × E`, the boundary of `TauCeti.normalHalfSpace a`. Its linear part is
`TauCeti.normalLinearReflection`. -/
def normalReflection (a : ℝ) : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) :=
  (normalLinearReflection E).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ (WithLp 2 (ℝ × E)) (WithLp.toLp 2 (2 * a, 0)))

/-- The normal reflection in `{a} × E` replaces the normal coordinate `t` by `2a - t`. -/
@[simp]
theorem normalReflection_apply (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    normalReflection E a x = WithLp.toLp 2 (2 * a - x.fst, x.snd) := by
  cases x
  simp [normalReflection, vadd_eq_add, ← WithLp.toLp_add, sub_eq_add_neg]

/-- The normal reflection is an involution. -/
theorem normalReflection_normalReflection (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    normalReflection E a (normalReflection E a x) = x := by
  cases x; simp

/-- The normal reflection is its own inverse. -/
@[simp]
theorem normalReflection_symm (a : ℝ) : (normalReflection E a).symm = normalReflection E a :=
  AffineIsometryEquiv.ext fun x =>
    (normalReflection E a).symm_apply_eq.2 (normalReflection_normalReflection a x).symm

/-- The fixed points of the normal reflection in `{a} × E` are the points of that hyperplane. -/
theorem normalReflection_eq_self_iff (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    normalReflection E a x = x ↔ x.fst = a := by
  obtain ⟨⟨t, y⟩⟩ := x
  simp only [normalReflection_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  constructor
  · intro h
    have := congrArg WithLp.fst h
    simp only [WithLp.toLp_fst] at this
    linarith
  · intro h
    rw [h]
    congr 2
    ring

/-- The normal reflection in `{a} × E` exchanges the open half-spaces on either side. -/
theorem normalReflection_mem_normalHalfSpace_iff (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    normalReflection E a x ∈ normalHalfSpace (E := E) a ↔ x.fst < a := by
  simp only [mem_normalHalfSpace, normalReflection_apply]
  constructor <;> intro h <;> linarith

/-- The normal reflection in `{a} × E` is its linear part `TauCeti.normalLinearReflection`
followed by the translation by `(2a, 0)`. -/
theorem normalReflection_eq_add (a : ℝ) :
    (normalReflection E a : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)) =
      fun y => normalLinearReflection E y + WithLp.toLp 2 (2 * a, 0) := by
  funext y
  simp [normalReflection, vadd_eq_add, add_comm]

/-- The derivative of the normal reflection is its linear part. -/
theorem hasFDerivAt_normalReflection (a : ℝ) (x : WithLp 2 (ℝ × E)) :
    HasFDerivAt (normalReflection E a)
      ((normalLinearReflection E).toContinuousLinearEquiv :
        WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) x := by
  rw [normalReflection_eq_add]
  exact (normalLinearReflection E).toContinuousLinearEquiv.hasFDerivAt.add_const _

/-- The normal reflection is smooth. -/
theorem contDiff_normalReflection (a : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (normalReflection E a) := by
  rw [normalReflection_eq_add]
  exact (normalLinearReflection E).toContinuousLinearEquiv.contDiff.add contDiff_const

variable [MeasurableSpace E] [BorelSpace E]

/-- The normal reflection preserves Lebesgue measure. -/
theorem measurePreserving_normalReflection (a : ℝ) :
    MeasurePreserving (normalReflection E a) := by
  rw [normalReflection_eq_add]
  exact (measurePreserving_add_right (volume : Measure (WithLp 2 (ℝ × E)))
    (WithLp.toLp 2 (2 * a, 0))).comp (normalLinearReflection E).measurePreserving

/-- Change of variables by the normal reflection: integrals against Lebesgue measure are
invariant under it. -/
theorem integral_comp_normalReflection (a : ℝ) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : WithLp 2 (ℝ × E) → F) :
    ∫ x, g (normalReflection E a x) = ∫ x, g x :=
  (measurePreserving_normalReflection a).integral_comp
    (normalReflection E a).toHomeomorph.measurableEmbedding g

/-- Precomposition with the normal reflection preserves local integrability. -/
theorem locallyIntegrable_comp_normalReflection (a : ℝ) {F : Type*}
    [NormedAddCommGroup F] {g : WithLp 2 (ℝ × E) → F} (hg : LocallyIntegrable g) :
    LocallyIntegrable fun x => g (normalReflection E a x) :=
  (locallyIntegrable_map_homeomorph (normalReflection E a).toHomeomorph).1 <| by
    rwa [AffineIsometryEquiv.coe_toHomeomorph, (measurePreserving_normalReflection a).map_eq]

end Reflection

/-! ### Cutoffs vanishing near the boundary hyperplane -/

section Cutoff

variable {E : Type*}

/-- The argument `(n + 1) (x.fst - a) - 1` of the `n`-th boundary cutoff. -/
private def cutoffArg (a : ℝ) (n : ℕ) (x : WithLp 2 (ℝ × E)) : ℝ :=
  ((n : ℝ) + 1) * (x.fst - a) - 1

/-- The `n`-th boundary cutoff: smooth, zero when `x.fst ≤ a + 1 / (n + 1)` and one when
`x.fst ≥ a + 2 / (n + 1)`. -/
private def cutoff (a : ℝ) (n : ℕ) (x : WithLp 2 (ℝ × E)) : ℝ :=
  Real.smoothTransition (cutoffArg a n x)

private theorem eventually_lt_cutoffArg {a : ℝ} {x : WithLp 2 (ℝ × E)} (hx : a < x.fst) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c < cutoffArg a n x := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (x.fst - a) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (((tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds).atTop_mul_const
        (sub_pos.2 hx))
  exact h.eventually_gt_atTop c

private theorem eventually_cutoff_eq_one {a : ℝ} {x : WithLp 2 (ℝ × E)} (hx : a < x.fst) :
    ∀ᶠ n : ℕ in atTop, cutoff a n x = 1 :=
  (eventually_lt_cutoffArg hx 1).mono fun _ hn => Real.smoothTransition.one_of_one_le hn.le

private theorem cutoff_nonneg (a : ℝ) (n : ℕ) (x : WithLp 2 (ℝ × E)) : 0 ≤ cutoff a n x :=
  Real.smoothTransition.nonneg _

private theorem cutoff_le_one (a : ℝ) (n : ℕ) (x : WithLp 2 (ℝ × E)) : cutoff a n x ≤ 1 :=
  Real.smoothTransition.le_one _

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_cutoffArg (a : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (cutoffArg (E := E) a n) :=
  (contDiff_const.mul ((WithLp.fstL 2 ℝ ℝ E).contDiff.sub contDiff_const)).sub contDiff_const

private theorem contDiff_cutoff (a : ℝ) (n : ℕ) : ContDiff ℝ ∞ (cutoff (E := E) a n) :=
  Real.smoothTransition.contDiff.comp (contDiff_cutoffArg a n)

private theorem hasFDerivAt_cutoff (a : ℝ) (n : ℕ) (x : WithLp 2 (ℝ × E)) :
    HasFDerivAt (cutoff a n)
      ((deriv Real.smoothTransition (cutoffArg a n x) * ((n : ℝ) + 1)) •
        WithLp.fstL 2 ℝ ℝ E) x := by
  have hℓ : HasFDerivAt (cutoffArg (E := E) a n) (((n : ℝ) + 1) • WithLp.fstL 2 ℝ ℝ E) x :=
    (((WithLp.fstL 2 ℝ ℝ E).hasFDerivAt.sub_const a).const_mul ((n : ℝ) + 1)).sub_const 1
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (cutoffArg a n x)) (cutoffArg a n x) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  exact (hst.comp_hasFDerivAt x hℓ).congr_fderiv (by rw [smul_smul])

/-- The product rule for a cutoff times a differentiable function. -/
private theorem lineDeriv_cutoff_mul (a : ℝ) (n : ℕ) {χ : WithLp 2 (ℝ × E) → ℝ}
    (hχ : Differentiable ℝ χ) (x v : WithLp 2 (ℝ × E)) :
    lineDeriv ℝ (cutoff a n * χ) x v =
      cutoff a n x * fderiv ℝ χ x v +
        χ x * (deriv Real.smoothTransition (cutoffArg a n x) * (((n : ℝ) + 1) * v.fst)) := by
  rw [((hasFDerivAt_cutoff a n x).mul (hχ x).hasFDerivAt).hasLineDerivAt v |>.lineDeriv]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    WithLp.fstL_apply]
  ring

/-- A differentiable function vanishing on the hyperplane `{a} × E`, with derivative bounded by
`M`, is bounded by `M (x.fst - a)` on the side `a ≤ x.fst`. -/
private theorem abs_le_mul_sub_of_eq_zero_on_hyperplane {a M : ℝ} {χ : WithLp 2 (ℝ × E) → ℝ}
    (hχ : Differentiable ℝ χ) (hM : ∀ y, ‖fderiv ℝ χ y‖ ≤ M)
    (hχa : ∀ y : E, χ (WithLp.toLp 2 (a, y)) = 0) {x : WithLp 2 (ℝ × E)} (hx : a ≤ x.fst) :
    |χ x| ≤ M * (x.fst - a) := by
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ)
    (fun y _ => hχ y) (fun y _ => hM y) convex_univ
    (mem_univ (WithLp.toLp 2 (a, x.snd))) (mem_univ x)
  have hx' : x - WithLp.toLp 2 (a, x.snd) = WithLp.toLp 2 (x.fst - a, (0 : E)) := by
    obtain ⟨⟨t, y⟩⟩ := x; simp [← WithLp.toLp_sub]
  rwa [hχa x.snd, sub_zero, hx', WithLp.norm_toLp_fst, Real.norm_of_nonneg (sub_nonneg.2 hx),
    Real.norm_eq_abs] at hmv

/-- The support of the `n`-th cutoff stays a positive distance inside the half-space. -/
private theorem tsupport_cutoff_subset (a : ℝ) (n : ℕ) :
    tsupport (cutoff (E := E) a n) ⊆ normalHalfSpace (E := E) a := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hclosed : IsClosed {x : WithLp 2 (ℝ × E) | a + ((n : ℝ) + 1)⁻¹ ≤ x.fst} :=
    isClosed_le continuous_const (WithLp.fstL 2 ℝ ℝ E).continuous
  refine (closure_minimal (fun x hx => ?_) hclosed).trans fun x hx => ?_
  · have h0 : 0 < cutoffArg a n x := by
      by_contra h
      exact hx (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
    simp only [cutoffArg] at h0
    rw [mem_ofPred_eq, inv_eq_one_div, ← le_sub_iff_add_le', div_le_iff₀ hpos]
    linarith
  · have : a < x.fst := lt_of_lt_of_le (lt_add_of_pos_right a (inv_pos.2 hpos)) hx
    simpa using this

end Cutoff

/-! ### Integration by parts up to the boundary -/

section HalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Multiplying by the boundary cutoffs does not change the limit of an integral over the
half-space. -/
private theorem tendsto_integral_cutoff_mul {a : ℝ} {F : WithLp 2 (ℝ × E) → ℝ}
    (hF : Integrable F) (hF0 : ∀ x, ¬ a < x.fst → F x = 0) :
    Tendsto (fun n : ℕ => ∫ x, cutoff a n x * F x) atTop (𝓝 (∫ x, F x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
    (fun n => (contDiff_cutoff a n).continuous.aestronglyMeasurable.mul hF.1) hF.norm
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by rw [Real.norm_of_nonneg (cutoff_nonneg a n x)]; exact cutoff_le_one a n x)
  · by_cases hx : a < x.fst
    · exact tendsto_const_nhds.congr' <|
        (eventually_cutoff_eq_one hx).mono fun n hn => by simp [hn]
    · simp [hF0 x hx]

/-- The error term created by differentiating the cutoff in the normal direction tends to zero
when `χ` vanishes on the boundary hyperplane: there `|χ| ≤ M (x.fst - a)`, which compensates the
size of the derivative of the cutoff. -/
private theorem tendsto_integral_mul_deriv_cutoff {a : ℝ} {w : WithLp 2 (ℝ × E) → ℝ}
    (hw : LocallyIntegrable w) (hw0 : ∀ x, ¬ a < x.fst → w x = 0)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχa : ∀ y : E, χ (WithLp.toLp 2 (a, y)) = 0) (c : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, χ x *
      (deriv Real.smoothTransition (cutoffArg a n x) * (((n : ℝ) + 1) * c)) * w x)
      atTop (𝓝 0) := by
  have hdst : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hdst.continuousOn
    (s := Icc (-1 : ℝ) 1)
  obtain ⟨M, hM⟩ :=
    (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hχc.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK : MeasurableSet (tsupport χ) := hχc.isCompact.measurableSet
  have hbound : Integrable fun x => 2 * (C * M * |c|) * (tsupport χ).indicator
      (fun x => ‖w x‖) x :=
    (IntegrableOn.integrable_indicator (hw.integrableOn_isCompact hχc.isCompact).norm
      hK).const_mul _
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => χ x *
      (deriv Real.smoothTransition (cutoffArg a n x) * (((n : ℝ) + 1) * c)) * w x) :=
    (hχ.continuous.mul ((hdst.comp (contDiff_cutoffArg a n).continuous).mul
      continuous_const)).aestronglyMeasurable.mul hw.aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) _
    hmeas hbound (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simpa using hlim
  -- Domination. The integrand vanishes off `tsupport χ`, off the half-space, and where the
  -- cutoff argument exceeds `1` (there `smoothTransition` is constant). On the remaining band
  -- the cutoff argument lies in `[-1, 1]`, so the derivative is at most `C`, and
  -- `(n + 1) (x.fst - a) ≤ 2` absorbs the factor `n + 1` against `|χ x| ≤ M (x.fst - a)`.
  · have hb0 : 0 ≤ 2 * (C * M * |c|) * (tsupport χ).indicator (fun x => ‖w x‖) x :=
      mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => norm_nonneg _) _)
    by_cases hxK : x ∈ tsupport χ
    swap
    · simpa [image_eq_zero_of_notMem_tsupport hxK] using hb0
    by_cases hxa : a < x.fst
    swap
    · simpa [hw0 x hxa] using hb0
    by_cases hs : 1 < cutoffArg a n x
    · simpa [Real.smoothTransition.deriv_of_one_lt hs] using hb0
    push Not at hs
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hs' : -1 ≤ cutoffArg a n x := by
      simp only [cutoffArg]; nlinarith [mul_pos hpos (sub_pos.2 hxa)]
    have hCs := hC _ ⟨hs', hs⟩
    have h2 : ((n : ℝ) + 1) * (x.fst - a) ≤ 2 := by simp only [cutoffArg] at hs; linarith
    rw [indicator_of_mem hxK]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hpos] at hCs ⊢
    calc |χ x| * (|deriv Real.smoothTransition (cutoffArg a n x)| *
          (((n : ℝ) + 1) * |c|)) * |w x|
        ≤ (M * (x.fst - a)) * (C * (((n : ℝ) + 1) * |c|)) * |w x| := by
          gcongr
          exact abs_le_mul_sub_of_eq_zero_on_hyperplane (hχ.differentiable (by simp)) hM hχa
            hxa.le
      _ = C * M * |c| * |w x| * (((n : ℝ) + 1) * (x.fst - a)) := by ring
      _ ≤ C * M * |c| * |w x| * 2 := by gcongr
      _ = 2 * (C * M * |c|) * |w x| := by ring
  -- Pointwise limit: inside the half-space the cutoff argument eventually exceeds `1`, where the
  -- derivative of `smoothTransition` vanishes; outside it `w` vanishes.
  · by_cases hxa : a < x.fst
    · exact tendsto_const_nhds.congr' <| (eventually_lt_cutoffArg hxa 1).mono fun n hn => by
        simp [Real.smoothTransition.deriv_of_one_lt hn]
    · simp [hw0 x hxa]

/-- **Integration by parts up to the boundary.** Let `w` have weak derivative `w'` in the
direction `v` on the half-space, both vanishing off it and locally integrable on the whole space.
Then the integration-by-parts identity holds against every smooth compactly supported `χ`, not
only those supported in the half-space, provided `v` is tangent to the boundary or `χ` vanishes
on the boundary. -/
private theorem integral_fderiv_mul_eq_neg_of_halfSpace {a : ℝ} {v : WithLp 2 (ℝ × E)}
    {w w' : WithLp 2 (ℝ × E) → ℝ}
    (h : HasWeakLineDerivOn volume (normalHalfSpace a) w w' v)
    (hw : LocallyIntegrable w) (hw' : LocallyIntegrable w')
    (hw0 : ∀ x, ¬ a < x.fst → w x = 0) (hw'0 : ∀ x, ¬ a < x.fst → w' x = 0)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hv : v.fst = 0 ∨ ∀ y : E, χ (WithLp.toLp 2 (a, y)) = 0) :
    ∫ x, fderiv ℝ χ x v * w x = -∫ x, χ x * w' x := by
  have hdχ : Continuous fun x => fderiv ℝ χ x v :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdst : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  -- `D n` is the derivative of the `n`-th cutoff in the direction `v`.
  set D : ℕ → WithLp 2 (ℝ × E) → ℝ := fun n x =>
    deriv Real.smoothTransition (cutoffArg a n x) * (((n : ℝ) + 1) * v.fst) with hD
  have hint1 : Integrable fun x => fderiv ℝ χ x v * w x := by
    simpa using hw.integrable_smul_left_of_hasCompactSupport hdχ (hχc.fderiv_apply (𝕜 := ℝ) v)
  have hint3 : Integrable fun x => χ x * w' x := by
    simpa using hw'.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
  have hint2 (n : ℕ) : Integrable fun x => χ x * D n x * w x := by
    simpa using hw.integrable_smul_left_of_hasCompactSupport (hχ.continuous.mul
      ((hdst.comp (contDiff_cutoffArg a n).continuous).mul continuous_const)) hχc.mul_right
  have hint1' (n : ℕ) : Integrable fun x => cutoff a n x * (fderiv ℝ χ x v * w x) :=
    hint1.bdd_mul (contDiff_cutoff a n).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (cutoff_nonneg a n x)]; exact cutoff_le_one a n x)
  -- The weak derivative identity on the half-space, tested against `cutoff a n * χ`.
  have key (n : ℕ) : (∫ x, cutoff a n x * (fderiv ℝ χ x v * w x)) +
      ∫ x, χ x * D n x * w x = -∫ x, cutoff a n x * (χ x * w' x) := by
    let θ : 𝓓(normalHalfSpace (E := E) a, ℝ) :=
      ⟨cutoff a n * χ, (contDiff_cutoff a n).mul hχ, hχc.mul_left,
        tsupport_mul_subset_left.trans (tsupport_cutoff_subset a n)⟩
    have hθ := h.integral_lineDeriv_smul_eq_neg_integral_smul θ
    have hcoe : ((θ : 𝓓(normalHalfSpace (E := E) a, ℝ)) : WithLp 2 (ℝ × E) → ℝ) =
        cutoff a n * χ := rfl
    simp only [hcoe, lineDeriv_cutoff_mul a n (hχ.differentiable (by simp)), smul_eq_mul,
      Pi.mul_apply] at hθ
    rw [← integral_add (hint1' n) (hint2 n)]
    convert hθ using 2
    · funext x; simp only [hD]; ring
    · congr 1; funext x; ring
  -- Pass to the limit `n → ∞` in each of the three integrals.
  have h1 := tendsto_integral_cutoff_mul (a := a) hint1 (fun x hx => by simp [hw0 x hx])
  have h3 := tendsto_integral_cutoff_mul (a := a) hint3 (fun x hx => by simp [hw'0 x hx])
  have h2 : Tendsto (fun n : ℕ => ∫ x, χ x * D n x * w x) atTop (𝓝 0) := by
    rcases hv with hv | hv
    · simp [hD, hv]
    · exact tendsto_integral_mul_deriv_cutoff hw hw0 hχ hχc hv v.fst
  have hlim := h1.add h2
  rw [add_zero] at hlim
  exact tendsto_nhds_unique (hlim.congr key) h3.neg

omit [MeasurableSpace E] [BorelSpace E] in
/-- The chain rule for precomposition with the normal reflection. -/
private theorem fderiv_comp_normalReflection_apply (a : ℝ) {φ : WithLp 2 (ℝ × E) → ℝ}
    (hφ : Differentiable ℝ φ) (y d : WithLp 2 (ℝ × E)) :
    fderiv ℝ (fun x => φ (normalReflection E a x)) y d =
      fderiv ℝ φ (normalReflection E a y) (normalLinearReflection E d) := by
  have h : HasFDerivAt (fun x => φ (normalReflection E a x)) _ y :=
    (hφ (normalReflection E a y)).hasFDerivAt.comp y (hasFDerivAt_normalReflection a y)
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The integral identity behind `hasWeakLineDerivOn_add_comp_normalReflection_of_eq_smul`, for
a single test function `φ`. Changing variables by the reflection turns both sides into pairings
on the half-space with `χ = φ + ε (φ ∘ ρ)`, where integration by parts up to the boundary
applies. -/
private theorem integral_lineDeriv_smul_add_comp_normalReflection {a : ℝ}
    {w : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hw : HasWeakFDerivOn volume (normalHalfSpace a) w fun x => innerSL ℝ (G x))
    (hwl : LocallyIntegrable w) (hGl : LocallyIntegrable G)
    (hw0 : ∀ x, ¬ a < x.fst → w x = 0) (hG0 : ∀ x, ¬ a < x.fst → G x = 0)
    {d : WithLp 2 (ℝ × E)} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hd : normalLinearReflection E d = ε • d)
    {φ : WithLp 2 (ℝ × E) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, lineDeriv ℝ φ x d • (w x + w (normalReflection E a x)) =
      -∫ x, φ x • inner ℝ (G x + normalLinearReflection E (G (normalReflection E a x))) d := by
  set ρ := normalReflection E a
  have hρρ (x : WithLp 2 (ℝ × E)) : ρ (ρ x) = x := normalReflection_normalReflection a x
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hwρ : LocallyIntegrable fun x => w (ρ x) := locallyIntegrable_comp_normalReflection a hwl
  have hGd := hGl.inner_const (𝕜 := ℝ) d
  have hGρd : LocallyIntegrable fun x => inner ℝ (G (ρ x)) d :=
    (locallyIntegrable_comp_normalReflection a hGl).inner_const d
  have hinner (x : WithLp 2 (ℝ × E)) :
      inner ℝ (G x + normalLinearReflection E (G (ρ x))) d =
        inner ℝ (G x) d + ε * inner ℝ (G (ρ x)) d := by
    rw [inner_add_left, inner_normalLinearReflection_left, hd, real_inner_smul_right]
  -- The reflected test function `ψ = φ ∘ ρ` and the combination `χ = φ + ε ψ`.
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set ψ : WithLp 2 (ℝ × E) → ℝ := fun x => φ (ρ x) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_normalReflection a)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph ρ.toHomeomorph
  have hfdφρ (y : WithLp 2 (ℝ × E)) : fderiv ℝ φ (ρ y) d = ε * fderiv ℝ ψ y d := by
    rw [hψdef, fderiv_comp_normalReflection_apply a hφd, hd, map_smul, smul_eq_mul, ← mul_assoc,
      hεε, one_mul]
  set χ : WithLp 2 (ℝ × E) → ℝ := fun x => φ x + ε * ψ x with hχdef
  have hfdχ (x : WithLp 2 (ℝ × E)) :
      fderiv ℝ χ x d = fderiv ℝ φ x d + ε * fderiv ℝ ψ x d := by
    have h : HasFDerivAt χ _ x :=
      (hφd x).hasFDerivAt.add ((hψ.differentiable (by simp) x).hasFDerivAt.const_mul ε)
    rw [h.fderiv]
    simp
  -- Tangential directions need no boundary condition; in the normal direction `χ = φ - ψ`
  -- vanishes on the boundary because `ρ` fixes it.
  have hv : d.fst = 0 ∨ ∀ y : E, χ (WithLp.toLp 2 (a, y)) = 0 := by
    rcases hε with rfl | rfl
    · left
      have h := congrArg WithLp.fst hd
      simp only [normalLinearReflection_apply, WithLp.toLp_fst, one_smul] at h
      linarith
    · right
      intro y
      have hy : ρ (WithLp.toLp 2 (a, y)) = WithLp.toLp 2 (a, y) :=
        (normalReflection_eq_self_iff a _).2 rfl
      simp only [χ, ψ, hy]
      ring
  have hC := integral_fderiv_mul_eq_neg_of_halfSpace (by simpa using hw.hasWeakLineDerivOn d)
    hwl hGd hw0 (fun x hx => by simp [hG0 x hx]) (hφ.add (contDiff_const.mul hψ))
    (hφc.add hψc.mul_left) hv
  -- Integrability of the six pieces into which the two sides split.
  have hcφ : Continuous fun x => fderiv ℝ φ x d :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcψ : Continuous fun x => fderiv ℝ ψ x d :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have I1 : Integrable fun x => fderiv ℝ φ x d * w x := by
    simpa using hwl.integrable_smul_left_of_hasCompactSupport hcφ (hφc.fderiv_apply (𝕜 := ℝ) d)
  have I2 : Integrable fun x => fderiv ℝ φ x d * w (ρ x) := by
    simpa using hwρ.integrable_smul_left_of_hasCompactSupport hcφ (hφc.fderiv_apply (𝕜 := ℝ) d)
  have I3 : Integrable fun x => ε * fderiv ℝ ψ x d * w x := by
    simpa using hwl.integrable_smul_left_of_hasCompactSupport (continuous_const.mul hcψ)
      (hψc.fderiv_apply (𝕜 := ℝ) d).mul_left
  have J1 : Integrable fun x => φ x * inner ℝ (G x) d := by
    simpa using hGd.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have J2 : Integrable fun x => φ x * (ε * inner ℝ (G (ρ x)) d) := by
    simpa only [smul_eq_mul, mul_left_comm] using
      (hGρd.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc).const_mul ε
  have J3 : Integrable fun x => ε * ψ x * inner ℝ (G x) d := by
    simpa using hGd.integrable_smul_left_of_hasCompactSupport (continuous_const.mul hψ.continuous)
      hψc.mul_left
  -- Change variables by the reflection in the two terms carrying `ρ`.
  have hcv1 : ∫ x, fderiv ℝ φ x d * w (ρ x) = ∫ x, ε * fderiv ℝ ψ x d * w x := by
    rw [← integral_comp_normalReflection a (fun y => ε * fderiv ℝ ψ y d * w y)]
    simp only [← hfdφρ, ρ, normalReflection_normalReflection]
  have hcv2 : ∫ x, φ x * (ε * inner ℝ (G (ρ x)) d) = ∫ x, ε * ψ x * inner ℝ (G x) d := by
    rw [← integral_comp_normalReflection a (fun y => ε * ψ y * inner ℝ (G y) d)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ψ, ρ, normalReflection_normalReflection]
    ring
  calc ∫ x, lineDeriv ℝ φ x d • (w x + w (ρ x))
      = ∫ x, (fderiv ℝ φ x d * w x + fderiv ℝ φ x d * w (ρ x)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [(hφd x).lineDeriv_eq_fderiv, smul_eq_mul, mul_add]
    _ = ∫ x, fderiv ℝ χ x d * w x := by
        rw [integral_add I1 I2, hcv1, ← integral_add I1 I3]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hfdχ]
        ring
    _ = -∫ x, χ x * inner ℝ (G x) d := hC
    _ = -((∫ x, φ x * inner ℝ (G x) d) + ∫ x, φ x * (ε * inner ℝ (G (ρ x)) d)) := by
        rw [hcv2, ← integral_add J1 J3]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [χ]
        ring
    _ = -∫ x, φ x • inner ℝ (G x + normalLinearReflection E (G (ρ x))) d := by
        rw [← integral_add J1 J2]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hinner, smul_eq_mul]
        ring

/-- The even reflection is weakly differentiable in every direction `d` which the linear normal
reflection maps to `ε • d` with `ε = ±1`: the tangential directions (`ε = 1`) and the normal
direction (`ε = -1`). -/
private theorem hasWeakLineDerivOn_add_comp_normalReflection_of_eq_smul {a : ℝ}
    {w : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hw : HasWeakFDerivOn volume (normalHalfSpace a) w fun x => innerSL ℝ (G x))
    (hwl : LocallyIntegrable w) (hGl : LocallyIntegrable G)
    (hw0 : ∀ x, ¬ a < x.fst → w x = 0) (hG0 : ∀ x, ¬ a < x.fst → G x = 0)
    {d : WithLp 2 (ℝ × E)} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hd : normalLinearReflection E d = ε • d) :
    HasWeakLineDerivOn volume ⊤ (fun x => w x + w (normalReflection E a x))
      (fun x => inner ℝ (G x + normalLinearReflection E (G (normalReflection E a x))) d) d := by
  have hderiv : LocallyIntegrable
      (fun x => inner ℝ (G x + normalLinearReflection E (G (normalReflection E a x))) d) := by
    simpa only [Pi.add_apply, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using LocallyIntegrable.inner_const (hGl.add
        (locallyIntegrableOn_univ.1 <|
          ((normalLinearReflection E).toContinuousLinearEquiv : WithLp 2 (ℝ × E) →L[ℝ] _)
            |>.locallyIntegrableOn_comp
              ((locallyIntegrable_comp_normalReflection a hGl).locallyIntegrableOn univ))) d
  exact (hasWeakLineDerivOn_iff ((hwl.add (locallyIntegrable_comp_normalReflection a hwl))
    |>.locallyIntegrableOn _) (hderiv.locallyIntegrableOn _)).2 fun φ hφ hφc _ =>
      integral_lineDeriv_smul_add_comp_normalReflection hw hwl hGl hw0 hG0 hε hd hφ hφc

/-- **Even reflection across the boundary of a half-space preserves weak differentiability.**
Let `w` have weak gradient `G` on the half-space `{x | a < x.fst}`, with `w` and `G` vanishing
off the half-space and locally integrable on the whole space (so integrable up to the boundary on
bounded sets). Then `x ↦ w x + w (ρ x)`, where `ρ` is the reflection in the boundary hyperplane,
is weakly differentiable on the whole space with weak gradient `x ↦ G x + R (G (ρ x))`, `R` the
linear part of `ρ`. No boundary condition on `w` is assumed. -/
theorem HasWeakFDerivOn.add_comp_normalReflection {a : ℝ}
    {w : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    (hw : HasWeakFDerivOn volume (normalHalfSpace a) w fun x => innerSL ℝ (G x))
    (hwl : LocallyIntegrable w) (hGl : LocallyIntegrable G)
    (hw0 : ∀ x ∉ normalHalfSpace (E := E) a, w x = 0)
    (hG0 : ∀ x ∉ normalHalfSpace (E := E) a, G x = 0) :
    HasWeakFDerivOn volume ⊤ (fun x => w x + w (normalReflection E a x))
      fun x => innerSL ℝ (G x + normalLinearReflection E (G (normalReflection E a x))) := by
  have hw0' (x : WithLp 2 (ℝ × E)) (hx : ¬ a < x.fst) : w x = 0 := hw0 x (by simpa using hx)
  have hG0' (x : WithLp 2 (ℝ × E)) (hx : ¬ a < x.fst) : G x = 0 := hG0 x (by simpa using hx)
  rw [hasWeakFDerivOn_iff]
  intro v
  -- Split `v` into its normal and tangential parts and add the two directional derivatives.
  have hv : v = WithLp.toLp 2 (v.fst, (0 : E)) + WithLp.toLp 2 ((0 : ℝ), v.snd) := by
    cases v; simp [← WithLp.toLp_add]
  have hn := hasWeakLineDerivOn_add_comp_normalReflection_of_eq_smul hw hwl hGl hw0' hG0'
    (d := WithLp.toLp 2 (v.fst, (0 : E))) (Or.inr rfl) (by simp [← WithLp.toLp_neg])
  have ht := hasWeakLineDerivOn_add_comp_normalReflection_of_eq_smul hw hwl hGl hw0' hG0'
    (d := WithLp.toLp 2 ((0 : ℝ), v.snd)) (Or.inl rfl) (by simp)
  have h := hn.add_direction ht
  rw [← hv] at h
  convert h using 1
  funext x
  rw [Pi.add_apply, ← inner_add_right, ← hv, innerSL_apply_apply]

end HalfSpace

end TauCeti
