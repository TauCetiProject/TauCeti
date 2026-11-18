/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
public import TauCeti.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Calderón–Zygmund operators

A **Calderón–Zygmund operator** on a finite-dimensional real inner product space `V` of dimension
`n` is a bounded linear operator `T` on `L²(V)` which, away from the support of its argument, is
integration against a **standard kernel** `K`: `‖K x y‖ ≤ C / dist x y ^ n`, `K` is `δ`-Hölder in
each variable off the diagonal at the scale of `dist x y`, and `T f x = ∫ K x y f y dy` for almost
every `x` outside a compact set carrying `f` (`TauCeti.HasStandardKernel`). This file proves the
basic theorems about this class.

* **Adjoints.** The adjoint of an `L²` operator with an off-diagonal kernel `k` has the transposed
  kernel `(x, y) ↦ (k y x)†` (`ContinuousLinearMap.ae_adjoint_apply_eq_integral`, proved for any
  proper metric measure space and operator-valued kernels bounded away from the diagonal in
  `TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint`). Hence the adjoint of a
  Calderón–Zygmund operator with kernel `K` is a Calderón–Zygmund operator with the kernel
  `(x, y) ↦ conj (K y x)` and the same constants (`TauCeti.HasStandardKernel.adjoint`).
* **The Calderón–Zygmund theorem.** A Calderón–Zygmund operator is of weak type `(1, 1)`
  (`TauCeti.HasStandardKernel.exists_mul_volume_lt_enorm_le`) and bounded in the `Lᵖ` norm for
  every `1 < p < ∞` (`TauCeti.HasStandardKernel.exists_eLpNorm_le`). These are the real
  Calderón–Zygmund theorems on `V`
  (`ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`,
  `ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`), whose hypotheses on the
  adjoint the adjoint theorem supplies.
* **Examples.** The identity has the kernel `0` (`TauCeti.hasStandardKernel_id`), and the Riesz
  transforms are Calderón–Zygmund operators (`TauCeti.hasStandardKernel_rieszTransform`).

The definition asks nothing of `K` on the diagonal, and no measurability: the smoothness estimate
makes `K` continuous off the diagonal (`TauCeti.HasStandardKernel.continuousOn_uncurry`), which is
all the measure theory needs. Boundedness on `L²` is part of the definition, since the kernel
estimates do not imply it: multiplication by `x` on `ℝ` has the kernel `0` off the diagonal and is
unbounded.

## References

* E. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory Integrals*,
  Chapter I, §6, and Chapter VII, §3.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3 (standard kernels and the
  Calderón–Zygmund theorem, Theorem 5.3.3).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate Topology

namespace TauCeti

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Calderón–Zygmund operators.** A bounded operator `T` on `L²(V, F)` **has the standard kernel**
`K` with constant `C` and exponent `δ > 0` when, writing `n` for the dimension of `V`,

* `K` satisfies the size estimate `‖K x y‖ ≤ C / dist x y ^ n` for `x ≠ y`;
* `K` satisfies the smoothness estimate in both variables,
  `‖K x y - K x y'‖ + ‖K y x - K y' x‖ ≤ C dist y y' ^ δ / dist x y ^ (n + δ)` whenever
  `2 dist y y' < dist x y`;
* `T` is given by `K` away from the support of its argument: if `f` vanishes outside a compact
  set `s`, then `T f x = ∫ K x y • f y dy` for almost every `x ∉ s`.

Such a `T` is a **Calderón–Zygmund operator**. Boundedness on `L²` is part of the data, since the
kernel estimates alone do not imply it: multiplication by `x` on `ℝ` has the kernel `0` off the
diagonal but is unbounded on `L²`. The kernel acts on `F`-valued functions by scalar
multiplication, as the Riesz transforms do. -/
structure HasStandardKernel (T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V))
    (K : V → V → ℂ) (C : ℝ≥0) (δ : ℝ) : Prop where
  /-- The smoothness exponent is positive. -/
  exponent_pos : 0 < δ
  /-- The size estimate. -/
  norm_le : ∀ x y, x ≠ y → ‖K x y‖ ≤ C / dist x y ^ Module.finrank ℝ V
  /-- The smoothness estimate in both variables. -/
  norm_sub_add_norm_sub_le : ∀ x y y', 2 * dist y y' < dist x y →
    ‖K x y - K x y'‖ + ‖K y x - K y' x‖ ≤
      C * dist y y' ^ δ / dist x y ^ (Module.finrank ℝ V + δ)
  /-- `T` is integration against `K` away from the support of its argument. -/
  ae_apply_eq_integral : ∀ (f : Lp F 2 (volume : Measure V)) (s : Set V), IsCompact s →
    (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s → T f x = ∫ y, K x y • f y

namespace HasStandardKernel

variable {T : Lp F 2 (volume : Measure V) →L[ℂ] Lp F 2 (volume : Measure V)} {K : V → V → ℂ}
  {C : ℝ≥0} {δ : ℝ}

/-- The estimates of a standard kernel persist under a larger constant. -/
theorem mono (h : HasStandardKernel T K C δ) {C' : ℝ≥0} (hC : C ≤ C') :
    HasStandardKernel T K C' δ where
  exponent_pos := h.exponent_pos
  norm_le x y hxy := (h.norm_le x y hxy).trans (by gcongr)
  norm_sub_add_norm_sub_le x y y' hy := (h.norm_sub_add_norm_sub_le x y y' hy).trans (by gcongr)
  ae_apply_eq_integral := h.ae_apply_eq_integral

/-- A standard kernel is continuous off the diagonal. -/
theorem continuousOn_uncurry (h : HasStandardKernel T K C δ) :
    ContinuousOn (Function.uncurry K) {p : V × V | p.1 ≠ p.2} := by
  rintro ⟨x₀, y₀⟩ (hxy : x₀ ≠ y₀)
  refine ContinuousAt.continuousWithinAt ?_
  have hd : 0 < dist x₀ y₀ := dist_pos.2 hxy
  set n : ℝ := (Module.finrank ℝ V : ℝ)
  -- The two smoothness estimates bound the oscillation of `K` near `(x₀, y₀)` by `b`.
  set b : V × V → ℝ := fun p ↦ C * dist p.2 y₀ ^ δ / dist p.1 p.2 ^ (n + δ) +
    C * dist p.1 x₀ ^ δ / dist y₀ p.1 ^ (n + δ)
  have hδ := h.exponent_pos
  have hb : ContinuousAt b (x₀, y₀) := by
    have hpow : ∀ {f : V × V → ℝ}, Continuous f → (∀ p, 0 ≤ f p) → ∀ {e : ℝ}, 0 ≤ e →
        Continuous fun p ↦ f p ^ e := fun hf _ _ he ↦ hf.rpow_const fun _ ↦ Or.inr he
    refine ContinuousAt.add (ContinuousAt.div ?_ ?_ ?_) (ContinuousAt.div ?_ ?_ ?_)
    · exact (continuous_const.mul (hpow (continuous_snd.dist continuous_const)
        (fun _ ↦ dist_nonneg) hδ.le)).continuousAt
    · exact (hpow (continuous_fst.dist continuous_snd) (fun _ ↦ dist_nonneg)
        (by positivity)).continuousAt
    · exact (Real.rpow_pos_of_pos hd _).ne'
    · exact (continuous_const.mul (hpow (continuous_fst.dist continuous_const)
        (fun _ ↦ dist_nonneg) hδ.le)).continuousAt
    · exact (hpow (continuous_const.dist continuous_fst) (fun _ ↦ dist_nonneg)
        (by positivity)).continuousAt
    · exact (Real.rpow_pos_of_pos (dist_comm x₀ y₀ ▸ hd) _).ne'
  have hb0 : b (x₀, y₀) = 0 := by simp [b, Real.zero_rpow hδ.ne']
  have h₁ : ∀ᶠ p : V × V in 𝓝 (x₀, y₀), 2 * dist p.2 y₀ < dist p.1 p.2 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hd)
  have h₂ : ∀ᶠ p : V × V in 𝓝 (x₀, y₀), 2 * dist p.1 x₀ < dist y₀ p.1 :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa [dist_comm] using hd)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ (hb0 ▸ hb.tendsto)
  filter_upwards [h₁, h₂] with ⟨x, y⟩ hp₁ hp₂
  calc ‖K x y - K x₀ y₀‖ ≤ ‖K x y - K x y₀‖ + ‖K x y₀ - K x₀ y₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ b (x, y) := add_le_add
        ((le_add_of_nonneg_right (norm_nonneg _)).trans (h.norm_sub_add_norm_sub_le x y y₀ hp₁))
        ((le_add_of_nonneg_left (norm_nonneg _)).trans (h.norm_sub_add_norm_sub_le y₀ x x₀ hp₂))

/-! ### The kernel modified on the diagonal

The estimates say nothing about `K` on the diagonal, where it need not even be measurable. The
real Calderón–Zygmund theorems and the kernel of the adjoint take a strongly measurable
operator-valued kernel, so they are applied to `K` set to `0` on the diagonal, which is continuous
off the diagonal. The change is invisible in the integrals `∫ K x y • f y dy` for `x` outside the
set carrying `f`. -/

open scoped Classical in
/-- The kernel `K` set to `0` on the diagonal. -/
private def offDiag (K : V → V → ℂ) (x y : V) : ℂ := if x = y then 0 else K x y

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
private theorem offDiag_of_ne {x y : V} (hxy : x ≠ y) : offDiag K x y = K x y := by
  simp [offDiag, hxy]

private theorem stronglyMeasurable_offDiag (h : HasStandardKernel T K C δ) :
    StronglyMeasurable (Function.uncurry (offDiag K)) := by
  classical
  have : Function.uncurry (offDiag K) =
      {p : V × V | p.1 ≠ p.2}.piecewise (Function.uncurry K) 0 := by
    ext ⟨x, y⟩
    by_cases hxy : x = y <;> simp [offDiag, hxy, Set.piecewise]
  rw [this]
  exact (h.continuousOn_uncurry.measurable_piecewise continuousOn_const
    (isOpen_ne_fun continuous_fst continuous_snd).measurableSet).stronglyMeasurable

/-- Changing a kernel on the diagonal does not change its integrals at points outside the set
carrying the integrand. -/
private theorem integral_offDiag_smul (K : V → V → ℂ) {f : V → F} {s : Set V}
    (hf : ∀ᵐ y, y ∉ s → f y = 0) {x : V} (hx : x ∉ s) :
    ∫ y, offDiag K x y • f y = ∫ y, K x y • f y := by
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  by_cases hxy : x = y
  · subst hxy
    simp [hy hx]
  · rw [offDiag_of_ne hxy]

private theorem norm_offDiag_le (h : HasStandardKernel T K C δ) {x y : V} (hxy : x ≠ y) :
    ‖offDiag K x y‖ ≤ C * dist x y ^ (-(Module.finrank ℝ V : ℝ)) := by
  rw [offDiag_of_ne hxy, Real.rpow_neg dist_nonneg, Real.rpow_natCast, ← div_eq_mul_inv]
  exact h.norm_le x y hxy

private theorem norm_offDiag_sub_le (h : HasStandardKernel T K C δ) {x y y' : V}
    (hy : 2 * dist y y' < dist x y') :
    ‖offDiag K x y - offDiag K x y'‖ ≤
      C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))) := by
  have hxy' : x ≠ y' := dist_pos.1 ((mul_nonneg zero_le_two dist_nonneg).trans_lt hy)
  have hxy : x ≠ y := by
    rintro rfl
    linarith [dist_nonneg (x := x) (y := y')]
  rw [offDiag_of_ne hxy, offDiag_of_ne hxy', norm_sub_rev, Real.rpow_neg dist_nonneg,
    ← mul_assoc, ← div_eq_mul_inv, dist_comm y y']
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans
    (h.norm_sub_add_norm_sub_le x y' y (by rwa [dist_comm y' y]))

section OpKernel

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass 𝕜 ℂ F]

variable (F 𝕜) in
/-- The kernel as a `𝕜`-linear operator-valued kernel `K x y • id`, set to `0` on the diagonal.
For `𝕜 = ℝ` it is in the form taken by the real Calderón–Zygmund theorems, and for `𝕜 = ℂ` in the
form taken by `ContinuousLinearMap.ae_adjoint_apply_eq_integral`. -/
private def opKernel (K : V → V → ℂ) (x y : V) : F →L[𝕜] F :=
  offDiag K x y • ContinuousLinearMap.id 𝕜 F

private theorem stronglyMeasurable_opKernel (h : HasStandardKernel T K C δ) :
    StronglyMeasurable (Function.uncurry (opKernel F 𝕜 K)) :=
  h.stronglyMeasurable_offDiag.smul_const _

private theorem norm_opKernel_le (h : HasStandardKernel T K C δ) (x y : V) (hxy : x ≠ y) :
    ‖opKernel F 𝕜 K x y‖ ≤ C * dist x y ^ (-(Module.finrank ℝ V : ℝ)) :=
  (ContinuousLinearMap.norm_smul_id_le _).trans (h.norm_offDiag_le hxy)

private theorem norm_opKernel_sub_le (h : HasStandardKernel T K C δ) (x y y' : V)
    (hy : 2 * dist y y' < dist x y') :
    ‖opKernel F 𝕜 K x y - opKernel F 𝕜 K x y'‖ ≤
      C * (dist y y' ^ δ * dist x y' ^ (-(Module.finrank ℝ V + δ))) := by
  rw [opKernel, opKernel, ← sub_smul]
  exact (ContinuousLinearMap.norm_smul_id_le _).trans (h.norm_offDiag_sub_le hy)

private theorem ae_apply_eq_integral_opKernel (h : HasStandardKernel T K C δ)
    (f : Lp F 2 (volume : Measure V)) (s : Set V) (hs : IsCompact s)
    (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → T f x = ∫ z, opKernel F 𝕜 K x z (f z) := by
  filter_upwards [h.ae_apply_eq_integral f s hs hf] with x hx hxs
  rw [hx hxs, ← integral_offDiag_smul K hf hxs]
  simp [opKernel]

/-- `ae_apply_eq_integral_opKernel` for the realification `T.restrictScalars ℝ`, the operator
taken by the real Calderón–Zygmund theorems. -/
private theorem ae_restrictScalars_apply_eq_integral_opKernel (h : HasStandardKernel T K C δ)
    (f : Lp F 2 (volume : Measure V)) (s : Set V) (hs : IsCompact s)
    (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → T.restrictScalars ℝ f x = ∫ z, opKernel F ℝ K x z (f z) := by
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using
    h.ae_apply_eq_integral_opKernel f s hs hf

end OpKernel

/-! ### Adjoints and the Calderón–Zygmund bounds -/

variable [CompleteSpace F]

/-- **Calderón–Zygmund operators are closed under adjoints.** The adjoint of a Calderón–Zygmund
operator with kernel `K` is a Calderón–Zygmund operator with the conjugate transposed kernel
`(x, y) ↦ conj (K y x)`, with the same constants. -/
theorem adjoint (h : HasStandardKernel T K C δ) :
    HasStandardKernel (ContinuousLinearMap.adjoint T) (fun x y ↦ conj (K y x)) C δ where
  exponent_pos := h.exponent_pos
  norm_le x y hxy := by simpa [dist_comm] using h.norm_le y x hxy.symm
  norm_sub_add_norm_sub_le x y y' hy := by
    simpa only [← map_sub, RCLike.norm_conj, add_comm] using h.norm_sub_add_norm_sub_le x y y' hy
  ae_apply_eq_integral g s hs hg := by
    have hk : ∀ r > 0, ∃ M, ∀ x y, r ≤ dist x y → ‖opKernel F ℂ K x y‖ ≤ M := fun r hr ↦
      ⟨C * r ^ (-(Module.finrank ℝ V : ℝ)), fun x y hxy ↦
        (h.norm_opKernel_le x y (dist_pos.1 (hr.trans_le hxy))).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hr hxy (neg_nonpos.2 (Nat.cast_nonneg _))) C.2)⟩
    filter_upwards [ContinuousLinearMap.ae_adjoint_apply_eq_integral T
      h.stronglyMeasurable_opKernel hk h.ae_apply_eq_integral_opKernel g hs hg] with x hx hxs
    rw [hx hxs, ← integral_offDiag_smul (fun x y ↦ conj (K y x)) hg hxs]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    by_cases hxz : x = z
    · simp [opKernel, offDiag, hxz]
    · dsimp only
      rw [opKernel, offDiag_of_ne hxz, offDiag_of_ne (Ne.symm hxz), map_smulₛₗ,
        ContinuousLinearMap.adjoint_id, smul_apply, ContinuousLinearMap.id_apply]

/-- **Calderón–Zygmund operators are of weak type `(1, 1)`**: there is a constant `A` with
`t · |{x | ‖T f x‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`. A Calderón–Zygmund operator
need not be bounded on `L¹`, and this is the substitute at the endpoint. -/
theorem exists_mul_volume_lt_enorm_le (h : HasStandardKernel T K C δ) :
    ∃ A : ℝ≥0, ∀ (f : Lp F 2 (volume : Measure V)) (t : ℝ≥0∞),
      t * volume {x | t < ‖T f x‖ₑ} ≤ A * eLpNorm f 1 volume := by
  obtain ⟨A, hA⟩ := ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow
    (T.restrictScalars ℝ) h.stronglyMeasurable_opKernel h.exponent_pos h.norm_opKernel_le
    h.norm_opKernel_sub_le h.ae_restrictScalars_apply_eq_integral_opKernel
  exact ⟨A, fun f t ↦ by
    rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f)]
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using hA f t⟩

/-- **Calderón–Zygmund operators are bounded on `Lᵖ`** for `1 < p < ∞`: there is a constant `A`
with `‖T f‖_p ≤ A ‖f‖_p` for every `f ∈ L²`. The adjoint of `T` is a Calderón–Zygmund operator
(`TauCeti.HasStandardKernel.adjoint`), which gives the range `p > 2` by duality. -/
theorem exists_eLpNorm_le (h : HasStandardKernel T K C δ) {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ A : ℝ≥0, ∀ f : Lp F 2 (volume : Measure V),
      eLpNorm (T f) p volume ≤ A * eLpNorm f p volume := by
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have h' := h.adjoint
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using
    ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow (T.restrictScalars ℝ)
      h.stronglyMeasurable_opKernel h'.stronglyMeasurable_opKernel h.exponent_pos
      h'.exponent_pos h.norm_opKernel_le h'.norm_opKernel_le h.norm_opKernel_sub_le
      h'.norm_opKernel_sub_le h.ae_restrictScalars_apply_eq_integral_opKernel
      (fun f s hs hf ↦ by
        rw [L2.adjoint_restrictScalars]
        exact h'.ae_restrictScalars_apply_eq_integral_opKernel f s hs hf) hp hp_top

end HasStandardKernel

/-- The identity is a Calderón–Zygmund operator, with the kernel `0`. -/
theorem hasStandardKernel_id (C : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    HasStandardKernel (ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure V))) 0 C δ where
  exponent_pos := hδ
  norm_le x y _ := by
    simp only [Pi.zero_apply, norm_zero]
    positivity
  norm_sub_add_norm_sub_le x y y' _ := by
    simp only [Pi.zero_apply, sub_zero, norm_zero, add_zero]
    positivity
  ae_apply_eq_integral f s _ hf := by
    filter_upwards [hf] with x hx hxs
    simp [hx hxs]

end TauCeti
