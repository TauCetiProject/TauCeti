/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Gradient

/-!
# Perturbations of a function by functions vanishing near its critical points

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, and `h : ι → E → ℝ` a finite family of `C²` functions with compact support, each
vanishing on a neighbourhood of the critical set of `f`. The perturbed function is
`perturb f h s = f + ∑ᵢ sᵢ hᵢ` for a parameter `s : EuclideanSpace ℝ ι`.

The negative-gradient flow of `perturb f h s` depends `C¹`-ly on `s`: the parameter is made a
state variable of a flow on `E × EuclideanSpace ℝ ι`, using a smooth cutoff of the parameter so
that the field is globally Lipschitz.

## Main declarations

* `TauCeti.IsAdmissiblePerturbation f h`: `h` is `C²`, compactly supported, and its support avoids
  the critical points of `f`.
* `TauCeti.perturb f h s`: the perturbed function, with `TauCeti.fderiv_perturb`,
  `TauCeti.gradient_perturb` and `TauCeti.contDiff_perturb`.
* `TauCeti.perturb_eventuallyEq_of_fderiv_eq_zero`: near each critical point of `f` the
  perturbation agrees with `f`.
* `TauCeti.exists_pos_forall_fderiv_perturb_eq_zero_iff`: for small parameters the critical
  points of `perturb f h s` are those of `f`.
* `TauCeti.perturbedFlow f h hf hh`: the flow of the field
  `(x, s) ↦ (-∇ f x - ∑ᵢ a(s)ᵢ ∇ hᵢ x, 0)` on `E × EuclideanSpace ℝ ι`, where `a` is the cutoff of
  the parameter. `TauCeti.contDiff_perturbedFlow` says it is `C¹` jointly in time, space and
  parameter, and `TauCeti.perturbedFlow_apply_of_norm_le` that, for `‖s‖ ≤ 1`, it is the
  negative-gradient flow of `perturb f h s`, with the parameter carried along.
-/

public section

open Set Topology Filter
open scoped Gradient NNReal ContDiff

namespace TauCeti

variable {E : Type*} {ι : Type*}

section Perturb

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] {f : E → ℝ}

/-- A function `h` is an **admissible perturbation** of `f` when it is twice continuously
differentiable, has compact support, and its support does not meet the critical points of `f`. -/
structure IsAdmissiblePerturbation (f h : E → ℝ) : Prop where
  /-- `h` is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 h
  /-- `h` has compact support. -/
  hasCompactSupport : HasCompactSupport h
  /-- The support of `h` avoids the critical points of `f`. -/
  disjoint : Disjoint (tsupport h) {x | fderiv ℝ f x = 0}

/-- The perturbation `f + ∑ᵢ sᵢ hᵢ` of `f` by the family `h` with coefficients `s`. -/
def perturb (f : E → ℝ) (h : ι → E → ℝ) (s : EuclideanSpace ℝ ι) : E → ℝ :=
  fun x ↦ f x + ∑ i, s i * h i x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem perturb_apply (f : E → ℝ) (h : ι → E → ℝ) (s : EuclideanSpace ℝ ι) (x : E) :
    perturb f h s x = f x + ∑ i, s i * h i x :=
  (rfl)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem perturb_zero (f : E → ℝ) (h : ι → E → ℝ) : perturb f h 0 = f := by
  ext x
  simp [perturb_apply]

end Perturb

section Gradient

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  {f : E → ℝ} {h : ι → E → ℝ}

omit [FiniteDimensional ℝ E] in
/-- The differential of a perturbation is the perturbed differential. -/
theorem fderiv_perturb (hf : Differentiable ℝ f) (hh : ∀ i, Differentiable ℝ (h i))
    (s : EuclideanSpace ℝ ι) (x : E) :
    fderiv ℝ (perturb f h s) x = fderiv ℝ f x + ∑ i, s i • fderiv ℝ (h i) x := by
  have hs : HasFDerivAt (fun y ↦ ∑ i, s i • h i y) (∑ i, s i • fderiv ℝ (h i) x) x :=
    HasFDerivAt.fun_sum fun i _ ↦ ((hh i x).hasFDerivAt).const_smul (s i)
  have e : perturb f h s = fun y ↦ f y + ∑ i, s i • h i y :=
    funext fun y ↦ by simp [perturb_apply, smul_eq_mul]
  rw [e]
  exact ((hf x).hasFDerivAt.add hs).fderiv

/-- The gradient of a perturbation is the perturbed gradient. -/
theorem gradient_perturb (hf : Differentiable ℝ f) (hh : ∀ i, Differentiable ℝ (h i))
    (s : EuclideanSpace ℝ ι) (x : E) :
    ∇ (perturb f h s) x = ∇ f x + ∑ i, s i • ∇ (h i) x := by
  simp only [gradient, fderiv_perturb hf hh, map_add, map_sum, map_smul]

omit [FiniteDimensional ℝ E] in
/-- The perturbation of a `C²` function by `C²` functions is `C²`. -/
theorem contDiff_perturb (hfs : ContDiff ℝ 2 f) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (s : EuclideanSpace ℝ ι) :
    ContDiff ℝ 2 (perturb f h s) :=
  hfs.add (ContDiff.sum fun i _ ↦ contDiff_const.mul (hh i))

omit [FiniteDimensional ℝ E] in
/-- **Near a critical point of `f`, a perturbation agrees with `f`.** The functions of an admissible
family vanish on a neighbourhood of each critical point. -/
theorem perturb_eventuallyEq_of_fderiv_eq_zero (hh : ∀ i, IsAdmissiblePerturbation f (h i))
    (s : EuclideanSpace ℝ ι) {x : E} (hx : fderiv ℝ f x = 0) : perturb f h s =ᶠ[𝓝 x] f := by
  have hi : ∀ i, ∀ᶠ y in 𝓝 x, h i y = 0 := fun i ↦
    notMem_tsupport_iff_eventuallyEq.1 fun hmem ↦
      Set.disjoint_left.1 (hh i).disjoint hmem hx
  filter_upwards [eventually_all.2 hi] with y hy
  simp [perturb_apply, hy]

omit [FiniteDimensional ℝ E] in
/-- **Small perturbations keep the critical points.** For all sufficiently small parameters, the
critical points of `perturb f h s` are those of `f`. -/
theorem exists_pos_forall_fderiv_perturb_eq_zero_iff (hfs : ContDiff ℝ 2 f)
    (hh : ∀ i, IsAdmissiblePerturbation f (h i)) :
    ∃ δ > 0, ∀ s : EuclideanSpace ℝ ι, ‖s‖ < δ → ∀ x,
      (fderiv ℝ (perturb f h s) x = 0 ↔ fderiv ℝ f x = 0) := by
  have hfd : Differentiable ℝ f := hfs.differentiable (by norm_num)
  have hhd : ∀ i, Differentiable ℝ (h i) := fun i ↦ (hh i).contDiff.differentiable (by norm_num)
  -- A bound on the differentials of the perturbing functions.
  have hB : ∀ i, ∃ C : ℝ, ∀ x, ‖fderiv ℝ (h i) x‖ ≤ C := fun i ↦
    ((hh i).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
      ((hh i).contDiff.continuous_fderiv (by norm_num))
  choose B hB using hB
  obtain ⟨C, hC⟩ := Finite.exists_le B
  -- A lower bound for the differential of `f` on the supports.
  set A : Set E := ⋃ i, tsupport (h i)
  have hA : IsCompact A := isCompact_iUnion fun i ↦ (hh i).hasCompactSupport
  have hAcrit : ∀ x ∈ A, fderiv ℝ f x ≠ 0 := fun x hx hx0 ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact Set.disjoint_left.1 (hh i).disjoint hi hx0
  obtain ⟨m, hm, hmA⟩ : ∃ m > 0, ∀ x ∈ A, m ≤ ‖fderiv ℝ f x‖ := by
    rcases A.eq_empty_or_nonempty with h0 | hne
    · exact ⟨1, one_pos, by simp [h0]⟩
    · have hc : Continuous fun x ↦ ‖fderiv ℝ f x‖ :=
        (hfs.continuous_fderiv (by norm_num)).norm
      obtain ⟨x₀, hx₀, hmin⟩ := hA.exists_isMinOn hne hc.continuousOn
      exact ⟨‖fderiv ℝ f x₀‖, norm_pos_iff.2 (hAcrit x₀ hx₀), fun x hx ↦ hmin hx⟩
  refine ⟨m / (Fintype.card ι * max C 0 + 1), by positivity, fun s hs x ↦ ?_⟩
  by_cases hx : x ∈ A
  · -- On the supports both differentials are nonzero.
    have hne : fderiv ℝ f x ≠ 0 := hAcrit x hx
    refine iff_of_false ?_ hne
    rw [fderiv_perturb hfd hhd]
    intro h0
    have h1 : ‖∑ i, s i • fderiv ℝ (h i) x‖ ≤ Fintype.card ι * max C 0 * ‖s‖ := by
      calc ‖∑ i, s i • fderiv ℝ (h i) x‖ ≤ ∑ i, ‖s i • fderiv ℝ (h i) x‖ := norm_sum_le _ _
        _ ≤ ∑ _i : ι, ‖s‖ * max C 0 := Finset.sum_le_sum fun i _ ↦ by
          rw [norm_smul]
          exact mul_le_mul (PiLp.norm_apply_le s i)
            ((hB i x).trans ((hC i).trans (le_max_left _ _))) (norm_nonneg _) (norm_nonneg _)
        _ = Fintype.card ι * max C 0 * ‖s‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    have h2 : ‖fderiv ℝ f x‖ ≤ ‖∑ i, s i • fderiv ℝ (h i) x‖ := by
      have : fderiv ℝ f x = -∑ i, s i • fderiv ℝ (h i) x := eq_neg_of_add_eq_zero_left h0
      rw [this, norm_neg]
    have hcard : (0 : ℝ) < Fintype.card ι * max C 0 + 1 := by positivity
    have h3 : ‖s‖ * (Fintype.card ι * max C 0 + 1) < m := by
      rwa [lt_div_iff₀ hcard] at hs
    have h4 : 0 ≤ (Fintype.card ι * max C 0 : ℝ) := by positivity
    nlinarith [hmA x hx, norm_nonneg s]
  · -- Off the supports the perturbation agrees with `f` near `x`.
    have hev : perturb f h s =ᶠ[𝓝 x] f := by
      have hi : ∀ i, ∀ᶠ y in 𝓝 x, h i y = 0 := fun i ↦
        notMem_tsupport_iff_eventuallyEq.1 fun hmem ↦ hx (mem_iUnion.2 ⟨i, hmem⟩)
      filter_upwards [eventually_all.2 hi] with y hy
      simp [perturb_apply, hy]
    rw [hev.fderiv_eq]

end Gradient

section Flow

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  {f : E → ℝ} {h : ι → E → ℝ} {K : ℝ≥0}

/-- A smooth cutoff of the parameter, equal to `1` on the closed unit ball and supported in the
closed ball of radius `2`. -/
noncomputable def paramBump : ContDiffBump (0 : EuclideanSpace ℝ ι) :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off parameter `s ↦ paramBump s • s`: it is the identity on the closed unit ball, and
has compact support. -/
noncomputable def paramCutoff (s : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  paramBump.toFun s • s

theorem contDiff_paramCutoff : ContDiff ℝ 1 (paramCutoff (ι := ι)) :=
  paramBump.contDiff.smul contDiff_id

theorem hasCompactSupport_paramCutoff : HasCompactSupport (paramCutoff (ι := ι)) :=
  paramBump.hasCompactSupport.smul_right

theorem paramCutoff_eq_self_of_norm_le {s : EuclideanSpace ℝ ι} (hs : ‖s‖ ≤ 1) :
    paramCutoff s = s := by
  have hr : (paramBump (ι := ι)).rIn = 1 := (rfl)
  have hb : paramBump.toFun s = 1 :=
    paramBump.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, hr]; exact hs)
  rw [paramCutoff, hb, one_smul]

private theorem gradient_eq_zero_of_notMem_tsupport {g : E → ℝ} {x : E}
    (hx : x ∉ tsupport g) : ∇ g x = 0 := by
  have : fderiv ℝ g x = 0 := by
    by_contra hne
    exact hx (support_fderiv_subset ℝ hne)
  rw [gradient, this, map_zero]

/-- The part of the augmented field that couples the state to the parameter. -/
private noncomputable def coupling (h : ι → E → ℝ) (p : E × EuclideanSpace ℝ ι) : E :=
  ∑ i, paramCutoff p.2 i • ∇ (h i) p.1

private theorem contDiff_coupling (hh : ∀ i, IsAdmissiblePerturbation f (h i)) :
    ContDiff ℝ 1 (coupling h) := by
  refine ContDiff.sum fun i _ ↦ ?_
  have h1 : ContDiff ℝ 1 fun p : E × EuclideanSpace ℝ ι ↦ paramCutoff p.2 i :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff.comp
      contDiff_paramCutoff).comp contDiff_snd
  have h2 : ContDiff ℝ 1 fun p : E × EuclideanSpace ℝ ι ↦ ∇ (h i) p.1 :=
    ((hh i).contDiff.gradient_right (m := 1) (by norm_num)).comp contDiff_fst
  exact h1.smul h2

private theorem hasCompactSupport_coupling (hh : ∀ i, IsAdmissiblePerturbation f (h i)) :
    HasCompactSupport (coupling h) := by
  have hA : IsCompact (⋃ i, tsupport (h i)) :=
    isCompact_iUnion fun i ↦ (hh i).hasCompactSupport
  refine HasCompactSupport.intro (hA.prod paramBump.hasCompactSupport) fun p hp ↦ ?_
  rw [mem_prod, not_and_or] at hp
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rcases hp with hp | hp
  · rw [gradient_eq_zero_of_notMem_tsupport (g := h i) fun hx ↦ hp (mem_iUnion.2 ⟨i, hx⟩),
      smul_zero]
  · have : paramBump.toFun p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
    simp [paramCutoff, this]

/-- **The augmented field.** The vector field on `E × EuclideanSpace ℝ ι` whose first component
is `-∇ f x - ∑ᵢ a(s)ᵢ ∇ hᵢ x`, with `a` the cutoff of the parameter, and whose second component is
zero: the parameter is constant along its orbits. -/
noncomputable def perturbedField (f : E → ℝ) (h : ι → E → ℝ)
    (p : E × EuclideanSpace ℝ ι) : E × EuclideanSpace ℝ ι :=
  (-∇ f p.1 - ∑ i, paramCutoff p.2 i • ∇ (h i) p.1, 0)

theorem exists_lipschitzWith_perturbedField (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, IsAdmissiblePerturbation f (h i)) :
    ∃ K' : ℝ≥0, LipschitzWith K' (perturbedField f h) := by
  obtain ⟨C, hC⟩ := (contDiff_coupling hh).lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_coupling hh) one_ne_zero
  exact ⟨_, ((hf.comp LipschitzWith.prod_fst).neg.sub hC).prodMk (LipschitzWith.const 0)⟩

theorem contDiff_perturbedField (hfs : ContDiff ℝ 2 f)
    (hh : ∀ i, IsAdmissiblePerturbation f (h i)) : ContDiff ℝ 1 (perturbedField f h) :=
  (((hfs.gradient_right (m := 1) (by norm_num)).comp contDiff_fst).neg.sub
    (contDiff_coupling hh)).prodMk contDiff_const

/-- **The flow of the augmented field**: the negative-gradient flow of the perturbation
`perturb f h s`, jointly in the parameter `s`, which is carried along unchanged. -/
noncomputable def perturbedFlow (f : E → ℝ) (h : ι → E → ℝ) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, IsAdmissiblePerturbation f (h i)) : Flow ℝ (E × EuclideanSpace ℝ ι) :=
  flowOfLipschitz (perturbedField f h) (exists_lipschitzWith_perturbedField hf hh).choose_spec

/-- **The perturbed flow is `C¹`**, jointly in time, the initial condition and the parameter. -/
theorem contDiff_perturbedFlow (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, IsAdmissiblePerturbation f (h i)) :
    ContDiff ℝ 1 (Function.uncurry (perturbedFlow f h hf hh)) := by
  have hc : ContDiff ℝ ((0 : ℕ) + 1) (perturbedField f h) := by
    simpa using contDiff_perturbedField hfs hh
  unfold perturbedFlow
  simpa using contDiff_flowOfLipschitz 0 (perturbedField f h)
    (exists_lipschitzWith_perturbedField hf hh).choose_spec hc

/-- **The perturbed flow is the negative-gradient flow of the perturbation.** For a parameter `s`
of norm at most `1`, the perturbed flow sends `(x, s)` at time `t` to the pair of the time-`t`
image of `x` under the negative-gradient flow of `perturb f h s`, and `s`. -/
theorem perturbedFlow_apply_of_norm_le (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, IsAdmissiblePerturbation f (h i)) {s : EuclideanSpace ℝ ι} (hs : ‖s‖ ≤ 1)
    {K' : ℝ≥0} (hf' : LipschitzWith K' (∇ (perturb f h s))) (t : ℝ) (x : E) :
    perturbedFlow f h hf hh t (x, s) = (negativeGradientFlow (perturb f h s) hf' t x, s) := by
  set φ := negativeGradientFlow (perturb f h s) hf'
  have hγ : ∀ t, HasDerivAt (fun t ↦ (φ t x, s))
      (perturbedField f h (φ t x, s)) t := by
    intro t
    have h1 : HasDerivAt (fun t ↦ φ t x) (-∇ (perturb f h s) (φ t x)) t :=
      (isNegativeGradient_negativeGradientFlow (perturb f h s) hf').isIntegralCurve x t
    have h2 := h1.prodMk (hasDerivAt_const t s)
    convert h2 using 1
    simp only [perturbedField, paramCutoff_eq_self_of_norm_le hs,
      gradient_perturb (hfs.differentiable (by norm_num))
        (fun i ↦ (hh i).contDiff.differentiable (by norm_num)), neg_add', sub_eq_add_neg]
    rfl
  have := eq_flowOfLipschitz (exists_lipschitzWith_perturbedField hf hh).choose_spec hγ t
  simpa [perturbedFlow] using this.symm

end Flow

end TauCeti
