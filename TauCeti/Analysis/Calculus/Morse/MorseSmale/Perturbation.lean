/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Dynamics.Flow.Stable
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Dynamics.Flow.Variational

/-!
# Perturbations of a function by functions vanishing near its critical points

Let `f` be a `C²` function with globally Lipschitz gradient on a finite-dimensional real inner
product space `E`, and `h : ι → E → ℝ` a finite family of `C²` functions with compact support, each
vanishing on a neighbourhood of the critical set of `f`. The perturbed function is
`perturb f h s = f + ∑ᵢ sᵢ hᵢ` for a parameter `s : EuclideanSpace ℝ ι`.

To study the dependence on `s` of the negative-gradient flow of `perturb f h s`, the parameter is
made a state variable: the flow of a cut-off augmented field on `E × EuclideanSpace ℝ ι` is `C¹`
jointly in time, space and parameter, and agrees with the negative-gradient flow of `perturb f h s`
for parameters in the closed unit ball.

## Main declarations

* `TauCeti.IsAdmissiblePerturbation f h`: `h` is `C²`, compactly supported, and its support avoids
  the critical points of `f`; `ContDiffBump.isAdmissiblePerturbation_mul`: a bump times a
  `C²` function is admissible when the bump's support avoids the critical points.
* `TauCeti.perturb f h s`: the perturbed function, with `TauCeti.fderiv_perturb`,
  `TauCeti.gradient_perturb` and `TauCeti.contDiff_perturb`.
* `TauCeti.perturb_eventuallyEq_of_fderiv_eq_zero`: near each critical point of `f` the
  perturbation agrees with `f`.
* `TauCeti.exists_pos_forall_fderiv_perturb_eq_zero_iff`: for small parameters the critical
  points of `perturb f h s` are those of `f`.
* `TauCeti.perturbedFlow f h hf hh hc`: the flow of the field
  `(x, s) ↦ (-∇ f x - ∑ᵢ a(s)ᵢ ∇ hᵢ x, 0)` on `E × EuclideanSpace ℝ ι`, where `a` is the cutoff of
  the parameter. `TauCeti.contDiff_perturbedFlow` says it is `C¹` jointly in time, space and
  parameter, and `TauCeti.perturbedFlow_apply_of_norm_le` that, for `‖s‖ ≤ 1`, it is the
  negative-gradient flow of `perturb f h s`, with the parameter carried along
  (`TauCeti.snd_perturbedFlow_apply`); `TauCeti.perturbedFlow_congr`: it does not depend on the
  Lipschitz witness for `∇ f`. `TauCeti.exists_lipschitzWith_gradient_perturb` supplies
  the Lipschitz hypothesis needed to speak of that flow.
* `TauCeti.hasDerivAt_fst_fderiv_perturbedFlow_apply`: at the parameter `0`, the derivative of the
  perturbed flow along a tangent vector `(v, e)` solves the inhomogeneous variational equation
  `u' = -D(∇f)(φₜ x) u - ∑ᵢ eᵢ ∇hᵢ(φₜ x)` along the negative-gradient orbit of `x`, with
  `TauCeti.perturbedFlow_apply_zero` and `TauCeti.snd_fderiv_perturbedFlow_apply`.
* `TauCeti.fst_fderiv_perturbedFlow_apply_eq_neg_integral`: Duhamel's formula for the derivative
  of the perturbed flow in a parameter direction at the parameter `0`.
* `TauCeti.negativeGradientFlow_perturb_apply_eq`, `TauCeti.mem_stableSet_perturb_iff`,
  `TauCeti.mem_unstableSet_perturb_iff`: away from the supports of the family, the perturbed flow,
  and membership in stable and unstable sets, are those of `f`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014
  (transversality of the unstable and stable manifolds of a Morse function by perturbation).
* S. Smale, *On gradient dynamical systems*, Ann. of Math. **74** (1961), 199--206.
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
@[simp]
theorem perturb_apply (f : E → ℝ) (h : ι → E → ℝ) (s : EuclideanSpace ℝ ι) (x : E) :
    perturb f h s x = f x + ∑ i, s i * h i x :=
  (rfl)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem perturb_zero (f : E → ℝ) (h : ι → E → ℝ) : perturb f h 0 = f := by
  ext x
  simp [perturb_apply]

end Perturb

section Differential

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] {f : E → ℝ} {h : ι → E → ℝ}

/-- The differential of a perturbation is the perturbed differential. -/
@[simp]
theorem fderiv_perturb {x : E} (hf : DifferentiableAt ℝ f x)
    (hh : ∀ i, DifferentiableAt ℝ (h i) x) (s : EuclideanSpace ℝ ι) :
    fderiv ℝ (perturb f h s) x = fderiv ℝ f x + ∑ i, s i • fderiv ℝ (h i) x := by
  have hs : HasFDerivAt (fun y ↦ ∑ i, s i • h i y) (∑ i, s i • fderiv ℝ (h i) x) x :=
    HasFDerivAt.fun_sum fun i _ ↦ (hh i).hasFDerivAt.const_smul (s i)
  have e : perturb f h s = fun y ↦ f y + ∑ i, s i • h i y :=
    funext fun y ↦ by simp [perturb_apply, smul_eq_mul]
  rw [e]
  exact (hf.hasFDerivAt.add hs).fderiv

/-- The perturbation of a `Cⁿ` function by `Cⁿ` functions is `Cⁿ`. -/
theorem contDiff_perturb {n : WithTop ℕ∞} (hfs : ContDiff ℝ n f) (hh : ∀ i, ContDiff ℝ n (h i))
    (s : EuclideanSpace ℝ ι) :
    ContDiff ℝ n (perturb f h s) :=
  hfs.add (ContDiff.sum fun i _ ↦ contDiff_const.mul (hh i))

omit [NormedSpace ℝ E] in
/-- A perturbation agrees with `f` near each point outside the supports of the family. -/
theorem perturb_eventuallyEq_of_forall_notMem_tsupport {x : E} (s : EuclideanSpace ℝ ι)
    (hx : ∀ i, x ∉ tsupport (h i)) : perturb f h s =ᶠ[𝓝 x] f := by
  have hi : ∀ i, ∀ᶠ y in 𝓝 x, h i y = 0 := fun i ↦ notMem_tsupport_iff_eventuallyEq.1 (hx i)
  filter_upwards [eventually_all.2 hi] with y hy
  simp [perturb_apply, hy]

/-- **Near a critical point of `f`, a perturbation agrees with `f`.** The functions of an admissible
family vanish on a neighbourhood of each critical point. -/
theorem perturb_eventuallyEq_of_fderiv_eq_zero (hh : ∀ i, IsAdmissiblePerturbation f (h i))
    (s : EuclideanSpace ℝ ι) {x : E} (hx : fderiv ℝ f x = 0) : perturb f h s =ᶠ[𝓝 x] f :=
  perturb_eventuallyEq_of_forall_notMem_tsupport s fun i hmem ↦
    Set.disjoint_left.1 (hh i).disjoint hmem hx

/-- **Small perturbations keep the critical points.** For a family of compactly supported `C¹`
functions whose supports avoid the critical points of `f` (for instance an admissible family), for
all sufficiently small parameters the critical points of `perturb f h s` are those of `f`. -/
theorem exists_pos_forall_fderiv_perturb_eq_zero_iff (hfs : ContDiff ℝ 1 f)
    (hh : ∀ i, ContDiff ℝ 1 (h i)) (hc : ∀ i, HasCompactSupport (h i))
    (hdisj : ∀ i, Disjoint (tsupport (h i)) {x | fderiv ℝ f x = 0}) :
    ∃ δ > 0, ∀ s : EuclideanSpace ℝ ι, ‖s‖ < δ → ∀ x,
      (fderiv ℝ (perturb f h s) x = 0 ↔ fderiv ℝ f x = 0) := by
  have hfd : Differentiable ℝ f := hfs.differentiable (by norm_num)
  have hhd : ∀ i, Differentiable ℝ (h i) := fun i ↦ (hh i).differentiable (by norm_num)
  -- A bound on the differentials of the perturbing functions.
  have hB : ∀ i, ∃ C : ℝ, ∀ x, ‖fderiv ℝ (h i) x‖ ≤ C := fun i ↦
    ((hc i).fderiv ℝ).exists_bound_of_continuous ((hh i).continuous_fderiv (by norm_num))
  choose B hB using hB
  obtain ⟨C, hC⟩ := Finite.exists_le B
  -- A lower bound for the differential of `f` on the supports.
  set A : Set E := ⋃ i, tsupport (h i)
  have hA : IsCompact A := isCompact_iUnion hc
  have hAcrit : ∀ x ∈ A, fderiv ℝ f x ≠ 0 := fun x hx hx0 ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    exact Set.disjoint_left.1 (hdisj i) hi hx0
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
    rw [fderiv_perturb (hfd x) fun i ↦ hhd i x]
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
    have hev : perturb f h s =ᶠ[𝓝 x] f :=
      perturb_eventuallyEq_of_forall_notMem_tsupport s fun i hmem ↦ hx (mem_iUnion.2 ⟨i, hmem⟩)
    rw [hev.fderiv_eq]

end Differential

section Witness

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [HasContDiffBump E]
  {f : E → ℝ}

/-- **Bumps away from the critical points give admissible perturbations.** If the closed support of
a smooth bump `θ` contains no critical point of `f`, then `θ g` is an admissible perturbation of
`f` for every `C²` function `g`; for instance `x ↦ θ x * ⟪v, x - z⟫`. -/
theorem _root_.ContDiffBump.isAdmissiblePerturbation_mul {z : E} (θ : ContDiffBump z)
    (hθ : ∀ x ∈ Metric.closedBall z θ.rOut, fderiv ℝ f x ≠ 0) {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    IsAdmissiblePerturbation f fun x ↦ θ x * g x where
  contDiff := θ.contDiff.mul hg
  hasCompactSupport := θ.hasCompactSupport.mul_right
  disjoint := Set.disjoint_left.2 fun x hx hx0 ↦ by
    have hxθ : x ∈ tsupport (θ : E → ℝ) := tsupport_mul_subset_left hx
    rw [θ.tsupport_eq] at hxθ
    exact hθ x hxθ hx0

end Witness

section Gradient

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  {f : E → ℝ} {h : ι → E → ℝ}

/-- The gradient of a perturbation is the perturbed gradient. -/
@[simp]
theorem gradient_perturb {x : E} (hf : DifferentiableAt ℝ f x)
    (hh : ∀ i, DifferentiableAt ℝ (h i) x) (s : EuclideanSpace ℝ ι) :
    ∇ (perturb f h s) x = ∇ f x + ∑ i, s i • ∇ (h i) x := by
  simp only [gradient, fderiv_perturb hf hh, map_add, map_sum, map_smul]

end Gradient

section AwayFromSupport

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]
  {f : E → ℝ} {h : ι → E → ℝ} {K : ℝ≥0}

/-- Outside the supports of the family, the gradient of a perturbation is the gradient of `f`. -/
theorem gradient_perturb_of_forall_notMem_tsupport (s : EuclideanSpace ℝ ι) {x : E}
    (hx : ∀ i, x ∉ tsupport (h i)) : ∇ (perturb f h s) x = ∇ f x := by
  rw [gradient, (perturb_eventuallyEq_of_forall_notMem_tsupport s hx).fderiv_eq, gradient]

/-- **Away from the perturbation, the perturbed flow is the flow of `f`.** If the orbit segment
`{φ_τ y | τ ∈ [[0, t]]}` of the negative-gradient flow of `f` avoids the supports of the family,
then the negative-gradient flow of `perturb f h s` sends `y` at time `t` to `φ_t y`. -/
theorem negativeGradientFlow_perturb_apply_eq (hf : LipschitzWith K (∇ f))
    {s : EuclideanSpace ℝ ι} {K' : ℝ≥0} (hf' : LipschitzWith K' (∇ (perturb f h s))) {y : E}
    {t : ℝ} (hy : ∀ τ ∈ uIcc 0 t, ∀ i, negativeGradientFlow f hf τ y ∉ tsupport (h i)) :
    negativeGradientFlow (perturb f h s) hf' t y = negativeGradientFlow f hf t y :=
  negativeGradientFlow_apply_eq_of_gradient_eq hf' hf fun τ hτ ↦
    gradient_perturb_of_forall_notMem_tsupport s (hy τ hτ)

/-- **Stable sets away from the perturbation.** If the forward orbit of `y` under the
negative-gradient flow of `f` avoids the supports of the family, then `y` lies in the stable set
of a point `q` for the perturbed flow if and only if it does for the flow of `f`. -/
theorem mem_stableSet_perturb_iff (hf : LipschitzWith K (∇ f)) {s : EuclideanSpace ℝ ι}
    {K' : ℝ≥0} (hf' : LipschitzWith K' (∇ (perturb f h s))) {y q : E}
    (hy : ∀ τ, 0 ≤ τ → ∀ i, negativeGradientFlow f hf τ y ∉ tsupport (h i)) :
    y ∈ Flow.stableSet (negativeGradientFlow (perturb f h s) hf') q ↔
      y ∈ Flow.stableSet (negativeGradientFlow f hf) q := by
  have heq : (fun t ↦ negativeGradientFlow (perturb f h s) hf' t y) =ᶠ[atTop]
      fun t ↦ negativeGradientFlow f hf t y := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    refine negativeGradientFlow_perturb_apply_eq hf hf' fun τ hτ ↦ hy τ ?_
    rw [uIcc_of_le ht] at hτ
    exact hτ.1
  simp only [Flow.mem_stableSet]
  exact tendsto_congr' heq

/-- **Unstable sets away from the perturbation.** If the backward orbit of `y` under the
negative-gradient flow of `f` avoids the supports of the family, then `y` lies in the unstable set
of a point `p` for the perturbed flow if and only if it does for the flow of `f`. -/
theorem mem_unstableSet_perturb_iff (hf : LipschitzWith K (∇ f)) {s : EuclideanSpace ℝ ι}
    {K' : ℝ≥0} (hf' : LipschitzWith K' (∇ (perturb f h s))) {y p : E}
    (hy : ∀ τ, τ ≤ 0 → ∀ i, negativeGradientFlow f hf τ y ∉ tsupport (h i)) :
    y ∈ Flow.unstableSet (negativeGradientFlow (perturb f h s) hf') p ↔
      y ∈ Flow.unstableSet (negativeGradientFlow f hf) p := by
  have heq : (fun t ↦ negativeGradientFlow (perturb f h s) hf' t y) =ᶠ[atBot]
      fun t ↦ negativeGradientFlow f hf t y := by
    filter_upwards [eventually_le_atBot 0] with t ht
    refine negativeGradientFlow_perturb_apply_eq hf hf' fun τ hτ ↦ hy τ ?_
    rw [uIcc_of_ge ht] at hτ
    exact hτ.2
  simp only [Flow.mem_unstableSet]
  exact tendsto_congr' heq

end AwayFromSupport

section Flow

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  {f : E → ℝ} {h : ι → E → ℝ} {K : ℝ≥0}

/-- A smooth cutoff of the parameter, equal to `1` on the closed unit ball and supported in the
closed ball of radius `2`. -/
private noncomputable def perturbationBump : ContDiffBump (0 : EuclideanSpace ℝ ι) :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off parameter `s ↦ φ(s) • s`, with `φ` a smooth bump equal to `1` on the closed unit
ball: it is the identity on the closed unit ball and has compact support. -/
private noncomputable def perturbationCutoff (s : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  perturbationBump.toFun s • s

private theorem contDiff_perturbationCutoff : ContDiff ℝ 1 (perturbationCutoff (ι := ι)) :=
  perturbationBump.contDiff.smul contDiff_id

private theorem hasCompactSupport_perturbationCutoff :
    HasCompactSupport (perturbationCutoff (ι := ι)) :=
  perturbationBump.hasCompactSupport.smul_right

@[simp]
private theorem perturbationCutoff_eq_self_of_norm_le {s : EuclideanSpace ℝ ι} (hs : ‖s‖ ≤ 1) :
    perturbationCutoff s = s := by
  have hr : (perturbationBump (ι := ι)).rIn = 1 := (rfl)
  have hb : perturbationBump.toFun s = 1 :=
    perturbationBump.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, hr]; exact hs)
  rw [perturbationCutoff, hb, one_smul]

/-- The part of the augmented field that couples the state to the parameter. -/
private noncomputable def coupling (h : ι → E → ℝ) (p : E × EuclideanSpace ℝ ι) : E :=
  ∑ i, perturbationCutoff p.2 i • ∇ (h i) p.1

private theorem contDiff_coupling (hh : ∀ i, ContDiff ℝ 2 (h i)) :
    ContDiff ℝ 1 (coupling h) := by
  refine ContDiff.sum fun i _ ↦ ?_
  have h1 : ContDiff ℝ 1 fun p : E × EuclideanSpace ℝ ι ↦ perturbationCutoff p.2 i :=
    ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff.comp
      contDiff_perturbationCutoff).comp contDiff_snd
  have h2 : ContDiff ℝ 1 fun p : E × EuclideanSpace ℝ ι ↦ ∇ (h i) p.1 :=
    ((hh i).gradient_right (m := 1) (by norm_num)).comp contDiff_fst
  exact h1.smul h2

private theorem hasCompactSupport_coupling (hc : ∀ i, HasCompactSupport (h i)) :
    HasCompactSupport (coupling h) := by
  have hA : IsCompact (⋃ i, tsupport (h i)) := isCompact_iUnion hc
  refine HasCompactSupport.intro (hA.prod perturbationBump.hasCompactSupport) fun p hp ↦ ?_
  rw [mem_prod, not_and_or] at hp
  rcases hp with hp | hp
  · exact Finset.sum_eq_zero fun i _ ↦ by
      rw [gradient_of_notMem_tsupport fun hmem ↦ hp (mem_iUnion.2 ⟨i, hmem⟩), smul_zero]
  · have : perturbationBump.toFun p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
    simp [coupling, perturbationCutoff, this]

/-- **The augmented field.** The vector field on `E × EuclideanSpace ℝ ι` whose first component
is `-∇ f x - ∑ᵢ a(s)ᵢ ∇ hᵢ x`, with `a` the cutoff of the parameter, and whose second component is
zero: the parameter is constant along its orbits. -/
private noncomputable def perturbedField (f : E → ℝ) (h : ι → E → ℝ)
    (p : E × EuclideanSpace ℝ ι) : E × EuclideanSpace ℝ ι :=
  (-∇ f p.1 - coupling h p, 0)

@[simp]
private theorem perturbedField_apply (x : E) (s : EuclideanSpace ℝ ι) :
    perturbedField f h (x, s) = (-∇ f x - ∑ i, perturbationCutoff s i • ∇ (h i) x, 0) :=
  (rfl)

/-- For a parameter of norm at most `1`, the augmented field is the negative gradient of the
perturbation, with zero parameter component. -/
private theorem perturbedField_apply_of_norm_le (hf : Differentiable ℝ f)
    (hh : ∀ i, Differentiable ℝ (h i)) {s : EuclideanSpace ℝ ι} (hs : ‖s‖ ≤ 1)
    (x : E) : perturbedField f h (x, s) = (-∇ (perturb f h s) x, 0) := by
  rw [perturbedField_apply, perturbationCutoff_eq_self_of_norm_le hs,
    gradient_perturb (hf x) (fun i ↦ hh i x), neg_add', sub_eq_add_neg]

/-- The gradient of a perturbation of `f` by compactly supported `C²` functions is Lipschitz if
the gradient of `f` is, so its negative-gradient flow is defined. -/
theorem exists_lipschitzWith_gradient_perturb (hf : Differentiable ℝ f)
    (hK : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (s : EuclideanSpace ℝ ι) :
    ∃ K' : ℝ≥0, LipschitzWith K' (∇ (perturb f h s)) := by
  have hg : ∀ i, HasCompactSupport (∇ (h i)) := fun i ↦
    ((hc i).fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (map_zero _)
  have hcs : HasCompactSupport fun x ↦ ∑ i, s i • ∇ (h i) x := by
    convert HasCompactSupport.finset_sum (s := Finset.univ)
      fun i _ ↦ (hg i).smul_left (f := fun _ ↦ s i) using 1
    ext x
    simp
  have hd : ContDiff ℝ 1 fun x ↦ ∑ i, s i • ∇ (h i) x :=
    ContDiff.sum fun i _ ↦
      contDiff_const.smul ((hh i).gradient_right (m := 1) (by norm_num))
  obtain ⟨C, hC⟩ := hd.lipschitzWith_of_hasCompactSupport hcs one_ne_zero
  have e : ∇ (perturb f h s) = fun x ↦ ∇ f x + ∑ i, s i • ∇ (h i) x :=
    funext fun x ↦
      gradient_perturb (hf x) (fun i ↦ (hh i).differentiable (by norm_num) x) s
  exact ⟨_, e ▸ hK.add hC⟩

private theorem exists_lipschitzWith_perturbedField (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    ∃ K' : ℝ≥0, LipschitzWith K' (perturbedField f h) := by
  obtain ⟨C, hC⟩ := (contDiff_coupling hh).lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_coupling hc) one_ne_zero
  unfold perturbedField
  exact ⟨_, ((hf.comp LipschitzWith.prod_fst).neg.sub hC).prodMk (LipschitzWith.const 0)⟩

private theorem contDiff_perturbedField (hfs : ContDiff ℝ 2 f) (hh : ∀ i, ContDiff ℝ 2 (h i)) :
    ContDiff ℝ 1 (perturbedField f h) := by
  unfold perturbedField
  exact (((hfs.gradient_right (m := 1) (by norm_num)).comp contDiff_fst).neg.sub
    (contDiff_coupling hh)).prodMk contDiff_const

/-- **The flow of the cut-off augmented field** on `E × EuclideanSpace ℝ ι`: the field is
`(x, s) ↦ (-∇ f x - ∑ᵢ a(s)ᵢ ∇ hᵢ x, 0)`, with `a` a smooth cutoff of the parameter equal to the
identity on the closed unit ball. The parameter is constant along its orbits, and for `‖s‖ ≤ 1` the
first component is the negative-gradient flow of `perturb f h s`
(`perturbedFlow_apply_of_norm_le`); outside the unit ball it is the flow of the cut-off field,
not of `perturb f h s`. -/
noncomputable def perturbedFlow (f : E → ℝ) (h : ι → E → ℝ) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    Flow ℝ (E × EuclideanSpace ℝ ι) :=
  flowOfLipschitz (perturbedField f h) (exists_lipschitzWith_perturbedField hf hh hc).choose_spec

/-- The perturbed flow is, by its definition, the flow of the augmented field with the chosen
Lipschitz witness. -/
private theorem perturbedFlow_eq_flowOfLipschitz (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) :
    perturbedFlow f h hf hh hc = flowOfLipschitz (perturbedField f h)
      (exists_lipschitzWith_perturbedField hf hh hc).choose_spec :=
  (rfl)

/-- **Independence of the Lipschitz witness.** The perturbed flow does not depend on the Lipschitz
bound for `∇ f` used to construct it: the Lipschitz constant of the augmented field is chosen from a
proposition that does not mention that bound. -/
theorem perturbedFlow_congr {K' : ℝ≥0} (hf : LipschitzWith K (∇ f)) (hf' : LipschitzWith K' (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    perturbedFlow f h hf hh hc = perturbedFlow f h hf' hh hc :=
  (rfl)

/-- **The perturbed flow is `C¹`**, jointly in time, the initial condition and the parameter. -/
theorem contDiff_perturbedFlow (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (hc : ∀ i, HasCompactSupport (h i)) :
    ContDiff ℝ 1 (Function.uncurry (perturbedFlow f h hf hh hc)) := by
  have hF : ContDiff ℝ ((0 : ℕ) + 1) (perturbedField f h) := by
    simpa using contDiff_perturbedField hfs hh
  unfold perturbedFlow
  simpa using contDiff_flowOfLipschitz 0 (perturbedField f h)
    (exists_lipschitzWith_perturbedField hf hh hc).choose_spec hF

/-- **The parameter is constant along the perturbed flow.** -/
@[simp]
theorem snd_perturbedFlow_apply (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (t : ℝ) (p : E × EuclideanSpace ℝ ι) :
    (perturbedFlow f h hf hh hc t p).2 = p.2 := by
  have hd : ∀ u, HasDerivAt (fun u ↦ (perturbedFlow f h hf hh hc u p).2) 0 u := fun u ↦ by
    have h0 :=
      hasDerivAt_flowOfLipschitz (exists_lipschitzWith_perturbedField hf hh hc).choose_spec p u
    exact (hasFDerivAt_snd.comp_hasDerivAt u h0).congr_deriv (by simp [perturbedField])
  have := is_const_of_deriv_eq_zero (fun u ↦ (hd u).differentiableAt) (fun u ↦ (hd u).deriv) t 0
  simpa using this

/-- **The perturbed flow is the negative-gradient flow of the perturbation.** For a parameter `s`
of norm at most `1`, the perturbed flow sends `(x, s)` at time `t` to the pair of the time-`t`
image of `x` under the negative-gradient flow of `perturb f h s`, and `s`. -/
theorem perturbedFlow_apply_of_norm_le (hd : Differentiable ℝ f) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) {s : EuclideanSpace ℝ ι} (hs : ‖s‖ ≤ 1)
    {K' : ℝ≥0} (hf' : LipschitzWith K' (∇ (perturb f h s))) (t : ℝ) (x : E) :
    perturbedFlow f h hf hh hc t (x, s) = (negativeGradientFlow (perturb f h s) hf' t x, s) := by
  set φ := negativeGradientFlow (perturb f h s) hf'
  have hγ : ∀ t, HasDerivAt (fun t ↦ (φ t x, s)) (perturbedField f h (φ t x, s)) t := by
    intro t
    have h1 : HasDerivAt (fun t ↦ φ t x) (-∇ (perturb f h s) (φ t x)) t :=
      (isNegativeGradient_negativeGradientFlow (perturb f h s) hf').isIntegralCurve x t
    rw [perturbedField_apply_of_norm_le hd
      (fun i ↦ (hh i).differentiable (by norm_num)) hs]
    exact h1.prodMk (hasDerivAt_const t s)
  have := eq_flowOfLipschitz (exists_lipschitzWith_perturbedField hf hh hc).choose_spec hγ t
  rw [perturbedFlow_eq_flowOfLipschitz]
  simpa using this.symm

end Flow

section ParameterDerivative

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  {f : E → ℝ} {h : ι → E → ℝ} {K : ℝ≥0}

/-- At the parameter `0` the perturbed flow is the negative-gradient flow of `f`. -/
@[simp]
theorem perturbedFlow_apply_zero (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (t : ℝ) (x : E) :
    perturbedFlow f h hf hh hc t (x, 0) = (negativeGradientFlow f hf t x, 0) := by
  set φ := negativeGradientFlow f hf
  -- On the zero-parameter slice the augmented field is `(-∇ f, 0)`.
  have hγ : ∀ t, HasDerivAt (fun t ↦ (φ t x, (0 : EuclideanSpace ℝ ι)))
      (perturbedField f h (φ t x, 0)) t := fun t ↦ by
    have hF : perturbedField f h (φ t x, 0) = (-∇ f (φ t x), 0) := by
      simp [perturbationCutoff]
    rw [hF]
    exact ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve x t).prodMk
      (hasDerivAt_const t 0)
  have := eq_flowOfLipschitz (exists_lipschitzWith_perturbedField hf hh hc).choose_spec hγ t
  rw [perturbedFlow_eq_flowOfLipschitz]
  simpa using this.symm

private theorem differentiableAt_perturbedFlow (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (t : ℝ)
    (p : E × EuclideanSpace ℝ ι) : DifferentiableAt ℝ (perturbedFlow f h hf hh hc t) p := by
  rw [perturbedFlow_eq_flowOfLipschitz]
  exact differentiable_flowOfLipschitz_apply _ (contDiff_perturbedField hfs hh) t p

/-- **The parameter component of a variation is constant**: the derivative of the time-`t` map
of the perturbed flow does not change the parameter component of a tangent vector. -/
@[simp]
theorem snd_fderiv_perturbedFlow_apply (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (t : ℝ) (p q : E × EuclideanSpace ℝ ι) :
    (fderiv ℝ (perturbedFlow f h hf hh hc t) p q).2 = q.2 := by
  have h1 := hasFDerivAt_snd.comp p (differentiableAt_perturbedFlow hfs hf hh hc t p).hasFDerivAt
  have hsnd : (fun p ↦ (perturbedFlow f h hf hh hc t p).2) = Prod.snd :=
    funext fun p ↦ snd_perturbedFlow_apply hf hh hc t p
  have h2 : HasFDerivAt (fun p ↦ (perturbedFlow f h hf hh hc t p).2)
      (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ ι)) p := by
    rw [hsnd]
    exact hasFDerivAt_snd
  simpa using congrArg (· q) (h1.unique h2)

/-- The cut-off parameter is the identity near `0`. -/
private theorem hasFDerivAt_perturbationCutoff_zero :
    HasFDerivAt (perturbationCutoff (ι := ι)) (ContinuousLinearMap.id ℝ _) 0 := by
  have hev : perturbationCutoff (ι := ι) =ᶠ[𝓝 0] id := by
    filter_upwards [perturbationBump.eventuallyEq_one] with s hs
    simp [perturbationCutoff, hs]
  exact (hasFDerivAt_id 0).congr_of_eventuallyEq hev

/-- The derivative of the augmented field at a point of parameter `0`. -/
private theorem fderiv_perturbedField_apply_zero (hfs : ContDiff ℝ 2 f)
    (hh : ∀ i, ContDiff ℝ 2 (h i)) (y u : E) (e : EuclideanSpace ℝ ι) :
    fderiv ℝ (perturbedField f h) (y, 0) (u, e) =
      (-(fderiv ℝ (∇ f) y) u - ∑ i, e i • ∇ (h i) y, 0) := by
  have hG := ((hfs.gradient_right (m := 1) (by norm_num)).differentiable one_ne_zero
    y).hasFDerivAt.comp (y, (0 : EuclideanSpace ℝ ι)) (hasFDerivAt_fst (𝕜 := ℝ))
  have hC := fun i ↦
    ((((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).hasFDerivAt.comp 0
      hasFDerivAt_perturbationCutoff_zero).comp (y, (0 : EuclideanSpace ℝ ι))
        (hasFDerivAt_snd (𝕜 := ℝ))).smul
      ((((hh i).gradient_right (m := 1) (by norm_num)).differentiable
        one_ne_zero y).hasFDerivAt.comp (y, (0 : EuclideanSpace ℝ ι)) (hasFDerivAt_fst (𝕜 := ℝ))))
  have hV : HasFDerivAt (perturbedField f h) _ (y, (0 : EuclideanSpace ℝ ι)) :=
    (hG.neg.sub (HasFDerivAt.fun_sum fun i _ ↦ hC i)).prodMk (hasFDerivAt_const _ _)
  rw [hV.fderiv]
  simp

/-- **The variation of the perturbed flow.** At the parameter `0`, the derivative
`u t = (Dφₜ(x, 0) q).1` of the perturbed flow along a tangent vector `q = (v, e)` solves the
inhomogeneous variational equation along the negative-gradient orbit `φₜ x` of `f`:
`u' = -D(∇f)(φₜ x) u - ∑ᵢ eᵢ ∇hᵢ(φₜ x)`. For `q = (0, e)` this is the derivative of
`s ↦ φ^{f + ∑ sᵢ hᵢ}_t x` at `s = 0` in the direction `e`; for `q = (v, 0)` it is the variational
equation of the negative-gradient flow of `f`. -/
theorem hasDerivAt_fst_fderiv_perturbedFlow_apply (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (x : E)
    (q : E × EuclideanSpace ℝ ι) (t : ℝ) :
    HasDerivAt (fun τ ↦ (fderiv ℝ (perturbedFlow f h hf hh hc τ) (x, 0) q).1)
      (-(fderiv ℝ (∇ f) (negativeGradientFlow f hf t x))
          (fderiv ℝ (perturbedFlow f h hf hh hc t) (x, 0) q).1 -
        ∑ i, q.2 i • ∇ (h i) (negativeGradientFlow f hf t x)) t := by
  have h0 := hasDerivAt_fderiv_flowOfLipschitz_apply
    (exists_lipschitzWith_perturbedField hf hh hc).choose_spec (contDiff_perturbedField hfs hh)
    (x, 0) q t
  rw [← perturbedFlow_eq_flowOfLipschitz hf hh hc, perturbedFlow_apply_zero hf hh hc] at h0
  set w := fderiv ℝ (perturbedFlow f h hf hh hc t) (x, 0) q with hw
  have hw2 : w = (w.1, q.2) := Prod.ext rfl (snd_fderiv_perturbedFlow_apply hfs hf hh hc t _ _)
  rw [hw2, fderiv_perturbedField_apply_zero hfs hh] at h0
  exact hasFDerivAt_fst.comp_hasDerivAt t h0

/-- **Duhamel's formula for the parameter variation.** At the parameter `0`, the derivative of the
perturbed flow in a parameter direction `e` is
`-Dφ_T(x) ∫₀ᵀ Dφ_{-σ}(φ_σ x) (∑ᵢ eᵢ ∇hᵢ(φ_σ x)) dσ`, where `φ` is the negative-gradient flow of
`f`: the perturbation `∑ᵢ eᵢ ∇hᵢ` met along the orbit is transported back to time `0`,
integrated, and carried forward to time `T`. -/
theorem fst_fderiv_perturbedFlow_apply_eq_neg_integral (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hc : ∀ i, HasCompactSupport (h i)) (x : E)
    (e : EuclideanSpace ℝ ι) (T : ℝ) :
    (fderiv ℝ (perturbedFlow f h hf hh hc T) (x, 0) (0, e)).1 =
      -fderiv ℝ (negativeGradientFlow f hf T) x
        (∫ σ in (0 : ℝ)..T, fderiv ℝ (negativeGradientFlow f hf (-σ))
          (negativeGradientFlow f hf σ x)
          (∑ i, e i • ∇ (h i) (negativeGradientFlow f hf σ x))) := by
  set φ := negativeGradientFlow f hf
  have hφd : ∀ t, Differentiable ℝ (φ t) := differentiable_negativeGradientFlow_apply f hf hfs
  set M : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ (φ t) x
  set N : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ (φ (-t)) (φ t x)
  set u : ℝ → E := fun t ↦ (fderiv ℝ (perturbedFlow f h hf hh hc t) (x, 0) (0, e)).1
  set b : ℝ → E := fun t ↦ ∑ i, e i • ∇ (h i) (φ t x)
  have hs : ∀ t, DifferentiableAt ℝ (φ (-t)) (φ t x) := fun t ↦ hφd (-t) _
  have hinv : ∀ t, Ring.inverse (M t) = N t := fun t ↦ Flow.ringInverse_fderiv (hs t) (hφd t x)
  have hMN : ∀ t v, M t (N t v) = v := fun t v ↦
    Flow.fderiv_apply_fderiv_neg (hs t) (hφd t x) v
  have hM : ∀ t, HasDerivAt M (-(fderiv ℝ (∇ f) (φ t x)).comp (M t)) t :=
    hasDerivAt_fderiv_negativeGradientFlow f hf hfs x
  have hu : ∀ t, HasDerivAt u (-(fderiv ℝ (∇ f) (φ t x)) (u t) - b t) t := fun t ↦ by
    simpa using hasDerivAt_fst_fderiv_perturbedFlow_apply hfs hf hh hc x (0, e) t
  -- The inverse of `Dφₜ(x)` moves with derivative `Dφ_{-t}(φₜ x) ∘ D(∇f)(φₜ x)`.
  have hN : ∀ t, HasDerivAt (fun τ ↦ Ring.inverse (M τ))
      (N t * (fderiv ℝ (∇ f) (φ t x)).comp (M t) * N t) t := fun t ↦ by
    have hU := hasFDerivAt_ringInverse (𝕜 := ℝ) (Flow.fderivUnit (hs t) (hφd t x))
    rw [Flow.coe_fderivUnit] at hU
    refine (hU.comp_hasDerivAt t (hM t)).congr_deriv ?_
    simp [N]
  have hW : ∀ t, HasDerivAt (fun τ ↦ Ring.inverse (M τ) (u τ)) (-(N t (b t))) t := fun t ↦ by
    refine ((hN t).clm_apply (hu t)).congr_deriv ?_
    rw [hinv, mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply, hMN, map_sub, map_neg]
    abel
  have hcont : Continuous fun σ ↦ -(N σ (b σ)) := by
    have hN' : Continuous fun σ ↦ N σ := continuous_fderiv_negativeGradientFlow_neg f hf hfs x
    have horb : Continuous fun σ ↦ φ σ x :=
      (contDiff_negativeGradientFlow f hf hfs).continuous.comp
        (continuous_id.prodMk continuous_const)
    have hb : Continuous b := continuous_finsetSum _ fun i _ ↦ continuous_const.smul
      ((((hh i).gradient_right (m := 1) (by norm_num)).continuous).comp horb)
    exact (hN'.clm_apply hb).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hW t)
    (hcont.intervalIntegrable 0 T)
  have hu0 : u 0 = 0 := by simp [u, Flow.map_zero]
  rw [hu0, map_zero, sub_zero, intervalIntegral.integral_neg, hinv] at hFTC
  calc u T = M T (N T (u T)) := (hMN T _).symm
    _ = -M T (∫ σ in (0 : ℝ)..T, N σ (b σ)) := by rw [← hFTC, map_neg]

end ParameterDerivative

end TauCeti
