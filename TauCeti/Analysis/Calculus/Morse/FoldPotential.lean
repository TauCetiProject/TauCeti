/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Fredholm
public import TauCeti.Analysis.Calculus.Morse.OneDimensional
public import TauCeti.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The cubic fold potential and its negative-gradient dynamics

The one-parameter family of cubic polynomials `f_μ(x) = x³ / 3 + μ x` (`TauCeti.foldPotential`) is
the canonical one-dimensional Cerf normal form of an ordinary birth-death (`A₂` or fold)
bifurcation. Its negative-gradient equation is the scalar Riccati ODE `x'(s) = -x(s)² - μ`.

At `(μ, x) = (0, 0)` the family exhibits the two defining `A₂` invariants: its third spatial
derivative is `2 ≠ 0` (`TauCeti.iteratedDeriv_three_foldPotential`) and the parameter derivative of
its spatial derivative is `1 ≠ 0` (`TauCeti.hasDerivAt_deriv_foldPotential_param`). Varying `μ`
across `0` sweeps out the complete bifurcation trichotomy for critical points and global
negative-gradient trajectories:

* **For `μ > 0`**, `f_μ` has no critical points and every global trajectory diverges to `-∞` at
  `+∞` and to `+∞` at `-∞`; no trajectory converges at either end.
* **At `μ = 0`**, `0` is the unique critical point and is degenerate, while the constant zero curve
  is the unique global trajectory with finite limits at both ends
  (`TauCeti.eq_zero_of_isIntegralCurve_foldPotential_zero`).
* **For `μ = -a² < 0` (`a > 0`)**, `f_{-a²}` has two nondegenerate critical points: `-a` of Morse
  index `1` and `a` of Morse index `0`. Consequently `f_μ` has nondegenerate critical points on `ℝ`
  if and only if `μ ≠ 0` (`TauCeti.hasNondegenerateCriticalPointsOn_foldPotential_iff`).

For `μ = -a²` (`a > 0`), the open interval `(-a, a)` is parametrized by the inverse-hyperbolic
time coordinate `U_a(x) = a⁻¹ * artanh (x / a)` (`TauCeti.foldTimeCoordinate`), whose inverse is
the reference connecting orbit `q_a(s) = a * tanh (a * s)` (`TauCeti.foldOrbit`). Every global
trajectory from `-a` to `a` is a unique time translate `s ↦ q_a (s + s₀)` with `s₀ = U_a(γ 0)`
(`TauCeti.existsUnique_foldOrbit_add_of_isIntegralCurve`), and no trajectory runs from `a` to `-a`
(`TauCeti.not_isIntegralCurve_foldPotential_self_to_neg`). Along any connecting trajectory from
`-a` to `a`, the linearized operator `ξ ↦ ξ' + 2 γ ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is
Fredholm of index `1`, surjective, has kernel spanned by `γ'`, and has injective formal adjoint;
at `-a` and `a` the constant-coefficient operators are bijective.

## Main declarations

* `TauCeti.foldPotential`, `TauCeti.foldOrbit`, `TauCeti.foldTimeCoordinate`.
* `TauCeti.iteratedDeriv_three_foldPotential`, `TauCeti.hasDerivAt_deriv_foldPotential_param`,
  `TauCeti.hasNondegenerateCriticalPointsOn_foldPotential_iff`.
* `TauCeti.eq_of_isIntegralCurve_foldPotential`,
  `TauCeti.tendsto_atTop_atBot_of_isIntegralCurve_foldPotential_of_pos`,
  `TauCeti.eq_zero_of_isIntegralCurve_foldPotential_zero`,
  `TauCeti.existsUnique_foldOrbit_add_of_isIntegralCurve`,
  `TauCeti.not_isIntegralCurve_foldPotential_self_to_neg`.
* `TauCeti.isFredholm_trajectoryOperator_foldPotential`,
  `TauCeti.index_trajectoryOperator_foldPotential`,
  `TauCeti.exists_ker_trajectoryOperator_foldPotential_eq_span`,
  `TauCeti.surjective_trajectoryOperator_foldPotential`,
  `TauCeti.ker_trajectoryOperator_neg_foldPotential_eq_bot`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173.
* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2.
-/

public section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

namespace TauCeti

/-! ### The cubic fold potential and its `A₂` invariants -/

/-- The one-dimensional cubic fold potential `f_μ(x) = x³ / 3 + μ x`, whose negative gradient is
`-x² - μ`. -/
noncomputable def foldPotential (μ x : ℝ) : ℝ :=
  x ^ 3 / 3 + μ * x

theorem foldPotential_apply (μ x : ℝ) : foldPotential μ x = x ^ 3 / 3 + μ * x :=
  (rfl)

@[simp]
theorem foldPotential_zero_right (μ : ℝ) : foldPotential μ 0 = 0 := by
  simp [foldPotential]

/-- The fold potential is odd in `x`: `f_μ(-x) = -f_μ(x)`. -/
@[simp]
theorem foldPotential_neg (μ x : ℝ) : foldPotential μ (-x) = -foldPotential μ x := by
  simp only [foldPotential]
  ring

theorem foldPotential_neg_sq_self (a : ℝ) :
    foldPotential (-a ^ 2) a = -(2 * a ^ 3 / 3) := by
  simp only [foldPotential]
  ring

theorem foldPotential_neg_sq_neg (a : ℝ) :
    foldPotential (-a ^ 2) (-a) = 2 * a ^ 3 / 3 := by
  rw [foldPotential_neg, foldPotential_neg_sq_self, neg_neg]

@[fun_prop]
theorem contDiff_foldPotential_uncurry {n : WithTop ℕ∞} :
    ContDiff ℝ n (Function.uncurry foldPotential) := by
  have heq : Function.uncurry foldPotential = fun p : ℝ × ℝ ↦ p.2 ^ 3 / 3 + p.1 * p.2 := rfl
  rw [heq]
  fun_prop

@[fun_prop]
theorem contDiff_foldPotential (μ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (foldPotential μ) := by
  unfold foldPotential
  fun_prop

@[fun_prop]
theorem continuous_foldPotential (μ : ℝ) : Continuous (foldPotential μ) :=
  (contDiff_foldPotential (n := 0) μ).continuous

@[fun_prop]
theorem differentiable_foldPotential (μ : ℝ) : Differentiable ℝ (foldPotential μ) :=
  (contDiff_foldPotential (n := 1) μ).differentiable one_ne_zero

/-- The first spatial derivative of `foldPotential μ` at `x` is `x² + μ`. -/
theorem hasDerivAt_foldPotential (μ x : ℝ) :
    HasDerivAt (foldPotential μ) (x ^ 2 + μ) x := by
  refine (((hasDerivAt_pow 3 x).div_const 3).add
    ((hasDerivAt_id' x).const_mul μ)).congr_deriv ?_
  push_cast
  ring

@[simp]
theorem deriv_foldPotential (μ : ℝ) :
    deriv (foldPotential μ) = fun x ↦ x ^ 2 + μ :=
  funext fun x ↦ (hasDerivAt_foldPotential μ x).deriv

@[simp]
theorem gradient_foldPotential (μ x : ℝ) :
    ∇ (foldPotential μ) x = x ^ 2 + μ := by
  rw [gradient_eq_deriv', deriv_foldPotential]

/-- **Parameter transversality of the fold family.** Differentiating `deriv (foldPotential ν) x`
with respect to the parameter `ν` gives `1 ≠ 0`. -/
theorem hasDerivAt_deriv_foldPotential_param (μ x : ℝ) :
    HasDerivAt (fun ν ↦ deriv (foldPotential ν) x) 1 μ := by
  simp only [deriv_foldPotential]
  simpa using (hasDerivAt_id' μ).const_add (x ^ 2)

theorem deriv_deriv_foldPotential_param (μ x : ℝ) :
    deriv (fun ν ↦ deriv (foldPotential ν) x) μ = 1 :=
  (hasDerivAt_deriv_foldPotential_param μ x).deriv

/-- The second spatial derivative of `foldPotential μ` at `x` is `2 x`. -/
theorem hasDerivAt_deriv_foldPotential (μ x : ℝ) :
    HasDerivAt (deriv (foldPotential μ)) (2 * x) x := by
  rw [deriv_foldPotential]
  simpa using (hasDerivAt_pow 2 x).add_const μ

@[simp]
theorem iteratedDeriv_two_foldPotential (μ x : ℝ) :
    iteratedDeriv 2 (foldPotential μ) x = 2 * x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_foldPotential μ x).deriv

/-- **Cubic `A₂` nondegeneracy in one dimension.** The third spatial derivative of
`foldPotential μ` is identically `2 ≠ 0`. -/
@[simp]
theorem iteratedDeriv_three_foldPotential (μ x : ℝ) :
    iteratedDeriv 3 (foldPotential μ) x = 2 := by
  have h3 : (3 : ℕ) = 2 + 1 := rfl
  rw [h3, iteratedDeriv_succ, funext (iteratedDeriv_two_foldPotential μ)]
  have hd : HasDerivAt (fun y : ℝ ↦ 2 * y) (2 * 1) x := (hasDerivAt_id' x).const_mul 2
  rw [mul_one] at hd
  exact hd.deriv

@[simp]
theorem hessianOperator_foldPotential (μ x : ℝ) :
    hessianOperator (foldPotential μ) x = (2 * x) • ContinuousLinearMap.id ℝ ℝ := by
  rw [hessianOperator_real, iteratedDeriv_two_foldPotential]

theorem hessianQuadraticForm_foldPotential_apply (μ x v : ℝ) :
    hessianQuadraticForm (foldPotential μ) x v = 2 * x * v ^ 2 := by
  rw [hessianQuadraticForm_real_apply, iteratedDeriv_two_foldPotential]

/-! ### Critical-point trichotomy in one dimension -/

private theorem fderiv_real_eq_zero_iff {f : ℝ → ℝ} {x : ℝ} :
    fderiv ℝ f x = 0 ↔ deriv f x = 0 := by
  rw [← toSpanSingleton_deriv]
  exact ⟨fun h ↦ by simpa using congrArg (· 1) h, fun h ↦ by simp [h]⟩

/-- For `μ > 0`, the derivative of `foldPotential μ` is strictly positive everywhere. -/
theorem deriv_foldPotential_pos {μ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    0 < deriv (foldPotential μ) x := by
  rw [deriv_foldPotential]
  dsimp only
  nlinarith [sq_nonneg x]

theorem deriv_foldPotential_ne_zero_of_pos {μ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    deriv (foldPotential μ) x ≠ 0 :=
  (deriv_foldPotential_pos hμ x).ne'

theorem fderiv_foldPotential_ne_zero_of_pos {μ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    fderiv ℝ (foldPotential μ) x ≠ 0 := by
  rw [Ne, fderiv_real_eq_zero_iff]
  exact deriv_foldPotential_ne_zero_of_pos hμ x

/-- At `μ = 0`, the origin is the unique critical point of `foldPotential 0`. -/
theorem deriv_foldPotential_zero_eq_zero_iff {x : ℝ} :
    deriv (foldPotential 0) x = 0 ↔ x = 0 := by
  rw [deriv_foldPotential]
  dsimp only
  rw [add_zero, sq_eq_zero_iff]

/-- At `μ = 0`, no point is a nondegenerate critical point of `foldPotential 0`. -/
theorem not_isNondegenerateCriticalPoint_foldPotential_zero (x : ℝ) :
    ¬ IsNondegenerateCriticalPoint (foldPotential 0) x := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_foldPotential 0).contDiffAt,
    deriv_foldPotential_zero_eq_zero_iff, iteratedDeriv_two_foldPotential]
  rintro ⟨rfl, h⟩
  exact h (mul_zero 2)

/-- For `μ = -a²`, the critical points of `foldPotential (-a²)` are `-a` and `a`. -/
theorem deriv_foldPotential_neg_sq_eq_zero_iff {a x : ℝ} :
    deriv (foldPotential (-a ^ 2)) x = 0 ↔ x = -a ∨ x = a := by
  rw [deriv_foldPotential]
  dsimp only
  have hfac : x ^ 2 + -a ^ 2 = (x + a) * (x - a) := by ring
  rw [hfac, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero]

theorem isNondegenerateCriticalPoint_foldPotential_neg_sq_neg {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPoint (foldPotential (-a ^ 2)) (-a) := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_foldPotential _).contDiffAt,
    deriv_foldPotential_neg_sq_eq_zero_iff, iteratedDeriv_two_foldPotential]
  exact ⟨.inl rfl, mul_ne_zero two_ne_zero (neg_ne_zero.2 ha)⟩

theorem isNondegenerateCriticalPoint_foldPotential_neg_sq_self {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPoint (foldPotential (-a ^ 2)) a := by
  rw [isNondegenerateCriticalPoint_real_iff (contDiff_foldPotential _).contDiffAt,
    deriv_foldPotential_neg_sq_eq_zero_iff, iteratedDeriv_two_foldPotential]
  exact ⟨.inr rfl, mul_ne_zero two_ne_zero ha⟩

@[simp]
theorem isNondegenerateCriticalPoint_foldPotential_neg_sq_iff {a x : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPoint (foldPotential (-a ^ 2)) x ↔ x = -a ∨ x = a := by
  refine ⟨fun h ↦ deriv_foldPotential_neg_sq_eq_zero_iff.1
    ((isNondegenerateCriticalPoint_real_iff (contDiff_foldPotential _).contDiffAt).1 h).1, ?_⟩
  rintro (rfl | rfl)
  · exact isNondegenerateCriticalPoint_foldPotential_neg_sq_neg ha
  · exact isNondegenerateCriticalPoint_foldPotential_neg_sq_self ha

@[simp]
theorem morseIndex_foldPotential_neg_sq_neg {a : ℝ} (ha : 0 < a) :
    morseIndex (foldPotential (-a ^ 2)) (-a) = 1 :=
  morseIndex_real_of_neg (by rw [iteratedDeriv_two_foldPotential]; linarith)

@[simp]
theorem morseIndex_foldPotential_neg_sq_self {a : ℝ} (ha : 0 < a) :
    morseIndex (foldPotential (-a ^ 2)) a = 0 :=
  morseIndex_real_of_pos (by rw [iteratedDeriv_two_foldPotential]; linarith)

/-- **Morse characterization of the 1D fold family.** `foldPotential μ` has nondegenerate critical
points on all of `ℝ` if and only if `μ ≠ 0`. -/
@[simp]
theorem hasNondegenerateCriticalPointsOn_foldPotential_iff {μ : ℝ} :
    HasNondegenerateCriticalPointsOn (foldPotential μ) univ ↔ μ ≠ 0 := by
  refine ⟨fun h h0 ↦ ?_, fun hμ ↦ hasNondegenerateCriticalPointsOn_iff.2 fun x _ hx ↦ ?_⟩
  · subst h0
    refine not_isNondegenerateCriticalPoint_foldPotential_zero 0
      (hasNondegenerateCriticalPointsOn_iff.1 h (mem_univ 0) ?_)
    rw [fderiv_real_eq_zero_iff, deriv_foldPotential_zero_eq_zero_iff]
  · rcases lt_trichotomy μ 0 with hneg | rfl | hpos
    · have ha : √(-μ) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 hneg)).ne'
      have hμeq : μ = -(√(-μ)) ^ 2 := by rw [Real.sq_sqrt (neg_nonneg.2 hneg.le), neg_neg]
      rw [hμeq] at hx ⊢
      exact (isNondegenerateCriticalPoint_foldPotential_neg_sq_iff ha).2
        (deriv_foldPotential_neg_sq_eq_zero_iff.1 (fderiv_real_eq_zero_iff.1 hx))
    · exact absurd rfl hμ
    · exact absurd hx (fderiv_foldPotential_ne_zero_of_pos hpos x)

/-! ### Global ODE uniqueness, symmetry, and the regimes `μ > 0` and `μ = 0` -/

/-- The negative gradient field `x ↦ -x² - μ` of `foldPotential μ` is `2 R`-Lipschitz on `[-R, R]`
(`R ≥ 0`). -/
theorem lipschitzOnWith_neg_gradient_foldPotential (μ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith (2 * ‖R‖₊) (fun x ↦ -∇ (foldPotential μ) x) (Icc (-R) R) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [mem_Icc] at hx hy
  have hsum : |x + y| ≤ 2 * R := abs_le.2 ⟨by linarith, by linarith⟩
  simp only [gradient_foldPotential, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul,
    NNReal.coe_ofNat, coe_nnnorm, Real.norm_of_nonneg hR]
  have hdiff : -(x ^ 2 + μ) - -(y ^ 2 + μ) = -(x + y) * (x - y) := by ring
  rw [hdiff, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

/-- **Global uniqueness for negative-gradient trajectories of `foldPotential μ`.** Two global
trajectories of `x' = -x² - μ` that agree at one time `t₀` coincide everywhere on `ℝ`. -/
theorem eq_of_isIntegralCurve_foldPotential {μ : ℝ} {γ₁ γ₂ : ℝ → ℝ}
    (h₁ : IsIntegralCurve γ₁ (fun _ x ↦ -∇ (foldPotential μ) x))
    (h₂ : IsIntegralCurve γ₂ (fun _ x ↦ -∇ (foldPotential μ) x))
    {t₀ : ℝ} (heq : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  funext t
  let A := min t t₀ - 1
  let B := max t t₀ + 1
  have ht : t ∈ Ioo A B := ⟨by grind, by grind⟩
  have ht₀ : t₀ ∈ Ioo A B := ⟨by grind, by grind⟩
  have hcont : Continuous fun u ↦ max |γ₁ u| |γ₂ u| :=
    h₁.continuous.abs.max h₂.continuous.abs
  obtain ⟨u₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t₀, Ioo_subset_Icc_self ht₀⟩
    hcont.continuousOn
  let R := max |γ₁ u₀| |γ₂ u₀|
  have hR : 0 ≤ R := le_max_of_le_left (abs_nonneg _)
  have hmem₁ : ∀ u ∈ Ioo A B, γ₁ u ∈ Icc (-R) R := fun u hu ↦
    abs_le.1 ((le_max_left _ _).trans (hmax (Ioo_subset_Icc_self hu)))
  have hmem₂ : ∀ u ∈ Ioo A B, γ₂ u ∈ Icc (-R) R := fun u hu ↦
    abs_le.1 ((le_max_right _ _).trans (hmax (Ioo_subset_Icc_self hu)))
  exact ODE_solution_unique_of_mem_Ioo
    (fun _ _ ↦ lipschitzOnWith_neg_gradient_foldPotential μ hR) ht₀
    (fun u hu ↦ ⟨h₁ u, hmem₁ u hu⟩) (fun u hu ↦ ⟨h₂ u, hmem₂ u hu⟩) heq ht

/-- **Time-reversal symmetry of the fold ODE.** Since `foldPotential μ` is odd, `s ↦ -γ (-s)` is a
negative-gradient trajectory whenever `γ` is. -/
theorem isIntegralCurve_neg_comp_neg_foldPotential {μ : ℝ} {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential μ) x)) :
    IsIntegralCurve (fun s ↦ -γ (-s)) (fun _ x ↦ -∇ (foldPotential μ) x) := fun s ↦ by
  have hd := ((hγ (-s)).comp s (hasDerivAt_id' s).neg).neg
  refine hd.congr_deriv ?_
  simp only [gradient_foldPotential]
  ring

private theorem tendsto_const_sub_mul_atTop_atBot (A : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t ↦ A - c * t) atTop atBot :=
  tendsto_atBot.2 fun B ↦ eventually_atTop.2
    ⟨(A - B) / c, fun _ ht ↦ by linarith [(div_le_iff₀ hc).1 ht]⟩

/-- **For `μ > 0`, every global trajectory diverges to `-∞` at `+∞`.** -/
theorem tendsto_atTop_atBot_of_isIntegralCurve_foldPotential_of_pos {μ : ℝ} (hμ : 0 < μ)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential μ) x)) :
    Tendsto γ atTop atBot := by
  have hd : ∀ s, HasDerivAt (fun t ↦ γ t + μ * t) (-(γ s ^ 2)) s := fun s ↦ by
    have h₁ : HasDerivAt γ (-∇ (foldPotential μ) (γ s)) s := hγ s
    rw [gradient_foldPotential] at h₁
    exact (h₁.add ((hasDerivAt_id' s).const_mul μ)).congr_deriv (by ring)
  have hant : Antitone (fun s ↦ γ s + μ * s) :=
    antitone_of_hasDerivAt_nonpos hd fun s ↦ neg_nonpos.2 (sq_nonneg _)
  refine tendsto_atBot_mono' atTop ?_ (tendsto_const_sub_mul_atTop_atBot (γ 0) hμ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := hant ht
  dsimp only at h
  linarith

/-- **For `μ > 0`, every global trajectory diverges to `+∞` at `-∞`.** -/
theorem tendsto_atBot_atTop_of_isIntegralCurve_foldPotential_of_pos {μ : ℝ} (hμ : 0 < μ)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential μ) x)) :
    Tendsto γ atBot atTop := by
  have h := tendsto_neg_atBot_atTop.comp
    ((tendsto_atTop_atBot_of_isIntegralCurve_foldPotential_of_pos hμ
      (isIntegralCurve_neg_comp_neg_foldPotential hγ)).comp tendsto_neg_atBot_atTop)
  simpa [Function.comp_def] using h

/-- For `μ > 0`, no global negative-gradient trajectory of `foldPotential μ` converges at `+∞`. -/
theorem not_tendsto_atTop_nhds_of_isIntegralCurve_foldPotential_of_pos {μ : ℝ} (hμ : 0 < μ)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential μ) x)) (q : ℝ) :
    ¬ Tendsto γ atTop (𝓝 q) := by
  intro hq
  have hbot := tendsto_atTop_atBot_of_isIntegralCurve_foldPotential_of_pos hμ hγ
  obtain ⟨s, hs1, hs2⟩ := ((hq.eventually (Ioi_mem_nhds (sub_one_lt q))).and
    (hbot.eventually (eventually_le_atBot (q - 2)))).exists
  linarith

/-- For `μ > 0`, no global negative-gradient trajectory of `foldPotential μ` converges at `-∞`. -/
theorem not_tendsto_atBot_nhds_of_isIntegralCurve_foldPotential_of_pos {μ : ℝ} (hμ : 0 < μ)
    {γ : ℝ → ℝ} (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential μ) x)) (p : ℝ) :
    ¬ Tendsto γ atBot (𝓝 p) := by
  intro hp
  refine not_tendsto_atTop_nhds_of_isIntegralCurve_foldPotential_of_pos hμ
    (isIntegralCurve_neg_comp_neg_foldPotential hγ) (-p) ?_
  simpa [Function.comp_def] using (hp.comp tendsto_neg_atTop_atBot).neg

private theorem eq_zero_of_tendsto_atTop_foldPotential_zero {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential 0) x)) {q : ℝ}
    (htop : Tendsto γ atTop (𝓝 q)) : q = 0 := by
  by_contra hq
  have hqpos : 0 < |q| / 2 := half_pos (abs_pos.2 hq)
  set c := (|q| / 2) ^ 2
  have hc : 0 < c := sq_pos_of_pos hqpos
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (htop.abs.eventually (Ioi_mem_nhds (half_lt_self (abs_pos.2 hq))))
  have hd : ∀ s ∈ Ici S, HasDerivAt (fun t ↦ γ t + c * t) (-(γ s ^ 2) + c) s := fun s _ ↦ by
    have h₁ : HasDerivAt γ (-∇ (foldPotential 0) (γ s)) s := hγ s
    rw [gradient_foldPotential, add_zero] at h₁
    exact (h₁.add ((hasDerivAt_id' s).const_mul c)).congr_deriv (by ring)
  have hant : AntitoneOn (fun t ↦ γ t + c * t) (Ici S) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici S)
      (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hd s (interior_subset hs)).hasDerivWithinAt) fun s hs ↦ ?_
    have hlt : |q| / 2 < |γ s| := hS s (interior_subset hs)
    have hsq : c ≤ γ s ^ 2 := by
      rw [← sq_abs (γ s)]
      exact pow_le_pow_left₀ hqpos.le hlt.le 2
    linarith
  have hbot : Tendsto γ atTop atBot := by
    refine tendsto_atBot_mono' atTop ?_ (tendsto_const_sub_mul_atTop_atBot (γ S + c * S) hc)
    filter_upwards [eventually_ge_atTop S] with s hs
    have h := hant self_mem_Ici hs hs
    dsimp only at h
    linarith
  obtain ⟨s, hs1, hs2⟩ := ((htop.eventually (Ioi_mem_nhds (sub_one_lt q))).and
    (hbot.eventually (eventually_le_atBot (q - 2)))).exists
  linarith

/-- **At the birth-death instant `μ = 0`, the constant zero trajectory is the unique global
connecting trajectory.** Any global negative-gradient trajectory of `foldPotential 0` with finite
limits `p` and `q` at `-∞` and `+∞` satisfies `p = q = 0` and `γ = 0`. -/
theorem eq_zero_of_isIntegralCurve_foldPotential_zero {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential 0) x)) {p q : ℝ}
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) :
    p = 0 ∧ q = 0 ∧ γ = 0 := by
  have hp : p = 0 := neg_eq_zero.1 <| eq_zero_of_tendsto_atTop_foldPotential_zero
    (isIntegralCurve_neg_comp_neg_foldPotential hγ)
    (by simpa [Function.comp_def] using (hbot.comp tendsto_neg_atTop_atBot).neg)
  have hq : q = 0 := eq_zero_of_tendsto_atTop_foldPotential_zero hγ htop
  refine ⟨hp, hq, funext fun s ↦ ?_⟩
  subst hp hq
  have hant : Antitone (foldPotential 0 ∘ γ) :=
    hγ.antitone_comp_neg_gradient fun t ↦ differentiable_foldPotential 0 (γ t)
  have hfbot : Tendsto (foldPotential 0 ∘ γ) atBot (𝓝 0) := by
    simpa using ((continuous_foldPotential 0).tendsto 0).comp hbot
  have hftop : Tendsto (foldPotential 0 ∘ γ) atTop (𝓝 0) := by
    simpa using ((continuous_foldPotential 0).tendsto 0).comp htop
  have hle : foldPotential 0 (γ s) ≤ 0 :=
    ge_of_tendsto hfbot (eventually_le_atBot s |>.mono fun t ht ↦ hant ht)
  have hge : 0 ≤ foldPotential 0 (γ s) :=
    le_of_tendsto hftop (eventually_ge_atTop s |>.mono fun t ht ↦ hant ht)
  have hval : (γ s) ^ 3 / 3 = 0 := by
    simpa [foldPotential_apply] using le_antisymm hle hge
  exact eq_zero_of_pow_eq_zero (n := 3) (by linarith)

/-! ### The connecting orbit, time coordinate, and Möbius flow for `μ = -a²` -/

/-- The reference connecting trajectory `q_a(s) = a * tanh (a * s)` of `foldPotential (-a²)`. For
`a > 0` it runs from `-a` at `-∞` to `a` at `+∞`, passing through `0` at time `0`. -/
noncomputable def foldOrbit (a s : ℝ) : ℝ :=
  a * Real.tanh (a * s)

theorem foldOrbit_apply (a s : ℝ) : foldOrbit a s = a * Real.tanh (a * s) :=
  (rfl)

@[simp]
theorem foldOrbit_zero_left (s : ℝ) : foldOrbit 0 s = 0 := by
  simp [foldOrbit]

@[simp]
theorem foldOrbit_zero_right (a : ℝ) : foldOrbit a 0 = 0 := by
  simp [foldOrbit]

@[simp]
theorem foldOrbit_neg_left (a s : ℝ) : foldOrbit (-a) s = foldOrbit a s := by
  simp [foldOrbit, Real.tanh_neg]

@[simp]
theorem foldOrbit_neg_right (a s : ℝ) : foldOrbit a (-s) = -foldOrbit a s := by
  simp [foldOrbit, Real.tanh_neg]

@[fun_prop]
theorem contDiff_foldOrbit (a : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (foldOrbit a) := by
  unfold foldOrbit
  exact contDiff_const.mul (Real.contDiff_tanh.comp (contDiff_const.mul contDiff_id))

@[fun_prop]
theorem continuous_foldOrbit (a : ℝ) : Continuous (foldOrbit a) :=
  (contDiff_foldOrbit (n := 0) a).continuous

theorem foldOrbit_mem_Ioo {a : ℝ} (ha : 0 < a) (s : ℝ) :
    foldOrbit a s ∈ Ioo (-a) a := by
  rw [foldOrbit_apply, mem_Ioo]
  have h1 := mul_lt_mul_of_pos_left (Real.neg_one_lt_tanh (a * s)) ha
  have h2 := mul_lt_mul_of_pos_left (Real.tanh_lt_one (a * s)) ha
  exact ⟨by linarith, by linarith⟩

theorem foldOrbit_mem_Icc {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    foldOrbit a s ∈ Icc (-a) a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  · exact Ioo_subset_Icc_self (foldOrbit_mem_Ioo ha' s)

theorem strictMono_foldOrbit {a : ℝ} (ha : 0 < a) : StrictMono (foldOrbit a) :=
  fun _ _ hst ↦ mul_lt_mul_of_pos_left (Real.tanh_strictMono (mul_lt_mul_of_pos_left hst ha)) ha

/-- **The curve `foldOrbit a` solves the negative-gradient equation of `foldPotential (-a²)`.** -/
theorem hasDerivAt_foldOrbit (a s : ℝ) :
    HasDerivAt (foldOrbit a) (-∇ (foldPotential (-a ^ 2)) (foldOrbit a s)) s := by
  have hd : HasDerivAt (foldOrbit a) (a * (1 / Real.cosh (a * s) ^ 2 * (a * 1))) s :=
    ((Real.hasDerivAt_tanh (a * s)).comp s ((hasDerivAt_id' s).const_mul a)).const_mul a
  refine hd.congr_deriv ?_
  rw [gradient_foldPotential, foldOrbit_apply, mul_one, ← Real.one_sub_tanh_sq]
  ring

theorem isIntegralCurve_foldOrbit (a : ℝ) :
    IsIntegralCurve (foldOrbit a) (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x) :=
  hasDerivAt_foldOrbit a

theorem tendsto_foldOrbit_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (foldOrbit a) atBot (𝓝 (-a)) := by
  have h : Tendsto (foldOrbit a) atBot (𝓝 (a * -1)) :=
    (tendsto_const_nhds (x := a)).mul
      (Real.tendsto_tanh_atBot.comp (tendsto_id.const_mul_atBot ha))
  rw [mul_neg_one] at h
  exact h

theorem tendsto_foldOrbit_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (foldOrbit a) atTop (𝓝 a) := by
  have h : Tendsto (foldOrbit a) atTop (𝓝 (a * 1)) :=
    (tendsto_const_nhds (x := a)).mul
      (Real.tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop ha))
  rw [mul_one] at h
  exact h

/-- The time coordinate `U_a(x) = a⁻¹ * artanh (x / a)` on `(-a, a)`, inverse to `foldOrbit a` for
`a > 0`. -/
noncomputable def foldTimeCoordinate (a x : ℝ) : ℝ :=
  a⁻¹ * Real.artanh (x / a)

theorem foldTimeCoordinate_apply (a x : ℝ) :
    foldTimeCoordinate a x = a⁻¹ * Real.artanh (x / a) :=
  (rfl)

@[simp]
theorem foldTimeCoordinate_zero_right (a : ℝ) : foldTimeCoordinate a 0 = 0 := by
  simp [foldTimeCoordinate]

@[simp]
theorem foldTimeCoordinate_neg_right (a x : ℝ) :
    foldTimeCoordinate a (-x) = -foldTimeCoordinate a x := by
  simp [foldTimeCoordinate, neg_div, Real.artanh_neg_eq_neg_artanh]

@[simp]
theorem foldTimeCoordinate_foldOrbit {a : ℝ} (ha : a ≠ 0) (s : ℝ) :
    foldTimeCoordinate a (foldOrbit a s) = s := by
  rw [foldTimeCoordinate_apply, foldOrbit_apply, mul_div_cancel_left₀ _ ha, Real.artanh_tanh,
    inv_mul_cancel_left₀ ha]

@[simp]
theorem foldOrbit_foldTimeCoordinate {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (-a) a) :
    foldOrbit a (foldTimeCoordinate a x) = x := by
  have hx' : x / a ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hx.1]), (div_lt_iff₀ ha).2 (by linarith [hx.2])⟩
  rw [foldOrbit_apply, foldTimeCoordinate_apply, mul_inv_cancel_left₀ ha.ne', Real.tanh_artanh hx',
    mul_div_cancel₀ _ ha.ne']

theorem bijOn_foldTimeCoordinate {a : ℝ} (ha : 0 < a) :
    BijOn (foldTimeCoordinate a) (Ioo (-a) a) univ := by
  refine ⟨mapsTo_univ _ _, ?_, fun s _ ↦ ⟨foldOrbit a s, foldOrbit_mem_Ioo ha s,
    foldTimeCoordinate_foldOrbit ha.ne' s⟩⟩
  intro x hx y hy hxy
  rw [← foldOrbit_foldTimeCoordinate ha hx, ← foldOrbit_foldTimeCoordinate ha hy, hxy]

theorem strictMonoOn_foldTimeCoordinate {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (foldTimeCoordinate a) (Ioo (-a) a) := by
  intro x hx y hy hxy
  have hx' : x / a ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hx.1]), (div_lt_iff₀ ha).2 (by linarith [hx.2])⟩
  have hy' : y / a ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hy.1]), (div_lt_iff₀ ha).2 (by linarith [hy.2])⟩
  exact mul_lt_mul_of_pos_left
    (Real.strictMonoOn_artanh hx' hy' ((div_lt_div_iff_of_pos_right ha).2 hxy)) (inv_pos.2 ha)

/-- On `(-a, a)` (`a > 0`), `foldTimeCoordinate a` has derivative `(a² - x²)⁻¹`, reciprocal to the
negative-gradient speed `a² - x²`. -/
theorem hasDerivAt_foldTimeCoordinate {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (foldTimeCoordinate a) ((a ^ 2 - x ^ 2)⁻¹) x := by
  have hx' : x / a ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(lt_div_iff₀ ha).2 (by linarith [hx.1]), (div_lt_iff₀ ha).2 (by linarith [hx.2])⟩
  have hd := (((hasDerivAt_id' x).div_const a).artanh hx').const_mul a⁻¹
  refine hd.congr_deriv ?_
  have ha0 : a ≠ 0 := ha.ne'
  have hsub : a ^ 2 - x ^ 2 ≠ 0 := sub_ne_zero.2 (by nlinarith [hx.1, hx.2])
  have h1 : 1 - (x / a) ^ 2 = (a ^ 2 - x ^ 2) / a ^ 2 := by field_simp
  rw [h1]
  field_simp

/-! ### Classification of connecting trajectories for `μ = -a²` -/

private theorem lt_of_isIntegralCurve_foldPotential {a : ℝ} (ha : 0 < a) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (s : ℝ) : γ s < a := by
  by_contra! hge
  rcases hge.eq_or_lt with heq | hgt
  · have hconst : γ = fun _ ↦ a :=
      eq_of_isIntegralCurve_foldPotential hγ
        (isIntegralCurve_const_neg_gradient_iff.2 (by simp [gradient_foldPotential]))
        (t₀ := s) heq.symm
    rw [hconst] at hbot
    have h := tendsto_nhds_unique tendsto_const_nhds hbot
    linarith
  · obtain ⟨t, hts, hta⟩ := ((eventually_le_atBot s).and
      (hbot.eventually (Iio_mem_nhds (by linarith : -a < a)))).exists
    obtain ⟨r, -, hval⟩ := intermediate_value_Icc hts hγ.continuous.continuousOn
      ⟨le_of_lt hta, hgt.le⟩
    have hconst : γ = fun _ ↦ a :=
      eq_of_isIntegralCurve_foldPotential hγ
        (isIntegralCurve_const_neg_gradient_iff.2 (by simp [gradient_foldPotential])) (t₀ := r) hval
    have := congrFun hconst s
    linarith

/-- Any global negative-gradient trajectory of `foldPotential (-a²)` (`a > 0`) running from `-a` at
`-∞` to `a` at `+∞` stays strictly inside `(-a, a)`. -/
theorem mem_Ioo_of_isIntegralCurve_foldPotential {a : ℝ} (ha : 0 < a) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a)) (s : ℝ) :
    γ s ∈ Ioo (-a) a := by
  refine ⟨?_, lt_of_isIntegralCurve_foldPotential ha hγ hbot s⟩
  have hrev := lt_of_isIntegralCurve_foldPotential ha
    (isIntegralCurve_neg_comp_neg_foldPotential hγ)
    (by simpa [Function.comp_def] using (htop.comp tendsto_neg_atBot_atTop).neg) (-s)
  simp only [neg_neg] at hrev
  linarith

/-- Every time translate `s ↦ foldOrbit a (s + s₀)` is a negative-gradient trajectory of
`foldPotential (-a²)`. -/
theorem isIntegralCurve_foldOrbit_add (a s₀ : ℝ) :
    IsIntegralCurve (fun s ↦ foldOrbit a (s + s₀))
      (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x) := fun s ↦ by
  have hd : HasDerivAt (foldOrbit a ∘ fun t ↦ t + s₀)
      (-∇ (foldPotential (-a ^ 2)) (foldOrbit a (s + s₀)) * 1) s :=
    HasDerivAt.comp s (hasDerivAt_foldOrbit a (s + s₀)) ((hasDerivAt_id' s).add_const s₀)
  exact hd.congr_deriv (mul_one _)

/-- **Classification of the newborn connecting orbit in one dimension.** For `a > 0`, every
negative-gradient trajectory of `foldPotential (-a²)` from `-a` at `-∞` to `a` at `+∞` is a unique
time translate `s ↦ foldOrbit a (s + s₀)` (with `s₀ = foldTimeCoordinate a (γ 0)`). -/
theorem existsUnique_foldOrbit_add_of_isIntegralCurve {a : ℝ} (ha : 0 < a) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a)) :
    ∃! s₀ : ℝ, γ = fun s ↦ foldOrbit a (s + s₀) := by
  have h0 : γ 0 ∈ Ioo (-a) a := mem_Ioo_of_isIntegralCurve_foldPotential ha hγ hbot htop 0
  refine ⟨foldTimeCoordinate a (γ 0), ?_, fun s₀ hs₀ ↦ ?_⟩
  · refine eq_of_isIntegralCurve_foldPotential hγ
      (isIntegralCurve_foldOrbit_add a (foldTimeCoordinate a (γ 0))) (t₀ := 0) ?_
    rw [zero_add, foldOrbit_foldTimeCoordinate ha h0]
  · have hval := congrArg (foldTimeCoordinate a) (congrFun hs₀ 0)
    simpa [foldTimeCoordinate_foldOrbit ha.ne'] using hval.symm

/-- **No reverse connecting trajectory exists.** For `a > 0`, no negative-gradient trajectory of
`foldPotential (-a²)` runs from `a` at `-∞` to `-a` at `+∞`. -/
theorem not_isIntegralCurve_foldPotential_self_to_neg {a : ℝ} (ha : 0 < a) {γ : ℝ → ℝ}
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 a)) (htop : Tendsto γ atTop (𝓝 (-a))) : False := by
  have hant : Antitone (foldPotential (-a ^ 2) ∘ γ) :=
    hγ.antitone_comp_neg_gradient fun t ↦ differentiable_foldPotential (-a ^ 2) (γ t)
  have hfbot : Tendsto (foldPotential (-a ^ 2) ∘ γ) atBot
      (𝓝 (foldPotential (-a ^ 2) a)) :=
    ((continuous_foldPotential (-a ^ 2)).tendsto a).comp hbot
  have hftop : Tendsto (foldPotential (-a ^ 2) ∘ γ) atTop
      (𝓝 (foldPotential (-a ^ 2) (-a))) :=
    ((continuous_foldPotential (-a ^ 2)).tendsto (-a)).comp htop
  have hle0 : foldPotential (-a ^ 2) (γ 0) ≤ foldPotential (-a ^ 2) a :=
    ge_of_tendsto hfbot (eventually_le_atBot 0 |>.mono fun t ht ↦ hant ht)
  have hge0 : foldPotential (-a ^ 2) (-a) ≤ foldPotential (-a ^ 2) (γ 0) :=
    le_of_tendsto hftop (eventually_ge_atTop 0 |>.mono fun t ht ↦ hant ht)
  have hineq : foldPotential (-a ^ 2) (-a) ≤ foldPotential (-a ^ 2) a := hge0.trans hle0
  rw [foldPotential_neg_sq_neg, foldPotential_neg_sq_self] at hineq
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  linarith

/-! ### Fredholm regularity of the linearized trajectory operators in one dimension -/

section Operator1D

open TauCeti.WeakDerivStep

variable {a : ℝ} {γ : ℝ → ℝ}
  {AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- Along a negative-gradient trajectory of `foldPotential (-a²)` (`a ≠ 0`) from `-a` to `a`, the
linearized operator `ξ ↦ ξ' + 2 γ ξ` from `W^{1,2}(ℝ, ℝ)` to `L²(ℝ, ℝ)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_foldPotential (ha : a ≠ 0)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s)) :
    (trajectoryOperator (p := 2) AL).IsFredholm :=
  hγ.isFredholm_trajectoryOperator_hessianOperator (contDiff_foldPotential _)
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_neg ha)
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_self ha) hbot htop hAL

/-- **The linearized fold trajectory operator has index `1`.** -/
theorem index_trajectoryOperator_foldPotential (ha : 0 < a)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s)) :
    (trajectoryOperator (p := 2) AL).index = 1 := by
  rw [hγ.index_trajectoryOperator_hessianOperator (contDiff_foldPotential _)
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_neg ha.ne')
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_self ha.ne') hbot htop hAL,
    morseIndex_foldPotential_neg_sq_neg ha, morseIndex_foldPotential_neg_sq_self ha]
  simp

/-- **The kernel of the linearized fold trajectory operator is spanned by `γ'`.** -/
theorem exists_ker_trajectoryOperator_foldPotential_eq_span (ha : a ≠ 0)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] deriv γ ∧
        (trajectoryOperator (p := 2) AL).ker = ℝ ∙ u :=
  hγ.exists_ker_trajectoryOperator_hessianOperator_eq_span (Module.finrank_self ℝ)
    (contDiff_foldPotential _) hbot htop (fun h ↦ ha (by linarith)) hAL

/-- **Transversality of the newborn fold connecting trajectory.** -/
theorem surjective_trajectoryOperator_foldPotential (ha : 0 < a)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s)) :
    Function.Surjective (trajectoryOperator (p := 2) AL) :=
  (hγ.surjective_trajectoryOperator_hessianOperator_iff (Module.finrank_self ℝ)
    (contDiff_foldPotential _)
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_neg ha.ne')
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_self ha.ne') hbot htop
    (by linarith) hAL).2
    (by rw [morseIndex_foldPotential_neg_sq_neg ha, morseIndex_foldPotential_neg_sq_self ha])

/-- **Injectivity of the formal adjoint in one dimension.** -/
theorem ker_trajectoryOperator_neg_foldPotential_eq_bot (ha : 0 < a)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s)) :
    (trajectoryOperator (p := 2) (-AL)).ker = ⊥ := by
  have hadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
    filter_upwards [hAL] with s hs
    rw [hs]
    exact (contDiff_foldPotential _).contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
      |>.clm_adjoint_eq.symm
  exact (surjective_trajectoryOperator_iff_ker_neg_eq_bot hadj
    (isFredholm_trajectoryOperator_foldPotential ha.ne' hγ hbot htop hAL).isClosed_range).1
    (surjective_trajectoryOperator_foldPotential ha hγ hbot htop hAL)

/-- Along any negative-gradient trajectory of `foldPotential (-a²)` (`a > 0`) from `-a` to `a`, the
adjoint ODE `v' - 2 γ v = 0` has no nonzero square-integrable solution. -/
theorem squareIntegrableSolutions_neg_hessianOperator_foldPotential_eq_bot (ha : 0 < a)
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ (foldPotential (-a ^ 2)) x))
    (hbot : Tendsto γ atBot (𝓝 (-a))) (htop : Tendsto γ atTop (𝓝 a)) :
    squareIntegrableSolutions
      (fun s ↦ -hessianOperator (foldPotential (-a ^ 2)) (γ s)) = ⊥ := by
  have hmem : MemLp (fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s)) ∞
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    (contDiff_foldPotential _).memLp_top_hessianOperator_comp hγ.continuous hbot htop _
  set AL := hmem.toLp _
  have hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hessianOperator (foldPotential (-a ^ 2)) (γ s) := hmem.coeFn_toLp
  have hnegAL : (-AL : Lp (ℝ →L[ℝ] ℝ) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ -hessianOperator (foldPotential (-a ^ 2)) (γ s) := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with s hs1 hs2
    rw [hs1, Pi.neg_apply, hs2]
  have hcont : Continuous fun s ↦ -hessianOperator (foldPotential (-a ^ 2)) (γ s) :=
    (((contDiff_foldPotential (n := 2) _).contDiff_hessianOperator (m := 0)
      (by norm_num)).continuous.comp hγ.continuous).neg
  exact (ker_trajectoryOperator_eq_bot_iff hcont (-AL) hnegAL).1
    (ker_trajectoryOperator_neg_foldPotential_eq_bot ha hγ hbot htop hAL)

/-- At the constant trajectory `-a` (`a ≠ 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_foldPotential_neg (ha : a ≠ 0)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (foldPotential (-a ^ 2)) (-a)) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_neg ha) hAL

/-- At the constant trajectory `a` (`a ≠ 0`), the linearized operator is bijective. -/
theorem bijective_trajectoryOperator_foldPotential_self (ha : a ≠ 0)
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun _ ↦ hessianOperator (foldPotential (-a ^ 2)) a) :
    Function.Bijective (trajectoryOperator (p := 2) AL) :=
  IsNondegenerateCriticalPoint.bijective_trajectoryOperator_hessianOperator
    (isNondegenerateCriticalPoint_foldPotential_neg_sq_self ha) hAL

end Operator1D

end TauCeti

end
