/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness
import TauCeti.Analysis.Sobolev.W1p.Truncation

/-!
# Convex functions of supersolutions and the lower bound for positive supersolutions

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak supersolution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`. If `u ≥ m` almost everywhere and `F` is
convex and nonincreasing on `[m, ∞)`, then `F(u)` is a weak **sub**solution:
`a(F(u), v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. The weak gradient of `F(u)` is
`F'(u) ∇u`, and the formal computation is

`a(F(u), v) = ∫ F'(u) ⟨a ∇u, ∇v⟩ = -a(u, -F'(u) v) - ∫ F''(u) v ⟨a ∇u, ∇u⟩ ≤ 0`,

using `-F'(u) v ≥ 0` as a test function for the supersolution `u`, and `F'' ≥ 0`. This is only
formal because `-F'(u) v` need not lie in `H¹₀(Ω)` for a general `v`; the proof carries it out
for `v` a test function and extends the inequality by density (see the implementation notes).

The main application is to the reciprocal `t ↦ 1/t` of a supersolution bounded below by a
positive constant. The reciprocal itself is not `C²` and does not vanish at `0`, so it is
approached by the functions `t ↦ t / (t² + c²)`: these are convex and nonincreasing on
`[2c, ∞)`, so each `u / (u² + c²)` is a subsolution once `2c ≤ m`, and De Giorgi's local
boundedness theorem for subsolutions bounds them from above, uniformly in `c`. Letting `c → 0`
bounds `u⁻¹`. This is the lower bound for positive supersolutions in Moser's proof of the
Harnack inequality: in dimension `n ≥ 3`, on every ball `B(x₀, R) ⊆ Ω`,

`u⁻¹ ≤ D R^{-n/2} ‖u⁻¹‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

with `D` depending only on `λ`, `Λ`, the dimension and the normalization of the additive Haar
measure, and in particular not on the lower bound `m`. Together with the local boundedness of
subsolutions in terms of small powers and the logarithmic estimate for supersolutions, this lower
bound is an ingredient of Moser's weak Harnack inequality.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.energyFormH1_contDiffComp_nonpos`: a convex nonincreasing
  function of a supersolution is a subsolution.
* `TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_sqrt_setIntegral`: the lower bound
  `u⁻¹ ≤ D R^{-1/α} ‖u⁻¹‖_{L²(B(x₀, R))}` for positive supersolutions, under a Sobolev inequality
  with exponent `q > 2` and `α = 1 - 2/q`.
* `TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv`: the
  scale-invariant lower bound `u⁻¹ ≤ D R^{-n/2} ‖u⁻¹‖_{L²(B(x₀, R))}` in dimension `n ≥ 3`.

## Implementation notes

The test function `-F'(u) v` is a product of two Sobolev functions, which need not lie in
`H¹₀(Ω)` for a general `v`. It is first formed for a test function `φ ∈ C_c^∞(Ω)` as the positive
part of `-φ F'(u)`, and the inequality `a(F(u), φ⁺) ≤ 0` obtained for it passes to every
`v ∈ H¹₀(Ω)` in the form `a(F(u), v⁺) ≤ 0`, by density of the test functions and continuity of
`v ↦ v⁺` on `H¹(Ω)`.

The reciprocal is approached through the smooth functions `t ↦ t / (t² + c²)`, which vanish at
`0`, have bounded first and second derivatives, are convex and decreasing on `[√3 c, ∞)`, and
increase to `1/t` as `c → 0`.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  14 (1961).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-! ### Convex nonincreasing functions of supersolutions -/

omit [DecidableEq ι] in
/-- The pointwise form of `a(F(u), φ⁺) ≤ -a(u, (-φ F'(u))⁺)`. At a point where `φ = z`,
`F'(u) = d₁ ≤ 0`, `F''(u) = d₂ ≥ 0`, `∇u = g` and `∇φ = q`, the gradient of `φ⁺` is `q` or `0`,
and that of `(-φ F'(u))⁺` is `-z d₂ g - d₁ q` or `0`, according to the sign of `φ`, respectively
of `-φ F'(u)`. -/
private theorem matrixBilinearForm_ite_smul_le {A : Matrix ι ι ℝ}
    (hA : ∀ ξ, 0 ≤ matrixBilinearForm A ξ ξ) {z d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 ≤ d₂)
    (g q : EuclideanSpace ℝ ι) :
    matrixBilinearForm A (if 0 < z then q else 0) (d₁ • g) ≤
      -matrixBilinearForm A (if 0 < -(z * d₁) then -(z * d₂) • g - d₁ • q else 0) g := by
  by_cases hz : 0 < z
  · by_cases hT : 0 < -(z * d₁)
    · rw [ite_eq_left hz, ite_eq_left hT]
      simp only [map_smul, map_sub, _root_.sub_apply, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul]
      nlinarith [mul_nonneg (mul_nonneg hz.le hd₂) (hA g)]
    · have hd : d₁ = 0 := by nlinarith
      rw [ite_eq_left hz, ite_eq_right hT, hd]
      simp
  · have hT : ¬ 0 < -(z * d₁) := by nlinarith
    rw [ite_eq_right hz, ite_eq_right hT]
    simp

/-- The test-function case of `TauCeti.PDE.UniformlyEllipticOn.energyFormH1_contDiffComp_nonpos`:
`a(F(u), φ⁺) ≤ 0` for every `φ ∈ C_c^∞(Ω)`. The supersolution inequality is tested against
`T = (-φ F'(u))⁺`, and the energy densities of `a(F(u), φ⁺)` and `-a(u, T)` are compared
pointwise. -/
private theorem energyFormH1_contDiffComp_posPart_ofTestFunction_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {M M' : ℝ≥0} (hM : ∀ t, ‖deriv F t‖₊ ≤ M)
    (hM' : ∀ t, ‖deriv (deriv F) t‖₊ ≤ M') (hF0 : F 0 = 0) {m : ℝ}
    (hum : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    (hF' : ∀ t, m ≤ t → deriv F t ≤ 0) (hF'' : ∀ t, m ≤ t → 0 ≤ deriv (deriv F) t)
    (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 a 0 0 (W1p.contDiffComp ENNReal.ofNat_ne_top (hF.of_le one_le_two) hM hF0 u)
      (W1p.posPart ENNReal.ofNat_ne_top (W1p.ofTestFunctionₗ mu Omega 2 φ)) ≤ 0 := by
  have hp : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := ENNReal.ofNat_ne_top
  set w := W1p.contDiffComp hp (hF.of_le one_le_two) hM hF0 u
  set P := W1p.posPart hp (W1p.ofTestFunctionₗ mu Omega 2 φ)
  -- `T₀ = -φ F'(u)`, with weak gradient `-φ F''(u) ∇u - F'(u) ∇φ`.
  have hdF : ContDiff ℝ 1 (deriv F) := (contDiff_succ_iff_deriv.1 hF).2.2
  set T₀ := -W1p.testFunctionSMulComp hp φ hdF hM' u
  have hvalT₀ : ∀ᵐ x ∂mu.restrict Omega, W1p.value T₀ x = -(φ x * deriv F (W1p.value u x)) := by
    filter_upwards [Lp.coeFn_neg (W1p.value (W1p.testFunctionSMulComp hp φ hdF hM' u)),
      W1p.value_testFunctionSMulComp_ae hp φ hdF hM' u] with x h₁ h₂
    rw [← W1p.valueL_apply, map_neg, W1p.valueL_apply, h₁, Pi.neg_apply, h₂]
  have hgradT₀ : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient T₀ x =
      -(φ x * deriv (deriv F) (W1p.value u x)) • W1p.gradient u x -
        deriv F (W1p.value u x) • ∇ (φ : EuclideanSpace ℝ ι → ℝ) x := by
    filter_upwards [Lp.coeFn_neg (W1p.gradient (W1p.testFunctionSMulComp hp φ hdF hM' u)),
      W1p.gradient_testFunctionSMulComp_ae hp φ hdF hM' u] with x h₁ h₂
    rw [← W1p.gradientL_apply, map_neg, W1p.gradientL_apply, h₁, Pi.neg_apply, h₂,
      neg_smul]
    abel
  set T := W1p.posPart hp T₀
  -- `T` is a nonnegative element of `H¹₀(Ω)`, as the positive part of `-φ F'(u)`.
  have hvalT : ∀ᵐ x ∂mu.restrict Omega, W1p.value T x = max (W1p.value T₀ x) 0 := by
    rw [W1p.value_posPart]
    exact Lp.coeFn_posPart _
  have hTmem : T ∈ w1p0Submodule mu Omega 2 :=
    W1p.posPart_mem_w1p0Submodule hp
      ((w1p0Submodule mu Omega 2).toSubmodule.neg_mem
        (W1p.testFunctionSMulComp_mem_w1p0Submodule hp φ hdF hM' u))
  have hTnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value T x := by
    filter_upwards [hvalT] with x hx
    rw [hx]
    exact le_max_right _ _
  have hsup := hu ⟨T, hTmem⟩ hTnonneg
  simp only at hsup
  -- Compare the energy densities pointwise.
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hE (v₁ v₂ : W1p mu Omega 2) := h.integrable_energyIntegrand_jetField (b := 0) (c := 0)
    (beta := 0) (gamma := 0) ha aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ _ => by simp) (fun _ _ => by simp) v₁ v₂
  rw [energyFormH1_def] at hsup ⊢
  refine (integral_mono_ae (hE w P) (hE u T).neg ?_).trans
    (by simp only [Pi.neg_apply, integral_neg]; linarith)
  filter_upwards [hmem, hum, W1p.gradient_contDiffComp_ae hp (hF.of_le one_le_two) hM hF0 u,
    W1p.gradient_posPart_ae hp (W1p.ofTestFunctionₗ mu Omega 2 φ),
    W1p.gradient_posPart_ae hp T₀, hvalT₀, hgradT₀, testFunctionLp_apply_ae (mu := mu) 2 φ,
    gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx hux hgw hgP hgT hT₀ hgT₀ hφx hgφx
  have key := matrixBilinearForm_ite_smul_le (A := a x)
    (fun ξ => by rw [matrixBilinearForm_self]; exact h.quadraticForm_nonneg hx ξ)
    (z := φ x) (hF' _ hux) (hF'' _ hux) (W1p.gradient u x) (∇ (φ : EuclideanSpace ℝ ι → ℝ) x)
  have hP : W1p.gradient P x = if 0 < φ x then ∇ (φ : EuclideanSpace ℝ ι → ℝ) x else 0 := by
    rw [hgP, indicator_apply]
    simp only [mem_ofPred_eq, W1p.value_ofTestFunctionₗ, hφx, W1p.gradient_ofTestFunctionₗ, hgφx]
  have hT : W1p.gradient T x = if 0 < -(φ x * deriv F (W1p.value u x)) then
      -(φ x * deriv (deriv F) (W1p.value u x)) • W1p.gradient u x -
        deriv F (W1p.value u x) • ∇ (φ : EuclideanSpace ℝ ι → ℝ) x else 0 := by
    rw [hgT, indicator_apply]
    simp only [mem_ofPred_eq, hT₀, hgT₀]
  simp only [energyIntegrand_apply, jetField_apply, Pi.zero_apply, Pi.neg_apply,
    driftForm_apply, massForm_apply, inner_zero_left, zero_mul, add_zero]
  rw [hgw, hP, hT]
  exact key

/-- **A convex nonincreasing function of a supersolution is a subsolution.** Let `a` be measurable
and uniformly elliptic on `Ω`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ m`
almost everywhere on `Ω`. Let `F` be `C²` with bounded first and second derivatives and
`F(0) = 0`, so that `F(u) ∈ H¹(Ω)` (`TauCeti.W1p.contDiffComp`), and suppose that `F' ≤ 0` and
`F'' ≥ 0` on `[m, ∞)`. Then `F(u)` is a weak subsolution: `a(F(u), v) ≤ 0` for every
nonnegative `v ∈ H¹₀(Ω)`.

The condition at `0` and the global bounds on `F'` and `F''` only make `F(u)` and the localized
products `φ F'(u)`, for test functions `φ ∈ C_c^∞(Ω)`, Sobolev functions; the sign conditions are
used on `[m, ∞)` alone. -/
theorem UniformlyEllipticOn.energyFormH1_contDiffComp_nonpos
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {M M' : ℝ≥0} (hM : ∀ t, ‖deriv F t‖₊ ≤ M)
    (hM' : ∀ t, ‖deriv (deriv F) t‖₊ ≤ M') (hF0 : F 0 = 0) {m : ℝ}
    (hum : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    (hF' : ∀ t, m ≤ t → deriv F t ≤ 0) (hF'' : ∀ t, m ≤ t → 0 ≤ deriv (deriv F) t)
    (v : W1p0 mu Omega 2)
    (hv : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) :
    energyFormH1 a 0 0 (W1p.contDiffComp ENNReal.ofNat_ne_top (hF.of_le one_le_two) hM hF0 u)
      (v : W1p mu Omega 2) ≤ 0 := by
  have hp : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := ENNReal.ofNat_ne_top
  set w := W1p.contDiffComp hp (hF.of_le one_le_two) hM hF0 u
  have hcoeff := memLp_energyIntegrand_of_bounds (mu := mu) (Omega := Omega) (a := a)
    (b := 0) (c := 0) (beta := 0) (gamma := 0) h.upper_nonneg ha aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _ hx η ξ => h.upper_bound hx η ξ) (fun _ _ => by simp)
    (fun _ _ => by simp)
  -- The set of `z` with `a(F(u), z⁺) ≤ 0` is closed and contains every test function.
  have hclosed : IsClosed {z : W1p mu Omega 2 | energyFormH1 a 0 0 w (W1p.posPart hp z) ≤ 0} := by
    simp only [← energyFormH1L_apply hcoeff]
    exact isClosed_le ((energyFormH1L hcoeff w).continuous.comp (W1p.continuous_posPart hp))
      continuous_const
  have hsub := w1p0Submodule_subset_of_isClosed hclosed fun φ =>
    energyFormH1_contDiffComp_posPart_ofTestFunction_nonpos h ha hu hF hM hM' hF0 hum hF' hF'' φ
  have := hsub v.2
  rwa [mem_ofPred_eq, W1p.posPart_eq_self_of_ae_nonneg hp hv] at this

/-! ### The lower bound for positive supersolutions -/

/-- The smooth approximation `t / (t² + c²)` of the reciprocal `1/t`. -/
private def invApprox (c t : ℝ) : ℝ := t / (t ^ 2 + c ^ 2)

private theorem hasDerivAt_invApprox {c : ℝ} (hc : 0 < c) (t : ℝ) :
    HasDerivAt (invApprox c) ((c ^ 2 - t ^ 2) / (t ^ 2 + c ^ 2) ^ 2) t :=
  ((hasDerivAt_id' t).div ((hasDerivAt_pow 2 t).add_const (c ^ 2)) (by positivity)).congr_deriv
    (by ring)

private theorem deriv_invApprox {c : ℝ} (hc : 0 < c) :
    deriv (invApprox c) = fun t => (c ^ 2 - t ^ 2) / (t ^ 2 + c ^ 2) ^ 2 :=
  funext fun t => (hasDerivAt_invApprox hc t).deriv

private theorem deriv_deriv_invApprox {c : ℝ} (hc : 0 < c) :
    deriv (deriv (invApprox c)) = fun t => 2 * t * (t ^ 2 - 3 * c ^ 2) / (t ^ 2 + c ^ 2) ^ 3 := by
  rw [deriv_invApprox hc]
  refine funext fun t => HasDerivAt.deriv ?_
  have h : t ^ 2 + c ^ 2 ≠ 0 := by positivity
  refine (((hasDerivAt_pow 2 t).const_sub (c ^ 2)).div
    (((hasDerivAt_pow 2 t).add_const (c ^ 2)).fun_pow 2) (pow_ne_zero 2 h)).congr_deriv ?_
  field_simp
  ring

private theorem contDiff_invApprox {c : ℝ} (hc : 0 < c) : ContDiff ℝ 2 (invApprox c) := by
  unfold invApprox
  fun_prop (disch := intro; positivity)

private theorem abs_deriv_invApprox_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |deriv (invApprox c) t| ≤ (c ^ 2)⁻¹ := by
  have hs : 0 < t ^ 2 + c ^ 2 := by positivity
  have h1 : |c ^ 2 - t ^ 2| ≤ t ^ 2 + c ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t, sq_nonneg c]
  rw [deriv_invApprox hc, abs_div, abs_of_pos (pow_pos hs 2)]
  calc |c ^ 2 - t ^ 2| / (t ^ 2 + c ^ 2) ^ 2 ≤ (t ^ 2 + c ^ 2) / (t ^ 2 + c ^ 2) ^ 2 := by
        gcongr
    _ = (t ^ 2 + c ^ 2)⁻¹ := by field_simp
    _ ≤ (c ^ 2)⁻¹ := by gcongr; nlinarith [sq_nonneg t]

private theorem abs_deriv_deriv_invApprox_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |deriv (deriv (invApprox c)) t| ≤ 3 / c ^ 3 := by
  have hs : 0 < t ^ 2 + c ^ 2 := by positivity
  have h1 : |t ^ 2 - 3 * c ^ 2| ≤ 3 * (t ^ 2 + c ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t, sq_nonneg c]
  have h2 : 2 * |t| * c ≤ t ^ 2 + c ^ 2 := by nlinarith [sq_nonneg (|t| - c), sq_abs t]
  rw [deriv_deriv_invApprox hc, abs_div, abs_of_pos (pow_pos hs 3),
    div_le_div_iff₀ (pow_pos hs 3) (pow_pos hc 3), abs_mul, abs_mul, abs_two]
  calc 2 * |t| * |t ^ 2 - 3 * c ^ 2| * c ^ 3 ≤ 2 * |t| * (3 * (t ^ 2 + c ^ 2)) * c ^ 3 := by
        gcongr
    _ = 3 * (t ^ 2 + c ^ 2) * ((2 * |t| * c) * c ^ 2) := by ring
    _ ≤ 3 * (t ^ 2 + c ^ 2) * ((t ^ 2 + c ^ 2) * (t ^ 2 + c ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg t]
    _ = 3 * (t ^ 2 + c ^ 2) ^ 3 := by ring

/-- `t / (t² + c²)` is nonincreasing on `[2c, ∞)`. -/
private theorem deriv_invApprox_nonpos {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 2 * c ≤ t) :
    deriv (invApprox c) t ≤ 0 := by
  rw [deriv_invApprox hc]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

/-- `t / (t² + c²)` is convex on `[2c, ∞)`. -/
private theorem deriv_deriv_invApprox_nonneg {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 2 * c ≤ t) :
    0 ≤ deriv (deriv (invApprox c)) t := by
  rw [deriv_deriv_invApprox hc]
  exact div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by positivity)

/-- `0 ≤ t / (t² + c²) ≤ 1/t` for `t > 0`. -/
private theorem invApprox_mem_Icc {c t : ℝ} (ht : 0 < t) : invApprox c t ∈ Icc 0 t⁻¹ := by
  unfold invApprox
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ ht]
  nlinarith [sq_nonneg c]

/-- `t / (t² + c²) → 1/t` as `c → 0`. -/
private theorem tendsto_invApprox {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => invApprox (c k) t) atTop (𝓝 t⁻¹) := by
  unfold invApprox
  have hlim : Tendsto (fun k => t / (t ^ 2 + c k ^ 2)) atTop (𝓝 (t / (t ^ 2 + 0 ^ 2))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add (hc.pow 2)) (by positivity)
  rwa [show t / (t ^ 2 + 0 ^ 2) = t⁻¹ by rw [zero_pow two_ne_zero, add_zero]; field_simp] at hlim

/-- The lower bound for a positive supersolution, from an upper bound for subsolutions at the
level `0`: if every weak subsolution `w` satisfies `w ≤ K ‖w⁺‖_{L²(B(x₀, R))}` on `B(x₀, R/2)`,
then `u⁻¹ ≤ K ‖u⁻¹‖_{L²(B(x₀, R))}` there. The bound is applied to `w = u / (u² + c²)` and
`c → 0`. -/
private theorem ae_inv_value_le_mul_sqrt_setIntegral
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2))
    {m : ℝ} (hm : 0 < m) (hum : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    {x₀ : EuclideanSpace ℝ ι} {R K : ℝ} (hR : 0 < R)
    (hball : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (hK : 0 ≤ K)
    (hsub : ∀ w : W1p mu Omega 2,
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 w (v : W1p mu Omega 2) ≤ 0) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        W1p.value w x ≤ 0 + K * √(∫ x in ball x₀ R, max (W1p.value w x - 0) 0 ^ 2 ∂mu)) :
    ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
      (W1p.value u x)⁻¹ ≤ K * √(∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ 2 ∂mu) := by
  have hhalf : ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (half_le_self hR.le)).trans hball
  have humB : ∀ᵐ x ∂mu.restrict (ball x₀ R), m ≤ W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset hball hum
  -- `u⁻² ≤ m⁻²` is integrable on the ball, which has finite measure.
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (fun x => (W1p.value u x)⁻¹ ^ 2) (mu.restrict (ball x₀ R)) := by
    have hmeas : AEMeasurable (fun x => (W1p.value u x)⁻¹ ^ 2) (mu.restrict Omega) :=
      ((Lp.aestronglyMeasurable (W1p.value u)).aemeasurable.inv).pow_const 2
    refine (integrable_const ((m⁻¹) ^ 2)).mono'
      (hmeas.aestronglyMeasurable.mono_measure (Measure.restrict_mono hball le_rfl)) ?_
    filter_upwards [humB] with x hx
    have hux : 0 < W1p.value u x := hm.trans_le hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  -- The approximations `u / (u² + c²)`, with `c = m / (k + 2) ≤ m / 2`, are subsolutions.
  set c : ℕ → ℝ := fun k => m / ((k : ℝ) + 2)
  have hc : ∀ k, 0 < c k := fun k => by positivity
  have hcm : ∀ k, 2 * c k ≤ m := fun k => by
    simp only [c]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hbound : ∀ k, ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
      invApprox (c k) (W1p.value u x) ≤
        K * √(∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ 2 ∂mu) := by
    intro k
    have hF := contDiff_invApprox (hc k)
    have hF0 : invApprox (c k) 0 = 0 := by simp [invApprox]
    -- The bounds on `F'` and `F''` in the form required by `TauCeti.W1p.contDiffComp`.
    have hM : ∀ t, ‖deriv (invApprox (c k)) t‖₊ ≤ ((c k ^ 2)⁻¹).toNNReal := fun t => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)]
      exact abs_deriv_invApprox_le (hc k) t
    have hM' : ∀ t, ‖deriv (deriv (invApprox (c k))) t‖₊ ≤ (3 / c k ^ 3).toNNReal := fun t => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)]
      exact abs_deriv_deriv_invApprox_le (hc k) t
    have hval := W1p.value_contDiffComp_ae ENNReal.ofNat_ne_top (hF.of_le one_le_two) hM hF0 u
    have hw := hsub _ fun v hv => h.energyFormH1_contDiffComp_nonpos ha hu hF hM hM' hF0 hum
      (fun t ht => deriv_invApprox_nonpos (hc k) ((hcm k).trans ht))
      (fun t ht => deriv_deriv_invApprox_nonneg (hc k) ((hcm k).trans ht)) v hv
    have hle : ∫ x in ball x₀ R, max (W1p.value (W1p.contDiffComp ENNReal.ofNat_ne_top
          (hF.of_le one_le_two) hM hF0 u) x - 0) 0 ^ 2 ∂mu ≤
        ∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ 2 ∂mu := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hint ?_
      filter_upwards [humB, ae_restrict_of_ae_restrict_of_subset hball hval] with x hx hvx
      have hux := invApprox_mem_Icc (c := c k) (hm.trans_le hx)
      rw [hvx, sub_zero, max_eq_left hux.1]
      exact pow_le_pow_left₀ hux.1 hux.2 2
    filter_upwards [hw, ae_restrict_of_ae_restrict_of_subset hhalf hval] with x hx hvx
    rw [← hvx]
    refine hx.trans ?_
    rw [zero_add]
    gcongr
  filter_upwards [ae_all_iff.2 hbound, ae_restrict_of_ae_restrict_of_subset hhalf hum]
    with x hx hux
  have hlim : Tendsto c atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact le_of_tendsto' (tendsto_invApprox hlim (hm.trans_le hux)) hx

/-- **The lower bound for positive supersolutions.** For every exponent `q > 2` and constant `S`
there is `D > 0`, depending on `λ`, `Λ`, `q`, `S` (and the normalization of the additive Haar
measure used), such that the following holds. Let `a` be measurable and uniformly elliptic on
`Ω` with constants `λ, Λ`, suppose that `‖v‖_q ≤ S ‖∇v‖₂` for every `v ∈ W^{1,2}_0(Ω)`, and let
`u ∈ H¹(Ω)` be a weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every
nonnegative `v ∈ H¹₀(Ω)`, with `u ≥ m > 0` almost everywhere on `Ω`. Then for every ball
`B(x₀, R) ⊆ Ω`,

`u⁻¹ ≤ D R^{-1/α} (∫_{B(x₀, R)} u⁻²)^{1/2}` almost everywhere on `B(x₀, R/2)`,

where `α = 1 - 2/q`. The constant does not depend on `m`. -/
theorem exists_ae_inv_value_le_mul_rpow_mul_sqrt_setIntegral {q : ℝ≥0∞} (hq : 2 < q) (S : ℝ≥0) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {m : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        (W1p.value u x)⁻¹ ≤ D * R ^ (-(1 - 2 / q.toReal)⁻¹) *
          √(∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ := exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral (mu := mu)
    (lam := lam) (Lam := Lam) hq S
  exact ⟨D, hD, fun h ha hS hu hm hum hR hball =>
    ae_inv_value_le_mul_sqrt_setIntegral h ha hu hm hum hR hball (by positivity)
      fun _ hw => hbound (k := 0) h ha hS hw hR hball⟩

/-- **The lower bound for positive supersolutions in dimension `n ≥ 3`.** Let `2*` be the Sobolev
exponent of `W^{1,2}` in dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces
`n ≥ 3`). There is `D > 0`, depending on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that for every measurable, uniformly elliptic `a` on `Ω` with
constants `λ, Λ`, every weak supersolution `u ∈ H¹(Ω)` of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0` with `u ≥ m > 0`
almost everywhere on `Ω`, and every ball `B(x₀, R) ⊆ Ω`,

`u⁻¹ ≤ D R^{-n/2} (∫_{B(x₀, R)} u⁻²)^{1/2}` almost everywhere on `B(x₀, R/2)`.

So `u` is bounded below on `B(x₀, R/2)` by `D⁻¹ R^{n/2} ‖u⁻¹‖_{L²(B(x₀, R))}⁻¹`. The constant does
not depend on `m`, on `Ω`, or on the size of `u`. -/
theorem exists_ae_inv_value_le_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {m : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        (W1p.value u x)⁻¹ ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral_of_inv_add_eq_inv (mu := mu)
      (lam := lam) (Lam := Lam) hpstar hexp
  exact ⟨D, hD, fun h ha hu hm hum hR hball =>
    ae_inv_value_le_mul_sqrt_setIntegral h ha hu hm hum hR hball (by positivity)
      fun _ hw => hbound (k := 0) h ha hw hR hball⟩

end PDE

end TauCeti
