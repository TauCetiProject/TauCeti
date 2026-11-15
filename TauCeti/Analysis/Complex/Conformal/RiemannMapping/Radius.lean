/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
public import TauCeti.Analysis.Complex.Sqrt
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.Moebius
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Equivalence
import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane
import TauCeti.Analysis.Complex.SlitPlane

/-!
# The conformal radius of a simply connected plane domain

Let `Ω ⊆ ℂ` be a simply connected open proper subset of the complex plane and `z₀ ∈ Ω` a base
point. By `TauCeti.riemannMapping_normalized`, there is a holomorphic bijection `φ : Ω → 𝔻` onto the
open unit disc sending `z₀` to `0` with positive real derivative at `z₀`, and any two such maps
agree on `Ω`. The **conformal radius** (or **inner radius**) of `Ω` with respect to `z₀` is the
positive real number

`riemannConformalRadius Ω z₀ = ‖deriv φ z₀‖⁻¹`,

equivalently `‖deriv F 0‖` for the inverse biholomorphism `F : 𝔻 → Ω` sending `0` to `z₀`. Outside
the class of pointed simply connected open proper domains `(Ω, z₀)` with `z₀ ∈ Ω`, the function is
totalized to `0`.

## Main definitions and results

* `TauCeti.riemannConformalRadius` — the conformal radius `‖deriv φ z₀‖⁻¹` of a simply connected
  open proper domain `Ω ⊆ ℂ` at `z₀ ∈ Ω`, and `0` outside that eligible pointed-domain class.
* `TauCeti.IsNormalizedRiemannMapOn.riemannConformalRadius_eq` and
  `TauCeti.IsNormalizedRiemannMapOn.deriv_eq_inv_riemannConformalRadius` — independence of the
  normalized Riemann-map witness and identification of `deriv φ z₀` with
  `(riemannConformalRadius Ω z₀)⁻¹`.
* `TauCeti.riemannConformalRadius_eq_inv_norm_deriv_of_bijOn_ball`,
  `TauCeti.riemannConformalRadius_eq_one_sub_norm_sq_div_norm_deriv_of_bijOn_ball`, and
  `TauCeti.riemannConformalRadius_eq_norm_deriv_of_bijOn_ball_domain` — formulas for unnormalized
  biholomorphisms `Ω → 𝔻` (both origin-centered and uncentered, where the hyperbolic defect
  `1 - ‖φ z₀‖ ^ 2` appears) and inverse biholomorphisms `𝔻 → Ω`.
* `TauCeti.norm_deriv_le_riemannConformalRadius_of_mapsTo_ball` and
  `TauCeti.norm_deriv_eq_riemannConformalRadius_iff_bijOn` — Schwarz extremality of the conformal
  radius among holomorphic maps `𝔻 → Ω` sending `0` to `z₀`, with equality if and only if the map
  is a bijection onto `Ω`.
* `TauCeti.riemannConformalRadius_mono` and `TauCeti.riemannConformalRadius_strictMono` — domain
  monotonicity and strict monotonicity on proper subdomains.
* `TauCeti.riemannConformalRadius_of_bijOn` and `TauCeti.riemannConformalRadius_image_affine` —
  conformal covariance `cr(h(Ω), h(z₀)) = ‖h'(z₀)‖ cr(Ω, z₀)` under holomorphic bijections and
  unconditional affine covariance `cr(a Ω + b, a z₀ + b) = ‖a‖ cr(Ω, z₀)`.
* `TauCeti.tendsto_riemannConformalRadius_iUnion` — monotone open-exhaustion continuity: if open
  simply connected domains `U i` increase to a proper domain `⋃ i, U i`, then their conformal radii
  at `z₀` converge to that of the union.
* Closed-form evaluations on classical domains:
  * `TauCeti.riemannConformalRadius_ball_zero_one`, `TauCeti.riemannConformalRadius_ball`,
    `TauCeti.riemannConformalRadius_ball_self`, and
    `TauCeti.le_riemannConformalRadius_of_ball_subset` — `(R ^ 2 - ‖z₀ - b‖ ^ 2) / R` on
    `ball b R`, hence `1 - ‖z₀‖ ^ 2` on the unit disc, `R` at the centre `b`, and the inner-disc
    lower bound `R ≤ riemannConformalRadius Ω z₀` whenever `ball z₀ R ⊆ Ω`.
  * `TauCeti.riemannConformalRadius_re_pos` and
    `TauCeti.riemannConformalRadius_upperHalfPlaneSet` — `2 * z₀.re` on `{z | 0 < z.re}` (giving
    `2` at `1`) and `2 * z₀.im` on the upper half-plane.
  * `TauCeti.riemannConformalRadius_slitPlane`,
    `TauCeti.riemannConformalRadius_slitPlane_ofReal`, and
    `TauCeti.riemannConformalRadius_slitPlane_one` — `4 * ‖Complex.sqrt z₀‖ * (Complex.sqrt z₀).re`
    on `Complex.slitPlane`, giving `4 * x` at `x > 0` and `4` at `1`.

## References

* L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill, 1979, Ch. 6 §1.
* V. N. Dubinin, *On the change in harmonic measure under symmetrization*, Mat. Sb. 124(166)
  (1984), English transl. Math. USSR-Sb. 52 (1985), §1, pp. 270–271.
* E. B. Saff, *Logarithmic Potential Theory with Applications to Approximation Theory*,
  Approximation Theory XIII: San Antonio 2010, Contemp. Math. 553, Amer. Math. Soc., 2011, §3,
  Theorem 3.5, p. 185.
-/

public section

namespace TauCeti

open _root_.Complex Filter Function Metric Set
open scoped ComplexConjugate ComplexOrder Topology

variable {Ω Ω' : Set ℂ} {f φ ψ F h : ℂ → ℂ} {z₀ : ℂ}

/-! ### Definition and eligibility API -/

/-- The **conformal radius** of a simply connected open proper subset `Ω ⊆ ℂ` at a base point
`z₀ ∈ Ω`, defined as `‖deriv φ z₀‖⁻¹` for the normalized Riemann map `φ : Ω → ball 0 1` sending
`z₀` to `0` with `0 < deriv φ z₀`. Outside the class of pointed simply connected open proper
domains `(Ω, z₀)` with `z₀ ∈ Ω`, its value is `0`. -/
noncomputable def riemannConformalRadius (Ω : Set ℂ) (z₀ : ℂ) : ℝ := by
  classical
  exact if h : IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω then
    ‖deriv (Classical.choose (exists_isNormalizedRiemannMapOn h.1 h.2.1 h.2.2.1 h.2.2.2)) z₀‖⁻¹
  else 0

/-- For any normalized Riemann map `f` of an open domain `Ω` at `z₀`, the conformal radius is
`‖deriv f z₀‖⁻¹`. Neither simple connectivity nor properness of `Ω` needs to be supplied separately,
since the existence of `f` on open `Ω` already entails both. -/
theorem IsNormalizedRiemannMapOn.riemannConformalRadius_eq
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) :
    riemannConformalRadius Ω z₀ = ‖deriv f z₀‖⁻¹ := by
  have helig : IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω :=
    ⟨hΩo, hf.isSimplyConnected hΩo, hf.ne_univ, hf.base_mem⟩
  rw [riemannConformalRadius, dite_eq_left_of_eq_true (eq_true helig)]
  have hchoose := Classical.choose_spec
    (exists_isNormalizedRiemannMapOn helig.1 helig.2.1 helig.2.2.1 helig.2.2.2)
  rw [hchoose.norm_deriv_eq hf hΩo]

/-- The derivative norm of a normalized Riemann map at its base point is the reciprocal of the
conformal radius. -/
theorem IsNormalizedRiemannMapOn.norm_deriv_eq_inv_riemannConformalRadius
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) :
    ‖deriv f z₀‖ = (riemannConformalRadius Ω z₀)⁻¹ := by
  rw [hf.riemannConformalRadius_eq hΩo, inv_inv]

/-- Because a normalized Riemann map has positive real derivative at its base point, that complex
derivative itself equals `(riemannConformalRadius Ω z₀)⁻¹`. -/
theorem IsNormalizedRiemannMapOn.deriv_eq_inv_riemannConformalRadius
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) :
    deriv f z₀ = ((riemannConformalRadius Ω z₀)⁻¹ : ℝ) := by
  rw [← hf.coe_norm_deriv, hf.norm_deriv_eq_inv_riemannConformalRadius hΩo]

/-- The holomorphic inverse `Function.invFunOn f Ω` of a normalized Riemann map has derivative
`riemannConformalRadius Ω z₀` at the origin. -/
theorem IsNormalizedRiemannMapOn.hasDerivAt_invFunOn_zero
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) :
    HasDerivAt (Function.invFunOn f Ω) (riemannConformalRadius Ω z₀) 0 := by
  have hinv := hasDerivAt_invFunOn hf.differentiableOn hΩo hf.injOn hf.base_mem
  rw [hf.map_base, hf.deriv_eq_inv_riemannConformalRadius hΩo, ← Complex.ofReal_inv, inv_inv]
    at hinv
  exact hinv

/-- The complex derivative at `0` of the inverse of a normalized Riemann map is the conformal
radius. -/
theorem IsNormalizedRiemannMapOn.deriv_invFunOn_zero
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) :
    deriv (Function.invFunOn f Ω) 0 = riemannConformalRadius Ω z₀ :=
  (hf.hasDerivAt_invFunOn_zero hΩo).deriv

/-- Outside the eligible pointed-domain class, `riemannConformalRadius` takes the value `0`. -/
private theorem riemannConformalRadius_eq_zero_of_not
    (h : ¬ (IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω)) :
    riemannConformalRadius Ω z₀ = 0 := by
  rw [riemannConformalRadius, dite_eq_right_of_eq_false (eq_false h)]

/-- If `Ω` is not open, its conformal radius at any point is `0`. -/
theorem riemannConformalRadius_eq_zero_of_not_isOpen (h : ¬ IsOpen Ω) :
    riemannConformalRadius Ω z₀ = 0 :=
  riemannConformalRadius_eq_zero_of_not fun helig => h helig.1

/-- If `Ω` is not simply connected, its conformal radius at any point is `0`. -/
theorem riemannConformalRadius_eq_zero_of_not_isSimplyConnected (h : ¬ IsSimplyConnected Ω) :
    riemannConformalRadius Ω z₀ = 0 :=
  riemannConformalRadius_eq_zero_of_not fun helig => h helig.2.1

/-- At a point outside `Ω`, `riemannConformalRadius Ω z₀` is `0`. -/
theorem riemannConformalRadius_eq_zero_of_notMem (h : z₀ ∉ Ω) :
    riemannConformalRadius Ω z₀ = 0 :=
  riemannConformalRadius_eq_zero_of_not fun helig => h helig.2.2.2

/-- The whole complex plane has totalized conformal radius `0`. -/
@[simp]
theorem riemannConformalRadius_univ (z₀ : ℂ) : riemannConformalRadius univ z₀ = 0 :=
  riemannConformalRadius_eq_zero_of_not fun helig => helig.2.2.1 rfl

/-- The empty set has conformal radius `0`. -/
@[simp]
theorem riemannConformalRadius_empty (z₀ : ℂ) : riemannConformalRadius ∅ z₀ = 0 :=
  riemannConformalRadius_eq_zero_of_notMem (notMem_empty z₀)

/-- A singleton in `ℂ` is not open, so its conformal radius is `0`. -/
@[simp]
theorem riemannConformalRadius_singleton (w z₀ : ℂ) : riemannConformalRadius {w} z₀ = 0 :=
  riemannConformalRadius_eq_zero_of_not_isOpen (not_isOpen_singleton w)

/-- On an eligible pointed domain, the conformal radius is strictly positive. -/
theorem riemannConformalRadius_pos (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ)
    (hz₀ : z₀ ∈ Ω) : 0 < riemannConformalRadius Ω z₀ := by
  obtain ⟨f, hf⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hΩ hz₀
  rw [hf.riemannConformalRadius_eq hΩo]
  exact inv_pos.mpr hf.norm_deriv_pos

/-- The conformal radius is nonnegative for every set and base point. -/
@[simp]
theorem riemannConformalRadius_nonneg (Ω : Set ℂ) (z₀ : ℂ) :
    0 ≤ riemannConformalRadius Ω z₀ := by
  by_cases h : IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω
  · exact (riemannConformalRadius_pos h.1 h.2.1 h.2.2.1 h.2.2.2).le
  · rw [riemannConformalRadius_eq_zero_of_not h]

/-- The conformal radius is strictly positive if and only if `(Ω, z₀)` is an eligible pointed
simply connected open proper domain. -/
theorem riemannConformalRadius_pos_iff :
    0 < riemannConformalRadius Ω z₀ ↔
      IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω :=
  ⟨fun hpos => by_contra fun h => by
      rw [riemannConformalRadius_eq_zero_of_not h] at hpos
      exact lt_irrefl 0 hpos,
    fun h => riemannConformalRadius_pos h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-- The conformal radius is nonzero if and only if `(Ω, z₀)` is an eligible pointed simply
connected open proper domain. -/
theorem riemannConformalRadius_ne_zero_iff :
    riemannConformalRadius Ω z₀ ≠ 0 ↔
      IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω :=
  ⟨fun h => riemannConformalRadius_pos_iff.mp
      ((riemannConformalRadius_nonneg Ω z₀).lt_of_ne' h),
    fun h => (riemannConformalRadius_pos_iff.mpr h).ne'⟩

/-- The conformal radius vanishes if and only if `(Ω, z₀)` lies outside the eligible pointed-domain
class. -/
theorem riemannConformalRadius_eq_zero_iff :
    riemannConformalRadius Ω z₀ = 0 ↔
      ¬ (IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω) := by
  rw [← not_ne_iff, riemannConformalRadius_ne_zero_iff]

/-! ### Formulas for unnormalized and inverse biholomorphisms -/

/-- **Phase-independent domain-to-disc formula.** For *any* holomorphic bijection `φ` of an open set
`Ω` onto `ball 0 1` with `φ z₀ = 0` — without requiring `deriv φ z₀` to be real and positive — the
conformal radius is `‖deriv φ z₀‖⁻¹`. Rotating `φ` by `‖deriv φ z₀‖ / deriv φ z₀` produces the
normalized Riemann map without changing the derivative modulus. -/
theorem riemannConformalRadius_eq_inv_norm_deriv_of_bijOn_ball (hΩo : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hφd : DifferentiableOn ℂ φ Ω) (hφbij : BijOn φ Ω (ball (0 : ℂ) 1)) (hφ0 : φ z₀ = 0) :
    riemannConformalRadius Ω z₀ = ‖deriv φ z₀‖⁻¹ := by
  have hc : deriv φ z₀ ≠ 0 := deriv_ne_zero_of_injOn hφd hΩo hφbij.injOn hz₀
  have hcpos : 0 < ‖deriv φ z₀‖ := norm_pos_iff.mpr hc
  set u : ℂ := ((‖deriv φ z₀‖ : ℝ) : ℂ) / deriv φ z₀ with hu_def
  have hnu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
      div_self hcpos.ne']
  have hnorm_map : IsNormalizedRiemannMapOn (fun z => u * φ z) Ω z₀ := by
    refine ⟨hz₀, hφd.const_mul u, (bijOn_mul_left_of_norm_eq_one hnu).2.comp hφbij,
      by simp [hφ0], ?_⟩
    rw [deriv_const_mul_field, hu_def, div_mul_cancel₀ _ hc]
    exact Complex.zero_lt_real.mpr hcpos
  rw [hnorm_map.riemannConformalRadius_eq hΩo, deriv_const_mul_field, norm_mul, hnu, one_mul]

/-- **General uncentered Riemann-map formula.** For any holomorphic bijection `φ` of an open set `Ω`
onto the open unit disc, even when `φ z₀ ≠ 0`, the conformal radius at `z₀ ∈ Ω` is
`(1 - ‖φ z₀‖ ^ 2) / ‖deriv φ z₀‖`. Post-composing `φ` with the unit-disc Möbius factor centred at
`φ z₀` restores the base-point condition `0` and multiplies the derivative modulus by
`(1 - ‖φ z₀‖ ^ 2)⁻¹`. -/
theorem riemannConformalRadius_eq_one_sub_norm_sq_div_norm_deriv_of_bijOn_ball (hΩo : IsOpen Ω)
    (hz₀ : z₀ ∈ Ω) (hφd : DifferentiableOn ℂ φ Ω) (hφbij : BijOn φ Ω (ball (0 : ℂ) 1)) :
    riemannConformalRadius Ω z₀ = (1 - ‖φ z₀‖ ^ 2) / ‖deriv φ z₀‖ := by
  set w₀ : ℂ := φ z₀
  have hw₀ : ‖w₀‖ < 1 := mem_ball_zero_iff.mp (hφbij.mapsTo hz₀)
  have hnw₀ : ‖-w₀‖ < 1 := by simpa using hw₀
  set μ : ℂ → ℂ := fun w => (w - w₀) / (1 - (starRingEnd ℂ) w₀ * w)
  have hμbij : BijOn μ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    refine InvOn.bijOn ⟨leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hw₀, ?_⟩
      (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hw₀)
      (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hnw₀)
    simpa only [neg_neg] using leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hnw₀
  have hcomp_d : DifferentiableOn ℂ (μ ∘ φ) Ω :=
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hw₀).comp hφd hφbij.mapsTo
  have hcomp_bij : BijOn (μ ∘ φ) Ω (ball (0 : ℂ) 1) := hμbij.comp hφbij
  have hcomp_0 : (μ ∘ φ) z₀ = 0 := by simp [μ, w₀]
  have hden : 1 - (starRingEnd ℂ) w₀ * w₀ ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hw₀.le hw₀
  have hμ_at : HasDerivAt μ ((1 - (starRingEnd ℂ) w₀ * w₀) / (1 - (starRingEnd ℂ) w₀ * w₀) ^ 2)
      (φ z₀) := hasDerivAt_unitDiscMoebiusFormula w₀ w₀ hden
  have hφ_at : HasDerivAt φ (deriv φ z₀) z₀ :=
    (hφd.differentiableAt (hΩo.mem_nhds hz₀)).hasDerivAt
  have hderiv : deriv (μ ∘ φ) z₀ =
      ((1 - (starRingEnd ℂ) w₀ * w₀) / (1 - (starRingEnd ℂ) w₀ * w₀) ^ 2) * deriv φ z₀ :=
    (hμ_at.comp z₀ hφ_at).deriv
  rw [riemannConformalRadius_eq_inv_norm_deriv_of_bijOn_ball hΩo hz₀ hcomp_d hcomp_bij hcomp_0,
    hderiv, sq, div_mul_eq_div_div, div_self hden, norm_mul, norm_div, norm_one,
    norm_one_sub_conj_mul_self_of_norm_le_one hw₀.le, one_div_mul_eq_div, inv_div]

/-- **Disc-to-domain biholomorphism formula.** If `F` maps `ball 0 1` holomorphically and
bijectively onto `Ω` with `F 0 = z₀`, then `riemannConformalRadius Ω z₀ = ‖deriv F 0‖`. Openness,
simple connectivity, and properness of `Ω` follow automatically from those of the disc. -/
theorem riemannConformalRadius_eq_norm_deriv_of_bijOn_ball_domain
    (hFd : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hFbij : BijOn F (ball (0 : ℂ) 1) Ω)
    (hF0 : F 0 = z₀) : riemannConformalRadius Ω z₀ = ‖deriv F 0‖ := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hz₀ : z₀ ∈ Ω := hF0 ▸ hFbij.mapsTo h0
  have hΩo : IsOpen Ω :=
    hFbij.image_eq ▸ isOpen_image_of_differentiableOn_of_injOn isOpen_ball hFd hFbij.injOn
  have hinv_d : DifferentiableOn ℂ (Function.invFunOn F (ball (0 : ℂ) 1)) Ω := by
    have h := DifferentiableOn.invFunOn hFd isOpen_ball hFbij.injOn
    rwa [hFbij.image_eq] at h
  have hinv_bij : BijOn (Function.invFunOn F (ball (0 : ℂ) 1)) Ω (ball (0 : ℂ) 1) :=
    hFbij.symm hFbij.invOn_invFunOn.symm
  have hinv_0 : Function.invFunOn F (ball (0 : ℂ) 1) z₀ = 0 := by
    rw [← hF0]
    exact hFbij.injOn.leftInvOn_invFunOn h0
  have hinv_deriv : deriv (Function.invFunOn F (ball (0 : ℂ) 1)) z₀ = (deriv F 0)⁻¹ := by
    have h := (hasDerivAt_invFunOn hFd isOpen_ball hFbij.injOn h0).deriv
    rwa [hF0] at h
  rw [riemannConformalRadius_eq_inv_norm_deriv_of_bijOn_ball hΩo hz₀ hinv_d hinv_bij hinv_0,
    hinv_deriv, norm_inv, inv_inv]

/-! ### Schwarz extremality and domain monotonicity -/

/-- **Disc-to-domain Schwarz bound.** Any holomorphic map `F : ball 0 1 → Ω` into a simply connected
open proper domain `Ω` satisfies `‖deriv F 0‖ ≤ riemannConformalRadius Ω (F 0)`. -/
theorem norm_deriv_le_riemannConformalRadius_of_mapsTo_ball (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) (hFd : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hFm : MapsTo F (ball (0 : ℂ) 1) Ω) (hF0 : F 0 = z₀) :
    ‖deriv F 0‖ ≤ riemannConformalRadius Ω z₀ := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hz₀ : z₀ ∈ Ω := hF0 ▸ hFm h0
  obtain ⟨φ, hφ⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hΩ hz₀
  have hGd : DifferentiableOn ℂ (φ ∘ F) (ball (0 : ℂ) 1) := hφ.differentiableOn.comp hFd hFm
  have hG0 : (φ ∘ F) 0 = 0 := by simp [hF0, hφ.map_base]
  have hGm : MapsTo (φ ∘ F) (ball (0 : ℂ) 1) (closedBall ((φ ∘ F) 0) 1) := by
    rw [hG0]
    exact (hφ.mapsTo.comp hFm).mono_right ball_subset_closedBall
  have hschwarz : ‖deriv (φ ∘ F) 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hGd hGm one_pos
  have hF_at : HasDerivAt F (deriv F 0) 0 :=
    (hFd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
  have hφ_at : HasDerivAt φ (deriv φ z₀) (F 0) := by
    rw [hF0]
    exact (hφ.differentiableOn.differentiableAt (hΩo.mem_nhds hz₀)).hasDerivAt
  rw [(hφ_at.comp 0 hF_at).deriv, norm_mul] at hschwarz
  rw [hφ.riemannConformalRadius_eq hΩo]
  simpa only [mul_one] using (le_inv_mul_iff₀ hφ.norm_deriv_pos).mpr hschwarz

/-- **Extremality of the conformal radius.** Among holomorphic maps `F : ball 0 1 → Ω` into a simply
connected open proper domain `Ω` with `F 0 = z₀`, equality
`‖deriv F 0‖ = riemannConformalRadius Ω z₀` holds if and only if `F` maps `ball 0 1` bijectively
onto `Ω`. -/
theorem norm_deriv_eq_riemannConformalRadius_iff_bijOn (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) (hFd : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hFm : MapsTo F (ball (0 : ℂ) 1) Ω) (hF0 : F 0 = z₀) :
    ‖deriv F 0‖ = riemannConformalRadius Ω z₀ ↔ BijOn F (ball (0 : ℂ) 1) Ω := by
  refine ⟨fun heq => ?_, fun hbij =>
    (riemannConformalRadius_eq_norm_deriv_of_bijOn_ball_domain hFd hbij hF0).symm⟩
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hz₀ : z₀ ∈ Ω := hF0 ▸ hFm h0
  obtain ⟨φ, hφ⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hΩ hz₀
  set G : ℂ → ℂ := φ ∘ F
  have hGd : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := hφ.differentiableOn.comp hFd hFm
  have hG0 : G 0 = 0 := by simp [G, hF0, hφ.map_base]
  have hGm : MapsTo G (ball (0 : ℂ) 1) (closedBall (G 0) 1) := by
    rw [hG0]
    exact (hφ.mapsTo.comp hFm).mono_right ball_subset_closedBall
  have hF_at : HasDerivAt F (deriv F 0) 0 :=
    (hFd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
  have hφ_at : HasDerivAt φ (deriv φ z₀) (F 0) := by
    rw [hF0]
    exact (hφ.differentiableOn.differentiableAt (hΩo.mem_nhds hz₀)).hasDerivAt
  have hGnorm : ‖deriv G 0‖ = 1 := by
    rw [(hφ_at.comp 0 hF_at).deriv, norm_mul, heq, hφ.riemannConformalRadius_eq hΩo,
      mul_inv_cancel₀ hφ.norm_deriv_pos.ne']
  have hds : ‖dslope G 0 0‖ = 1 / 1 := by rw [dslope_same, hGnorm, div_one]
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hGd hGm h0 hds
  have hGrot : BijOn G (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    refine (bijOn_mul_left_of_norm_eq_one hGnorm).2.congr fun w hw => ?_
    simp [haff hw, hG0, dslope_same, mul_comm]
  refine ⟨hFm, fun w₁ hw₁ w₂ hw₂ hw => hGrot.injOn hw₁ hw₂ (congrArg φ hw), fun z hz => ?_⟩
  obtain ⟨w, hw, hwz⟩ := hGrot.surjOn (hφ.mapsTo hz)
  exact ⟨w, hw, hφ.injOn (hFm hw) hz hwz⟩

/-- **Domain-to-disc Schwarz bound.** Any holomorphic map `ψ : Ω → ball 0 1` on an open set `Ω` with
`ψ z₀ = 0` satisfies `‖deriv ψ z₀‖ * riemannConformalRadius Ω z₀ ≤ 1`, without needing `ψ` to be
injective or `Ω` to be eligible (when `(Ω, z₀)` is ineligible the left-hand side is `0`). -/
theorem norm_deriv_mul_riemannConformalRadius_le_one (hΩo : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hψd : DifferentiableOn ℂ ψ Ω) (hψm : MapsTo ψ Ω (ball (0 : ℂ) 1)) (hψ0 : ψ z₀ = 0) :
    ‖deriv ψ z₀‖ * riemannConformalRadius Ω z₀ ≤ 1 := by
  by_cases helig : IsOpen Ω ∧ IsSimplyConnected Ω ∧ Ω ≠ univ ∧ z₀ ∈ Ω
  · obtain ⟨φ, hφ⟩ := exists_isNormalizedRiemannMapOn helig.1 helig.2.1 helig.2.2.1 helig.2.2.2
    set F : ℂ → ℂ := Function.invFunOn φ Ω
    have hFd : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
      have h := DifferentiableOn.invFunOn hφ.differentiableOn hΩo hφ.injOn
      rwa [hφ.image_eq] at h
    have hFm : MapsTo F (ball (0 : ℂ) 1) Ω := hφ.surjOn.mapsTo_invFunOn
    have hF0 : F 0 = z₀ := by rw [← hφ.map_base]; exact hφ.injOn.leftInvOn_invFunOn hz₀
    have hGd : DifferentiableOn ℂ (ψ ∘ F) (ball (0 : ℂ) 1) := hψd.comp hFd hFm
    have hG0 : (ψ ∘ F) 0 = 0 := by simp [hF0, hψ0]
    have hGm : MapsTo (ψ ∘ F) (ball (0 : ℂ) 1) (closedBall ((ψ ∘ F) 0) 1) := by
      rw [hG0]
      exact (hψm.comp hFm).mono_right ball_subset_closedBall
    have hschwarz : ‖deriv (ψ ∘ F) 0‖ ≤ 1 :=
      Complex.norm_deriv_le_one_of_mapsTo_ball hGd hGm one_pos
    have hF_at := hφ.hasDerivAt_invFunOn_zero hΩo
    have hψ_at : HasDerivAt ψ (deriv ψ z₀) (F 0) := by
      rw [hF0]
      exact (hψd.differentiableAt (hΩo.mem_nhds hz₀)).hasDerivAt
    rw [(hψ_at.comp 0 hF_at).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (riemannConformalRadius_nonneg Ω z₀)] at hschwarz
    exact hschwarz
  · rw [riemannConformalRadius_eq_zero_of_not helig, mul_zero]
    exact zero_le_one

/-- **Domain monotonicity of conformal radius.** If `Ω ⊆ Ω'` are simply connected open sets and
`Ω'` is a proper subset of `ℂ`, then `riemannConformalRadius Ω z₀ ≤ riemannConformalRadius Ω' z₀`
for every `z₀ : ℂ`. Properness of `Ω'` is genuinely needed because `riemannConformalRadius univ z₀`
is totalized to `0`. -/
theorem riemannConformalRadius_mono (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩ'o : IsOpen Ω') (hΩ'c : IsSimplyConnected Ω') (hΩ' : Ω' ≠ univ) (hsub : Ω ⊆ Ω') :
    riemannConformalRadius Ω z₀ ≤ riemannConformalRadius Ω' z₀ := by
  by_cases hz₀ : z₀ ∈ Ω
  · have hΩ : Ω ≠ univ := fun h => hΩ' (univ_subset_iff.mp (h ▸ hsub))
    obtain ⟨φ, hφ⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hΩ hz₀
    have hFd : DifferentiableOn ℂ (Function.invFunOn φ Ω) (ball (0 : ℂ) 1) := by
      have h := DifferentiableOn.invFunOn hφ.differentiableOn hΩo hφ.injOn
      rwa [hφ.image_eq] at h
    have hFm : MapsTo (Function.invFunOn φ Ω) (ball (0 : ℂ) 1) Ω' :=
      hφ.surjOn.mapsTo_invFunOn.mono_right hsub
    have hF0 : Function.invFunOn φ Ω 0 = z₀ := by
      rw [← hφ.map_base]
      exact hφ.injOn.leftInvOn_invFunOn hz₀
    have hle := norm_deriv_le_riemannConformalRadius_of_mapsTo_ball hΩ'o hΩ'c hΩ' hFd hFm hF0
    rwa [hφ.deriv_invFunOn_zero hΩo, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (riemannConformalRadius_nonneg Ω z₀)] at hle
  · rw [riemannConformalRadius_eq_zero_of_notMem hz₀]
    exact riemannConformalRadius_nonneg Ω' z₀

/-- **Strict domain monotonicity of conformal radius.** Enlarging a simply connected open domain
`Ω` strictly inside a simply connected open proper domain `Ω'` strictly increases the conformal
radius at every point `z₀ ∈ Ω`. -/
theorem riemannConformalRadius_strictMono (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω)
    (hΩ'o : IsOpen Ω') (hΩ'c : IsSimplyConnected Ω') (hΩ' : Ω' ≠ univ) (hsub : Ω ⊂ Ω')
    (hz₀ : z₀ ∈ Ω) :
    riemannConformalRadius Ω z₀ < riemannConformalRadius Ω' z₀ := by
  refine (riemannConformalRadius_mono hΩo hΩc hΩ'o hΩ'c hΩ' hsub.subset).lt_of_ne fun heq => ?_
  have hΩ : Ω ≠ univ := fun h => hΩ' (univ_subset_iff.mp (h ▸ hsub.subset))
  obtain ⟨φ, hφ⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hΩ hz₀
  set F : ℂ → ℂ := Function.invFunOn φ Ω
  have hFd : DifferentiableOn ℂ F (ball (0 : ℂ) 1) := by
    have h := DifferentiableOn.invFunOn hφ.differentiableOn hΩo hφ.injOn
    rwa [hφ.image_eq] at h
  have hFbij : BijOn F (ball (0 : ℂ) 1) Ω := hφ.bijOn.symm hφ.bijOn.invOn_invFunOn.symm
  have hF0 : F 0 = z₀ := by rw [← hφ.map_base]; exact hφ.injOn.leftInvOn_invFunOn hz₀
  have hnorm : ‖deriv F 0‖ = riemannConformalRadius Ω' z₀ := by
    rw [← heq, hφ.deriv_invFunOn_zero hΩo, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (riemannConformalRadius_nonneg Ω z₀)]
  have hbij' : BijOn F (ball (0 : ℂ) 1) Ω' :=
    (norm_deriv_eq_riemannConformalRadius_iff_bijOn hΩ'o hΩ'c hΩ' hFd
      (hFbij.mapsTo.mono_right hsub.subset) hF0).mp hnorm
  exact hsub.ne (hFbij.image_eq.symm.trans hbij'.image_eq)

/-! ### Conformal transformation law and affine covariance -/

/-- **Conformal transformation law.** If `h` maps an open set `Ω` holomorphically and bijectively
onto `Ω'`, then at every `z₀ ∈ Ω` we have
`riemannConformalRadius Ω' (h z₀) = ‖deriv h z₀‖ * riemannConformalRadius Ω z₀`.
Both the eligible and the totalized zero cases are covered uniformly. -/
theorem riemannConformalRadius_of_bijOn (hΩo : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hhd : DifferentiableOn ℂ h Ω) (hhbij : BijOn h Ω Ω') :
    riemannConformalRadius Ω' (h z₀) = ‖deriv h z₀‖ * riemannConformalRadius Ω z₀ := by
  have hΩ'o : IsOpen Ω' :=
    hhbij.image_eq ▸ isOpen_image_of_differentiableOn_of_injOn hΩo hhd hhbij.injOn
  have hsc_iff : IsSimplyConnected Ω' ↔ IsSimplyConnected Ω :=
    (hhd.toHomeomorphOfBijOn hΩo hhbij).toHomotopyEquiv.simplyConnectedSpace_iff.symm
  by_cases hΩc : IsSimplyConnected Ω
  · have hΩ'c : IsSimplyConnected Ω' := hsc_iff.mpr hΩc
    have huniv_iff : Ω' = univ ↔ Ω = univ := by
      refine ⟨fun h' => ?_, fun h0 => ?_⟩
      · by_contra h0
        have hinv_d : Differentiable ℂ (Function.invFunOn h Ω) := by
          rw [← differentiableOn_univ, ← h', ← hhbij.image_eq]
          exact DifferentiableOn.invFunOn hhd hΩo hhbij.injOn
        exact not_bijOn_univ_of_isSimplyConnected hinv_d hΩo hΩc h0
          (h' ▸ hhbij.symm hhbij.invOn_invFunOn.symm)
      · by_contra h'
        exact not_bijOn_univ_of_isSimplyConnected (differentiableOn_univ.mp (h0 ▸ hhd))
          hΩ'o hΩ'c h' (h0 ▸ hhbij)
    by_cases hΩ : Ω = univ
    · rw [huniv_iff.mpr hΩ, hΩ, riemannConformalRadius_univ, riemannConformalRadius_univ, mul_zero]
    · have hΩ' : Ω' ≠ univ := mt huniv_iff.mp hΩ
      obtain ⟨ψ, hψ⟩ := exists_isNormalizedRiemannMapOn hΩ'o hΩ'c hΩ' (hhbij.mapsTo hz₀)
      have hcomp_d : DifferentiableOn ℂ (ψ ∘ h) Ω := hψ.differentiableOn.comp hhd hhbij.mapsTo
      have hcomp_bij : BijOn (ψ ∘ h) Ω (ball (0 : ℂ) 1) := hψ.bijOn.comp hhbij
      have hcomp_0 : (ψ ∘ h) z₀ = 0 := by simp [hψ.map_base]
      have hh_at : HasDerivAt h (deriv h z₀) z₀ :=
        (hhd.differentiableAt (hΩo.mem_nhds hz₀)).hasDerivAt
      have hψ_at : HasDerivAt ψ (deriv ψ (h z₀)) (h z₀) :=
        (hψ.differentiableOn.differentiableAt (hΩ'o.mem_nhds (hhbij.mapsTo hz₀))).hasDerivAt
      have hh0 : ‖deriv h z₀‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn hhd hΩo hhbij.injOn hz₀)
      rw [riemannConformalRadius_eq_inv_norm_deriv_of_bijOn_ball hΩo hz₀ hcomp_d hcomp_bij hcomp_0,
        (hψ_at.comp z₀ hh_at).deriv, norm_mul, mul_inv,
        ← hψ.riemannConformalRadius_eq hΩ'o, mul_comm (riemannConformalRadius Ω' (h z₀)),
        ← mul_assoc, mul_inv_cancel₀ hh0, one_mul]
  · rw [riemannConformalRadius_eq_zero_of_not_isSimplyConnected hΩc,
      riemannConformalRadius_eq_zero_of_not_isSimplyConnected (mt hsc_iff.mp hΩc), mul_zero]

/-- **Conformal transformation law for injective holomorphic images.** -/
theorem riemannConformalRadius_image_of_injOn (hΩo : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hhd : DifferentiableOn ℂ h Ω) (hhinj : InjOn h Ω) :
    riemannConformalRadius (h '' Ω) (h z₀) = ‖deriv h z₀‖ * riemannConformalRadius Ω z₀ :=
  riemannConformalRadius_of_bijOn hΩo hz₀ hhd hhinj.bijOn_image

/-- **Affine covariance of conformal radius.** For *every* `a b : ℂ`, `Ω : Set ℂ`, and `z₀ : ℂ`,
the conformal radius of `(fun z => a * z + b) '' Ω` at `a * z₀ + b` equals
`‖a‖ * riemannConformalRadius Ω z₀`.
No hypothesis `a ≠ 0` or eligibility assumption on `(Ω, z₀)` is required: when `a = 0` the image is
either empty or `{b}`, neither of which is open and nonempty, so both sides vanish. -/
theorem riemannConformalRadius_image_affine (a b : ℂ) (Ω : Set ℂ) (z₀ : ℂ) :
    riemannConformalRadius ((fun z => a * z + b) '' Ω) (a * z₀ + b) =
      ‖a‖ * riemannConformalRadius Ω z₀ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, zero_add, norm_zero]
    rcases Ω.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [Nonempty.image_const hne, riemannConformalRadius_singleton]
  · set T : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
    have hT_eq : (T : ℂ → ℂ) = fun z => a * z + b := rfl
    have hT_pt : a * z₀ + b = T z₀ := rfl
    rw [← hT_eq, hT_pt]
    by_cases hΩo : IsOpen Ω
    · by_cases hz₀ : z₀ ∈ Ω
      · have hTd : DifferentiableOn ℂ T Ω := by
          rw [hT_eq]
          exact ((differentiable_id.const_mul a).add_const b).differentiableOn
        have hTderiv : deriv (T : ℂ → ℂ) z₀ = a := by
          rw [hT_eq]
          simpa only [mul_one] using (((hasDerivAt_id' z₀).const_mul a).add_const b).deriv
        rw [riemannConformalRadius_image_of_injOn hΩo hz₀ hTd T.injective.injOn, hTderiv]
      · have hTz₀ : T z₀ ∉ T '' Ω := mt T.injective.mem_set_image.mp hz₀
        rw [riemannConformalRadius_eq_zero_of_notMem hTz₀,
          riemannConformalRadius_eq_zero_of_notMem hz₀, mul_zero]
    · have hTo : ¬ IsOpen (T '' Ω) := by rwa [T.isOpen_image]
      rw [riemannConformalRadius_eq_zero_of_not_isOpen hTo,
        riemannConformalRadius_eq_zero_of_not_isOpen hΩo, mul_zero]

/-- Scaling covariance of conformal radius under left multiplication by `a : ℂ`. -/
@[simp]
theorem riemannConformalRadius_image_mul_left (a : ℂ) (Ω : Set ℂ) (z₀ : ℂ) :
    riemannConformalRadius ((a * ·) '' Ω) (a * z₀) = ‖a‖ * riemannConformalRadius Ω z₀ := by
  simpa using riemannConformalRadius_image_affine a 0 Ω z₀

/-- Translation invariance of conformal radius under `· + b`. -/
theorem riemannConformalRadius_image_add_right (b : ℂ) (Ω : Set ℂ) (z₀ : ℂ) :
    riemannConformalRadius ((· + b) '' Ω) (z₀ + b) = riemannConformalRadius Ω z₀ := by
  simpa using riemannConformalRadius_image_affine 1 b Ω z₀

/-- Translation invariance of conformal radius under `b + ·`. -/
theorem riemannConformalRadius_image_add_left (b : ℂ) (Ω : Set ℂ) (z₀ : ℂ) :
    riemannConformalRadius ((b + ·) '' Ω) (b + z₀) = riemannConformalRadius Ω z₀ := by
  simpa [add_comm b] using riemannConformalRadius_image_add_right b Ω z₀

/-- Translation invariance of conformal radius under `· - b`. -/
@[simp]
theorem riemannConformalRadius_image_sub_right (b : ℂ) (Ω : Set ℂ) (z₀ : ℂ) :
    riemannConformalRadius ((· - b) '' Ω) (z₀ - b) = riemannConformalRadius Ω z₀ := by
  simpa [sub_eq_add_neg] using riemannConformalRadius_image_add_right (-b) Ω z₀

/-- Negation invariance of conformal radius. -/
theorem riemannConformalRadius_image_neg (Ω : Set ℂ) (z₀ : ℂ) :
    riemannConformalRadius ((-·) '' Ω) (-z₀) = riemannConformalRadius Ω z₀ := by
  simpa using riemannConformalRadius_image_mul_left (-1) Ω z₀

/-! ### Monotone open exhaustion continuity -/

/-- A directed monotone union of open simply connected subsets of a topological space is itself
simply connected: any two points lie in a common member, and the compact trace of any loop in the
union lies in a single member where it is null-homotopic. -/
private theorem isSimplyConnected_iUnion_of_monotone {X ι : Type*} [TopologicalSpace X]
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {U : ι → Set X}
    (hmono : Monotone U) (hUo : ∀ i, IsOpen (U i)) (hUc : ∀ i, IsSimplyConnected (U i)) :
    IsSimplyConnected (⋃ i, U i) := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  refine ⟨?_, fun x p hp => ?_⟩
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨x₀, hx₀⟩ := (hUc i₀).nonempty
    refine ⟨x₀, mem_iUnion.mpr ⟨i₀, hx₀⟩, fun y hy => ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨k, hi₀k, hik⟩ := exists_ge_ge i₀ i
    exact ((hUc k).isPathConnected.joinedIn x₀ (hmono hi₀k hx₀) y (hmono hik hi)).mono
      (subset_iUnion U k)
  · obtain ⟨k, hk⟩ := (isCompact_range p.continuous).elim_directed_cover U hUo
      (range_subset_iff.mpr hp) hmono.directed_le
    obtain ⟨H, hH⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp (hUc k)).2 x p
      fun t => hk (mem_range_self t)
    exact ⟨H, fun t => subset_iUnion U k (hH t)⟩

/-- If the compact sub-disc image `Function.invFunOn f Ω '' closedBall 0 q` (`0 < q < 1`) for a
normalized Riemann map `f` of `(Ω, z₀)` is contained in a simply connected open proper set `V`,
then `q * riemannConformalRadius Ω z₀ ≤ riemannConformalRadius V z₀`. -/
private theorem mul_riemannConformalRadius_le_of_image_closedBall_subset {V : Set ℂ} {q : ℝ}
    (hf : IsNormalizedRiemannMapOn f Ω z₀) (hΩo : IsOpen Ω) (hVo : IsOpen V)
    (hVc : IsSimplyConnected V) (hV : V ≠ univ) (hq0 : 0 < q) (hq1 : q < 1)
    (hsub : Function.invFunOn f Ω '' closedBall (0 : ℂ) q ⊆ V) :
    q * riemannConformalRadius Ω z₀ ≤ riemannConformalRadius V z₀ := by
  set G : ℂ → ℂ := Function.invFunOn f Ω
  have hGd : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := by
    have h := DifferentiableOn.invFunOn hf.differentiableOn hΩo hf.injOn
    rwa [hf.image_eq] at h
  have hG0 : G 0 = z₀ := by rw [← hf.map_base]; exact hf.injOn.leftInvOn_invFunOn hf.base_mem
  have hsc_maps : MapsTo (fun w : ℂ => (q : ℂ) * w) (ball (0 : ℂ) 1) (closedBall (0 : ℂ) q) := by
    intro w hw
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    exact mul_le_of_le_one_right hq0.le (mem_ball_zero_iff.mp hw).le
  have hcomp_d : DifferentiableOn ℂ (fun w => G ((q : ℂ) * w)) (ball (0 : ℂ) 1) :=
    hGd.comp (differentiable_id.const_mul (q : ℂ)).differentiableOn
      (hsc_maps.mono_right (closedBall_subset_ball hq1))
  have hcomp_m : MapsTo (fun w => G ((q : ℂ) * w)) (ball (0 : ℂ) 1) V :=
    fun w hw => hsub (mem_image_of_mem G (hsc_maps hw))
  have hle := norm_deriv_le_riemannConformalRadius_of_mapsTo_ball (z₀ := z₀) hVo hVc hV
    hcomp_d hcomp_m (by simp [hG0])
  have hcomp_deriv : deriv (fun w : ℂ => G ((q : ℂ) * w)) 0 =
      (riemannConformalRadius Ω z₀ : ℂ) * (q : ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => (q : ℂ) * w) (q : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (q : ℂ)
    have h2 : HasDerivAt G (riemannConformalRadius Ω z₀) ((fun w : ℂ => (q : ℂ) * w) 0) := by
      simpa using hf.hasDerivAt_invFunOn_zero hΩo
    exact (h2.comp 0 h1).deriv
  rw [hcomp_deriv, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (riemannConformalRadius_nonneg Ω z₀), abs_of_pos hq0,
    mul_comm] at hle
  exact hle

/-- **Exhaustion continuity of conformal radius.** Let `U : ι → Set ℂ` be a monotone family of open
simply connected domains indexed by a nonempty directed preorder `ι`. If the union `⋃ i, U i` is a
proper subset of `ℂ`, then `riemannConformalRadius (U i) z₀` tends to
`riemannConformalRadius (⋃ i, U i) z₀` along `atTop`: monotonicity supplies the upper bound, while
placing the compact inverse-Riemann image of `closedBall 0 q` (`0 < q < 1`) inside a single `U k`
gives the lower bound `q * riemannConformalRadius (⋃ i, U i) z₀`. -/
theorem tendsto_riemannConformalRadius_iUnion {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {U : ι → Set ℂ} (hmono : Monotone U) (hUo : ∀ i, IsOpen (U i))
    (hUc : ∀ i, IsSimplyConnected (U i)) (hU : ⋃ i, U i ≠ univ) (z₀ : ℂ) :
    Tendsto (fun i => riemannConformalRadius (U i) z₀) atTop
      (𝓝 (riemannConformalRadius (⋃ i, U i) z₀)) := by
  set Ω : Set ℂ := ⋃ i, U i
  by_cases hz₀ : z₀ ∈ Ω
  · have hΩo : IsOpen Ω := isOpen_iUnion hUo
    have hΩc : IsSimplyConnected Ω := isSimplyConnected_iUnion_of_monotone hmono hUo hUc
    have hRpos : 0 < riemannConformalRadius Ω z₀ := riemannConformalRadius_pos hΩo hΩc hU hz₀
    obtain ⟨φ, hφ⟩ := exists_isNormalizedRiemannMapOn hΩo hΩc hU hz₀
    have hGd : DifferentiableOn ℂ (Function.invFunOn φ Ω) (ball (0 : ℂ) 1) := by
      have h := DifferentiableOn.invFunOn hφ.differentiableOn hΩo hφ.injOn
      rwa [hφ.image_eq] at h
    refine tendsto_order.mpr ⟨fun r hr => ?_, fun r hr => Filter.Eventually.of_forall fun i =>
      (riemannConformalRadius_mono (hUo i) (hUc i) hΩo hΩc hU (subset_iUnion U i)).trans_lt hr⟩
    obtain ⟨q, hq_gt, hq1⟩ :=
      exists_between (max_lt zero_lt_one ((div_lt_one hRpos).mpr hr))
    have hq0 : 0 < q := (le_max_left _ _).trans_lt hq_gt
    have hrq : r < q * riemannConformalRadius Ω z₀ :=
      (div_lt_iff₀ hRpos).mp ((le_max_right _ _).trans_lt hq_gt)
    have hsub_ball : closedBall (0 : ℂ) q ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hq1
    have hKcomp : IsCompact (Function.invFunOn φ Ω '' closedBall (0 : ℂ) q) :=
      (isCompact_closedBall (0 : ℂ) q).image_of_continuousOn (hGd.continuousOn.mono hsub_ball)
    obtain ⟨k, hk⟩ := hKcomp.elim_directed_cover U hUo
      ((hφ.surjOn.mapsTo_invFunOn.mono_left hsub_ball).image_subset) hmono.directed_le
    filter_upwards [Filter.eventually_ge_atTop k] with i hi
    have hUi_ne : U i ≠ univ := fun h => hU (univ_subset_iff.mp (h ▸ subset_iUnion U i))
    exact hrq.trans_le (mul_riemannConformalRadius_le_of_image_closedBall_subset hφ hΩo (hUo i)
      (hUc i) hUi_ne hq0 hq1 (hk.trans (hmono hi)))
  · have hzero : ∀ i, riemannConformalRadius (U i) z₀ = 0 := fun i =>
      riemannConformalRadius_eq_zero_of_notMem fun h => hz₀ (mem_iUnion.mpr ⟨i, h⟩)
    simp_rw [hzero, riemannConformalRadius_eq_zero_of_notMem hz₀]
    exact tendsto_const_nhds

/-- Named-target form of `tendsto_riemannConformalRadius_iUnion` when `⋃ i, U i = Ω`. -/
theorem tendsto_riemannConformalRadius_of_iUnion_eq {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] {U : ι → Set ℂ} (hmono : Monotone U) (hUo : ∀ i, IsOpen (U i))
    (hUc : ∀ i, IsSimplyConnected (U i)) (hUΩ : ⋃ i, U i = Ω) (hΩ : Ω ≠ univ) (z₀ : ℂ) :
    Tendsto (fun i => riemannConformalRadius (U i) z₀) atTop
      (𝓝 (riemannConformalRadius Ω z₀)) := by
  subst hUΩ
  exact tendsto_riemannConformalRadius_iUnion hmono hUo hUc hΩ z₀

/-! ### Closed-form evaluations on discs, half-planes, and the slit plane -/

/-- **Conformal radius of the open unit disc.** At any point `z₀ ∈ ball 0 1`, the conformal radius
of `ball 0 1` is the Poincaré defect `1 - ‖z₀‖ ^ 2` (in particular, it is `1` only at the
origin). -/
theorem riemannConformalRadius_ball_zero_one (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    riemannConformalRadius (ball (0 : ℂ) 1) z₀ = 1 - ‖z₀‖ ^ 2 := by
  have h := riemannConformalRadius_eq_one_sub_norm_sq_div_norm_deriv_of_bijOn_ball isOpen_ball hz₀
    differentiable_id.differentiableOn (bijOn_id (ball (0 : ℂ) 1))
  simpa using h

/-- At the origin, the open unit disc has conformal radius `1`. -/
@[simp]
theorem riemannConformalRadius_ball_zero_one_zero :
    riemannConformalRadius (ball (0 : ℂ) 1) 0 = 1 := by
  simpa using riemannConformalRadius_ball_zero_one (mem_ball_self one_pos)

/-- **Conformal radius of an arbitrary Euclidean disc.** At any point `z₀ ∈ ball b R`, the conformal
radius of `ball b R` is `(R ^ 2 - ‖z₀ - b‖ ^ 2) / R`. -/
theorem riemannConformalRadius_ball {b : ℂ} {R : ℝ} (hz₀ : z₀ ∈ ball b R) :
    riemannConformalRadius (ball b R) z₀ = (R ^ 2 - ‖z₀ - b‖ ^ 2) / R := by
  have hR : 0 < R := pos_of_mem_ball hz₀
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have himg : (fun z : ℂ => (R : ℂ) * z + b) '' ball (0 : ℂ) 1 = ball b R := by
    ext w
    simp only [mem_image, mem_ball_iff_norm, sub_zero]
    refine ⟨?_, fun hw => ⟨(w - b) / (R : ℂ), ?_, by field_simp; ring⟩⟩
    · rintro ⟨z, hz, rfl⟩
      rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      exact (mul_lt_iff_lt_one_right hR).mpr hz
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      exact (div_lt_one hR).mpr hw
  have hpt : (R : ℂ) * ((z₀ - b) / (R : ℂ)) + b = z₀ := by field_simp; ring
  have hw₀ : (z₀ - b) / (R : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_lt_one hR).mpr (mem_ball_iff_norm.mp hz₀)
  conv_lhs => rw [← himg, ← hpt]
  rw [riemannConformalRadius_image_affine, riemannConformalRadius_ball_zero_one hw₀,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  field_simp

/-- At the centre `b` of `ball b R` (`0 ≤ R`), the conformal radius is `R` (including the degenerate
radius `R = 0`, where `ball b 0 = ∅`). -/
theorem riemannConformalRadius_ball_self (b : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    riemannConformalRadius (ball b R) b = R := by
  rcases hR.eq_or_lt with rfl | hRpos
  · simp
  · rw [riemannConformalRadius_ball (mem_ball_self hRpos), sub_self, norm_zero]
    field_simp
    ring

/-- **Inner-disc lower bound.** If `ball z₀ R ⊆ Ω` for a simply connected open proper domain `Ω`,
then `R ≤ riemannConformalRadius Ω z₀` (for every `R : ℝ`). -/
theorem le_riemannConformalRadius_of_ball_subset {R : ℝ} (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) (hsub : ball z₀ R ⊆ Ω) :
    R ≤ riemannConformalRadius Ω z₀ := by
  rcases le_or_gt R 0 with hR | hR
  · exact hR.trans (riemannConformalRadius_nonneg Ω z₀)
  · have : ContractibleSpace (ball z₀ R) := contractibleSpace_ball hR
    rw [← riemannConformalRadius_ball_self z₀ hR.le]
    exact riemannConformalRadius_mono isOpen_ball
      (inferInstance : SimplyConnectedSpace (ball z₀ R)) hΩo hΩc hΩ hsub

/-- The right-half-plane Cayley transform `z ↦ (z - 1) / (z + 1)` carries `{z | 0 < z.re}`
bijectively onto `ball 0 1`: it is the upper-half-plane Cayley transform `(w - I) / (w + I)`
precomposed with multiplication by `I`. -/
private theorem bijOn_sub_one_div_add_one_re_pos :
    BijOn (fun z : ℂ => (z - 1) / (z + 1)) {z : ℂ | 0 < z.re} (ball (0 : ℂ) 1) := by
  have hrot : BijOn (I * ·) {z : ℂ | 0 < z.re} UpperHalfPlane.upperHalfPlaneSet := by
    refine InvOn.bijOn (f' := (-I * ·))
      ⟨fun z _ => by dsimp only; rw [← mul_assoc]; simp,
        fun w _ => by dsimp only; rw [← mul_assoc]; simp⟩
      (fun z hz => ?_) (fun w hw => ?_)
    · simpa [UpperHalfPlane.upperHalfPlaneSet, mul_im] using hz
    · simpa [UpperHalfPlane.upperHalfPlaneSet, mul_re] using hw
  refine (bijOn_sub_I_div_add_I_upperHalfPlaneSet.comp hrot).congr fun z _ => ?_
  have hnum : I * z - I = I * (z - 1) := by ring
  have hden : I * z + I = I * (z + 1) := by ring
  simp only [Function.comp_apply, hnum, hden, mul_div_mul_left _ _ I_ne_zero]

/-- At `1`, the open right half-plane `{z | 0 < z.re}` has conformal radius `2`, witnessed by the
Cayley map `z ↦ (z - 1) / (z + 1)` with derivative `1 / 2` at `1`. -/
@[simp]
theorem riemannConformalRadius_re_pos_one :
    riemannConformalRadius {z : ℂ | 0 < z.re} 1 = 2 := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z - 1) / (z + 1)) {z : ℂ | 0 < z.re} :=
    (differentiableOn_id.sub (differentiableOn_const 1)).div
      (differentiableOn_id.add (differentiableOn_const 1)) fun z hz h0 => by
        have := congrArg Complex.re h0
        simp only [add_re, one_re, zero_re] at this
        linarith [hz.out]
  have hderiv : HasDerivAt (fun z : ℂ => (z - 1) / (z + 1)) (1 / 2 : ℂ) 1 := by
    have h20 : (1 : ℂ) + 1 ≠ 0 := by norm_num
    refine (((hasDerivAt_id (1 : ℂ)).sub_const 1).div
      ((hasDerivAt_id (1 : ℂ)).add_const 1) h20).congr_deriv ?_
    norm_num
  rw [riemannConformalRadius_eq_inv_norm_deriv_of_bijOn_ball hopen h1 hd
    bijOn_sub_one_div_add_one_re_pos (by simp), hderiv.deriv]
  norm_num

/-- **Conformal radius of the open right half-plane.** For every `z₀` with `0 < z₀.re`,
`riemannConformalRadius {z | 0 < z.re} z₀ = 2 * z₀.re`, obtained from the base value `2` at `1`
via the half-plane automorphism `z ↦ z₀.re * z + z₀.im * I`. -/
theorem riemannConformalRadius_re_pos (hz₀ : 0 < z₀.re) :
    riemannConformalRadius {z : ℂ | 0 < z.re} z₀ = 2 * z₀.re := by
  have himg : (fun z : ℂ => (z₀.re : ℂ) * z + (z₀.im : ℂ) * I) '' {z : ℂ | 0 < z.re} =
      {z : ℂ | 0 < z.re} := by
    ext w
    simp only [mem_image, mem_ofPred_eq]
    refine ⟨?_, fun hw => ⟨(w - (z₀.im : ℂ) * I) / (z₀.re : ℂ), ?_, ?_⟩⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using mul_pos hz₀ hz
    · have hre : ((w - (z₀.im : ℂ) * I) / (z₀.re : ℂ)).re = w.re / z₀.re := by
        rw [div_ofReal_re]
        simp
      rw [hre]
      exact div_pos hw hz₀
    · have hne : (z₀.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz₀.ne'
      field_simp
      ring
  have hpt : (z₀.re : ℂ) * 1 + (z₀.im : ℂ) * I = z₀ := by simp
  conv_lhs =>
    rw [← hpt]
    rw [← himg]
  rw [riemannConformalRadius_image_affine, riemannConformalRadius_re_pos_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz₀, mul_comm]

/-- **Conformal radius of the open upper half-plane.** At any
`z₀ ∈ UpperHalfPlane.upperHalfPlaneSet` (`0 < z₀.im`), the conformal radius is `2 * z₀.im`. -/
theorem riemannConformalRadius_upperHalfPlaneSet (hz₀ : z₀ ∈ UpperHalfPlane.upperHalfPlaneSet) :
    riemannConformalRadius UpperHalfPlane.upperHalfPlaneSet z₀ = 2 * z₀.im := by
  have him : 0 < z₀.im := hz₀
  have himg : (I * ·) '' {z : ℂ | 0 < z.re} = UpperHalfPlane.upperHalfPlaneSet := by
    ext w
    simp only [mem_image, mem_ofPred_eq, UpperHalfPlane.upperHalfPlaneSet]
    refine ⟨?_, fun hw => ⟨-I * w, by simpa [mul_re] using hw, by rw [← mul_assoc]; simp⟩⟩
    rintro ⟨z, hz, rfl⟩
    simpa [mul_im] using hz
  have hpt : I * (-I * z₀) = z₀ := by rw [← mul_assoc]; simp
  have hre : 0 < (-I * z₀).re := by simpa [mul_re] using him
  conv_lhs => rw [← himg, ← hpt]
  rw [riemannConformalRadius_image_mul_left, norm_I, one_mul,
    riemannConformalRadius_re_pos hre]
  simp [mul_re]

/-- At `i`, the open upper half-plane has conformal radius `2`. -/
@[simp]
theorem riemannConformalRadius_upperHalfPlaneSet_I :
    riemannConformalRadius UpperHalfPlane.upperHalfPlaneSet I = 2 := by
  have hI : I ∈ UpperHalfPlane.upperHalfPlaneSet := by simp [UpperHalfPlane.upperHalfPlaneSet]
  simpa using riemannConformalRadius_upperHalfPlaneSet hI

/-- Squaring maps the open right half-plane `{w | 0 < w.re}` bijectively onto `Complex.slitPlane`,
inverted by the principal square root `Complex.sqrt`. -/
private theorem bijOn_sq_re_pos_slitPlane :
    BijOn (· ^ 2 : ℂ → ℂ) {w : ℂ | 0 < w.re} Complex.slitPlane := by
  refine InvOn.bijOn ⟨fun w hw => ?_, fun z _ => Complex.sq_sqrt z⟩
    (fun w hw => by rw [sq]; exact mul_mem_slitPlane_of_re_pos hw hw)
    (fun z hz => (Complex.sqrt_re_pos_iff z).mpr hz)
  have hw2 : w ^ 2 ∈ Complex.slitPlane := by rw [sq]; exact mul_mem_slitPlane_of_re_pos hw hw
  have hsq : Complex.sqrt (w ^ 2) ^ 2 = w ^ 2 := Complex.sq_sqrt (w ^ 2)
  have hmul : (Complex.sqrt (w ^ 2) - w) * (Complex.sqrt (w ^ 2) + w) = 0 := by
    linear_combination hsq
  have hsum : Complex.sqrt (w ^ 2) + w ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [add_re, zero_re] at hre
    linarith [(Complex.sqrt_re_pos_iff (w ^ 2)).mpr hw2, hw.out]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hsum)

/-- **Conformal radius of the slit plane `ℂ \ (-∞, 0]`.** At any `z₀ ∈ Complex.slitPlane`, the
conformal radius is `4 * ‖Complex.sqrt z₀‖ * (Complex.sqrt z₀).re`: the squaring biholomorphism
`w ↦ w ^ 2` carries `{w | 0 < w.re}` onto `Complex.slitPlane` with derivative `2 * w` at
`w = Complex.sqrt z₀` (equivalently, `(√z - 1) / (√z + 1)` maps `Complex.slitPlane` onto
`ball 0 1`). -/
theorem riemannConformalRadius_slitPlane (hz₀ : z₀ ∈ Complex.slitPlane) :
    riemannConformalRadius Complex.slitPlane z₀ =
      4 * ‖Complex.sqrt z₀‖ * (Complex.sqrt z₀).re := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hw₀ : Complex.sqrt z₀ ∈ {w : ℂ | 0 < w.re} := (Complex.sqrt_re_pos_iff z₀).mpr hz₀
  have hd : DifferentiableOn ℂ (· ^ 2 : ℂ → ℂ) {w : ℂ | 0 < w.re} :=
    (differentiable_id.pow 2).differentiableOn
  have hderiv : deriv (· ^ 2 : ℂ → ℂ) (Complex.sqrt z₀) = 2 * Complex.sqrt z₀ := by
    rw [(hasDerivAt_pow 2 (Complex.sqrt z₀)).deriv]
    ring
  have h := riemannConformalRadius_of_bijOn hopen hw₀ hd bijOn_sq_re_pos_slitPlane
  rw [Complex.sq_sqrt z₀, hderiv, norm_mul, norm_ofNat, riemannConformalRadius_re_pos hw₀] at h
  linarith

/-- At a positive real point `x > 0`, the slit plane `Complex.slitPlane` has conformal radius
`4 * x`. -/
theorem riemannConformalRadius_slitPlane_ofReal {x : ℝ} (hx : 0 < x) :
    riemannConformalRadius Complex.slitPlane (x : ℂ) = 4 * x := by
  have hx_slit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have hsqrt : Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
    simpa using Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr hx.le)
  rw [riemannConformalRadius_slitPlane hx_slit, hsqrt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg x), Complex.ofReal_re, mul_assoc, Real.mul_self_sqrt hx.le]

/-- At `1`, the slit plane `Complex.slitPlane` (`ℂ \ (-∞, 0]`) has conformal radius `4`. -/
@[simp]
theorem riemannConformalRadius_slitPlane_one :
    riemannConformalRadius Complex.slitPlane 1 = 4 := by
  simpa using riemannConformalRadius_slitPlane_ofReal one_pos

end TauCeti
