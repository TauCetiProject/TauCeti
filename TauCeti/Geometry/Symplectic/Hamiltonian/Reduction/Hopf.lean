/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Manifold.Instances.Sphere.Hopf
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
import TauCeti.Analysis.InnerProductSpace.Complex
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Symplectic.Manifold.Sphere.Area

/-!
# Hopf reduction: the reduced spaces of `ℂ²` by the diagonal circle

Give `ℂ²` its Kähler form `Ω(v, w) = Im ⟪v, w⟫_ℂ`, which in the coordinates `z_j = q_j + i p_j` is
`dq₀ ∧ dp₀ + dq₁ ∧ dp₁`. The statements below take any symplectic form `Ω` with this formula, such
as `(AlmostComplexStructure.ofComplexModule ℂ²).symplecticForm`, `⟪i v, w⟫_ℝ`. The diagonal circle
action `z ↦ e^(-iθ) z` is Hamiltonian with moment map `μ(z) = ‖z‖² / 2`
(`TauCeti.hamiltonianVectorField_half_norm_sq_eq_neg_I_smul`). This file computes its
symplectic reductions. For `c > 0` the level `μ⁻¹(c)` is the sphere of radius `√(2c)`, which
`z ↦ √(2c) z` parametrizes by the unit sphere `S³`
(`TauCeti.range_sqrt_two_mul_smul_coe_sphere_eq_setOf_half_norm_sq_eq`), and the quotient of the
level by the circle is the two-sphere, through the Hopf map `h : S³ → S²` (`TauCeti.hopfMap`),
whose fibres are the circle orbits. Here `h` is shown to be a submersion
(`TauCeti.mfderiv_hopfMap_surjective`, `TauCeti.isSubmersion_hopfMap`), whose vertical tangent
vectors at `z` are the real multiples of `i z`, the velocity of the circle orbit through `z`
(`TauCeti.mfderiv_hopfMap_eq_zero_iff`). The reduced symplectic form is computed by the identity

`h^* ((c / 2) σ) = (z ↦ √(2c) z)^* Ω`

on `S³` (`TauCeti.mpullback_sqrt_two_mul_smul_coe_sphere_constSmooth_eq_mpullback_hopfMap`), where
`σ_x(v, w) = x ⬝ (v × w)` is the area form of the unit sphere `S²` (`TauCeti.sphereAreaForm`).
Since `h` is a surjective submersion, `(c / 2) σ` is the only form on `S²` with this property
(`TauCeti.mpullback_hopfMap_eq_iff`): it is the reduced form of the level `c`. As `S²` has area
`4π`, the reduced space has symplectic area `2πc`
(`TauCeti.liouvilleMeasure_univ_of_mpullback_hopfMap_eq`), so the area grows by `2π δ` when the
level grows by `δ`, the Duistermaat–Heckman variation for the Hopf circle bundle.

These statements also hold at `c = 0`, but there they are degenerate: the level is the origin,
which is not a regular value, the reduced space is a point rather than `S²`, and both sides of each
identity vanish.

The pullback identity comes from `h(z) ⬝ (dh v × dh w) = 4 Im ⟪v, w⟫_ℂ` for tangent vectors `v, w`
of `S³` (`TauCeti.dotProduct_cross_mvfderiv_coe_mfderiv_hopfMap`). The orientation matters: the
conjugate map `z ↦ (2 Re (z₀ conj z₁), 2 Im (z₀ conj z₁), |z₀|² - |z₁|²)` differs from `h` by a
reflection of `ℝ³`, and reduces `Ω` to `-(c / 2) σ`.

## Main results

* `TauCeti.mfderiv_hopfMap_surjective`, `TauCeti.isSubmersion_hopfMap`: the Hopf map is a
  submersion.
* `TauCeti.mfderiv_hopfMap_eq_zero_iff`: its vertical tangent vectors at `z` are the real multiples
  of `i z`.
* `TauCeti.eval₂_sphereAreaForm_mfderiv_hopfMap`: it pulls the area form of `S²` back to
  `4 Im ⟪·, ·⟫_ℂ`.
* `TauCeti.range_sqrt_two_mul_smul_coe_sphere_eq_setOf_half_norm_sq_eq`: `z ↦ √(2c) z`
  parametrizes the level `‖x‖² / 2 = c`.
* `TauCeti.hamiltonianVectorField_half_norm_sq_eq_neg_I_smul`: `‖x‖² / 2` is the moment map of the
  diagonal circle action.
* `TauCeti.mpullback_sqrt_two_mul_smul_coe_sphere_constSmooth_eq_mpullback_hopfMap`: the reduced
  form of the level `c` is `(c / 2) σ`.
* `TauCeti.mpullback_hopfMap_eq_iff`: it is the unique form with this property.
* `TauCeti.liouvilleMeasure_univ_of_mpullback_hopfMap_eq`: the reduced space has area `2πc`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (symplectic reduction, with the reduction of `ℂⁿ` by the diagonal
  circle to `ℂℙⁿ⁻¹` among its examples) and Section 30.3 (the variation of the reduced
  symplectic volume).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 5.4 (symplectic reduction).
-/

public section

noncomputable section

open Metric Module Matrix WithLp Complex Real
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℂ²" => EuclideanSpace ℂ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S³" => sphere (0 : ℂ²) 1
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### The Hopf map is a submersion -/

/-- **The Hopf map pulls the area form of `S²` back to four times `Im ⟪·, ·⟫_ℂ`.** For tangent
vectors `v, w` of `S³` at `z`, `σ(dh v, dh w) = 4 Im ⟪v, w⟫_ℂ`. -/
theorem eval₂_sphereAreaForm_mfderiv_hopfMap (z : S³) (v w : TangentSpace (𝓡 3) z) :
    SmoothBundleForm.eval₂ sphereAreaForm (hopfMap z) (mfderiv (𝓡 3) (𝓡 2) hopfMap z v)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap z w) =
      4 * (⟪mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z w⟫_ℂ).im := by
  rw [eval₂_sphereAreaForm, dotProduct_cross_mvfderiv_coe_mfderiv_hopfMap]

/-- **The Hopf map is a submersion**: its differential at every point of `S³` is onto the tangent
plane of `S²`. -/
theorem mfderiv_hopfMap_surjective (z : S³) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2) hopfMap z) := by
  -- The vectors `u = (-conj z₁, conj z₀)` and `i u` are tangent to `S³`, and the area form pairs
  -- their images to `4 ‖u‖² = 4`, so the images span the tangent plane of `S²`.
  set u : ℂ² := toLp 2 ![-conj ((z : ℂ²) 1), conj ((z : ℂ²) 0)]
  have hu₀ : ⟪(z : ℂ²), u⟫_ℂ = 0 := by
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hu : ⟪(z : ℂ²), u⟫_ℝ = 0 := by
    rw [EuclideanSpace.real_inner_eq_re_inner, hu₀, zero_re]
  have hIu : ⟪(z : ℂ²), I • u⟫_ℝ = 0 := by
    rw [EuclideanSpace.real_inner_eq_re_inner, inner_smul_right, hu₀, mul_zero, zero_re]
  have hnorm : ‖u‖ ^ 2 = 1 := by
    rw [← one_pow 2, ← norm_eq_of_mem_sphere z, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    simp [u, Fin.sum_univ_two, add_comm]
  obtain ⟨a, ha⟩ := exists_mvfderiv_coe_sphere_eq (n := 3) z hu
  obtain ⟨b, hb⟩ := exists_mvfderiv_coe_sphere_eq (n := 3) z hIu
  have hI : (⟪u, I • u⟫_ℂ).im = 1 := by
    rw [inner_smul_right, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add, ← hnorm]
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hab : sphereAreaForm.bilinFormAt (hopfMap z)
      ((1 / 4 : ℝ) • mfderiv (𝓡 3) (𝓡 2) hopfMap z a) (mfderiv (𝓡 3) (𝓡 2) hopfMap z b) = 1 := by
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_smul_left,
      eval₂_sphereAreaForm_mfderiv_hopfMap, ha, hb, hI, smul_eq_mul]
    norm_num
  have hspan := ((SmoothForm.isAlt_bilinFormAt _ _).linearIndependent_pair_of_apply_eq_one
    hab).span_eq_top_of_card_eq_finrank (by simp)
  refine LinearMap.range_eq_top.1 (eq_top_iff.2 (hspan ▸ Submodule.span_le.2 ?_))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨b, rfl⟩
  · exact ⟨(1 / 4 : ℝ) • a, map_smul _ _ _⟩

/-- The Hopf map is a submersion. -/
theorem isSubmersion_hopfMap : Manifold.IsSubmersion (𝓡 3) (𝓡 2) ∞ hopfMap :=
  (contMDiff_hopfMap.isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    mfderiv_hopfMap_surjective).isSubmersion

/-- **The vertical tangent vectors of the Hopf map.** A tangent vector `v` of `S³` at `z` lies in
the kernel of the differential of the Hopf map exactly when, read in `ℂ²`, it is a real multiple of
`i z`, the velocity of the circle orbit `t ↦ e^(it) z` through `z`. -/
theorem mfderiv_hopfMap_eq_zero_iff (z : S³) (v : TangentSpace (𝓡 3) z) :
    mfderiv (𝓡 3) (𝓡 2) hopfMap z v = 0 ↔
      ∃ t : ℝ, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v = t • (I • (z : ℂ²)) := by
  constructor
  · intro h
    -- `i v` is orthogonal to every tangent vector at `z`, so it lies on the normal line `ℝ z`.
    have horth : I • mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v ∈ ((ℝ ∙ (z : ℂ²))ᗮ)ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := 3) z]
      rintro _ ⟨w, rfl⟩
      have hw := eval₂_sphereAreaForm_mfderiv_hopfMap z v w
      rw [h, SmoothBundleForm.eval₂_zero_left, im_inner_eq_real_inner_I_smul,
        real_inner_comm] at hw
      exact (mul_eq_zero.1 hw.symm).resolve_left four_ne_zero
    rw [Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton] at horth
    obtain ⟨s, hs⟩ := horth
    exact ⟨-s, by linear_combination (norm := (match_scalars <;> simp [mul_comm])) I • hs⟩
  · -- The area form pairs `dh v` with every `dh w` to `4 Im ⟪t i z, w⟫_ℂ = -4t ⟪z, w⟫_ℝ = 0`.
    rintro ⟨t, ht⟩
    refine (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1
      isSymplectic_sphereAreaForm.isNondegenerate) (hopfMap z) _ fun u ↦ ?_
    obtain ⟨w, rfl⟩ := mfderiv_hopfMap_surjective z u
    have hn : I • t • I • (z : ℂ²) = (-t) • (z : ℂ²) := by
      simp [smul_comm I t, smul_smul]
    rw [eval₂_sphereAreaForm_mfderiv_hopfMap, ht, im_inner_eq_real_inner_I_smul, hn,
      real_inner_smul_left, inner_coe_mvfderiv_subtypeVal_sphere]
    simp

/-! ### The reduced space of a level -/

/-- **`‖x‖² / 2` generates the reversed diagonal rotation.** For a symplectic form `Ω` on
`EuclideanSpace ℂ ι` with `Ω(v, w) = Im ⟪v, w⟫_ℂ`, and the convention `ι_(X_H) Ω = dH`, the
Hamiltonian vector field of `‖x‖² / 2` is `-i x`, the generator of the circle action
`x ↦ e^(-iθ) x`. So `‖x‖² / 2` is the moment map of that action. -/
theorem hamiltonianVectorField_half_norm_sq_eq_neg_I_smul {ι : Type*} [Fintype ι]
    {Ω : SymplecticForm (EuclideanSpace ℂ ι)} (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im)
    (x : EuclideanSpace ℂ ι) :
    Ω.hamiltonianVectorField (fun y ↦ ‖y‖ ^ 2 / 2) x = -(I • x) := by
  have hg : ∀ v w, Ω v (AlmostComplexStructure.ofComplexModule _ w) = ⟪v, w⟫_ℝ := fun v w ↦ by
    rw [AlmostComplexStructure.ofComplexModule_apply, hΩ, inner_smul_right,
      EuclideanSpace.real_inner_eq_re_inner]
    simp
  have hQ : (fun y : EuclideanSpace ℂ ι ↦ ‖y‖ ^ 2 / 2) = fun y ↦ 1 / 2 * ‖y‖ ^ 2 := by
    funext y
    ring
  rw [hQ, Ω.hamiltonianVectorField_div_two_mul_norm_sq hg 1]
  simp

/-- The parametrization `z ↦ √(2c) z` of the level `‖x‖² / 2 = c` of `ℂ²` by `S³` is smooth. -/
theorem contMDiff_sqrt_two_mul_smul_coe_sphere (c : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℂ²) ∞ (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) :=
  (√(2 * c) • ContinuousLinearMap.id ℝ ℂ²).contMDiff.comp contMDiff_coe_sphere

/-- For `c ≥ 0`, the map `z ↦ √(2c) z` carries `S³` onto the level `‖x‖² / 2 = c` of `ℂ²`. -/
theorem range_sqrt_two_mul_smul_coe_sphere_eq_setOf_half_norm_sq_eq {c : ℝ} (hc : 0 ≤ c) :
    Set.range (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) = {x : ℂ² | ‖x‖ ^ 2 / 2 = c} := by
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, rfl⟩
    rw [norm_smul, norm_eq_of_mem_sphere z, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity)]
    ring
  · intro hx
    rcases eq_or_lt_of_le hc with rfl | hc
    · refine ⟨⟨EuclideanSpace.single 0 1, by simp⟩, ?_⟩
      have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
      simp [norm_eq_zero.1 this]
    · have hr : 0 < √(2 * c) := Real.sqrt_pos.2 (by positivity)
      have hn : ‖x‖ = √(2 * c) := by
        rw [← Real.sqrt_sq (norm_nonneg x)]
        congr 1
        linarith
      refine ⟨⟨(√(2 * c))⁻¹ • x, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), hn,
          inv_mul_cancel₀ hr.ne']
      · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- **Hopf reduction.** For `c ≥ 0`, the Kähler form `Ω = Im ⟪v, w⟫_ℂ` of `ℂ²` restricted to the
level `‖x‖² / 2 = c`, parametrized by `z ↦ √(2c) z`, is the pullback along the Hopf map of `c / 2`
times the area form `σ` of `S²`. In other words, for `c > 0` the level data
`(z ↦ √(2c) z, hopfMap)` of the reversed diagonal circle action reduce the Kähler form to
`(c / 2) σ`. At `c = 0` the level is the origin and both sides vanish. -/
theorem mpullback_sqrt_two_mul_smul_coe_sphere_constSmooth_eq_mpullback_hopfMap
    {Ω : SymplecticForm ℂ²} (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) {c : ℝ} (hc : 0 ≤ c) :
    SmoothForm.mpullback (fun z : S³ ↦ √(2 * c) • (z : ℂ²))
        (contMDiff_sqrt_two_mul_smul_coe_sphere c) Ω.constSmooth =
      SmoothForm.mpullback hopfMap contMDiff_hopfMap ((c / 2) • sphereAreaForm) := by
  refine Subtype.ext (funext fun z ↦ ?_)
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  have hd (u : TangentSpace (𝓡 3) z) :
      mvfderiv (𝓡 3) (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) z u =
        √(2 * c) • mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z u :=
    (√(2 * c) • ContinuousLinearMap.id ℝ ℂ²).mvfderiv_comp_apply
      ((contMDiff_coe_sphere (n := 3) (m := 1) z).mdifferentiableAt one_ne_zero) u
  rw [hv, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback]
  refine (SymplecticForm.eval₂_constSmooth_mfderiv_eq Ω
    (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) z _ _).trans ?_
  have hσ : SmoothBundleForm.eval₂ ((c / 2) • sphereAreaForm) (hopfMap z)
      (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 0)) (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 1)) =
      c / 2 * SmoothBundleForm.eval₂ sphereAreaForm (hopfMap z)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 0)) (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 1)) := by
    simp [SmoothBundleForm.eval₂_apply]
  have hsmul (a b : ℂ²) : Ω (√(2 * c) • a) (√(2 * c) • b) =
      √(2 * c) * √(2 * c) * (⟪a, b⟫_ℂ).im := by
    simp [hΩ, mul_assoc]
  rw [hd, hd, hσ, eval₂_sphereAreaForm_mfderiv_hopfMap, hsmul, Real.mul_self_sqrt (by positivity)]
  ring

/-- **The reduced form of Hopf reduction is `(c / 2) σ`.** For `c ≥ 0`, a two-form `η` on `S²`
pulls back along the Hopf map to the restriction of the Kähler form `Ω` of `ℂ²` to the level
`‖x‖² / 2 = c` exactly when `η` is `c / 2` times the area form. For `c > 0` this is the reduced
form; at `c = 0` the level is the origin, `S²` is not its quotient, and `η = 0`. -/
theorem mpullback_hopfMap_eq_iff {Ω : SymplecticForm ℂ²} (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im)
    {c : ℝ} (hc : 0 ≤ c) {η : SmoothTwoForm (𝓡 2) S²} :
    SmoothForm.mpullback hopfMap contMDiff_hopfMap η =
        SmoothForm.mpullback (fun z : S³ ↦ √(2 * c) • (z : ℂ²))
          (contMDiff_sqrt_two_mul_smul_coe_sphere c) Ω.constSmooth ↔
      η = (c / 2) • sphereAreaForm := by
  rw [mpullback_sqrt_two_mul_smul_coe_sphere_constSmooth_eq_mpullback_hopfMap hΩ hc]
  exact (SmoothForm.mpullback_injective_of_surjective contMDiff_hopfMap hopfMap_surjective
    mfderiv_hopfMap_surjective).eq_iff

/-- **The reduced space of the level `c` has area `2πc`.** For `c ≥ 0`, a two-form `η` on `S²`
which pulls back along the Hopf map to the restriction of the Kähler form `Ω` of `ℂ²` to the level
`‖x‖² / 2 = c` gives `S²` the symplectic area `2πc`. For `c > 0`, `η` is the reduced form of Hopf
reduction; at `c = 0` the level is the origin, `η = 0`, and the area is `0`. -/
theorem liouvilleMeasure_univ_of_mpullback_hopfMap_eq {Ω : SymplecticForm ℂ²}
    (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) {c : ℝ} (hc : 0 ≤ c) {η : SmoothTwoForm (𝓡 2) S²}
    (hη : SmoothForm.mpullback hopfMap contMDiff_hopfMap η =
      SmoothForm.mpullback (fun z : S³ ↦ √(2 * c) • (z : ℂ²))
        (contMDiff_sqrt_two_mul_smul_coe_sphere c) Ω.constSmooth) :
    η.liouvilleMeasure 1 Set.univ = ENNReal.ofReal (2 * π * c) := by
  rw [(mpullback_hopfMap_eq_iff hΩ hc).1 hη, sphereAreaForm_eq_sphereVolumeForm,
    Orientation.liouvilleMeasure_smul_sphereVolumeForm_univ, abs_of_nonneg (by positivity)]
  congr 1
  ring

end TauCeti
