/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.Instances.OnePoint.VectorField

/-!
# Holomorphic sections of `𝒪(k)` on the Riemann sphere

This file computes the global holomorphic sections of the line bundles `𝒪(k)` on the Riemann
sphere `OnePoint ℂ` (`OnePoint.twistCore k`). For `k = n ≥ 0` they are the polynomial sections
of degree at most `n`: a section `s` is holomorphic exactly when its affine coordinate is a
polynomial `p` of degree at most `n` and its value at `∞` is `p.coeff n`
(`OnePoint.mdifferentiable_section_twistCore_natCast_iff`). For `k < 0` the only holomorphic
section is `0` (`OnePoint.eq_zero_of_mdifferentiable_section_twistCore`), so `H⁰(𝒪(k)) = 0`.
Hence the holomorphic sections of `𝒪(n)` form a complex vector space isomorphic to the polynomials
of degree less than `n + 1` (`OnePoint.holomorphicTwistSectionsEquiv`), of complex dimension
`n + 1`, with basis the monomial sections `zʲ`, `j ≤ n` (`OnePoint.holomorphicTwistSectionsBasis`).

The proof follows the computation of the holomorphic vector fields in
`TauCeti.Geometry.Manifold.Instances.OnePoint.VectorField`. In the affine chart a holomorphic
section is an entire function `f`; in the inverted chart `w = z⁻¹` it reads as
`h w = wᵏ f(w⁻¹)` (`OnePoint.twistInvCoeff`), which is holomorphic at `0`. So `f(z) = zᵏ h(z⁻¹)`
is `O(|z|ᵏ)` at infinity, and Liouville's theorem makes `f` a polynomial of degree at most `k`
when `k ≥ 0` and `0` when `k < 0`. Conversely, for `p` of degree at most `n` the inverted
coordinate of the polynomial section is the reflected polynomial `Polynomial.reflect n p`, which
is entire.

As checks, the section of the trivial bundle `𝒪(0)` with affine coordinate `z` is not holomorphic,
since it has a pole at `∞` (`OnePoint.not_mdifferentiable_section_twistCore_zero_of_coe`), and the
holomorphic vector fields `(a + b z + c z²) ∂_z` correspond to the holomorphic sections of
`𝒪(2)` with the same affine coordinate (`OnePoint.holomorphicVectorFieldsEquivTwistSections`).

## Main declarations

* `OnePoint.twistInvCoeff k s`: the coordinate of a section `s` of `𝒪(k)` in the inverted chart.
* `OnePoint.mdifferentiable_section_twistCore_iff`: a section of `𝒪(k)` is holomorphic exactly
  when its affine coordinate is entire and its inverted coordinate is differentiable at `0`.
* `OnePoint.polynomialSection n p`: the section of `𝒪(n)` with affine coordinate `p`, analytic
  when `p` has degree at most `n` (`OnePoint.contMDiff_polynomialSection`).
* `OnePoint.holomorphicTwistSections k`: the space of holomorphic sections of `𝒪(k)`.
* `OnePoint.holomorphicTwistSections_eq_bot`: `H⁰(𝒪(k)) = 0` for `k < 0`.
* `OnePoint.holomorphicTwistSectionsEquiv n`: `H⁰(𝒪(n)) ≃ Polynomial.degreeLT ℂ (n + 1)`, and
  `OnePoint.finrank_holomorphicTwistSections`: complex dimension `n + 1`.
* `OnePoint.contMDiff_section_twistCore_iff_mdifferentiable`: holomorphic sections of `𝒪(k)` are
  analytic.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §29.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.4.
-/

public section

open Bornology Bundle Filter Function Polynomial Set Topology

open scoped Manifold ContDiff

noncomputable section

namespace OnePoint

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/-! ### Sections in the inverted chart -/

/-- The coordinate of a section `s` of `𝒪(k)` in the inverted chart: at `w ≠ 0` it is
`wᵏ s(w⁻¹)` (`OnePoint.twistInvCoeff_of_ne_zero`), and at `w = 0` it is the value of `s` at `∞`
(`OnePoint.twistInvCoeff_zero`). -/
def twistInvCoeff (k : ℤ) (s : OnePoint 𝕜 → 𝕜) (w : 𝕜) : 𝕜 :=
  twistTransition k (invChart.symm w) ∞ (invChart.symm w) * s (invChart.symm w)

@[simp]
theorem twistInvCoeff_zero (k : ℤ) (s : OnePoint 𝕜 → 𝕜) : twistInvCoeff k s 0 = s ∞ := by
  simp [twistInvCoeff, invChart_symm_zero]

theorem twistInvCoeff_of_ne_zero (k : ℤ) (s : OnePoint 𝕜 → 𝕜) {w : 𝕜} (hw : w ≠ 0) :
    twistInvCoeff k s w = w ^ k * s (w⁻¹ : 𝕜) := by
  rw [twistInvCoeff, invChart_symm_of_ne_zero hw, twistTransition_coe_infty, affineChart_coe,
    inv_zpow', neg_neg]

/-- Off `0`, the coordinate of a section in the chart at `∞` is its inverted coordinate at the
inverted chart value. -/
theorem twistTransition_mul_eq_twistInvCoeff (k : ℤ) (s : OnePoint 𝕜 → 𝕜) {p : OnePoint 𝕜}
    (hp : p ≠ ((0 : 𝕜) : OnePoint 𝕜)) :
    twistTransition k p ∞ p * s p = twistInvCoeff k s (invChart p) := by
  have hmem : p ∈ (invChart : OpenPartialHomeomorph (OnePoint 𝕜) 𝕜).source := by
    simpa [invChart_source] using hp
  rw [twistInvCoeff, invChart.left_inv hmem]

/-! ### Holomorphic sections in the two charts -/

/-- In the preferred trivialization at `y`, a section `s` of `𝒪(k)` has the coordinate
`twistTransition k p y p * s p` at `p`. -/
private theorem trivializationAt_twistCore_apply (k : ℤ) (y : OnePoint 𝕜) (s : OnePoint 𝕜 → 𝕜)
    (p : OnePoint 𝕜) :
    (trivializationAt 𝕜 (twistCore k).Fiber y ⟨p, s p⟩).2 = twistTransition k p y p * s p := by
  rw [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def, twistCore_indexAt]
  exact twistCore_localTriv_apply k y s p

/-- A section of `𝒪(k)` is differentiable at a finite point `z₀` exactly when its affine
coordinate is differentiable at `z₀`. -/
theorem mdifferentiableAt_section_twistCore_coe_iff (k : ℤ) (s : OnePoint 𝕜 → 𝕜) (z₀ : 𝕜) :
    MDifferentiableAt 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜))
        (fun p ↦ TotalSpace.mk' 𝕜 (E := (twistCore k).Fiber) p (s p)) (z₀ : OnePoint 𝕜) ↔
      DifferentiableAt 𝕜 (fun z : 𝕜 ↦ s z) z₀ := by
  let s' : ∀ p, (twistCore (𝕜 := 𝕜) k).Fiber p := s
  refine (mdifferentiableAt_section (IB := 𝓘(𝕜)) (F := 𝕜) s').trans ?_
  rw [TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm]
  refine Iff.of_eq (congrArg₂ _ (funext fun z ↦ ?_) (by simp [chartAt_coe]))
  have hz : (extChartAt 𝓘(𝕜) (z₀ : OnePoint 𝕜)).symm z = z := by simp [chartAt_coe]
  rw [Function.comp_apply, hz]
  rw [trivializationAt_twistCore_apply, twistTransition_coe_coe, one_mul]

/-- A section of `𝒪(k)` is differentiable at `∞` exactly when its inverted coordinate is
differentiable at `0`. -/
theorem mdifferentiableAt_section_twistCore_infty_iff (k : ℤ) (s : OnePoint 𝕜 → 𝕜) :
    MDifferentiableAt 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜))
        (fun p ↦ TotalSpace.mk' 𝕜 (E := (twistCore k).Fiber) p (s p)) (∞ : OnePoint 𝕜) ↔
      DifferentiableAt 𝕜 (twistInvCoeff k s) 0 := by
  let s' : ∀ p, (twistCore (𝕜 := 𝕜) k).Fiber p := s
  refine (mdifferentiableAt_section (IB := 𝓘(𝕜)) (F := 𝕜) s').trans ?_
  have h0 : extChartAt 𝓘(𝕜) (∞ : OnePoint 𝕜) ∞ = 0 := by simp [chartAt_infty]
  rw [TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm, h0]
  refine Iff.of_eq (congrArg₂ _ (funext fun w ↦ ?_) rfl)
  have hw : (extChartAt 𝓘(𝕜) (∞ : OnePoint 𝕜)).symm w = invChart.symm w := by
    simp [chartAt_infty]
  rw [Function.comp_apply, hw, trivializationAt_twistCore_apply, twistInvCoeff]

/-- **Holomorphic sections of `𝒪(k)` in the two charts.** A section of `𝒪(k)` is differentiable
exactly when its affine coordinate is differentiable on `𝕜` and its inverted coordinate is
differentiable at `0`. -/
theorem mdifferentiable_section_twistCore_iff (k : ℤ) (s : OnePoint 𝕜 → 𝕜) :
    MDifferentiable 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜))
        (fun p ↦ TotalSpace.mk' 𝕜 (E := (twistCore k).Fiber) p (s p)) ↔
      Differentiable 𝕜 (fun z : 𝕜 ↦ s z) ∧ DifferentiableAt 𝕜 (twistInvCoeff k s) 0 := by
  refine ⟨fun h ↦ ⟨fun z ↦ (mdifferentiableAt_section_twistCore_coe_iff k s z).1 (h z),
    (mdifferentiableAt_section_twistCore_infty_iff k s).1 (h ∞)⟩, fun ⟨hf, hh⟩ x ↦ ?_⟩
  induction x using OnePoint.rec with
  | infty => exact (mdifferentiableAt_section_twistCore_infty_iff k s).2 hh
  | coe z => exact (mdifferentiableAt_section_twistCore_coe_iff k s z).2 (hf z)

/-! ### Polynomial sections -/

/-- The section of `𝒪(n)` attached to a polynomial `p`: its affine coordinate is `p`, and its
value at `∞` is `p.coeff n`. For `p` of degree at most `n` its inverted coordinate is the
reflected polynomial `wⁿ p(w⁻¹)` (`OnePoint.twistInvCoeff_polynomialSection`), and the section is
analytic (`OnePoint.contMDiff_polynomialSection`). -/
def polynomialSection (n : ℕ) : 𝕜[X] →ₗ[𝕜] OnePoint 𝕜 → 𝕜 where
  toFun p x := x.elim (p.coeff n) p.eval
  map_add' p q := by
    funext x
    induction x using OnePoint.rec with
    | infty => simp
    | coe z => simp
  map_smul' c p := by
    funext x
    induction x using OnePoint.rec with
    | infty => simp
    | coe z => simp [Polynomial.eval_smul, smul_eq_mul]

omit [ProperSpace 𝕜] in
@[simp]
theorem polynomialSection_coe (n : ℕ) (p : 𝕜[X]) (z : 𝕜) :
    polynomialSection n p z = p.eval z :=
  (rfl)

omit [ProperSpace 𝕜] in
@[simp]
theorem polynomialSection_infty (n : ℕ) (p : 𝕜[X]) :
    polynomialSection n p ∞ = p.coeff n :=
  (rfl)

omit [ProperSpace 𝕜] in
theorem polynomialSection_injective (n : ℕ) : Injective (polynomialSection (𝕜 := 𝕜) n) :=
  fun p q h ↦ Polynomial.funext fun z ↦ by simpa using congrFun h z

omit [ProperSpace 𝕜] in
/-- The polynomial section of the monomial `zʲ` is the monomial section `zʲ`. -/
@[simp]
theorem polynomialSection_X_pow (n j : ℕ) :
    polynomialSection n (X ^ j : 𝕜[X]) = monomialSection n j := by
  funext x
  induction x using OnePoint.rec with
  | infty => simp [coeff_X_pow, eq_comm]
  | coe z => simp

/-- The inverted coordinate of the polynomial section of `p`, of degree at most `n`, is the
reflected polynomial `wⁿ p(w⁻¹)`. -/
theorem twistInvCoeff_polynomialSection {n : ℕ} {p : 𝕜[X]} (hp : p ∈ degreeLT 𝕜 (n + 1)) :
    twistInvCoeff n (polynomialSection n p) = fun w ↦ (reflect n p).eval w := by
  funext w
  rcases eq_or_ne w 0 with rfl | hw
  · simp [← coeff_zero_eq_eval_zero, coeff_reflect]
  · rw [twistInvCoeff_of_ne_zero _ _ hw, polynomialSection_coe, zpow_natCast]
    let : Invertible w⁻¹ := invertibleOfNonzero (inv_ne_zero hw)
    have hn : p.natDegree ≤ n :=
      natDegree_le_iff_degree_le.2 <| mem_degreeLE.1 <| by rwa [← degreeLT_succ_eq_degreeLE]
    have h := eval₂_reflect_mul_pow (RingHom.id 𝕜) w⁻¹ n p hn
    rw [invOf_eq_inv, inv_inv] at h
    simp only [eval₂_id] at h
    rw [← h, inv_pow, mul_comm, inv_mul_cancel_right₀ (pow_ne_zero n hw)]

/-- **Polynomial sections are global.** For `p` of degree at most `n`, the section of `𝒪(n)`
with affine coordinate `p` is analytic on the whole projective line. -/
theorem contMDiff_polynomialSection {n : ℕ} {p : 𝕜[X]} (hp : p ∈ degreeLT 𝕜 (n + 1)) :
    ContMDiff 𝓘(𝕜) (𝓘(𝕜).prod 𝓘(𝕜)) ω
      (fun x ↦ TotalSpace.mk' 𝕜 (E := (twistCore (n : ℤ)).Fiber) x
        (polynomialSection (𝕜 := 𝕜) n p x)) := by
  rw [contMDiff_section_twistCore_iff]
  constructor
  · have h : ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) ω (fun x ↦ p.eval (chartAt 𝕜 ((0 : 𝕜) : OnePoint 𝕜) x))
        (chartAt 𝕜 ((0 : 𝕜) : OnePoint 𝕜)).source := by
      have hp : ContDiff 𝕜 ω (fun z : 𝕜 ↦ p.eval z) := by
        simpa using p.contDiff_aeval (R := 𝕜) (𝕜 := 𝕜) ω
      exact hp.contMDiff.comp_contMDiffOn contMDiffOn_chart
    refine (h.congr fun x hx ↦ ?_).mono fun x hx ↦ by simpa using hx
    induction x using OnePoint.rec with
    | infty => simp at hx
    | coe z => simp [chartAt_coe]
  · have h : ContMDiffOn 𝓘(𝕜) 𝓘(𝕜) ω (fun x ↦ (reflect n p).eval (chartAt 𝕜 (∞ : OnePoint 𝕜) x))
        (chartAt 𝕜 (∞ : OnePoint 𝕜)).source := by
      have hp : ContDiff 𝕜 ω (fun z : 𝕜 ↦ (reflect n p).eval z) := by
        simpa using (reflect n p).contDiff_aeval (R := 𝕜) (𝕜 := 𝕜) ω
      exact hp.contMDiff.comp_contMDiffOn contMDiffOn_chart
    refine (h.congr fun x hx ↦ ?_).mono fun x hx ↦ by simpa using hx
    have hx' : x ≠ ((0 : 𝕜) : OnePoint 𝕜) := by simpa using hx
    rw [twistTransition_mul_eq_twistInvCoeff _ _ hx', twistInvCoeff_polynomialSection hp,
      chartAt_infty]

end NontriviallyNormedField

/-! ### Holomorphic sections on the Riemann sphere -/

/-- **Holomorphic sections of `𝒪(n)`.** For `n ≥ 0`, a section of `𝒪(n)` on the Riemann sphere
is holomorphic exactly when it is the polynomial section of a polynomial `p` of degree at most
`n`: its affine coordinate is `p` and its value at `∞` is `p.coeff n`. -/
theorem mdifferentiable_section_twistCore_natCast_iff (n : ℕ) (s : OnePoint ℂ → ℂ) :
    MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ))
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (n : ℤ)).Fiber) x (s x)) ↔
      ∃ p ∈ degreeLT ℂ (n + 1), polynomialSection n p = s := by
  rw [mdifferentiable_section_twistCore_iff]
  constructor
  · rintro ⟨hf, hh⟩
    -- In the affine chart `s z = zⁿ h(z⁻¹)`, which is `O(|z|ⁿ)` since `h` is continuous at `0`.
    have hbound : (fun z ↦ twistInvCoeff n s z⁻¹) =O[cobounded ℂ] (fun _ ↦ (1 : ℂ)) :=
      (hh.continuousAt.tendsto.comp tendsto_inv₀_cobounded).isBigO_one ℂ
    have hgrowth : (fun z : ℂ ↦ s z) =O[cobounded ℂ] (· ^ n) := by
      refine ((Asymptotics.isBigO_refl (fun z : ℂ ↦ z ^ n) _).mul hbound).congr' ?_ ?_
      · filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
        rw [twistInvCoeff_of_ne_zero _ _ (inv_ne_zero hz), inv_inv, inv_zpow', zpow_neg,
          zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hz), one_mul]
      · filter_upwards with z using mul_one _
    obtain ⟨p, hpn, hp⟩ := hf.exists_eq_polynomial_eval_of_isBigO_pow hgrowth
    have hpmem : p ∈ degreeLT ℂ (n + 1) := by
      rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
      exact natDegree_le_iff_degree_le.1 hpn
    refine ⟨p, hpmem, funext fun x ↦ ?_⟩
    induction x using OnePoint.rec with
    | coe z => exact (congrFun hp z).symm
    | infty =>
      -- Both inverted coordinates are continuous at `0` and agree off `0`.
      have heq : twistInvCoeff n s =ᶠ[𝓝[≠] 0] twistInvCoeff n (polynomialSection n p) := by
        filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
        rw [twistInvCoeff_of_ne_zero _ _ hw, twistInvCoeff_of_ne_zero _ _ hw,
          polynomialSection_coe, ← congrFun hp]
      have hcont : Continuous (twistInvCoeff n (polynomialSection n p)) := by
        rw [twistInvCoeff_polynomialSection hpmem]
        exact (reflect n p).differentiable.continuous
      have h0 := tendsto_nhds_unique
        (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).congr' heq.symm)
      rw [twistInvCoeff_zero, twistInvCoeff_zero] at h0
      exact h0.symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun z ↦ by simpa using p.differentiable z, ?_⟩
    rw [twistInvCoeff_polynomialSection hp]
    exact (reflect n p).differentiable 0

/-- **Vanishing theorem: `H⁰(𝒪(k)) = 0` for `k < 0`.** On the Riemann sphere, every holomorphic
section of `𝒪(k)` with `k < 0` vanishes identically. -/
theorem eq_zero_of_mdifferentiable_section_twistCore {k : ℤ} (hk : k < 0) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ))
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore k).Fiber) x (s x))) :
    s = 0 := by
  rw [mdifferentiable_section_twistCore_iff] at hs
  obtain ⟨hf, hh⟩ := hs
  obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hk
  -- In the affine chart `s z = (z⁻¹)ᵐ⁺¹ h(z⁻¹)`, which tends to `0` at infinity.
  have hlim : Tendsto (fun z : ℂ ↦ s z) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    have h1 : Tendsto (fun z : ℂ ↦ z⁻¹ ^ (m + 1)) (cobounded ℂ) (𝓝 0) := by
      have h := ((continuous_pow (m + 1)).tendsto (0 : ℂ)).comp tendsto_inv₀_cobounded
      rwa [zero_pow (Nat.succ_ne_zero m)] at h
    have h2 : Tendsto (fun z ↦ twistInvCoeff (Int.negSucc m) s z⁻¹) (cobounded ℂ) (𝓝 (s ∞)) := by
      have h := hh.continuousAt.tendsto.comp tendsto_inv₀_cobounded
      rwa [twistInvCoeff_zero] at h
    refine (zero_mul (s ∞) ▸ h1.mul h2).congr' ?_
    filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
    rw [twistInvCoeff_of_ne_zero _ _ (inv_ne_zero hz), inv_inv, zpow_negSucc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (inv_ne_zero hz)), one_mul]
  have hf0 (z : ℂ) : s z = 0 := hf.apply_eq_of_tendsto_cocompact z hlim
  funext x
  induction x using OnePoint.rec with
  | coe z => exact hf0 z
  | infty =>
    -- The inverted coordinate vanishes off `0`, so by continuity also at `0`.
    have heq : twistInvCoeff (Int.negSucc m) s =ᶠ[𝓝[≠] 0] fun _ ↦ 0 := by
      filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
      rw [twistInvCoeff_of_ne_zero _ _ hw, hf0, mul_zero]
    have h0 := tendsto_nhds_unique
      (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)
    rw [twistInvCoeff_zero] at h0
    exact h0

/-- **Holomorphic sections of `𝒪(k)` are analytic.** For `m ≠ 0`, a section of `𝒪(k)` on the
Riemann sphere is `C^m` exactly when it is holomorphic. -/
theorem contMDiff_section_twistCore_iff_mdifferentiable (k : ℤ) {m : ℕ∞ω} (hm : m ≠ 0)
    (s : OnePoint ℂ → ℂ) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) m
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore k).Fiber) x (s x)) ↔
      MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ))
        (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore k).Fiber) x (s x)) := by
  refine ⟨fun h ↦ h.mdifferentiable hm, fun h ↦ ?_⟩
  rcases lt_or_ge k 0 with hk | hk
  · obtain rfl := eq_zero_of_mdifferentiable_section_twistCore hk h
    exact (contMDiff_zeroSection ℂ (twistCore (𝕜 := ℂ) k).Fiber).of_le le_top
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    obtain ⟨p, hp, rfl⟩ := (mdifferentiable_section_twistCore_natCast_iff n s).1 h
    exact (contMDiff_polynomialSection hp).of_le le_top

/-! ### The space of holomorphic sections -/

/-- The complex vector space `H⁰(𝒪(k))` of **holomorphic sections** of `𝒪(k)` on the Riemann
sphere: the sections `s` for which `x ↦ (x, s x)` is a holomorphic map into the total space. -/
def holomorphicTwistSections (k : ℤ) : Submodule ℂ (OnePoint ℂ → ℂ) where
  carrier := {s | MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ))
    (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore k).Fiber) x (s x))}
  add_mem' hs ht := mdifferentiable_add_section hs ht
  zero_mem' := mdifferentiable_zeroSection ℂ (twistCore (𝕜 := ℂ) k).Fiber
  smul_mem' _ _ hs := mdifferentiable_smul_const_section hs

theorem mem_holomorphicTwistSections {k : ℤ} {s : OnePoint ℂ → ℂ} :
    s ∈ holomorphicTwistSections k ↔ MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ))
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore k).Fiber) x (s x)) :=
  (Iff.rfl)

/-- `H⁰(𝒪(k)) = 0` for `k < 0`. -/
theorem holomorphicTwistSections_eq_bot {k : ℤ} (hk : k < 0) : holomorphicTwistSections k = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hs ↦ eq_zero_of_mdifferentiable_section_twistCore hk hs

/-- The holomorphic sections of `𝒪(k)` with `k < 0` form a space of dimension `0`. -/
theorem finrank_holomorphicTwistSections_of_neg {k : ℤ} (hk : k < 0) :
    Module.finrank ℂ (holomorphicTwistSections k) = 0 := by
  rw [holomorphicTwistSections_eq_bot hk, finrank_bot]

/-- The holomorphic sections of `𝒪(n)` are the polynomial sections of the polynomials of degree
less than `n + 1`. -/
theorem holomorphicTwistSections_natCast_eq_map (n : ℕ) :
    holomorphicTwistSections n = (degreeLT ℂ (n + 1)).map (polynomialSection n) := by
  ext s
  rw [mem_holomorphicTwistSections, mdifferentiable_section_twistCore_natCast_iff,
    Submodule.mem_map]

/-- The holomorphic sections of `𝒪(n)` on the Riemann sphere: the space they form is isomorphic
to the space of polynomials of degree less than `n + 1`. -/
def holomorphicTwistSectionsEquiv (n : ℕ) :
    holomorphicTwistSections n ≃ₗ[ℂ] degreeLT ℂ (n + 1) :=
  (LinearEquiv.ofEq _ _ (holomorphicTwistSections_natCast_eq_map n)).trans
    (Submodule.equivMapOfInjective _ (polynomialSection_injective n) _).symm

/-- The holomorphic section corresponding to a polynomial of degree less than `n + 1` is its
polynomial section. -/
@[simp]
theorem coe_holomorphicTwistSectionsEquiv_symm_apply (n : ℕ) (p : degreeLT ℂ (n + 1)) :
    ((holomorphicTwistSectionsEquiv n).symm p : OnePoint ℂ → ℂ) = polynomialSection n p := by
  simp [holomorphicTwistSectionsEquiv]

/-- The polynomial corresponding to a holomorphic section is its affine coordinate. -/
@[simp]
theorem eval_holomorphicTwistSectionsEquiv_apply (n : ℕ) (s : holomorphicTwistSections n)
    (z : ℂ) : (holomorphicTwistSectionsEquiv n s : ℂ[X]).eval z = (s : OnePoint ℂ → ℂ) z := by
  conv_rhs => rw [← (holomorphicTwistSectionsEquiv n).symm_apply_apply s]
  rw [coe_holomorphicTwistSectionsEquiv_symm_apply, polynomialSection_coe]

/-- The holomorphic sections of `𝒪(n)` form a complex vector space of dimension `n + 1`. -/
theorem finrank_holomorphicTwistSections (n : ℕ) :
    Module.finrank ℂ (holomorphicTwistSections n) = n + 1 := by
  rw [(holomorphicTwistSectionsEquiv n).finrank_eq, (degreeLTEquiv ℂ (n + 1)).finrank_eq,
    Module.finrank_fin_fun]

/-- The holomorphic sections of `𝒪(n)` form a real vector space of dimension `2 (n + 1)`. -/
theorem finrank_real_holomorphicTwistSections (n : ℕ) :
    Module.finrank ℝ (holomorphicTwistSections n) = 2 * (n + 1) := by
  rw [finrank_real_of_complex, finrank_holomorphicTwistSections]

/-- The basis of the holomorphic sections of `𝒪(n)` given by the monomial sections `zʲ`,
`j ≤ n` (`OnePoint.coe_holomorphicTwistSectionsBasis`). -/
def holomorphicTwistSectionsBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) ℂ (holomorphicTwistSections n) :=
  (degreeLT.basis ℂ (n + 1)).map (holomorphicTwistSectionsEquiv n).symm

/-- **The monomial sections form a basis.** The `j`-th vector of
`OnePoint.holomorphicTwistSectionsBasis n` is the monomial section `zʲ` of `𝒪(n)`. -/
@[simp]
theorem coe_holomorphicTwistSectionsBasis (n : ℕ) (j : Fin (n + 1)) :
    (holomorphicTwistSectionsBasis n j : OnePoint ℂ → ℂ) = monomialSection n j := by
  simp [holomorphicTwistSectionsBasis]

/-- **The coordinate `z` is not a global section of the trivial bundle.** A section of `𝒪(0)`
whose affine coordinate is `z` is not holomorphic, whatever its value at `∞`: in the inverted
chart it reads as `w⁻¹`, which has a pole at `0`. -/
theorem not_mdifferentiable_section_twistCore_zero_of_coe {s : OnePoint ℂ → ℂ}
    (hs : ∀ z : ℂ, s z = z) :
    ¬ MDifferentiable 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ))
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (0 : ℤ)).Fiber) x (s x)) := by
  intro h
  obtain ⟨p, hp, rfl⟩ := (mdifferentiable_section_twistCore_natCast_iff 0 s).1 h
  have hp0 : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero <| Nat.le_zero.1 <|
    natDegree_le_iff_degree_le.2 <| mem_degreeLE.1 <| by rwa [← degreeLT_succ_eq_degreeLE]
  have h0 := hs 0
  have h1 := hs 1
  rw [polynomialSection_coe, hp0, eval_C] at h0 h1
  exact one_ne_zero (h1.symm.trans h0)

/-! ### Holomorphic vector fields as sections of `𝒪(2)` -/

/-- **The tangent bundle of the Riemann sphere is `𝒪(2)` on holomorphic sections.** The holomorphic
vector fields `(a + b z + c z²) ∂_z` correspond to the holomorphic sections of `𝒪(2)` with the same
affine coordinate (`OnePoint.holomorphicVectorFieldsEquivTwistSections_apply_coe`); the value `-c`
of the vector field at `∞` corresponds to the value `c` of the section
(`OnePoint.holomorphicVectorFieldsEquivTwistSections_apply_infty`). -/
def holomorphicVectorFieldsEquivTwistSections :
    holomorphicVectorFields ≃ₗ[ℂ] holomorphicTwistSections 2 :=
  holomorphicVectorFieldsEquiv.trans (holomorphicTwistSectionsEquiv 2).symm

@[simp]
theorem holomorphicVectorFieldsEquivTwistSections_apply_coe (X : holomorphicVectorFields)
    (z : ℂ) :
    (holomorphicVectorFieldsEquivTwistSections X : OnePoint ℂ → ℂ) z =
      (X : OnePoint ℂ → ℂ) z := by
  have h := congrFun
    (coe_holomorphicTwistSectionsEquiv_symm_apply 2 (holomorphicVectorFieldsEquiv X)) z
  rw [polynomialSection_coe, eval_holomorphicVectorFieldsEquiv_apply] at h
  exact h

@[simp]
theorem holomorphicVectorFieldsEquivTwistSections_apply_infty (X : holomorphicVectorFields) :
    (holomorphicVectorFieldsEquivTwistSections X : OnePoint ℂ → ℂ) ∞ =
      -(X : OnePoint ℂ → ℂ) ∞ := by
  have h := congrFun
    (coe_holomorphicTwistSectionsEquiv_symm_apply 2 (holomorphicVectorFieldsEquiv X)) ∞
  rw [polynomialSection_infty] at h
  refine h.trans ?_
  conv_rhs => rw [← holomorphicVectorFieldsEquiv.symm_apply_apply X]
  rw [coe_holomorphicVectorFieldsEquiv_symm_apply, polynomialVectorField_infty, neg_neg]

end OnePoint
