/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Operator

/-!
# Realizations of the stationary Schrödinger operator on `H²` are isomorphisms

Let `E` be a finite-dimensional real inner product space and `P` an essentially bounded real
potential on `E`. A map `T : H²(E) → L²(E; ℂ)`, from the complex Bessel-potential space
`H^{2}(E)` to the complex square-integrable functions, *realizes* the Schrödinger operator
`-Δ + P` when

`∫ (T u) φ = ∫ u (-Δφ + P φ)`

for every `u ∈ H²(E)` and every smooth compactly supported real function `φ`. Such a realization
is determined by its weak equation: `T u = g` exactly when `u` is a weak solution of
`-Δu + P u = g` (`TauCeti.apply_eq_iff_forall_integral_mul_neg_laplacian_add_mul_eq`). This holds
for every potential, and needs no linearity or continuity of `T`.

If moreover `P` is almost everywhere nonnegative and almost everywhere at least `a > 0` outside a
ball, then every such realization is a bijection
(`TauCeti.bijective_of_integral_apply_mul_eq`). For a bounded linear `T` this makes it a
continuous linear isomorphism `H²(E) ≃ L²(E; ℂ)`, by `ContinuousLinearEquiv.ofBijective`.

* It is injective, because the real and imaginary parts of a complex `L²` weak solution of
  `-Δu + P u = 0` are real weak solutions, which vanish
  (`TauCeti.ae_eq_zero_of_integral_mul_neg_laplacian_add_mul_eq_zero`, from the uniqueness theorem
  `TauCeti.ae_eq_of_integral_mul_neg_laplacian_add_mul_eq`).
* It is onto, because for `g ∈ L²(E; ℂ)` the real equations with right-hand sides `Re g` and
  `Im g` have weak solutions in `H²(E)`
  (`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`), and these
  combine into a complex weak solution in `H^{2}(E)`.

The potential may vanish on a large set inside the ball, so the operator need not be bounded
below by a positive constant pointwise. The linearization `v ↦ -Δv + h e^{2w} v / 4` of Taubes's
reduced plane-vortex equation `Δw = (h e^{2w} - 1) / 8 + g` at a real solution `w` has a potential
of this kind whenever `w` is bounded and tends to zero at infinity, since `h = |p|² / (1 + |p|²)`,
for the polynomial `p` of the zeros, lies in `[0, 1)` and tends to `1` at infinity. This
invertibility is the input of the implicit function theorem for the dependence of the reduced
solution on the zeros. Since the statements only use the weak equation, they apply to any
construction of the realization, for instance through the distributional Laplacian on
Bessel-potential spaces.

## Main results

* `TauCeti.ae_eq_zero_of_integral_mul_neg_laplacian_add_mul_eq_zero`: a complex `L²` weak solution
  of `-Δu + P u = 0` vanishes almost everywhere.
* `TauCeti.apply_eq_iff_forall_integral_mul_neg_laplacian_add_mul_eq`: a realization is
  characterized by its weak equation.
* `TauCeti.injective_of_integral_apply_mul_eq`, `TauCeti.surjective_of_integral_apply_mul_eq`,
  `TauCeti.bijective_of_integral_apply_mul_eq`: a realization is injective, onto and bijective.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped Laplacian ContDiff BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {P : E → ℝ}

namespace TauCeti

/-- **Complex weak solutions of the homogeneous Schrödinger equation vanish.** Let `P` be
essentially bounded, almost everywhere nonnegative, and almost everywhere at least `a > 0` outside
the closed ball of radius `R`. If `v ∈ L²(E; ℂ)` satisfies `-Δv + P v = 0` weakly, that is
`∫ v (-Δφ + P φ) = 0` for every smooth compactly supported real function `φ`, then `v = 0` almost
everywhere. -/
theorem ae_eq_zero_of_integral_mul_neg_laplacian_add_mul_eq_zero [Nontrivial E]
    (hP : MemLp P ⊤ (volume : Measure E)) (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a)
    (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z) {v : E → ℂ} (hv : MemLp v 2 volume)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, v z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ) = 0) :
    v =ᵐ[volume] 0 := by
  -- The integrand is integrable, so its real and imaginary parts integrate to zero.
  have hint (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      Integrable (fun z ↦ v z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ)) volume :=
    hv.integrable_mul (memLp_neg_laplacian_add_mul hP (hφ.of_le (by simp)) hc).ofReal
  have hre := ae_eq_of_integral_mul_neg_laplacian_add_mul_eq hP hP₀ ha hPa (g := 0) hv.re
    MemLp.zero (fun φ hφ hc ↦ by
      have h := integral_re (hint φ hφ hc)
      simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, hweak φ hφ hc, Complex.zero_re] at h
      simpa only [RCLike.re_to_complex, Pi.zero_apply, zero_mul, integral_zero] using h)
    (fun φ _ _ ↦ by simp)
  have him := ae_eq_of_integral_mul_neg_laplacian_add_mul_eq hP hP₀ ha hPa (g := 0) hv.im
    MemLp.zero (fun φ hφ hc ↦ by
      have h := integral_im (hint φ hφ hc)
      simp only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add, hweak φ hφ hc, Complex.zero_im] at h
      simpa only [RCLike.im_to_complex, Pi.zero_apply, zero_mul, integral_zero] using h)
    (fun φ _ _ ↦ by simp)
  filter_upwards [hre, him] with z h₁ h₂
  exact Complex.ext (by simpa using h₁) (by simpa using h₂)

variable (T : H^{2}(E) → Lp ℂ 2 (volume : Measure E))

/-- **A realization of the Schrödinger operator is determined by its weak equation.** Let
`T : H²(E) → L²(E; ℂ)` satisfy `∫ (T u) φ = ∫ u (-Δφ + P φ)` for every
`u` and every smooth compactly supported real `φ`. Then `T u = g` exactly when
`∫ u (-Δφ + P φ) = ∫ g φ` for every such `φ`, that is, when `u` is a weak solution of
`-Δu + P u = g`. -/
theorem apply_eq_iff_forall_integral_mul_neg_laplacian_add_mul_eq
    (hT : ∀ (u : H^{2}(E)) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, T u z * (φ z : ℂ) =
        ∫ z, inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ))
    {u : H^{2}(E)} {g : Lp ℂ 2 (volume : Measure E)} :
    T u = g ↔ ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ) =
        ∫ z, g z * (φ z : ℂ) := by
  refine ⟨fun h φ hφ hc ↦ by rw [← hT u φ hφ hc, h], fun h ↦ Lp.ext ?_⟩
  -- `T u - g` is orthogonal to every test function, so it vanishes.
  have hd : ∀ᵐ z ∂volume, (T u - g) z = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp (T u - g)).locallyIntegrable (by norm_num)) fun φ hφ hc ↦ ?_
    have hφ2 : MemLp (fun z ↦ (φ z : ℂ)) 2 volume :=
      (hφ.continuous.memLp_of_hasCompactSupport hc).ofReal
    calc ∫ z, φ z • (T u - g) z = ∫ z, (T u z * (φ z : ℂ) - g z * (φ z : ℂ)) := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_sub (T u) g] with z hz
          rw [hz, Pi.sub_apply, Complex.real_smul]
          ring
      _ = 0 := by
          rw [integral_sub (f := fun z ↦ T u z * (φ z : ℂ)) (g := fun z ↦ g z * (φ z : ℂ))
            ((Lp.memLp _).integrable_mul hφ2) ((Lp.memLp _).integrable_mul hφ2),
            hT u φ hφ hc, h φ hφ hc, sub_self]
  filter_upwards [hd, Lp.coeFn_sub (T u) g] with z h₁ h₂
  rw [← sub_eq_zero, ← Pi.sub_apply, ← h₂, h₁]

/-- **A realization of the Schrödinger operator is injective.** Let `P` be essentially bounded,
almost everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of
radius `R`. Every `T : H²(E) → L²(E; ℂ)` with `∫ (T u) φ = ∫ u (-Δφ + P φ)` for all `u` and all
smooth compactly supported real `φ` is injective. -/
theorem injective_of_integral_apply_mul_eq [Nontrivial E] (hP : MemLp P ⊤ (volume : Measure E))
    (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a) (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z)
    (hT : ∀ (u : H^{2}(E)) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, T u z * (φ z : ℂ) =
        ∫ z, inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ)) :
    Function.Injective T := by
  intro u v huv
  -- `u` and `v` are weak solutions with the same right-hand side, so their difference is a weak
  -- solution of the homogeneous equation.
  refine inclusionLp_injective zero_le_two (sub_eq_zero.1 ?_)
  rw [← map_sub]
  refine Lp.ext ((ae_eq_zero_of_integral_mul_neg_laplacian_add_mul_eq_zero hP hP₀ ha hPa
    (Lp.memLp _) fun φ hφ hc ↦ ?_).trans (Lp.coeFn_zero ℂ 2 volume).symm)
  have hL := (memLp_neg_laplacian_add_mul hP (hφ.of_le (by simp)) hc).ofReal (K := ℂ)
  calc ∫ z, inclusionLp zero_le_two (u - v) z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ)
      = ∫ z, (inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ) -
          inclusionLp zero_le_two v z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ)) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_inclusionLp_sub_ae_eq zero_le_two (u := u) (v := v)
          (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)] with z hz
        rw [hz, sub_mul]
    _ = 0 := by
        rw [integral_sub
          (f := fun z ↦ inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ))
          (g := fun z ↦ inclusionLp zero_le_two v z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ))
          ((Lp.memLp _).integrable_mul hL) ((Lp.memLp _).integrable_mul hL),
          (apply_eq_iff_forall_integral_mul_neg_laplacian_add_mul_eq T hT).1 huv φ hφ hc,
          (apply_eq_iff_forall_integral_mul_neg_laplacian_add_mul_eq T hT).1 rfl φ hφ hc,
          sub_self]

/-- **A realization of the Schrödinger operator is onto.** Let `P` be essentially bounded, almost
everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of radius
`R`. Every `T : H²(E) → L²(E; ℂ)` with `∫ (T u) φ = ∫ u (-Δφ + P φ)` for all `u` and all smooth
compactly supported real `φ` is onto: every `g ∈ L²(E; ℂ)` is `T u` for the weak solution
`u ∈ H²(E)` of `-Δu + P u = g`. -/
theorem surjective_of_integral_apply_mul_eq [Nontrivial E] (hP : MemLp P ⊤ (volume : Measure E))
    (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a) (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z)
    (hT : ∀ (u : H^{2}(E)) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, T u z * (φ z : ℂ) =
        ∫ z, inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ)) :
    Function.Surjective T := by
  intro g
  have hg := Lp.memLp g
  -- Real weak solutions in `H²` for the real and imaginary parts of `g`.
  obtain ⟨h₁, hh₁, hw₁⟩ :=
    exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq hP hP₀ ha hPa
      hg.re
  obtain ⟨h₂, hh₂, hw₂⟩ :=
    exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq hP hP₀ ha hPa
      hg.im
  obtain ⟨u₁, hu₁⟩ := (mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq zero_le_two).1 hh₁
  obtain ⟨u₂, hu₂⟩ := (mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq zero_le_two).1 hh₂
  -- They combine into the complex weak solution `u₁ + i u₂`.
  have hu : ⇑(inclusionLp zero_le_two (u₁ + Complex.I • u₂)) =ᵐ[volume]
      fun z ↦ (h₁ z : ℂ) + h₂ z * Complex.I :=
    (coeFn_inclusionLp_add_ae_eq zero_le_two hu₁
      (coeFn_inclusionLp_smul_ae_eq zero_le_two Complex.I hu₂)).mono fun z hz ↦ by
        simp only [hz, smul_eq_mul, mul_comm]
  refine ⟨u₁ + Complex.I • u₂,
    (apply_eq_iff_forall_integral_mul_neg_laplacian_add_mul_eq T hT).2 fun φ hφ hc ↦ ?_⟩
  have h := (integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im hP hg
    (memLp_of_mem_realSobolevFunctions hh₁) (memLp_of_mem_realSobolevFunctions hh₂)
    (fun ψ hψ hψc ↦ by simpa using hw₁ ψ hψ hψc) (fun ψ hψ hψc ↦ by simpa using hw₂ ψ hψ hψc)
    (hφ.of_le (by simp)) hc).2
  rw [← h]
  exact integral_congr_ae (hu.mono fun z hz ↦ by simp only [hz])

/-- **A realization of the Schrödinger operator is bijective.** Let `P` be essentially bounded,
almost everywhere nonnegative, and almost everywhere at least `a > 0` outside the closed ball of
radius `R`. Every map `T : H²(E) → L²(E; ℂ)` with `∫ (T u) φ = ∫ u (-Δφ + P φ)` for all `u` and
all smooth compactly supported real `φ` is bijective. When `T` is a bounded linear map, it is
therefore a continuous linear isomorphism `H²(E) ≃ L²(E; ℂ)` (`ContinuousLinearEquiv.ofBijective`),
by the open mapping theorem. -/
theorem bijective_of_integral_apply_mul_eq [Nontrivial E] (hP : MemLp P ⊤ (volume : Measure E))
    (hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z) {a R : ℝ} (ha : 0 < a) (hPa : ∀ᵐ z ∂volume, R < ‖z‖ → a ≤ P z)
    (hT : ∀ (u : H^{2}(E)) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ z, T u z * (φ z : ℂ) =
        ∫ z, inclusionLp zero_le_two u z * ((-Δ (φ : E → ℝ) z + P z * φ z : ℝ) : ℂ)) :
    Function.Bijective T :=
  ⟨injective_of_integral_apply_mul_eq T hP hP₀ ha hPa hT,
    surjective_of_integral_apply_mul_eq T hP hP₀ ha hPa hT⟩

end TauCeti
