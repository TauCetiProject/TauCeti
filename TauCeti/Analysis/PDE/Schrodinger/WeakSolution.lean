/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Duhamel
public import TauCeti.Analysis.Semigroups.CauchyProblem.Unitary
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Weak solutions of the Schrödinger equation

On a finite-dimensional real inner product space `E`, consider the inhomogeneous Schrödinger
equation `i ∂ₜu + Δu = G`, `u(0) = f`, with `f ∈ L²(E, F)` and a forcing `G : ℝ → L²(E, F)` locally
integrable on `[0, ∞)`. Pairing the equation with a test function `ψ` and integrating in time gives
its **weak formulation**: for every `ψ ∈ L²` whose Laplacian `Δψ` lies in `L²` and every `t ≥ 0`,

`⟪ψ, u t⟫ = ⟪ψ, f⟫ + i ∫_{(0,t]} (⟪Δψ, u s⟫ - ⟪ψ, G s⟫) ds`,

which is the integrated form of `d/dt ⟪ψ, u t⟫ = i ⟪Δψ, u t⟫ - i ⟪ψ, G t⟫`, that is, of
`∂ₜu = i Δu - i G`. Here `Δψ ∈ L²` is the `χ ∈ L²` with `𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ`; the Schwartz
functions are such test functions, with `χ` their classical Laplacian.

The main theorem (`TauCeti.eqOn_schrodingerDuhamel_iff`) says that a function continuous on
`[0, ∞)` with values in `L²` satisfies the weak formulation exactly when it is given by
Duhamel's formula `u(t) = S(t) f - i ∫_0^t S(t - s) G(s) ds` (`TauCeti.schrodingerDuhamel`). So
Duhamel's formula solves the equation in the weak sense, in particular in the sense of
distributions in space (`TauCeti.inner_toLp_schrodingerDuhamel`), and it is the only weak
solution in `C([0, ∞); L²)`: the Cauchy problem is uniquely solvable in the energy class.

## The argument

The Schrödinger group `S(t) = exp(itΔ)` is the unitary group `exp(itω(D))` of the phase
`ω(ξ) = -4π² ‖ξ‖²`, whose generator `A` is `i ω(D)`: its domain consists of the `ψ ∈ L²` with
`ω 𝓕 ψ ∈ L²`, and `𝓕 (A ψ) = i ω 𝓕 ψ` (`TauCeti.complexGenerator_phaseGroup_apply_of_ae_eq`,
`TauCeti.coeFn_fourier_complexGenerator_phaseGroup`). So the test functions above are exactly the
domain of `A`, with `A ψ = i Δψ`. Duhamel's formula is the mild solution of `∂ₜu = A u - i G`
(`TauCeti.isForcedMildSolution_schrodingerDuhamel`), and the unique one
(`TauCeti.Semigroups.IsForcedMildSolution.eq_schrodingerDuhamel`). For the generator of a
unitary group, mild solutions are exactly the weak solutions tested against the domain of `A`
(`TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isForcedMildSolution_iff_forall_inner_eq`);
with `A ψ = i Δψ` that weak formulation is the one above, since `⟪i Δψ, u⟫ = -i ⟪Δψ, u⟫`.

## Main declarations

* `TauCeti.exists_complexGenerator_phaseGroup_laplacianSymbol_eq_I_smul`: if
  `𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ`, then `ψ` lies in the domain of the generator `A` of the Schrödinger group
  and `A ψ = i χ`.
* `TauCeti.coeFn_fourier_neg_I_smul_complexGenerator_phaseGroup_laplacianSymbol`: conversely,
  every `ψ` in the domain of `A` has such a `χ`, namely `-i A ψ`.
* `TauCeti.eqOn_schrodingerDuhamel_iff`: a continuous `L²`-valued function satisfies the weak
  formulation of the Schrödinger equation if and only if it is Duhamel's formula.
* `TauCeti.inner_schrodingerDuhamel`: Duhamel's formula satisfies the weak formulation.
* `TauCeti.inner_toLp_schrodingerDuhamel`: the weak formulation tested against Schwartz functions,
  the Schrödinger equation in the sense of distributions in space.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
* J. M. Ball, *Strongly continuous semigroups, weak solutions, and the variation of constants
  formula*, Proc. Amer. Math. Soc. 63 (1977), 370–373.
-/

public section

noncomputable section

open MeasureTheory Set Complex
open scoped FourierTransform InnerProductSpace Laplacian SchwartzMap

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {f : Lp F 2 (volume : Measure E)} {G : ℝ → Lp F 2 (volume : Measure E)}

/-- **The generator of the Schrödinger group is `i Δ`.** If `χ ∈ L²` is the Laplacian of
`ψ ∈ L²` in the sense that `𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ`, then `ψ` lies in the domain of the generator
`A` of `S(t) = exp(itΔ)`, and `A ψ = i χ`. -/
theorem exists_complexGenerator_phaseGroup_laplacianSymbol_eq_I_smul
    {ψ χ : Lp F 2 (volume : Measure E)}
    (h : 𝓕 χ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 ψ ξ) :
    ∃ hψ : ψ ∈ ((phaseGroup E F laplacianSymbol).complexGenerator
        (isUnitary_phaseGroup laplacianSymbol)).domain,
      (phaseGroup E F laplacianSymbol).complexGenerator (isUnitary_phaseGroup laplacianSymbol)
        ⟨ψ, hψ⟩ = I • χ := by
  have hI : 𝓕 (I • χ) =ᵐ[volume] fun ξ ↦ (I * laplacianSymbol ξ) • 𝓕 ψ ξ := by
    rw [FourierTransform.fourier_smul]
    filter_upwards [Lp.coeFn_smul I (𝓕 χ), h] with ξ h₁ h₂
    rw [h₁, Pi.smul_apply, h₂, smul_smul]
  exact ⟨_, complexGenerator_phaseGroup_apply_of_ae_eq laplacianSymbol hI⟩

/-- Every `ψ` in the domain of the generator `A` of the Schrödinger group has its Laplacian in
`L²`: `χ = -i A ψ` satisfies `𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ`. -/
theorem coeFn_fourier_neg_I_smul_complexGenerator_phaseGroup_laplacianSymbol
    (ψ : ((phaseGroup E F laplacianSymbol).complexGenerator
      (isUnitary_phaseGroup laplacianSymbol)).domain) :
    𝓕 ((-I) • (phaseGroup E F laplacianSymbol).complexGenerator
        (isUnitary_phaseGroup laplacianSymbol) ψ) =ᵐ[volume]
      fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 (ψ : Lp F 2 (volume : Measure E)) ξ := by
  rw [FourierTransform.fourier_smul]
  filter_upwards [Lp.coeFn_smul (-I) (𝓕 ((phaseGroup E F laplacianSymbol).complexGenerator
      (isUnitary_phaseGroup laplacianSymbol) ψ)),
    coeFn_fourier_complexGenerator_phaseGroup laplacianSymbol ψ] with ξ h₁ h₂
  rw [h₁, Pi.smul_apply, h₂]
  simp [smul_smul, ← mul_assoc]

/-- A continuous function on `[0, ∞)` is Duhamel's formula there exactly when it is the mild
solution of `∂ₜu = A u - i G`, `u(0) = f`, for the generator `A` of the Schrödinger group. -/
private theorem eqOn_schrodingerDuhamel_iff_isForcedMildSolution
    (hG : LocallyIntegrableOn G (Ici 0)) {u : ℝ → Lp F 2 (volume : Measure E)} :
    EqOn u (schrodingerDuhamel f G) (Ici 0) ↔
      Semigroups.IsForcedMildSolution (phaseGroup E F laplacianSymbol).toSemigroup.generator
        ((-I) • G) f u :=
  ⟨fun h ↦ (isForcedMildSolution_schrodingerDuhamel f hG).congr h.symm,
    fun h _ ht ↦ h.eq_schrodingerDuhamel ht⟩

omit [CompleteSpace F] in
/-- The weak formulation against a test vector `ψ` in the domain of the generator, with
`A ψ = i χ`, rewritten from the abstract form, where the generator and the forcing `-i G` appear,
to the form where the Laplacian `χ` of `ψ` and `G` appear. -/
private theorem inner_eq_iff_of_eq_I_smul {u : ℝ → Lp F 2 (volume : Measure E)}
    {ψ χ : Lp F 2 (volume : Measure E)} (Aψ : Lp F 2 (volume : Measure E)) (hA : Aψ = I • χ)
    (t : ℝ) :
    ⟪ψ, u t⟫_ℂ = ⟪ψ, f⟫_ℂ - (∫ s in Ioc 0 t, ⟪Aψ, u s⟫_ℂ) + ∫ s in Ioc 0 t, ⟪ψ, ((-I) • G) s⟫_ℂ ↔
      ⟪ψ, u t⟫_ℂ = ⟪ψ, f⟫_ℂ + I * ((∫ s in Ioc 0 t, ⟪χ, u s⟫_ℂ) - ∫ s in Ioc 0 t, ⟪ψ, G s⟫_ℂ) := by
  have h₁ : ∫ s in Ioc 0 t, ⟪Aψ, u s⟫_ℂ = -I * ∫ s in Ioc 0 t, ⟪χ, u s⟫_ℂ := by
    simp only [hA, inner_smul_left, conj_I]
    exact integral_const_mul _ _
  have h₂ : ∫ s in Ioc 0 t, ⟪ψ, ((-I) • G) s⟫_ℂ = -I * ∫ s in Ioc 0 t, ⟪ψ, G s⟫_ℂ := by
    simp only [Pi.smul_apply, inner_smul_right]
    exact integral_const_mul _ _
  rw [h₁, h₂]
  constructor <;> intro h <;> rw [h] <;> ring

/-- **The weak formulation of the Schrödinger equation characterizes Duhamel's formula.** Let
`G` be locally integrable on `[0, ∞)` and let `u` be continuous on `[0, ∞)` with values in
`L²(E, F)`. Then `u` agrees on `[0, ∞)` with Duhamel's formula
`u(t) = S(t) f - i ∫_0^t S(t - s) G(s) ds` if and only if `u` is a weak solution of
`i ∂ₜu + Δu = G`, `u(0) = f`: for all `ψ, χ ∈ L²` with `𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ`, that is `χ = Δψ`,
and all `t ≥ 0`,

`⟪ψ, u t⟫ = ⟪ψ, f⟫ + i (∫_{(0,t]} ⟪χ, u s⟫ ds - ∫_{(0,t]} ⟪ψ, G s⟫ ds)`.

In particular the weak solution is unique in `C([0, ∞); L²)`. -/
theorem eqOn_schrodingerDuhamel_iff (hG : LocallyIntegrableOn G (Ici 0))
    {u : ℝ → Lp F 2 (volume : Measure E)} (hu : ContinuousOn u (Ici 0)) :
    EqOn u (schrodingerDuhamel f G) (Ici 0) ↔
      ∀ ψ χ : Lp F 2 (volume : Measure E),
        (𝓕 χ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 ψ ξ) → ∀ t : ℝ, 0 ≤ t →
          ⟪ψ, u t⟫_ℂ = ⟪ψ, f⟫_ℂ +
            I * ((∫ s in Ioc 0 t, ⟪χ, u s⟫_ℂ) - ∫ s in Ioc 0 t, ⟪ψ, G s⟫_ℂ) := by
  refine (eqOn_schrodingerDuhamel_iff_isForcedMildSolution hG).trans <|
    ((isUnitary_phaseGroup laplacianSymbol).isForcedMildSolution_iff_forall_inner_eq
      (hG.smul (-I)) hu).trans ⟨fun h ψ χ hχ t ht ↦ ?_, fun h ψ t ht ↦ ?_⟩
  · obtain ⟨hψ, hA⟩ := exists_complexGenerator_phaseGroup_laplacianSymbol_eq_I_smul hχ
    exact (inner_eq_iff_of_eq_I_smul _ hA t).1 (h ⟨ψ, hψ⟩ t ht)
  · refine (inner_eq_iff_of_eq_I_smul _
      (χ := (-I) • (phaseGroup E F laplacianSymbol).complexGenerator
        (isUnitary_phaseGroup laplacianSymbol) ψ) ?_ t).2
      (h ψ _ (coeFn_fourier_neg_I_smul_complexGenerator_phaseGroup_laplacianSymbol ψ) t ht)
    rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

/-- **Duhamel's formula is a weak solution** of the Schrödinger equation `i ∂ₜu + Δu = G`,
`u(0) = f`: for all `ψ, χ ∈ L²` with `𝓕 χ = -4π² ‖ξ‖² 𝓕 ψ`, that is `χ = Δψ`, and all `t ≥ 0`,
`⟪ψ, u t⟫ = ⟪ψ, f⟫ + i (∫_{(0,t]} ⟪χ, u s⟫ ds - ∫_{(0,t]} ⟪ψ, G s⟫ ds)`. -/
theorem inner_schrodingerDuhamel (hG : LocallyIntegrableOn G (Ici 0))
    {ψ χ : Lp F 2 (volume : Measure E)}
    (hχ : 𝓕 χ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 ψ ξ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪ψ, schrodingerDuhamel f G t⟫_ℂ = ⟪ψ, f⟫_ℂ +
      I * ((∫ s in Ioc 0 t, ⟪χ, schrodingerDuhamel f G s⟫_ℂ) - ∫ s in Ioc 0 t, ⟪ψ, G s⟫_ℂ) :=
  (eqOn_schrodingerDuhamel_iff hG (continuousOn_schrodingerDuhamel f hG)).1 (fun _ _ ↦ rfl)
    ψ χ hχ t ht

/-- **The Schrödinger equation in the sense of distributions.** Duhamel's formula `u` satisfies
`i ∂ₜu + Δu = G`, `u(0) = f`, tested against every Schwartz function `φ` in space:
`⟪φ, u t⟫ = ⟪φ, f⟫ + i (∫_{(0,t]} ⟪Δφ, u s⟫ ds - ∫_{(0,t]} ⟪φ, G s⟫ ds)` for `t ≥ 0`. -/
theorem inner_toLp_schrodingerDuhamel (hG : LocallyIntegrableOn G (Ici 0)) (φ : 𝓢(E, F))
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪φ.toLp 2, schrodingerDuhamel f G t⟫_ℂ = ⟪φ.toLp 2, f⟫_ℂ +
      I * ((∫ s in Ioc 0 t, ⟪(Δ φ).toLp 2, schrodingerDuhamel f G s⟫_ℂ) -
        ∫ s in Ioc 0 t, ⟪φ.toLp 2, G s⟫_ℂ) := by
  refine inner_schrodingerDuhamel hG ?_ ht
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.laplacian_eq_fourierMultiplierCLM_laplacianSymbol,
    SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  filter_upwards [(𝓕 φ).coeFn_toLp 2, (SchwartzMap.smulLeftCLM F (laplacianSymbol : E → ℝ)
    (𝓕 φ)).coeFn_toLp 2] with ξ h₁ h₂
  rw [h₂, h₁, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_laplacianSymbol,
    Complex.coe_smul]

end TauCeti
