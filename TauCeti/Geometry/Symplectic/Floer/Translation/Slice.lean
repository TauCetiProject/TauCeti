/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
public import TauCeti.Geometry.Symplectic.Floer.Translation.Manifold

/-!
# A slice for the translation action on Floer cylinders in a vector space

Floer cylinders `u : ℝ × [0, 1] → V` in a symplectic vector space, solutions of
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt`, are counted up
to the translations `(s, t) ↦ (s + c, t)`. Away from the stationary cylinders this action of `ℝ`
is free (`TauCeti.SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`).
This file specializes to a vector-space target the global slice of
`TauCeti.Geometry.Symplectic.Floer.Translation.Manifold`, for the constant form `ω.constSmooth`.

The center of a cylinder is the arctan center (`MeasureTheory.Measure.arctanCenter`) of its strip
energy measure `TauCeti.SmoothTwoForm.stripEnergyMeasure ω.constSmooth Ks Kt u`, the measure on
`ℝ` giving each set `A` of `s`-values the Floer energy of `u` over `A × [0, 1]`, which for a
constant form is the energy of the vector-space theory
(`TauCeti.SymplecticForm.floerEnergyDensity_constSmooth`). Translation equivariance of the center
and the uniqueness of the recentered cylinder in each orbit are the constant-form cases of
`TauCeti.SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`,
`TauCeti.SmoothTwoForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero` and
`TauCeti.SmoothTwoForm.comp_add_arctanCenter_stripEnergyMeasure_comp_add_right`. For a solution of
the Floer equation, nonzero energy means not stationary
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`), so each orbit of
nonstationary finite-energy Floer cylinders meets the slice of center zero exactly once.

Unlike the usual action level slice `A_H(u(0, ·)) = a`, which needs a level strictly between the
actions of the two ends and the strict monotonicity of the action along the cylinder, this slice
needs neither unique continuation nor a choice of level. The center is continuous along cylinders
whose energy densities converge without loss of energy.

No Sobolev completion of the space of cylinders is considered: the statements are about the action
of `ℝ` on classical solutions.

## Main results

* `SymplecticForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer`:
  each translation orbit of a nonstationary finite-energy Floer cylinder meets the slice of center
  zero exactly once.
* `TauCeti.SymplecticForm.tendsto_arctanCenter_stripEnergyMeasure`: the center is continuous along
  cylinders whose energy densities converge without loss of energy.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on moduli spaces of Floer cylinders modulo translation.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The slice for nonstationary Floer cylinders.** Let `u` be `C¹` on a neighbourhood of the
strip `ℝ × [0, 1]`, solve the Floer equation for the cylindrical perturbation `K = H_t dt` and
almost complex structures tamed by `ω`, have finite energy, and not be stationary. Then exactly
one translate `(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of arctan center `0`. -/
theorem existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer
    {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {J : ℝ × ℝ → AlmostComplexStructure V} {U : Set (ℝ × ℝ)}
    (hH : ContDiff ℝ 1 (Function.uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t)) :
    ∃! c : ℝ, (ω.constSmooth.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2)
      fun w ↦ u (w + (c, 0))).arctanCenter = 0 := by
  refine SmoothTwoForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero
    (by simpa only [floerEnergyDensity_constSmooth] using hfin) fun hE ↦ ?_
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((ω.lintegral_floerEnergyDensity_eq_zero_iff hH hU hu hRU hJ hfloer).1
    (by simpa only [floerEnergyDensity_constSmooth] using hE) s t ht)

/-- **Continuity of the energy center, for a vector-space target.** If the energy densities of maps
`u i` of the strip `ℝ × [0, 1]` into a symplectic vector space are integrable, nonnegative almost
everywhere and converge almost everywhere on the strip to the integrable energy density of `u₀`,
and the energies of `u i` converge to the nonzero energy of `u₀`, then the arctan centers of the
strip energy measures of `u i` converge to that of `u₀`. This is the constant-form case of
`TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure`. -/
theorem tendsto_arctanCenter_stripEnergyMeasure {ω : SymplecticForm V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {u : ι → ℝ × ℝ → V} {u₀ : ℝ × ℝ → V}
    (hint : ∀ i, IntegrableOn (ω.floerEnergyDensity Ks Kt (u i)) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hint₀ : IntegrableOn (ω.floerEnergyDensity Ks Kt u₀) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hnonneg : ∀ i, 0 ≤ᵐ[volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)]
      ω.floerEnergyDensity Ks Kt (u i))
    (hlim : ∀ᵐ z ∂volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1),
      Tendsto (fun i ↦ ω.floerEnergyDensity Ks Kt (u i) z) l
        (𝓝 (ω.floerEnergyDensity Ks Kt u₀ z)))
    (henergy : Tendsto
      (fun i ↦ ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt (u i) z) l
      (𝓝 (∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u₀ z)))
    (hE : ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u₀ z ≠ 0) :
    Tendsto (fun i ↦ (ω.constSmooth.stripEnergyMeasure Ks Kt (u i)).arctanCenter) l
      (𝓝 (ω.constSmooth.stripEnergyMeasure Ks Kt u₀).arctanCenter) := by
  have he (v : ℝ × ℝ → V) :
      ω.constSmooth.floerEnergyDensity Ks Kt v = ω.floerEnergyDensity Ks Kt v :=
    funext (floerEnergyDensity_constSmooth ω Ks Kt v)
  exact SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure (by simpa only [he] using hint)
    (by simpa only [he] using hint₀) (by simpa only [he] using hnonneg)
    (by simpa only [he] using hlim) (by simpa only [he] using henergy)
    (by simpa only [he] using hE)

end TauCeti.SymplecticForm
