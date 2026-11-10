/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
public import TauCeti.MeasureTheory.Measure.Strip

/-!
# A slice for the translation action on Floer cylinders

Floer cylinders `u : ℝ × [0, 1] → V`, solutions of `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the
cylindrical perturbation `K = H_t dt`, are counted up to the translations
`(s, t) ↦ (s + c, t)`. Away from the stationary cylinders this action of `ℝ` is free
(`TauCeti.SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). This file
constructs a global slice for it: a translation-equivariant real-valued *center* of a cylinder,
whose zero set meets every orbit of nonstationary finite-energy cylinders exactly once.

The center is read off from the energy. The strip measure
`TauCeti.stripMeasure (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z))` of the energy
density is the measure on `ℝ` giving each set `A` of `s`-values the Floer energy of `u` over
`A × [0, 1]`. Its total mass is the energy of `u` over the strip, so it is finite and nonzero
exactly for a finite-energy cylinder of nonzero energy; for a solution of the Floer equation,
nonzero energy means not stationary
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`). Translating `u` and its
perturbation data by `(c, 0)` translates the energy density
(`TauCeti.SymplecticForm.floerEnergyDensity_comp_add_right`), hence translates this measure by
`-c` (`TauCeti.stripMeasure_comp_add_right`). The center of `u` is the arctan center of its strip
energy measure (`MeasureTheory.Measure.arctanCenter`), the unique `m` with
`∫ arctan (s - m) dE(s) = 0`. It is therefore equivariant: the center of the translate of `u` by
`(c, 0)` is the center of `u` minus `c` (`TauCeti.arctanCenter_stripMeasure_comp_add_right`).
Hence:

* each orbit of a nonstationary finite-energy Floer cylinder contains exactly one cylinder of
  center zero, the translate of `u` by its center
  (`SymplecticForm.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero_of_floer`);
* recentering a translate of `u` gives the recentered `u` itself
  (`TauCeti.arctanCenter_stripMeasure_comp_add_right_add`), so recentering is a well-defined
  section of the quotient by translations.

The center is continuous for the weak topology on energy measures
(`MeasureTheory.FiniteMeasure.tendsto_arctanCenter`), so cylinders whose finite energy measures
converge weakly to a nonzero limit have converging centers. Unlike the usual action level slice
`A_H(u(0, ·)) = a`, which needs a level strictly between the actions of the two ends and the strict
monotonicity of the action along the cylinder, this slice needs neither unique continuation nor a
choice of level.

The target is a symplectic vector space and no Sobolev completion of the space of cylinders is
considered: the statements are about the action of `ℝ` on classical solutions.

## Main results

* `SymplecticForm.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero_of_floer`:
  each translation orbit of a nonstationary finite-energy Floer cylinder meets the slice of center
  zero exactly once.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on moduli spaces of Floer cylinders modulo translation.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Slice

variable {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **The slice for nonstationary Floer cylinders.** Let `u` be `C¹` on a neighbourhood of the
strip `ℝ × [0, 1]`, solve the Floer equation for the cylindrical perturbation `K = H_t dt` and
almost complex structures tamed by `ω`, have finite energy, and not be stationary. Then exactly
one translate `(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of arctan center `0`. -/
theorem existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero_of_floer
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
    ∃! c : ℝ, (stripMeasure fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) z)).arctanCenter = 0 := by
  have hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0 := fun hE ↦ by
    obtain ⟨s, t, ht, hne⟩ := hns
    exact hne ((ω.lintegral_floerEnergyDensity_eq_zero_iff hH hU hu hRU hJ hfloer).1 hE s t ht)
  simpa [← ω.floerEnergyDensity_comp_add_right] using
    existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero hfin hE

end Slice

end TauCeti.SymplecticForm
