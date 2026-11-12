/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Rotation
public import TauCeti.Geometry.Symplectic.Floer.Stationary
public import TauCeti.MeasureTheory.Measure.Strip
import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# Translations of Floer cylinders in a manifold and a slice for them

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and `H : ℝ → M → ℝ` a time-dependent Hamiltonian. Floer cylinders
`u : ℝ × [0, 1] → M`, solutions of `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical
perturbation `K = H_t dt`, are counted up to the translations `(s, t) ↦ (s + c, t)`. This file
is the manifold-target counterpart of `TauCeti.Geometry.Symplectic.Floer.Translation.Basic` and
`TauCeti.Geometry.Symplectic.Floer.Translation.Slice`, whose target is a symplectic vector space.

**The translation action.** The derivative of a translate `w ↦ u (w + v)` at `w` is the derivative
of `u` at `w + v`, for an arbitrary map `u` (`TauCeti.mfderiv_comp_add_right_apply`). Hence
translating a map and its perturbation data translates the perturbed derivative `du - X_K` and the
energy density (`SmoothTwoForm.perturbedMFDeriv_comp_add_right`,
`SmoothTwoForm.floerEnergyDensity_comp_add_right`). A translate of a Floer cylinder solves the
Floer equation for the translated almost complex structures
(`SmoothTwoForm.mfderiv_comp_add_right_add_apply_sub_hamiltonianVectorField_eq_zero`), which are
the original ones when they do not depend on `s`.

**The slice.** Away from the stationary cylinders the action of `ℝ` is free
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). A
global slice for it is read off from the energy, as for a vector-space target. The strip measure
`TauCeti.stripMeasure (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z))` of the energy
density is the measure on `ℝ` giving each set `A` of `s`-values the Floer energy of `u` over
`A × [0, 1]`. Its total mass is the energy of `u` over the strip, so it is finite and nonzero
exactly for a finite-energy cylinder of nonzero energy, and for a Floer cylinder nonzero energy
means not stationary (`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`).
Since translating `u` by `(c, 0)` translates its energy density, it translates this measure by
`-c`, and the arctan center of the measure is translation equivariant
(`TauCeti.arctanCenter_stripMeasure_comp_add_right`). Hence each translation orbit of a
nonstationary finite-energy Floer cylinder contains exactly one cylinder of center zero
(`IsNondegenerate.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero`), and recentering
is a well-defined section of the quotient by translations
(`TauCeti.arctanCenter_stripMeasure_comp_add_right_add`).

These are statements about classical solutions; no Sobolev completion of the space of cylinders,
compactness or transversality is asserted.

## Main results

* `TauCeti.SmoothTwoForm.floerEnergyDensity_comp_add_right`: the energy density commutes with
  translations of the domain.
* `IsNondegenerate.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero`:
  each translation orbit of a nonstationary finite-energy Floer cylinder meets the slice of center
  zero exactly once.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on moduli spaces of Floer cylinders modulo translation.
-/

public section

open Function MeasureTheory Set
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]

/-! ### Translations of the domain -/

section Translation

/-- The Floer energy density commutes with translations of the domain. -/
theorem floerEnergyDensity_comp_add_right (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (v z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.floerEnergyDensity Ks Kt u (z + v) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, perturbedMFDeriv_comp_add_right]

/-- **Translates of Floer cylinders are Floer cylinders.** If `u` solves the Floer equation
`∂_s u + J_z (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt` at the point
`z + (c, 0)`, then its translate `w ↦ u (w + (c, 0))` solves it at `z` for the translated
structure `J_{z + (c, 0)}`. When `J` does not depend on `s`, this is the same equation. -/
theorem mfderiv_comp_add_right_add_apply_sub_hamiltonianVectorField_eq_zero
    {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}
    {J : (z : ℝ × ℝ) → AlmostComplexStructure (TangentSpace I (u z))} {c : ℝ} {z : ℝ × ℝ}
    (hfloer : mfderiv 𝓘(ℝ, ℝ × ℝ) I u (z + (c, 0)) stdComplexLineReal +
      J (z + (c, 0)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (z + (c, 0)) stdComplexLineImag -
        ω.hamiltonianVectorField (H (z + (c, 0)).2) (u (z + (c, 0)))) = 0) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (c, 0))) z stdComplexLineReal +
      J (z + (c, 0)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (w + (c, 0))) z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u (z + (c, 0)))) = 0 := by
  have hz : (z + (c, 0)).2 = z.2 := by simp
  rw [mfderiv_comp_add_right_apply, mfderiv_comp_add_right_apply, ← hz]
  exact hfloer

end Translation

/-! ### The slice -/

section Slice

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- **The slice for nonstationary Floer cylinders in a manifold.** Let `ω` be nondegenerate on a
finite-dimensional manifold, `H` jointly `C¹`, and let `u` be a `C¹` solution of the Floer equation
for the cylindrical perturbation `K = H_t dt` on the strip `ℝ × [0, 1]`, for almost complex
structures `J z` tamed by `ω`, of finite energy and not stationary. Then exactly one translate
`(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of arctan center `0`. -/
theorem IsNondegenerate.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero
    [FiniteDimensional ℝ E] {J : (z : ℝ × ℝ) → AlmostComplexStructure (TangentSpace I (u z))}
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t)) :
    ∃! c : ℝ, (stripMeasure fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) z)).arctanCenter = 0 := by
  have hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0 := fun hE ↦ by
    obtain ⟨s, t, ht, hne⟩ := hns
    exact hne ((hω.lintegral_floerEnergyDensity_eq_zero_iff hH hu hJ hfloer).1 hE s t ht)
  simpa [← ω.floerEnergyDensity_comp_add_right] using
    TauCeti.existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero hfin hE

end Slice

end TauCeti.SmoothTwoForm
