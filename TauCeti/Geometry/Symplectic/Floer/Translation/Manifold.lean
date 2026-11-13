/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Stationary
public import TauCeti.MeasureTheory.Measure.Strip

/-!
# A slice for the translation action on Floer cylinders in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and `H : ℝ → M → ℝ` a time-dependent Hamiltonian. Floer cylinders
`u : ℝ × [0, 1] → M`, solutions of `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical
perturbation `K = H_t dt`, are counted up to the translations `(s, t) ↦ (s + c, t)`. Away from
the stationary cylinders this action of `ℝ` is free
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`).
This file constructs a global slice for it, as
`TauCeti.Geometry.Symplectic.Floer.Translation.Slice` does for a symplectic vector space target:
a translation-equivariant real-valued *center* of a cylinder, whose zero set meets every orbit of
nonstationary finite-energy cylinders exactly once.

The energy density `e = ω.floerEnergyDensity Ks Kt u` of a map into `M` is intrinsic: it is the
two-form `ω` evaluated on the two components of the perturbed derivative `du - X_K`, and needs no
metric on `M`. Its strip measure `TauCeti.stripMeasure e` gives each set `A` of `s`-values the
Floer energy of `u` over `A × [0, 1]`. Translating `u` by `(c, 0)` translates `e`, since the
cylindrical perturbation is translation invariant
(`TauCeti.SmoothTwoForm.floerEnergyDensity_cylindrical_comp_add_right`), and therefore
translates the strip measure by `-c`. The center of `u` is the arctan center of this measure
(`MeasureTheory.Measure.arctanCenter`), the unique `m` with `∫ arctan (s - m) dE(s) = 0`, defined
when the energy is finite and nonzero. For a Floer cylinder with tamed almost complex structures,
zero energy means stationary
(`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`). Hence:

* the center is translation equivariant: the center of the translate of `u` by `(c, 0)` is the
  center of `u` minus `c`
  (`SmoothTwoForm.arctanCenter_stripMeasure_floerEnergyDensity_cylindrical_comp_add_right`);
* each translation orbit of a nonstationary finite-energy Floer cylinder contains exactly one
  cylinder of center zero, by the theorem
  `IsNondegenerate.existsUnique_arctanCenter_stripMeasure_floerEnergyDensity_comp_add_right_eq_zero`
  in the namespace `TauCeti.SmoothTwoForm`;
* recentering a translate of `u` gives the recentered `u` itself
  (`SmoothTwoForm.comp_add_arctanCenter_stripMeasure_floerEnergyDensity_comp_add_right`), so
  recentering is a well-defined section of the quotient by translations.

The center is continuous along cylinders whose energy densities converge almost everywhere on the
strip without loss of energy, towards a limit of nonzero energy
(`TauCeti.tendsto_arctanCenter_stripMeasure`); this statement only involves the densities, so it
applies to manifold targets as it stands.

These are statements about the action of `ℝ` on classical solutions; no Sobolev completion of the
space of cylinders, compactness or transversality is asserted.

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
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- **Translation equivariance of the energy center.** For the cylindrical perturbation
`K = H_t dt` and a map `u` of finite nonzero energy over the strip, the arctan center of the
energy measure of the translate `(s, t) ↦ u(s + c, t)` is that of `u` minus `c`. -/
theorem arctanCenter_stripMeasure_floerEnergyDensity_cylindrical_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (stripMeasure (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        fun w ↦ u (w + (c, 0)))).arctanCenter =
      (stripMeasure (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u)).arctanCenter - c := by
  rw [funext (ω.floerEnergyDensity_cylindrical_comp_add_right H u c)]
  exact arctanCenter_stripMeasure_comp_add_right hfin hE c

/-- **Recentering is constant on translation orbits.** For the cylindrical perturbation
`K = H_t dt` and a map `u` of finite nonzero energy over the strip, translate any translate
`v = u(· + (c, 0))` of `u` by the arctan center of its energy measure: the result is the translate
of `u` by its own center. So recentering is a section of the quotient by translations, with values
in the slice of center zero. -/
theorem comp_add_arctanCenter_stripMeasure_floerEnergyDensity_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (fun w ↦ u (w + ((stripMeasure (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        fun w ↦ u (w + (c, 0)))).arctanCenter, 0) + (c, 0))) =
      fun w ↦ u (w + ((stripMeasure
        (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u)).arctanCenter, 0)) := by
  rw [arctanCenter_stripMeasure_floerEnergyDensity_cylindrical_comp_add_right hfin hE]
  simp_rw [add_assoc, Prod.mk_add_mk, sub_add_cancel, add_zero]

variable [FiniteDimensional ℝ E] {J : (z : ℝ × ℝ) → AlmostComplexStructure (TangentSpace I (u z))}

/-- **The slice for nonstationary Floer cylinders in a manifold.** Let `H` be a jointly `C¹`
time-dependent Hamiltonian and let `u` be a `C¹` map solving the Floer equation for the
cylindrical perturbation `K = H_t dt` on the strip `ℝ × [0, 1]`, for almost complex structures
`J z` tamed by `ω`. If `u` has finite energy over the strip and is not stationary there, then
exactly one translate `(s, t) ↦ u(s + c, t)` of `u` has energy measure of arctan center `0`. -/
theorem
    IsNondegenerate.existsUnique_arctanCenter_stripMeasure_floerEnergyDensity_comp_add_right_eq_zero
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t)) :
    ∃! c : ℝ, (stripMeasure (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
      fun w ↦ u (w + (c, 0)))).arctanCenter = 0 := by
  -- A nonstationary Floer cylinder has nonzero energy.
  have hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0 := by
    intro hE
    obtain ⟨s, t, ht, hne⟩ := hns
    exact hne ((hω.lintegral_floerEnergyDensity_eq_zero_iff hH hu hJ hfloer).1 hE s t ht)
  simp_rw [fun c ↦ funext (ω.floerEnergyDensity_cylindrical_comp_add_right H u c)]
  exact existsUnique_arctanCenter_stripMeasure_comp_add_right_eq_zero hfin hE

end TauCeti.SmoothTwoForm
