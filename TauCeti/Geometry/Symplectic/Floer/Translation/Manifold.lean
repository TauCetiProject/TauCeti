/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Stationary
public import TauCeti.MeasureTheory.Measure.ArctanCenter
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
`SmoothTwoForm.floerEnergyDensity_comp_add_right`), and translations preserve the energy
(`SmoothTwoForm.lintegral_floerEnergyDensity_comp_add_right`). A translate of a Floer cylinder
solves the Floer equation for the translated almost complex structures
(`SmoothTwoForm.mfderiv_comp_add_right_add_apply_sub_hamiltonianVectorField_eq_zero`), which are
the original ones when they do not depend on `s`.

**The slice.** Away from the stationary cylinders the action of `ℝ` is free
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). A
global slice for it is read off from the energy, as for a vector-space target. The *strip energy
measure* `SmoothTwoForm.stripEnergyMeasure ω Ks Kt u` is the measure on `ℝ` giving each set `A` of
`s`-values the Floer energy of `u` over `A × [0, 1]`. Its total mass is the energy of `u` over the
strip, so it is finite and nonzero exactly for a finite-energy cylinder of nonzero energy, and for a
Floer cylinder nonzero energy means not stationary
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`). Translating `u` by
`(c, 0)` translates this measure by `-c` (`SmoothTwoForm.stripEnergyMeasure_comp_add_right`). The
*center* of `u` is the arctan center of its strip energy measure
(`MeasureTheory.Measure.arctanCenter`), so it is translation equivariant: the center of the
translate of `u` by `(c, 0)` is the center of `u` minus `c`
(`SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`). Hence:

* each translation orbit of a nonstationary finite-energy Floer cylinder contains exactly one
  cylinder of center zero
  (`IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero`);
* recentering a translate of `u` gives the recentered `u` itself
  (`SmoothTwoForm.comp_add_arctanCenter_stripEnergyMeasure_comp_add_right`), so recentering is a
  well-defined section of the quotient by translations.

These are statements about classical solutions; no Sobolev completion of the space of cylinders,
compactness or transversality is asserted.

## Main definitions

* `TauCeti.SmoothTwoForm.stripEnergyMeasure`: the distribution along the strip of the Floer energy
  of a map into a manifold.

## Main results

* `TauCeti.SmoothTwoForm.perturbedMFDeriv_comp_add_right`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_comp_add_right`: the perturbed derivative and the
  energy density commute with translations of the domain.
* `TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_comp_add_right`: translations preserve the
  energy.
* `TauCeti.SmoothTwoForm.stripEnergyMeasure_comp_add_right`: translating the cylinder translates
  its strip energy measure.
* `TauCeti.SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`: the center
  is translation equivariant.
* `IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero`:
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

/-- The perturbed derivative commutes with translations of the domain: translating the map and
the perturbation data by `v` translates the perturbed derivative by `v`. No differentiability is
needed. -/
theorem perturbedMFDeriv_comp_add_right (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (v z : ℝ × ℝ) :
    ω.perturbedMFDeriv (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.perturbedMFDeriv Ks Kt u (z + v) := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, mfderiv_comp_add_right_apply]

/-- The Floer energy density commutes with translations of the domain. -/
theorem floerEnergyDensity_comp_add_right (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (v z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.floerEnergyDensity Ks Kt u (z + v) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, perturbedMFDeriv_comp_add_right]

/-- **Translations preserve the energy.** Translating a map and its perturbation data by `v`
preserves the energy: the energy of the translate over `(· + v) ⁻¹' S` is the energy of the
original over `S`. -/
theorem lintegral_floerEnergyDensity_comp_add_right (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    ∫⁻ z in (· + v) ⁻¹' S, ENNReal.ofReal
        (ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [floerEnergyDensity_comp_add_right]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight v)
    (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)) S

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

/-! ### The strip energy measure -/

section Measure

variable (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M)

/-- The *strip energy measure* of a map `u` of the strip `ℝ × [0, 1]` into a manifold: the
measure on `ℝ` giving each set `A` of `s`-values the Floer energy of `u` over `A × [0, 1]` for
the perturbation data `Ks`, `Kt` (`TauCeti.SmoothTwoForm.stripEnergyMeasure_apply`). It is the
pushforward to the `s`-axis of the energy density on the strip. -/
noncomputable def stripEnergyMeasure : Measure ℝ :=
  ((volume.restrict ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1)).withDensity fun z ↦
    ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)).map Prod.fst

/-- The strip energy measure of a measurable set `A` is the energy over `A × [0, 1]`. -/
theorem stripEnergyMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) :
    ω.stripEnergyMeasure Ks Kt u A =
      ∫⁻ z in A ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  rw [stripEnergyMeasure, Measure.map_apply measurable_fst hA,
    withDensity_apply _ (measurable_fst hA), Measure.restrict_restrict (measurable_fst hA),
    ← prod_univ, prod_inter_prod, inter_univ, univ_inter]

/-- The total mass of the strip energy measure is the energy over the strip. -/
theorem stripEnergyMeasure_univ :
    ω.stripEnergyMeasure Ks Kt u univ =
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) :=
  ω.stripEnergyMeasure_apply Ks Kt u MeasurableSet.univ

variable {ω Ks Kt u}

/-- The strip energy measure of a map of finite energy is finite. -/
theorem isFiniteMeasure_stripEnergyMeasure
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) ≠ ⊤) :
    IsFiniteMeasure (ω.stripEnergyMeasure Ks Kt u) :=
  ⟨by rw [stripEnergyMeasure_univ]; exact hfin.lt_top⟩

/-- The strip energy measure vanishes exactly when the energy over the strip does. -/
theorem stripEnergyMeasure_eq_zero_iff :
    ω.stripEnergyMeasure Ks Kt u = 0 ↔
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) = 0 := by
  rw [← Measure.measure_univ_eq_zero, stripEnergyMeasure_univ]

variable (ω Ks Kt u)

/-- **Translations translate the strip energy measure.** Translating a map and its perturbation
data by `(c, 0)` translates its strip energy measure by `-c`. -/
theorem stripEnergyMeasure_comp_add_right (c : ℝ) :
    ω.stripEnergyMeasure (fun w ↦ Ks (w + (c, 0))) (fun w ↦ Kt (w + (c, 0)))
        (fun w ↦ u (w + (c, 0))) =
      (ω.stripEnergyMeasure Ks Kt u).map (· - c) := by
  ext A hA
  have hpre : A ×ˢ Icc (0 : ℝ) 1 = (· + (c, 0)) ⁻¹' (((· - c) ⁻¹' A) ×ˢ Icc 0 1) := by
    ext z
    simp
  rw [Measure.map_apply (measurable_sub_const c) hA, stripEnergyMeasure_apply _ _ _ _ hA,
    stripEnergyMeasure_apply _ _ _ _ (measurable_sub_const c hA), hpre,
    lintegral_floerEnergyDensity_comp_add_right]

/-- For the cylindrical perturbation `K = H_t dt`, translating the map by `(c, 0)` translates its
strip energy measure by `-c`. -/
theorem stripEnergyMeasure_cylindrical_comp_add_right (H : ℝ → M → ℝ) (c : ℝ) :
    ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) =
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).map (· - c) := by
  simpa using ω.stripEnergyMeasure_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u c

end Measure

/-! ### The slice -/

section Slice

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- **Translation equivariance of the energy center.** For the cylindrical perturbation
`K = H_t dt` and a map `u` of finite nonzero energy over the strip, the arctan center of the strip
energy measure of the translate `(s, t) ↦ u(s + c, t)` is that of `u` minus `c`. -/
theorem arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter - c := by
  have := isFiniteMeasure_stripEnergyMeasure hfin
  have : NeZero (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u) :=
    ⟨fun h ↦ hE (stripEnergyMeasure_eq_zero_iff.1 h)⟩
  simp_rw [stripEnergyMeasure_cylindrical_comp_add_right, sub_eq_add_neg,
    Measure.arctanCenter_map_add]

/-- **Each translation orbit meets the slice once.** For the cylindrical perturbation `K = H_t dt`
and a map `u` of finite nonzero energy over the strip, there is exactly one translation
`(s, t) ↦ (s + c, t)` after which the arctan center of the strip energy measure is `0`; it is
translation by the center of `u`. -/
theorem existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) :
    ∃! c : ℝ,
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
        0 := by
  simp_rw [arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right hfin hE, sub_eq_zero]
  exact ⟨_, rfl, fun _ h ↦ h.symm⟩

/-- **The slice for nonstationary Floer cylinders in a manifold.** Let `ω` be nondegenerate on a
finite-dimensional manifold, `H` jointly `C¹`, and let `u` be a `C¹` solution of the Floer equation
for the cylindrical perturbation `K = H_t dt` on the strip `ℝ × [0, 1]`, for almost complex
structures `J z` tamed by `ω`, of finite energy and not stationary. Then exactly one translate
`(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of arctan center `0`. -/
theorem IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero
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
    ∃! c : ℝ,
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
        0 := by
  refine SmoothTwoForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero hfin
    fun hE ↦ ?_
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((hω.lintegral_floerEnergyDensity_eq_zero_iff hH hu hJ hfloer).1 hE s t ht)

/-- **Recentering is constant on translation orbits.** For the cylindrical perturbation
`K = H_t dt` and a map `u` of finite nonzero energy over the strip, translate any translate
`v = u(· + (c, 0))` of `u` by the arctan center of its strip energy measure: the result is the
translate of `u` by its own center. So recentering is a section of the quotient by translations,
with values in the slice of center zero. -/
theorem comp_add_arctanCenter_stripEnergyMeasure_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (fun w ↦ u (w + ((ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2)
        fun w ↦ u (w + (c, 0))).arctanCenter, 0) + (c, 0))) =
      fun w ↦ u (w + ((ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter, 0)) := by
  rw [arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right hfin hE]
  set m := (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter
  have hm : ((m - c, 0) + (c, 0) : ℝ × ℝ) = (m, 0) := by ext <;> simp
  simp_rw [add_assoc, hm]

end Slice

end TauCeti.SmoothTwoForm
