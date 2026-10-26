/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry

/-!
# Dilation invariance of harmonic functions

`TauCeti.Analysis.InnerProductSpace.Laplacian.Basic` records invariance under rigid motions and the
Laplacian scaling law under affine homotheties. This file transports the homothety bookkeeping to
harmonicity: under the right-composition `AffineMap.homothety a c`, harmonicity is preserved and
reflected when `c ≠ 0`.

These lemmas let mean-value, maximum-principle, and Poisson-kernel arguments normalize balls by
translating and rescaling without reproving the Laplacian calculation each time.

## Main declarations

* `TauCeti.harmonicAt_comp_homothety_right_iff`: harmonicity is invariant under nonzero
  homothety about an arbitrary center.
* `TauCeti.harmonicOnNhd_comp_homothety_right_iff`: set-level nonzero homothety invariance.
* `TauCeti.harmonicAt_comp_smul_right_iff`: harmonicity is invariant under nonzero dilation.
* `TauCeti.harmonicOnNhd_comp_smul_right_iff`: set-level nonzero dilation invariance.
* `TauCeti.harmonicAt_comp_const_add_smul_iff`: harmonicity is invariant under the affine
  normalization `z ↦ x + c • z` with nonzero scale.
* `TauCeti.harmonicOnNhd_comp_const_add_smul_iff`: set-level affine normalization invariance.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Harmonicity is invariant under nonzero dilation.**

For `c ≠ 0`, the function `y ↦ f (c • y)` is harmonic at `x` iff `f` is harmonic at
`c • x`. -/
theorem harmonicAt_comp_smul_right_iff (c : ℝ) (hc : c ≠ 0) {f : E → F} {x : E} :
    HarmonicAt (fun y ↦ f (c • y)) x ↔ HarmonicAt f (c • x) := by
  let l : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have hl : ⇑l = fun y : E ↦ c • y := by
    funext y
    simp only [l, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0]
  have hcd : ContDiffAt ℝ 2 (fun y ↦ f (c • y)) x ↔ ContDiffAt ℝ 2 f (c • x) := by
    have h := l.contDiffAt_comp_iff (f := f) (n := 2) (x := l x)
    rw [l.symm_apply_apply] at h
    simpa only [hl, Function.comp_def] using h
  have hmap : Filter.map (fun y : E ↦ c • y) (𝓝 x) = 𝓝 (c • x) := by
    simpa only [hl] using l.map_nhds_eq x
  have hlap : (Δ (fun y ↦ f (c • y)) =ᶠ[𝓝 x] 0) ↔ (Δ f =ᶠ[𝓝 (c • x)] 0) := by
    rw [laplacian_comp_smul_right, ← hmap]
    simp only [Filter.EventuallyEq, Filter.eventually_map, Pi.zero_apply, smul_eq_zero,
      pow_ne_zero 2 hc, false_or]
  exact and_congr hcd hlap

/-- Harmonicity on a neighbourhood of a set is invariant under nonzero dilation. -/
theorem harmonicOnNhd_comp_smul_right_iff (c : ℝ) (hc : c ≠ 0) {f : E → F} {s : Set E} :
    HarmonicOnNhd (fun y ↦ f (c • y)) ((fun y ↦ c • y) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  simp only [HarmonicOnNhd, Set.mem_preimage, harmonicAt_comp_smul_right_iff c hc]
  let l : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  simpa only [l, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0] using
    (l.surjective.forall (p := fun y ↦ y ∈ s → HarmonicAt f y)).symm

/-- **Harmonicity is invariant under the affine normalization `z ↦ x + c • z`** when the scale
is nonzero.

For `c ≠ 0`, the function `z ↦ f (x + c • z)` is harmonic at `y` iff `f` is harmonic at
`x + c • y`. -/
theorem harmonicAt_comp_const_add_smul_iff (x : E) {c : ℝ} (hc : c ≠ 0) {f : E → F} {y : E} :
    HarmonicAt (fun z ↦ f (x + c • z)) y ↔ HarmonicAt f (x + c • y) := by
  simpa only [add_comm x] using
    (harmonicAt_comp_smul_right_iff c hc (f := fun w ↦ f (w + x)) (x := y)).trans
      harmonicAt_comp_add_right_iff

/-- **Harmonicity on a neighbourhood of a set is invariant under the affine normalization
`z ↦ x + c • z`** when the scale is nonzero.

For `c ≠ 0`, the function `z ↦ f (x + c • z)` is harmonic near `(fun z ↦ x + c • z) ⁻¹' s`
iff `f` is harmonic near `s`. -/
theorem harmonicOnNhd_comp_const_add_smul_iff (x : E) {c : ℝ} (hc : c ≠ 0) {f : E → F} {s : Set E} :
    HarmonicOnNhd (fun z ↦ f (x + c • z)) ((fun z ↦ x + c • z) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  simpa only [Set.preimage_preimage, Function.comp_def, add_comm x] using
    (harmonicOnNhd_comp_smul_right_iff c hc (f := fun w ↦ f (w + x))
      (s := (fun w ↦ w + x) ⁻¹' s)).trans (harmonicOnNhd_comp_add_right_iff x)

/-- **Harmonicity is invariant under nonzero homothety.**

For `c ≠ 0`, the function `y ↦ f (AffineMap.homothety a c y)` is harmonic at `x` iff `f`
is harmonic at `AffineMap.homothety a c x`. -/
theorem harmonicAt_comp_homothety_right_iff (a : E) (c : ℝ) (hc : c ≠ 0) {f : E → F} {x : E} :
    HarmonicAt (fun y ↦ f (AffineMap.homothety a c y)) x ↔
      HarmonicAt f (AffineMap.homothety a c x) := by
  simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg,
    add_comm a] using
    (harmonicAt_comp_add_right_iff (f := fun z ↦ f (a + c • z)) (x := x) (a := -a)).trans
      (harmonicAt_comp_const_add_smul_iff a hc)

/-- Harmonicity on a neighbourhood of a set is invariant under nonzero homothety. -/
theorem harmonicOnNhd_comp_homothety_right_iff (a : E) (c : ℝ) (hc : c ≠ 0) {f : E → F}
    {s : Set E} :
    HarmonicOnNhd (fun y ↦ f (AffineMap.homothety a c y))
        ((fun y ↦ AffineMap.homothety a c y) ⁻¹' s) ↔
      HarmonicOnNhd f s := by
  simpa only [Set.preimage_preimage, Function.comp_def, AffineMap.homothety_apply,
    vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, add_comm a] using
    (harmonicOnNhd_comp_add_right_iff (f := fun z ↦ f (a + c • z))
      (s := (fun z ↦ a + c • z) ⁻¹' s) (-a)).trans
      (harmonicOnNhd_comp_const_add_smul_iff a hc)

end TauCeti
