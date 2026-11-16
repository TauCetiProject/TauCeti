/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Algebra.Group.Subgroup.Pointwise

/-!
# The automorphic extension of a local section

Let `Γ' ≤ SL(2, ℝ)`, let `U ⊆ ℍ` and let `k ∈ ℤ`. A function `f` on `U` is *compatible* with the
weight-`k` action of `Γ'` if `f (g • τ) = denom g τ ^ k * f τ` whenever `g ∈ Γ'` and both `τ` and
`g • τ` lie in `U`. For instance, if `U` is precisely invariant, in the sense that an element of
`Γ'` moving a point of `U` into `U` belongs to a subgroup `H`, then every `f` satisfying the
weight-`k` transformation law for the elements of `H` on `U` is compatible. This is the situation
of a local section of the weight-`k` automorphy sheaf on a chart of `Γ \ ℍ`, given on a
precisely invariant disc about an elliptic point or on a horodisc at a cusp.

A compatible function extends uniquely to a function on the saturation `Γ' • U` satisfying the
weight-`k` transformation law for all of `Γ'`. This file constructs that extension,
`Subgroup.automorphyExtension Γ' U k f`, as `τ ↦ denom g τ ^ (-k) * f (g • τ)` for any `g ∈ Γ'`
with `g • τ ∈ U`, and `0` off the saturation:

* the value does not depend on the choice of `g` (`Subgroup.automorphyExtension_eq`), and on `U`
  the extension is `f` (`Subgroup.automorphyExtension_of_mem`);
* the extension satisfies the weight-`k` transformation law for every element of `Γ'` at every
  point of `ℍ` (`Subgroup.automorphyExtension_smul`);
* it is the unique such function agreeing with `f` on `U`, on the saturation
  (`Subgroup.eqOn_automorphyExtension`), and globally among functions vanishing off the saturation
  (`Subgroup.eq_automorphyExtension`);
* if `U` is open and `f` is holomorphic on `U`, the extension is holomorphic on the open set
  `Γ' • U` (`Subgroup.mdifferentiableOn_automorphyExtension`).

Extending the frame of the automorphy sheaf in one chart to the saturation of its domain is what
makes it comparable with the frame of another chart on their overlap: the transition function
between the two trivializations is the coefficient of the extended frame.

## Main declarations

* `Subgroup.automorphyExtension`: the automorphic extension of a compatible local section.
* `Subgroup.automorphyExtension_eq`, `Subgroup.automorphyExtension_of_mem`: its values.
* `Subgroup.automorphyExtension_smul`: its transformation law.
* `Subgroup.eqOn_automorphyExtension`, `Subgroup.eq_automorphyExtension`: its uniqueness.
* `Subgroup.mdifferentiableOn_automorphyExtension`: its holomorphy on the saturation.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3–2.4 and 3.1.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §2.1.
-/

public section

noncomputable section

open Filter Set UpperHalfPlane

open scoped Manifold MatrixGroups Pointwise Topology

namespace Subgroup

variable (Γ' : Subgroup SL(2, ℝ)) (U : Set ℍ) (k : ℤ) (f : ℍ → ℂ)

open Classical in
/-- **The automorphic extension of a local section.** For a function `f` on `U ⊆ ℍ` compatible
with the weight-`k` action of `Γ' ≤ SL(2, ℝ)`, this is the function
`τ ↦ denom g τ ^ (-k) * f (g • τ)` on the saturation `Γ' • U`, for any `g ∈ Γ'` with
`g • τ ∈ U` (`Subgroup.automorphyExtension_eq`), extended by `0` off the saturation. It satisfies
the weight-`k` transformation law for all of `Γ'` (`Subgroup.automorphyExtension_smul`). -/
def automorphyExtension (τ : ℍ) : ℂ :=
  if h : ∃ g ∈ Γ', g • τ ∈ U then
    denom (Matrix.SpecialLinearGroup.mapGL ℝ h.choose) τ ^ (-k) * f (h.choose • τ)
  else 0

variable {Γ' U k f}

/-- Off the saturation `Γ' • U` the extension vanishes. -/
@[simp]
theorem automorphyExtension_of_notMem {τ : ℍ} (hτ : τ ∉ (Γ' : Set SL(2, ℝ)) • U) :
    automorphyExtension Γ' U k f τ = 0 := by
  rw [automorphyExtension, dite_eq_right (fun h ↦ absurd h
    (mem_smul_set_iff_exists_smul_mem.not.mp hτ))]

variable (hf : ∀ g ∈ Γ', ∀ τ ∈ U, g • τ ∈ U →
  f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ)
include hf

/-- **The extension is well defined.** For every `g ∈ Γ'` moving `τ` into `U`, the extension at
`τ` is `denom g τ ^ (-k) * f (g • τ)`. -/
theorem automorphyExtension_eq {g : SL(2, ℝ)} (hg : g ∈ Γ') {τ : ℍ} (hτ : g • τ ∈ U) :
    automorphyExtension Γ' U k f τ =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ (-k) * f (g • τ) := by
  have h : ∃ g ∈ Γ', g • τ ∈ U := ⟨g, hg, hτ⟩
  rw [automorphyExtension, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hg₀, hτ₀⟩ := h.choose_spec
  set g₀ := h.choose
  -- `g = (g * g₀⁻¹) * g₀`, and `g * g₀⁻¹ ∈ Γ'` carries the point `g₀ • τ` of `U` into `U`
  have hgτ : (g * g₀⁻¹) • (g₀ • τ) = g • τ := by rw [smul_smul, inv_mul_cancel_right]
  have hlaw := hf (g * g₀⁻¹) (Γ'.mul_mem hg (Γ'.inv_mem hg₀)) _ hτ₀ (hgτ ▸ hτ)
  have hden := Matrix.SpecialLinearGroup.denom_mapGL_mul (g * g₀⁻¹) g₀ τ
  rw [inv_mul_cancel_right] at hden
  rw [hgτ] at hlaw
  rw [hlaw, hden, mul_zpow]
  linear_combination -(denom (Matrix.SpecialLinearGroup.mapGL ℝ g₀) τ ^ (-k) * f (g₀ • τ)) *
    zpow_neg_mul_zpow_self k (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ (g * g₀⁻¹))
      (g₀ • τ))

/-- **On `U` the extension is the given function.** -/
@[simp]
theorem automorphyExtension_of_mem {τ : ℍ} (hτ : τ ∈ U) :
    automorphyExtension Γ' U k f τ = f τ := by
  rw [automorphyExtension_eq hf Γ'.one_mem (by rwa [one_smul]), one_smul, map_one, denom_one,
    one_zpow, one_mul]

/-- **The transformation law of the extension.** The extension satisfies the weight-`k`
transformation law for every element of `Γ'` at every point of the upper half-plane. -/
theorem automorphyExtension_smul {g : SL(2, ℝ)} (hg : g ∈ Γ') (τ : ℍ) :
    automorphyExtension Γ' U k f (g • τ) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * automorphyExtension Γ' U k f τ := by
  by_cases hτ : ∃ h ∈ Γ', h • τ ∈ U
  · obtain ⟨h, hh, hhτ⟩ := hτ
    have hgτ : (h * g⁻¹) • (g • τ) = h • τ := by rw [smul_smul, inv_mul_cancel_right]
    have hden := Matrix.SpecialLinearGroup.denom_mapGL_mul (h * g⁻¹) g τ
    rw [inv_mul_cancel_right] at hden
    rw [automorphyExtension_eq hf (Γ'.mul_mem hh (Γ'.inv_mem hg)) (hgτ ▸ hhτ),
      automorphyExtension_eq hf hh hhτ, hgτ, hden, mul_zpow]
    linear_combination
      -(denom (Matrix.SpecialLinearGroup.mapGL ℝ (h * g⁻¹)) ((g • τ : ℍ) : ℂ) ^ (-k) * f (h • τ)) *
        zpow_neg_mul_zpow_self k (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) τ)
  · have hgτ : g • τ ∉ (Γ' : Set SL(2, ℝ)) • U := by
      rw [mem_smul_set_iff_exists_smul_mem]
      rintro ⟨h, hh, hhτ⟩
      exact hτ ⟨h * g, Γ'.mul_mem hh hg, by rwa [mul_smul]⟩
    rw [automorphyExtension_of_notMem hgτ, automorphyExtension_of_notMem
      (mem_smul_set_iff_exists_smul_mem.not.mpr hτ), mul_zero]

omit hf in
/-- **Uniqueness of the extension on the saturation.** A function satisfying the weight-`k`
transformation law for every element of `Γ'` and agreeing with `f` on `U` agrees with the
extension on the saturation `Γ' • U`. The compatibility of `f` follows from these hypotheses. -/
theorem eqOn_automorphyExtension {F : ℍ → ℂ} (hF : ∀ g ∈ Γ', ∀ τ : ℍ,
    F (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * F τ) (hFU : EqOn F f U) :
    EqOn F (automorphyExtension Γ' U k f) ((Γ' : Set SL(2, ℝ)) • U) := by
  intro τ hτ
  obtain ⟨g, hg, hgτ⟩ := mem_smul_set_iff_exists_smul_mem.mp hτ
  have hf : ∀ g ∈ Γ', ∀ τ ∈ U, g • τ ∈ U →
      f (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * f τ :=
    fun g hg τ hτ hgτ ↦ by rw [← hFU hgτ, ← hFU hτ, hF g hg τ]
  rw [automorphyExtension_eq hf hg hgτ, ← hFU hgτ, hF g hg τ, ← mul_assoc,
    zpow_neg_mul_zpow_self k (denom_ne_zero _ _), one_mul]

omit hf in
/-- **Uniqueness of the extension.** A function satisfying the weight-`k` transformation law for
every element of `Γ'`, agreeing with `f` on `U` and vanishing off the saturation `Γ' • U` is the
extension. -/
theorem eq_automorphyExtension {F : ℍ → ℂ} (hF : ∀ g ∈ Γ', ∀ τ : ℍ,
    F (g • τ) = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) τ ^ k * F τ) (hFU : EqOn F f U)
    (hF0 : ∀ τ ∉ (Γ' : Set SL(2, ℝ)) • U, F τ = 0) :
    F = automorphyExtension Γ' U k f := by
  ext τ
  by_cases hτ : τ ∈ (Γ' : Set SL(2, ℝ)) • U
  · exact eqOn_automorphyExtension hF hFU hτ
  · rw [hF0 τ hτ, automorphyExtension_of_notMem hτ]

/-- **The extension is holomorphic on the saturation.** If `U` is open and `f` is holomorphic on
`U`, then the extension is holomorphic on the open set `Γ' • U`. -/
theorem mdifferentiableOn_automorphyExtension (hU : IsOpen U)
    (hfd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (automorphyExtension Γ' U k f) ((Γ' : Set SL(2, ℝ)) • U) := by
  intro τ hτ
  obtain ⟨g, hg, hgτ⟩ := mem_smul_set_iff_exists_smul_mem.mp hτ
  -- near `τ` the extension is `σ ↦ denom g σ ^ (-k) * f (g • σ)` for the same `g`
  have hnhds : (fun σ : ℍ ↦ g • σ) ⁻¹' U ∈ 𝓝 τ :=
    (continuous_const_smul g).continuousAt.preimage_mem_nhds (hU.mem_nhds hgτ)
  have heq : automorphyExtension Γ' U k f =ᶠ[𝓝 τ]
      fun σ ↦ denom (Matrix.SpecialLinearGroup.mapGL ℝ g) σ ^ (-k) * f (g • σ) := by
    filter_upwards [hnhds] with σ hσ
    exact automorphyExtension_eq hf hg hσ
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ ↦ f (g • σ)) τ := by
    refine MDifferentiableAt.comp (g := f) (f := fun σ : ℍ ↦ g • σ) τ
      ((hfd _ hgτ).mdifferentiableAt (hU.mem_nhds hgτ)) ?_
    have h := mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) τ
    simpa only [Matrix.SpecialLinearGroup.mapGL_smul] using h
  exact (((mdifferentiable_denom_zpow _ _ τ).mul hcomp).congr_of_eventuallyEq
    heq).mdifferentiableWithinAt

end Subgroup
