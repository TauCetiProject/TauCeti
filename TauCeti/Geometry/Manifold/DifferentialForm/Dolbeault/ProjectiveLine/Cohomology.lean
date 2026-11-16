/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Cohomology
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ProjectiveLine.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace

/-!
# Dolbeault cohomology of the projective line

On the complex projective line `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)`, the operator `∂bar` on smooth functions
with values in a complex Banach space `F` has kernel the constants and cokernel zero: every smooth
`(0,1)`-form is `∂bar` of a smooth function. So `H^(0,0)_∂bar(ℂℙ¹; F) ≃ F` and
`H^(0,1)_∂bar(ℂℙ¹; F) = 0`, and for `F = ℂ` the index of `∂bar` is `2 - 0 = 2`, the Euler
characteristic of the sphere.

The kernel is the constants because a holomorphic function on a compact connected complex manifold
is constant
(`TauCeti.SmoothAlmostComplexStructure.delBar_eq_zero_iff_exists_eq_const_of_compactSpace` and
`TauCeti.dolbeaultCohomology.zeroZeroEquivOfCompactSpace`). For the cokernel, read a
`(0,1)`-form `α` in the affine coordinates `t ↦ [t : 1]` and `s ↦ [1 : s]`, related by
`s = 1 / t`. A smooth cutoff splits `α` into two forms whose coefficients are compactly supported
in the coordinate `t` and in the coordinate `s` respectively. For each
piece, with coefficient `c(t) d(conj t)` say, the Cauchy transform `u = T c` solves
`∂bar u = c d(conj t)` on `ℂ` (`HasCompactSupport.conjWirtingerDeriv_cauchyTransform`). Off the
support of `c` it is holomorphic, and it tends to `0` at infinity
(`TauCeti.hasDerivAt_cauchyTransform_of_notMem_tsupport` and
`HasCompactSupport.tendsto_cauchyTransform_cobounded`), so `s ↦ u (1 / s)` has a removable
singularity at `s = 0` (`TauCeti.contDiff_update_comp_inv`). Hence `u` extends by `0` to a smooth
function on `ℂℙ¹` (`TauCeti.ProjectiveLine.contMDiff_indicator_affineOpen`). Its `∂bar` agrees
with the piece in the coordinate `t`, which covers a dense open set, hence everywhere.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_projectivization`: every smooth `(0,1)`-form on
  `ℂℙ¹` is `∂bar` of a smooth function.
* `TauCeti.dolbeaultCohomology.instSubsingletonProjectivizationZeroOne`: `H^(0,1)_∂bar(ℂℙ¹; F)`
  vanishes.
* `TauCeti.dolbeaultCohomology.finrank_zero_zero_sub_finrank_zero_one_projectivization`: the
  index of `∂bar` on complex functions over `ℂℙ¹` is `2`.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Sections 1 and 2 (the `∂bar`-Poincaré lemma in one variable).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.3 and Section 2.6.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.2.
-/

public section

noncomputable section

open Set Filter Function Complex Projectivization Metric Bornology MeasureTheory
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold LinearAlgebra.Projectivization
  ComplexConjugate

namespace TauCeti

open SmoothAlmostComplexStructure ProjectiveLine

/-! ### Solving `∂bar f = β` -/

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Solving `∂bar f = β` for a form supported in one affine chart.** Let `β` be a `(0,1)`-form on
the projective line whose coefficient `c(t)` in the affine coordinate `t` of the chart `i` is
compactly supported. Its Cauchy transform `u` solves `∂bar u = c d(conj t)` on `ℂ`, is
holomorphic off the support of `c` and tends to `0` at infinity, so in the other coordinate
`s = 1 / t` it has a removable singularity at `s = 0`. Hence `u`, read in the chart `i` and
extended by `0` at the remaining point, is a smooth function with `∂bar f = β`. -/
private theorem exists_delBar_eq_of_hasCompactSupport
    {β : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 1}
    (hβ : β.IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 0 1) (i : Fin 2)
    (hc : HasCompactSupport fun t ↦
      (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) β).1 t ![(1 : ℂ)]) :
    ∃ f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0,
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).delBar f = β := by
  set η := SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) β
  set c : ℂ → F := fun t ↦ η.1 t ![(1 : ℂ)]
  have hcs : ContDiff ℝ ∞ c := by
    let Θ : ℂ → ℂ [⋀^Fin 1]→L[ℝ] F := fun y ↦ η.1 y
    have hd : ContDiff ℝ ∞ Θ := isSmoothForm_modelSpace_iff.1 η.isSmoothForm
    exact (ContinuousAlternatingMap.apply ℝ ℂ F ![(1 : ℂ)]).contDiff.comp hd
  set u := cauchyTransform c
  have hu : ContDiff ℝ ∞ u := hc.contDiff_cauchyTransform hcs
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hhol (w : ℂ) (hw : R < ‖w‖) : DifferentiableAt ℂ u w := by
    refine (hasDerivAt_cauchyTransform_of_notMem_tsupport
      (hcs.continuous.integrable_of_hasCompactSupport hc) fun h ↦ ?_).differentiableAt
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  -- `g` is `u` read in the chart `i`, extended by `0` at the remaining point.
  set g : ℙ ℂ (Fin 2 → ℂ) → F :=
    (affineOpen (K := ℂ) i).indicator fun x ↦ u (affineChart (K := ℂ) (n := 1) i x 0)
  have hg : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, F) ∞ g :=
    contMDiff_indicator_affineOpen i hu (contDiff_update_comp_inv hu hhol
      (hc.tendsto_cauchyTransform_cobounded (hcs.continuous.integrable_of_hasCompactSupport hc)))
  set f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0 :=
    ⟨RoughForm.ofFunction _ g, (isSmoothForm_ofFunction_iff.2 hg).mem_smoothBundleForms⟩
  refine ⟨f, mpullback_affineParam_injective i ?_⟩
  rw [mpullback_delBar _ _ (isPseudoholomorphic_affineParam i)]
  -- In the coordinate `t`, both sides are conjugate-linear with coefficient `c(t) = ∂bar u(t)`.
  have hfun : (fun y ↦ (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) f).1
      y 0) = u := by
    rw [← indicator_affineOpen_comp_affineParam i u]
    funext y
    rw [SmoothForm.mpullback_apply]
    exact RoughForm.ofFunction_apply _ _ _
  refine Subtype.ext (funext fun t ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  obtain ⟨w, rfl⟩ : ∃ w : ℂ, v = ![w] := ⟨v 0, by ext k; fin_cases k; rfl⟩
  have hη : (η.1 t : ℂ [⋀^Fin 1]→L[ℝ] F).IsOfType (Complex.I • ContinuousLinearMap.id ℝ ℂ) 0 1 := by
    simpa only [toEndomorphism_ofComplexManifold] using
      (hβ.mpullback _ (isPseudoholomorphic_affineParam i)).apply t
  have hη' := hη.map_smul_conj w (1 : ℂ)
  rw [smul_eq_mul, mul_one] at hη'
  refine (delBar_apply_eq_conjWirtingerDeriv _ t w).trans ?_
  rw [hfun, conjWirtingerDeriv_apply_eq_conj_smul_apply_one,
    hc.conjWirtingerDeriv_cauchyTransform (hcs.of_le (by simp))]
  exact hη'.symm

/-- A smooth cutoff on the projective line, `1` near `[0 : 1]` and `0` near `[1 : 0]`: in the
coordinate `t` of the chart `1` it is compactly supported, and `1` minus it is compactly supported
in the coordinate `s` of the chart `0`. -/
private theorem exists_cutoff_projectivization :
    ∃ ρ : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); ℝ⟯,
      HasCompactSupport (fun t ↦ ρ (affineParam 1 t)) ∧
        HasCompactSupport (fun s ↦ 1 - ρ (affineParam 0 s)) := by
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχ : ContDiff ℝ ∞ χ := χ.contDiff
  -- `ρ` is `χ` read in the chart `1` and extended by `0` at the remaining point.
  let ρ : ℙ ℂ (Fin 2 → ℂ) → ℝ :=
    (affineOpen (K := ℂ) 1).indicator fun x ↦ χ (affineChart (K := ℂ) (n := 1) 1 x 0)
  have h1 : (fun t ↦ ρ (affineParam 1 t)) = χ := indicator_affineOpen_comp_affineParam 1 _
  have h0 (s : ℂ) (hs : s ≠ 0) : ρ (affineParam 0 s) = χ s⁻¹ := by
    rw [← comp_apply (f := ρ), indicator_affineOpen_comp_affineParam_of_ne (by decide),
      update_of_ne hs]
  have hρ := contMDiff_indicator_affineOpen 1 hχ (χ.hasCompactSupport.contDiff_update_comp_inv hχ)
  refine ⟨⟨ρ, hρ⟩, ?_, HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun s hs ↦ ?_⟩
  · simpa only [ContMDiffMap.coeFn_mk, h1] using χ.hasCompactSupport
  · rw [mem_closedBall, dist_zero_right, not_le] at hs
    have hs0 : s ≠ 0 := norm_pos_iff.1 (one_pos.trans hs)
    simp only [ContMDiffMap.coeFn_mk]
    rw [h0 s hs0, χ.one_of_mem_closedBall, sub_self]
    rw [mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hs.le

/-- **Every `(0,1)`-form on the projective line is `∂bar` of a smooth function.** For a smooth
`(0,1)`-form `α` on `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` with coefficients in a complex Banach space, there is
a smooth function `f` with `∂bar f = α`. -/
theorem IsOfType.exists_delBar_eq_projectivization
    {α : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 1}
    (hα : α.IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 0 1) :
    ∃ f : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0,
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).delBar f = α := by
  obtain ⟨ρ, h1, h0⟩ := exists_cutoff_projectivization
  -- Split `α = ρ α + (1 - ρ) α` into pieces supported in the two affine charts.
  have htype (g : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); ℝ⟯) :
      (funSMulₗ g α).IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 0 1 :=
    isOfType_iff_forall.2 ⟨rfl, fun x ↦ by
      simpa only [coe_funSMulₗ, Complex.coe_smul] using (hα.apply x).smul (g x : ℂ)⟩
  have hcoeff (g : C^∞⟮𝓘(ℝ, Fin 1 → ℂ), ℙ ℂ (Fin 2 → ℂ); ℝ⟯) (l : Fin 2) :
      (fun t ↦ (SmoothForm.mpullback (affineParam l) (contMDiff_affineParam_real l)
        (funSMulₗ g α)).1 t ![(1 : ℂ)]) = fun t ↦ g (affineParam l t) •
          (SmoothForm.mpullback (affineParam l) (contMDiff_affineParam_real l) α).1 t
            ![(1 : ℂ)] := by
    funext t
    simp only [SmoothForm.mpullback_apply, coe_funSMulₗ, ContinuousAlternatingMap.smul_apply]
  obtain ⟨f₁, hf₁⟩ := exists_delBar_eq_of_hasCompactSupport (htype ρ) 1
    (by rw [hcoeff]; exact h1.smul_right)
  obtain ⟨f₀, hf₀⟩ := exists_delBar_eq_of_hasCompactSupport (htype (1 - ρ)) 0
    (by rw [hcoeff]; exact h0.smul_right)
  refine ⟨f₁ + f₀, ?_⟩
  rw [map_add, hf₁, hf₀]
  refine Subtype.ext (funext fun x ↦ ?_)
  simp [← add_smul]

end SmoothForm

/-! ### Dolbeault cohomology -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace dolbeaultCohomology

open Dolbeault

variable [CompleteSpace F]

/-- **`H^(0,1)` of the projective line vanishes.** Every `(0,1)`-form on `ℂℙ¹` is `∂bar` of a
smooth function. -/
instance instSubsingletonProjectivizationZeroOne :
    Subsingleton (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 0 1) := by
  refine subsingleton_of_forall_eq 0 fun a ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective 0 1 a
  rw [mk_eq_zero_iff, mem_exactForms_succ]
  obtain ⟨f, hf⟩ := ((((ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).mem_typeForms 0 1
    φ.1.1).1 φ.1.2)).exists_delBar_eq_projectivization
  exact ⟨⟨f, ((ofComplexManifold _ _).mem_typeForms 0 0 f).2
    (SmoothForm.isOfType_zero_zero f _)⟩, hf⟩

/-- **The index of `∂bar` on functions over the projective line.** Its kernel `H^(0,0)` is the
constants (`TauCeti.dolbeaultCohomology.zeroZeroEquivOfCompactSpace`), of real dimension `2`,
and its cokernel `H^(0,1)` vanishes, so the index is `2 - 0 = 2`, the Euler characteristic of the
sphere. -/
theorem finrank_zero_zero_sub_finrank_zero_one_projectivization :
    (Module.finrank ℝ (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 0) : ℤ) -
      Module.finrank ℝ (dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 1) = 2 := by
  rw [finrank_real_of_complex, finrank_real_of_complex,
    (zeroZeroEquivOfCompactSpace (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ).finrank_eq,
    Module.finrank_zero_of_subsingleton
      (M := dolbeaultCohomology (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) ℂ 0 1)]
  simp

end dolbeaultCohomology

end TauCeti
