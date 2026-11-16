/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Liouville
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Plane
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine

/-!
# The projective line has no holomorphic one-forms

A holomorphic one-form on the complex projective line `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)`, that is a smooth
complex-valued one-form of type `(1,0)` which is `∂bar`-closed, vanishes
(`TauCeti.SmoothForm.IsOfType.eq_zero_of_delBar_eq_zero_projectivization`). The coefficients may
lie in any complex normed space.

The proof reads the form in the two affine coordinates `t ↦ [t : 1]` and `s ↦ [1 : s]`. Pulled
back along them, it becomes `f(t) dt` and `g(s) ds` with `f` and `g` entire
(`TauCeti.SmoothForm.IsOfType.delBar_eq_zero_iff`). On the overlap `s = 1 / t`, so
`ds = -dt / t²` and `f(t) = -g(1 / t) / t²`, which tends to `0` as `t → ∞` since `g` is bounded
near `0`. By Liouville's theorem `f = 0`, and likewise `g = 0`. Every point of `ℂℙ¹` is in the
image of one of the two coordinates, where the differential of the coordinate is nonzero, and a
`(1,0)`-form on the one-dimensional complex tangent space vanishing on a nonzero vector is zero.

The two affine coordinates are `TauCeti.ProjectiveLine.affineParam`. Pulled-back forms are related
on the overlap by `TauCeti.ProjectiveLine.coe_mpullback_affineParam_apply_of_ne_zero`, and a smooth
form is determined by its pullback along either coordinate
(`TauCeti.ProjectiveLine.mpullback_affineParam_injective`).

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 1 (projective space and its affine charts).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

open Set Filter Function Complex Projectivization
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold LinearAlgebra.Projectivization

namespace TauCeti

open SmoothAlmostComplexStructure

namespace ProjectiveLine

/-- The affine coordinates of the projective line are pseudoholomorphic for the complex structures
of `ℂ` and of the projective line. -/
theorem isPseudoholomorphic_affineParam (i : Fin 2) :
    IsPseudoholomorphic (ofComplexManifold ℂ ℂ)
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) (affineParam i) :=
  isPseudoholomorphic_ofComplexManifold_iff.2
    ((contMDiff_affineParam (n := 1) i).mdifferentiable one_ne_zero)

/-- Near a nonzero point `s`, the affine coordinate `i` is the affine coordinate `j` composed with
`y ↦ 1 / y`, so a form pulled back along the coordinate `i` is, at `s`, the pullback along
`y ↦ 1 / y` of the form pulled back along the coordinate `j`. -/
theorem coe_mpullback_affineParam_apply_of_ne_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {k : ℕ} (α : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k)
    {i j : Fin 2} (hij : i ≠ j) {s : ℂ} (hs : s ≠ 0) :
    (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) α).1 s =
      TauCeti.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ ↦ y⁻¹)
        (SmoothForm.mpullback (affineParam j) (contMDiff_affineParam_real j) α).1 s := by
  have heq : affineParam i =ᶠ[𝓝 s] affineParam j ∘ fun y ↦ y⁻¹ := by
    filter_upwards [eventually_ne_nhds hs] with y hy using affineParam_inv hij hy
  have hinv := (hasDerivAt_inv hs).hasFDerivAt.restrictScalars ℝ
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, heq.mpullback_eq,
    mpullback_comp_at hinv.differentiableAt.mdifferentiableAt
      ((contMDiff_affineParam_real (n := 1) j _).mdifferentiableAt one_ne_zero)]

/-- A smooth form on the projective line is determined by its pullback along one affine
coordinate: that coordinate covers all points but one, and the forms are continuous. -/
theorem mpullback_affineParam_injective {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {k : ℕ} (i : Fin 2) :
    Injective (SmoothForm.mpullback (F := F) (k := k) (affineParam i)
      (contMDiff_affineParam_real i)) := by
  -- First, two forms agreeing after pullback along both coordinates are equal.
  have hboth {α β : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k}
      (h : ∀ i, SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) α =
        SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) β) : α = β := by
    refine Subtype.ext (funext fun x ↦ ?_)
    obtain ⟨i, hi⟩ := exists_mem_affineOpen x
    obtain ⟨t, rfl⟩ : ∃ t, affineParam i t = x := ⟨_, affineParam_affineChart hi⟩
    ext v
    choose w hw using fun m ↦ surjective_mfderiv_affineParam i t (v m)
    have h' := congrArg (fun γ : SmoothForm 𝓘(ℝ, ℂ) ℂ F k ↦ γ.1 t w) (h i)
    simp only [SmoothForm.mpullback_apply, hw] at h'
    exact h'
  -- Pullbacks along the other coordinate agree off `0`, hence everywhere by continuity.
  intro α β h
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by fin_cases i <;> simp
  refine hboth fun l ↦ ?_
  obtain rfl | rfl : l = i ∨ l = j := by omega
  · exact h
  let Θ (γ : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k) : ℂ → ℂ [⋀^Fin k]→L[ℝ] F :=
    fun s ↦ (SmoothForm.mpullback (affineParam l) (contMDiff_affineParam_real l) γ).1 s
  have hcont (γ : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F k) : Continuous (Θ γ) :=
    (isSmoothForm_modelSpace_iff.1 (SmoothForm.mpullback _ _ γ).isSmoothForm).continuous
  have hΘ : Θ α = Θ β := (hcont α).ext_on (dense_compl_singleton 0) (hcont β) fun s hs ↦ by
    simp only [Θ]
    rw [coe_mpullback_affineParam_apply_of_ne_zero α hij.symm hs,
      coe_mpullback_affineParam_apply_of_ne_zero β hij.symm hs, h]
  exact Subtype.ext (funext fun s ↦ congrFun hΘ s)

end ProjectiveLine

open ProjectiveLine

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {α : SmoothForm 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) F 1}

/-- The transformation law between the two affine coordinates: pulled back along them, a
`(1,0)`-form becomes `c₁(t) dt` and `c₀(s) ds`, and on the overlap `s = 1 / t`, so
`c₁(t) = -c₀(1 / t) / t²`, and symmetrically. -/
private theorem IsOfType.mpullback_affineParam_apply_inv
    (hα : α.IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 1 0) {i j : Fin 2}
    (hij : i ≠ j) {s : ℂ} (hs : s ≠ 0) :
    (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) α).1 s ![(1 : ℂ)] =
      -(s ^ 2)⁻¹ • (SmoothForm.mpullback (affineParam j) (contMDiff_affineParam_real j) α).1 s⁻¹
        ![(1 : ℂ)] := by
  have hinv := (hasDerivAt_inv hs).hasFDerivAt.restrictScalars ℝ
  have hD : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ ↦ y⁻¹) s (1 : ℂ) = (-(s ^ 2)⁻¹ : ℂ) := by
    rw [mfderiv_eq_fderiv, hinv.fderiv]
    -- The tangent-space identifications of `ℂ` are the identity.
    exact one_smul ℂ (-(s ^ 2)⁻¹)
  rw [← (hα.mpullback _ (isPseudoholomorphic_affineParam j)).apply_eq_smul,
    coe_mpullback_affineParam_apply_of_ne_zero α hij hs,
    TauCeti.mpullback_apply]
  congr 1
  ext k
  fin_cases k
  exact hD

/-- **The projective line has no holomorphic one-forms.** A smooth one-form of type `(1,0)` on
`ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` whose `∂bar` vanishes is zero. -/
theorem IsOfType.eq_zero_of_delBar_eq_zero_projectivization
    (hα : α.IsOfType (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) 1 0)
    (hd : (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).delBar α = 0) : α = 0 := by
  -- The pullbacks `c i dz` of `α` along the two affine coordinates have entire coefficients.
  let η (i : Fin 2) : SmoothForm 𝓘(ℝ, ℂ) ℂ F 1 :=
    SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) α
  have hη (i : Fin 2) : (η i).IsOfType (ofComplexManifold ℂ ℂ) 1 0 :=
    hα.mpullback _ (isPseudoholomorphic_affineParam i)
  have hc (i : Fin 2) : Differentiable ℂ fun y ↦ (η i).1 y ![(1 : ℂ)] := by
    refine (hη i).delBar_eq_zero_iff.1 ?_
    rw [← (ofComplexManifold ℂ ℂ).mpullback_delBar (contMDiff_affineParam_real i)
      (isPseudoholomorphic_affineParam i), hd, map_zero]
  -- By Liouville's theorem and the transformation law, the coefficients vanish.
  have hc₀ {i j : Fin 2} (hij : i ≠ j) (t : ℂ) : (η i).1 t ![(1 : ℂ)] = 0 :=
    (hc i).eq_zero_of_eq_neg_inv_sq_smul (hc j).continuous.continuousAt
      (fun _ hs ↦ hα.mpullback_affineParam_apply_inv hij hs) t
  -- Every point `x` is `[t : 1]` or `[1 : s]`, and `α` vanishes on the nonzero derivative there.
  refine Subtype.ext (funext fun x ↦ ?_)
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by fin_cases i <;> simp
  obtain ⟨t, rfl⟩ : ∃ t, affineParam i t = x := ⟨_, affineParam_affineChart hi⟩
  have hβ := hα.apply (affineParam i t)
  rw [toEndomorphism_ofComplexManifold] at hβ
  refine ContinuousAlternatingMap.IsOfType.eq_zero_of_apply_eq_zero (U := Fin 1 → ℂ) hβ
    (Module.finrank_fin_fun ℂ)
    (w := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t (1 : ℂ)) ?_ ?_
  · exact fun h ↦ (one_ne_zero : (1 : ℂ) ≠ 0)
      (injective_mfderiv_affineParam i t (h.trans (map_zero _).symm))
  · have h := hc₀ hij t
    rw [SmoothForm.mpullback_apply] at h
    refine (congrArg _ (funext fun k ↦ ?_)).trans h
    fin_cases k
    rfl

end SmoothForm

end TauCeti
