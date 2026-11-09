/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Liouville
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Plane
public import TauCeti.Geometry.Manifold.Instances.Projectivization

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

/-- The affine coordinate of the projective line on the open set where the `i`-th homogeneous
coordinate does not vanish: `t ↦ [t : 1]` for `i = 1` and `s ↦ [1 : s]` for `i = 0`. -/
private noncomputable def affineParam (i : Fin 2) (t : ℂ) : ℙ ℂ (Fin 2 → ℂ) :=
  (affineChart (K := ℂ) (n := 1) i).symm fun _ ↦ t

private theorem affineParam_eq (i : Fin 2) (t : ℂ) :
    affineParam i t = mk ℂ (Fin.insertNth (α := fun _ ↦ ℂ) i 1 fun _ ↦ t)
      (Fin.insertNth_one_ne_zero i _) :=
  affineChart_symm_apply i _

/-- The two affine coordinates are related by `s = 1 / t` on their overlap. -/
private theorem affineParam_inv {i j : Fin 2} (hij : i ≠ j) {t : ℂ} (ht : t ≠ 0) :
    affineParam i t = affineParam j t⁻¹ := by
  rw [affineParam_eq, affineParam_eq, mk_eq_mk_iff]
  have h₁ (x : ℂ) : Fin.insertNth (α := fun _ ↦ ℂ) (1 : Fin 2) 1 (fun _ ↦ x) 0 = x := rfl
  refine ⟨Units.mk0 t ht, ?_⟩
  ext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

private theorem contMDiff_affineParam (i : Fin 2) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) ∞ (affineParam i) :=
  (contMDiff_affineChart_symm i ∞).comp (contDiff_pi.2 fun _ ↦ contDiff_id).contMDiff

private theorem contMDiff_affineParam_real (i : Fin 2) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) ∞ (affineParam i) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_affineParam i).restrictScalars ℝ

private theorem isPseudoholomorphic_affineParam (i : Fin 2) :
    IsPseudoholomorphic (ofComplexManifold ℂ ℂ)
      (ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) (affineParam i) :=
  isPseudoholomorphic_ofComplexManifold_iff.2 ((contMDiff_affineParam i).mdifferentiable (by simp))

/-- The derivative of an affine coordinate of the projective line is injective: the affine chart
is a left inverse of the coordinate. -/
private theorem injective_mfderiv_affineParam (i : Fin 2) (t : ℂ) :
    Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (affineParam i) t) := by
  let e : ℂ →L[ℝ] Fin 1 → ℂ := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℝ ℂ
  have he : Injective e := fun a b hab ↦ by simpa [e] using congrFun hab 0
  have hcomp : affineChart (K := ℂ) (n := 1) i ∘ affineParam i = e :=
    funext fun s ↦ (affineChart i).right_inv (by simp [affineChart_target])
  have hmem : affineParam i t ∈ affineOpen (K := ℂ) i := by
    rw [← affineChart_source]
    exact (affineChart i).map_target (by simp [affineChart_target])
  have hchart : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
      (affineChart (K := ℂ) (n := 1) i) (affineParam i t) := by
    have := (((contMDiffOn_affineChart (𝕜 := ℂ) (n := 1) i ∞).contMDiffAt
      ((isOpen_affineOpen i).mem_nhds hmem)).restrictScalars ℝ)
    simpa only [modelWithCornersSelf_restrictScalars] using this.mdifferentiableAt (by simp)
  have key := mfderiv_comp t hchart ((contMDiff_affineParam_real i t).mdifferentiableAt (by simp))
  rw [hcomp, mfderiv_eq_fderiv, e.fderiv] at key
  refine Injective.of_comp (f := mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
    (affineChart (K := ℂ) (n := 1) i) (affineParam i t)) ?_
  rw [← ContinuousLinearMap.coe_comp, ← key]
  -- The derivative of `e` read through the model spaces is `e` itself.
  exact (NormedSpace.fromTangentSpace _).symm.injective.comp
    (he.comp (NormedSpace.fromTangentSpace t).injective)

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
  have heq : affineParam i =ᶠ[𝓝 s] affineParam j ∘ fun y ↦ y⁻¹ := by
    filter_upwards [eventually_ne_nhds hs] with y hy using affineParam_inv hij hy
  have hinv := (hasDerivAt_inv hs).hasFDerivAt.restrictScalars ℝ
  have hD : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ ↦ y⁻¹) s (1 : ℂ) = (-(s ^ 2)⁻¹ : ℂ) := by
    rw [mfderiv_eq_fderiv, hinv.fderiv]
    -- The tangent-space identifications of `ℂ` are the identity.
    exact one_smul ℂ (-(s ^ 2)⁻¹)
  -- Near `s`, the coordinate `i` is the coordinate `j` composed with `y ↦ 1 / y`.
  have hpull : (SmoothForm.mpullback (affineParam i) (contMDiff_affineParam_real i) α).1 s =
      TauCeti.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ ↦ y⁻¹)
        (SmoothForm.mpullback (affineParam j) (contMDiff_affineParam_real j) α).1 s := by
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, heq.mpullback_eq,
      mpullback_comp_at hinv.differentiableAt.mdifferentiableAt
        ((contMDiff_affineParam_real j _).mdifferentiableAt (by simp))]
  rw [← (hα.mpullback _ (isPseudoholomorphic_affineParam j)).apply_eq_smul, hpull,
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
  obtain ⟨t, rfl⟩ : ∃ t, affineParam i t = x := by
    refine ⟨affineChart (K := ℂ) (n := 1) i x 0, ?_⟩
    have h' : (fun _ : Fin 1 ↦ affineChart (K := ℂ) (n := 1) i x 0) =
        affineChart (K := ℂ) (n := 1) i x :=
      funext fun k ↦ by fin_cases k; rfl
    rw [affineParam, h']
    exact (affineChart i).left_inv (by rwa [affineChart_source])
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
