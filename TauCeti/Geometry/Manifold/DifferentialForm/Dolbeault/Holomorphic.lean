/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# The `∂bar`-closed functions are the holomorphic functions

Let `J` be a smooth almost complex structure on a manifold `M` and let `F` be a complex normed
space. On a smooth function `f : M → F`, regarded as a `0`-form, the operators `∂` and `∂bar` of
`J` are the Wirtinger parts of the differential:

`∂f(v) = (df(v) - i df(J v)) / 2`, `∂bar f(v) = (df(v) + i df(J v)) / 2`

(`TauCeti.SmoothAlmostComplexStructure.delBar_apply_apply` in
`TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic`). So `∂bar f` vanishes at a point
exactly when `df` is complex linear there, `df ∘ J = i df`; that is, exactly when `f` is
pseudoholomorphic there as a map into the complex vector space `F`.

On a complex manifold, with its almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`, the pseudoholomorphic maps are the
holomorphic maps. Hence a smooth function satisfies `∂bar f = 0` exactly when it is holomorphic,
and for a finite-dimensional model the kernel of `∂bar` on smooth `0`-forms is the complex vector
space of holomorphic functions `M → F` (`TauCeti.kerDelBarZeroEquiv`). This is the Dolbeault
cohomology `H^(0,0)` of `M` with coefficients in `F`, since there are no forms of degree `-1`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.delBar_apply_eq_zero_iff_isPseudoholomorphicAt`,
  `TauCeti.SmoothAlmostComplexStructure.delBar_eq_zero_iff_isPseudoholomorphic`: on any almost
  complex manifold, `∂bar f = 0` exactly when `f` is pseudoholomorphic.
* `TauCeti.SmoothAlmostComplexStructure.delBar_ofComplexManifold_apply_eq_zero_iff`,
  `TauCeti.SmoothAlmostComplexStructure.delBar_ofComplexManifold_eq_zero_iff`: on a complex
  manifold, `∂bar f = 0` exactly when `f` is holomorphic.
* `TauCeti.kerDelBarZeroEquiv`: the `∂bar`-closed smooth functions are the holomorphic
  functions.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.3 and 2.6.
-/

public section

noncomputable section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace SmoothAlmostComplexStructure

/-! ### `∂bar`-closed functions on an almost complex manifold -/

section AlmostComplex

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (J : SmoothAlmostComplexStructure I M)

/-- **`∂bar f = 0` is the Cauchy–Riemann equation.** On any almost complex manifold, `∂bar f`
vanishes at a point exactly when `f` is pseudoholomorphic there as a map into the complex vector
space `F`, whose almost complex structure is multiplication by `i`. -/
theorem delBar_apply_eq_zero_iff_isPseudoholomorphicAt (f : SmoothForm I M F 0) (x : M) :
    (J.delBar f).1 x = 0 ↔
      IsPseudoholomorphicAt J (ofComplexManifold F F) (fun y ↦ f.1 y 0) x := by
  have hf : ContMDiff I 𝓘(ℝ, F) ∞ fun y ↦ f.1 y 0 := by
    rw [← isSmoothForm_ofFunction_iff, ← RoughForm.eq_ofFunction]
    exact f.isSmoothForm
  rw [delBar_apply_eq_zero_iff]
  simp only [mvfderiv_apply_eq_mfderiv_apply]
  exact ⟨fun h ↦ isPseudoholomorphicAt_of_hasMFDerivAt
      (hf.mdifferentiableAt (by simp)).hasMFDerivAt fun w ↦
        (h w).trans (ofComplexManifold_apply (E := F) _ _).symm,
    fun h v ↦ (h.mfderiv_apply_commute v).trans (ofComplexManifold_apply (E := F) _ _)⟩

/-- On any almost complex manifold, `∂bar f = 0` exactly when `f` is pseudoholomorphic as a map
into the complex vector space `F`. -/
theorem delBar_eq_zero_iff_isPseudoholomorphic (f : SmoothForm I M F 0) :
    J.delBar f = 0 ↔ IsPseudoholomorphic J (ofComplexManifold F F) (fun y ↦ f.1 y 0) := by
  rw [isPseudoholomorphic_iff,
    ← forall_congr' (J.delBar_apply_eq_zero_iff_isPseudoholomorphicAt f)]
  exact ⟨fun h x ↦ by simp [h], fun h ↦ Subtype.ext (funext h)⟩

end AlmostComplex

/-! ### Holomorphic functions on a complex manifold -/

section ComplexManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The `∂bar`-closed functions are the holomorphic functions, pointwise.** On a complex
manifold, `∂bar f` vanishes at a point exactly when the smooth function `f` is holomorphic
there. -/
theorem delBar_ofComplexManifold_apply_eq_zero_iff (f : SmoothForm 𝓘(ℝ, E) M F 0) (x : M) :
    ((ofComplexManifold E M).delBar f).1 x = 0 ↔
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) (fun y ↦ f.1 y 0) x := by
  rw [delBar_apply_eq_zero_iff_isPseudoholomorphicAt, isPseudoholomorphicAt_ofComplexManifold_iff]

/-- **The `∂bar`-closed functions are the holomorphic functions.** On a complex manifold, a smooth
function `f` satisfies `∂bar f = 0` exactly when it is holomorphic. -/
theorem delBar_ofComplexManifold_eq_zero_iff (f : SmoothForm 𝓘(ℝ, E) M F 0) :
    (ofComplexManifold E M).delBar f = 0 ↔ MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) (fun y ↦ f.1 y 0) := by
  rw [delBar_eq_zero_iff_isPseudoholomorphic, isPseudoholomorphic_ofComplexManifold_iff]

end ComplexManifold

end SmoothAlmostComplexStructure

open SmoothAlmostComplexStructure

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Holomorphic functions are the `∂bar`-closed smooth functions.** On a complex manifold with
finite-dimensional model, the kernel of `∂bar` on smooth `F`-valued functions is the complex vector
space of holomorphic functions `M → F`, which are the complex `C^∞` maps. This is the Dolbeault
cohomology `H^(0,0)` of `M` with coefficients in `F`. -/
def kerDelBarZeroEquiv :
    LinearMap.ker ((ofComplexManifold E M).delBar (F := F) (k := 0)) ≃ₗ[ℂ]
      C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ, F), F⟯ where
  toFun φ := ⟨fun y ↦ φ.1.1 y 0,
    ((delBar_ofComplexManifold_eq_zero_iff φ.1).1 (LinearMap.mem_ker.1 φ.2)).contMDiff⟩
  invFun g := ⟨⟨RoughForm.ofFunction 𝓘(ℝ, E) g,
      (isSmoothForm_ofFunction_iff.2 <| by
        simpa only [modelWithCornersSelf_restrictScalars] using
          g.contMDiff.restrictScalars ℝ).mem_smoothBundleForms⟩,
    LinearMap.mem_ker.2 <| (delBar_ofComplexManifold_eq_zero_iff _).2 <| by
      simpa only [RoughForm.ofFunction_apply] using g.contMDiff.mdifferentiable (by simp)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| Subtype.ext
    (RoughForm.eq_ofFunction (I := 𝓘(ℝ, E)) (F := F) φ.1.1).symm
  right_inv g := ContMDiffMap.ext fun x ↦ RoughForm.ofFunction_apply (I := 𝓘(ℝ, E)) (f := ⇑g) x 0

variable {E M F}

/-- The holomorphic function of a `∂bar`-closed smooth function is its value on the empty tuple of
tangent vectors. -/
@[simp]
theorem kerDelBarZeroEquiv_apply (φ : LinearMap.ker ((ofComplexManifold E M).delBar (F := F)
    (k := 0))) (x : M) : kerDelBarZeroEquiv E M F φ x = φ.1.1 x 0 := by
  rw [kerDelBarZeroEquiv]
  rfl

/-- The `∂bar`-closed smooth function of a holomorphic function is its `0`-form. -/
@[simp]
theorem coe_kerDelBarZeroEquiv_symm_apply (g : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ, F), F⟯) :
    ((kerDelBarZeroEquiv E M F).symm g).1.1 = RoughForm.ofFunction 𝓘(ℝ, E) g := by
  rw [kerDelBarZeroEquiv]
  rfl

end TauCeti
