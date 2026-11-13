/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The flat map of a two-form on a manifold

A two-form `σ` on a manifold `M` gives at each point its **flat map**
`σ♭_x : T_x M → T_x^* M`, `v ↦ ι_v σ = σ(v, ·)` (`TauCeti.SmoothTwoForm.flat`), the continuous
form of the algebraic bilinear form `TauCeti.SmoothForm.bilinFormAt`. The flat maps of a smooth
two-form form a smooth section of the bundle `Hom(TM, Hom(TM, ℝ))`
(`TauCeti.SmoothTwoForm.contMDiff_flat`). On a finite-dimensional manifold, the form is
nondegenerate exactly when every flat map is invertible
(`TauCeti.SmoothTwoForm.isNondegenerate_iff_isInvertible_flat`); the inverse maps then form a
smooth section as well, by `ContMDiff.clm_bundle_inverse`.

Inverting the flat map turns covector fields into vector fields: a Hamiltonian vector field is
`(σ♭)⁻¹ df`, and the Liouville field of a primitive `α` is `(σ♭)⁻¹ α`. For a nondegenerate form,
in any dimension, a vector field is determined by its contraction with the form
(`TauCeti.SmoothTwoForm.IsNondegenerate.interior_injective`), and a linear map between two tangent
spaces of `M` that preserves the form is surjective in finite dimensions
(`TauCeti.SmoothTwoForm.IsNondegenerate.surjective_of_eval₂_map`).

On smooth sections, contraction `X ↦ ι_X σ` is a linear map from smooth vector fields to smooth
one-forms (`TauCeti.SmoothTwoForm.interiorₗ`). For a nondegenerate form on a finite-dimensional
manifold it is a linear equivalence (`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`), whose
inverse sends a one-form `α` to the vector field `(σ♭)⁻¹ α`.

Inverting the flat map also projects a section `C` of `End(TM)` to its `σ`-skew part
`(σ♭)⁻¹ ∘ (β + βᵀ) / 2`, where `β = σ(C ·, ·)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.skewPart`). Skew-adjointness for a varying form is a
pointwise condition, so this is how a section with a skew-adjoint value at one point is made
skew-adjoint everywhere without changing that value.

## Main declarations

* `TauCeti.SmoothTwoForm.flat`: the flat map `v ↦ σ(v, ·)` at a point.
* `TauCeti.SmoothTwoForm.interior_apply_eq_ofSubsingleton_flat`: the interior product `ι_X σ` is
  the flat map applied to `X`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.interior_injective`: for a nondegenerate form,
  `X ↦ ι_X σ` is injective.
* `TauCeti.SmoothTwoForm.contMDiff_flat`: the flat maps form a smooth section.
* `TauCeti.SmoothTwoForm.contMDiffAt_sectionAlong_flatL` and
  `TauCeti.SmoothTwoForm.contMDiffAt_sectionAlong_flat`: the flat maps of a smooth family of
  two-forms along a map depend smoothly on the parameter.
* `TauCeti.SmoothTwoForm.isNondegenerate_iff_isInvertible_flat`,
  `TauCeti.SmoothTwoForm.isInvertible_flat_iff`: nondegeneracy is invertibility of the flat maps,
  globally and at each point, in finite dimensions.
* `TauCeti.SmoothTwoForm.IsNondegenerate.surjective_of_eval₂_map`: a linear map between tangent
  spaces preserving a nondegenerate form is surjective, in finite dimensions.
* `TauCeti.SmoothTwoForm.interiorₗ`: contraction of smooth vector fields, as a linear map to smooth
  one-forms.
* `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`: for a nondegenerate form in finite
  dimensions, contraction identifies smooth vector fields with smooth one-forms. The vector field
  `(σ♭)⁻¹ α` vanishes exactly where `α` does
  (`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv_symm_apply_eq_zero_iff`).
* `TauCeti.SmoothTwoForm.flatComp`: the bilinear forms `σ(C ·, ·)` of a section of `End(TM)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.skewPart`: the `σ`-skew part of a section of `End(TM)`,
  skew-adjoint at every point and equal to `C` wherever `C` is already skew-adjoint.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- The **flat map** of a two-form at a point: the contraction `v ↦ ι_v σ = σ(v, ·)`, as a
continuous linear map from the tangent space to its dual. -/
def flat (σ : SmoothTwoForm I M) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  -- The tangent space is the model space `E`, whose norm gives continuous currying.
  ContinuousAlternatingMap.flatL ℝ E ℝ (σ.1 x)

/-- The flat map at a point is the currying `ContinuousAlternatingMap.flatL` of the value of the
form there. -/
theorem flat_def (σ : SmoothTwoForm I M) (x : M) :
    σ.flat x = ContinuousAlternatingMap.flatL ℝ E ℝ (σ.1 x) :=
  (rfl)

/-- The flat map evaluates as the two-form. -/
@[simp]
theorem flat_apply (σ : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    σ.flat x v w = SmoothBundleForm.eval₂ σ x v w := by
  rw [SmoothBundleForm.eval₂_apply]
  exact ContinuousAlternatingMap.flatL_apply_apply (E := E) (σ.1 x) v w

/-- The interior product `ι_X σ` at a point is the flat map applied to `X`, read as a one-form. -/
theorem interior_apply_eq_ofSubsingleton_flat (σ : SmoothTwoForm I M)
    (X : (x : M) → TangentSpace I x) (x : M) :
    RoughForm.interior X σ.1 x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (σ.flat x (X x)) := by
  rw [RoughForm.interior_apply_eq_curryLeft]
  exact (ContinuousAlternatingMap.ofSubsingleton_flatL_apply (E := E) (σ.1 x) (X x)).symm

/-- For a nondegenerate two-form, a vector field is determined by its contraction with the form:
if `ι_X σ = ι_Y σ`, then `X = Y`. In particular, the Liouville field of a primitive is unique. -/
theorem IsNondegenerate.interior_injective (h : σ.IsNondegenerate) :
    Function.Injective fun X : (x : M) → TangentSpace I x ↦ RoughForm.interior X σ.1 := by
  intro X Y hXY
  funext x
  rw [← sub_eq_zero]
  refine isNondegenerate_iff_separatingLeft.1 h x _ fun w ↦ ?_
  -- By bilinearity, `σ(X - Y, w)` is `ι_X σ (w) - ι_Y σ (w)`, which vanishes.
  rw [← flat_apply, map_sub, sub_apply, sub_eq_zero]
  simpa [interior_apply_eq_ofSubsingleton_flat] using congr($hXY x ![w])

/-- **Flat maps of a smooth family of two-forms.** Let `σ m` be alternating two-forms on the
tangent spaces `T_(b m) M` along a map `b : N → M`, depending `C^n` on `m`. Then their flat maps
`v ↦ σ m (v, ·)` depend `C^n` on `m`, as a section of `Hom(TM, Hom(TM, ℝ))` along `b`. -/
theorem contMDiffAt_sectionAlong_flatL {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {b : N → M}
    {σ : (m : N) → TangentSpace I (b m) [⋀^Fin 2]→L[ℝ] Trivial M ℝ (b m)} {m₀ : N}
    (hσ : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m) (σ m)) m₀) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (b m)
        (ContinuousAlternatingMap.flatL ℝ E ℝ (σ m))) m₀ := by
  rw [contMDiffAt_hom_bundle]
  have hσ' := (contMDiffAt_continuousAlternatingMap_bundle _).1 hσ
  refine ⟨hσ'.1, ?_⟩
  -- In coordinates, the flat map is `flatL` applied to the coordinate expression of the form.
  refine ((ContinuousAlternatingMap.flatL ℝ E ℝ).contDiff.comp_contMDiffAt
    hσ'.2).congr_of_eventuallyEq ?_
  filter_upwards [hσ'.1.continuousAt.preimage_mem_nhds
    ((trivializationAt E (TangentSpace I) (b m₀)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) (b m₀)))] with m
    (hm : b m ∈ (trivializationAt E (TangentSpace I) (b m₀)).baseSet)
  ext v w
  -- `flatL ℝ E ℝ (σ m)` is typed over the model space `E`, while the bundle lemmas apply maps of
  -- tangent fibres `TangentSpace I (b m)`. These are definitionally `E`, so the map is passed
  -- explicitly to `inCoordinates_apply_eq₂`, and its evaluation `flatL_apply_apply` on fibre
  -- vectors is applied by unification.
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ)
    (ϕ := ContinuousAlternatingMap.flatL ℝ E ℝ (σ m)) hm hm (Set.mem_univ _),
    Function.comp_apply, ContinuousAlternatingMap.flatL_apply_apply]
  simp only [Trivial.fiberBundle_trivializationAt',
    Trivial.linearMapAt_trivialization, Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.id_compContinuousAlternatingMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, LinearMap.id_coe, id_eq]
  refine (ContinuousAlternatingMap.flatL_apply_apply (E := E) (F := ℝ) (σ m) _ _).trans ?_
  congr 1
  ext i
  fin_cases i <;> exact (Trivialization.symmL_apply _ hm _).symm

/-- **Flat maps of a smooth family of smooth two-forms.** Let `σ m` be smooth two-forms on `M`
depending on a parameter `m ∈ N`, and let `b : N → M`. If the values `(σ m)_(b m)` depend `C^n` on
`m`, as a section along `b`, then so do the flat maps `(σ m)♭_(b m)`. This is
`TauCeti.SmoothTwoForm.contMDiffAt_sectionAlong_flatL` stated with `TauCeti.SmoothTwoForm.flat`. -/
theorem contMDiffAt_sectionAlong_flat {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {b : N → M} {σ : N → SmoothTwoForm I M} {m₀ : N}
    (hσ : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m) ((σ m).1 (b m)))
      m₀) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (b m)
        ((σ m).flat (b m))) m₀ :=
  contMDiffAt_sectionAlong_flatL hσ

/-- **The flat maps of a two-form form a smooth section** of the bundle `Hom(TM, Hom(TM, ℝ))`. -/
theorem contMDiff_flat (σ : SmoothTwoForm I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (σ.flat x)) :=
  fun x₀ ↦ contMDiffAt_sectionAlong_flatL (b := id) (σ.contMDiff x₀)

/-- The flat map is the continuous form of the algebraic bilinear form of `σ` at a point. -/
theorem toBilinForm_flat (σ : SmoothTwoForm I M) (x : M) :
    (σ.flat x).toBilinForm = σ.bilinFormAt x := by
  ext v w
  simp

/-- In finite dimensions, the flat map of a two-form at a point is invertible exactly when the
form is nondegenerate there. -/
theorem isInvertible_flat_iff [FiniteDimensional ℝ E] {x : M} :
    (σ.flat x).IsInvertible ↔ (σ.bilinFormAt x).Nondegenerate := by
  refine ⟨fun h ↦ ?_, fun h ↦ ContinuousLinearMap.isInvertible_of_separatingLeft (E := E)
    fun (v : TangentSpace I x) hv ↦ h.1 v fun w ↦ (SmoothForm.bilinFormAt_apply σ x v w).trans
      ((flat_apply σ x v w).symm.trans (hv w))⟩
  apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (SmoothForm.isAlt_bilinFormAt σ x).isRefl).mpr
  intro v hv
  apply h.injective
  ext w
  simpa using hv w

/-- In finite dimensions, a two-form is nondegenerate exactly when all its flat maps are
invertible. -/
theorem isNondegenerate_iff_isInvertible_flat [FiniteDimensional ℝ E] :
    σ.IsNondegenerate ↔ ∀ x, (σ.flat x).IsInvertible := by
  rw [isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot]
  -- For the alternating form at `x`, nondegeneracy is triviality of the kernel.
  refine forall_congr' fun x ↦ Iff.symm <| isInvertible_flat_iff.trans ?_
  exact (SmoothForm.isAlt_bilinFormAt σ x).isRefl.nondegenerate_iff_separatingLeft.trans
    LinearMap.separatingLeft_iff_ker_eq_bot

/-- The flat maps of a nondegenerate two-form on a finite-dimensional manifold are invertible. -/
theorem IsNondegenerate.isInvertible_flat [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
    (x : M) : (σ.flat x).IsInvertible :=
  isNondegenerate_iff_isInvertible_flat.1 h x

/-- **Linear maps preserving a nondegenerate form are surjective.** A linear map `D` from the
tangent space at `x` to the tangent space at `y` with `σ_y(D u, D v) = σ_x(u, v)` is injective
because `σ` is nondegenerate, hence surjective in finite dimension. -/
theorem IsNondegenerate.surjective_of_eval₂_map [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
    {x y : M} {D : TangentSpace I x →L[ℝ] TangentSpace I y}
    (hD : ∀ u v, SmoothBundleForm.eval₂ σ y (D u) (D v) = SmoothBundleForm.eval₂ σ x u v) :
    Function.Surjective D := by
  have hinj : Function.Injective D :=
    (injective_iff_map_eq_zero D).2 fun u hu ↦
      isNondegenerate_iff_separatingLeft.1 h x u fun w ↦ by
        rw [← hD, hu, ← flat_apply, map_zero, zero_apply]
  exact (LinearMap.injective_iff_surjective (f := (D.toLinearMap : E →ₗ[ℝ] E))).1 hinj

/-! ### Contraction of smooth vector fields -/

variable (σ) in
/-- Contraction `X ↦ ι_X σ = σ(X, ·)` of smooth vector fields into a two-form, as a linear map to
smooth one-forms. -/
def interiorₗ : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ →ₗ[ℝ] SmoothForm I M ℝ 1 where
  toFun X := ⟨RoughForm.interior X σ.1, by
    rw [funext (σ.interior_apply_eq_ofSubsingleton_flat X)]
    exact (isSmoothForm_ofSubsingleton_iff.2
      (σ.contMDiff_flat.clm_bundle_apply X.contMDiff)).mem_smoothBundleForms⟩
  map_add' X Y := Subtype.ext (RoughForm.interior_add_field _ _ σ.1)
  map_smul' c X := Subtype.ext (RoughForm.interior_smul_field (fun _ ↦ c) X σ.1)

/-- The one-form `ι_X σ` is the interior product of `σ` with `X`. -/
@[simp]
theorem coe_interiorₗ (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    (σ.interiorₗ X : RoughForm I M ℝ 1) = RoughForm.interior X σ.1 :=
  (rfl)

/-- As a section of the bundle of covectors, `ι_X σ` is the flat map applied to `X`. -/
@[simp]
theorem degreeOneEquiv_interiorₗ (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) (x : M) :
    SmoothForm.degreeOneEquiv (σ.interiorₗ X) x = σ.flat x (X x) := by
  ext v
  rw [SmoothForm.degreeOneEquiv_apply_apply, coe_interiorₗ,
    interior_apply_eq_ofSubsingleton_flat, ContinuousAlternatingMap.ofSubsingleton_apply_apply]

/-- For a nondegenerate two-form on a finite-dimensional manifold, contraction `X ↦ ι_X σ` is a
linear equivalence between smooth vector fields and smooth one-forms. Its inverse sends a one-form
`α` to the vector field `(σ♭)⁻¹ α`. -/
def IsNondegenerate.interiorEquiv [FiniteDimensional ℝ E] (h : σ.IsNondegenerate) :
    Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ ≃ₗ[ℝ] SmoothForm I M ℝ 1 where
  __ := σ.interiorₗ
  invFun α := ⟨fun x ↦ (σ.flat x).inverse (SmoothForm.degreeOneEquiv α x),
    (σ.contMDiff_flat.clm_bundle_inverse h.isInvertible_flat).clm_bundle_apply
      (SmoothForm.degreeOneEquiv α).contMDiff⟩
  left_inv X := ContMDiffSection.ext fun x ↦ by
    simp only [LinearMap.toFun_eq_coe, degreeOneEquiv_interiorₗ]
    exact (h.isInvertible_flat x).inverse_apply_self (X x)
  right_inv α := SmoothForm.degreeOneEquiv.injective <| ContMDiffSection.ext fun x ↦ by
    simp only [LinearMap.toFun_eq_coe, degreeOneEquiv_interiorₗ]
    exact (h.isInvertible_flat x).self_apply_inverse _

/-- The nondegenerate contraction equivalence is contraction. -/
@[simp]
theorem IsNondegenerate.interiorEquiv_apply [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
    (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) : h.interiorEquiv X = σ.interiorₗ X :=
  (rfl)

/-- The vector field contracting to a one-form `α` is `(σ♭)⁻¹ α`. -/
@[simp]
theorem IsNondegenerate.interiorEquiv_symm_apply [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (α : SmoothForm I M ℝ 1) (x : M) :
    h.interiorEquiv.symm α x = (σ.flat x).inverse (SmoothForm.degreeOneEquiv α x) :=
  (rfl)

/-- The vector field `(σ♭)⁻¹ α` contracts to `α`. -/
@[simp]
theorem IsNondegenerate.interiorₗ_interiorEquiv_symm [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (α : SmoothForm I M ℝ 1) : σ.interiorₗ (h.interiorEquiv.symm α) = α :=
  h.interiorEquiv.apply_symm_apply α

/-- The vector field `(σ♭)⁻¹ α` contracts to `α`, as rough forms: `ι_((σ♭)⁻¹ α) σ = α`. -/
@[simp]
theorem IsNondegenerate.interior_interiorEquiv_symm [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (α : SmoothForm I M ℝ 1) :
    RoughForm.interior (h.interiorEquiv.symm α) σ.1 = α.1 :=
  congrArg Subtype.val (h.interiorₗ_interiorEquiv_symm α)

/-- The vector field `(σ♭)⁻¹ α` vanishes exactly where `α` does. -/
theorem IsNondegenerate.interiorEquiv_symm_apply_eq_zero_iff [FiniteDimensional ℝ E]
    (h : σ.IsNondegenerate) (α : SmoothForm I M ℝ 1) (x : M) :
    h.interiorEquiv.symm α x = 0 ↔ α.1 x = 0 := by
  rw [interiorEquiv_symm_apply, (h.isInvertible_flat x).inverse_apply_eq, map_zero,
    ← SmoothForm.degreeOneEquiv_coe_eq_zero_iff, ← ContinuousLinearMap.toLinearMap_zero,
    ContinuousLinearMap.coe_inj]

/-! ### The skew part of an endomorphism field -/

section SkewPart

/-- Mathlib's derived `IsNormableSpace` instance on `TangentSpace I x` is stated with the model
space's `Module` instance instead of the tangent space's own one, so instance search never finds
it; restate it against the tangent space's structure. It is needed to transpose sections of
`Hom(TM, Hom(TM, ℝ))`. -/
local instance (x : M) : IsNormableSpace ℝ (TangentSpace I x) :=
  instIsNormableSpaceTangentSpace I x

/-- The bilinear forms `σ(C ·, ·)` of a section `C` of `End(TM)`, as a smooth section of
`Hom(TM, Hom(TM, ℝ))`. -/
def flatComp (σ : SmoothTwoForm I M)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯ :=
  (⟨σ.flat, σ.contMDiff_flat⟩ : Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯).clmComp C

/-- The bilinear form `σ(C ·, ·)` at a point is the flat map composed with `C`. -/
@[simp]
theorem flatComp_apply (σ : SmoothTwoForm I M)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M) :
    σ.flatComp C x = (σ.flat x).comp (C x) :=
  ContMDiffSection.clmComp_apply _ C x

/-- `C ↦ σ(C ·, ·)` is additive. -/
theorem flatComp_add (σ : SmoothTwoForm I M)
    (C D : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    σ.flatComp (C + D) = σ.flatComp C + σ.flatComp D := by
  ext1 x
  simp [ContinuousLinearMap.comp_add]

/-- `C ↦ σ(C ·, ·)` commutes with scalar multiplication. -/
theorem flatComp_smul (σ : SmoothTwoForm I M) (a : ℝ)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    σ.flatComp (a • C) = a • σ.flatComp C := by
  ext1 x
  simp

variable [FiniteDimensional ℝ E]

/-- The `σ`-skew part `(C - C^†) / 2` of a section `C` of `End(TM)`, where `C^†` is the adjoint
for a nondegenerate two-form `σ`: it is `(σ♭)⁻¹ ∘ (β + βᵀ) / 2` for the bilinear forms
`β = σ(C ·, ·)`. It is skew-adjoint for `σ` at every point
(`TauCeti.SmoothTwoForm.IsNondegenerate.skewPart_skew`) and keeps every value of `C` which is
already skew-adjoint (`TauCeti.SmoothTwoForm.IsNondegenerate.skewPart_apply_of_skew`). -/
def IsNondegenerate.skewPart (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯ :=
  (2⁻¹ : ℝ) • ((⟨fun x ↦ (σ.flat x).inverse,
      σ.contMDiff_flat.clm_bundle_inverse hσ.isInvertible_flat⟩ :
      Cₛ^∞⟮I; (E →L[ℝ] ℝ) →L[ℝ] E,
        fun x : M ↦ (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x⟯).clmComp
    (σ.flatComp C + ⟨fun x ↦ (σ.flatComp C x).flip, fun x ↦ contMDiffWithinAt_univ.1
      ((σ.flatComp C).contMDiff x).contMDiffWithinAt.clm_bundle_flip⟩))

/-- The defining identity of the skew part: `σ(S v, w) = (σ(C v, w) + σ(C w, v)) / 2`. -/
theorem IsNondegenerate.flat_skewPart_apply (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M)
    (v w : TangentSpace I x) :
    σ.flat x (hσ.skewPart C x v) w = 2⁻¹ * (σ.flat x (C x v) w + σ.flat x (C x w) v) := by
  simp [skewPart, (hσ.isInvertible_flat x).self_apply_inverse, mul_add]

/-- The skew part of a section is skew-adjoint for `σ` at every point. -/
theorem IsNondegenerate.skewPart_skew (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) (x : M)
    (v w : TangentSpace I x) :
    hσ.symplecticFormAt x (hσ.skewPart C x v) w + hσ.symplecticFormAt x v (hσ.skewPart C x w) =
      0 := by
  have h := (hσ.symplecticFormAt x).isAlt.neg_eq (hσ.skewPart C x w) v
  simp only [IsNondegenerate.symplecticFormAt_apply, ← flat_apply] at h ⊢
  rw [← h, hσ.flat_skewPart_apply, hσ.flat_skewPart_apply]
  ring

/-- The skew part does not change a value which is already skew-adjoint for `σ`. -/
theorem IsNondegenerate.skewPart_apply_of_skew (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) {x : M}
    (hC : ∀ v w, hσ.symplecticFormAt x (C x v) w + hσ.symplecticFormAt x v (C x w) = 0) :
    hσ.skewPart C x = C x := by
  ext v
  refine (hσ.isInvertible_flat x).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  have h₁ := hC v w
  have h₂ := (hσ.symplecticFormAt x).isAlt.neg_eq (C x w) v
  simp only [IsNondegenerate.symplecticFormAt_apply, ← flat_apply] at h₁ h₂
  rw [hσ.flat_skewPart_apply]
  linarith

/-- The skew part is idempotent: it is a projection onto the skew-adjoint sections. -/
@[simp]
theorem IsNondegenerate.skewPart_skewPart (hσ : σ.IsNondegenerate)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    hσ.skewPart (hσ.skewPart C) = hσ.skewPart C := by
  ext1 x
  exact hσ.skewPart_apply_of_skew _ (hσ.skewPart_skew C x)

/-- The skew part is additive. -/
theorem IsNondegenerate.skewPart_add (hσ : σ.IsNondegenerate)
    (C D : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    hσ.skewPart (C + D) = hσ.skewPart C + hσ.skewPart D := by
  ext x v
  refine (hσ.isInvertible_flat x).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  simp only [ContMDiffSection.coe_add, Pi.add_apply, add_apply, map_add,
    hσ.flat_skewPart_apply]
  ring

/-- The skew part commutes with scalar multiplication. -/
theorem IsNondegenerate.skewPart_smul (hσ : σ.IsNondegenerate) (a : ℝ)
    (C : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯) :
    hσ.skewPart (a • C) = a • hσ.skewPart C := by
  ext x v
  refine (hσ.isInvertible_flat x).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, smul_apply, map_smul,
    hσ.flat_skewPart_apply, smul_eq_mul]
  ring

/-- The skew part of the zero section is zero. -/
@[simp]
theorem IsNondegenerate.skewPart_zero (hσ : σ.IsNondegenerate) : hσ.skewPart 0 = 0 := by
  ext1 x
  refine hσ.skewPart_apply_of_skew _ fun v w ↦ ?_
  simp only [ContMDiffSection.coe_zero, Pi.zero_apply, zero_apply, map_zero,
    LinearMap.zero_apply, add_zero]

end SkewPart

end SmoothTwoForm

end TauCeti
