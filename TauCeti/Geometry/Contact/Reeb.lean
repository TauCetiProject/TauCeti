/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The Reeb vector field of a contact form

A vector field `R` is a **Reeb vector field** of a one-form `α` when `α(R) = 1` and `ι_R dα = 0`
at every point (`TauCeti.SmoothForm.IsReebField`). A contact form has exactly one Reeb vector
field, and it is smooth.

The construction inverts, at each point `x`, the linear map
`v ↦ ι_v dα + α(v) α` from tangent vectors to covectors (`TauCeti.SmoothForm.reebOperator`).
For a contact form this map is injective: testing `ι_v dα + α(v) α = 0` against `v` gives
`α(v)² = 0`, so `v ∈ ker α`, and then `ι_v dα` vanishes on `ker α`, which forces `v = 0` because
`dα` is nondegenerate on `ker α`. In finite dimension it is therefore invertible, and the Reeb
vector at `x` is the preimage of `α_x` (`TauCeti.SmoothForm.reebField`). The maps
`v ↦ ι_v dα + α(v) α` form a smooth section of the bundle `Hom(TM, Hom(TM, ℝ))`, so their inverses
do too, and the Reeb vector field is smooth
(`TauCeti.SmoothForm.IsContactForm.contMDiff_reebField`).

The Reeb vector field depends on the contact form, not only on the contact distribution: the
constant multiple `c α` has Reeb vector field `c⁻¹ R`
(`TauCeti.SmoothForm.IsContactForm.reebField_smul`).

## Main declarations

* `TauCeti.SmoothForm.IsReebField`: the equations `α(R) = 1` and `ι_R dα = 0`.
* `TauCeti.SmoothForm.reebOperator`: the map `v ↦ ι_v dα + α(v) α` at a point, a smooth section
  of `Hom(TM, Hom(TM, ℝ))` (`TauCeti.SmoothForm.contMDiff_reebOperator`), invertible for a contact
  form (`TauCeti.SmoothForm.IsContactForm.isInvertible_reebOperator`).
* `TauCeti.SmoothForm.reebField`: the vector field `x ↦ (reebOperator α x)⁻¹ α_x`.
* `TauCeti.SmoothForm.IsContactForm.isReebField_reebField`,
  `TauCeti.SmoothForm.IsContactForm.isReebField_iff_eq`: existence and uniqueness of the Reeb
  vector field.
* `TauCeti.SmoothForm.IsContactForm.contMDiff_reebField`: the Reeb vector field is smooth.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Predicate

variable [IsManifold I 2 M] {α : SmoothForm I M ℝ 1} {R R' : (x : M) → TangentSpace I x}

/-- A vector field `R` is a **Reeb vector field** of a one-form `α` when, at every point, `R` is a
Reeb vector of the covector `α_x` and the bilinear form `dα_x`: `α(R) = 1` and `ι_R dα = 0`. -/
def IsReebField (α : SmoothForm I M ℝ 1) (R : (x : M) → TangentSpace I x) : Prop :=
  ∀ x, Module.Dual.IsReebVector (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
    ((mextDerivₗ I 1 α).bilinFormAt x) (R x)

/-- The defining equations of a Reeb vector field: `α(R) = 1` and `dα(R, v) = 0` for every tangent
vector `v`. -/
theorem isReebField_iff :
    α.IsReebField R ↔ ∀ x, α.1 x ![R x] = 1 ∧ ∀ v, mextDeriv α.1 x ![R x, v] = 0 := by
  refine forall_congr' fun x ↦ ?_
  simp only [Module.Dual.isReebVector_iff, degreeOneEquiv_coe_apply, bilinFormAt_apply,
    eval₂_apply, mextDerivₗ_apply]

/-- A Reeb vector field of `α` has `α(R) = 1`. -/
theorem IsReebField.apply_eq_one (hR : α.IsReebField R) (x : M) : α.1 x ![R x] = 1 :=
  (isReebField_iff.1 hR x).1

/-- A Reeb vector field of `α` lies in the kernel of `dα`: `dα(R, v) = 0`. -/
theorem IsReebField.mextDeriv_apply_eq_zero (hR : α.IsReebField R) (x : M)
    (v : TangentSpace I x) : mextDeriv α.1 x ![R x, v] = 0 :=
  (isReebField_iff.1 hR x).2 v

/-- A Reeb vector field is transverse to the kernel of its form. -/
theorem IsReebField.notMem_kerDistribution (hR : α.IsReebField R) (x : M) :
    R x ∉ α.kerDistribution x := by
  rw [mem_kerDistribution, hR.apply_eq_one]
  exact one_ne_zero

/-- **Uniqueness of the Reeb vector field.** A contact form has at most one Reeb vector field. -/
theorem IsContactForm.isReebField_unique (hα : α.IsContactForm) (hR : α.IsReebField R)
    (hR' : α.IsReebField R') : R = R' :=
  funext fun x ↦ (isContactForm_def.1 hα x).isReebVector_unique (hR x) (hR' x)

/-- If `R` is a Reeb vector field of `α`, then `c⁻¹ R` is a Reeb vector field of `c α`, for a
nonzero constant `c`. -/
theorem IsReebField.smul (hR : α.IsReebField R) {c : ℝ} (hc : c ≠ 0) :
    (c • α).IsReebField (fun x ↦ c⁻¹ • R x) := fun x ↦ by
  have ha : (degreeOneEquiv (c • α) x : TangentSpace I x →ₗ[ℝ] ℝ) =
      c • (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) := by
    ext v
    simp
  have hB : (mextDerivₗ I 1 (c • α)).bilinFormAt x = c • (mextDerivₗ I 1 α).bilinFormAt x := by
    ext v w
    simp
  rw [ha, hB]
  exact (hR x).smul hc

end Predicate

section Construction

variable [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}

/-- The linear map `v ↦ ι_v dα + α(v) α` from the tangent space at `x` to its dual. For a contact
form it is invertible (`TauCeti.SmoothForm.IsContactForm.isInvertible_reebOperator`), and the Reeb
vector at `x` is the preimage of `α_x`. -/
def reebOperator (α : SmoothForm I M ℝ 1) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  SmoothTwoForm.flat (mextDerivₗ I 1 α) x + (degreeOneEquiv α x).smulRight (degreeOneEquiv α x)

/-- The map `reebOperator α x` sends `v` to `w ↦ dα(v, w) + α(v) α(w)`. -/
@[simp]
theorem reebOperator_apply (α : SmoothForm I M ℝ 1) (x : M) (v w : TangentSpace I x) :
    α.reebOperator x v w = mextDeriv α.1 x ![v, w] + α.1 x ![v] * α.1 x ![w] := by
  simp [reebOperator, eval₂_apply, ← Matrix.vec_single_eq_const]

/-- The section `x ↦ α_x ⊗ α_x` of the bundle `Hom(TM, Hom(TM, ℝ))`, sending `v` to `α_x(v) α_x`,
is smooth. -/
private theorem contMDiff_smulRight_degreeOneEquiv (α : SmoothForm I M ℝ 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((degreeOneEquiv α x).smulRight (degreeOneEquiv α x))) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hα := (contMDiffAt_hom_bundle _).1 ((degreeOneEquiv α).contMDiff x₀)
  -- In coordinates, the section is `A ⊗ A` for the coordinate expression `A` of `α`.
  refine (((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).contDiff.comp_contMDiffAt
    hα.2).clm_apply hα.2).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ) hy hy (Set.mem_univ _)]
  simp [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, Trivialization.symmL_apply _ hy]

/-- **The maps `v ↦ ι_v dα + α(v) α` form a smooth section** of the bundle
`Hom(TM, Hom(TM, ℝ))`. -/
theorem contMDiff_reebOperator (α : SmoothForm I M ℝ 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (α.reebOperator x)) :=
  (SmoothTwoForm.contMDiff_flat _).add_section (contMDiff_smulRight_degreeOneEquiv α)

/-- For a contact form on a finite-dimensional manifold, the map `v ↦ ι_v dα + α(v) α` is
invertible at every point. -/
theorem IsContactForm.isInvertible_reebOperator [FiniteDimensional ℝ E] (hα : α.IsContactForm)
    (x : M) : (α.reebOperator x).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_separatingLeft (E := E) fun (v : TangentSpace I x) hv ↦
    (isContactForm_def.1 hα x).eq_zero_of_forall_add_mul_eq_zero (isAlt_bilinFormAt _ x) fun w ↦ by
      -- `L.toBilinForm v w` is `L v w` by definition.
      have h : α.reebOperator x v w = 0 := hv w
      rw [reebOperator_apply] at h
      simpa [eval₂_apply, degreeOneEquiv_apply_apply, ← Matrix.vec_single_eq_const] using h

/-- The **Reeb vector field** of a one-form `α`: at each point `x`, the preimage of `α_x` under the
map `v ↦ ι_v dα + α(v) α`. For a contact form on a finite-dimensional manifold, this is the unique
Reeb vector field (`TauCeti.SmoothForm.IsContactForm.isReebField_iff_eq`). -/
def reebField (α : SmoothForm I M ℝ 1) (x : M) : TangentSpace I x :=
  (α.reebOperator x).inverse (degreeOneEquiv α x)

/-- **Existence of the Reeb vector field.** The Reeb vector field of a contact form on a
finite-dimensional manifold satisfies `α(R) = 1` and `ι_R dα = 0`. -/
theorem IsContactForm.isReebField_reebField [FiniteDimensional ℝ E] (hα : α.IsContactForm) :
    α.IsReebField α.reebField := fun x ↦ by
  refine ((isContactForm_def.1 hα x).isReebVector_iff_forall_add_mul_eq
    (isAlt_bilinFormAt _ x)).2 fun w ↦ ?_
  have h := congrArg (fun φ ↦ φ w) ((hα.isInvertible_reebOperator x).self_apply_inverse
    (degreeOneEquiv α x))
  simpa [reebField, eval₂_apply, degreeOneEquiv_apply_apply, ← Matrix.vec_single_eq_const]
    using h

/-- **Existence and uniqueness of the Reeb vector field.** On a finite-dimensional manifold, a
vector field is a Reeb vector field of a contact form `α` exactly when it is `reebField α`. -/
theorem IsContactForm.isReebField_iff_eq [FiniteDimensional ℝ E] (hα : α.IsContactForm)
    {R : (x : M) → TangentSpace I x} : α.IsReebField R ↔ R = α.reebField :=
  ⟨fun hR ↦ hα.isReebField_unique hR hα.isReebField_reebField,
    fun h ↦ h ▸ hα.isReebField_reebField⟩

/-- The Reeb vector field of a contact form `α` has `α(R) = 1`. -/
@[simp]
theorem IsContactForm.apply_reebField [FiniteDimensional ℝ E] (hα : α.IsContactForm) (x : M) :
    α.1 x ![α.reebField x] = 1 :=
  hα.isReebField_reebField.apply_eq_one x

/-- The Reeb vector field of a contact form `α` lies in the kernel of `dα`. -/
@[simp]
theorem IsContactForm.mextDeriv_reebField [FiniteDimensional ℝ E] (hα : α.IsContactForm) (x : M)
    (v : TangentSpace I x) : mextDeriv α.1 x ![α.reebField x, v] = 0 :=
  hα.isReebField_reebField.mextDeriv_apply_eq_zero x v

/-- **The Reeb vector field of a contact form is smooth.** -/
theorem IsContactForm.contMDiff_reebField [FiniteDimensional ℝ E] (hα : α.IsContactForm) :
    ContMDiff I I.tangent ∞ (T% α.reebField) :=
  (α.contMDiff_reebOperator.clm_bundle_inverse hα.isInvertible_reebOperator).clm_bundle_apply
    (degreeOneEquiv α).contMDiff

/-- **Rescaling the Reeb vector field.** For a nonzero constant `c`, the Reeb vector field of the
contact form `c α` is `c⁻¹` times that of `α`. -/
theorem IsContactForm.reebField_smul [FiniteDimensional ℝ E] (hα : α.IsContactForm) {c : ℝ}
    (hc : c ≠ 0) : (c • α).reebField = fun x ↦ c⁻¹ • α.reebField x :=
  (((isContactForm_smul_iff hc).2 hα).isReebField_iff_eq.1
    (hα.isReebField_reebField.smul hc)).symm

end Construction

end SmoothForm

end TauCeti
