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
# The flat map of a contact form

A one-form `α` on a manifold `M` gives at each point its **contact flat map**
`α♭_x : T_x M → T_x^* M`, `v ↦ ι_v dα + α(v) α` (`TauCeti.SmoothForm.contactFlat`). It is the sum
of the flat map `v ↦ ι_v dα` of the two-form `dα` and of the rank-one map `v ↦ α(v) α`, and these
maps form a smooth section of the bundle `Hom(TM, Hom(TM, ℝ))`
(`TauCeti.SmoothForm.contMDiff_contactFlat`).

For a contact form on a finite-dimensional manifold, the flat map `v ↦ ι_v dα` alone is never
invertible, since an alternating form in odd dimension is degenerate. Adding `α ⊗ α` repairs this:
every contact flat map is then invertible
(`TauCeti.SmoothForm.IsContactForm.isInvertible_contactFlat`). Indeed if `ι_v dα + α(v) α = 0`,
then evaluating at `v` gives `α(v)² = 0`, so `v ∈ ker α` is `dα`-orthogonal to `ker α`, and `v = 0`
because `dα` is nondegenerate on `ker α`. Inverting it solves the pointwise linear equations which
define vector fields from a contact form, such as the Reeb vector field `R_α` and contact
Hamiltonian vector fields. The Reeb vector field is the preimage of `α` itself: the solutions
of `ι_v dα + α(v) α = α` are exactly the vectors with `α(v) = 1` and `ι_v dα = 0`
(`TauCeti.SmoothForm.IsContactForm.contactFlat_apply_eq_iff`).

On smooth sections, `X ↦ ι_X dα + α(X) α` is a linear map from smooth vector fields to smooth
one-forms (`TauCeti.SmoothForm.contactFlatₗ`). For a contact form in finite dimensions it is a
linear equivalence (`TauCeti.SmoothForm.IsContactForm.contactFlatEquiv`), so the preimage of a
smooth one-form is a smooth vector field. This smooth-section construction and its evaluation and
cancellation lemmas are adapted from the symplectic flat equivalence
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` and its accompanying API in
`TauCeti.Geometry.Symplectic.Manifold.Flat`.

## Main declarations

* `TauCeti.SmoothForm.contactFlat`: the contact flat map `v ↦ ι_v dα + α(v) α` at a point.
* `TauCeti.SmoothForm.contMDiff_contactFlat`: the contact flat maps form a smooth section.
* `TauCeti.SmoothForm.IsContactForm.isInvertible_contactFlat`: for a contact form in finite
  dimensions the contact flat maps are invertible.
* `TauCeti.SmoothForm.IsContactForm.contactFlat_apply_eq_iff`: the preimage of `α` is
  characterized by the Reeb equations.
* `TauCeti.SmoothForm.contactFlatₗ`, `TauCeti.SmoothForm.IsContactForm.contactFlatEquiv`: the
  contact flat map on smooth sections, and its inverse for a contact form.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, AMS, 1997,
  Proposition 43.18.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1}

/-- The **contact flat map** of a real one-form `α` at a point `x`: the map
`v ↦ ι_v dα + α(v) α` from the tangent space to its dual. For a contact form on a
finite-dimensional manifold it is invertible
(`TauCeti.SmoothForm.IsContactForm.isInvertible_contactFlat`). -/
def contactFlat (α : SmoothForm I M ℝ 1) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  SmoothTwoForm.flat (mextDerivₗ I 1 α) x + (degreeOneEquiv α x).smulRight (degreeOneEquiv α x)

/-- The contact flat map evaluates as `(v, w) ↦ dα(v, w) + α(v) α(w)`. -/
@[simp]
theorem contactFlat_apply (α : SmoothForm I M ℝ 1) (x : M) (v w : TangentSpace I x) :
    α.contactFlat x v w = mextDeriv α.1 x ![v, w] + α.1 x ![v] * α.1 x ![w] := by
  simp [contactFlat, SmoothBundleForm.eval₂_apply, ← degreeOneEquiv_coe_apply]

/-- **The contact flat maps form a smooth section** of the bundle `Hom(TM, Hom(TM, ℝ))`. -/
theorem contMDiff_contactFlat (α : SmoothForm I M ℝ 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (α.contactFlat x)) := by
  refine (SmoothTwoForm.contMDiff_flat _).add_section fun x₀ ↦ ?_
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hα := ((contMDiffAt_hom_bundle _).1 ((degreeOneEquiv α).contMDiff x₀)).2
  -- In coordinates, `α ⊗ α` is `smulRight` applied twice to the coordinate expression of `α`.
  refine (((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).contDiff.comp_contMDiffAt
    hα).clm_apply hα).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ) hy hy (Set.mem_univ _)]
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.inCoordinates_eq (E' := Trivial M ℝ) hy
    (by simp [Trivial.eq_trivialization M ℝ])]
  simp [Trivial.eq_trivialization M ℝ]

/-! ### Contact flat maps of contact forms -/

namespace IsContactForm

variable (hα : α.IsContactForm)
include hα

/-- A vector `v` solves `ι_v dα + α(v) α = α` exactly when it satisfies the Reeb equations
`α(v) = 1` and `ι_v dα = 0`. -/
theorem contactFlat_apply_eq_iff {x : M} {v : TangentSpace I x} :
    α.contactFlat x v = degreeOneEquiv α x ↔
      α.1 x ![v] = 1 ∧ ∀ w, mextDeriv α.1 x ![v, w] = 0 := by
  have h := (isContactForm_def.1 hα x).add_smulRight_apply_eq_self_iff
    (isAlt_bilinFormAt _ x) (r := v)
  simp only [LinearMap.ext_iff, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
    degreeOneEquiv_coe_apply, LinearMap.zero_apply, smul_eq_mul] at h
  rw [ContinuousLinearMap.ext_iff]
  simpa [degreeOneEquiv_apply_apply, ← Matrix.vec_single_eq_const] using h

/-- **The contact flat map of a contact form is invertible** at every point of a
finite-dimensional manifold. -/
theorem isInvertible_contactFlat [FiniteDimensional ℝ E] (x : M) :
    (α.contactFlat x).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_separatingLeft (E := E) fun (v : TangentSpace I x) hv ↦
    (isContactForm_def.1 hα x).separatingLeft_add_smulRight (isAlt_bilinFormAt _ x) v fun w ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.smul_apply, bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
        degreeOneEquiv_coe_apply, degreeOneEquiv_coe_apply, smul_eq_mul]
      exact (contactFlat_apply α x v w).symm.trans (hv w)

end IsContactForm

/-! ### Smooth sections -/

variable (α) in
/-- The contact flat map on smooth sections, `X ↦ ι_X dα + α(X) α`, as a linear map from smooth
vector fields to smooth one-forms. -/
def contactFlatₗ : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ →ₗ[ℝ] SmoothForm I M ℝ 1 where
  toFun X := degreeOneEquiv.symm ⟨fun x ↦ α.contactFlat x (X x),
    (contMDiff_contactFlat α).clm_bundle_apply X.contMDiff⟩
  map_add' X Y := by
    rw [← map_add]
    congr 1
    exact ContMDiffSection.ext fun x ↦ map_add (α.contactFlat x) (X x) (Y x)
  map_smul' c X := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact ContMDiffSection.ext fun x ↦ map_smul (α.contactFlat x) c (X x)

/-- As a section of the bundle of covectors, `ι_X dα + α(X) α` is the contact flat map applied
to `X`. -/
@[simp]
theorem degreeOneEquiv_contactFlatₗ (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) (x : M) :
    degreeOneEquiv (α.contactFlatₗ X) x = α.contactFlat x (X x) := by
  simp [contactFlatₗ]

/-- The one-form `ι_X dα + α(X) α` evaluates a tangent vector as the contact flat map applied to
`X`. -/
@[simp]
theorem contactFlatₗ_apply (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (α.contactFlatₗ X).1 x v = α.contactFlat x (X x) (v 0) := by
  simp [contactFlatₗ]

/-- For a contact form on a finite-dimensional manifold, `X ↦ ι_X dα + α(X) α` is a linear
equivalence between smooth vector fields and smooth one-forms. Its inverse sends a one-form `θ`
to the vector field `x ↦ (α♭_x)⁻¹ θ_x`. -/
def IsContactForm.contactFlatEquiv [FiniteDimensional ℝ E] (hα : α.IsContactForm) :
    Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ ≃ₗ[ℝ] SmoothForm I M ℝ 1 where
  __ := α.contactFlatₗ
  invFun θ := ⟨fun x ↦ (α.contactFlat x).inverse (degreeOneEquiv θ x),
    ((contMDiff_contactFlat α).clm_bundle_inverse hα.isInvertible_contactFlat).clm_bundle_apply
      (degreeOneEquiv θ).contMDiff⟩
  left_inv X := ContMDiffSection.ext fun x ↦ by
    simp only [LinearMap.toFun_eq_coe, degreeOneEquiv_contactFlatₗ]
    exact (hα.isInvertible_contactFlat x).inverse_apply_self (X x)
  right_inv θ := degreeOneEquiv.injective <| ContMDiffSection.ext fun x ↦ by
    simp only [LinearMap.toFun_eq_coe, degreeOneEquiv_contactFlatₗ]
    exact (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- The contact flat equivalence is the contact flat map on smooth sections. -/
@[simp]
theorem IsContactForm.contactFlatEquiv_apply [FiniteDimensional ℝ E] (hα : α.IsContactForm)
    (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) : hα.contactFlatEquiv X = α.contactFlatₗ X :=
  (rfl)

/-- The vector field corresponding to a one-form `θ` is `x ↦ (α♭_x)⁻¹ θ_x`. -/
@[simp]
theorem IsContactForm.contactFlatEquiv_symm_apply [FiniteDimensional ℝ E] (hα : α.IsContactForm)
    (θ : SmoothForm I M ℝ 1) (x : M) :
    hα.contactFlatEquiv.symm θ x = (α.contactFlat x).inverse (degreeOneEquiv θ x) :=
  (rfl)

/-- The contact flat map sends the vector field corresponding to `θ` back to `θ`, pointwise. -/
@[simp↓]
theorem IsContactForm.contactFlat_contactFlatEquiv_symm [FiniteDimensional ℝ E]
    (hα : α.IsContactForm) (θ : SmoothForm I M ℝ 1) (x : M) :
    α.contactFlat x (hα.contactFlatEquiv.symm θ x) = degreeOneEquiv θ x :=
  (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- The vector field corresponding to `θ` is sent back to `θ` by `X ↦ ι_X dα + α(X) α`. -/
@[simp]
theorem IsContactForm.contactFlatₗ_contactFlatEquiv_symm [FiniteDimensional ℝ E]
    (hα : α.IsContactForm) (θ : SmoothForm I M ℝ 1) :
    α.contactFlatₗ (hα.contactFlatEquiv.symm θ) = θ :=
  hα.contactFlatEquiv.apply_symm_apply θ

end SmoothForm

end TauCeti
