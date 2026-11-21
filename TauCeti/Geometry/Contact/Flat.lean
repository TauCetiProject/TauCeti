/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Translate
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
(`TauCeti.SmoothForm.IsContactForm.contactFlat_apply_eq_iff`), so the Reeb vector field
`TauCeti.SmoothForm.reebVectorField` is the inverse contact flat map applied to `α`
(`TauCeti.SmoothForm.IsContactForm.reebVectorField_eq_inverse_contactFlat`).

On smooth sections, `X ↦ ι_X dα + α(X) α` is a linear map from smooth vector fields to smooth
one-forms (`TauCeti.SmoothForm.contactFlatₗ`). For a contact form in finite dimensions it is a
linear equivalence (`TauCeti.SmoothForm.IsContactForm.contactFlatEquiv`), so the preimage of a
smooth one-form is a smooth vector field. In particular the Reeb vector field of a contact form is
smooth (`TauCeti.SmoothForm.IsContactForm.contMDiff_reebVectorField`). This smooth-section
construction and its evaluation and cancellation lemmas are adapted from the symplectic flat
equivalence `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv` and its accompanying API in
`TauCeti.Geometry.Symplectic.Manifold.Flat`.

## Main declarations

* `TauCeti.SmoothForm.contactFlat`: the contact flat map `v ↦ ι_v dα + α(v) α` at a point.
* `TauCeti.SmoothForm.contMDiff_contactFlat`: the contact flat maps form a smooth section.
* `TauCeti.SmoothForm.contMDiffAt_sectionAlong_contactFlat`: the contact flat maps of a smooth
  family of one-forms depend smoothly on the parameter.
* `TauCeti.SmoothForm.IsContactForm.isInvertible_contactFlat`: for a contact form in finite
  dimensions the contact flat maps are invertible.
* `TauCeti.SmoothForm.isContactFormAt_iff_isInvertible_contactFlat`: in odd finite dimension, a
  one-form is contact at a point exactly when its contact flat map there is invertible. Since
  invertibility is an open condition, this shows that the contact condition is open.
* `TauCeti.SmoothForm.IsContactForm.contactFlat_apply_eq_iff`: the preimage of `α` is
  characterized by the Reeb equations.
* `TauCeti.SmoothForm.IsContactForm.eq_of_mem_kerDistribution_of_forall_mextDeriv_eq`: `dα` is
  nondegenerate on the contact hyperplane `ker α`.
* `TauCeti.SmoothForm.contactFlatₗ`, `TauCeti.SmoothForm.IsContactForm.contactFlatEquiv`: the
  contact flat map on smooth sections, and its inverse for a contact form.
* `TauCeti.SmoothForm.IsContactForm.contactFlatEquiv_symm_self`,
  `TauCeti.SmoothForm.IsContactForm.contMDiff_reebVectorField`: the Reeb vector field corresponds
  to `α` under the contact flat equivalence, and is smooth.
* `TauCeti.SmoothForm.contMDiffAt_sectionAlong_reebVectorField`: the Reeb vector fields of a smooth
  family of contact forms depend smoothly on the parameter.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, AMS, 1997,
  Proposition 43.18.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold Topology

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
    α.contactFlat x v w = mextDeriv α.val x ![v, w] + α.val x ![v] * α.val x ![w] := by
  simp [contactFlat, SmoothBundleForm.eval₂_apply]

/-- The contact flat map evaluates as the bilinear form `dα + α ⊗ α` of linear algebra, the form
whose left separation characterizes contact covectors in odd finite dimension
(`Module.Dual.isContact_iff_separatingLeft_add_smulRight`). -/
theorem contactFlat_apply_eq_bilinFormAt_add_smulRight (α : SmoothForm I M ℝ 1) (x : M)
    (v w : TangentSpace I x) :
    α.contactFlat x v w = ((mextDerivₗ I 1 α).bilinFormAt x +
      (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ).smulRight
        (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)) v w := by
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, ← mextDeriv_eq_bilinFormAt, degreeOneEquiv_coe_apply,
    degreeOneEquiv_coe_apply, smul_eq_mul, contactFlat_apply]

/-- **Contact flat maps of a smooth family of one-forms.** Let `α m` be one-forms on `M` depending
on a parameter `m ∈ N`, and let `b : N → M`. If the values `(α m)_(b m)` and the exterior
derivatives `(dα m)_(b m)` depend `C^n` on `m`, as sections along `b`, then so do the contact flat
maps `(α m)♭_(b m)`, as a section of `Hom(TM, Hom(TM, ℝ))` along `b`. -/
theorem contMDiffAt_sectionAlong_contactFlat {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {b : N → M} {α : N → SmoothForm I M ℝ 1} {m₀ : N}
    (hα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m) ((α m).val
            (b m))) m₀)
    (hdα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m)
        (mextDeriv (α m).val (b m))) m₀) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (b m)
        ((α m).contactFlat (b m))) m₀ := by
  -- The contact flat map is the flat map of `dα` plus the rank-one map `α ⊗ α`. The flat map
  -- `flatL ℝ E ℝ` is typed over the model space `E`; the `show` reads it at the tangent space
  -- `TangentSpace I (b m)`, which is definitionally `E`, so that it can be added to `α ⊗ α`.
  have heq (m : N) : (α m).contactFlat (b m) =
      (show TangentSpace I (b m) →L[ℝ] TangentSpace I (b m) →L[ℝ] ℝ from
          ContinuousAlternatingMap.flatL ℝ E ℝ (mextDeriv (α m).val (b m))) +
        (degreeOneEquiv (α m) (b m)).smulRight (degreeOneEquiv (α m) (b m)) := by
    ext v w
    rw [contactFlat_apply, add_apply, add_apply]
    exact congrArg₂ (· + ·) (ContinuousAlternatingMap.flatL_apply_apply (E := E) _ v w).symm
      (by simp)
  simp only [heq]
  refine (SmoothTwoForm.contMDiffAt_sectionAlong_flatL hdα).add_sectionAlong ?_
  -- The values of `α m`, as linear maps.
  have hα₁ : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (b m)
        (degreeOneEquiv (α m) (b m))) m₀ :=
    contMDiffAt_sectionAlong_degreeOneEquiv_iff.2 hα
  exact hα₁.clm_bundle_smulRight hα₁

/-- **The contact flat maps form a smooth section** of the bundle `Hom(TM, Hom(TM, ℝ))`. -/
theorem contMDiff_contactFlat (α : SmoothForm I M ℝ 1) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (α.contactFlat x)) :=
  fun x₀ ↦ contMDiffAt_sectionAlong_contactFlat (b := id) (α := fun _ ↦ α) (α.contMDiff x₀)
    (contMDiff_mextDeriv α x₀)

/-! ### Invertibility of the contact flat map -/

/-- **The contact flat map at a contact point is invertible.** If `α` satisfies the pointwise
contact condition at `x`, its contact flat map at `x` is invertible, on a finite-dimensional
manifold. -/
theorem isInvertible_contactFlat_of_isContactFormAt [FiniteDimensional ℝ E] {x : M}
    (h : IsContactFormAt α.val x) : (α.contactFlat x).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_separatingLeft fun (v : TangentSpace I x) hv ↦
    (isContactFormAt_iff_isContact.1 h).separatingLeft_add_smulRight (isAlt_bilinFormAt _ x) v
      fun w ↦ (contactFlat_apply_eq_bilinFormAt_add_smulRight α x v w).symm.trans (hv w)

/-- **In odd dimension, an invertible contact flat map detects a contact point.** On a manifold
modelled on a space of odd finite dimension, if the contact flat map of `α` at `x` is invertible,
then `α` satisfies the pointwise contact condition at `x`. The parity hypothesis is needed: on
`ℝ²`, the form `α = (x dy - y dx) / 2` vanishes at the origin, where its contact flat map is the
invertible map `v ↦ ι_v (dx ∧ dy)`. -/
theorem isContactFormAt_of_isInvertible_contactFlat [FiniteDimensional ℝ E]
    (hodd : Odd (finrank ℝ E)) {x : M} (h : (α.contactFlat x).IsInvertible) :
    IsContactFormAt α.val x := by
  refine isContactFormAt_iff_isContact.2 (Module.Dual.isContact_of_separatingLeft_add_smulRight
    (V := TangentSpace I x) (isAlt_bilinFormAt _ x) hodd fun v hv ↦ h.bijective.1 ?_)
  ext w
  rw [contactFlat_apply_eq_bilinFormAt_add_smulRight, map_zero, zero_apply]
  exact hv w

/-- On a manifold modelled on a space of odd finite dimension, `α` satisfies the pointwise contact
condition at `x` exactly when its contact flat map at `x` is invertible. -/
theorem isContactFormAt_iff_isInvertible_contactFlat [FiniteDimensional ℝ E]
    (hodd : Odd (finrank ℝ E)) {x : M} :
    IsContactFormAt α.val x ↔ (α.contactFlat x).IsInvertible :=
  ⟨isInvertible_contactFlat_of_isContactFormAt, isContactFormAt_of_isInvertible_contactFlat hodd⟩

/-! ### Contact flat maps of contact forms -/

namespace IsContactForm

variable (hα : α.IsContactForm)
include hα

/-- A vector `v` solves `ι_v dα + α(v) α = α` exactly when it satisfies the Reeb equations
`α(v) = 1` and `ι_v dα = 0`. -/
theorem contactFlat_apply_eq_iff {x : M} {v : TangentSpace I x} :
    α.contactFlat x v = degreeOneEquiv α x ↔
      α.val x ![v] = 1 ∧ ∀ w, mextDeriv α.val x ![v, w] = 0 := by
  have h := (isContactForm_def.1 hα x).add_smulRight_apply_eq_self_iff
    (isAlt_bilinFormAt _ x) (r := v)
  simp only [LinearMap.ext_iff, ← contactFlat_apply_eq_bilinFormAt_add_smulRight,
    LinearMap.zero_apply] at h
  rw [ContinuousLinearMap.ext_iff]
  simpa using h

/-- **The contact flat map of a contact form is invertible** at every point of a
finite-dimensional manifold. -/
theorem isInvertible_contactFlat [FiniteDimensional ℝ E] (x : M) :
    (α.contactFlat x).IsInvertible :=
  isInvertible_contactFlat_of_isContactFormAt (isContactForm_iff_forall_isContactFormAt.1 hα x)

/-- The Reeb vector field of a contact form is the image of `α` under the inverse contact flat
map. -/
theorem reebVectorField_eq_inverse_contactFlat [FiniteDimensional ℝ E] (x : M) :
    α.reebVectorField x = (α.contactFlat x).inverse (degreeOneEquiv α x) := by
  rw [← hα.contactFlat_apply_eq_iff.2 ⟨hα.apply_reebVectorField x,
    hα.mextDeriv_reebVectorField_left x⟩, (hα.isInvertible_contactFlat x).inverse_apply_self]

/-- **`dα` is nondegenerate on the contact hyperplane.** Two vectors of the contact hyperplane
`ξ_x` with the same `dα_x`-pairing against `ξ_x` are equal. -/
theorem eq_of_mem_kerDistribution_of_forall_mextDeriv_eq [FiniteDimensional ℝ E] {x : M}
    {a b : TangentSpace I x} (ha : α.val x ![a] = 0) (hb : α.val x ![b] = 0)
    (hab : ∀ u ∈ α.kerDistribution x, mextDeriv α.val x ![a, u] = mextDeriv α.val x ![b, u]) :
    a = b := by
  -- The contact flat maps of `a` and `b` agree on the component of `v` in `ξ_x` and on the Reeb
  -- vector, which `dα_x` kills.
  refine (hα.isInvertible_contactFlat x).injective (ContinuousLinearMap.ext fun v ↦ ?_)
  have h := hab _ (hα.sub_smul_reebVectorField_mem_kerDistribution v)
  have hRa := hα.mextDeriv_reebVectorField_right x a
  have hRb := hα.mextDeriv_reebVectorField_right x b
  simp only [mextDeriv_eq_bilinFormAt] at h hRa hRb
  simp only [map_sub, map_smul, hRa, hRb, smul_zero, sub_zero] at h
  simpa only [contactFlat_apply, ha, hb, zero_mul, add_zero, mextDeriv_eq_bilinFormAt] using h

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
    (α.contactFlatₗ X).val x v = α.contactFlat x (X x) (v 0) := by
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

/-- The Reeb vector field of a contact form is the vector field corresponding to `α` under the
contact flat equivalence. -/
@[simp]
theorem IsContactForm.contactFlatEquiv_symm_self [FiniteDimensional ℝ E] (hα : α.IsContactForm) :
    ⇑(hα.contactFlatEquiv.symm α) = α.reebVectorField :=
  funext fun x ↦ by
    rw [hα.contactFlatEquiv_symm_apply, hα.reebVectorField_eq_inverse_contactFlat]

/-- **The Reeb vector field of a contact form is smooth.** -/
theorem IsContactForm.contMDiff_reebVectorField [FiniteDimensional ℝ E] (hα : α.IsContactForm) :
    ContMDiff I I.tangent ∞ (T% α.reebVectorField) := by
  rw [← hα.contactFlatEquiv_symm_self]
  exact (hα.contactFlatEquiv.symm α).contMDiff

/-- **Reeb vector fields of a smooth family of contact forms.** Let `α m` be one-forms on `M`
depending on a parameter `m ∈ N` which are contact forms for `m` near `m₀`, and let `b : N → M`.
If the values `(α m)_(b m)` and the exterior derivatives `(dα m)_(b m)` depend `C^n` on `m`, as
sections along `b`, then so do the Reeb vectors `R_(α m)(b m)`, as a map to the tangent bundle. -/
theorem contMDiffAt_sectionAlong_reebVectorField [FiniteDimensional ℝ E] {EN HN N : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] {n : WithTop ℕ∞}
    {b : N → M} {α : N → SmoothForm I M ℝ 1} {m₀ : N}
    (hc : ∀ᶠ m in 𝓝 m₀, (α m).IsContactForm)
    (hα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) (b m) ((α m).val
            (b m))) m₀)
    (hdα : ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) (b m)
        (mextDeriv (α m).val (b m))) m₀) :
    ContMDiffAt J I.tangent n
      (fun m ↦ (⟨b m, (α m).reebVectorField (b m)⟩ : TangentBundle I M)) m₀ := by
  have h := (ContMDiffAt.clm_bundle_inverse (x := m₀) (ϕ := fun m ↦ (α m).contactFlat (b m))
    (contMDiffAt_sectionAlong_contactFlat hα hdα)
    (hc.self_of_nhds.isInvertible_contactFlat (b m₀))).clm_bundle_apply
      (contMDiffAt_sectionAlong_degreeOneEquiv_iff.2 hα)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hc] with m hm
  rw [hm.reebVectorField_eq_inverse_contactFlat]

end SmoothForm

end TauCeti
