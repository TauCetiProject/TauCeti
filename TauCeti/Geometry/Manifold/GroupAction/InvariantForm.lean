/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Quotient
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Invariant differential forms on an action groupoid

Let a discrete monoid `G` act on a smooth manifold `X` by smooth maps, and let `G ⋉ X` be the
action groupoid, with its smooth object and arrow manifolds. A smooth form `φ` on the objects is
*invariant* if its pullbacks along the source and the target to the arrow manifold agree,
`s^* φ = t^* φ`. These forms make up the submodule `TauCeti.ActionGroupoid.invariantForms`. They
are the differential forms of the orbifold presented by `G ⋉ X`.

Every label is a separate open slice of arrows, on which the target is the translate of the
source by that label. So a form is invariant exactly when the corresponding form on `X` is
preserved by every element of `G`
(`TauCeti.ActionGroupoid.mpullback_objectDiffeomorph_mem_invariantForms_iff`). Elements acting
trivially on `X` are arrows of `G ⋉ X` as well, but they impose no condition on forms.

Invariant forms are closed under the exterior derivative and under wedge products, and they pull
back to invariant forms along the functor induced by a smooth equivariant map. When the action is a
free, properly discontinuous group action, the invariant forms are exactly the forms on the orbit
manifold `X / G`: `TauCeti.ActionGroupoid.invariantFormsEquivQuotient` identifies a form on `X / G`
with its pullback along the orbit map, compatibly with the exterior derivative.

## Main definitions

* `TauCeti.ActionGroupoid.invariantForms`: the smooth forms `φ` on the objects of `G ⋉ X` with
  `s^* φ = t^* φ`.
* `TauCeti.ActionGroupoid.invariantFormsEquivQuotient`: for a free, properly discontinuous action,
  the invariant forms are the forms on the orbit manifold.

## Main results

* `TauCeti.ActionGroupoid.mpullback_objectDiffeomorph_mem_invariantForms_iff`,
  `TauCeti.ActionGroupoid.mem_invariantForms_iff_forall_mpullback_smul`: a form is invariant
  exactly when every element of `G` preserves the corresponding form on `X`.
* `TauCeti.ActionGroupoid.mextDerivₗ_mem_invariantForms`,
  `TauCeti.ActionGroupoid.wedgeWith_mem_invariantForms`: invariant forms are closed under the
  exterior derivative and the wedge product.
* `TauCeti.ActionGroupoid.mpullback_map_obj_mem_invariantForms`: invariant forms pull back to
  invariant forms along the functor induced by a smooth equivariant map.
* `TauCeti.ActionGroupoid.invariantFormsEquivQuotient_mextDerivₗ`: the identification with forms on
  the orbit manifold commutes with the exterior derivative.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 2, for differential forms on an
  orbifold as the forms on the objects of a presenting groupoid with `s^* φ = t^* φ`.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1, for
  action groupoids.
-/

public noncomputable section

open CategoryTheory Topology
open CategoryTheory.ActionCategory
open scoped Manifold ContDiff

namespace TauCeti.ActionGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (G X : Type*) [TopologicalSpace X] [ChartedSpace H X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)

section Monoid

variable [Monoid G] [TopologicalSpace G] [DiscreteTopology G] [MulAction G X]

variable {I G X F k}

/-- The point underlying the source of an arrow of `G ⋉ X`, as a map from the arrow manifold to
`X`, has surjective derivative, so pullback along it detects forms pointwise. -/
private theorem surjective_mfderiv_back_left (a : Quiver.Total (ActionCategory G X)) :
    Function.Surjective
      (mfderiv I I (fun b : Quiver.Total (ActionCategory G X) ↦ b.left.back) a) := by
  have ho := (objectDiffeomorph I ∞ G X).isInvertible_mfderiv (x := a.left) (by simp)
  have hs := (isLocalDiffeomorph_source I ∞ G X).isInvertible_mfderiv (by simp) a
  have hcomp : (fun b : Quiver.Total (ActionCategory G X) ↦ b.left.back) =
      objectDiffeomorph I ∞ G X ∘ Quiver.Total.left :=
    funext fun b ↦ (objectDiffeomorph_apply I ∞ G X b.left).symm
  rw [hcomp, mfderiv_comp a ((objectDiffeomorph I ∞ G X).contMDiff.mdifferentiableAt (by simp))
    ((isLocalDiffeomorph_source I ∞ G X).contMDiff.mdifferentiableAt (by simp))]
  exact ho.surjective.comp hs.surjective

variable [ContMDiffConstSMul I ∞ G X]

/-- At an arrow labelled `g`, the pullback of a form on `X` along the point underlying the target
is the pullback along the point underlying the source of its translate by `g`: on the open slice
of arrows labelled `g`, the target is the translate of the source by `g`. -/
private theorem mpullback_back_right_apply (α : RoughForm I X F k)
    (a : Quiver.Total (ActionCategory G X)) :
    mpullback I I (fun b : Quiver.Total (ActionCategory G X) ↦ b.right.back) α a =
      mpullback I I (fun b : Quiver.Total (ActionCategory G X) ↦ b.left.back)
        (mpullback I I (a.hom.hom • ·) α) a := by
  have hev : (fun b : Quiver.Total (ActionCategory G X) ↦ b.right.back) =ᶠ[𝓝 a]
      (a.hom.hom • ·) ∘ fun b ↦ b.left.back := by
    filter_upwards [((isOpen_discrete {a.hom.hom}).preimage (continuous_label G X)).mem_nhds rfl]
      with b hb
    rw [Function.comp_apply, ← show b.hom.hom = a.hom.hom from hb]
    exact b.hom.map_val.symm
  have hback : ContMDiff I I ∞ fun b : Quiver.Total (ActionCategory G X) ↦ b.left.back :=
    (contMDiff_objects_iff I ∞).1 (isLocalDiffeomorph_source I ∞ G X).contMDiff
  rw [hev.mpullback_eq, mpullback_comp_at (hback.mdifferentiableAt (by simp))
    ((contMDiff_const_smul (I := I) (n := ∞) a.hom.hom).mdifferentiableAt (by simp))]

/-- A rough form on `X` has the same pullbacks along the points underlying the source and the
target of the arrows of `G ⋉ X` exactly when every element of `G` preserves it. -/
private theorem mpullback_back_left_eq_mpullback_back_right_iff (α : RoughForm I X F k) :
    mpullback I I (fun b : Quiver.Total (ActionCategory G X) ↦ b.left.back) α =
        mpullback I I (fun b : Quiver.Total (ActionCategory G X) ↦ b.right.back) α ↔
      ∀ g : G, mpullback I I (g • ·) α = α := by
  refine ⟨fun h g ↦ funext fun x ↦ ?_, fun h ↦ funext fun a ↦ ?_⟩
  · -- Test the equality at the arrow labelled `g` with source `x`.
    let a := (totalEquiv G X).symm (g, x)
    have ha : a.hom.hom = g := totalEquiv_symm_apply_hom_hom (g, x)
    have hx : a.left.back = x := by
      rw [totalEquiv_symm_apply_left, ← objectDiffeomorph_symm_apply I ∞,
        ← objectDiffeomorph_apply I ∞, Diffeomorph.apply_symm_apply]
    have := congrFun h a
    rw [mpullback_back_right_apply, ha] at this
    rw [← hx]
    exact ((mpullback_apply_eq_mpullback_apply_iff (surjective_mfderiv_back_left a)).1
      this).symm
  · rw [mpullback_back_right_apply, h]

variable [IsManifold I ∞ X]

variable (I G X F k) in
/-- The invariant smooth `k`-forms on the objects of the action groupoid `G ⋉ X`: the forms `φ`
whose pullbacks along the source and the target to the arrow manifold agree, `s^* φ = t^* φ`. -/
def invariantForms : Submodule ℝ (SmoothForm I (ActionCategory G X) F k) :=
  LinearMap.eqLocus
    (SmoothForm.mpullback Quiver.Total.left (isLocalDiffeomorph_source I ∞ G X).contMDiff)
    (SmoothForm.mpullback Quiver.Total.right (contMDiff_target I ∞ G X))

/-- A form on the objects of `G ⋉ X` is invariant exactly when its pullbacks along the source and
the target agree. -/
theorem mem_invariantForms_iff {φ : SmoothForm I (ActionCategory G X) F k} :
    φ ∈ invariantForms I G X F k ↔
      SmoothForm.mpullback Quiver.Total.left (isLocalDiffeomorph_source I ∞ G X).contMDiff φ =
        SmoothForm.mpullback Quiver.Total.right (contMDiff_target I ∞ G X) φ :=
  LinearMap.mem_eqLocus

/-- A form on `X`, transported to the objects of `G ⋉ X`, is invariant exactly when every element
of `G` preserves it. -/
theorem mpullback_objectDiffeomorph_mem_invariantForms_iff {α : SmoothForm I X F k} :
    SmoothForm.mpullback (objectDiffeomorph I ∞ G X) (objectDiffeomorph I ∞ G X).contMDiff α ∈
        invariantForms I G X F k ↔
      ∀ g : G, SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) α = α := by
  rw [mem_invariantForms_iff, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← SmoothForm.mpullback_comp, ← SmoothForm.mpullback_comp, Subtype.ext_iff]
  simp only [SmoothForm.coe_mpullback, Subtype.ext_iff, Function.comp_def,
    objectDiffeomorph_apply]
  exact mpullback_back_left_eq_mpullback_back_right_iff α.1

/-- A form on the objects of `G ⋉ X` is invariant exactly when every element of `G` preserves the
corresponding form on `X`. -/
theorem mem_invariantForms_iff_forall_mpullback_smul
    {φ : SmoothForm I (ActionCategory G X) F k} :
    φ ∈ invariantForms I G X F k ↔
      ∀ g : G, SmoothForm.mpullback (g • ·) (contMDiff_const_smul g)
          (SmoothForm.mpullback (objectDiffeomorph I ∞ G X).symm
            (objectDiffeomorph I ∞ G X).symm.contMDiff φ) =
        SmoothForm.mpullback (objectDiffeomorph I ∞ G X).symm
          (objectDiffeomorph I ∞ G X).symm.contMDiff φ := by
  rw [← mpullback_objectDiffeomorph_mem_invariantForms_iff,
    SmoothForm.mpullback_mpullback_symm]

/-- The exterior derivative of an invariant form is invariant. -/
theorem mextDerivₗ_mem_invariantForms {φ : SmoothForm I (ActionCategory G X) F k}
    (hφ : φ ∈ invariantForms I G X F k) :
    mextDerivₗ I k φ ∈ invariantForms I G X F (k + 1) := by
  rw [mem_invariantForms_iff] at hφ ⊢
  rw [← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback, hφ]

/-- The wedge product of invariant forms, for any continuous pairing of their coefficients, is
invariant. -/
theorem wedgeWith_mem_invariantForms {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℝ F₃] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {l : ℕ}
    {φ : SmoothForm I (ActionCategory G X) F₁ k} {ψ : SmoothForm I (ActionCategory G X) F₂ l}
    (hφ : φ ∈ invariantForms I G X F₁ k) (hψ : ψ ∈ invariantForms I G X F₂ l) :
    SmoothForm.wedgeWith μ φ ψ ∈ invariantForms I G X F₃ (k + l) := by
  rw [mem_invariantForms_iff] at hφ hψ ⊢
  rw [SmoothForm.mpullback_wedgeWith, SmoothForm.mpullback_wedgeWith, hφ, hψ]

/-- The wedge product of invariant real-valued forms is invariant. -/
theorem wedge_mem_invariantForms {l : ℕ} {φ : SmoothForm I (ActionCategory G X) ℝ k}
    {ψ : SmoothForm I (ActionCategory G X) ℝ l} (hφ : φ ∈ invariantForms I G X ℝ k)
    (hψ : ψ ∈ invariantForms I G X ℝ l) :
    SmoothForm.wedge φ ψ ∈ invariantForms I G X ℝ (k + l) := by
  rw [SmoothForm.wedge_def]
  exact wedgeWith_mem_invariantForms _ hφ hψ

/-- The pullback of an invariant form along the functor induced by a smooth equivariant map is
invariant. -/
theorem mpullback_map_obj_mem_invariantForms {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {G' Y : Type*}
    [Monoid G'] [TopologicalSpace G'] [DiscreteTopology G'] [MulAction G' Y] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [ContMDiffConstSMul I' ∞ G' Y] (φ : G →* G')
    (f : X →ₑ[φ] Y) (hf : ContMDiff I I' ∞ f) {ψ : SmoothForm I' (ActionCategory G' Y) F k}
    (hψ : ψ ∈ invariantForms I' G' Y F k) :
    SmoothForm.mpullback (map φ f).obj (contMDiff_map_obj I ∞ φ f hf) ψ ∈
      invariantForms I G X F k := by
  rw [mem_invariantForms_iff] at hψ ⊢
  have hmap := contMDiff_map_total I ∞ φ f hf
  -- The functor commutes with the source and target maps, by the definition of its arrow map.
  calc _ = SmoothForm.mpullback _ hmap (SmoothForm.mpullback Quiver.Total.left
          (isLocalDiffeomorph_source I' ∞ G' Y).contMDiff ψ) := by
        rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp, ← LinearMap.comp_apply,
          ← SmoothForm.mpullback_comp]
        rfl
    _ = SmoothForm.mpullback _ hmap (SmoothForm.mpullback Quiver.Total.right
          (contMDiff_target I' ∞ G' Y) ψ) := by rw [hψ]
    _ = _ := by
        rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp, ← LinearMap.comp_apply,
          ← SmoothForm.mpullback_comp]
        rfl

end Monoid

section Quotient

variable [Group G] [TopologicalSpace G] [DiscreteTopology G] [MulAction G X]
  [ContMDiffConstSMul I ∞ G X] [IsManifold I ∞ X] [ProperlyDiscontinuousSMul G X]
  [ContinuousConstSMul G X] [IsCancelSMul G X] [T2Space X] [LocallyCompactSpace X]

variable {I G X F k}

/-- The pullback of a form on the orbit manifold to the objects of `G ⋉ X` is invariant. -/
theorem mpullback_quotientMk_mem_invariantForms
    (β : SmoothForm I (MulAction.orbitRel.Quotient G X) F k) :
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G X) ∘ objectDiffeomorph I ∞ G X)
      (isLocalDiffeomorph_quotientMk.contMDiff.comp (objectDiffeomorph I ∞ G X).contMDiff) β ∈
        invariantForms I G X F k := by
  rw [SmoothForm.mpullback_comp _ _ (objectDiffeomorph I ∞ G X).contMDiff
    isLocalDiffeomorph_quotientMk.contMDiff, LinearMap.comp_apply,
    mpullback_objectDiffeomorph_mem_invariantForms_iff]
  intro g
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  congr 2
  exact funext fun x ↦ Quotient.sound (MulAction.mem_orbit x g)

variable (I G X F k) in
/-- For a free, properly discontinuous action, the invariant forms on the objects of `G ⋉ X` are
the forms on the orbit manifold `X / G`: a form on `X / G` corresponds to its pullback along the
orbit map, and an invariant form to its descent. -/
def invariantFormsEquivQuotient :
    invariantForms I G X F k ≃ₗ[ℝ] SmoothForm I (MulAction.orbitRel.Quotient G X) F k :=
  LinearEquiv.symm
    { (SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G X) ∘ objectDiffeomorph I ∞ G X)
        (isLocalDiffeomorph_quotientMk.contMDiff.comp
          (objectDiffeomorph I ∞ G X).contMDiff)).codRestrict
        (invariantForms I G X F k) mpullback_quotientMk_mem_invariantForms with
      invFun φ := SmoothForm.descend _ (mem_invariantForms_iff_forall_mpullback_smul.1 φ.2)
      left_inv β := by
        symm
        rw [SmoothForm.eq_descend_iff]
        simp only [LinearMap.toFun_eq_coe, LinearMap.codRestrict_apply]
        rw [SmoothForm.mpullback_comp _ _ (objectDiffeomorph I ∞ G X).contMDiff
          isLocalDiffeomorph_quotientMk.contMDiff, LinearMap.comp_apply,
          SmoothForm.mpullback_symm_eq_of_mpullback_eq rfl]
      right_inv φ := by
        apply Subtype.ext
        simp only [LinearMap.toFun_eq_coe, LinearMap.codRestrict_apply]
        rw [SmoothForm.mpullback_comp _ _ (objectDiffeomorph I ∞ G X).contMDiff
          isLocalDiffeomorph_quotientMk.contMDiff, LinearMap.comp_apply,
          SmoothForm.mpullback_quotientMk_descend, SmoothForm.mpullback_mpullback_symm] }

/-- The invariant form corresponding to a form on the orbit manifold is its pullback along the
orbit map. -/
@[simp]
theorem coe_invariantFormsEquivQuotient_symm
    (β : SmoothForm I (MulAction.orbitRel.Quotient G X) F k) :
    ((invariantFormsEquivQuotient I G X F k).symm β : SmoothForm I (ActionCategory G X) F k) =
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G X) ∘ objectDiffeomorph I ∞ G X)
        (isLocalDiffeomorph_quotientMk.contMDiff.comp (objectDiffeomorph I ∞ G X).contMDiff) β :=
  (rfl)

/-- An invariant form is the pullback along the orbit map of the corresponding form on the orbit
manifold. -/
@[simp]
theorem mpullback_invariantFormsEquivQuotient (φ : invariantForms I G X F k) :
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G X) ∘ objectDiffeomorph I ∞ G X)
        (isLocalDiffeomorph_quotientMk.contMDiff.comp (objectDiffeomorph I ∞ G X).contMDiff)
        (invariantFormsEquivQuotient I G X F k φ) = φ := by
  rw [← coe_invariantFormsEquivQuotient_symm, LinearEquiv.symm_apply_apply]

/-- The identification of invariant forms with forms on the orbit manifold commutes with the
exterior derivative. -/
theorem invariantFormsEquivQuotient_mextDerivₗ (φ : invariantForms I G X F k) :
    invariantFormsEquivQuotient I G X F (k + 1)
        ⟨mextDerivₗ I k φ, mextDerivₗ_mem_invariantForms φ.2⟩ =
      mextDerivₗ I k (invariantFormsEquivQuotient I G X F k φ) := by
  rw [← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [coe_invariantFormsEquivQuotient_symm, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_invariantFormsEquivQuotient]

end Quotient

end TauCeti.ActionGroupoid
