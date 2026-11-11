/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid
public import TauCeti.Geometry.Manifold.Category.InvariantForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Quotient

/-!
# Invariant differential forms on an action groupoid

Let a discrete monoid `G` act on a smooth manifold `X` by smooth maps, and let `G ⋉ X` be the
action category, with its smooth object and arrow manifolds; it is the action groupoid when `G` is
a group. A smooth form `φ` on the objects is *invariant* if its pullbacks along the source and the
target to the arrow manifold agree, `s^* φ = t^* φ`. These forms make up the submodule
`TauCeti.Quiver.invariantForms`. When `G ⋉ X` is a proper étale groupoid presenting an
orbifold, for instance for a proper action of a discrete group, these are the differential forms of
that orbifold.

Every label is a separate open slice of arrows, on which the target is the translate of the
source by that label. So a form is invariant exactly when the corresponding form on `X` is
preserved by every element of `G`
(`TauCeti.ActionGroupoid.mpullback_objectDiffeomorph_mem_invariantForms_iff`). Elements acting
trivially on `X` are arrows of `G ⋉ X` as well, but they impose no condition on forms.

Invariant forms are closed under the exterior derivative and under wedge products, and they pull
back to invariant forms along the functor induced by a smooth equivariant map. When the action is a
free, properly discontinuous group action, the invariant forms are exactly the forms on the orbit
manifold `X / G`: `TauCeti.ActionGroupoid.invariantFormsEquivQuotient` identifies a form on `X / G`
with its pullback along the orbit map, compatibly with the exterior derivative and wedge products.

## Main definitions

The equalizer, exterior derivative, wedge closure and smooth-prefunctor pullbacks are provided
by `TauCeti.Geometry.Manifold.Category.InvariantForm` and specialize to the source and target of
`G ⋉ X` without a separate action-specific interface.

* `TauCeti.ActionGroupoid.invariantFormsEquivQuotient`: for a free, properly discontinuous action,
  the invariant forms are the forms on the orbit manifold.

## Main results

* `TauCeti.ActionGroupoid.mpullback_objectDiffeomorph_mem_invariantForms_iff`,
  `TauCeti.ActionGroupoid.mem_invariantForms_iff_forall_mpullback_smul`: a form is invariant
  exactly when every element of `G` preserves the corresponding form on `X`.
* `TauCeti.ActionGroupoid.invariantFormsEquivQuotient_mextDerivₗ`,
  `TauCeti.ActionGroupoid.invariantFormsEquivQuotient_wedgeWith`: the identification with forms on
  the orbit manifold commutes with the exterior derivative and with wedge products.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 2, for differential forms on an
  orbifold as the forms on the objects of a presenting groupoid with `s^* φ = t^* φ`.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1, for
  action groupoids.
-/

public noncomputable section

open CategoryTheory Topology
open CategoryTheory.ActionCategory TauCeti.Quiver
open scoped Manifold ContDiff

namespace TauCeti.ActionGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (G X : Type*) [TopologicalSpace X] [ChartedSpace H X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)

section Monoid

variable [Monoid G] [TopologicalSpace G] [DiscreteTopology G] [MulAction G X]

variable {I G X F k}

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
      (a.hom.hom • ·) ∘ fun b ↦ b.left.back :=
    eventually_back_right_eq_smul a
  rw [hev.mpullback_eq, mpullback_comp_at
    ((isLocalDiffeomorph_back_left I ∞ G X).contMDiff.mdifferentiableAt (by simp))
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
      rw [totalEquiv_symm_apply_left]
      exact coe_back x
    have := congrFun h a
    rw [mpullback_back_right_apply, ha] at this
    rw [← hx]
    exact ((mpullback_apply_eq_mpullback_apply_iff
      ((isLocalDiffeomorph_back_left I ∞ G X).isInvertible_mfderiv (by simp) a).surjective).1
        this).symm
  · rw [mpullback_back_right_apply, h]

variable [IsManifold I ∞ X]

/-- A form on `X`, transported to the objects of `G ⋉ X`, is invariant exactly when every element
of `G` preserves it. -/
theorem mpullback_objectDiffeomorph_mem_invariantForms_iff {α : SmoothForm I X F k} :
    SmoothForm.mpullback (objectDiffeomorph I ∞ G X) (objectDiffeomorph I ∞ G X).contMDiff α ∈
        invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
          (contMDiff_target I ∞ G X) F k ↔
      ∀ g : G, SmoothForm.mpullback (g • ·) (contMDiff_const_smul g) α = α := by
  rw [mem_invariantForms_iff, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
    Subtype.ext_iff]
  simp only [SmoothForm.coe_mpullback, Subtype.ext_iff, Function.comp_def,
    objectDiffeomorph_apply]
  exact mpullback_back_left_eq_mpullback_back_right_iff α.1

/-- A form on the objects of `G ⋉ X` is invariant exactly when every element of `G` preserves the
corresponding form on `X`. -/
theorem mem_invariantForms_iff_forall_mpullback_smul
    {φ : SmoothForm I (ActionCategory G X) F k} :
    φ ∈ invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
        (contMDiff_target I ∞ G X) F k ↔
      ∀ g : G, SmoothForm.mpullback (g • ·) (contMDiff_const_smul g)
          (SmoothForm.mpullback (objectDiffeomorph I ∞ G X).symm
            (objectDiffeomorph I ∞ G X).symm.contMDiff φ) =
        SmoothForm.mpullback (objectDiffeomorph I ∞ G X).symm
          (objectDiffeomorph I ∞ G X).symm.contMDiff φ := by
  rw [← mpullback_objectDiffeomorph_mem_invariantForms_iff,
    SmoothForm.mpullback_mpullback_symm]

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
        invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
          (contMDiff_target I ∞ G X) F k := by
  rw [← SmoothForm.mpullback_mpullback _ _ (objectDiffeomorph I ∞ G X).contMDiff
      isLocalDiffeomorph_quotientMk.contMDiff,
    mpullback_objectDiffeomorph_mem_invariantForms_iff]
  intro g
  rw [SmoothForm.mpullback_mpullback]
  congr 2
  exact funext fun x ↦ Quotient.sound (MulAction.mem_orbit x g)

variable (I G X F k) in
/-- For a free, properly discontinuous action, the invariant forms on the objects of `G ⋉ X` are
the forms on the orbit manifold `X / G`: a form on `X / G` corresponds to its pullback along the
orbit map, and an invariant form to its descent. -/
def invariantFormsEquivQuotient :
    invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
        (contMDiff_target I ∞ G X) F k ≃ₗ[ℝ] SmoothForm I (MulAction.orbitRel.Quotient G X) F k :=
  LinearEquiv.symm
    { (SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G X) ∘ objectDiffeomorph I ∞ G X)
        (isLocalDiffeomorph_quotientMk.contMDiff.comp
          (objectDiffeomorph I ∞ G X).contMDiff)).codRestrict
        (invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
          (contMDiff_target I ∞ G X) F k) mpullback_quotientMk_mem_invariantForms with
      invFun φ := SmoothForm.descend _ (mem_invariantForms_iff_forall_mpullback_smul.1 φ.2)
      left_inv β := by
        symm
        rw [SmoothForm.eq_descend_iff]
        simp only [LinearMap.toFun_eq_coe, LinearMap.codRestrict_apply]
        rw [← SmoothForm.mpullback_mpullback _ _ (objectDiffeomorph I ∞ G X).contMDiff
            isLocalDiffeomorph_quotientMk.contMDiff,
          SmoothForm.mpullback_symm_mpullback]
      right_inv φ := by
        apply Subtype.ext
        simp only [LinearMap.toFun_eq_coe, LinearMap.codRestrict_apply]
        rw [← SmoothForm.mpullback_mpullback _ _ (objectDiffeomorph I ∞ G X).contMDiff
            isLocalDiffeomorph_quotientMk.contMDiff,
          SmoothForm.mpullback_quotientMk_descend,
          SmoothForm.mpullback_mpullback_symm] }

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
theorem mpullback_invariantFormsEquivQuotient
    (φ : invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
      (contMDiff_target I ∞ G X) F k) :
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G X) ∘ objectDiffeomorph I ∞ G X)
        (isLocalDiffeomorph_quotientMk.contMDiff.comp (objectDiffeomorph I ∞ G X).contMDiff)
        (invariantFormsEquivQuotient I G X F k φ) = φ := by
  rw [← coe_invariantFormsEquivQuotient_symm, LinearEquiv.symm_apply_apply]

/-- The identification of invariant forms with forms on the orbit manifold commutes with the
exterior derivative. -/
theorem invariantFormsEquivQuotient_mextDerivₗ
    (φ : invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
      (contMDiff_target I ∞ G X) F k) :
    invariantFormsEquivQuotient I G X F (k + 1)
        (invariantForms.mextDerivₗ I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
          (contMDiff_target I ∞ G X) F k φ) =
      mextDerivₗ I k (invariantFormsEquivQuotient I G X F k φ) := by
  rw [← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [coe_invariantFormsEquivQuotient_symm, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_invariantFormsEquivQuotient, invariantForms.coe_mextDerivₗ]

/-- The identification of invariant forms with forms on the orbit manifold commutes with the wedge
product, for any continuous pairing of coefficients. -/
theorem invariantFormsEquivQuotient_wedgeWith {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℝ F₃] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {l : ℕ}
    (φ : invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
      (contMDiff_target I ∞ G X) F₁ k)
    (ψ : invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
      (contMDiff_target I ∞ G X) F₂ l) :
    invariantFormsEquivQuotient I G X F₃ (k + l)
        ⟨SmoothForm.wedgeWith μ φ ψ, wedgeWith_mem_invariantForms μ φ.2 ψ.2⟩ =
      SmoothForm.wedgeWith μ (invariantFormsEquivQuotient I G X F₁ k φ)
        (invariantFormsEquivQuotient I G X F₂ l ψ) := by
  rw [← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [coe_invariantFormsEquivQuotient_symm, SmoothForm.mpullback_wedgeWith,
    mpullback_invariantFormsEquivQuotient, mpullback_invariantFormsEquivQuotient]

/-- The identification of invariant real-valued forms with forms on the orbit manifold commutes
with the wedge product. -/
theorem invariantFormsEquivQuotient_wedge {l : ℕ}
    (φ : invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
      (contMDiff_target I ∞ G X) ℝ k)
    (ψ : invariantForms I I (isLocalDiffeomorph_source I ∞ G X).contMDiff
      (contMDiff_target I ∞ G X) ℝ l) :
    invariantFormsEquivQuotient I G X ℝ (k + l)
        ⟨SmoothForm.wedge φ ψ, wedge_mem_invariantForms φ.2 ψ.2⟩ =
      SmoothForm.wedge (invariantFormsEquivQuotient I G X ℝ k φ)
        (invariantFormsEquivQuotient I G X ℝ l ψ) := by
  simp only [SmoothForm.wedge_def]
  exact invariantFormsEquivQuotient_wedgeWith _ φ ψ

end Quotient

end TauCeti.ActionGroupoid
