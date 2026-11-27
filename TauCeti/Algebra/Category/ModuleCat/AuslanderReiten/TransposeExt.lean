/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction
public import TauCeti.Algebra.Category.ModuleCat.End
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.HomCokernel

/-!
# The right transpose of a projective resolution of length one

For a right module `N` presented by `0 → P₁ → P₀ → N → 0`, the right transpose is naturally
`Ext¹(N, A)` in the category of right modules. The comparison sends a functional on `P₁` to
the pushout of the resolution along that functional. The left action of `A` on the transpose
corresponds to pushforward along left multiplication on the right regular module.

The comparison combines `ModuleCat.covariantDefectEquivHomQuotient` with
`TauCeti.homCokernelEquivExt` and commutes with morphisms of presentations.

This computes the transpose in the description of the inverse Auslander–Reiten translate over
hereditary algebras in Grant, *The Nakayama automorphism of a self-injective preprojective
algebra*, https://arxiv.org/abs/1906.11817, Section 2.3 and Proposition 2.5.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace TauCeti.FiniteProjectivePresentation

universe u v w

variable {A : Type u} [Ring A] {N : ModuleCat.{max u v} Aᵐᵒᵖ}
variable (Q : FiniteProjectivePresentation N)

variable (k : Type w) [CommRing k] [Algebra k A]

private instance : Projective Q.shortComplex.X₂ :=
  inferInstanceAs (Projective Q.P₀)

/-- For a length-one projective resolution of a right module, the right transpose computes
`Ext¹(N, A)`. The left action is described by `rightTransposeEquivExt_smul`. -/
noncomputable def rightTransposeEquivExt (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[k] Ext N (ModuleCat.of Aᵐᵒᵖ (ULift.{v} A)) 1 :=
  (Q.rightTransposeHomCokernelEquiv k).trans
    (homCokernelEquivExt k (Q.shortExact_shortComplex hp) (ModuleCat.of Aᵐᵒᵖ (ULift.{v} A)))

/-- A functional represents the pushout of the short exact presentation along that functional. -/
@[simp↓]
theorem rightTransposeEquivExt_mk (hp : Function.Injective Q.p) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExt k hp (Submodule.Quotient.mk g) =
      (Q.shortExact_shortComplex hp).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g))) (add_zero 1) := by
  rw [rightTransposeEquivExt, LinearEquiv.trans_apply, rightTransposeHomCokernelEquiv_mk,
    homCokernelEquivExt_mk]

/-- Multiplication on the transpose corresponds to pushforward along left multiplication of the
right regular coefficient module. -/
theorem rightTransposeEquivExt_smul (hp : Function.Injective Q.p) (a : A)
    (x : Q.rightTranspose) :
    Q.rightTransposeEquivExt k hp (a • x) = (Q.rightTransposeEquivExt k hp x).comp
      (Ext.mk₀ (rightRegularEnd.{u, v} a).asHom) (add_zero 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, rightTransposeEquivExt_mk, rightTransposeEquivExt_mk]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2
  ext x
  simp [rightRegularEnd_asHom]

/-- The projective right-transpose comparison is linear over `A` when Ext carries the
left action induced by the right regular coefficient module. -/
noncomputable def rightTransposeLinearEquivExt (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[A] Abelian.ExtWithAction (rightRegularEnd.{u, v} (A := A)) N 1 where
  toFun x := (Abelian.ExtWithAction.toExt rightRegularEnd.{u, v}).symm
    (Q.rightTransposeEquivExt ℤ hp x)
  invFun x := (Q.rightTransposeEquivExt ℤ hp).symm
    (Abelian.ExtWithAction.toExt rightRegularEnd.{u, v} x)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' a x := by
    apply (Abelian.ExtWithAction.toExt rightRegularEnd.{u, v}).injective
    simpa only [AddEquiv.apply_symm_apply, Abelian.ExtWithAction.toExt_smul,
      RingHom.id_apply] using
      Q.rightTransposeEquivExt_smul ℤ hp a x

/-- Forgetting the left action recovers the integral linear Ext comparison. -/
@[simp↓]
theorem rightTransposeLinearEquivExt_toExt (hp : Function.Injective Q.p)
    (x : Q.rightTranspose) :
    Abelian.ExtWithAction.toExt rightRegularEnd.{u, v}
      (Q.rightTransposeLinearEquivExt hp x) = Q.rightTransposeEquivExt ℤ hp x := by
  simp [rightTransposeLinearEquivExt]

/-- The `A`-linear comparison sends a functional to the corresponding pushout class. -/
theorem rightTransposeLinearEquivExt_mk (hp : Function.Injective Q.p)
    (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Abelian.ExtWithAction.toExt rightRegularEnd.{u, v}
      (Q.rightTransposeLinearEquivExt hp (Submodule.Quotient.mk g)) =
      (Q.shortExact_shortComplex hp).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g))) (add_zero 1) := by
  rw [rightTransposeLinearEquivExt_toExt, rightTransposeEquivExt_mk]

/-- Naturality of the projective Ext comparison under a morphism of presentations. -/
theorem rightTransposeEquivExt_naturality {N' : ModuleCat.{max u v} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex) (x : P.rightTranspose) :
    Q.rightTransposeEquivExt k hQ (Q.rightTransposeMap P φ x) =
      (Ext.mk₀ φ.τ₃).comp (P.rightTransposeEquivExt k hP x) (zero_add 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := (Q.shortExact_shortComplex hQ).extClass_naturality (P.shortExact_shortComplex hP) φ
  have hg : ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ φ.τ₁.hom) =
      φ.τ₁ ≫ ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g) := by
    ext x
    rfl
  rw [rightTransposeMap_mk, rightTransposeEquivExt_mk, rightTransposeEquivExt_mk]
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hg] using
    congrArg (fun α ↦ α.comp
      (Ext.mk₀ (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g))) (add_zero 1)) h

end TauCeti.FiniteProjectivePresentation
