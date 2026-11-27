/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Defect
import TauCeti.LinearAlgebra.LinearMap.RestrictScalars

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

universe u w

variable {A : Type u} [Ring A] {N : ModuleCat.{u} Aᵐᵒᵖ}
variable (Q : FiniteProjectivePresentation N)

variable (k : Type w) [CommRing k] [Algebra k A]

/-- The right transpose as the cokernel of precomposition on bundled morphisms into
the right regular module. -/
noncomputable def rightTransposeHomCokernelEquiv :
    Q.rightTranspose ≃ₗ[k] HomCokernel k Q.shortComplex.f (ModuleCat.of Aᵐᵒᵖ A) :=
  ((Q.p.lcomp A A).cokerRestrictScalarsEquiv k).symm.trans
    (ModuleCat.covariantDefectEquivHomQuotient k (B := ModuleCat.of Aᵐᵒᵖ A)
      (LinearEquiv.refl Aᵐᵒᵖ A) Q.shortComplex.f)

/-- The Hom cokernel comparison bundles the functional representing a transpose class. -/
@[simp]
theorem rightTransposeHomCokernelEquiv_mk (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    let _ := Linear.homModule (R := k) Q.P₀ (ModuleCat.of Aᵐᵒᵖ A)
    let _ := Linear.homModule (R := k) Q.P₁ (ModuleCat.of Aᵐᵒᵖ A)
    Q.rightTransposeHomCokernelEquiv k (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (ModuleCat.ofHom g) := by
  let e := ModuleCat.covariantDefectEquivHomQuotient k (B := ModuleCat.of Aᵐᵒᵖ A)
    (LinearEquiv.refl Aᵐᵒᵖ A) Q.shortComplex.f
  have h := LinearMap.cokerRestrictScalarsEquiv_symm_mk k (Q.p.lcomp A A) g
  -- The restricted-scalar cokernel of precomposition is the covariant defect.
  have h' := ModuleCat.covariantDefectEquivHomQuotient_mk k (B := ModuleCat.of Aᵐᵒᵖ A)
    (LinearEquiv.refl Aᵐᵒᵖ A) Q.shortComplex.f g
  exact (congrArg (fun x ↦ e x) h).trans (h'.trans (by simp))

private instance : Projective Q.shortComplex.X₂ :=
  inferInstanceAs (Projective Q.P₀)

/-- For a length-one projective resolution of a right module, the right transpose computes
`Ext¹(N, A)`. The left action is described by `rightTransposeEquivExt_smul`. -/
noncomputable def rightTransposeEquivExt (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[k] Ext N (ModuleCat.of Aᵐᵒᵖ A) 1 :=
  (Q.rightTransposeHomCokernelEquiv k).trans
    (homCokernelEquivExt k (Q.shortExact_shortComplex hp) (ModuleCat.of Aᵐᵒᵖ A))

/-- A functional represents the pushout of the short exact presentation along that functional. -/
@[simp]
theorem rightTransposeEquivExt_mk (hp : Function.Injective Q.p) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExt k hp (Submodule.Quotient.mk g) =
      (Q.shortExact_shortComplex hp).extClass.comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1) := by
  rw [rightTransposeEquivExt, LinearEquiv.trans_apply, rightTransposeHomCokernelEquiv_mk,
    homCokernelEquivExt_mk]

/-- Multiplication on the transpose corresponds to pushforward along left multiplication of the
right regular coefficient module. -/
theorem rightTransposeEquivExt_smul (hp : Function.Injective Q.p) (a : A)
    (x : Q.rightTranspose) :
    Q.rightTransposeEquivExt k hp (a • x) = (Q.rightTransposeEquivExt k hp x).comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a))) (add_zero 1) := by
  rw [rightTransposeEquivExt, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    ← homCokernelEquivExt_naturality]
  congr 1
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, rightTransposeHomCokernelEquiv_mk,
    rightTransposeHomCokernelEquiv_mk, HomCokernel.map_mk,
    LinearMap.smul_eq_mulLeft_comp, ModuleCat.ofHom_comp]

/-- Naturality of the projective Ext comparison under a morphism of presentations. -/
theorem rightTransposeEquivExt_comp {N' : ModuleCat.{u} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex) (x : P.rightTranspose) :
    Q.rightTransposeEquivExt k hQ (Q.rightTransposeMap P φ x) =
      (Ext.mk₀ φ.τ₃).comp (P.rightTransposeEquivExt k hP x) (zero_add 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := (Q.shortExact_shortComplex hQ).extClass_naturality (P.shortExact_shortComplex hP) φ
  rw [rightTransposeMap_mk, rightTransposeEquivExt_mk, rightTransposeEquivExt_mk,
    ModuleCat.ofHom_comp, ModuleCat.ofHom_hom]
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] using
    congrArg (fun α ↦ α.comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1)) h

end TauCeti.FiniteProjectivePresentation
