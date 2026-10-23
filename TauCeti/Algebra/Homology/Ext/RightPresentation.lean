/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.CategoryTheory.Linear.HomCokernel.Exact

/-!
# Ext¹ from a right exact projective presentation

Let `0 → K → P → M → 0` be short exact, with `P` projective, and let
`e : X → K` be an epimorphism. Then `X → P → M → 0` is a right exact
presentation with projective middle term. Its Hom cokernel need not be Ext¹: a representative
must also vanish on `ker e`. `extEquivKerHomCokernelRestrict` identifies Ext¹
with the kernel of this restriction on the Hom cokernel.

The comparison is natural in the coefficient object and computes on pushout
extension classes. Neither projectivity of `X` nor injectivity of `X → P`
is required. This cocycle condition is needed when using a minimal projective
presentation to calculate Auslander–Reiten duality.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.

For a short exact presentation, `homCokernelEquivExt` identifies the whole Hom
cokernel with Ext¹. For a right exact presentation, `HomCokernel.equivKerRestrict`
identifies the Hom cokernel on the syzygy with the classes satisfying the cocycle condition.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v w t

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact)
  [Projective S.X₂] {X : C} (e : X ⟶ S.X₁) [Epi e] (Y : C)

/-- Ext¹ from a right exact projective presentation is the kernel of restriction
of its Hom cokernel to the kernel of the relation epimorphism. -/
noncomputable def extEquivKerHomCokernelRestrict :
    Ext.{w} S.X₃ Y 1 ≃ₗ[R]
      LinearMap.ker (HomCokernel.restrict R (e ≫ S.f) (kernel.ι e)
        (Y := Y) (by simp [← Category.assoc])) :=
  (homCokernelEquivExt R hS Y).symm.trans
    (HomCokernel.equivKerRestrict R
      (S := ShortComplex.mk (kernel.ι e) e (kernel.condition e))
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel e)) S.f)

/-- The kernel comparison first represents an extension on the syzygy and then
precomposes with the relation epimorphism. -/
@[simp]
theorem extEquivKerHomCokernelRestrict_apply (x : Ext.{w} S.X₃ Y 1) :
    (extEquivKerHomCokernelRestrict R hS e Y x).val =
      HomCokernel.precomp R S.f e ((homCokernelEquivExt R hS Y).symm x) := by
  rw [extEquivKerHomCokernelRestrict, LinearEquiv.trans_apply,
    HomCokernel.equivKerRestrict_apply]

/-- The inverse comparison sends a cocycle descending to `f` to its pushout extension. -/
@[simp]
theorem extEquivKerHomCokernelRestrict_symm_mk (f : S.X₁ ⟶ Y)
    (hf : HomCokernel.restrict R (e ≫ S.f) (kernel.ι e)
      (by simp [← Category.assoc]) (Submodule.Quotient.mk (e ≫ f)) = 0) :
    (extEquivKerHomCokernelRestrict R hS e Y).symm
        ⟨Submodule.Quotient.mk (e ≫ f), hf⟩ =
      hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
  apply (extEquivKerHomCokernelRestrict R hS e Y).injective
  apply Subtype.ext
  simp

variable {Y}

/-- The Ext¹ kernel comparison commutes with postcomposition in the coefficient object. -/
theorem extEquivKerHomCokernelRestrict_naturality {Z : C} (g : Y ⟶ Z)
    (x : Ext.{w} S.X₃ Y 1) :
    (extEquivKerHomCokernelRestrict R hS e Z (x.comp (Ext.mk₀ g) (add_zero 1))).val =
      HomCokernel.map R (e ≫ S.f) g (extEquivKerHomCokernelRestrict R hS e Y x).val := by
  obtain ⟨y, rfl⟩ := (homCokernelEquivExt R hS Y).surjective x
  rw [← homCokernelEquivExt_naturality R hS g y]
  simp only [extEquivKerHomCokernelRestrict_apply, LinearEquiv.symm_apply_apply,
    HomCokernel.precomp_map]

end TauCeti
