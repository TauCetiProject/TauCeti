/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.HomCokernel.Basic
public import TauCeti.Algebra.Homology.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Computing Ext¹ from a projective presentation

For a short exact sequence `S : 0 → P₁ → P₀ → M → 0` with `P₀` projective,
`homCokernelEquivExt` identifies the explicit quotient
`Hom(P₁, Y) / im(Hom(P₀, Y))` with `Ext¹(M, Y)`. The quotient is defined
independently of derived categories in `TauCeti.CategoryTheory.Linear.HomCokernel.Basic`.
The comparison is natural in `Y` and identifies the quotients obtained from any
two projective presentations of `M`. No projectivity of `P₁` is needed to compute
degree one.

Mathlib's extension class defines the connecting morphism in the contravariant
long exact Ext sequence. For a projective middle term, this morphism is surjective
with kernel the maps extending to that term, giving the quotient identification.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe u v w t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S T : ShortComplex C}

section Ring

variable (R : Type t) [Ring R] [Linear R C] (hS : S.ShortExact) (Y : C)

/-- The connecting map `Hom(S.X₁, Y) → Ext¹(S.X₃, Y)` of a short exact sequence. -/
noncomputable def homBoundary : (S.X₁ ⟶ Y) →ₗ[R] Ext.{w} S.X₃ Y 1 where
  toFun f := hS.extClass.comp (Ext.mk₀ f) (add_zero 1)
  map_add' := by simp [Ext.mk₀_add]
  map_smul' := by simp [Ext.mk₀_smul]

/-- The Hom connecting map pushes the extension class forward along its argument. -/
@[simp]
theorem homBoundary_apply (f : S.X₁ ⟶ Y) :
    homBoundary R hS Y f = hS.extClass.comp (Ext.mk₀ f) (add_zero 1) :=
  (rfl)

/-- The kernel of the connecting map consists exactly of maps extending to `S.X₂`. -/
theorem ker_homBoundary :
    (homBoundary R hS Y).ker = (Linear.leftComp R Y S.f).range := by
  ext f
  simp only [LinearMap.mem_ker, homBoundary_apply, LinearMap.mem_range,
    Linear.leftComp_apply]
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ f) rfl hf
    refine ⟨Ext.linearEquiv₀ (R := R) g, ?_⟩
    apply (Ext.mk₀_bijective _ _).1
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_linearEquiv₀_apply]
    exact hg
  · rintro ⟨g, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ g)

/-- If the middle term is projective, every extension class is a Hom boundary. -/
theorem homBoundary_surjective [Projective S.X₂] :
    Function.Surjective (homBoundary R hS Y) := by
  intro e
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₃ hS Y e (n₀ := 0)
    (Ext.eq_zero_of_projective _) rfl
  exact ⟨Ext.linearEquiv₀ (R := R) f, by simpa using hf⟩

/-- The Hom cokernel of a projective presentation computes `Ext¹` as an `R`-module. -/
noncomputable def homCokernelEquivExt [Projective S.X₂] :
    HomCokernel R S.f Y ≃ₗ[R] Ext.{w} S.X₃ Y 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_homBoundary R hS Y).symm).trans
    ((homBoundary R hS Y).quotKerEquivOfSurjective (homBoundary_surjective R hS Y))

/-- The comparison sends the class of a map to the corresponding pushout extension class. -/
@[simp]
theorem homCokernelEquivExt_mk [Projective S.X₂] (f : S.X₁ ⟶ Y) :
    homCokernelEquivExt R hS Y (Submodule.Quotient.mk f) =
      hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
  simp [homCokernelEquivExt]

/-- Under the inverse comparison, a pushout extension is represented by its defining map. -/
@[simp]
theorem homCokernelEquivExt_symm_comp_mk₀ [Projective S.X₂] (f : S.X₁ ⟶ Y) :
    (homCokernelEquivExt R hS Y).symm
        (hS.extClass.comp (Ext.mk₀ f) (add_zero 1)) = Submodule.Quotient.mk f := by
  rw [← homCokernelEquivExt_mk R hS Y, LinearEquiv.symm_apply_apply]

variable {Y}

/-- The Hom-cokernel computation of `Ext¹` is natural in the target object. -/
@[simp]
theorem homCokernelEquivExt_naturality [Projective S.X₂] {Z : C} (g : Y ⟶ Z)
    (x : HomCokernel R S.f Y) :
    homCokernelEquivExt R hS Z (HomCokernel.map R S.f g x) =
      (homCokernelEquivExt R hS Y x).comp (Ext.mk₀ g) (add_zero 1) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => simp

variable (Y)

/-- Projective presentations of isomorphic objects give canonically equivalent Hom cokernels.
The comparison identifies the extension classes represented in the two presentations. -/
noncomputable def homCokernelEquiv (hT : T.ShortExact) [Projective S.X₂] [Projective T.X₂]
    (e : S.X₃ ≅ T.X₃) : HomCokernel R S.f Y ≃ₗ[R] HomCokernel R T.f Y :=
  (homCokernelEquivExt R hS Y).trans <|
    (extLinearEquivOfIso R e (Iso.refl Y) 1).trans (homCokernelEquivExt R hT Y).symm

/-- Comparing presentations preserves their extension classes, after transport along `e`. -/
@[simp]
theorem homCokernelEquivExt_homCokernelEquiv (hT : T.ShortExact)
    [Projective S.X₂] [Projective T.X₂] (e : S.X₃ ≅ T.X₃) (x : HomCokernel R S.f Y) :
    homCokernelEquivExt R hT Y (homCokernelEquiv R hS Y hT e x) =
      (Ext.mk₀ e.inv).comp (homCokernelEquivExt R hS Y x) (zero_add 1) := by
  simp [homCokernelEquiv]

variable {Y} in
/-- Presentation comparisons are natural in the target object. -/
@[simp]
theorem homCokernelEquiv_naturality (hT : T.ShortExact) [Projective S.X₂] [Projective T.X₂]
    (e : S.X₃ ≅ T.X₃) {Z : C} (g : Y ⟶ Z) (x : HomCokernel R S.f Y) :
    homCokernelEquiv R hS Z hT e (HomCokernel.map R S.f g x) =
      HomCokernel.map R T.f g (homCokernelEquiv R hS Y hT e x) := by
  apply (homCokernelEquivExt R hT Z).injective
  simp

/-- Comparing a presentation with itself induces the identity on its Hom cokernel. -/
@[simp]
theorem homCokernelEquiv_refl [Projective S.X₂] :
    homCokernelEquiv R hS Y hS (Iso.refl S.X₃) = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro x
  apply (homCokernelEquivExt R hS Y).injective
  simp

/-- Reversing the isomorphism of resolved objects reverses the presentation comparison. -/
@[simp]
theorem homCokernelEquiv_symm (hT : T.ShortExact) [Projective S.X₂] [Projective T.X₂]
    (e : S.X₃ ≅ T.X₃) :
    (homCokernelEquiv R hS Y hT e).symm = homCokernelEquiv R hT Y hS e.symm := by
  apply LinearEquiv.ext
  intro x
  apply (homCokernelEquivExt R hS Y).injective
  apply (extLinearEquivOfIso R e (Iso.refl Y) 1).injective
  simp only [extLinearEquivOfIso_apply, Iso.refl_hom, Ext.comp_mk₀_id]
  rw [← homCokernelEquivExt_homCokernelEquiv R hS Y hT e]
  simp

/-- Presentation comparisons compose according to the isomorphisms of resolved objects. -/
@[simp]
theorem homCokernelEquiv_trans {U : ShortComplex C} (hT : T.ShortExact) (hU : U.ShortExact)
    [Projective S.X₂] [Projective T.X₂] [Projective U.X₂]
    (e : S.X₃ ≅ T.X₃) (f : T.X₃ ≅ U.X₃) :
    (homCokernelEquiv R hS Y hT e).trans (homCokernelEquiv R hT Y hU f) =
      homCokernelEquiv R hS Y hU (e ≪≫ f) := by
  apply LinearEquiv.ext
  intro x
  apply (homCokernelEquivExt R hU Y).injective
  simp

end Ring

end TauCeti
