/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Homology.Ext.Realization

/-!
# Reconstructing short exact sequences from an Ext comparison

For an exact functor `F` out of an abelian category with enough projectives, surjectivity
on `Ext¹(X, Y)` reconstructs every short exact sequence with endpoints `F(Y)` and `F(X)`
as the image of a short exact sequence with
endpoints `Y` and `X`. The comparison is an isomorphism on the middle terms and the
identity on both endpoints, so it preserves the given inclusion and projection.

This converts descent of extension classes into descent of actual extensions, as needed
when reconstructing modules from a formal neighbourhood and its open complement.
No fullness, faithfulness, or preservation of projective objects is required of `F`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 3.4,
  classification of extensions by `Ext¹`.
* [The Stacks Project, Proposition 15.91.16](https://stacks.math.columbia.edu/tag/05ER),
  the step reconstructing an extension from the degree-one comparison of Lemma 15.91.8.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v u' v' w w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Surjectivity on degree-one extensions reconstructs a prescribed short exact sequence
as the image of one with the prescribed endpoints. The resulting isomorphism respects
both the inclusion and the projection. -/
theorem exists_shortExact_map_of_mapExt_one_surjective (X Y : C)
    (hsurj : Function.Surjective (F.mapExtAddHom.{w, w'} X Y 1))
    {E : D} (i : F.obj Y ⟶ E) (p : E ⟶ F.obj X) (hip : i ≫ p = 0)
    (hT : (ShortComplex.mk i p hip).ShortExact) :
    ∃ (E₀ : C) (i₀ : Y ⟶ E₀) (p₀ : E₀ ⟶ X) (hi₀p₀ : i₀ ≫ p₀ = 0)
      (_ : (ShortComplex.mk i₀ p₀ hi₀p₀).ShortExact) (e : F.obj E₀ ≅ E),
      F.map i₀ ≫ e.hom = i ∧ e.hom ≫ p = F.map p₀ := by
  obtain ⟨α, hα⟩ := hsurj hT.extClass
  let P := Classical.choice (EnoughProjectives.presentation X)
  have hP : (ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)).ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_kernel P.f)
  obtain ⟨E₀, i₀, p₀, hi₀p₀, hS, hSα⟩ := hP.exists_extClass_eq Y α
  have hext : (hS.map_of_exact F).extClass = hT.extClass := by
    rw [← Ext.mapExactFunctor_extClass F hS, hSα]
    exact hα
  obtain ⟨e, he₁, he₃⟩ :=
    ((hS.map_of_exact F).exists_iso_iff_extClass_comp_eq hT (Iso.refl _) (Iso.refl _)).mpr
      (by simpa using hext)
  refine ⟨E₀, i₀, p₀, hi₀p₀, hS, ShortComplex.π₂.mapIso e, ?_, ?_⟩
  · simpa [he₁] using e.hom.comm₁₂.symm
  · simpa [he₃] using e.hom.comm₂₃

end CategoryTheory.Functor
