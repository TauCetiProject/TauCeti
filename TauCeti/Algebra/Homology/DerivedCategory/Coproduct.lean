/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.HomotopyCategory.Coproduct
public import TauCeti.Algebra.Homology.ShortComplex.Colimit

/-!
# Coproducts in the derived category

Let `C` be an abelian category with K-injective resolutions, for instance a Grothendieck abelian
category such as the category of sheaves of modules on a ringed site.

The derived category `D(C)` is a reflective subcategory of the homotopy category, via the
K-injective replacement functor `TauCeti.kInjectiveReplacement`, and the homotopy category has the
coproducts of `C` (`TauCeti.Algebra.Homology.HomotopyCategory.Coproduct`). Hence `D(C)` has all
coproducts which exist in `C`, and the localization functor
`DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C` preserves them: a coproduct in `D(C)`
is represented by the degreewise coproduct of complexes. When these coproducts are exact in `C`,
the homology functors `DerivedCategory.homologyFunctor C n` preserve them as well.

Further, let `N` be an object of the derived category and `(Xᵢ)` a family of objects of `C` with a
coproduct `∐ Xᵢ`. If every map from each `Xᵢ` placed in degree `n` to `N` vanishes, then so does
every map from `∐ Xᵢ` placed in degree `n`
(`DerivedCategory.singleFunctor_hom_eq_zero_of_isColimit`). No exactness of coproducts in `C` is
assumed. Represent `N` by a K-injective complex `L`. Maps from `X` placed in degree `n` to `L` in
the derived category are homotopy classes of chain maps, that is, maps `X ⟶ Lⁿ` killed by the
differential, modulo those factoring through the differential `Lⁿ⁻¹ ⟶ Lⁿ`
(`CochainComplex.nonempty_homotopy_zero_iff_of_single`). A factorization through the differential
can be chosen on each summand and glued along the coproduct.
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory

universe w' w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [TauCeti.HasKInjectiveResolutions C]

namespace DerivedCategory

section

variable {J : Type w'} [HasColimitsOfShape (Discrete J) C]

/-- The derived category of an abelian category with K-injective resolutions has the coproducts
which exist in the abelian category: it is a reflective subcategory of the homotopy category. -/
instance : HasColimitsOfShape (Discrete J) (DerivedCategory C) :=
  have : Reflective (TauCeti.kInjectiveReplacement C) :=
    { L := Qh, adj := TauCeti.kInjectiveReplacementAdjunction C }
  hasColimitsOfShape_of_reflective (TauCeti.kInjectiveReplacement C)

/-- A coproduct in the derived category is represented by the degreewise coproduct of
complexes. -/
instance : PreservesColimitsOfShape (Discrete J) (Q : CochainComplex C ℤ ⥤ DerivedCategory C) :=
  have := (TauCeti.kInjectiveReplacementAdjunction C).leftAdjoint_preservesColimits
  preservesColimitsOfShape_of_natIso (quotientCompQhIso C)

/-- When coproducts are exact in `C`, the homology functors of the derived category preserve
coproducts. -/
instance [HasExactColimitsOfShape (Discrete J) C] (n : ℤ) :
    PreservesColimitsOfShape (Discrete J) (homologyFunctor C n) where
  preservesColimit {G} := by
    -- represent the diagram by complexes, and compute its coproduct degreewise
    let K : Discrete J ⥤ CochainComplex C ℤ := Discrete.functor fun j ↦ Q.objPreimage (G.obj ⟨j⟩)
    let e : K ⋙ Q ≅ G := Discrete.natIso fun j ↦ Q.objObjPreimageIso (G.obj j)
    have : PreservesColimitsOfShape (Discrete J) (Q ⋙ homologyFunctor C n) :=
      preservesColimitsOfShape_of_natIso (homologyFunctorFactors C n).symm
    have : PreservesColimit (K ⋙ Q) (homologyFunctor C n) :=
      preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves Q (colimit.isColimit K))
        (isColimitOfPreserves (Q ⋙ homologyFunctor C n) (colimit.isColimit K))
    exact preservesColimit_of_iso_diagram _ e

end

open CochainComplex in
/-- If every map from each `Xᵢ` placed in degree `n` to `N` vanishes, then so does every map from
their coproduct placed in degree `n`. -/
lemma singleFunctor_hom_eq_zero_of_isColimit {ι : Type*} {X : ι → C} {c : Cofan X}
    (hc : IsColimit c) {n : ℤ} {N : DerivedCategory C}
    (h : ∀ i (φ : (singleFunctor C n).obj (X i) ⟶ N), φ = 0)
    (φ : (singleFunctor C n).obj c.pt ⟶ N) : φ = 0 := by
  obtain ⟨L, i, _, _⟩ :=
    TauCeti.HasKInjectiveResolutions.exists_quasiIso_isKInjective (Q.objPreimage N)
  let e : N ≅ Q.obj L := (Q.objObjPreimageIso N).symm ≪≫ asIso (Q.map i)
  rw [← cancel_mono e.hom, zero_comp]
  obtain ⟨χ, hχ⟩ := IsKInjective.Q_map_surjective _ L (φ ≫ e.hom)
  rw [← hχ, IsKInjective.Q_map_eq_zero_iff,
    nonempty_homotopy_zero_iff_of_single L (sub_add_cancel n 1)]
  -- On each summand the composite vanishes, so its component factors through the differential.
  have (j : ι) : ∃ g : X j ⟶ L.X (n - 1), g ≫ L.d (n - 1) n =
      (HomologicalComplex.singleObjXSelf (.up ℤ) n (X j)).inv ≫
        ((HomologicalComplex.single C _ n).map (c.inj j) ≫ χ).f n := by
    rw [← nonempty_homotopy_zero_iff_of_single L (sub_add_cancel n 1),
      ← IsKInjective.Q_map_eq_zero_iff, Functor.map_comp, hχ, Q_map_single_map, ← Category.assoc]
    have := h j ((singleFunctor C n).map (c.inj j) ≫ φ)
    rw [this, zero_comp]
  choose g hg using this
  refine ⟨Cofan.IsColimit.desc hc g, Cofan.IsColimit.hom_ext hc _ _ fun j ↦ ?_⟩
  rw [Cofan.IsColimit.fac_assoc, hg]
  simp [HomologicalComplex.single_map_f_self]

end DerivedCategory
