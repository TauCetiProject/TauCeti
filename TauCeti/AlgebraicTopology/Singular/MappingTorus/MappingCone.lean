/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.Algebra.Homology.HomotopyCofiber
import Mathlib.RingTheory.Nilpotent.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# The mapping cone of `id - φ_*` is a model of the chains of a mapping torus

Let `φ : F ≃ₜ F` be a homeomorphism and `T_φ` its mapping torus. The fibre inclusion
`i : F → T_φ` and the monodromy homotopy from `i ∘ φ` to `i` give a chain map
`TauCeti.MappingTorus.wangMappingConeMap` from the mapping cone of `id - φ_*` on the singular
chains of `F` to the singular chains of `T_φ`. This file proves that it is a quasi-isomorphism
(`TauCeti.MappingTorus.quasiIso_wangMappingConeMap`), for coefficients in an abelian category
with coproducts. Hence the singular homology of `T_φ` is the homology of the chain-level mapping
cone `Cone(1 - φ_#)` (`TauCeti.MappingTorus.wangMappingConeHomologyIso`).

The proof follows Milnor's comparison with the infinite cyclic cover `F × ℝ → T_φ`, whose deck
transformation is `τ (x, t) = (φ x, t + 1)`. The chains of `T_φ` are the cokernel of the
degreewise split monomorphism `𝟙 - τ_*` on the chains of `F × ℝ`
(`TauCeti.MappingTorus.cyclicCoverShortComplex_shortExact`), so the map from the mapping cone of
`𝟙 - τ_*` to the chains of `T_φ` is a quasi-isomorphism. The inclusion `s : x ↦ (x, 0)` of the
fibre into the cylinder intertwines `φ` and `τ` up to the homotopy `(t, x) ↦ (φ x, t)`, which
covers the monodromy homotopy of `T_φ`. Together these give a map of cones from `Cone(1 - φ_#)`
to `Cone(1 - τ_#)` through which `wangMappingConeMap` factors. The projection `p : F × ℝ → F`
intertwines `τ` and `φ` exactly, so it induces a map of cones in the other direction which is a
quasi-isomorphism, `p` being a homotopy equivalence. The composite of the two maps of cones is the
identity up to a map `X` that factors through the inclusion of the chains of `F` and kills them,
so `X ≫ X = 0` and the composite is an isomorphism of complexes.

## Main results

* `TauCeti.MappingTorus.quasiIso_wangMappingConeMap`: the chain map from the mapping cone of
  `id - φ_*` to the singular chains of the mapping torus is a quasi-isomorphism.
* `TauCeti.MappingTorus.wangMappingConeHomologyIso`: the resulting isomorphism between the
  homology of the mapping cone of `id - φ_*` and the singular homology of the mapping torus.

## References

* J. Milnor, *Infinite cyclic coverings*, Conference on the Topology of Manifolds (1968),
  Section 1.
* A. Hatcher, *Algebraic Topology*, Section 2.2 (the mapping-torus construction) and
  Example 2.48.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex MonoidalCategory

open scoped Simplicial

universe w v u

namespace TauCeti.MappingTorus

variable {F : Type w} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- The monodromy homotopy lifted to the cylinder: `(t, x) ↦ (φ x, t)` runs from the inclusion
`x ↦ (φ x, 0)` of the fibre after the monodromy to the deck transformation after the inclusion,
`x ↦ (φ x, 1)`. -/
private def cylinderMonodromyHomotopy :
    ((ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun.comp
        (⟨φ, φ.continuous⟩ : C(F, F))).Homotopy
      ((deck φ : C(F × ℝ, F × ℝ)).comp
        (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun) where
  toFun p := (φ p.2, p.1)
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

@[simp]
private lemma cylinderMonodromyHomotopy_apply (t : unitInterval) (x : F) :
    cylinderMonodromyHomotopy φ (t, x) = (φ x, (t : ℝ)) :=
  (rfl)

/-- The lifted monodromy homotopy as a homotopy in `TopCat`. A `TopCat.Homotopy` between
composites of `TopCat.ofHom` maps unfolds to a homotopy between the underlying continuous maps,
which is the type of `cylinderMonodromyHomotopy φ`. -/
private def cylinderMonodromyTopHomotopy :
    TopCat.Homotopy
      (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)) ≫
        TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun)
      (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun ≫
        TopCat.ofHom (deck φ : C(F × ℝ, F × ℝ))) :=
  cylinderMonodromyHomotopy φ

section Preadditive

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

variable (F) in
/-- The map on singular chains induced by the inclusion `x ↦ (x, 0)` of `F` into `F × ℝ`. -/
private def sectionChainMap :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of (F × ℝ)) :=
  ((singularChainComplexFunctor C).obj R).map
    (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun)

variable (F) in
/-- The map on singular chains induced by the projection `F × ℝ → F`. -/
private def projChainMap :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of (F × ℝ)) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of F) :=
  ((singularChainComplexFunctor C).obj R).map
    (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.toFun)

/-- The projection is a retraction of the inclusion at height zero. -/
@[reassoc]
private lemma sectionChainMap_comp_projChainMap :
    sectionChainMap F R ≫ projChainMap F R = 𝟙 _ := by
  rw [sectionChainMap, projChainMap, ← Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  ext x
  simp

@[reassoc]
private lemma sectionChainMap_f_comp_projChainMap_f (n : ℕ) :
    (sectionChainMap F R).f n ≫ (projChainMap F R).f n = 𝟙 _ := by
  rw [← HomologicalComplex.comp_f, sectionChainMap_comp_projChainMap, HomologicalComplex.id_f]

/-- The projection intertwines the deck transformation with the monodromy. -/
private lemma deckChainMap_comp_projChainMap :
    deckChainMap φ R ≫ projChainMap F R = projChainMap F R ≫ monodromyChainMap φ R := by
  rw [deckChainMap_def, monodromyChainMap_def, projChainMap, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  ext p
  simp

/-- The inclusion at height zero followed by the covering map is the fibre inclusion. -/
private lemma sectionChainMap_comp_coverChainMap :
    sectionChainMap F R ≫ coverChainMap φ R = fibreInclusionChainMap φ R := by
  rw [sectionChainMap, coverChainMap_def, fibreInclusionChainMap_def, ← Functor.map_comp]
  congr 1
  ext x
  simp

/-- The singular chain homotopy induced by the lifted monodromy homotopy. -/
private def cylinderSingularChainHomotopy :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)) ≫
          TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun))
      (((singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ).symm.invFun ≫
          TopCat.ofHom (deck φ : C(F × ℝ, F × ℝ)))) :=
  (cylinderMonodromyTopHomotopy φ).singularChainComplexFunctorObjMap R

/-- The chain homotopy on the cylinder from `s ∘ φ` to `τ ∘ s` induced by the lifted monodromy
homotopy, where `s` is the inclusion at height zero. -/
private def cylinderChainHomotopy :
    Homotopy (monodromyChainMap φ R ≫ sectionChainMap F R)
      (sectionChainMap F R ≫ deckChainMap φ R) :=
  (Homotopy.ofEq (by rw [monodromyChainMap_def, sectionChainMap, ← Functor.map_comp])).trans
    ((cylinderSingularChainHomotopy φ R).trans
      (Homotopy.ofEq (by rw [deckChainMap_def, sectionChainMap, Functor.map_comp])))

private lemma cylinderChainHomotopy_hom (i j : ℕ) :
    (cylinderChainHomotopy φ R).hom i j = (cylinderSingularChainHomotopy φ R).hom i j := by
  simp only [cylinderChainHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Pi.zero_apply, zero_add, add_zero]

/-- Followed by the covering map, the chain homotopy of the lifted monodromy homotopy is the
chain homotopy of the monodromy homotopy of the mapping torus. -/
private lemma cylinderChainHomotopy_hom_comp_coverChainMap (i j : ℕ) :
    (cylinderChainHomotopy φ R).hom i j ≫ (coverChainMap φ R).f j =
      (singularChainHomotopy φ R).hom i j := by
  let H := cylinderMonodromyTopHomotopy φ
  let H' : TopCat.Homotopy
      (TopCat.ofHom (⟨φ, φ.continuous⟩ : C(F, F)) ≫ TopCat.ofHom (incl φ))
      (TopCat.ofHom (incl φ)) := monodromyHomotopy φ
  -- The lifted homotopy followed by the covering map is the monodromy homotopy.
  have ht : H'.h = H.h ≫ TopCat.ofHom (coverMap φ) := by
    ext p
    -- Evaluate category morphisms as continuous maps to expose the homotopy tracks.
    change monodromyHomotopy φ (TopCat.I.homeomorph p.2, p.1) =
      coverMap φ (cylinderMonodromyHomotopy φ (TopCat.I.homeomorph p.2, p.1))
    simp
  have hu : 𝟙 (TopCat.toSSet.obj (TopCat.of F)) ▷ Δ[1] ≫ H'.toSSet.h =
      H.toSSet.h ≫ TopCat.toSSet.map (TopCat.ofHom (coverMap φ)) := by
    simp only [id_whiskerRight, Category.id_comp, TopCat.Homotopy.toSSet, Category.assoc,
      ← Functor.map_comp, ← ht]
  have h := H.toSSet.chainComplexMap_hom_comm H'.toSSet hu R i j
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.id_comp] at h
  rw [cylinderChainHomotopy_hom, singularChainHomotopy_hom, coverChainMap_def]
  exact h.symm

variable [HasBinaryBiproducts C]

/-- The composite `(id - φ_*) ≫ s_* ≫ inr` into the mapping cone of `𝟙 - τ_*` is null-homotopic:
`(id - φ_*) ≫ s_* = s_* ≫ (𝟙 - τ_*) + (s_* ≫ τ_* - φ_* ≫ s_*)`, the first summand composed with
`inr` is null-homotopic in the cone, and the second is the difference of two homotopic maps. -/
private def coneComparisonHomotopy :
    Homotopy (wangEndomorphism φ R ≫ sectionChainMap F R ≫
      homotopyCofiber.inr (𝟙 _ - deckChainMap φ R)) 0 :=
  (Homotopy.ofEq (by
      simp only [wangEndomorphism_def, Preadditive.sub_comp, Preadditive.comp_sub,
        Category.id_comp, Category.assoc]
      abel)).trans
    ((((homotopyCofiber.inrCompHomotopy (𝟙 _ - deckChainMap φ R)
          (fun j ↦ ⟨j + 1, by simp⟩)).compLeft (sectionChainMap F R)).add
        ((Homotopy.equivSubZero (cylinderChainHomotopy φ R).symm).compRight
          (homotopyCofiber.inr (𝟙 _ - deckChainMap φ R)))).trans
      (Homotopy.ofEq (by rw [Limits.comp_zero, Limits.zero_comp, add_zero])))

private lemma coneComparisonHomotopy_hom (n : ℕ) :
    (coneComparisonHomotopy φ R).hom n (n + 1) =
      (sectionChainMap F R).f n ≫ homotopyCofiber.inlX (𝟙 _ - deckChainMap φ R) n (n + 1)
          (by simp) -
        (cylinderChainHomotopy φ R).hom n (n + 1) ≫
          homotopyCofiber.inrX (𝟙 _ - deckChainMap φ R) (n + 1) := by
  simp only [coneComparisonHomotopy, Homotopy.trans_hom, Homotopy.add_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.compLeft_hom, Homotopy.compRight_hom,
    Homotopy.equivSubZero_apply_hom, Homotopy.symm_hom,
    homotopyCofiber.inrCompHomotopy_hom (𝟙 _ - deckChainMap φ R) _ n (n + 1) (by simp),
    zero_add, add_zero, Preadditive.neg_comp, homotopyCofiber.inr_f, sub_eq_add_neg]

/-- The map of mapping cones from the Wang mapping cone of `φ` to the mapping cone of `𝟙 - τ_*` on
the chains of the cylinder, induced by the inclusion at height zero and the lifted monodromy
homotopy. -/
private def coneComparison :
    wangMappingCone φ R ⟶ homotopyCofiber (𝟙 _ - deckChainMap φ R) :=
  homotopyCofiber.desc _ (sectionChainMap F R ≫ homotopyCofiber.inr _)
    (coneComparisonHomotopy φ R)

@[reassoc]
private lemma inr_coneComparison :
    homotopyCofiber.inr (wangEndomorphism φ R) ≫ coneComparison φ R =
      sectionChainMap F R ≫ homotopyCofiber.inr _ :=
  homotopyCofiber.inr_desc _ _ _

@[reassoc]
private lemma inrX_coneComparison_f (n : ℕ) :
    homotopyCofiber.inrX (wangEndomorphism φ R) n ≫ (coneComparison φ R).f n =
      (sectionChainMap F R).f n ≫ homotopyCofiber.inrX (𝟙 _ - deckChainMap φ R) n := by
  simpa only [HomologicalComplex.comp_f, homotopyCofiber.inr_f] using
    congrArg (fun k ↦ k.f n) (inr_coneComparison φ R)

@[reassoc]
private lemma inlX_coneComparison_f (n : ℕ) :
    homotopyCofiber.inlX (wangEndomorphism φ R) n (n + 1) (by simp) ≫
        (coneComparison φ R).f (n + 1) =
      (sectionChainMap F R).f n ≫ homotopyCofiber.inlX (𝟙 _ - deckChainMap φ R) n (n + 1)
          (by simp) -
        (cylinderChainHomotopy φ R).hom n (n + 1) ≫
          homotopyCofiber.inrX (𝟙 _ - deckChainMap φ R) (n + 1) := by
  rw [coneComparison, homotopyCofiber.inlX_desc_f, coneComparisonHomotopy_hom]

/-- In degree `n`, the Wang mapping-cone map restricts to the fibre inclusion on the unsuspended
summand. -/
@[reassoc]
private lemma inrX_wangMappingConeMap_f (n : ℕ) :
    homotopyCofiber.inrX (wangEndomorphism φ R) n ≫ (wangMappingConeMap φ R).f n =
      (fibreInclusionChainMap φ R).f n := by
  simpa only [HomologicalComplex.comp_f, homotopyCofiber.inr_f] using
    congrArg (fun k ↦ k.f n) (homotopyCofiber_inr_comp_wangMappingConeMap φ R)

/-- The map from the mapping cone of `𝟙 - τ_*` to the chains of the mapping torus induced by the
covering map. -/
private abbrev coverConeMap :
    homotopyCofiber (𝟙 _ - deckChainMap φ R) ⟶
      ((singularChainComplexFunctor C).obj R).obj (TopCat.of (MappingTorus φ)) :=
  homotopyCofiber.desc (𝟙 _ - deckChainMap φ R) (coverChainMap φ R)
    (Homotopy.ofEq (cyclicCoverShortComplex φ R).zero)

/-- **The Wang mapping-cone map factors through the mapping cone of `𝟙 - τ_*`**: it is the
comparison map of cones followed by the map from that cone to the chains of the mapping torus
induced by the covering map. -/
private lemma coneComparison_comp_coverConeMap :
    coneComparison φ R ≫ coverConeMap φ R = wangMappingConeMap φ R := by
  ext (_ | n) : 1
  · apply homotopyCofiber.ext_from_X' (wangEndomorphism φ R) 0 (by simp)
    rw [HomologicalComplex.comp_f, reassoc_of% inrX_coneComparison_f,
      homotopyCofiber.inrX_desc_f, ← HomologicalComplex.comp_f, sectionChainMap_comp_coverChainMap,
      inrX_wangMappingConeMap_f]
  · apply homotopyCofiber.ext_from_X (wangEndomorphism φ R) n (n + 1) (by simp)
    · rw [HomologicalComplex.comp_f, reassoc_of% inlX_coneComparison_f,
        homotopyCofiber_inlX_comp_wangMappingConeMap_f, Preadditive.sub_comp, Category.assoc,
        Category.assoc, homotopyCofiber.inlX_desc_f, homotopyCofiber.inrX_desc_f,
        cylinderChainHomotopy_hom_comp_coverChainMap]
      simp
    · rw [HomologicalComplex.comp_f, reassoc_of% inrX_coneComparison_f,
        homotopyCofiber.inrX_desc_f, ← HomologicalComplex.comp_f,
        sectionChainMap_comp_coverChainMap, inrX_wangMappingConeMap_f]

/-- The projection `F × ℝ → F` as a morphism of arrows from `𝟙 - τ_*` to `id - φ_*`. -/
private def projArrowHom :
    Arrow.mk (𝟙 _ - deckChainMap φ R) ⟶ Arrow.mk (wangEndomorphism φ R) :=
  Arrow.homMk' (projChainMap F R) (projChainMap F R) (by
    rw [wangEndomorphism_def, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      Category.comp_id, deckChainMap_comp_projChainMap])

omit [HasBinaryBiproducts C] in
private lemma projArrowHom_left : (projArrowHom φ R).left = projChainMap F R := (rfl)

omit [HasBinaryBiproducts C] in
private lemma projArrowHom_right : (projArrowHom φ R).right = projChainMap F R := (rfl)

/-- The map of mapping cones induced by the projection `F × ℝ → F`. -/
private def coneProj :
    homotopyCofiber (𝟙 _ - deckChainMap φ R) ⟶ wangMappingCone φ R :=
  homotopyCofiber.mapArrowHom _ _ (fun j ↦ ⟨j + 1, by simp⟩) (projArrowHom φ R)

@[reassoc]
private lemma inrX_coneProj_f (n : ℕ) :
    homotopyCofiber.inrX (𝟙 _ - deckChainMap φ R) n ≫ (coneProj φ R).f n =
      (projChainMap F R).f n ≫ homotopyCofiber.inrX (wangEndomorphism φ R) n := by
  rw [coneProj, homotopyCofiber.inrX_mapArrowHom_f, projArrowHom_right]

@[reassoc]
private lemma inlX_coneProj_f (n : ℕ) :
    homotopyCofiber.inlX (𝟙 _ - deckChainMap φ R) n (n + 1) (by simp) ≫
        (coneProj φ R).f (n + 1) =
      (projChainMap F R).f n ≫ homotopyCofiber.inlX (wangEndomorphism φ R) n (n + 1) (by simp) := by
  rw [coneProj, homotopyCofiber.inlX_mapArrowHom_f, projArrowHom_left]

/-- The defect `𝟙 - coneComparison ≫ coneProj` of the composite of the two maps of cones. It
vanishes on the chains of `F` and maps the shifted chains of `F` into them. -/
private def coneDefect : wangMappingCone φ R ⟶ wangMappingCone φ R :=
  𝟙 _ - coneComparison φ R ≫ coneProj φ R

@[reassoc]
private lemma inrX_coneDefect_f (n : ℕ) :
    homotopyCofiber.inrX (wangEndomorphism φ R) n ≫ (coneDefect φ R).f n = 0 := by
  rw [coneDefect, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, HomologicalComplex.id_f,
    HomologicalComplex.comp_f, reassoc_of% inrX_coneComparison_f, inrX_coneProj_f,
    reassoc_of% sectionChainMap_f_comp_projChainMap_f]
  simp

@[reassoc]
private lemma inlX_coneDefect_f (n : ℕ) :
    homotopyCofiber.inlX (wangEndomorphism φ R) n (n + 1) (by simp) ≫
        (coneDefect φ R).f (n + 1) =
      (cylinderChainHomotopy φ R).hom n (n + 1) ≫ (projChainMap F R).f (n + 1) ≫
        homotopyCofiber.inrX (wangEndomorphism φ R) (n + 1) := by
  rw [coneDefect, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, HomologicalComplex.id_f,
    HomologicalComplex.comp_f, reassoc_of% inlX_coneComparison_f, Preadditive.sub_comp,
    Category.assoc, Category.assoc, inlX_coneProj_f, inrX_coneProj_f,
    reassoc_of% sectionChainMap_f_comp_projChainMap_f]
  simp

/-- The defect of the composite of the two maps of cones squares to zero. -/
private lemma coneDefect_comp_coneDefect : coneDefect φ R ≫ coneDefect φ R = 0 := by
  ext (_ | n) : 1
  · apply homotopyCofiber.ext_from_X' (wangEndomorphism φ R) 0 (by simp)
    rw [HomologicalComplex.comp_f, reassoc_of% inrX_coneDefect_f]
    simp
  · apply homotopyCofiber.ext_from_X (wangEndomorphism φ R) n (n + 1) (by simp)
    · rw [HomologicalComplex.comp_f, reassoc_of% inlX_coneDefect_f, inrX_coneDefect_f]
      simp
    · rw [HomologicalComplex.comp_f, reassoc_of% inrX_coneDefect_f]
      simp

/-- The composite of the two maps of cones is an isomorphism: it is `𝟙 - X` with `X ≫ X = 0`,
with inverse `𝟙 + X`. -/
private lemma isIso_coneComparison_comp_coneProj :
    IsIso (coneComparison φ R ≫ coneProj φ R) := by
  have h : coneComparison φ R ≫ coneProj φ R = (1 - End.of (coneDefect φ R)).asHom := by
    simp [coneDefect]
  rw [h, ← isUnit_iff_isIso]
  exact IsNilpotent.isUnit_one_sub ⟨2, End.ext (by simp [pow_two, coneDefect_comp_coneDefect])⟩

end Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

/-- **The mapping cone of `id - φ_*` is a model of the chains of the mapping torus.** For a
homeomorphism `φ : F ≃ₜ F` and coefficients `R` in an abelian category with coproducts, the chain
map `wangMappingConeMap` from the mapping cone of `id - φ_*` on the singular chains of `F` to the
singular chains of the mapping torus of `φ`, induced by the fibre inclusion and the monodromy
homotopy, is a quasi-isomorphism. -/
theorem quasiIso_wangMappingConeMap : QuasiIso (wangMappingConeMap φ R) := by
  have : QuasiIso (projChainMap F R) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap, projChainMap, ← cylinderHomologyIso_hom]
    infer_instance
  have : QuasiIso (projArrowHom φ R).left := by rwa [projArrowHom_left]
  have : QuasiIso (projArrowHom φ R).right := by rwa [projArrowHom_right]
  have : QuasiIso (coneProj φ R) :=
    homotopyCofiber.quasiIso_mapArrowHom _ _ (fun j ↦ ⟨j + 1, by simp⟩) (projArrowHom φ R)
  have : QuasiIso (coneComparison φ R ≫ coneProj φ R) := by
    have := isIso_coneComparison_comp_coneProj φ R
    infer_instance
  have : QuasiIso (coneComparison φ R) := quasiIso_of_comp_right _ (coneProj φ R)
  have : QuasiIso (coverConeMap φ R) :=
    (cyclicCoverShortComplex_shortExact φ R).quasiIso_homotopyCofiberDesc fun j ↦ ⟨j + 1, by simp⟩
  rw [← coneComparison_comp_coverConeMap]
  infer_instance

/-- The homology of the mapping cone of `id - φ_*` on the singular chains of `F` is the singular
homology of the mapping torus of `φ`, through `wangMappingConeMap`. -/
def wangMappingConeHomologyIso (n : ℕ) :
    (wangMappingCone φ R).homology n ≅
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of (MappingTorus φ))).homology n :=
  have := quasiIso_wangMappingConeMap φ R
  asIso (homologyMap (wangMappingConeMap φ R) n)

@[simp]
lemma wangMappingConeHomologyIso_hom (n : ℕ) :
    (wangMappingConeHomologyIso φ R n).hom = homologyMap (wangMappingConeMap φ R) n :=
  (rfl)

end TauCeti.MappingTorus
