/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.Topology.MappingTorus.Refl

/-!
# The homology of a product with a circle

For the mapping torus of the identity of a space `F`, the Wang endomorphism `𝟙 - φ_*` vanishes,
so the Wang sequence breaks into short exact sequences

`0 ⟶ Hₙ₊₁(F) ⟶ Hₙ₊₁(T) ⟶ Hₙ(F) ⟶ 0`

(`TauCeti.MappingTorus.shortExact_wang_refl`), with coefficients in any object of an abelian
category with coproducts. The mapping torus of the identity is the product `S¹ × F`
(`TauCeti.MappingTorus.reflCircleHomeomorph`), so this describes the homology of a product with a
circle, for any space `F` and with coefficients in any such abelian category.

Reading it on `S¹ × F`, with the circle the unit circle `Circle` of `ℂ`, the inclusion
`F → S¹ × F`, `y ↦ (1, y)`, is a monomorphism on homology in every degree
(`TauCeti.mono_singularHomologyMap_prodMk_const_one`) and an isomorphism in degree zero
(`TauCeti.isIso_singularHomologyMap_prodMk_const_one_zero`). In degree `n + 1` it is an isomorphism
exactly when `Hₙ(F)` vanishes (`TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff`), and
`Hₙ₊₁(S¹ × F)` vanishes exactly when `Hₙ₊₁(F)` and `Hₙ(F)` do
(`TauCeti.isZero_singularHomology_circle_prod_succ_iff`). These are the forms in which the
homology of a space weakly equivalent to `S¹ × F`, such as the loop space of a complex projective
space, is computed from that of `F`.

## Main results

* `TauCeti.MappingTorus.shortExact_wang_refl`: the Wang sequence of the mapping torus of the
  identity splits into short exact sequences.
* `TauCeti.isIso_singularHomologyMap_prodMk_const_one_succ_iff`: `Hₙ₊₁(F) → Hₙ₊₁(S¹ × F)` is an
  isomorphism if and only if `Hₙ(F) = 0`.
* `TauCeti.isZero_singularHomology_circle_prod_succ_iff`: `Hₙ₊₁(S¹ × F) = 0` if and only if
  `Hₙ₊₁(F) = 0` and `Hₙ(F) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a mapping
  torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace TauCeti

namespace MappingTorus

variable (F : Type w) [TopologicalSpace F]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The monodromy of the mapping torus of the identity induces the identity on singular chains. -/
@[simp]
theorem monodromyChainMap_refl : monodromyChainMap (Homeomorph.refl F) R = 𝟙 _ := by
  rw [monodromyChainMap_def]
  exact ((singularChainComplexFunctor A).obj R).map_id (TopCat.of F)

/-- The Wang endomorphism `𝟙 - φ_*` of the mapping torus of the identity vanishes. -/
@[simp]
theorem wangEndomorphism_refl : wangEndomorphism (Homeomorph.refl F) R = 0 := by
  rw [wangEndomorphism_def, monodromyChainMap_refl, sub_self]

/-- For the mapping torus of the identity, the fibre inclusion is a monomorphism on homology in
every degree. -/
instance mono_homologyMap_fibreInclusionChainMap_refl (n : ℕ) :
    Mono (homologyMap (fibreInclusionChainMap (Homeomorph.refl F) R) n) :=
  (wang_exact₂ (Homeomorph.refl F) R n).mono_g (by simp)

/-- For the mapping torus of the identity, the Wang connecting morphism is an epimorphism in every
degree. -/
instance epi_wangδ_refl (n : ℕ) : Epi (wangδ (Homeomorph.refl F) R n) :=
  (wang_exact₁ (Homeomorph.refl F) R n).epi_f (by simp)

/-- **The Wang sequence of the mapping torus of the identity splits into short exact sequences**
`0 ⟶ Hₙ₊₁(F) ⟶ Hₙ₊₁(T) ⟶ Hₙ(F) ⟶ 0`, with maps the fibre inclusion and the Wang connecting
morphism. -/
theorem shortExact_wang_refl (n : ℕ) :
    (ShortComplex.mk _ _
      (homologyMap_fibreInclusionChainMap_comp_wangδ (Homeomorph.refl F) R n)).ShortExact :=
  .mk' (wang_exact₃ (Homeomorph.refl F) R n) inferInstance inferInstance

end MappingTorus

variable {F : Type w} [TopologicalSpace F]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The map `Hₙ(F) → Hₙ(S¹ × F)` induced by `y ↦ (1, y)` is the map induced by the fibre
inclusion of the mapping torus of the identity, followed by an isomorphism. -/
private theorem singularHomologyMap_prodMk_const_one_eq (n : ℕ) :
    ((singularHomologyFunctor A n).obj R).map
        (TopCat.ofHom ((ContinuousMap.const F (1 : Circle)).prodMk (ContinuousMap.id F))) =
      ((singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom (MappingTorus.incl (Homeomorph.refl F))) ≫
        ((singularHomologyFunctor A n).obj R).map
          (TopCat.ofHom (MappingTorus.reflCircleHomeomorph (F := F) :
            C(MappingTorus (Homeomorph.refl F), Circle × F))) := by
  rw [← MappingTorus.reflCircleHomeomorph_comp_incl, TopCat.ofHom_comp, Functor.map_comp]

private instance mono_singularHomologyMap_incl_refl (n : ℕ) :
    Mono (((singularHomologyFunctor A n).obj R).map
      (TopCat.ofHom (MappingTorus.incl (Homeomorph.refl F)))) := by
  rw [MappingTorus.singularHomologyMap_incl_eq]
  exact MappingTorus.mono_homologyMap_fibreInclusionChainMap_refl F R n

private instance isIso_singularHomologyMap_reflCircleHomeomorph (n : ℕ) :
    IsIso (((singularHomologyFunctor A n).obj R).map
      (TopCat.ofHom (MappingTorus.reflCircleHomeomorph (F := F) :
        C(MappingTorus (Homeomorph.refl F), Circle × F)))) :=
  (((singularHomologyFunctor A n).obj R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of _) (Y := TopCat.of _)
      (MappingTorus.reflCircleHomeomorph (F := F)))).isIso_hom

/-- **The inclusion `F → S¹ × F`, `y ↦ (1, y)`, is a monomorphism on singular homology** in every
degree. -/
instance mono_singularHomologyMap_prodMk_const_one (n : ℕ) :
    Mono (((singularHomologyFunctor A n).obj R).map
      (TopCat.ofHom ((ContinuousMap.const F (1 : Circle)).prodMk (ContinuousMap.id F)))) := by
  rw [singularHomologyMap_prodMk_const_one_eq]
  infer_instance

/-- **The inclusion `F → S¹ × F`, `y ↦ (1, y)`, is an isomorphism on `H₀`.** -/
instance isIso_singularHomologyMap_prodMk_const_one_zero :
    IsIso (((singularHomologyFunctor A 0).obj R).map
      (TopCat.ofHom ((ContinuousMap.const F (1 : Circle)).prodMk (ContinuousMap.id F)))) := by
  have : Epi (((singularHomologyFunctor A 0).obj R).map
      (TopCat.ofHom (MappingTorus.incl (Homeomorph.refl F)))) := by
    rw [MappingTorus.singularHomologyMap_incl_eq]
    exact MappingTorus.epi_homologyMap_fibreInclusionChainMap_zero (Homeomorph.refl F) R
  have := isIso_of_mono_of_epi (((singularHomologyFunctor A 0).obj R).map
      (TopCat.ofHom (MappingTorus.incl (Homeomorph.refl F))))
  rw [singularHomologyMap_prodMk_const_one_eq]
  infer_instance

/-- **The inclusion `F → S¹ × F`, `y ↦ (1, y)`, is an isomorphism on `Hₙ₊₁` exactly when `Hₙ(F)`
vanishes.** -/
theorem isIso_singularHomologyMap_prodMk_const_one_succ_iff (n : ℕ) :
    IsIso (((singularHomologyFunctor A (n + 1)).obj R).map
        (TopCat.ofHom ((ContinuousMap.const F (1 : Circle)).prodMk (ContinuousMap.id F)))) ↔
      IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of F)) := by
  rw [singularHomologyMap_prodMk_const_one_eq, isIso_comp_right_iff,
    MappingTorus.singularHomologyMap_incl_eq]
  exact (MappingTorus.shortExact_wang_refl F R n).isIso_f_iff

/-- **`Hₙ₊₁(S¹ × F)` vanishes exactly when `Hₙ₊₁(F)` and `Hₙ(F)` do.** -/
theorem isZero_singularHomology_circle_prod_succ_iff (n : ℕ) :
    IsZero (((singularHomologyFunctor A (n + 1)).obj R).obj (TopCat.of (Circle × F))) ↔
      IsZero (((singularHomologyFunctor A (n + 1)).obj R).obj (TopCat.of F)) ∧
        IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of F)) := by
  have hS := MappingTorus.shortExact_wang_refl F R n
  rw [← (((singularHomologyFunctor A (n + 1)).obj R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of _) (Y := TopCat.of _)
      (MappingTorus.reflCircleHomeomorph (F := F)))).isZero_iff]
  -- The middle term of a short exact sequence vanishes exactly when the outer two do.
  refine ⟨fun h ↦ ⟨@IsZero.of_mono _ _ _ _ _ _
    (MappingTorus.mono_homologyMap_fibreInclusionChainMap_refl F R (n + 1)) h,
      @IsZero.of_epi _ _ _ _ _ _ (MappingTorus.epi_wangδ_refl F R n) h⟩, fun ⟨h₁, h₃⟩ ↦ ?_⟩
  exact hS.exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end TauCeti
