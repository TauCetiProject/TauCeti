/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Homology.Single.Projective
public import TauCeti.CategoryTheory.Triangulated.Orthogonal.Basic

/-!
# Morphisms from a projective object placed in one degree

Let `P` be a projective object of an abelian category `C`, placed in degree `n` of the derived
category. For every object `M` of `D(C)`, taking `n`-th cohomology is a bijection
`Hom_{D(C)}(P[-n], M) ≃ Hom_C(P, Hⁿ(M))`
(`DerivedCategory.homologyFunctor_map_bijective_of_projective`). No boundedness of `M` is needed:
`P` placed in one degree is K-projective, so every such morphism is a chain map, and a chain map
which vanishes on cohomology is null-homotopic since `P` is projective
(`CochainComplex.nonempty_homotopy_zero_of_homologyMap_eq_zero`).

As a consequence, for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` in `C` with `X₁` and `X₂`
projective, every morphism from `X₃` placed in degree zero to every shift of `M` vanishes if and
only if precomposition with `X₁ → X₂` is a bijection `Hom(X₂, Hⁿ(M)) → Hom(X₁, Hⁿ(M))` for every
`n` (`CategoryTheory.ShortComplex.ShortExact.forall_singleFunctor_hom_eq_zero_iff`). This is the
form in which the projective dimension of `X₃`, at most one, enters into derived completeness.

## Main results

* `DerivedCategory.homologyFunctor_map_bijective_of_projective`: for a projective `P`, `Hⁿ` is a
  bijection from morphisms `P[-n] ⟶ M` to morphisms `P ⟶ Hⁿ(M)`.
* `CategoryTheory.ShortComplex.ShortExact.forall_singleFunctor_hom_eq_zero_iff`: the
  corresponding statement in `D(C)` for a projective presentation of length one, in terms of the
  cohomology of `M`.
-/

public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open HomologicalComplex

/-- **Morphisms from a projective object placed in one degree.** For a projective object `P` of
`C`, every object `M` of `D(C)` and every `n : ℤ`, taking `n`-th cohomology is a bijection from
morphisms `P[-n] ⟶ M` to morphisms `Hⁿ(P[-n]) ⟶ Hⁿ(M)`, and `Hⁿ(P[-n]) ≅ P`. -/
theorem homologyFunctor_map_bijective_of_projective (P : C) [Projective P]
    (M : DerivedCategory C) (n : ℤ) :
    Function.Bijective
      ((homologyFunctor C n).map : ((singleFunctor C n).obj P ⟶ M) → _) := by
  let H := homologyFunctor C n
  let K := (CochainComplex.singleFunctor C n).obj P
  have := CochainComplex.isKProjective_of_projective K n
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (Q.obj L ≅ M) := ⟨_, ⟨Q.objObjPreimageIso M⟩⟩
  let η := homologyFunctorFactors C n
  -- The case of `Q.obj L`, by comparison with the cohomology of chain maps.
  have key : Function.Bijective (H.map : (Q.obj K ⟶ Q.obj L) → _) := by
    refine ⟨fun φ₁ φ₂ hφ ↦ ?_, fun ψ ↦ ?_⟩
    · rw [← sub_eq_zero]
      obtain ⟨g, hg⟩ := CochainComplex.IsKProjective.Q_map_surjective K L (φ₁ - φ₂)
      rw [← hg]
      obtain ⟨ho⟩ := CochainComplex.nonempty_homotopy_zero_of_homologyMap_eq_zero g (by
        have h := homologyFunctorFactors_hom_naturality g n
        rw [hg, H.map_sub, hφ, sub_self, zero_comp] at h
        exact (Iso.cancel_iso_hom_left ((homologyFunctorFactors C n).app K) _ _).1
          (h.symm.trans comp_zero.symm))
      exact (Q_map_eq_of_homotopy C ho).trans (Q.map_zero _ _)
    · obtain ⟨g, hg⟩ := CochainComplex.exists_homologyMap_eq_of_projective (L := L) (n := n)
        ((singleObjHomologySelfIso _ n P).inv ≫ η.inv.app K ≫ ψ ≫ η.hom.app L)
      refine ⟨Q.map g, ?_⟩
      have h := homologyFunctorFactors_hom_naturality g n
      rw [hg, Iso.hom_inv_id_assoc] at h
      rw [← cancel_mono (η.hom.app L), h]
      exact (homologyFunctorFactors C n).hom_inv_id_app_assoc _ _
  have h : (H.map : ((singleFunctor C n).obj P ⟶ M) → _) =
      (fun ψ ↦ ψ ≫ (H.mapIso e).hom) ∘ H.map ∘ fun φ ↦ φ ≫ e.symm.hom := by
    funext φ
    simp only [Function.comp_apply, Functor.mapIso_hom, Iso.symm_hom, ← H.map_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  exact ((H.mapIso e).homToEquiv.bijective.comp key).comp e.symm.homToEquiv.bijective

end DerivedCategory

namespace CategoryTheory.ShortComplex.ShortExact

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₁` and `X₂` projective and an
object `M` of `D(C)`, every morphism from `X₃` placed in degree zero to every shift of `M`
vanishes if and only if precomposition with `X₁ → X₂` is a bijection
`Hom(X₂, H⁰(M⟦n⟧)) → Hom(X₁, H⁰(M⟦n⟧))` for every `n`. -/
theorem forall_singleFunctor_hom_eq_zero_iff {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₁] [Projective S.X₂] (M : DerivedCategory C) :
    (∀ (n : ℤ) (φ : (singleFunctor C 0).obj S.X₃ ⟶ M⟦n⟧), φ = 0) ↔
      ∀ n : ℤ, Function.Bijective
        fun g : S.X₂ ⟶ (DerivedCategory.homologyFunctor C 0).obj (M⟦n⟧) ↦ S.f ≫ g := by
  refine (forall_hom_shift_eq_zero_iff hS.singleTriangle_distinguished M).trans
    (forall_congr' fun n ↦ ?_)
  let H := DerivedCategory.homologyFunctor C 0
  let ε := singleFunctorCompHomologyFunctorIso C 0
  -- Under `H⁰`, precomposition with `X₁[0] ⟶ X₂[0]` is precomposition with `X₁ ⟶ X₂`.
  let Φ (X : C) : ((singleFunctor C 0).obj X ⟶ M⟦n⟧) → (X ⟶ H.obj (M⟦n⟧)) :=
    fun φ ↦ (ε.app X).symm.hom ≫ H.map φ
  have hΦ (X : C) [Projective X] : Function.Bijective (Φ X) :=
    (ε.app X).homFromEquiv.bijective.comp (homologyFunctor_map_bijective_of_projective X _ 0)
  have hcomm : Φ S.X₁ ∘ (fun g ↦ (singleFunctor C 0).map S.f ≫ g) =
      (fun g ↦ S.f ≫ g) ∘ Φ S.X₂ := by
    ext g
    simp only [Function.comp_apply, Φ, H.map_comp]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (ε.inv.naturality S.f).symm
  dsimp only [singleTriangle_obj₂, singleTriangle_mor₁]
  rw [← Function.Bijective.of_comp_iff' (hΦ S.X₁), hcomm,
    Function.Bijective.of_comp_iff _ (hΦ S.X₂)]

end CategoryTheory.ShortComplex.ShortExact
