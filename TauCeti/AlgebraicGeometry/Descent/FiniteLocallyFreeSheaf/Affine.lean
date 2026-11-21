/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Affine
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import TauCeti.RingTheory.Finiteness.Descent
import TauCeti.RingTheory.Flat.ProjectiveDimension

/-!
# Affine faithfully flat descent of finite locally free sheaves

Finite local freeness and invertibility of quasi-coherent sheaves are reflected by pullback
along a faithfully flat morphism of affine schemes.

The existing quasi-coherent comparison equivalence then makes descent effective for these
sheaves: a coalgebra whose underlying sheaf is finite locally free or invertible comes from
a sheaf with the same property on the base, compatibly with its coaction.

## Main declarations

* `isFiniteLocallyFree_pullback_specMap_iff`: reflection of finite local freeness;
* `isInvertible_pullback_specMap_iff`: reflection of invertibility;
* `QuasicoherentSheaf.exists_finiteLocallyFree_of_coalgebra` and
  `QuasicoherentSheaf.exists_invertible_of_coalgebra`: effective affine descent.

## References

* [The Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
* [The Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- A quasi-coherent sheaf on an affine scheme is finite locally free if its pullback along
a faithfully flat affine morphism is finite locally free. -/
theorem isFiniteLocallyFree_of_pullback_specMap (hφ : φ.hom.FaithfullyFlat)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : Scheme.Modules.isFiniteLocallyFree (Spec S)
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)) :
    Scheme.Modules.isFiniteLocallyFree (Spec R) M := by
  let := φ.hom.toAlgebra
  have : Module.FaithfullyFlat R S := by
    rwa [← RingHom.faithfullyFlat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
  let N := moduleSpecΓFunctor.obj M
  let e := @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ M)
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)
  let e' := (Scheme.Modules.pullback (Spec.map φ)).mapIso e.symm ≪≫
    (tildeFunctorCompPullbackIso φ).app N
  obtain ⟨hfin, hproj⟩ := (isFiniteLocallyFree_tilde_iff _).mp
    ((Scheme.Modules.isFiniteLocallyFree (Spec S)).prop_of_iso e' hM)
  have : Module.Finite S (S ⊗[R] N) := hfin
  have : Module.Projective S (S ⊗[R] N) := hproj
  have : Module.FinitePresentation S (S ⊗[R] N) :=
    Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation R N :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat S
  have : Module.Projective R N := Module.Projective.of_projective_tensorProduct R N S
  exact (Scheme.Modules.isFiniteLocallyFree (Spec R)).prop_of_iso e
    ((isFiniteLocallyFree_tilde_iff N).mpr ⟨inferInstance, inferInstance⟩)

/-- Finite local freeness of a quasi-coherent sheaf can be checked after a faithfully flat
affine base change. -/
theorem isFiniteLocallyFree_pullback_specMap_iff (hφ : φ.hom.FaithfullyFlat)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    Scheme.Modules.isFiniteLocallyFree (Spec S)
        ((Scheme.Modules.pullback (Spec.map φ)).obj M) ↔
      Scheme.Modules.isFiniteLocallyFree (Spec R) M := by
  refine ⟨isFiniteLocallyFree_of_pullback_specMap φ hφ M, fun hM ↦ ?_⟩
  simpa only [FiniteLocallyFreeSheaf.pullback_obj_obj] using
    ((FiniteLocallyFreeSheaf.pullback (Spec.map φ)).obj ⟨M, hM⟩).property

/-- A quasi-coherent sheaf on an affine scheme is invertible if its pullback along a faithfully
flat affine morphism is invertible. -/
theorem isInvertible_of_pullback_specMap (hφ : φ.hom.FaithfullyFlat)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : SheafOfModules.isInvertible (Spec S)
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)) :
    SheafOfModules.isInvertible (Spec R) M := by
  have hfin := ((InvertibleSheaf.toFiniteLocallyFree (Spec S)).obj ⟨_, hM⟩).property
  let E : FiniteLocallyFreeSheaf (Spec R) :=
    ⟨M, isFiniteLocallyFree_of_pullback_specMap φ hφ M hfin⟩
  apply E.isInvertible_iff_forall_rank_eq_one.mpr
  intro x
  obtain ⟨y, hy⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hφ).2 x
  have hI : SheafOfModules.isInvertible (Spec S)
      ((FiniteLocallyFreeSheaf.pullback (Spec.map φ)).obj E).obj := by
    simpa only [FiniteLocallyFreeSheaf.pullback_obj_obj] using hM
  have h := (FiniteLocallyFreeSheaf.isInvertible_iff_forall_rank_eq_one
    ((FiniteLocallyFreeSheaf.pullback (Spec.map φ)).obj E)).mp hI y
  have hrank := (FiniteLocallyFreeSheaf.rank_pullback_apply (Spec.map φ) E y).symm.trans h
  have hxy : (Spec.map φ) y = x := (Spec.map_apply φ y).trans hy
  exact hxy ▸ hrank

/-- Invertibility of a quasi-coherent sheaf can be checked after a faithfully flat affine base
change. -/
theorem isInvertible_pullback_specMap_iff (hφ : φ.hom.FaithfullyFlat)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    SheafOfModules.isInvertible (Spec S) ((Scheme.Modules.pullback (Spec.map φ)).obj M) ↔
      SheafOfModules.isInvertible (Spec R) M := by
  refine ⟨isInvertible_of_pullback_specMap φ hφ M, fun hM ↦ ?_⟩
  have := hM
  exact SheafOfModules.isInvertible_pullback (Spec.map φ) M

namespace QuasicoherentSheaf

/-- A coalgebra for affine faithfully flat descent whose underlying sheaf is finite locally
free is induced by a finite locally free sheaf on the base. The isomorphism respects the
descent coaction. -/
theorem exists_finiteLocallyFree_of_coalgebra (hφ : φ.hom.FaithfullyFlat)
    (D : (pullbackPushforwardSpecMapAdjunction φ).toComonad.Coalgebra)
    (hD : Scheme.Modules.isFiniteLocallyFree (Spec S) D.A.obj) :
    ∃ M : QuasicoherentSheaf (Spec R),
      Scheme.Modules.isFiniteLocallyFree (Spec R) M.obj ∧
        Nonempty ((Comonad.comparison (pullbackPushforwardSpecMapAdjunction φ)).obj M ≅ D) := by
  have := isEquivalence_comparison_pullbackPushforwardSpecMapAdjunction φ hφ
  let F := Comonad.comparison (pullbackPushforwardSpecMapAdjunction φ)
  let M := F.objPreimage D
  let e := F.objObjPreimageIso D
  let e' := ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι).mapIso
    ((pullbackPushforwardSpecMapAdjunction φ).toComonad.forget.mapIso e)
  let e'' : (Scheme.Modules.pullback (Spec.map φ)).obj M.obj ≅ D.A.obj :=
    (eqToIso (pullback_obj_obj (Spec.map φ) M)).symm ≪≫ e'
  have : M.obj.IsQuasicoherent := M.property
  exact ⟨M, isFiniteLocallyFree_of_pullback_specMap φ hφ M.obj
    ((Scheme.Modules.isFiniteLocallyFree (Spec S)).prop_of_iso e''.symm hD), ⟨e⟩⟩

/-- A coalgebra for affine faithfully flat descent whose underlying sheaf is invertible is
induced by an invertible sheaf on the base, with an isomorphism respecting the descent coaction. -/
theorem exists_invertible_of_coalgebra (hφ : φ.hom.FaithfullyFlat)
    (D : (pullbackPushforwardSpecMapAdjunction φ).toComonad.Coalgebra)
    (hD : SheafOfModules.isInvertible (Spec S) D.A.obj) :
    ∃ M : QuasicoherentSheaf (Spec R),
      SheafOfModules.isInvertible (Spec R) M.obj ∧
        Nonempty ((Comonad.comparison (pullbackPushforwardSpecMapAdjunction φ)).obj M ≅ D) := by
  have := isEquivalence_comparison_pullbackPushforwardSpecMapAdjunction φ hφ
  let F := Comonad.comparison (pullbackPushforwardSpecMapAdjunction φ)
  let M := F.objPreimage D
  let e := F.objObjPreimageIso D
  let e' := ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι).mapIso
    ((pullbackPushforwardSpecMapAdjunction φ).toComonad.forget.mapIso e)
  let e'' : (Scheme.Modules.pullback (Spec.map φ)).obj M.obj ≅ D.A.obj :=
    (eqToIso (pullback_obj_obj (Spec.map φ) M)).symm ≪≫ e'
  have : M.obj.IsQuasicoherent := M.property
  exact ⟨M, isInvertible_of_pullback_specMap φ hφ M.obj
    ((SheafOfModules.isInvertible (Spec S)).prop_of_iso e''.symm hD), ⟨e⟩⟩

end QuasicoherentSheaf

end TauCeti.AlgebraicGeometry
