/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity

/-!
# Coherence of internal Hom under pullback

The canonical internal-Hom comparison respects the identity and composition isomorphisms
of module pullback. These equations allow base change of internal Hom to be iterated without
choosing new comparison maps. The source is quasicoherent and the target is arbitrary; these
coherence equations assume neither flatness nor invertibility of the internal-Hom comparison.

If the comparison along `f` is invertible, the composition criterion identifies invertibility
along `f ≫ g` with invertibility of the pullback along `f` of the comparison along `g`. This
allows invertibility to be checked on open covers.

Composed with the identification `f^* 𝒪_Y ≅ 𝒪_X`, the comparison at the structure sheaf is the
base-change map `f^* 𝓗om(M, 𝒪_Y) ⟶ 𝓗om(f^* M, 𝒪_X)` of linear functionals. It is compatible with
composites and with replacing `f` by an equal morphism, and it carries the pullback of evaluation
at a global section `s` of `M` to evaluation at the pulled-back section of `f^* M`. These are the
inputs for the naturality, in the test scheme, of descriptions of points by sections or by linear
functionals.

The equations use Mathlib's `Scheme.Modules.pullbackId` and `pullbackComp`, and the canonical
tensor comparison of module pullback. For finite locally free sources they also describe the
coherence of the resulting internal-Hom base-change isomorphisms.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

/-- The internal-Hom comparison along the identity is the internal-Hom map induced by the
canonical identity isomorphism of module pullback. -/
@[reassoc (attr := simp)]
theorem pullbackIhomComparison_id (M N : X.Modules) [M.IsQuasicoherent] :
    (pullbackIhomComparison M (𝟙 X)).app N ≫
        (ihom ((Scheme.Modules.pullback (𝟙 X)).obj M)).map
          ((Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackId X).hom.app ((ihom M).obj N) ≫
        (pre ((Scheme.Modules.pullbackId X).hom.app M)).app N := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_natural_left]
  -- Instantiate precomposition before normalizing the identity functor objects.
  rw [uncurry_pre ((Scheme.Modules.pullbackId X).hom.app M) N, uncurry_eq]
  dsimp only [Functor.id_obj]
  rw [whiskerLeft_pullbackIhomComparison_app_comp_ev]
  rw [← cancel_epi (δ (Scheme.Modules.pullback (𝟙 X)) M ((ihom M).obj N))]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← dsimp% tensorHom_def'_assoc (C := X.Modules)
    ((Scheme.Modules.pullbackId X).hom.app M)
    ((Scheme.Modules.pullbackId X).hom.app ((ihom M).obj N))]
  rw [Scheme.Modules.pullback_id_δ_assoc]
  exact (Scheme.Modules.pullbackId X).hom.naturality ((ihom.ev M).app N)

/-- The internal-Hom comparison for a composite agrees with the two successive comparisons,
using the canonical composition isomorphism on its source, target, and argument. -/
@[reassoc]
theorem pullbackIhomComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback f).map ((pullbackIhomComparison M g).app N) ≫
        (pullbackIhomComparison ((Scheme.Modules.pullback g).obj M) f).app
          ((Scheme.Modules.pullback g).obj N) ≫
        (ihom ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))).map
          ((Scheme.Modules.pullbackComp f g).hom.app N) =
      (Scheme.Modules.pullbackComp f g).hom.app ((ihom M).obj N) ≫
        (pullbackIhomComparison M (f ≫ g)).app N ≫
        (pre ((Scheme.Modules.pullbackComp f g).hom.app M)).app
          ((Scheme.Modules.pullback (f ≫ g)).obj N) := by
  -- Compare both routes after evaluation, normalizing composite functor objects.
  apply uncurry_injective
  simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [ihom.ev_naturality
    ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
    ((Scheme.Modules.pullbackComp f g).hom.app N)]
  rw [dsimp% id_tensor_pre_app_comp_ev
    ((Scheme.Modules.pullbackComp f g).hom.app M)
    ((Scheme.Modules.pullback (f ≫ g)).obj N)]
  dsimp only [Functor.comp_obj]
  rw [whiskerLeft_pullbackIhomComparison_app_comp_ev_assoc
    ((Scheme.Modules.pullback g).obj M) f ((Scheme.Modules.pullback g).obj N)]
  rw [whisker_exchange_assoc]
  rw [whiskerLeft_pullbackIhomComparison_app_comp_ev]
  -- Cancel the two tensor comparisons to reduce to monoidal composition coherence.
  rw [← cancel_epi (δ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj M)
    ((Scheme.Modules.pullback g).obj ((ihom M).obj N)))]
  rw [δ_natural_right_assoc]
  rw [IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    whiskerLeft_pullbackIhomComparison_app_comp_ev]
  rw [← tensorHom_def'_assoc]
  rw [← cancel_epi ((Scheme.Modules.pullback f).map
    (δ (Scheme.Modules.pullback g) M ((ihom M).obj N)))]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rw [← pullbackComp_hom_app_comp_δ_assoc]
  simp only [IsIso.hom_inv_id_assoc]
  exact (Scheme.Modules.pullbackComp f g).hom.naturality ((ihom.ev M).app N)

/-- If the internal-Hom comparison along `f` is invertible on the pullbacks of `M` and `N`,
then invertibility along `f ≫ g` is equivalent to invertibility of the pullback along `f`
of the comparison along `g`. This allows invertibility to be checked on open covers. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_comp_iff
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) [M.IsQuasicoherent]
    [IsIso ((pullbackIhomComparison ((Scheme.Modules.pullback g).obj M) f).app
      ((Scheme.Modules.pullback g).obj N))] :
    IsIso ((pullbackIhomComparison M (f ≫ g)).app N) ↔
      IsIso ((Scheme.Modules.pullback f).map ((pullbackIhomComparison M g).app N)) := by
  have hpre := pre_isIso ((Scheme.Modules.pullbackComp f g).app M)
  have : IsIso ((pre ((Scheme.Modules.pullbackComp f g).hom.app M)).app
      ((Scheme.Modules.pullback (f ≫ g)).obj N)) :=
    (NatTrans.isIso_iff_isIso_app _).mp hpre _
  have h := congrArg IsIso (pullbackIhomComparison_comp f g M N)
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using (Iff.of_eq h).symm

section Unit

/-- The base-change map `f^* 𝓗om(M, 𝒪_Y) ⟶ 𝓗om(f^* M, 𝒪_X)` of linear functionals, the
internal-Hom comparison at the structure sheaf followed by `f^* 𝒪_Y ≅ 𝒪_X`, is compatible with
composites: along `f ≫ g` it is the pullback along `f` of the map along `g` followed by the map
along `f`, through the composition isomorphism of pullback. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.Scheme.Hom.pullbackIhomComparison_app_unit_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullbackComp f g).inv.app ((ihom M).obj (𝟙_ Z.Modules)) ≫
        (Scheme.Modules.pullback f).map ((pullbackIhomComparison M g).app (𝟙_ Z.Modules) ≫
          (ihom ((Scheme.Modules.pullback g).obj M)).map
            (Scheme.Modules.pullbackObjUnitIso g).hom) ≫
        (pullbackIhomComparison ((Scheme.Modules.pullback g).obj M) f).app (𝟙_ Y.Modules) ≫
        (ihom ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))).map
          (Scheme.Modules.pullbackObjUnitIso f).hom =
      (pullbackIhomComparison M (f ≫ g)).app (𝟙_ Z.Modules) ≫
        (ihom ((Scheme.Modules.pullback (f ≫ g)).obj M)).map
          (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).hom ≫
        (pre ((Scheme.Modules.pullbackComp f g).hom.app M)).app (𝟙_ X.Modules) := by
  have hn := (pullbackIhomComparison ((Scheme.Modules.pullback g).obj M) f).naturality
    (Scheme.Modules.pullbackObjUnitIso g).hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  have hu : (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackObjUnitIso g).hom ≫
      (Scheme.Modules.pullbackObjUnitIso f).hom =
        (Scheme.Modules.pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫
          (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).hom := by
    rw [← Scheme.Modules.pullbackObjUnitIso_comp, Iso.hom_inv_id_app_assoc]
  -- Move the structure-sheaf comparison along `g` past the comparison along `f`, combine the two
  -- structure-sheaf comparisons, and apply the coherence `pullbackIhomComparison_comp`.
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn]
  simp only [← Functor.map_comp, hu]
  simp only [Functor.map_comp]
  rw [pullbackIhomComparison_comp_assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (_ ≫ ·) ((pre _).naturality _).symm

/-- The base-change map of linear functionals is unchanged, up to the canonical identifications,
when the scheme morphism is replaced by an equal one. -/
@[reassoc]
theorem pullbackIhomComparison_app_unit_congr {f f' : X ⟶ Y} (h : f = f') (M : Y.Modules)
    [M.IsQuasicoherent] :
    (pullbackIhomComparison M f').app (𝟙_ Y.Modules) ≫
        (ihom ((Scheme.Modules.pullback f').obj M)).map
          (Scheme.Modules.pullbackObjUnitIso f').hom ≫
        (pre ((Scheme.Modules.pullbackCongr h).hom.app M)).app (𝟙_ X.Modules) =
      (Scheme.Modules.pullbackCongr h).inv.app ((ihom M).obj (𝟙_ Y.Modules)) ≫
        (pullbackIhomComparison M f).app (𝟙_ Y.Modules) ≫
        (ihom ((Scheme.Modules.pullback f).obj M)).map
          (Scheme.Modules.pullbackObjUnitIso f).hom := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- **Evaluation at a section commutes with pullback.** For a global section `s : 𝒪_Y ⟶ M`, the
pullback along `f` of evaluation `𝓗om(M, 𝒪_Y) ⟶ 𝒪_Y` at `s`, followed by `f^* 𝒪_Y ≅ 𝒪_X`, is the
base-change map `f^* 𝓗om(M, 𝒪_Y) ⟶ 𝓗om(f^* M, 𝒪_X)` followed by evaluation at the pulled-back
section `𝒪_X ≅ f^* 𝒪_Y ⟶ f^* M`. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.Scheme.Hom.pullback_map_evaluation_comp_pullbackObjUnitIso_hom
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] (s : 𝟙_ Y.Modules ⟶ M) :
    (Scheme.Modules.pullback f).map ((λ_ _).inv ≫ s ▷ (ihom M).obj (𝟙_ Y.Modules) ≫
        (ihom.ev M).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullbackObjUnitIso f).hom =
      (pullbackIhomComparison M f).app (𝟙_ Y.Modules) ≫
        (ihom ((Scheme.Modules.pullback f).obj M)).map (Scheme.Modules.pullbackObjUnitIso f).hom ≫
        (λ_ _).inv ≫
        ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) ▷
          (ihom ((Scheme.Modules.pullback f).obj M)).obj (𝟙_ X.Modules) ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj M)).app (𝟙_ X.Modules) := by
  -- Move the base-change map past the section and evaluate, using the characterization
  -- `whiskerLeft_pullbackIhomComparison_app_comp_ev` of the comparison by evaluation.
  rw [leftUnitor_inv_naturality_assoc, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc, ihom.ev_naturality,
    whiskerLeft_pullbackIhomComparison_app_comp_ev_assoc]
  dsimp only [Functor.comp_obj]
  -- Oplax left unitality of pullback, whose unit comparison is `f^* 𝒪_Y ≅ 𝒪_X`, and naturality
  -- of the tensor comparison in the section reduce both sides to the same pulled-back composite.
  rw [left_unitality (Scheme.Modules.pullback f), Scheme.Modules.pullback_η]
  simp only [comp_whiskerRight, Category.assoc, hom_inv_whiskerRight_assoc, δ_natural_left_assoc,
    IsIso.hom_inv_id_assoc, Functor.map_comp]

end Unit

end

end TauCeti.AlgebraicGeometry
