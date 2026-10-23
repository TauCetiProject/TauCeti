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
choosing new comparison maps. The source is quasicoherent and the target is arbitrary; neither
flatness nor invertibility of the internal-Hom comparison is assumed.

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

end

end TauCeti.AlgebraicGeometry
