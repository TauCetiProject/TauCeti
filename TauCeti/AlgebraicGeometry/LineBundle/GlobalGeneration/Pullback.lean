/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback

/-!
# Global generation under pullback

The pullback `f^* L` of a globally generated line bundle `L` along any morphism of schemes `f`
is globally generated. The result applies to the bundled `InvertibleSheaf.pullback` functor,
so globally generated line bundles can be transported to any scheme over their base.

## Main results

* `TauCeti.AlgebraicGeometry.InvertibleSheaf.IsGloballyGenerated.pullback`: pullbacks of globally
  generated line bundles are globally generated.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 7.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X Y : Scheme.{u}}

/-- The pullback of a globally generated line bundle along any morphism of schemes is globally
generated. -/
theorem IsGloballyGenerated.pullback {L : InvertibleSheaf Y} (hL : L.IsGloballyGenerated)
    (f : X ⟶ Y) : ((InvertibleSheaf.pullback f).obj L).IsGloballyGenerated := by
  obtain ⟨σ⟩ := isGloballyGenerated_iff_nonempty_generatingSections.mp hL
  -- The functor is rebound with its type as a functor between categories of sheaves of modules,
  -- where `SheafOfModules.GeneratingSections.map` seeks its colimit-preservation instance.
  let F : SheafOfModules Y.ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.pullback f
  have : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  exact isGloballyGenerated_iff_nonempty_generatingSections.mpr
    ⟨σ.map F (Scheme.Modules.pullbackObjUnitIso f).symm⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf
