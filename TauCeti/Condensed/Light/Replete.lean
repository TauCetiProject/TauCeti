/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.SequentialLimit
public import Mathlib.Condensed.Light.Epi
public import TauCeti.CategoryTheory.Limits.Replete

/-!
# Light condensed sets and modules are replete

Sequential limits of epimorphisms of light condensed sets, and of light condensed modules, are
epimorphisms. In the language of `TauCeti.IsReplete`, these categories are replete. Unlike the
category of types, epimorphisms here are only locally surjective, so this is a genuine statement
about the topos of sheaves on light profinite sets: it rests on Mathlib's theorems
`CategoryTheory.coherentTopology.epi_π_app_zero_of_epi` and
`LightCondensed.epi_π_app_zero_of_epi`, which reduce it to the fact that a sequential limit of
surjections of light profinite sets is surjective.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Definition 3.1.1, for repleteness.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti

/-- The category of light condensed sets is replete. -/
instance isReplete_lightCondSet : IsReplete LightCondSet.{u} where
  epi_π_app_zero hF _ hc := coherentTopology.epi_π_app_zero_of_epi (C := LightProfinite.{u})
    (fun G hG ↦ (LightProfinite.effectiveEpi_iff_surjective _).2 <|
      Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit G)
        fun n ↦ (LightProfinite.effectiveEpi_iff_surjective _).1 (hG n)) hc hF

/-- The category of light condensed modules over a ring is replete. -/
instance isReplete_lightCondMod (R : Type u) [Ring R] : IsReplete (LightCondMod.{u} R) where
  epi_π_app_zero hF _ hc := LightCondensed.epi_π_app_zero_of_epi R hc hF

end TauCeti
