/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.Basic
public import TauCeti.Topology.Sheaves.LocalCohomology.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.UnderlyingAbelian

/-!
# Local cohomology sheaves of modules and of the underlying abelian sheaf

Let `F` be a sheaf of `R`-modules on a topological space `X` and `S` a closed subset. The
cohomology `H_Sⁿ(W, F)` with supports in `S`, computed with module coefficients, agrees with the
cohomology with supports of the underlying abelian sheaf of `F`, compatibly with restriction
(`CategoryTheory.Sheaf.supportedModuleHPresheafForgetIso`).

Since this comparison is bijective and compatible with restriction, a class in `H_Sⁿ(W, F)`
vanishes locally for module coefficients exactly when it does for the underlying abelian sheaf.
Hence the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules vanishes if and only if the local
cohomology sheaf of the underlying abelian sheaf does
(`CategoryTheory.Sheaf.isZero_supportedHSheaf_iff_isZero_supportedModuleHSheaf`). This lets
vanishing hypotheses pass between module coefficients and the abelian-group API of
`TauCeti.Topology.Sheaves.LocalCohomology.Basic`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (S : Closeds X)

noncomputable section

/-- The local cohomology sheaf `𝓗_Sⁿ` of the underlying abelian sheaf of `F` vanishes if and only
if the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules does. -/
theorem isZero_supportedHSheaf_iff_isZero_supportedModuleHSheaf {n : ℕ} :
    IsZero (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedHSheaf
      S n) ↔ IsZero (F.supportedModuleHSheaf S n) := by
  constructor
  · refine fun h ↦ (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff_moduleCat _).2
      fun x W c hx ↦ ?_
    -- the underlying abelian class of `c` vanishes locally, and the comparison is injective
    obtain ⟨V, hVW, hxV, hV⟩ :=
      exists_supportedHRestrict_eq_zero_of_isZero_supportedHSheaf _ S h
        (F.supportedModuleHAddEquiv S W n c) hx
    exact ⟨V, hVW, hxV, (F.supportedModuleHAddEquiv S V n).injective
      ((F.supportedModuleHAddEquiv_supportedModuleHPresheaf_map S (homOfLE hVW).op c).trans
        (hV.trans (map_zero _).symm))⟩
  · refine fun h ↦ (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff _).2 fun x W c hx ↦ ?_
    -- `c` is the image of a module-valued class, which vanishes locally
    obtain ⟨c, rfl⟩ := (F.supportedModuleHAddEquiv S W n).surjective c
    obtain ⟨V, hVW, hxV, hV⟩ :=
      F.exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf S h c hx
    exact ⟨V, hVW, hxV,
      (F.supportedModuleHAddEquiv_supportedModuleHPresheaf_map S (homOfLE hVW).op c).symm.trans
        ((congrArg _ hV).trans (map_zero _))⟩

end

end CategoryTheory.Sheaf
