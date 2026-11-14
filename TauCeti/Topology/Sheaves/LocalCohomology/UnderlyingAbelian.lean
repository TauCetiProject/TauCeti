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

If the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules vanishes, every class in `H_Sⁿ(W, F)`
vanishes locally, so the local cohomology sheaf of the underlying abelian sheaf vanishes too
(`CategoryTheory.Sheaf.isZero_supportedHSheaf_of_isZero_supportedModuleHSheaf`). This lets
vanishing hypotheses stated for module coefficients feed the abelian-group API of
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

/-- If the local cohomology sheaf `𝓗_Sⁿ(F)` of `R`-modules vanishes, so does the local cohomology
sheaf `𝓗_Sⁿ` of the underlying abelian sheaf of `F`. -/
theorem isZero_supportedHSheaf_of_isZero_supportedModuleHSheaf {n : ℕ}
    (h : IsZero (F.supportedModuleHSheaf S n)) :
    IsZero (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).supportedHSheaf
      S n) := by
  refine (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff _).2 fun x W c hx ↦ ?_
  -- `c` is the image of a module-valued class, which vanishes locally
  obtain ⟨c, rfl⟩ := (F.supportedModuleHAddEquiv S W n).surjective c
  obtain ⟨V, hVW, hxV, hV⟩ :=
    F.exists_supportedModuleHPresheaf_map_eq_zero_of_isZero_supportedModuleHSheaf S h c hx
  exact ⟨V, hVW, hxV,
    (F.supportedModuleHAddEquiv_supportedModuleHPresheaf_map S (homOfLE hVW).op c).symm.trans
      ((congrArg _ hV).trans (map_zero _))⟩

end

end CategoryTheory.Sheaf
