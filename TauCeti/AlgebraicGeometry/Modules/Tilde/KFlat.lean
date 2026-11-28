/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Resolution
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.KFlat
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Free K-flat resolutions on an affine scheme

The functorial cellular resolution `CochainComplex.kFlatResolutionFunctor`, applied to
`forget ⋙ ModuleCat.free` and the counit of `ModuleCat.adj`, resolves every unbounded complex
of modules by a K-flat complex whose degreewise associated sheaf is also K-flat.
Its augmentation remains a quasi-isomorphism after applying `tilde.functor`.
Thus the same functorial resolution can compute derived tensor products both over a ring
and over the structure sheaf of its spectrum.

The free cells become free module sheaves by `AlgebraicGeometry.tildeFinsupp`. K-flatness of
the mapped resolution follows from `CategoryTheory.Functor.isKFlat_map_kFlatResolution`, which uses
zero-differential complexes, mapping cones and the sequential colimit of the cellular stages.
All constructions and naturality laws are those of the native resolution functor and its
natural augmentation `CochainComplex.kFlatResolutionNatTrans`.

## References

* The Stacks Project, Lemma 36.3.9 (Tag 08DX).
* The Stacks Project, Cohomology on Sites, Section 21.17, Flat resolutions.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CochainComplex

universe u

namespace TauCeti.AlgebraicGeometry

variable (R : CommRingCat.{u})

/-- The associated sheaf of an arbitrarily generated free module is flat. -/
instance preservesFiniteLimits_tensorLeft_tilde_free (I : Type u) :
    PreservesFiniteLimits
      (tensorLeft ((tilde.functor R).obj ((ModuleCat.free R).obj I))) := by
  have : PreservesFiniteLimits
      (tensorLeft (C := (Spec R).Modules) (_root_.SheafOfModules.free I)) :=
    _root_.SheafOfModules.preservesFiniteLimits_tensorLeft_free (R := (Spec R).sheaf) I
  exact preservesFiniteLimits_of_natIso
    ((curriedTensor (Spec R).Modules).mapIso (tildeFinsupp I).symm)

/-- The degreewise associated sheaf of the native free cellular resolution is K-flat,
without any boundedness assumption on the input complex. -/
instance isKFlat_tilde_map_kFlatResolutionFunctor_obj
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsKFlat (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
      ((kFlatResolutionFunctor
        (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit).obj K)) := by
  -- `Scheme.Modules` has its own category instance, so apply the site-level instance explicitly.
  have : AB5OfSize.{0, 0} (Spec R).Modules :=
    _root_.SheafOfModules.instAB5OfSizeSmall _
  have (X : ModuleCat.{u} R) : PreservesFiniteLimits (tensorLeft
      ((tilde.functor R).obj ((forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X))) :=
    preservesFiniteLimits_tensorLeft_tilde_free R X
  rw [kFlatResolutionFunctor_obj]
  exact (tilde.functor R).isKFlat_map_kFlatResolution _ _ K

end TauCeti.AlgebraicGeometry
