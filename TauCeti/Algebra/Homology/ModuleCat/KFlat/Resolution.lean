/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Unbounded K-flat resolutions of module complexes

Every cochain complex of modules over a commutative ring, without any boundedness assumption,
receives a quasi-isomorphism from a K-flat complex. Such a resolution computes the derived tensor
product of unbounded complexes of modules. This is the case of
`CochainComplex.exists_quasiIso_isKFlat` in which every module is covered by the free module
on its elements.

The native functorial cellular resolution with the free-forgetful counit is K-flat as well
(`CochainComplex.isKFlat_kFlatResolutionFunctor_obj`), so its natural augmentation can be
used without making nonfunctorial choices of covers.

## References

* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
-/

public section

open CategoryTheory Limits

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Tensoring with the free module on the elements of a module preserves finite limits.
This instance exposes the free object through composition of the forgetful and free functors. -/
instance preservesFiniteLimits_tensorLeft_forget_comp_free_obj (X : ModuleCat.{u} R) :
    PreservesFiniteLimits (MonoidalCategory.tensorLeft
      ((CategoryTheory.forget (ModuleCat.{u} R) ⋙ ModuleCat.free R).obj X)) := by
  dsimp only [Functor.comp_obj]
  infer_instance

end ModuleCat

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Every possibly unbounded complex of modules over a commutative ring admits a
quasi-isomorphism from a K-flat complex. -/
theorem exists_quasiIso_isKFlat_moduleCat (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (π : P ⟶ K), QuasiIso π ∧ P.IsKFlat := by
  -- sequential colimits of modules are exact, also for the small index category `ℕ`
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  refine K.exists_quasiIso_isKFlat fun X ↦ ⟨ModuleCat.of R (X →₀ R),
    ModuleCat.ofHom (Finsupp.linearCombination R id), ?_, inferInstance, inferInstance⟩
  rw [ModuleCat.epi_iff_surjective]
  exact Finsupp.linearCombination_id_surjective R X

end CochainComplex
