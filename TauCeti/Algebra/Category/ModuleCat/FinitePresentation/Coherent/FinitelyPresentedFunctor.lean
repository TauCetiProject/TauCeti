/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Coherent.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.WeakKernels

/-!
# Six-way coherence characterization via finitely presented functors

By Chase's theorem and the Freyd-Auslander criterion, the following six properties of a ring `R`
are equivalent (`TauCeti.isCoherentRing_tfae`):

* `R` is left coherent (`TauCeti.IsCoherentRing R`);
* `TauCeti.finitePresentationModules R` is closed under kernels in `ModuleCat R`;
* `(TauCeti.finitePresentationModules R).FullSubcategory` is abelian;
* `(TauCeti.finitePresentationModules R).FullSubcategory` has kernels;
* `proj R` (`(TauCeti.finiteProjectiveModules R).FullSubcategory`) has weak kernels;
* `mod (proj R)`
  (`TauCeti.isFinitelyPresentedFunctor (TauCeti.finiteProjectiveModules R).FullSubcategory`)
  is closed under kernels in the functor category.

## Main results

* `TauCeti.isCoherentRing_tfae`: the six-way equivalence.

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), 457–473.
* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer (1966), 189–231.
* [The Stacks Project, Section 10.90, Tag 05CU](https://stacks.math.columbia.edu/tag/05CU).
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti

variable (R : Type u) [Ring R]

/-- **Chase's coherence theorem and categorical characterizations of left coherence.** For any ring
`R`, the following are equivalent:
1. `R` is left coherent (`TauCeti.IsCoherentRing R`);
2. `TauCeti.finitePresentationModules R` is closed under kernels in `ModuleCat R`;
3. `(TauCeti.finitePresentationModules R).FullSubcategory` is an abelian category;
4. `(TauCeti.finitePresentationModules R).FullSubcategory` has kernels;
5. `(TauCeti.finiteProjectiveModules R).FullSubcategory` (`proj R`) has weak kernels;
6. `TauCeti.isFinitelyPresentedFunctor (TauCeti.finiteProjectiveModules R).FullSubcategory`
   (`mod (proj R)`) is closed under kernels in the functor category. -/
theorem isCoherentRing_tfae :
    List.TFAE
      [IsCoherentRing R,
        (finitePresentationModules R).IsClosedUnderKernels,
        Nonempty (Abelian (finitePresentationModules R).FullSubcategory),
        HasKernels (finitePresentationModules R).FullSubcategory,
        HasWeakKernels (finiteProjectiveModules R).FullSubcategory,
        (isFinitelyPresentedFunctor
          (finiteProjectiveModules R).FullSubcategory).IsClosedUnderKernels] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ ⟨inferInstance⟩
  tfae_have 3 → 4 := fun ⟨_⟩ ↦ inferInstance
  tfae_have 4 → 5 := fun _ ↦ hasWeakKernels_finiteProjectiveModules_of_hasKernels R
  tfae_have 5 → 6 := fun _ ↦
    have : HasBinaryBiproducts (finiteProjectiveModules R).FullSubcategory := .of_hasBinaryProducts
    inferInstance
  tfae_have 6 → 5 := fun _ ↦ hasWeakKernels_of_isClosedUnderKernels
  tfae_have 5 → 1 := fun _ ↦ isCoherentRing_of_hasWeakKernels_finiteProjectiveModules R
  tfae_finish

end TauCeti
