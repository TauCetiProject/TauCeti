/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Torsor
public import TauCeti.CategoryTheory.Monoidal.Grp.Kernel

/-!
# The kernel of the fppf quotient projection

For a normal closed subgroup `N = Spec (H / I)` of `G = Spec H`, the sequence
`1 ⟶ N ⟶ G ⟶ G/N ⟶ 1` is exact as a sequence of fppf group sheaves:
the subgroup inclusion is the categorical kernel of the quotient projection, and
the projection is locally surjective by `isLocallySurjective_fppfQuotientProjection`.

The kernel universal property supplies unique factorizations of group-sheaf morphisms
annihilated by the quotient projection. It needs neither representability of `G/N`
nor smoothness, finiteness, or field assumptions.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §5.
-/

public section

open CategoryTheory Limits

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]
variable (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal)

/-- The inclusion of a normal closed subgroup followed by the fppf quotient
projection is the trivial group-sheaf morphism. -/
@[reassoc (attr := simp)]
theorem quotientSubgroupPointsFppfGrpInclusion_comp_fppfQuotientProjection :
    quotientSubgroupPointsFppfGrpInclusion H I ≫ fppfQuotientProjection H I hI = 0 := by
  apply Grp.comp_eq_zero_of_commSq
  simpa only [fppfQuotientTorsorAction_def] using
    (isPullback_fppfQuotientTorsor H I hI).toCommSq

/-- The original closed subgroup is the categorical kernel of the fppf quotient
projection, as a group object in fppf sheaves. -/
noncomputable def isLimitFppfQuotientKernel :
    IsLimit (KernelFork.ofι (quotientSubgroupPointsFppfGrpInclusion H I)
      (quotientSubgroupPointsFppfGrpInclusion_comp_fppfQuotientProjection H I hI)) := by
  apply Grp.isLimitKernelForkOfIsPullback
  simpa only [fppfQuotientTorsorAction_def] using isPullback_fppfQuotientTorsor H I hI

end TauCeti.CommHopfAlgCat
