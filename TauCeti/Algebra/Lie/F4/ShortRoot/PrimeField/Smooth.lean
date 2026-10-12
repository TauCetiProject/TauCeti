/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Carrier
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.PerfectField
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smoothness of the prime-field short-root F₄ carrier

The short-root type-`F₄` carrier over `𝔽₂` is smooth. Its eight numbered root subgroups
and rank-four weight torus have reduced coordinate rings. Over the finite ground field,
the common-kernel quotient they generate is therefore smooth. Consequently the scalar
extension of this same prime-field carrier is smooth over every commutative `𝔽₂`-algebra.

This proves smoothness of the actual prime-field carrier and its scalar extensions.
It does not require identifying those scalar extensions with the subgroups generated
after extension, and makes no assertion of reductivity or pinned-group recognition.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.F4ShortRoot.PrimeField

/-- The coordinate Hopf algebra of the short-root type-`F₄` carrier over `𝔽₂` is smooth. -/
instance algebraSmooth_quotient :
    Algebra.Smooth (ZMod 2)
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
        definingIdeal) := by
  let : ∀ j, IsReduced (generatorCodomain j) := by
    intro j
    cases j with
    | inl _ => exact AdditiveGroup.isReduced_coordinateHopfAlgebra (ZMod 2)
    | inr _ => exact inferInstance
  rw [definingIdeal_def]
  exact (smoothCommHopfAlgProperty_iff _).mp
    (CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_perfectField
      generator)

/-- The structural morphism of the prime-field short-root type-`F₄` carrier is smooth. -/
instance smooth_groupScheme : Smooth groupScheme.X.hom := by
  rw [groupScheme_def]
  exact (smoothAffineGroupSchemeProperty_iff _ _).mp
    ((algebraSmooth_iff_smooth_hopfSpec (ZMod 2) _).mp
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))

end TauCeti.F4ShortRoot.PrimeField
