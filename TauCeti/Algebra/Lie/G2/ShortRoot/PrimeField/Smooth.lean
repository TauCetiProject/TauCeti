/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Carrier
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.PerfectField
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smoothness of the prime-field short-root G₂ carrier

The short-root type-`G₂` carrier over `𝔽₃` is smooth. The coordinate algebras of its four
numbered root subgroups and rank-two weight torus are reduced. Over the perfect ground field
`𝔽₃`, the common-kernel quotient they generate is therefore smooth. This concerns the actual
prime-field carrier, so its scalar extensions are smooth as well.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.4.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

-- The argument follows `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Smooth`, using
-- `smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_perfectField`.
/-- The coordinate algebra of the short-root type-`G₂` carrier over `𝔽₃` is smooth. -/
instance algebraSmooth_carrierAlgebra : Algebra.Smooth (ZMod 3) carrierAlgebra := by
  let : ∀ j, IsReduced (generatorCodomain j) := by
    intro j
    cases j with
    | inl _ => exact AdditiveGroup.isReduced_coordinateHopfAlgebra (ZMod 3)
    | inr _ => exact inferInstance
  exact (smoothCommHopfAlgProperty_iff _).mp
    (CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal_of_perfectField
      generator)

/-- The structural morphism of the prime-field short-root type-`G₂` carrier is smooth. -/
instance smooth_groupScheme : Smooth groupScheme.X.hom := by
  rw [groupScheme_eq_commonKernelSpec]
  exact (smoothAffineGroupSchemeProperty_iff _ _).mp
    ((algebraSmooth_iff_smooth_hopfSpec (ZMod 3) _).mp
      ((smoothCommHopfAlgProperty_iff _).mpr algebraSmooth_carrierAlgebra))

end TauCeti.G2ShortRoot.PrimeField
