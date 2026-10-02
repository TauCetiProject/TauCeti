/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.CommonKernel.Reduced
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange

/-!
# Smoothness of the generated short-root type-G2 subgroup after scalar extension

After extending the coordinate maps of the four numbered root subgroups and the rank-two weight
torus of the short-root type-`G₂` carrier over `𝔽₃` to an algebraically closed characteristic-three
field, their common-kernel quotient is reduced and hence smooth.

## Main declarations

In the namespace `TauCeti.G2ShortRoot.PrimeField`:

* `isReduced_generatedCoordinateHopfAlgebra` and
  `smoothCommHopfAlgProperty_generatedCoordinateHopfAlgebra`: reducedness and smoothness over an
  algebraically closed field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26–27.
* J. S. Milne, *Algebraic Groups* (2017), §2.h.

The interface follows the generated-subgroup smoothness construction for the type-`E₇`
minuscule carrier in `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Smooth`.
-/

public section

open CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

universe u

variable (k : Type u) [Field k] [Algebra (ZMod 3) k]

private theorem isReduced_baseChangeGeneratorCodomain :
    ∀ j, IsReduced (baseChangeGeneratorCodomain k j) := by
  rintro (j | u)
  · let e := AdditiveGroup.coordinateHopfAlgebraBaseChangeIso (ZMod 3) k
    exact isReduced_of_injective e.hom.hom.toAlgHom.toRingHom
      (ConcreteCategory.bijective_of_isIso e.hom).1
  · rcases u with ⟨⟩
    let e := DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso
      (ZMod 3) k (SplitTorus.characterGroup (Fin 2))
    exact isReduced_of_injective e.hom.hom.toAlgHom.toRingHom
      (ConcreteCategory.bijective_of_isIso e.hom).1

/-- The subgroup generated after scalar extension has reduced coordinate algebra over an
algebraically closed field. -/
theorem isReduced_generatedCoordinateHopfAlgebra [IsAlgClosed k] :
    IsReduced (generatedCoordinateHopfAlgebra k) := by
  let : ∀ j, IsReduced (baseChangeGeneratorCodomain k j) :=
    isReduced_baseChangeGeneratorCodomain k
  rw [generatedCoordinateHopfAlgebra_def, generatedDefiningIdeal_def]
  exact CommHopfAlgCat.isReduced_quotient_commonKernelHopfIdeal (baseChangeGenerator k)

/-- The subgroup generated after scalar extension is smooth over an algebraically closed field. -/
theorem smoothCommHopfAlgProperty_generatedCoordinateHopfAlgebra [IsAlgClosed k] :
    smoothCommHopfAlgProperty k (generatedCoordinateHopfAlgebra k) := by
  let : ∀ j, IsReduced (baseChangeGeneratorCodomain k j) :=
    isReduced_baseChangeGeneratorCodomain k
  rw [generatedCoordinateHopfAlgebra_def, generatedDefiningIdeal_def]
  exact CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_commonKernelHopfIdeal
    (baseChangeGenerator k)

end TauCeti.G2ShortRoot.PrimeField
