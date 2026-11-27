/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Takeuchi.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteType
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants

/-!
# The Takeuchi correspondence for geometrically reduced groups

For a geometrically reduced commutative Hopf algebra `H` of finite type over a field, the
Takeuchi Galois connection `TauCeti.CommHopfAlgCat.gc_kernelHopfIdeal_coinvariants` between Hopf
subalgebras and normal Hopf ideals is an order isomorphism. Geometrically, normal closed
subgroups of a geometrically reduced affine group of finite type correspond to its quotients.

The two identities behind it are the following.
* For a normal Hopf ideal `I`, the kernel Hopf ideal of the inclusion of the coinvariants
  `H^{co H/I}` is `I`: this is `TauCeti.CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq`.
* For a Hopf subalgebra `B`, the coinvariants of `H·B⁺` are `B`. A Hopf subalgebra of a
  geometrically reduced Hopf algebra of finite type is again geometrically reduced and of finite
  type, so `H` is faithfully flat over it, and faithfully flat descent identifies the
  coinvariants of the kernel with `B`.

Over a general field, without geometric reducedness, both identities still hold (Takeuchi 1972,
Theorem 4.3), but need the quotient by a normal subgroup of a nonreduced group and faithful
flatness over every Hopf subalgebra.

## Main declarations

* `TauCeti.CommHopfAlgCat.coinvariants_kernelHopfIdeal_hopfSubalgebraι_of_isGeometricallyReduced`:
  a Hopf subalgebra is the algebra of coinvariants of the Hopf ideal it generates.
* `TauCeti.CommHopfAlgCat.HopfSubalgebra.coinvariants_kernelHopfIdeal` and
  `TauCeti.CommHopfAlgCat.NormalHopfIdeal.kernelHopfIdeal_coinvariants`: the two round trips.
* `TauCeti.CommHopfAlgCat.HopfSubalgebra.orderIsoNormalHopfIdeal`: `B ↦ H·B⁺` as an order
  isomorphism from Hopf subalgebras onto normal Hopf ideals.

## References

* M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*, Manuscripta Math.
  **7** (1972), 251–270, Theorem 4.3.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]

/-- **Takeuchi correspondence, subalgebra side, geometrically reduced case.** A Hopf subalgebra
`B` of a geometrically reduced commutative Hopf algebra `H` of finite type over a field is the
algebra of right coinvariants of the Hopf ideal `H·B⁺` it generates. -/
@[simp]
theorem coinvariants_kernelHopfIdeal_hopfSubalgebraι_of_isGeometricallyReduced
    {B : Subalgebra k H} (hB : B.IsHopfSubalgebra) :
    (kernelHopfIdeal (hopfSubalgebraι hB)).coinvariants = B := by
  have hinj := hopfSubalgebraι_injective hB
  have : Algebra.FiniteType k (ofHopfSubalgebra hB) :=
    _root_.CommHopfAlgCat.finiteType_of_injective _ hinj
  have : Algebra.IsGeometricallyReduced k (ofHopfSubalgebra hB) :=
    Algebra.IsGeometricallyReduced.of_injective (hopfSubalgebraι hB).hom.toAlgHom hinj
  rw [coinvariants_kernelHopfIdeal_eq_range _
    ((faithfullyFlat_iff_injective_of_isGeometricallyReduced _).mpr hinj), range_hopfSubalgebraι]

/-- A Hopf subalgebra is recovered from the normal Hopf ideal it generates. -/
@[simp]
theorem HopfSubalgebra.coinvariants_kernelHopfIdeal (B : HopfSubalgebra H) :
    B.kernelHopfIdeal.coinvariants = B :=
  Subtype.ext <| by
    rw [NormalHopfIdeal.coe_coinvariants, HopfSubalgebra.coe_kernelHopfIdeal,
      coinvariants_kernelHopfIdeal_hopfSubalgebraι_of_isGeometricallyReduced]

/-- A normal Hopf ideal is recovered from its Hopf subalgebra of coinvariants. -/
@[simp]
theorem NormalHopfIdeal.kernelHopfIdeal_coinvariants (I : NormalHopfIdeal H) :
    I.coinvariants.kernelHopfIdeal = I :=
  Subtype.ext <| by
    rw [NormalHopfIdeal.coe_kernelHopfIdeal_coinvariants, kernelHopfIdeal_coinvariantsι_eq]

/-- **The Takeuchi correspondence, geometrically reduced case.** For a geometrically reduced
commutative Hopf algebra `H` of finite type over a field, `B ↦ H·B⁺` is an order isomorphism from
Hopf subalgebras onto normal Hopf ideals, with inverse `I ↦ H^{co H/I}`. -/
noncomputable def HopfSubalgebra.orderIsoNormalHopfIdeal : HopfSubalgebra H ≃o NormalHopfIdeal H
    where
  toFun := kernelHopfIdeal
  invFun := NormalHopfIdeal.coinvariants
  left_inv := HopfSubalgebra.coinvariants_kernelHopfIdeal
  right_inv := NormalHopfIdeal.kernelHopfIdeal_coinvariants
  map_rel_iff' {B B'} := by
    rw [Equiv.coe_fn_mk, gc_kernelHopfIdeal_coinvariants,
      ← Subtype.coe_le_coe, ← Subtype.coe_le_coe, NormalHopfIdeal.coe_coinvariants,
      HopfSubalgebra.coe_kernelHopfIdeal,
      coinvariants_kernelHopfIdeal_hopfSubalgebraι_of_isGeometricallyReduced]

@[simp]
theorem HopfSubalgebra.orderIsoNormalHopfIdeal_apply (B : HopfSubalgebra H) :
    orderIsoNormalHopfIdeal B = B.kernelHopfIdeal :=
  (rfl)

@[simp]
theorem HopfSubalgebra.orderIsoNormalHopfIdeal_symm_apply (I : NormalHopfIdeal H) :
    orderIsoNormalHopfIdeal.symm I = I.coinvariants :=
  (rfl)

end TauCeti.CommHopfAlgCat
