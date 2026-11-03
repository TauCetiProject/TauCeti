/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.WeightTorus
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer

/-!
# Schematic weight blocks in the short-root F₄ torus centralizer

Over every commutative `𝔽₂`-algebra, schematic centralization of the short-root carrier's
weight torus is equivalent to the vanishing of matrix entries between distinct integral
weights. Testing the universal torus point separates those weights even over finite fields
and nonreduced value algebras, where rational torus points alone need not separate them.

The representation has a two-dimensional zero-weight space. The criterion retains that
block: it does not identify the centralizer with the weight torus. Controlling that block
and recognizing the full torus centralizer requires the carrier's additional equations.
This supplies the schematic character-separation step in recognition of its chosen torus;
no identification with an independently pinned group is asserted.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* The closed-immersion transport follows
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`; the weight-block argument
  uses `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer`.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

universe v

local notation "GLCoord" => GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26
local notation "Q" => CommHopfAlgCat.quotient GLCoord
  (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- Schematic centralization of the short-root F₄ weight torus is exactly preservation of
its weight blocks, over every commutative value algebra, including nonreduced algebras. -/
@[simp↓]
theorem mem_centralizerPointsSubgroup_iff_apply_eq_zero
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (g : HopfAlgebra.points (R := ZMod 2) (H := Q) (CommAlgCat.of (ZMod 2) A)) :
    g ∈ BialgHom.centralizerPointsSubgroup weightTorusRestriction.hom
        (CommAlgCat.of (ZMod 2) A) ↔
      ∀ i j, f4ShortRootWeight i ≠ f4ShortRootWeight j →
        ((coordinatePointsEquiv A g : GL (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) i j = 0 := by
  have hcomp : weightTorusRestriction.hom.comp
        (CommHopfAlgCat.mkQuotient GLCoord (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ZMod 2) f4ShortRootWeight := by
    rw [← CommHopfAlgCat.hom_comp, weightTorusRestriction,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have h := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (CommHopfAlgCat.mkQuotient GLCoord (CommHopfAlgCat.commonKernelHopfIdeal generator)).hom
    (CommHopfAlgCat.mkQuotient_surjective _ _) weightTorusRestriction.hom g
  rw [hcomp, GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_apply_eq_zero] at h
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    coe_coordinatePointsEquiv]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal,
    BialgHom.mapDomain_apply] using h.symm

end TauCeti.F4ShortRoot.PrimeField
