/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Carrier
import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Raising

/-!
# Weight characters and positive root actions in the E7 minuscule representation

The 56 basis vectors have distinct integral torus characters. A positive simple root element
at parameter one sends a basis vector of simple weight minus one to its sum with the reflected
basis vector. These identities apply to both the integral carrier and the field-generated carrier.
-/

public section

open WithConv
open scoped Matrix

namespace TauCeti.E7Minuscule

/-- The character of the weight torus corresponding to a minuscule-basis index. -/
noncomputable abbrev minusculeCharacter (a : Fin 56) :
    Multiplicative (Fin 7 →₀ ℤ) :=
  SplitTorus.weightCharacter (DynkinType.e7MinusculeWeight a)

/-- Distinct minuscule basis vectors have distinct integral torus characters. -/
theorem minusculeCharacter_injective : Function.Injective minusculeCharacter := by
  intro a b h
  apply DynkinType.e7MinusculeWeight_injective
  funext i
  simpa only [minusculeCharacter, SplitTorus.toAdd_weightCharacter] using
    congrArg (fun χ : Multiplicative (Fin 7 →₀ ℤ) ↦ Multiplicative.toAdd χ i) h

/-- Subtracting a basis vector from its positive simple root translate at parameter one
leaves the reflected basis vector when its simple weight is minus one. -/
theorem positiveRoot_mulVec_single_sub (k : Type*) [CommRing k] (i : Fin 7) (a : Fin 56)
    (ha : DynkinType.e7MinusculeWeight a i = -1) :
    (((rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (DynkinType.e7MinusculeReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, one_smul]
  simpa only [weightTable_raisingMatrix, weightTable_reflection] using
    weightTable.one_add_raisingMatrix_mulVec_single_sub (R := k) i a
      (by simpa only [weightTable_weight] using ha)

end TauCeti.E7Minuscule
