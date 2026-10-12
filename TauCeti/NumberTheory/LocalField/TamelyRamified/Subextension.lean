/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic

/-!
# The maximal tamely ramified subextension

For a finite Galois subextension `L/K` of the algebraic closure of a nonarchimedean local
field, its maximal tamely ramified subextension is `Kᵗ ⊓ L`, where `Kᵗ` is the canonical
maximal tamely ramified extension. This field is the fixed field of the first lower
ramification group `G₁(L/K)`. Its degree over `K` is `[L : K] / p ^ (v_p e(L/K))`, where `p`
is the residue characteristic. These statements accept any compatible local-field structures
on `L`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel TauCeti TauCeti.LocalFieldsRamification

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- The degree over the base of the field fixed by wild inertia is
`[L : K] / p ^ (v_p e(L/K))`. -/
theorem finrank_fixedField_lowerRamificationGroup_one :
    Module.finrank K (IntermediateField.fixedField (lowerRamificationGroup K L 1)) =
      Module.finrank K L /
        ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    IntermediateField.fixingSubgroup_fixedField, Subgroup.index_eq_card_div]
  rw [IsGalois.card_aut_eq_finrank, natCard_lowerRamificationGroup_one]

end TauCeti.LocalFieldsRamification

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/-- The fixed field of finite wild inertia, lifted to the algebraic closure, is the intersection
of `L` with the maximal tamely ramified extension. -/
@[simp]
theorem lift_fixedField_lowerRamificationGroup_one :
    lift (fixedField (lowerRamificationGroup K L 1)) =
      maximalTameExtension K (AlgebraicClosure K) ⊓ L := by
  rw [← map_wildInertiaSubgroup_restrictNormalHom L, wildInertiaSubgroup_def]
  rw [← InfiniteGalois.restrict_fixedField]
  -- In equal characteristic the absolute fixed field also contains purely inseparable elements;
  -- intersecting with the separable field `L` removes them.
  have hT : maximalTameExtension K (AlgebraicClosure K) ≤
      separableClosure K (AlgebraicClosure K) := le_separableClosure _ _ _
  have hfix := fixedField_fixingSubgroup_lift_inf_separableClosure (restrict hT)
  rw [lift_restrict] at hfix
  calc
    fixedField (maximalTameExtension K (AlgebraicClosure K)).fixingSubgroup ⊓ L =
        (fixedField (maximalTameExtension K (AlgebraicClosure K)).fixingSubgroup ⊓
          separableClosure K (AlgebraicClosure K)) ⊓ L := by
      rw [inf_assoc, inf_eq_right.mpr (le_separableClosure K _ L)]
    _ = maximalTameExtension K (AlgebraicClosure K) ⊓ L := congrArg (· ⊓ L) hfix

/-- The degree of the maximal tamely ramified subextension of a finite Galois extension is
`[L : K] / p ^ (v_p e(L/K))`. -/
theorem finrank_maximalTameExtension_inf :
    Module.finrank K ↥(maximalTameExtension K (AlgebraicClosure K) ⊓ L) =
      Module.finrank K L /
        ringChar 𝓀[K] ^ (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  rw [← L.lift_fixedField_lowerRamificationGroup_one,
    ← (liftAlgEquiv (fixedField (lowerRamificationGroup K L 1))).toLinearEquiv.finrank_eq]
  exact finrank_fixedField_lowerRamificationGroup_one K L

end IntermediateField
