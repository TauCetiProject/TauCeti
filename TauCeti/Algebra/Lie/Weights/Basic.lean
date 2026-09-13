/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# Elementary identities for Lie algebra weights

This file records general identities for weights that are used by several parts of the Lie algebra
weight-space theory.

## Main results

* `LieModule.map_weightSpace_le`: a Lie-module homomorphism preserves each weight space.
* `LieModule.comap_weightSpace_eq_of_injective`: the preimage under an injective Lie-module
  homomorphism is the corresponding source weight space.
* `LieModule.map_weightSpace_eq_of_injective`: an injective Lie-module homomorphism identifies a
  weight space with the intersection of the target weight space and its range.
* `LieModule.map_weightSpace_eq`: a Lie-module equivalence maps each weight space onto the
  corresponding weight space.
* `LieSubmodule.toSubmodule_map_weightSpace_incl`: inclusion identifies a submodule's weight space
  with its intersection with the ambient weight space.
* `LieSubmodule.finrank_inf_weightSpace`: that intersection has the dimension of the submodule's
  weight space.
* `TauCeti.Weight.coe_neg_eq_add_of_coe_eq_add`: reading a vanishing sum of four weights as an
  equation between opposite pair sums.

## References

The weight-space transport family follows the generalized-weight-space API
`LieModule.map_genWeightSpace_le` through `LieModule.map_genWeightSpace_eq` in
`Mathlib.Algebra.Lie.Weights.Basic`.
-/

public section

namespace LieModule

variable {R L M M₂ : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

/-- A morphism of Lie modules sends a weight space into the corresponding weight space. -/
theorem map_weightSpace_le (f : LieModuleHom R L M M₂) (χ : L → R) :
    (weightSpace M χ).map f ≤ weightSpace M₂ χ := by
  intro y hy
  rw [LieSubmodule.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [mem_weightSpace] at hx ⊢
  intro l
  rw [← f.map_lie, hx l, map_smul]

/-- The preimage of a weight space under an injective Lie-module homomorphism is the corresponding
weight space in the source. -/
theorem comap_weightSpace_eq_of_injective {f : LieModuleHom R L M M₂} (χ : L → R)
    (hf : Function.Injective f) :
    (weightSpace M₂ χ).comap f = weightSpace M χ := by
  apply le_antisymm
  · intro m hm
    rw [LieSubmodule.mem_comap, mem_weightSpace] at hm
    rw [mem_weightSpace]
    intro x
    apply hf
    rw [f.map_lie, map_smul, hm x]
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_weightSpace_le f χ

/-- Under an injective Lie-module homomorphism, the image of a weight space is the intersection of
the corresponding target weight space with the range. -/
theorem map_weightSpace_eq_of_injective {f : LieModuleHom R L M M₂} (χ : L → R)
    (hf : Function.Injective f) :
    (weightSpace M χ).map f = weightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm
    (le_inf_iff.mpr ⟨map_weightSpace_le f χ, LieSubmodule.map_le_range f⟩) ?_
  rintro y ⟨hy, ⟨x, rfl⟩⟩
  simp only [← comap_weightSpace_eq_of_injective χ hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap] at hy ⊢
  exact ⟨x, hy, rfl⟩

/-- A Lie-module equivalence maps a weight space onto the corresponding weight space. -/
theorem map_weightSpace_eq (e : LieModuleEquiv R L M M₂) (χ : L → R) :
    (weightSpace M χ).map e = weightSpace M₂ χ := by
  simp [map_weightSpace_eq_of_injective χ e.injective]

end LieModule

namespace LieSubmodule

open LieModule Module

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {H : LieSubalgebra R L}

/-- Inclusion of a Lie submodule identifies its weight space with the intersection of the ambient
weight space and its carrier. -/
theorem toSubmodule_map_weightSpace_incl (N : LieSubmodule R L M) (χ : H → R) :
    ((weightSpace ↥N χ).map (N.incl.restrictLie H)).toSubmodule
      = (weightSpace M χ).toSubmodule ⊓ N.toSubmodule := by
  rw [LieModule.map_weightSpace_eq_of_injective χ (injective_incl N),
    LieSubmodule.inf_toSubmodule]
  congr 1
  ext x
  simp

/-- The intersection of an ambient weight space with a Lie submodule has the dimension of the
corresponding weight space in the submodule. -/
theorem finrank_inf_weightSpace {K : Type*} [Field K] [LieAlgebra K L]
    [Module K M] [LieModule K L M] {H : LieSubalgebra K L}
    (N : LieSubmodule K L M) (χ : H → K) :
    finrank K ((weightSpace M χ).toSubmodule ⊓ N.toSubmodule : Submodule K M)
      = finrank K (weightSpace ↥N χ) := by
  have hequiv := (LieSubmodule.equivMapOfInjective
    (f := N.incl.restrictLie H) (weightSpace ↥N χ) (injective_incl N)).toLinearEquiv.finrank_eq
  rw [← N.toSubmodule_map_weightSpace_incl χ, TauCeti.finrank_toSubmodule, ← hequiv]

end LieSubmodule

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- If four weights sum to zero and a weight `μ` names the sum of the first two, then `-μ` names
the sum of the last two. -/
theorem Weight.coe_neg_eq_add_of_coe_eq_add {μ : Weight K H L} {a b c d : H → K}
    (hsum : a + b + c + d = 0) (hμ : (μ : H → K) = a + b) :
    ((-μ : Weight K H L) : H → K) = c + d := by
  funext y
  have hy := congrFun hsum y
  simp only [Weight.coe_neg, hμ, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hy ⊢
  linear_combination -hy

end TauCeti
