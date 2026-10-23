/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Cochain

/-!
# Low-degree Lie algebra cochains

Complements to Mathlib's low-degree cochain complex `LieModule.Cohomology` of a Lie algebra `L`
with values in an `L`-module `M`.

* `LieModule.Cohomology.range_d₁₂_le_twoCocycle`: every coboundary is a 2-cocycle.
* `LieModule.Cohomology.d₁₂_comp_lieHom_apply_apply_ofTrivial`: with trivial coefficients, `d₁₂`
  commutes with pulling back along a Lie algebra morphism and pushing forward along a linear map.
* An additive group structure on every submodule of 2-cochains, such as the 2-cocycles, so that
  quotients of such submodules can be formed.
-/

public section

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

namespace LieModule.Cohomology

/-- Submodules of 2-cochains are additive groups. Instance search does not find
`Submodule.addCommGroup` here on its own: it cannot recover the ambient module `twoCochain R L M`
by unification, so it is named explicitly. -/
instance instAddCommGroupSubmoduleTwoCochain (S : Submodule R (twoCochain R L M)) :
    AddCommGroup S :=
  Submodule.addCommGroup (M := twoCochain R L M) S

variable [LieRingModule L M] [LieModule R L M]

/-- Every coboundary is a 2-cocycle. -/
lemma range_d₁₂_le_twoCocycle : LinearMap.range (d₁₂ R L M) ≤ twoCocycle R L M := by
  rintro _ ⟨f, rfl⟩
  rw [mem_twoCocycle_iff, ← LinearMap.comp_apply, d₂₃_comp_d₁₂, LinearMap.zero_apply]

/-- With trivial coefficients, the differential `d₁₂` commutes with pulling one-cochains back along
a Lie algebra morphism `φ` and pushing them forward along a linear map `e` of coefficients. -/
lemma d₁₂_comp_lieHom_apply_apply_ofTrivial {L' M' : Type*} [LieRing L'] [LieAlgebra R L']
    [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M'] (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (f : oneCochain R L M) (x y : L') :
    d₁₂ R L' M' (e ∘ₗ f ∘ₗ φ.toLinearMap) x y = e (d₁₂ R L M f (φ x) (φ y)) := by
  simp only [d₁₂_apply_apply_ofTrivial, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieHom.map_lie, map_neg]

end LieModule.Cohomology
