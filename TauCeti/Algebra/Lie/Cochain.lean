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
* `LieModule.Cohomology.twoCochainMap`: pulling 2-cochains back along a Lie algebra morphism and
  pushing them forward along a linear map; with trivial coefficients it preserves 2-cocycles
  (`LieModule.Cohomology.twoCochainMap_mem_twoCocycle`).
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

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [AddCommGroup M'] [Module R M']

/-- Pull a 2-cochain back along a Lie algebra morphism `φ` and push it forward along a linear map
`e` of coefficients: `(x, y) ↦ e (c (φ x) (φ y))`. -/
def twoCochainMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) :
    twoCochain R L M →ₗ[R] twoCochain R L' M' where
  toFun c := ⟨(c.1.compl₁₂ φ.toLinearMap φ.toLinearMap).compr₂ e, fun x ↦ by simp⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma twoCochainMap_apply_apply (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L) (c : twoCochain R L M)
    (x y : L') : twoCochainMap e φ c x y = e (c (φ x) (φ y)) :=
  (rfl)

variable [LieRingModule L M] [LieModule R L M]

/-- Every coboundary is a 2-cocycle. -/
lemma range_d₁₂_le_twoCocycle : LinearMap.range (d₁₂ R L M) ≤ twoCocycle R L M := by
  rintro _ ⟨f, rfl⟩
  rw [mem_twoCocycle_iff, ← LinearMap.comp_apply, d₂₃_comp_d₁₂, LinearMap.zero_apply]

/-- With trivial coefficients, the differential `d₁₂` commutes with pulling one-cochains back along
a Lie algebra morphism `φ` and pushing them forward along a linear map `e` of coefficients. -/
lemma d₁₂_comp_lieHom_apply_apply_ofTrivial [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M'] (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (f : oneCochain R L M) (x y : L') :
    d₁₂ R L' M' (e ∘ₗ f ∘ₗ φ.toLinearMap) x y = e (d₁₂ R L M f (φ x) (φ y)) := by
  simp only [d₁₂_apply_apply_ofTrivial, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    LieHom.map_lie, map_neg]

/-- With trivial coefficients, pulling back along a Lie algebra morphism and pushing forward along
a linear map sends 2-cocycles to 2-cocycles. -/
lemma twoCochainMap_mem_twoCocycle [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M'] (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    {c : twoCochain R L M} (hc : c ∈ twoCocycle R L M) :
    twoCochainMap e φ c ∈ twoCocycle R L' M' := by
  rw [mem_twoCocycle_iff_of_trivial] at hc ⊢
  intro x y z
  simp only [twoCochainMap_apply_apply, LieHom.map_lie, hc (φ x) (φ y) (φ z), map_add]

end LieModule.Cohomology
