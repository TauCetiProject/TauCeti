/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Basic facts about quotient modules

A surjective linear map `f : M → M₂` sending `p` into `q` induces a surjective map
`M ⧸ p → M₂ ⧸ q`, and the induced map is injective exactly when `f⁻¹(q) ≤ p`. The quotient by a
submodule is torsion-free exactly when the submodule is saturated, that is, contains every element
of which it contains a multiple by a regular scalar.

## Main results

* `Submodule.mapQ_surjective`: induced maps on quotients preserve surjectivity.
* `Submodule.mapQ_injective_iff`: the map `M ⧸ p → M₂ ⧸ q` induced by `f` is injective exactly
  when `f⁻¹(q) ≤ p`.
* `Submodule.isTorsionFree_quotient_iff`: a submodule has torsion-free quotient if and only if
  it is saturated.
-/

public section

namespace Submodule

variable {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [Ring R₂] [AddCommGroup M₂]
  [Module R₂ M₂] {τ₁₂ : R →+* R₂} (p : Submodule R M) (q : Submodule R₂ M₂)

/-- Surjectivity of a linear map implies surjectivity of the map it induces on quotients. -/
theorem mapQ_surjective (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) (hf : Function.Surjective f) :
    Function.Surjective (p.mapQ q f h) := by
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk x, rfl⟩

/-- The map `M ⧸ p → M₂ ⧸ q` induced by `f` is injective exactly when the inverse image of `q`
under `f` lies in `p`. -/
theorem mapQ_injective_iff (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) :
    Function.Injective (p.mapQ q f h) ↔ comap f q ≤ p := by
  rw [← LinearMap.ker_eq_bot, ker_mapQ, ← le_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ]

/-- The quotient by a submodule is torsion-free if and only if the submodule contains every
element of which it contains a multiple by a regular scalar. Over a domain the regular scalars
are exactly the nonzero ones, see `isRegular_iff_ne_zero`. -/
theorem isTorsionFree_quotient_iff {S : Submodule R M} :
    Module.IsTorsionFree R (M ⧸ S) ↔ ∀ (c : R) (z : M), IsRegular c → c • z ∈ S → z ∈ S :=
  ⟨fun _ c _ hc ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem S c).mp hc.isSMulRegular _,
    fun hS ↦ ⟨fun c hc ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem S c).mpr (hS c · hc)⟩⟩

end Submodule
