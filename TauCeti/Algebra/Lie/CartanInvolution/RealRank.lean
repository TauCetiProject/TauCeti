/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic

/-!
# The real rank of a real Lie algebra

For a Cartan involution `θ` of a real Lie algebra `L` and a maximal abelian subspace `𝔞` of the
`-1`-eigenspace `𝔭` of `θ`, the dimension of `𝔞` does not depend on the choices; the common value
is the *real rank* of `L`. This file defines the real rank without making a choice, as the
supremum of `finrank ℝ 𝔞` over all Cartan involutions `θ` and all maximal abelian subspaces `𝔞` of
their `𝔭`. A real Lie algebra with no Cartan involution, for instance one that is not semisimple,
has real rank `0` because the supremum is empty.

Transporting a Cartan involution `θ` of `L` along a Lie algebra isomorphism `e : L ≃ L'` to
`e ∘ θ ∘ e⁻¹` gives a Cartan involution of `L'` (`LieEquiv.IsCartanInvolution.conj`), with
`-1`-eigenspace the image of that of `θ` and the images of maximal abelian subspaces maximal
abelian (`LieEquiv.IsMaximalAbelianInP.map`), so the real rank is invariant under
isomorphism. A Cartan involution shows that the real rank vanishes exactly when the Killing form
is negative definite.

That every choice attains the supremum (conjugacy of the maximal abelian subspaces and of the
Cartan involutions) is not proved here.

## Main definitions

* `LieAlgebra.realRank`: the real rank of a real Lie algebra.

## Main results

* `LieAlgebra.finrank_le_realRank`: every maximal abelian subspace of `𝔭` has dimension at most
  the real rank.
* `LieAlgebra.exists_finrank_eq_realRank`: given a Cartan involution, the supremum defining the
  real rank is attained.
* `LieAlgebra.realRank_eq_zero_of_forall_not_isCartanInvolution`: without a Cartan involution the
  real rank is `0`.
* `LieAlgebra.realRank_congr`: the real rank is invariant under isomorphism.
* `LieAlgebra.realRank_eq_zero_of_killingForm_neg`: a real Lie algebra with negative definite
  Killing form (a compact one) has real rank `0`.
* `LieAlgebra.realRank_eq_zero_iff_of_isCartanInvolution`: given a Cartan involution, the real
  rank is `0` exactly when the Killing form is negative definite.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra Module Submodule

namespace LieAlgebra

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

/-- The **real rank** of a real Lie algebra: the supremum of `finrank ℝ 𝔞` over the Cartan
involutions `θ` of `L` and the maximal abelian subspaces `𝔞` of their `-1`-eigenspaces `𝔭`.
Written as a supremum so that it makes no choice. A real Lie algebra with no Cartan involution,
for instance one that is not semisimple, has real rank `0`. -/
noncomputable def realRank : ℕ :=
  sSup {n | ∃ θ : L ≃ₗ⁅ℝ⁆ L, θ.IsCartanInvolution ∧
    ∃ 𝔞 : Submodule ℝ L, θ.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = n}

theorem realRank_def : realRank L = sSup {n | ∃ θ : L ≃ₗ⁅ℝ⁆ L, θ.IsCartanInvolution ∧
    ∃ 𝔞 : Submodule ℝ L, θ.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = n} :=
  (rfl)

variable {L}

/-- Every value in the supremum defining the real rank is at most `finrank ℝ L`. -/
private theorem le_finrank_of_mem {n : ℕ} (hn : ∃ θ : L ≃ₗ⁅ℝ⁆ L, θ.IsCartanInvolution ∧
    ∃ 𝔞 : Submodule ℝ L, θ.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = n) : n ≤ finrank ℝ L := by
  obtain ⟨θ, hθ, 𝔞, -, rfl⟩ := hn
  have := hθ.finiteDimensional
  exact Submodule.finrank_le 𝔞

/-- The real rank is at most the dimension. -/
theorem realRank_le_finrank : realRank L ≤ finrank ℝ L :=
  csSup_le' fun _ ↦ le_finrank_of_mem

/-- Every maximal abelian subspace of the `-1`-eigenspace of a Cartan involution has dimension
at most the real rank. -/
theorem finrank_le_realRank {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) {𝔞 : Submodule ℝ L}
    (h𝔞 : θ.IsMaximalAbelianInP 𝔞) : finrank ℝ 𝔞 ≤ realRank L :=
  le_csSup ⟨finrank ℝ L, fun _ ↦ le_finrank_of_mem⟩ ⟨θ, hθ, 𝔞, h𝔞, rfl⟩

/-- Given a Cartan involution, the supremum defining the real rank is attained: some Cartan
involution has a maximal abelian subspace of its `-1`-eigenspace of dimension the real rank. -/
theorem exists_finrank_eq_realRank {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) :
    ∃ θ' : L ≃ₗ⁅ℝ⁆ L, θ'.IsCartanInvolution ∧
      ∃ 𝔞 : Submodule ℝ L, θ'.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = realRank L := by
  obtain ⟨𝔞, h𝔞⟩ := θ.exists_isMaximalAbelianInP
  exact Nat.sSup_mem (s := {n | ∃ θ : L ≃ₗ⁅ℝ⁆ L, θ.IsCartanInvolution ∧
    ∃ 𝔞 : Submodule ℝ L, θ.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = n})
    ⟨_, θ, hθ, 𝔞, h𝔞, rfl⟩ ⟨finrank ℝ L, fun _ ↦ le_finrank_of_mem⟩

/-- A real Lie algebra with no Cartan involution has real rank `0`. -/
theorem realRank_eq_zero_of_forall_not_isCartanInvolution
    (h : ∀ θ : L ≃ₗ⁅ℝ⁆ L, ¬ θ.IsCartanInvolution) : realRank L = 0 := by
  refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
  rintro _ ⟨θ, hθ, -⟩
  exact absurd hθ (h θ)

/-- A real Lie algebra that is not semisimple has real rank `0`. -/
theorem realRank_eq_zero_of_not_isSemisimple (h : ¬ IsSemisimple ℝ L) : realRank L = 0 :=
  realRank_eq_zero_of_forall_not_isCartanInvolution fun _ hθ ↦ h hθ.isSemisimple

/-- The values in the supremum defining the real rank only grow under an isomorphism. -/
private theorem subset_of_equiv {L' : Type*} [LieRing L'] [LieAlgebra ℝ L'] (e : L ≃ₗ⁅ℝ⁆ L') :
    {n | ∃ θ : L ≃ₗ⁅ℝ⁆ L, θ.IsCartanInvolution ∧
      ∃ 𝔞 : Submodule ℝ L, θ.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = n} ⊆
    {n | ∃ θ : L' ≃ₗ⁅ℝ⁆ L', θ.IsCartanInvolution ∧
      ∃ 𝔞 : Submodule ℝ L', θ.IsMaximalAbelianInP 𝔞 ∧ finrank ℝ 𝔞 = n} := by
  rintro _ ⟨θ, hθ, 𝔞, h𝔞, rfl⟩
  exact ⟨e.conj θ, hθ.conj e, 𝔞.map (e.toLinearEquiv : L →ₗ[ℝ] L'), h𝔞.map e,
    LinearEquiv.finrank_map_eq e.toLinearEquiv 𝔞⟩

/-- The real rank is invariant under isomorphism of real Lie algebras. -/
theorem realRank_congr {L' : Type*} [LieRing L'] [LieAlgebra ℝ L'] (e : L ≃ₗ⁅ℝ⁆ L') :
    realRank L = realRank L' := by
  rw [realRank_def, realRank_def, (subset_of_equiv e).antisymm (subset_of_equiv e.symm)]

/-- A real Lie algebra with negative definite Killing form, a compact one, has real rank `0`:
for every Cartan involution `𝔭 = 0`. -/
theorem realRank_eq_zero_of_killingForm_neg (h : ∀ x : L, x ≠ 0 → killingForm ℝ L x x < 0) :
    realRank L = 0 := by
  refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
  rintro _ ⟨θ, hθ, 𝔞, h𝔞, rfl⟩
  have h𝔞0 : 𝔞 = ⊥ := eq_bot_iff.mpr (h𝔞.le_cartanP.trans (hθ.cartanP_eq_bot_iff.mpr h).le)
  rw [h𝔞0, finrank_bot]

/-- Given a Cartan involution, a real Lie algebra has real rank `0` exactly when its Killing form
is negative definite, that is, when it is compact. -/
theorem realRank_eq_zero_iff_of_isCartanInvolution {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution) :
    realRank L = 0 ↔ ∀ x : L, x ≠ 0 → killingForm ℝ L x x < 0 := by
  refine ⟨fun h ↦ hθ.cartanP_eq_bot_iff.mp (eq_bot_iff.mpr fun x hx ↦ ?_),
    realRank_eq_zero_of_killingForm_neg⟩
  -- `x` lies in a maximal abelian subspace `𝔞`, of dimension at most the real rank `0`.
  have := hθ.finiteDimensional
  obtain ⟨𝔞, h𝔞, hx𝔞⟩ := LieEquiv.exists_isMaximalAbelianInP_mem hx
  have h𝔞0 : finrank ℝ 𝔞 = 0 := Nat.eq_zero_of_le_zero (h ▸ finrank_le_realRank hθ h𝔞)
  rw [Submodule.finrank_eq_zero] at h𝔞0
  rw [h𝔞0] at hx𝔞
  exact hx𝔞

end LieAlgebra
