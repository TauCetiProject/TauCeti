/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Positive

/-!
# The triangular and Iwasawa decompositions of a real Lie algebra

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀`, with fixed subalgebra `𝔨` and
`-1`-eigenspace `𝔭`, let `𝔞` be an abelian subspace of `𝔭` and `H₀ ∈ 𝔞` a regular element, one on
which no restricted root vanishes. With `𝔫 = positiveRestrictedRootSpace 𝔞 H₀` the sum of the
restricted root spaces of the roots positive at `H₀` and `𝔫⁻ = θ 𝔫` that of the negative ones,
the restricted root space decomposition gives the *triangular decomposition*

`𝔤₀ = 𝔫⁻ ⊕ 𝔤_0 ⊕ 𝔫`,

where `𝔤_0 ⊕ 𝔫` is the minimal parabolic subalgebra. When `𝔞` is maximal abelian in `𝔭`, so that
`𝔤_0 = 𝔪 ⊕ 𝔞` with `𝔪 ⊆ 𝔨`, this yields the *Iwasawa decomposition* of the Lie algebra

`𝔤₀ = 𝔨 ⊕ 𝔞 ⊕ 𝔫`:

every `X ∈ 𝔫⁻` is `(X + θ X) - θ X` with `X + θ X ∈ 𝔨` and `θ X ∈ 𝔫`, and if `k = a + n` with
`k ∈ 𝔨`, `a ∈ 𝔞`, `n ∈ 𝔫`, applying `θ` gives `θ n = 2a + n ∈ 𝔫⁻ ∩ (𝔤_0 ⊕ 𝔫) = 0`. This is the Lie
algebra form of the decomposition `G = KAN` of a real semisimple Lie group.

The independence statements need neither regularity nor a Cartan involution, and hold for any
torsion-free Lie algebra over a linearly ordered commutative ring.

## Main results

* `LieEquiv.disjoint_fixedSubalgebra_sup_positiveRestrictedRootSpace`: `𝔨 ∩ (𝔞 + 𝔫) = 0` for an
  automorphism `θ` and an abelian `𝔞 ⊆ 𝔭`.
* `LieEquiv.IsCartanInvolution.isCompl_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace`:
  the triangular decomposition `𝔤₀ = (𝔤_0 ⊕ 𝔫) ⊕ 𝔫⁻`.
* `LieEquiv.IsMaximalAbelianInP.isCompl_fixedSubalgebra_sup_positiveRestrictedRootSpace`: the
  Iwasawa decomposition `𝔤₀ = 𝔨 ⊕ (𝔞 ⊕ 𝔫)`; with `Submodule.disjoint_positiveRestrictedRootSpace`
  the sum `𝔞 + 𝔫` is direct.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, Proposition 6.43.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter VI, §3,
  Theorem 3.4.
-/

public section

open LieAlgebra Module

namespace LieEquiv

open Submodule

variable {K L : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] [IsTorsionFree K L] {θ : L ≃ₗ⁅K⁆ L} {𝔞 : Submodule K L}

/-- **`𝔨 ∩ (𝔞 + 𝔫) = 0`.** For an automorphism `θ`, an abelian subspace `𝔞` of its
`-1`-eigenspace `𝔭` and any `H₀ ∈ 𝔞`, the fixed subalgebra `𝔨` of `θ` meets `𝔞 + 𝔫` trivially. -/
theorem disjoint_fixedSubalgebra_sup_positiveRestrictedRootSpace (h𝔞 : 𝔞 ≤ θ.cartanP)
    (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) (H₀ : 𝔞) :
    Disjoint θ.toLieHom.fixedSubalgebra.toSubmodule (𝔞 ⊔ 𝔞.positiveRestrictedRootSpace H₀) := by
  refine disjoint_def.mpr fun k hk hk' ↦ ?_
  obtain ⟨a, ha, n, hn, rfl⟩ := mem_sup.mp hk'
  have hθk : θ (a + n) = a + n := by
    rwa [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra, coe_toLieHom] at hk
  rw [map_add, mem_cartanP.mp (h𝔞 ha)] at hθk
  have hθn : θ n ∈ 𝔞.positiveRestrictedRootSpace (-H₀) := by
    rw [← map_positiveRestrictedRootSpace h𝔞]
    exact mem_map_of_mem hn
  -- `θ n = 2a + n` lies both in `𝔫⁻` and in `𝔤_0 + 𝔫`, so it vanishes.
  have heq : θ n = (a + a) + n := by
    rw [add_assoc, ← hθk]
    abel
  have ha0' : a + a ∈ 𝔞.restrictedRootSpace 0 :=
    add_mem (le_restrictedRootSpace_zero hab ha) (le_restrictedRootSpace_zero hab ha)
  have h0 : θ n = 0 := disjoint_def.mp
    disjoint_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace _
    (heq ▸ add_mem_sup ha0' hn) hθn
  have hn0 : n = 0 := θ.injective (h0.trans (map_zero θ).symm)
  have ha0 : a = 0 := by
    rw [h0, hn0, add_zero, ← two_smul K a] at heq
    exact (smul_eq_zero.mp heq.symm).resolve_left two_ne_zero
  rw [ha0, hn0, add_zero]

namespace IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L} {H₀ : 𝔞}

/-- **The triangular decomposition `𝔤₀ = 𝔫⁻ ⊕ 𝔤_0 ⊕ 𝔫`.** For a Cartan involution `θ` of a real
Lie algebra, an abelian subspace `𝔞` of `𝔭` and `H₀ ∈ 𝔞` on which no restricted root vanishes, the
sum `𝔤_0 ⊕ 𝔫` of the centralizer of `𝔞` and the positive restricted root space is a complement of
the negative restricted root space `𝔫⁻ = positiveRestrictedRootSpace 𝔞 (-H₀)`. -/
theorem isCompl_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace
    (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0)
    (hH₀ : ∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0) :
    IsCompl (𝔞.restrictedRootSpace 0 ⊔ 𝔞.positiveRestrictedRootSpace H₀)
      (𝔞.positiveRestrictedRootSpace (-H₀)) := by
  refine ⟨disjoint_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace,
    codisjoint_iff.mpr (eq_top_iff.mpr ?_)⟩
  refine (hθ.restrictedRootSpace_zero_sup_iSup_restrictedRoots_eq_top h𝔞 hab).symm.le.trans
    (sup_le (le_sup_left.trans le_sup_left) (iSup₂_le fun μ hμ ↦ ?_))
  rcases (hH₀ μ hμ).lt_or_gt with h | h
  · exact le_sup_of_le_right (positiveRestrictedRootSpace_neg_le_iff.mp le_rfl μ h)
  · exact le_sup_of_le_left
      (le_sup_of_le_right (restrictedRootSpace_le_positiveRestrictedRootSpace h))

end IsCartanInvolution

namespace IsMaximalAbelianInP

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L} {H₀ : 𝔞}

/-- **The Iwasawa decomposition `𝔤₀ = 𝔨 ⊕ 𝔞 ⊕ 𝔫`.** For a Cartan involution `θ` of a real Lie
algebra, a maximal abelian subspace `𝔞` of `𝔭` and `H₀ ∈ 𝔞` on which no restricted root vanishes,
the fixed subalgebra `𝔨` of `θ` is a complement of `𝔞 ⊕ 𝔫`, with `𝔫` the positive restricted
root space of `H₀`. The sum `𝔞 + 𝔫` is direct by `Submodule.disjoint_positiveRestrictedRootSpace`.
-/
theorem isCompl_fixedSubalgebra_sup_positiveRestrictedRootSpace (h𝔞 : θ.IsMaximalAbelianInP 𝔞)
    (hθ : θ.IsCartanInvolution) (hH₀ : ∀ μ ∈ 𝔞.restrictedRoots, μ H₀ ≠ 0) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule (𝔞 ⊔ 𝔞.positiveRestrictedRootSpace H₀) := by
  have hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0 := fun _ hx _ hy ↦ h𝔞.lie_eq_zero hx hy
  refine ⟨disjoint_fixedSubalgebra_sup_positiveRestrictedRootSpace h𝔞.le_cartanP hab H₀,
    codisjoint_iff.mpr (eq_top_iff.mpr ?_)⟩
  rw [← (hθ.isCompl_restrictedRootSpace_zero_sup_positiveRestrictedRootSpace h𝔞.le_cartanP hab
    hH₀).sup_eq_top]
  refine sup_le (sup_le ?_ (le_sup_of_le_right le_sup_right)) fun y hy ↦ ?_
  · -- `𝔤_0 = 𝔪 + 𝔞` with `𝔪 ⊆ 𝔨`.
    rw [h𝔞.restrictedRootSpace_zero_eq_sup (by norm_num) hθ.involutive]
    exact sup_le (le_sup_of_le_left inf_le_right) (le_sup_of_le_right le_sup_left)
  · -- `y = (y + θ y) - θ y` with `y + θ y ∈ 𝔨` and `θ y ∈ 𝔫`.
    have hθy : θ y ∈ 𝔞.positiveRestrictedRootSpace H₀ := by
      rw [← neg_neg H₀, ← map_positiveRestrictedRootSpace h𝔞.le_cartanP]
      exact mem_map_of_mem hy
    have hk : y + θ y ∈ θ.toLieHom.fixedSubalgebra.toSubmodule := by
      rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra, coe_toLieHom, map_add,
        hθ.involutive y, add_comm]
    exact mem_sup.mpr ⟨y + θ y, hk, -θ y, mem_sup_right (neg_mem hθy), by abel⟩

end IsMaximalAbelianInP

end LieEquiv
