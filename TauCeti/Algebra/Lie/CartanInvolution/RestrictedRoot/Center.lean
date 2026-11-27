/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic
public import TauCeti.Algebra.Lie.Solvable.Basic

/-!
# Restricted roots and the centre

Let `θ` be an automorphism of a Lie algebra `𝔤₀` with `-1`-eigenspace `𝔭`, and `𝔞` a maximal
abelian subspace of `𝔭`. For reductive `𝔤₀` the centre `𝔷(𝔤₀)` is in general nonzero, and the
restricted root theory of `𝔞` only sees its part in `[𝔤₀, 𝔤₀]`. This file proves the centre
statements of restricted root theory:

* `𝔞` contains `𝔭 ∩ 𝔷(𝔤₀)`, so `𝔞_𝔷 = 𝔞 ∩ 𝔷(𝔤₀) = 𝔭 ∩ 𝔷(𝔤₀)`
  (`LieEquiv.IsMaximalAbelianInP.cartanP_inf_center_le`,
  `LieEquiv.IsMaximalAbelianInP.inf_center_eq`);
* every restricted root vanishes on `𝔞 ∩ 𝔷(𝔤₀)`
  (`Submodule.apply_eq_zero_of_mem_restrictedRoots_of_mem_center`);
* over a field, the restricted root space of a nonzero functional lies in the derived algebra
  `[𝔤₀, 𝔤₀]` (`Submodule.restrictedRootSpace_le_derivedSeries_one`).

None of these needs `θ` to be a Cartan involution.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra LieModule Module

namespace Submodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {𝔞 : Submodule R L}

/-- **Restricted roots vanish on the centre**: if `H ∈ 𝔞` is central, then `μ(H) = 0` for every
restricted root `μ`, since `H` acts by `0` on a nonzero vector of `𝔤_μ`. -/
theorem apply_eq_zero_of_mem_restrictedRoots_of_mem_center [IsDomain R] [IsTorsionFree R L]
    {μ : Dual R 𝔞} (hμ : μ ∈ 𝔞.restrictedRoots) {H : 𝔞} (hH : (H : L) ∈ center R L) :
    μ H = 0 := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (mem_restrictedRoots.mp hμ).2
  have h := mem_restrictedRootSpace.mp hx H
  rw [← lie_skew, (mem_maxTrivSubmodule R L L _).mp hH x, neg_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hx0

/-- **Restricted root spaces of nonzero functionals lie in the derived algebra**: for `x ∈ 𝔤_μ`
and `H ∈ 𝔞` with `μ(H) ≠ 0`, `x = μ(H)⁻¹ [H, x]`. -/
theorem restrictedRootSpace_le_derivedSeries_one {K L : Type*} [Field K] [LieRing L]
    [LieAlgebra K L] {𝔞 : Submodule K L} {μ : Dual K 𝔞} (hμ : μ ≠ 0) :
    𝔞.restrictedRootSpace μ ≤ (derivedSeries K L 1).toSubmodule := by
  intro x hx
  obtain ⟨H, hH⟩ := not_forall.mp (mt LinearMap.ext hμ)
  have hx' : x = (μ H)⁻¹ • ⁅(H : L), x⁆ := by
    rw [mem_restrictedRootSpace.mp hx H, smul_smul, inv_mul_cancel₀ hH, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (lie_mem_derivedSeries_one (R := K) (H : L) x)

end Submodule

namespace LieEquiv.IsMaximalAbelianInP

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {θ : L ≃ₗ⁅R⁆ L}
  {𝔞 : Submodule R L}

/-- **A maximal abelian subspace of `𝔭` contains `𝔭 ∩ 𝔷(𝔤₀)`**: a central element of `𝔭`
centralizes `𝔞`, and `𝔞` is its own centralizer in `𝔭`. -/
theorem cartanP_inf_center_le (h𝔞 : θ.IsMaximalAbelianInP 𝔞) :
    θ.cartanP ⊓ (center R L).toSubmodule ≤ 𝔞 := by
  refine le_trans ?_ h𝔞.restrictedRootSpace_zero_inf_cartanP.le
  rintro x ⟨hxp, hxz⟩
  refine ⟨Submodule.mem_restrictedRootSpace_zero.mpr fun H ↦ ?_, hxp⟩
  exact (mem_maxTrivSubmodule R L L _).mp hxz H

/-- **`𝔞_𝔷 = 𝔞 ∩ 𝔷(𝔤₀) = 𝔭 ∩ 𝔷(𝔤₀)`** for a maximal abelian subspace `𝔞` of `𝔭`. -/
theorem inf_center_eq (h𝔞 : θ.IsMaximalAbelianInP 𝔞) :
    𝔞 ⊓ (center R L).toSubmodule = θ.cartanP ⊓ (center R L).toSubmodule :=
  le_antisymm (inf_le_inf_right _ h𝔞.le_cartanP) (le_inf h𝔞.cartanP_inf_center_le inf_le_right)

end LieEquiv.IsMaximalAbelianInP
