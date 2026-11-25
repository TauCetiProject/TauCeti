/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Basic.Real.Basic
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# The restricted root space decomposition

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀` and `𝔞` an abelian subspace of the
`-1`-eigenspace `𝔭` of `θ`. The operators `ad H`, `H ∈ 𝔞`, commute, and each is self-adjoint for
the positive definite twisted Killing form `B_θ(x, y) = -B(x, θ y)`, hence diagonalizable over `ℝ`.
So they are simultaneously diagonalizable, and `𝔤₀` is the internal direct sum of the restricted
root spaces `𝔤_λ`, `λ ∈ 𝔞*`:

`𝔤₀ = 𝔤_0 ⊕ ⨁_{λ ∈ Σ} 𝔤_λ`.

This is the direct route of Knapp's construction, which needs no group: only the joint eigenspaces
of `ad 𝔞` for linear eigenvalue functions are nonzero, since `ad` is linear.

## Main results

* `LieEquiv.IsCartanInvolution.iSup_restrictedRootSpace_eq_top`: the restricted root spaces of an
  abelian subspace of `𝔭` span `𝔤₀`.
* `LieEquiv.IsCartanInvolution.isInternal_restrictedRootSpace`: `𝔤₀` is their internal direct sum.
* `LieEquiv.IsCartanInvolution.restrictedRootSpace_zero_sup_iSup_restrictedRoots_eq_top`:
  `𝔤₀ = 𝔤_0 + ∑_{λ ∈ Σ} 𝔤_λ`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
-/

public section

open LieAlgebra Module

namespace LieEquiv.IsCartanInvolution

open Submodule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {𝔞 : Submodule ℝ L}

/-- **The restricted root spaces span.** For a Cartan involution `θ` of a real Lie algebra and an
abelian subspace `𝔞` of `𝔭`, the restricted root spaces `𝔤_λ`, `λ ∈ 𝔞*`, span the Lie
algebra. -/
theorem iSup_restrictedRootSpace_eq_top (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)
    (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : ⨆ μ : Dual ℝ 𝔞, 𝔞.restrictedRootSpace μ = ⊤ := by
  have : FiniteDimensional ℝ L := hθ.finiteDimensional
  have hcomm : Pairwise fun H H' : 𝔞 ↦ Commute (ad ℝ L H) (ad ℝ L H') := fun H H' _ ↦
    TauCeti.LieAlgebra.commute_ad_of_lie_eq_zero (hab _ H.property _ H'.property)
  have h := TauCeti.iSup_iInf_eigenspace_eq_top_of_iSup_eigenspace_eq_top
    (fun H : 𝔞 ↦ ad ℝ L H) hcomm fun H ↦
      ((LinearMap.mem_selfAdjointSubmodule _).mp
        (θ.ad_mem_selfAdjointSubmodule_twistedKillingForm (h𝔞 H.property))).iSup_eigenspace_eq_top
        hθ.posDef_twistedKillingForm
  refine eq_top_iff.mpr (h.symm.le.trans (iSup_le fun χ ↦ ?_))
  by_cases hχ : ⨅ H : 𝔞, End.eigenspace (ad ℝ L H) (χ H) = ⊥
  · exact hχ.le.trans bot_le
  obtain ⟨μ, rfl⟩ := exists_dual_eq_of_iInf_eigenspace_ne_bot hχ
  exact le_iSup_of_le μ restrictedRootSpace_eq_iInf.ge

open scoped Classical in
/-- **The restricted root space decomposition.** For a Cartan involution `θ` of a real Lie algebra
and an abelian subspace `𝔞` of `𝔭`, the Lie algebra is the internal direct sum of the restricted
root spaces `𝔤_λ`, `λ ∈ 𝔞*`. -/
theorem isInternal_restrictedRootSpace (hθ : θ.IsCartanInvolution) (h𝔞 : 𝔞 ≤ θ.cartanP)
    (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) : DirectSum.IsInternal 𝔞.restrictedRootSpace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_restrictedRootSpace
    (hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab)

/-- **`𝔤₀ = 𝔤_0 + ∑_{λ ∈ Σ} 𝔤_λ`.** For a Cartan involution `θ` of a real Lie algebra and an
abelian subspace `𝔞` of `𝔭`, the Lie algebra is spanned by the centralizer `𝔤_0` of `𝔞` and the
restricted root spaces of the restricted roots. -/
theorem restrictedRootSpace_zero_sup_iSup_restrictedRoots_eq_top (hθ : θ.IsCartanInvolution)
    (h𝔞 : 𝔞 ≤ θ.cartanP) (hab : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) :
    𝔞.restrictedRootSpace 0 ⊔ ⨆ μ ∈ 𝔞.restrictedRoots, 𝔞.restrictedRootSpace μ = ⊤ := by
  refine eq_top_iff.mpr ((hθ.iSup_restrictedRootSpace_eq_top h𝔞 hab).symm.le.trans
    (iSup_le fun μ ↦ ?_))
  by_cases h0 : μ = 0
  · exact h0 ▸ le_sup_left
  by_cases hbot : 𝔞.restrictedRootSpace μ = ⊥
  · exact hbot.le.trans bot_le
  exact le_sup_of_le_right (le_iSup₂_of_le μ (mem_restrictedRoots.mpr ⟨h0, hbot⟩) le_rfl)

end LieEquiv.IsCartanInvolution
