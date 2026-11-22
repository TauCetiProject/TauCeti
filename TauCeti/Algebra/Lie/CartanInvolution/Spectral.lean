/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
import TauCeti.Algebra.Lie.CartanInvolution.ReductiveDecomposition
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Spectral properties of real Cartan involutions

Over `ℝ`, self-adjointness of `ad x` for `x ∈ 𝔭` with respect to the twisted Killing inner product
`B_θ` makes `ad x` diagonalizable (`LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`) and
semisimple (`LieEquiv.IsCartanInvolution.isSemisimple_ad`).

For a reductive Cartan involution of a real Lie algebra, splitting `x ∈ 𝔭` into its central and
derived components decomposes `ad x` across `L = Z(L) ⊕ [L, L]`: it vanishes on `Z(L)` and
diagonalizes on `[L, L]`, so `ad x` is diagonalizable and semisimple on all of `L` as well
(`LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top`,
`LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`).

## Main results

* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`,
  `LieEquiv.IsCartanInvolution.isSemisimple_ad`: diagonalizability and semisimplicity of `ad x`
  for `x ∈ θ.cartanP` when `θ` is a Cartan involution over `ℝ`.
* `LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top`,
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`: diagonalizability and semisimplicity of
  `ad x` for `x ∈ θ.cartanP` when `θ` is a reductive Cartan involution over `ℝ`.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

namespace IsCartanInvolution

/-- **Diagonalizability of `ad x` on `𝔭`.** For a Cartan involution of a real Lie algebra and
every `x ∈ 𝔭`, the eigenspaces of `ad x` over `ℝ` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have : FiniteDimensional ℝ L := hθ.finiteDimensional
  exact LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top
    (fun _ ↦ hθ.twistedKillingForm_self_pos)
    ((LinearMap.mem_selfAdjointSubmodule _).mp
      (θ.ad_mem_selfAdjointSubmodule_twistedKillingForm hx))

/-- For a Cartan involution of a real Lie algebra and every `x ∈ 𝔭`, the adjoint operator `ad x`
is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsCartanInvolution

namespace IsReductiveCartanInvolution

/-- **Diagonalizability of `ad x` on `𝔭` for a reductive Cartan involution.** Over `ℝ`, for every
`x ∈ θ.cartanP`, the eigenspaces of `ad x` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have hc := hθ.isCompl_center_derivedSeries
  obtain ⟨⟨z, d⟩, hzd⟩ := (θ.cartanPCenterDerivedEquiv hc).surjective ⟨x, hx⟩
  have hx_eq : x = (z.val : L) + (d.val : L) := by
    rw [← θ.coe_cartanPCenterDerivedEquiv_apply hc (z, d), hzd]
  have had_comp : (ad ℝ L x).comp (derivedSeries ℝ L 1).incl.toLinearMap =
      (derivedSeries ℝ L 1).incl.toLinearMap.comp (ad ℝ (derivedSeries ℝ L 1) d.val) := by
    ext u
    change ⁅x, (u : L)⁆ = ⁅(d.val : L), (u : L)⁆
    have hz : ⁅(z.val : L), (u : L)⁆ = 0 := by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule ℝ L L z.val).mp z.val.property u, neg_zero]
    rw [hx_eq, add_lie, hz, zero_add]
  rw [eq_top_iff]
  have hZ : (center ℝ L).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    refine le_trans ?_ (le_iSup (fun μ ↦ Module.End.eigenspace (ad ℝ L x) μ) 0)
    intro w hw
    rw [Module.End.mem_eigenspace_iff, zero_smul, ad_apply,
      (LieModule.mem_maxTrivSubmodule ℝ L L w).mp hw x]
  have hD : (derivedSeries ℝ L 1).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    have hspan := hθ.isCartanInvolution_derivedSeries.iSup_eigenspace_ad_eq_top d.property
    have hmap : Submodule.map (derivedSeries ℝ L 1).incl.toLinearMap
        (⨆ μ : ℝ, Module.End.eigenspace (ad ℝ (derivedSeries ℝ L 1) d.val) μ) ≤
        ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun μ ↦ Module.End.map_genEigenspace_le _ had_comp μ 1
    rw [hspan] at hmap
    intro w hw
    exact hmap ⟨⟨w, hw⟩, Submodule.mem_top, rfl⟩
  have hsup : (center ℝ L).toSubmodule ⊔ (derivedSeries ℝ L 1).toSubmodule = ⊤ :=
    (LieSubmodule.isCompl_toSubmodule.mpr hc).sup_eq_top
  rw [← hsup]
  exact sup_le hZ hD

/-- For a reductive Cartan involution of a real Lie algebra and every `x ∈ θ.cartanP`, the adjoint
operator `ad x` is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsReductiveCartanInvolution

end LieEquiv
