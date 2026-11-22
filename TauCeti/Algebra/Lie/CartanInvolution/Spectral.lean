/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import TauCeti.Algebra.Lie.CartanInvolution.Reductive.Basic
import TauCeti.Algebra.Lie.Prod
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Spectral properties of real Cartan involutions

Over `ℝ`, self-adjointness of `ad x` for `x ∈ 𝔭` with respect to the twisted Killing inner product
`B_θ` makes `ad x` diagonalizable (`LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`) and
semisimple (`LieEquiv.IsCartanInvolution.isSemisimple_ad`).

For a reductive Cartan involution of a real Lie algebra, whenever `θ x + x ∈ Z(L)`, splitting `x`
into its central and derived components forces the derived component to lie in `𝔭` and decomposes
`ad x` across `L = Z(L) ⊕ [L, L]`: it vanishes on `Z(L)` and diagonalizes on `[L, L]`, so `ad x`
is diagonalizable and semisimple on all of `L` as well
(`LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top`,
`LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`).

## Main results

* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`,
  `LieEquiv.IsCartanInvolution.isSemisimple_ad`: diagonalizability and semisimplicity of `ad x`
  for `x ∈ θ.cartanP` when `θ` is a Cartan involution over `ℝ`.
* `LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top`,
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`: diagonalizability and semisimplicity of
  `ad x` when `θ x + x ∈ center ℝ L` and `θ` is a reductive Cartan involution over `ℝ`.
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

/-- **Diagonalizability of `ad x` for a reductive Cartan involution.** Over `ℝ`, whenever
`θ x + x ∈ center ℝ L`, the eigenspaces of `ad x` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : θ x + x ∈ center ℝ L) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have hc := hθ.isCompl_center_derivedSeries
  obtain ⟨⟨z, d⟩, hzd⟩ :=
    (LieIdeal.prodEquivOfIsCompl (center ℝ L) (derivedSeries ℝ L 1) hc).surjective x
  have hx_eq : x = (z : L) + (d : L) :=
    hzd.symm.trans (LieIdeal.prodEquivOfIsCompl_apply (center ℝ L) (derivedSeries ℝ L 1) hc (z, d))
  have hd_mem : d ∈ (θ.derivedSeriesCongr 1).cartanP := by
    have hdD : θ (d : L) + (d : L) ∈ derivedSeries ℝ L 1 :=
      (derivedSeries ℝ L 1).add_mem ((θ.apply_mem_derivedSeries_iff 1).mpr d.property) d.property
    have hzZ : θ (z : L) + (z : L) ∈ center ℝ L :=
      (center ℝ L).add_mem (θ.apply_mem_center_iff.mpr z.property) z.property
    have hdZ : θ (d : L) + (d : L) ∈ center ℝ L := by
      have hsub : θ (d : L) + (d : L) = (θ x + x) - (θ (z : L) + (z : L)) := by
        rw [hx_eq, map_add]
        abel
      rw [hsub]
      exact (center ℝ L).sub_mem hx hzZ
    have hbot : θ (d : L) + (d : L) = 0 := by
      rw [← LieSubmodule.mem_bot (R := ℝ) (L := L) (M := L), ← hc.inf_eq_bot]
      exact ⟨hdZ, hdD⟩
    rw [mem_cartanP]
    exact Subtype.ext <| by
      rw [coe_derivedSeriesCongr, NegMemClass.coe_neg]
      exact eq_neg_of_add_eq_zero_left hbot
  have had_x : ad ℝ L x = ad ℝ L (d : L) := by
    have hz0 : ad ℝ L (z : L) = 0 := by
      ext w
      rw [ad_apply, LinearMap.zero_apply, ← lie_skew,
        (LieModule.mem_maxTrivSubmodule ℝ L L z).mp z.property w, neg_zero]
    rw [hx_eq, map_add, hz0, zero_add]
  have had_comp : (ad ℝ L x).comp (derivedSeries ℝ L 1).incl.toLinearMap =
      (derivedSeries ℝ L 1).incl.toLinearMap.comp (ad ℝ (derivedSeries ℝ L 1) d) := by
    rw [had_x]
    exact (derivedSeries ℝ L 1).toLieSubalgebra.ad_comp_incl_eq d
  rw [eq_top_iff]
  have hZ : (center ℝ L).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    refine le_trans ?_ (le_iSup (fun μ ↦ Module.End.eigenspace (ad ℝ L x) μ) 0)
    intro w hw
    rw [Module.End.mem_eigenspace_iff, zero_smul, ad_apply,
      (LieModule.mem_maxTrivSubmodule ℝ L L w).mp hw x]
  have hD : (derivedSeries ℝ L 1).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    have hspan := hθ.isCartanInvolution_derivedSeries.iSup_eigenspace_ad_eq_top hd_mem
    have hmap : Submodule.map (derivedSeries ℝ L 1).incl.toLinearMap
        (⨆ μ : ℝ, Module.End.eigenspace (ad ℝ (derivedSeries ℝ L 1) d) μ) ≤
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

/-- For a reductive Cartan involution of a real Lie algebra and every `x` with
`θ x + x ∈ center ℝ L`, the adjoint operator `ad x` is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : θ x + x ∈ center ℝ L) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsReductiveCartanInvolution

end LieEquiv
