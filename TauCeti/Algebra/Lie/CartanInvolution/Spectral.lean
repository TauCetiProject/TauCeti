/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Reductive.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Prod
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# `ad X` is diagonalizable on `𝔭`

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀`, with `-1`-eigenspace `𝔭`. For
`X ∈ 𝔭`, `ad X` is self-adjoint for the positive definite twisted Killing form `B_θ`
(`LieEquiv.ad_mem_selfAdjointSubmodule_twistedKillingForm`), so it is diagonalizable over `ℝ`: its
eigenspaces span `𝔤₀`, and it is a semisimple endomorphism. This feeds the restricted root space
decomposition `LieEquiv.IsCartanInvolution.iSup_restrictedRootSpace_eq_top`.

For a reductive Cartan involution of a real Lie algebra, whenever `θ x + x ∈ Z(L)`, splitting `x`
into its central and derived components forces the derived component to lie in `𝔭` and decomposes
`ad x` across `L = Z(L) ⊕ [L, L]`: it vanishes on `Z(L)` and diagonalizes on `[L, L]`, so `ad x`
is diagonalizable and semisimple on all of `L` as well
(`LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top`,
`LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`).

## Main results

* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: the eigenspaces of `ad X`, `X ∈ 𝔭`,
  span `𝔤₀`.
* `LieEquiv.IsCartanInvolution.isSemisimple_ad`: `ad X` is semisimple for `X ∈ 𝔭`.
* `LieEquiv.IsReductiveCartanInvolution.iSup_eigenspace_ad_eq_top`,
  `LieEquiv.IsReductiveCartanInvolution.isSemisimple_ad`: diagonalizability and semisimplicity of
  `ad x` when `θ x + x ∈ center ℝ L` and `θ` is a reductive Cartan involution over `ℝ`.
-/

public section

open LieAlgebra Module

namespace LieEquiv

namespace IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {θ : L ≃ₗ⁅ℝ⁆ L} {x : L}

/-- **`ad X` is diagonalizable over `ℝ` for `X ∈ 𝔭`.** The eigenspaces of `ad X` span the Lie
algebra: `ad X` is self-adjoint for the positive definite twisted Killing form. -/
theorem iSup_eigenspace_ad_eq_top (hθ : θ.IsCartanInvolution) (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, (ad ℝ L x).eigenspace μ = ⊤ :=
  have := hθ.finiteDimensional
  ((LinearMap.mem_selfAdjointSubmodule _).mp
    (θ.ad_mem_selfAdjointSubmodule_twistedKillingForm hx)).iSup_eigenspace_eq_top
      hθ.posDef_twistedKillingForm

/-- `ad X` is a semisimple endomorphism for `X ∈ 𝔭`. -/
theorem isSemisimple_ad (hθ : θ.IsCartanInvolution) (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsCartanInvolution

namespace IsReductiveCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- If `θ x + x` is central in `L = Z(L) ⊕ [L, L]`, then the `[L, L]`-component of `x` lies in
`(θ.derivedSeriesCongr 1).cartanP`. -/
private theorem derivedComponent_mem_cartanP {R L' : Type*} [CommRing R] [LieRing L']
    [LieAlgebra R L'] (θ : L' ≃ₗ⁅R⁆ L') (hc : IsCompl (center R L') (derivedSeries R L' 1))
    {x : L'} (hx : θ x + x ∈ center R L') :
    ((LieIdeal.prodEquivOfIsCompl (center R L') (derivedSeries R L' 1) hc).symm x).2 ∈
      (θ.derivedSeriesCongr 1).cartanP := by
  have hmap := LieIdeal.prodEquivOfIsCompl_symm_map (center R L') (derivedSeries R L' 1) hc hc
    (θ : L' →ₗ⁅R⁆ L') (fun _ ↦ θ.apply_mem_center_iff.mpr)
    (fun _ ↦ (θ.apply_mem_derivedSeries_iff 1).mpr) x
  simp only [LieEquiv.coe_toLieHom] at hmap
  have hsum := LieIdeal.prodEquivOfIsCompl_symm_apply_left (center R L')
    (derivedSeries R L' 1) hc ⟨θ x + x, hx⟩
  have h2 := congrArg Prod.snd hsum
  rw [map_add, Prod.snd_add, congrArg Prod.snd hmap] at h2
  rw [mem_cartanP]
  exact Subtype.ext <| by
    rw [coe_derivedSeriesCongr, NegMemClass.coe_neg, eq_neg_iff_add_eq_zero]
    simpa using congrArg Subtype.val h2

/-- **Diagonalizability of `ad x` for a reductive Cartan involution.** Over `ℝ`, whenever
`θ x + x ∈ center ℝ L`, the eigenspaces of `ad x` span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : θ x + x ∈ center ℝ L) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ := by
  have hc := hθ.isCompl_center_derivedSeries
  set p := (LieIdeal.prodEquivOfIsCompl (center ℝ L) (derivedSeries ℝ L 1) hc).symm x
  set z := p.1
  set d := p.2
  -- Split `x = z + d`; `ad x` agrees with `ad d`, and `d` lies in `cartanP` of `[L, L]`.
  have hx_eq : x = (z : L) + (d : L) :=
    (LieIdeal.prodEquivOfIsCompl_symm_fst_add_snd (center ℝ L) (derivedSeries ℝ L 1) hc x).symm
  have hd_mem : d ∈ (θ.derivedSeriesCongr 1).cartanP :=
    derivedComponent_mem_cartanP θ hc hx
  have had_comp : (ad ℝ L x).comp (derivedSeries ℝ L 1).incl.toLinearMap =
      (derivedSeries ℝ L 1).incl.toLinearMap.comp (ad ℝ (derivedSeries ℝ L 1) d) := by
    rw [hx_eq, TauCeti.LieAlgebra.ad_add_of_mem_center_left z.property (d : L)]
    exact (derivedSeries ℝ L 1).toLieSubalgebra.ad_comp_incl_eq d
  -- `Z(L)` lies in the `0`-eigenspace of `ad x`.
  have hZ : (center ℝ L).toSubmodule ≤ ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ := by
    refine le_trans ?_ (le_iSup (fun μ ↦ Module.End.eigenspace (ad ℝ L x) μ) 0)
    intro w hw
    rw [Module.End.mem_eigenspace_iff, zero_smul, ad_apply,
      (LieModule.mem_maxTrivSubmodule ℝ L L w).mp hw x]
  -- `[L, L]` is spanned by eigenspaces of `ad d`, which map into eigenspaces of `ad x`.
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
  rw [eq_top_iff, ← (LieSubmodule.isCompl_toSubmodule.mpr hc).sup_eq_top]
  exact sup_le hZ hD

/-- For a reductive Cartan involution of a real Lie algebra and every `x` with
`θ x + x ∈ center ℝ L`, the adjoint operator `ad x` is semisimple. -/
theorem isSemisimple_ad {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsReductiveCartanInvolution)
    {x : L} (hx : θ x + x ∈ center ℝ L) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end IsReductiveCartanInvolution

end LieEquiv
