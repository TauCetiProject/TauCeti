/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Basic.Real.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# `ad X` is diagonalizable on `𝔭`

Let `θ` be a Cartan involution of a real Lie algebra `𝔤₀`, with `-1`-eigenspace `𝔭`. For
`X ∈ 𝔭`, `ad X` is self-adjoint for the positive definite twisted Killing form `B_θ`
(`LieEquiv.ad_mem_selfAdjointSubmodule_twistedKillingForm`), so it is diagonalizable over `ℝ`: its
eigenspaces span `𝔤₀`, and it is a semisimple endomorphism. This feeds the restricted root space
decomposition `LieEquiv.IsCartanInvolution.iSup_restrictedRootSpace_eq_top`.

## Main results

* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: the eigenspaces of `ad X`, `X ∈ 𝔭`,
  span `𝔤₀`.
* `LieEquiv.IsCartanInvolution.isSemisimple_ad`: `ad X` is semisimple for `X ∈ 𝔭`.
-/

public section

open LieAlgebra Module

namespace LieEquiv.IsCartanInvolution

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

end LieEquiv.IsCartanInvolution
