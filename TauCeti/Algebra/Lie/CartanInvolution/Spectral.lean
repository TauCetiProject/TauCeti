/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import TauCeti.Algebra.Lie.CartanInvolution.Basic
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Real adjoint spectral theory for Cartan involutions

For a Cartan involution `θ` of a real Lie algebra `L` and any `x ∈ θ.cartanP`, the adjoint
operator `ad ℝ L x` is self-adjoint with respect to the positive-definite twisted Killing form
`θ.twistedKillingForm` (`LieEquiv.ad_mem_selfAdjointSubmodule_twistedKillingForm`). By the real
self-adjoint spectral theorem (`LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top`), `ad ℝ L x` is
diagonalizable over `ℝ` (`LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`) and hence
semisimple (`LieEquiv.IsCartanInvolution.isSemisimple_ad_of_mem_cartanP`).

## Main results

* `LieEquiv.IsCartanInvolution.iSup_eigenspace_ad_eq_top`: for `x ∈ θ.cartanP` over `ℝ`,
  `ad ℝ L x` is diagonalizable over `ℝ`.
* `LieEquiv.IsCartanInvolution.isSemisimple_ad_of_mem_cartanP`: for `x ∈ θ.cartanP` over `ℝ`,
  `ad ℝ L x` is a semisimple endomorphism.
-/

public section

open LieAlgebra

namespace LieEquiv.IsCartanInvolution

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- For a Cartan involution `θ` of a real Lie algebra and `x ∈ θ.cartanP`, the adjoint operator
`ad ℝ L x` is diagonalizable over `ℝ`: its real eigenspaces span `L`. -/
theorem iSup_eigenspace_ad_eq_top {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    ⨆ μ : ℝ, Module.End.eigenspace (ad ℝ L x) μ = ⊤ :=
  have := hθ.finiteDimensional
  LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top (fun _ hv ↦ hθ.twistedKillingForm_pos hv)
    ((LinearMap.mem_selfAdjointSubmodule (ad ℝ L x)).mp
      (ad_mem_selfAdjointSubmodule_twistedKillingForm hx))

/-- For a Cartan involution `θ` of a real Lie algebra and `x ∈ θ.cartanP`, `ad ℝ L x` is a
semisimple endomorphism. -/
theorem isSemisimple_ad_of_mem_cartanP {θ : L ≃ₗ⁅ℝ⁆ L} (hθ : θ.IsCartanInvolution)
    {x : L} (hx : x ∈ θ.cartanP) :
    (ad ℝ L x).IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (hθ.iSup_eigenspace_ad_eq_top hx)

end LieEquiv.IsCartanInvolution
