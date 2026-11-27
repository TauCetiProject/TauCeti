/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.HopfAlgebra.Subalgebra
import TauCeti.LinearAlgebra.TensorProduct.Descent

/-!
# Pullback of Hopf subalgebras along a field extension

If `D` is a Hopf subalgebra of `L ⊗[K] H`, its inverse image under `h ↦ 1 ⊗ h` is a Hopf
subalgebra of `H`. This does not require that `D` descend to `K`. If `D` is finite-dimensional,
so is its inverse image: the scalar extension of the inverse image embeds in `D`.

This allows finite quotients and their coefficient functions to be found over `K` after first
constructing them over a larger field.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace Subalgebra.IsHopfSubalgebra

variable {K L H : Type*} [Field K] [CommRing L] [Algebra K L] [Ring H] [HopfAlgebra K H]
  {D : Subalgebra L (L ⊗[K] H)}

/-- The inverse image of a Hopf subalgebra after extension of the ground field is a Hopf
subalgebra, even when the given subalgebra does not itself descend. -/
theorem comap_includeRight (hD : D.IsHopfSubalgebra) :
    ((D.restrictScalars K).comap
      (Algebra.TensorProduct.includeRight : H →ₐ[K] L ⊗[K] H)).IsHopfSubalgebra where
  comul_mem x hx := by
    apply Submodule.tensor_mem_range_comap_of_baseChange D.toSubmodule D.toSubmodule
    have h := hD.comul_mem (x := (1 : L) ⊗ₜ[K] x) hx
    simpa only [TensorProduct.comul_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def] using h
  antipode_mem x hx := by
    have h := hD.antipode_mem hx
    simpa [TensorProduct.antipode_def] using h

end Subalgebra.IsHopfSubalgebra
