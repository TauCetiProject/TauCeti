/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Integer multiples of a vector in a subgroup

For a `ℤ`-submodule `L` of an additive group and a vector `x`, the integers `a` with `a • x ∈ L`
form an ideal of `ℤ`, hence are the multiples of a single natural number `d`. For instance, the
vectors of a sublattice of `ℤ^m` supported on one coordinate are the multiples of `d • eᵢ`.

## Main results

* `Submodule.exists_smul_mem_iff_dvd`: `a • x ∈ L` exactly when `d ∣ a`, for some `d : ℕ`.
-/

public section

namespace Submodule

/-- For a `ℤ`-submodule `L` and a vector `x`, there is `d : ℕ` such that `a • x ∈ L` exactly when
`d` divides `a`. -/
theorem exists_smul_mem_iff_dvd {M : Type*} [AddCommGroup M] (L : Submodule ℤ M) (x : M) :
    ∃ d : ℕ, ∀ a : ℤ, a • x ∈ L ↔ (d : ℤ) ∣ a := by
  let I : Ideal ℤ := L.comap (LinearMap.toSpanSingleton ℤ M x)
  refine ⟨(IsPrincipal.generator I).natAbs, fun a ↦ ?_⟩
  rw [Int.natAbs_dvd, ← IsPrincipal.mem_iff_generator_dvd]
  simp [I]

end Submodule
