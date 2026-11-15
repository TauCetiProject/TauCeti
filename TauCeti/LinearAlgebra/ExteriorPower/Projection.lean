/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Projections of the exterior algebra onto exterior powers

The exterior algebra `⋀ M` is the internal direct sum of the exterior powers `⋀ⁱ M`. This file
defines the linear projection `⋀ M → ⋀ⁱ M` onto the degree-`i` component of this decomposition,
and computes it on homogeneous elements.

## Main declarations

* `TauCeti.exteriorPower.proj`: the projection `⋀ M → ⋀ⁱ M` onto the degree-`i` component.
* `TauCeti.exteriorPower.coe_proj_of_mem`: it is the identity on `⋀ⁱ M` and vanishes on the other
  exterior powers.
-/

public section

noncomputable section

namespace TauCeti

namespace exteriorPower

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The projection of the exterior algebra onto its degree-`i` component `⋀ⁱ M`. -/
def proj (i : ℕ) : ExteriorAlgebra R M →ₗ[R] ⋀[R]^i M :=
  DirectSum.component R ℕ (fun i ↦ ⋀[R]^i M) i ∘ₗ
    (DirectSum.decomposeLinearEquiv (fun i ↦ ⋀[R]^i M)).toLinearMap

variable {R M}

/-- The projection onto `⋀ⁱ M` is the degree-`i` component of the direct sum decomposition. -/
theorem proj_apply (i : ℕ) (x : ExteriorAlgebra R M) :
    proj R M i x = DirectSum.decompose (fun i ↦ ⋀[R]^i M) x i :=
  (rfl)

/-- On an element of `⋀ᵖ M`, the projection onto `⋀ⁱ M` is the identity if `p = i` and zero
otherwise. -/
theorem coe_proj_of_mem {i p : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^p M) :
    (proj R M i x : ExteriorAlgebra R M) = if p = i then x else 0 := by
  rw [proj_apply]
  split_ifs with hpi
  · subst hpi
    exact DirectSum.decompose_of_mem_same _ hx
  · exact DirectSum.decompose_of_mem_ne _ hx hpi

/-- The projection onto `⋀ᵖ M` is the identity on `⋀ᵖ M`. -/
@[simp]
theorem proj_coe (p : ℕ) (x : ⋀[R]^p M) : proj R M p x = x :=
  Subtype.ext ((coe_proj_of_mem x.2).trans (by simp))

end exteriorPower

end TauCeti
