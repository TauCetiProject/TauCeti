/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed Lie subalgebras

The fixed submodule of a Lie endomorphism is closed under brackets. Its underlying
submodule is the existing linear fixed submodule.
-/

public section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

namespace LieHom

/-- The Lie subalgebra fixed by an endomorphism, with the native fixed submodule. -/
def fixedSubalgebra (f : L →ₗ⁅R⁆ L) : LieSubalgebra R L where
  __ := f.toLinearMap.fixedSubmodule
  lie_mem' {x y} hx hy := by
    exact LinearMap.mem_fixedSubmodule_iff.mpr ((f.map_lie x y).trans
      (congrArg₂ (fun x y : L => ⁅x, y⁆) (LinearMap.mem_fixedSubmodule_iff.mp hx)
        (LinearMap.mem_fixedSubmodule_iff.mp hy)))

/-- Membership in the fixed Lie subalgebra is the fixed-point equation. -/
@[simp]
theorem mem_fixedSubalgebra {f : L →ₗ⁅R⁆ L} {x : L} :
    x ∈ f.fixedSubalgebra ↔ f x = x :=
  Iff.rfl

/-- The underlying submodule is the existing linear fixed submodule. -/
@[simp]
theorem fixedSubalgebra_toSubmodule (f : L →ₗ⁅R⁆ L) :
    f.fixedSubalgebra.toSubmodule = f.toLinearMap.fixedSubmodule := by
  rfl

end LieHom
