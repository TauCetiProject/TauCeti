/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Splitting the first coordinate of a submodule

The inverse image of a submodule of `Fin N → M` under deletion of coordinate zero
is the product of a copy of `M` and that submodule. For `M = R`, this is the fibrewise
coordinate splitting for adjoining a first trivial line to a plane. The construction
restricts Mathlib's `Fin.consLinearEquiv`.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {N : ℕ}

/-- Splitting off coordinate zero identifies the inverse image of a submodule under
`Fin.tail` with a copy of the coordinate module followed by that submodule. -/
def finConsEquiv (V : Submodule R (Fin N → M)) :
    (M × V) ≃ₗ[R] V.comap (LinearMap.funLeft R M Fin.succ) where
  toFun p := ⟨Fin.cons p.1 p.2.1, by
    apply (Submodule.mem_comap).2
    convert p.2.property using 1
    ext i
    simp⟩
  invFun v := (v.1 0, ⟨Fin.tail v.1, v.property⟩)
  left_inv p := by ext <;> simp
  right_inv v := Subtype.ext (Fin.cons_self_tail v.1)
  map_add' p q := by
    apply Subtype.ext
    exact (Fin.consLinearEquiv R (fun _ : Fin (N + 1) ↦ M)).map_add (p.1, p.2.1) (q.1, q.2.1)
  map_smul' a p := by
    apply Subtype.ext
    exact (Fin.consLinearEquiv R (fun _ : Fin (N + 1) ↦ M)).map_smul a (p.1, p.2.1)

@[simp]
theorem coe_finConsEquiv_apply (V : Submodule R (Fin N → M)) (p : M × V) :
    (V.finConsEquiv p).1 = Fin.cons p.1 p.2.1 := (rfl)

@[simp]
theorem finConsEquiv_symm_apply (V : Submodule R (Fin N → M))
    (v : V.comap (LinearMap.funLeft R M Fin.succ)) :
    V.finConsEquiv.symm v = (v.1 0, ⟨Fin.tail v.1, v.property⟩) := (rfl)

end Submodule
