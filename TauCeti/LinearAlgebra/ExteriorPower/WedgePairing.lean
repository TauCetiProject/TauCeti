/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Evaluation formulas for wedge products and pairings

The wedge product of pure exterior products concatenates their vector families. A trivialisation
in a specified top degree gives the wedge pairing by composing the wedge product with that
trivialisation; the degree transports disappear after identifying the degree with the finrank.
-/

public section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l : ℕ}

/-- The wedge product of pure exterior products concatenates their vector families. -/
@[simp 1100]
theorem wedge_ιMulti (u : Fin k → M) (v : Fin l → M) :
    wedge R M k l (ιMulti R k u) (ιMulti R l v) = ιMulti R (k + l) (Fin.append u v) := by
  apply Subtype.ext
  simp only [SetLike.coe_gMul, wedge, DirectSum.gMulLHom_apply_apply,
    ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]

/-- A wedge pairing transported from a specified top degree is the wedge product followed by
the trivialisation in that degree. -/
theorem wedgePairing_eq_compr₂_of_finrank_eq (n : ℕ) (hfin : Module.finrank R M = n)
    (hdeg : k + l = n) (vol : (⋀[R]^n M) ≃ₗ[R] R) :
    wedgePairing
        ((LinearEquiv.ofEq (⋀[R]^(Module.finrank R M) M) (⋀[R]^n M)
          (congrArg (fun d ↦ ⋀[R]^d M) hfin)).trans vol) (hdeg.trans hfin.symm) =
      (wedge R M k l).compr₂ (hdeg ▸ vol) := by
  subst n
  rfl

end exteriorPower
