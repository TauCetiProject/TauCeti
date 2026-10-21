/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
-- Private: `Module.Basis.exteriorAlgebra_eq_prod_map_sort` is used only inside a proof.
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Evaluation formulas for wedge products and pairings

The wedge product of pure exterior products concatenates their vector families. A trivialisation
in a specified top degree gives the wedge pairing by composing the wedge product with that
trivialisation; the degree transports disappear after identifying the degree with the finrank.
The top exterior product `Module.Basis.topVector` of a basis indexed by `Fin n` is the pure wedge
of the basis vectors, read in the degree `finrank R M = n`.
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

/-- The top exterior product of a basis indexed by `Fin n` is the wedge of the basis vectors in
their given order, read in the degree `finrank R M = n`. -/
theorem _root_.Module.Basis.topVector_eq_ιMulti [Nontrivial R] {n : ℕ}
    (h : Module.finrank R M = n) (b : Module.Basis (Fin n) R M) :
    b.topVector = ιMulti R _ (b ∘ finCongr h) := by
  ext
  rw [Module.Basis.coe_topVector, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    Module.Basis.exteriorAlgebra_eq_prod_map_sort, Fin.sort_univ, List.map_map,
    ← List.ofFn_eq_map]
  subst h
  rfl

end exteriorPower
