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
On the exterior-power bases induced by a basis `b`, the wedge pairing of `e_s` and `e_t` is the
shuffle sign of `s` times the volume of `b` when `s` and `t` are disjoint, and zero otherwise.
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

/-- **The wedge pairing on exterior-power basis vectors**: `e_s` and `e_t` pair to the shuffle sign
of `s` times the volume `vol b.topVector` when `s` and `t` are disjoint, and to zero otherwise.
This is the entrywise form of Mathlib's `exteriorPower.wedgePairing_eq_apply_topVector_smul`. -/
theorem wedgePairing_exteriorPower_apply [Nontrivial R] (vol : ⋀[R]^(Module.finrank R M) M ≃ₗ[R] R)
    (hkl : k + l = Module.finrank R M) {ι : Type*} [LinearOrder ι] [Fintype ι]
    (b : Module.Basis ι R M) (s : Set.powersetCard ι k) (t : Set.powersetCard ι l) :
    wedgePairing vol hkl (b.exteriorPower k s) (b.exteriorPower l t) =
      Set.powersetCard.sign s • vol b.topVector • if Disjoint s.val t.val then 1 else 0 := by
  have hkl' : k + l = Fintype.card ι := by rw [hkl, Module.finrank_eq_card_basis b]
  rw [wedgePairing_eq_apply_topVector_smul vol hkl b]
  simp [-Module.Basis.coe_dualBasis, -coe_basis, Module.Basis.groupSMul_apply,
    Module.Basis.dualBasis_apply_self, Equiv.eq_symm_apply, eq_comm (b := s),
    Set.powersetCard.disjoint_iff_eq_compl hkl']

end exteriorPower
