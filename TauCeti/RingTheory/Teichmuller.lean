/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Teichmuller

/-!
# Coordinates of the inverse of reduction on perfection

The inverse of `Perfection.quotientMulEquiv` commutes with shifting compatible root sequences.
Its `n`-th coordinate is therefore the Teichmüller map applied after `n` shifts. These formulas
extend Mathlib's zeroth-coordinate formula `Perfection.coeff_zero_symm_quotientMulEquiv`.

The Teichmüller map is natural (`Perfection.teichmuller₀_map`): a ring homomorphism `f : R →+* S`
carrying `I` into `J`, between `I`-adically and `J`-adically complete rings, intertwines
`teichmuller₀ p I` and `teichmuller₀ p J` with the induced map of perfections, because `f`
preserves the congruences characterising the Teichmüller lifts.
-/

public section

namespace Perfection

variable {p : ℕ} {R : Type*} [CommRing R] [Fact p.Prime] {I : Ideal R}
  [CharP (R ⧸ I) p] [IsAdicComplete I R]

/-- Reduction on perfection commutes with shifting the root sequence. -/
@[simp]
theorem quotientMulEquiv_symm_powMulEquiv (z : Perfection R p) :
    quotientMulEquiv p I ((powMulEquiv (Perfection R p) p).symm z) =
      (powMulEquiv (Perfection (R ⧸ I) p) p).symm (quotientMulEquiv p I z) := by
  apply Perfection.ext
  intro n
  simp only [← coeffMonoidHom_eq_coeff, coeffMonoidHom_symm_powMulEquiv,
    coeff_quotientMulEquiv]
  exact (coeff_quotientMulEquiv z (n + 1)).symm

/-- The inverse of reduction on perfection commutes with shifting the root sequence. -/
theorem semiconj_symm_quotientMulEquiv_pthRootMonoidHom :
    Function.Semiconj (quotientMulEquiv p I).symm
      (pthRootMonoidHom (R ⧸ I) p) (pthRootMonoidHom R p) := by
  intro y
  apply (quotientMulEquiv p I).injective
  simp only [coe_pthRootMonoidHom_eq_powMulEquiv_symm,
    quotientMulEquiv_symm_powMulEquiv, MulEquiv.apply_symm_apply]

/-- The `n`-th coordinate of inverse reduction is Teichmüller after `n` shifts. -/
@[simp]
theorem coeffMonoidHom_symm_quotientMulEquiv (x : Perfection (R ⧸ I) p) (n : ℕ) :
    coeffMonoidHom R p n ((quotientMulEquiv p I).symm x) =
      teichmuller₀ p I ((pthRootMonoidHom (R ⧸ I) p)^[n] x) := by
  have hc := coeffMonoidHom_iterate_symm_powMulEquiv
    ((quotientMulEquiv p I).symm x) 0 n
  rw [Nat.zero_add, ← coe_pthRootMonoidHom_eq_powMulEquiv_symm,
    ← semiconj_symm_quotientMulEquiv_pthRootMonoidHom.iterate_right n x,
    coeff_zero_symm_quotientMulEquiv] at hc
  exact hc.symm

variable {S : Type*} [CommRing S] {J : Ideal S} [CharP (S ⧸ J) p] [IsAdicComplete J S]

/-- **Naturality of the Teichmüller map**: a ring homomorphism `f : R →+* S` carrying `I` into `J`
satisfies `teichmuller₀ p J (Perfection.map p (Ideal.quotientMap J f h) x) =
f (teichmuller₀ p I x)`. -/
theorem teichmuller₀_map (f : R →+* S) (h : I ≤ J.comap f) (x : Perfection (R ⧸ I) p) :
    teichmuller₀ p J (map p (Ideal.quotientMap J f h) x) = f (teichmuller₀ p I x) := by
  refine teichmuller₀_spec fun n ↦ ⟨f (coeff _ p n x).out, ?_, ?_⟩
  · rw [coeff_map, ← Ideal.Quotient.mk_out (coeff _ p n x), Ideal.quotientMap_mk,
      Ideal.Quotient.mk_out]
  · have hI := SModEq.sub_mem.mp
      (teichmuller₀_sModEq (x := x) (n := n) (Ideal.Quotient.mk_out _)).symm
    rw [SModEq.sub_mem, ← map_pow, ← map_sub]
    -- `f` carries `I ^ (n + 1)` into `(I.map f) ^ (n + 1) ≤ J ^ (n + 1)`
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr h) _ <|
      Ideal.map_pow f I _ ▸ Ideal.mem_map_of_mem f hI

end Perfection
