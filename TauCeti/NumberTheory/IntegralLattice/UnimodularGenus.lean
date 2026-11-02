/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
public import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij
import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular

/-!
# The genus of unimodular lattices

Evenness is a genus invariant (`TauCeti.IntegralLattice.SameGenus.isEven_iff`), since it is
detected by the dyadic localization. For unimodular lattices it is, together with the signature,
a complete invariant of the genus: two unimodular lattices lie in one genus exactly when they have
the same signature and are both even or both odd.

The determinant of a unimodular lattice is `(-1) ^ n₋`, so only the prime `2` needs a local
comparison. There the unimodular forms over `ℤ_[2]` are classified by rank, type, determinant
square class and oddity, and the oddity of a unimodular lattice is its signature modulo `8` by
van der Blij's theorem (`TauCeti.IntegralLattice.vanDerBlij`). For instance, the odd unimodular
lattices of signature `(p, q)` form the single genus of `I_{p,q} = ⟨1⟩ ^ p ⊕ ⟨-1⟩ ^ q`.

## Main results

* `TauCeti.IntegralLattice.sameGenus_iff_of_isUnimodular`: unimodular lattices lie in one genus
  exactly when their signatures agree and they are even together.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

/-- **The genus of a unimodular lattice.** Two unimodular lattices lie in one genus exactly when
their signatures agree and they are both even or both odd. -/
theorem sameGenus_iff_of_isUnimodular (hLu : L.IsUnimodular) (hMu : M.IsUnimodular) :
    L.SameGenus M ↔ L.signature = M.signature ∧ (L.IsEven ↔ M.IsEven) := by
  refine ⟨fun h ↦ ⟨h.signature_eq, h.isEven_iff⟩, fun ⟨hsig, heven⟩ ↦ ?_⟩
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  have : M.IsNondegenerate := ⟨hMu.nondegenerate⟩
  -- Read off the positive and negative indices from the signature equality.
  have hsig' := hsig
  simp only [signature, Prod.mk.injEq] at hsig'
  obtain ⟨hpos, -, hneg⟩ := hsig'
  -- Both determinants are `(-1) ^ n₋`, since both discriminants are `1`.
  have hdet : L.determinant = M.determinant := by
    rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
      M.determinant_eq_neg_one_pow_sigNeg_mul_discriminant,
      L.isUnimodular_iff_discriminant_eq_one.mp hLu, M.isUnimodular_iff_discriminant_eq_one.mp hMu,
      hneg]
  have hL := L.isUnimodular_iff_isUnit_determinant.mp hLu
  have hM := M.isUnimodular_iff_isUnit_determinant.mp hMu
  refine (L.sameGenus_iff_localIntegralForm_equivalent_primeFactors M hdet hL.ne_zero).mpr
    ⟨hsig, fun p _ hp ↦ ?_⟩
  -- The determinant is a unit, so `2` is the only prime that needs checking.
  rw [Int.isUnit_iff_natAbs_eq.mp hL, mul_one, Nat.prime_two.primeFactors,
    Finset.mem_singleton] at hp
  subst hp
  -- By van der Blij's theorem both oddities are the common signature modulo `8`.
  obtain ⟨w, hw⟩ := hLu.exists_isCharacteristicVector
  obtain ⟨w', hw'⟩ := hMu.exists_isCharacteristicVector
  have hLw := L.vanDerBlij hLu hw
  have hMw := M.vanDerBlij hMu hw'
  rw [hpos, hneg] at hLw
  refine (L.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector M
    (hL.map (Int.castRingHom ℤ_[2])) (hM.map (Int.castRingHom ℤ_[2])) hw hw').mpr
    ⟨L.finrank_eq_of_signature_eq hsig, heven, ?_, hLw.symm.trans hMw⟩
  rw [hdet]
  exact IsSquare.mul_self _

end TauCeti.IntegralLattice
