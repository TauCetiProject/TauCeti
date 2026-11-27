/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Basic

/-!
# The Capelli eigenvalue on a highest weight vector

On a vector killed by the strictly upper entries, a principal quantum minor acts by the product
of the shifted diagonal eigenvalues. The same formula applies to an ordered principal block,
with the shifts counted within that block. No Lie commutation relations are needed for this
calculation.

For the Capelli eigenvalue, see A. Molev, M. Nazarov and G. Olshanski, *Yangians and classical Lie
algebras*, §2, especially Remark 2.11 for the evaluation in the enveloping algebra.
-/

public section

namespace Matrix

/-- The Capelli eigenvalue on a highest weight vector for the ordered principal block `a`.
For the full quantum determinant, take `a = id`. -/
theorem quantumMinor_smul_of_highestWeight {ι K A M : Type*} [DecidableEq ι] [CommRing K]
    [Ring A] [Algebra K A] [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
    {n : ℕ} (E : Matrix ι ι A) (u : K) {a : Fin n → ι} (ha : Function.Injective a)
    (v : M) (ν : Fin n → K)
    (hupper : ∀ i j, i < j → E (a i) (a j) • v = 0)
    (hdiag : ∀ i, E (a i) (a i) • v = ν i • v) :
    E.quantumMinor u a a • v = (∏ j : Fin n, (u - (j.val : K) + ν j)) • v := by
  rw [quantumMinor_eq_columnDet]
  apply columnDet_smul_of_upper_smul_eq_zero
  · intro i j hij
    simpa only [of_apply, ite_eq_right (ha.ne hij.ne), zero_add] using hupper i j hij
  · intro i
    simp only [of_apply, ↓reduceIte, add_smul, algebraMap_smul, hdiag]

end Matrix
