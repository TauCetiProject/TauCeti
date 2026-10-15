/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.LocalRing
public import TauCeti.NumberTheory.IntegralLattice.Localization.Ideals

/-!
# Binary summands of even dyadic lattices

An even integral lattice whose determinant is a unit at `2` has an even unimodular localization.
It therefore splits off a rank-two perfect summand orthogonally. This is the induction step for
decomposing an even unimodular dyadic form into binary constituents.

## Main results

* `TauCeti.IntegralLattice.exists_binary_isPerfPair_isCompl_orthogonal_localIntegralForm`: an even
  lattice unimodular at `2` splits off a perfect binary summand after localization.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter IX.
-/

public section

namespace TauCeti.IntegralLattice

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **An even lattice unimodular at `2` splits off a perfect binary summand.** If the rank is at
least two, the dyadic localization has a rank-two submodule carrying a perfect restriction of the
local integral form and complementary to its orthogonal complement. -/
theorem exists_binary_isPerfPair_isCompl_orthogonal_localIntegralForm
    (L : IntegralLattice V) (hrank : 2 ≤ finrank ℤ L) (heven : L.IsEven)
    (hdet : IsUnit (L.determinant : ℤ_[2])) :
    ∃ S : Submodule ℤ_[2] (L.LocalCarrier 2),
      finrank ℤ_[2] S = 2 ∧ ((L.localIntegralForm 2).restrict S).IsPerfPair ∧
        IsCompl S ((L.localIntegralForm 2).orthogonal S) := by
  have hrank' : finrank ℤ L = (finrank ℤ L - 2) + 2 := (Nat.sub_add_cancel hrank).symm
  let c := (Module.finBasis ℤ L).reindex (finCongr hrank')
  let b := c.baseChange ℤ_[2]
  have heven' (x : L.LocalCarrier 2) :
      (2 : ℤ_[2]) ∣ L.localIntegralForm 2 x x := by
    rw [← Ideal.mem_span_singleton]
    exact (L.isEven_iff_localNormIdeal_le_span_two.mp heven)
      ((L.localIntegralForm 2).self_mem_normIdeal x)
  have hdet' : IsUnit ((L.localIntegralForm 2).toMatrix b).det := by
    exact L.det_toMatrix_localIntegralForm 2 c ▸ hdet
  exact LinearMap.BilinForm.IsSymm.exists_binary_isPerfPair_isCompl_orthogonal
    (L.localIntegralForm 2) (L.isSymm_localIntegralForm 2) b heven'
      (mem_nonunits_iff.mp PadicInt.p_nonunit) hdet'

end TauCeti.IntegralLattice

end
