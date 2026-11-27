/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.Veronese
public import TauCeti.NumberTheory.ArithmeticStatistics.FormDensity.Basic

/-!
# Coefficient-vector forms and the projective Veronese map

In `N` variables, the degree-`d` monomials `FormDensity.Monomials (Fin N) d` are the exponent
vectors that `TauCeti.veroneseExponentEquiv` enumerates in lexicographic order. This file records
that identification,
`FormDensity.veroneseDimEquiv N d : Fin (veroneseDim N d) ≃ Monomials (Fin N) d`, so that the
two indexings of the Veronese vector agree:

* `FormDensity.veronese_veroneseDimEquiv`: reindexed along `veroneseDimEquiv`, the Veronese
  vector `FormDensity.veronese v` is the vector of monomials `TauCeti.veroneseMonomials d v`;
* `FormDensity.veroneseDim_eq_choose`: stars and bars gives the number of monomials,
  `veroneseDim N d = binom(N + d - 1, d)`.
-/

public section

open Finset

namespace TauCeti.FormDensity

variable (N d : ℕ)

/-- The lexicographic enumeration `Fin (veroneseDim N d)` of the exponent vectors of degree `d` in
`N` variables, as an enumeration of `Monomials (Fin N) d`. -/
noncomputable def veroneseDimEquiv : Fin (veroneseDim N d) ≃ Monomials (Fin N) d :=
  (veroneseExponentEquiv N d).trans <| Finsupp.equivFunOnFinite.symm.subtypeEquiv fun α ↦ by
    simp [Finsupp.degree_eq_sum]

/-- The monomial enumerated by `veroneseDimEquiv` has the exponent vector `veroneseExponent`. -/
@[simp]
theorem coe_veroneseDimEquiv_apply (k : Fin (veroneseDim N d)) :
    ⇑(veroneseDimEquiv N d k : Fin N →₀ ℕ) = veroneseExponent N d k := by
  simp [veroneseDimEquiv]

/-- There are as many lexicographically enumerated exponent vectors as degree-`d` monomials. -/
theorem veroneseDim_eq_card_monomials : veroneseDim N d = #(Monomials (Fin N) d) := by
  simpa using Fintype.card_congr (veroneseDimEquiv N d)

/-- **Stars and bars.** There are `binom(N + d - 1, d)` monomials of degree `d` in `N`
variables. -/
theorem veroneseDim_eq_choose : veroneseDim N d = (N + d - 1).choose d := by
  rw [veroneseDim_eq_card_monomials, card_monomials, Fintype.card_fin]

variable {N d}

/-- Reindexed along `veroneseDimEquiv`, the Veronese vector of `v` is the vector of its
degree-`d` monomials. -/
theorem veronese_veroneseDimEquiv {R : Type*} [CommSemiring R] (v : Fin N → R)
    (k : Fin (veroneseDim N d)) :
    veronese v (veroneseDimEquiv N d k) = veroneseMonomials d v k := by
  simp

end TauCeti.FormDensity
