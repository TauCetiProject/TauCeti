/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import TauCeti.RingTheory.FittingIdeal.BaseChange

/-!
# Fibre dimensions under change of scalars

The dimension of the fibre of a finite module is unchanged by extending its residue field.
In particular, the fibre dimension function of a base-changed module is the pullback of the
original dimension function on prime spectra. No flatness of the change of scalars is needed.

These statements use the fibre-dimension characterization of Fitting ideals.
-/

public section

open TensorProduct Module

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Extending the residue field does not change the dimension of the fibre of a finite module.
The field `K` may be any `R`-algebra whose structure map has kernel `p`. -/
theorem finrank_tensorProduct_eq_finrank_fiber (K : Type*) [Field K] [Algebra R K]
    (hK : RingHom.ker (algebraMap R K) = p) :
    finrank K (K ⊗[R] M) = finrank p.ResidueField (p.Fiber M) := by
  apply eq_of_forall_lt_iff
  intro n
  rw [← TauCeti.fittingIdeal_map_eq_bot_iff_lt_finrank,
    Ideal.map_eq_bot_iff_le_ker, hK, TauCeti.fittingIdeal_le_iff_lt_finrank]

variable {M}

/-- Fibre dimensions commute with arbitrary base change of the ring: the fibre over `q` of
`S ⊗[R] M` has the same dimension as the fibre of `M` at the inverse image of `q`. -/
theorem finrank_fiber_baseChange {S : Type*} [CommRing S] [Algebra R S] (q : Ideal S)
    [q.IsPrime] :
    finrank q.ResidueField (q.Fiber (S ⊗[R] M)) =
      finrank (q.comap (algebraMap R S)).ResidueField
        ((q.comap (algebraMap R S)).Fiber M) := by
  apply eq_of_forall_lt_iff
  intro n
  rw [← TauCeti.fittingIdeal_le_iff_lt_finrank,
    ← TauCeti.fittingIdeal_le_iff_lt_finrank,
    TauCeti.fittingIdeal_baseChange, Ideal.map_le_iff_le_comap]

end Ideal
