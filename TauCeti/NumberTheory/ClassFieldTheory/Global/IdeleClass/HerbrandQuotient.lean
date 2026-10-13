/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Finite
import TauCeti.NumberTheory.ClassFieldTheory.Global.OrdinaryUnits
import TauCeti.NumberTheory.ClassFieldTheory.Global.SUnitsCohomology
import TauCeti.NumberTheory.ClassFieldTheory.Global.Units
import TauCeti.NumberTheory.NumberField.Global.Ideles.Support

/-!
# The Herbrand quotient of the idele classes of a cyclic extension

Let `L/K` be a cyclic extension of number fields. This file proves that the idele class group
`C_L`, as a representation of `Gal(L/K)`, has Herbrand quotient

```text
h(C_L) = [L : K]
```

(`herbrandQuotient_ideleClassRep_eq_finrank`). Since `h(C_L) = #Ĥ⁰ / #Ĥ⁻¹` and the degree-zero
Tate group is `C_L^G / N_G C_L`, this is the source of the first fundamental inequality
`[C_K : N_{L/K} C_L] ≥ [L : K]` for cyclic extensions; the passage from a Herbrand quotient to the
norm index of a cyclic layer of a formation is
`TauCeti.ClassFieldTheory.NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq`.

The proof chooses a finite set `S` of finite places of `K` outside which `L/K` is unramified and
whose primes above generate the ideal class group of `L`, and reads off the Herbrand quotients of
the terms of `0 → U_{L,S} → I_{L,S} → C_L → 0` (`herbrandQuotient_ideleClassRep`). Writing
`ℤ[S_∞(L)]` and `ℤ[S_L]` for the permutation lattices on the infinite places of `L` and on the
primes of `L` above `S`, these are

```text
h(I_{L,S}) = h(ℤ[S_∞(L)]) · h(ℤ[S_L]),
h(U_{L,S}) = h((𝓞 L)ˣ) · h(ℤ[S_L]) = h(ℤ[S_∞(L)]) / [L : K] · h(ℤ[S_L]),
```

by the local computation `herbrandQuotient_sIdelesRep_eq_herbrandQuotient_ofMulAction`, the
valuation sequence `herbrandQuotient_sUnitsRep_eq_mul` and Dirichlet's unit theorem read
equivariantly, `herbrandQuotient_units_eq_div`. The permutation-lattice factors cancel.

## Main results

* `TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep_eq_finrank`: `h(C_L) = [L : K]`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4 (the first inequality).
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- **The Herbrand quotient of the idele classes.** For a cyclic extension `L/K` of number fields,
the idele class group `C_L`, as a representation of `Gal(L/K)`, has Herbrand quotient
`h(C_L) = [L : K]`. -/
theorem herbrandQuotient_ideleClassRep_eq_finrank :
    TateCohomology.herbrandQuotient (ideleClassRep K L) = Module.finrank K L := by
  obtain ⟨S, hgen, hunram⟩ :=
    GlobalNumberFields.exists_finset_primesAbove_closure_eq_top_and_isUnramified K L
  have := finite_tateCohomology_zero_sUnitsRep (L := L) (S : Set (HeightOneSpectrum (𝓞 K)))
  have := finite_tateCohomology_negOne_sUnitsRep (L := L) (S : Set (HeightOneSpectrum (𝓞 K)))
  have := (finite_tateCohomology_sIdelesRep hunram).2
  have := (primesAbove_finite (𝓞 K) (𝓞 L) S.finite_toSet).to_subtype
  -- the `S`-units have finite Tate groups, so a nonzero Herbrand quotient, which the valuation
  -- sequence factors through that of the permutation lattice on the primes above `S`
  have hU : TateCohomology.herbrandQuotient (sUnitsRep L (S : Set (HeightOneSpectrum (𝓞 K)))) ≠
      0 := by
    simp only [Ne, TateCohomology.herbrandQuotient_eq_zero_iff, not_or, not_infinite_iff_finite]
    exact ⟨inferInstance, inferInstance⟩
  rw [herbrandQuotient_sUnitsRep_eq_mul] at hU
  have hP := right_ne_zero_of_mul hU
  have hA : TateCohomology.herbrandQuotient
      (Rep.ofMulAction ℤ (L ≃ₐ[K] L) (InfinitePlace L)) ≠ 0 := by
    rw [herbrandQuotient_ofMulAction_infinitePlace]
    exact pow_ne_zero _ two_ne_zero
  have hn : (Module.finrank K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [herbrandQuotient_ideleClassRep L hgen,
    herbrandQuotient_sIdelesRep_eq_herbrandQuotient_ofMulAction hunram,
    TateCohomology.herbrandQuotient_ofMulAction_sum, herbrandQuotient_sUnitsRep_eq_mul,
    herbrandQuotient_sUnitsRep_empty, herbrandQuotient_units_eq_div]
  field_simp

end TauCeti.ClassFieldTheory
