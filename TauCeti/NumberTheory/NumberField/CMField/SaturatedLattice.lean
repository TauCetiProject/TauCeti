/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
public import TauCeti.NumberTheory.NumberField.Global.Adeles.SaturatedLattice

/-!
# Discriminants of saturated lattices

Let `E` be a CM field, `𝔸_f` its finite adeles, `Ô` the integral ones, `κ` a finite set and
`m ↦ m^*` the conjugate transpose for the complex conjugation of `𝔸_f`. A lattice `L` of rank `r`
in `𝔸_f^κ` has discriminant `d_r(L) ≥ 1` as soon as `B^*B` is integral for every `κ × r` matrix `B`
with columns in `L` (`NumberField.FiniteAdeleRing.IsLatticeOfRank.one_le_latticeDiscriminant`).
For the saturated lattice of a subspace `U ⊂ E^κ` for an adelic matrix `H` with a left inverse
(`NumberField.FiniteAdeleRing.saturatedLattice`), the columns `m` of such a `B` have `H m`
integral, so `d(U) ≥ 1` if `m^*m` is integral for every `m` with `dim U` columns and `H m`
integral.

## Main declarations

* `NumberField.FiniteAdeleRing.one_le_latticeDiscriminant_saturatedLattice`: the discriminant of a
  saturated lattice is at least `1`.

## References

* The formal proof that the roadmap credits for this statement: the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`New.Filling.one_le_sublatticeDiscriminant` in
  `New/Spanning/RemainingTerms/Discriminants.lean`).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open Matrix
open scoped NumberField.AdeleRing

namespace NumberField.FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {κ : Type*} [Fintype κ]

/-- **Discriminants of saturated lattices.** Let `H` be an adelic matrix with a left inverse such
that `m^*m` is integral for every `κ × dim U` adelic matrix `m` with `H m` integral. Then the
saturated lattice of `U` for `H` has discriminant at least `1`. -/
theorem one_le_latticeDiscriminant_saturatedLattice {ι : Type*} [Fintype ι] [DecidableEq κ]
    {U : Submodule E (κ → E)} {H : Matrix ι κ 𝔸ᶠ[E]} (hH : ∃ H' : Matrix κ ι 𝔸ᶠ[E], H' * H = 1)
    (hm : ∀ m : Matrix κ (Fin (Module.finrank E U)) 𝔸ᶠ[E],
      (∀ i j, (H * m) i j ∈ integralAdeles (𝓞 E) E) →
        ∀ i j, ((m.map (finiteAdeleConj E))ᵀ * m) i j ∈ integralAdeles (𝓞 E) E) :
    1 ≤ latticeDiscriminant (Module.finrank E U) (saturatedLattice U H) :=
  (isLatticeOfRank_saturatedLattice hH).one_le_latticeDiscriminant fun B hB ↦
    hm B fun i j ↦ (mem_saturatedLattice.1 (hB j)).2 i

end NumberField.FiniteAdeleRing
