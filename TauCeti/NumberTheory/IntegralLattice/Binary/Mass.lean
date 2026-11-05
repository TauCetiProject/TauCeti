/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.ClassNumber
public import TauCeti.NumberTheory.IntegralLattice.Binary.Genus
public import TauCeti.NumberTheory.IntegralLattice.Binary.NormOne
public import TauCeti.NumberTheory.IntegralLattice.Mass

/-!
# The mass of a definite binary genus

Let `L` be a rank-two lattice of negative primitive discriminant `Δ`, that is, a positive or
negative definite binary lattice, and let `w = #𝒪(L)ˣ` be the number of units of its quadratic
order `𝒪(L) = ℤ[(Δ + √Δ)/2]`: `6` for `Δ = -3`, `4` for `Δ = -4` and `2` otherwise. Every lattice
`M` of the genus of `L` has the same primitive discriminant, hence `|SO(M)| = w`, so the proper
mass of the genus is

  `m⁺(L) = h⁺(L) / w`,

where `h⁺(L)` is the proper class number. As `m⁺ = 2m` in positive rank, the mass is

  `m(L) = h⁺(L) / (2w)`.

It is the proper class number, not the class number `h(L)`, that enters the mass, because `|O(M)|`
is not constant on the genus: it is `2w` when `M` has an improper automorphism and `w` otherwise.
Writing `a` for the number of classes of the first kind, `h⁺ + a = 2h`
(`TauCeti.IntegralLattice.properClassNumber_add_card_eq_two_mul_classNumber`), and the mass does
not depend on `a`. Classically, the genus of the lattice `!![4, 1; 1, 6]` of determinant `23` has
`Δ = -23`, `w = 2`, `h⁺ = 3` and `a = 1`, so `h = 2` and its mass is `3/4 = h⁺/(2w)` rather than
`h/(2w) = 1/2`; these class counts are not formalized here.

## Main results

* `TauCeti.IntegralLattice.SameGenus.natCard_specialOrthogonalGroup_eq_of_binaryDiscriminant_neg`:
  in a genus of negative primitive discriminant, every special orthogonal group has `w` elements.
* `TauCeti.IntegralLattice.properMass_eq_properClassNumber_div_of_binaryDiscriminant_neg`:
  `m⁺ = h⁺ / w`.
* `TauCeti.IntegralLattice.mass_eq_properClassNumber_div_of_binaryDiscriminant_neg`:
  `m = h⁺ / (2w)`.

## References

* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), §2, equation (1), for the mass and the proper mass.
* D. A. Cox, *Primes of the Form x² + ny²*, §2 and §7, for proper classes of binary forms and
  the units of quadratic orders.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} (hV : finrank ℚ V = 2)

/-- In a genus of negative primitive discriminant, every lattice has as many proper isometries as
there are units in the quadratic order of `L`. -/
theorem SameGenus.natCard_specialOrthogonalGroup_eq_of_binaryDiscriminant_neg
    {M : IntegralLattice W} (h : L.SameGenus M) (hneg : L.binaryDiscriminant hV < 0) :
    Nat.card (specialOrthogonalGroup M) = Nat.card (L.binaryOrder hV)ˣ := by
  have hW : finrank ℚ W = 2 := by
    rw [← M.finrank_carrier, ← h.finrank_eq, L.finrank_carrier, hV]
  have hΔ := h.binaryDiscriminant_eq hV hW
  rw [card_specialOrthogonalGroup_of_binaryDiscriminant_neg hW (hΔ ▸ hneg), binaryOrder_def,
    binaryOrder_def, QuadraticOrder.card_units_of_neg _ _ (hΔ ▸ hneg),
    QuadraticOrder.card_units_of_neg _ _ hneg, hΔ]

/-- **The proper mass of a definite binary genus.** For a rank-two lattice of negative primitive
discriminant, `m⁺ = h⁺ / w`, where `h⁺` is the proper class number and `w` the number of units of
the quadratic order of `L`. -/
theorem properMass_eq_properClassNumber_div_of_binaryDiscriminant_neg
    (hneg : L.binaryDiscriminant hV < 0) :
    L.properMass = L.properClassNumber / Nat.card (L.binaryOrder hV)ˣ := by
  have := L.isNondegenerate_of_binaryDiscriminant_ne_zero hV hneg.ne
  have hfin := finite_genusProperClasses_iff.mpr
    (finite_genusClasses_of_finrank_eq_two (L.finrank_carrier.trans hV))
  have hw (c) (hc : c ∈ L.genusProperClasses) :
      ((Nat.card (specialOrthogonalGroup c.out) : ℚ))⁻¹ =
        (Nat.card (L.binaryOrder hV)ˣ : ℚ)⁻¹ := by
    rw [← properIsometryClass_out c, properIsometryClass_mem_genusProperClasses_iff] at hc
    rw [hc.natCard_specialOrthogonalGroup_eq_of_binaryDiscriminant_neg hV hneg]
  rw [properMass_def, finsum_mem_congr rfl hw, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_const, nsmul_eq_mul, properClassNumber_def, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card _ hfin, div_eq_mul_inv]

/-- **The mass of a definite binary genus.** For a rank-two lattice of negative primitive
discriminant, `m = h⁺ / (2w)`, where `h⁺` is the proper class number and `w` the number of units of
the quadratic order of `L`. -/
theorem mass_eq_properClassNumber_div_of_binaryDiscriminant_neg
    (hneg : L.binaryDiscriminant hV < 0) :
    L.mass = L.properClassNumber / (2 * Nat.card (L.binaryOrder hV)ˣ) := by
  have := L.isNondegenerate_of_binaryDiscriminant_ne_zero hV hneg.ne
  have h := properMass_eq_two_mul_mass
    (finite_genusClasses_of_finrank_eq_two (L.finrank_carrier.trans hV))
    (by rw [L.finrank_carrier, hV]; norm_num)
  rw [properMass_eq_properClassNumber_div_of_binaryDiscriminant_neg hV hneg] at h
  rw [div_mul_eq_div_div_swap, h]
  ring

end TauCeti.IntegralLattice
