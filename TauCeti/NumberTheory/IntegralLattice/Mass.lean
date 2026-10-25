/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.ClassNumber
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite

/-!
# The mass and the proper mass of a genus

The mass of the genus of `L` is the sum `m(L) = ∑ 1 / |O(M)|` over the classes `M` in the genus,
and its proper mass is the sum `m⁺(L) = ∑ 1 / |SO(M)|` over the proper classes. These are the
quantities that the Smith–Minkowski–Siegel mass formula evaluates.

Both are defined for every lattice, as `finsum`s, with the conventions of `Nat.card` and of
division by zero: an infinite isometry group contributes `0`, and a genus whose classes with
finite isometry group are infinite in number has mass `0`. For a positive definite lattice the
class set is finite and every isometry group is finite and nonempty, so the masses are honest
finite sums of positive terms, and they are positive.

The two masses are related by `m⁺ = 2m` in positive rank. A class `M` either is a single proper
class, when `M` has an improper isometry and then `|O(M)| = 2|SO(M)|`, or splits into two proper
classes, when `O(M) = SO(M)`; in both cases its proper classes contribute `2 / |O(M)|`
(`TauCeti.IntegralLattice.natCard_fiber_toIsometryQuotient_mul_natCard_isometry`). In rank zero
the relation fails: there `O(L) = SO(L)` is trivial and `m⁺ = m = 1`.

Both masses depend only on the genus, even across ambient spaces.

## Main definitions

* `TauCeti.IntegralLattice.mass`: the mass `m(L) = ∑ 1 / |O(M)|` of the genus of `L`.
* `TauCeti.IntegralLattice.properMass`: the proper mass `m⁺(L) = ∑ 1 / |SO(M)|`.

## Main results

* `TauCeti.IntegralLattice.properMass_eq_two_mul_mass`: `m⁺ = 2m` in positive rank.
* `TauCeti.IntegralLattice.mass_of_finrank_eq_zero` and
  `TauCeti.IntegralLattice.properMass_of_finrank_eq_zero`: `m = m⁺ = 1` in rank zero.
* `TauCeti.IntegralLattice.SameGenus.mass_eq` and `TauCeti.IntegralLattice.SameGenus.properMass_eq`:
  the masses are invariants of the genus.
* `TauCeti.IntegralLattice.IsPosDef.mass_pos` and `TauCeti.IntegralLattice.IsPosDef.properMass_pos`:
  a positive definite genus has positive mass and proper mass.

## References

* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. Roy. Soc. London Ser. A 419 (1988), §2, for the mass and its proper variant.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for classes and proper classes.
-/

public section

open Module

namespace TauCeti.IntegralLattice

open ProperIsometryQuotient

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- The mass `m(L) = ∑ 1 / |O(M)|` of the genus of `L`, summed over the classes `M` in the genus.
An infinite isometry group contributes `0`, and the mass is `0` when infinitely many classes in the
genus have finite isometry group. -/
noncomputable def mass (L : IntegralLattice V) : ℚ :=
  ∑ᶠ c ∈ L.genusClasses, (Nat.card (Isometry c.out c.out) : ℚ)⁻¹

/-- The proper mass `m⁺(L) = ∑ 1 / |SO(M)|` of the genus of `L`, summed over the proper classes `M`
in the genus. An infinite special isometry group contributes `0`, and the proper mass is `0` when
infinitely many proper classes in the genus have finite special isometry group. -/
noncomputable def properMass (L : IntegralLattice V) : ℚ :=
  ∑ᶠ c ∈ L.properGenusClasses, (Nat.card (specialOrthogonalGroup c.out) : ℚ)⁻¹

/-- Unfolding `mass` as a sum over the classes in the genus. -/
theorem mass_def (L : IntegralLattice V) :
    L.mass = ∑ᶠ c ∈ L.genusClasses, (Nat.card (Isometry c.out c.out) : ℚ)⁻¹ :=
  (rfl)

/-- Unfolding `properMass` as a sum over the proper classes in the genus. -/
theorem properMass_def (L : IntegralLattice V) :
    L.properMass = ∑ᶠ c ∈ L.properGenusClasses, (Nat.card (specialOrthogonalGroup c.out) : ℚ)⁻¹ :=
  (rfl)

/-- In positive rank, the proper classes in a class `c` contribute twice as much to the proper
mass as `c` contributes to the mass. -/
private theorem finsum_mem_preimage_toIsometryQuotient_singleton {c : IsometryQuotient V}
    (hc : 0 < finrank ℤ c.out) :
    ∑ᶠ d ∈ toIsometryQuotient ⁻¹' {c}, (Nat.card (specialOrthogonalGroup d.out) : ℚ)⁻¹ =
      2 * (Nat.card (Isometry c.out c.out) : ℚ)⁻¹ := by
  have hfib : toIsometryQuotient ⁻¹' {c} =
      {d : ProperIsometryQuotient V | d.toIsometryQuotient = c.out.isometryClass} := by
    ext d
    simp
  have hfin := finite_fiber_toIsometryQuotient c.out
  rw [← hfib] at hfin
  rw [finsum_mem_congr rfl fun d hd ↦ by
      rw [natCard_specialOrthogonalGroup_out_toIsometryQuotient, Set.eq_of_mem_singleton hd],
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq, hfib]
  have h := natCard_fiber_toIsometryQuotient_mul_natCard_isometry hc
  rw [Set.coe_ofPred] at *
  rcases eq_or_ne (Nat.card (specialOrthogonalGroup c.out)) 0 with h₀ | h₀
  · rw [← (specialOrthogonalGroup c.out).card_mul_index, h₀]
    simp
  · have h₁ : Nat.card (Isometry c.out c.out) ≠ 0 := by
      rw [← (specialOrthogonalGroup c.out).card_mul_index]
      exact mul_ne_zero h₀ (Subgroup.FiniteIndex.index_ne_zero)
    field_simp
    exact_mod_cast h.trans (mul_comm _ _)

/-- **The proper mass is twice the mass in positive rank.** Each class `M` in the genus contributes
`1 / |O(M)|` to the mass, and its one or two proper classes contribute `2 / |O(M)|` to the proper
mass. The identity holds for every lattice of positive rank, including the degenerate cases in
which the conventions of `mass` make both sides `0`. -/
theorem properMass_eq_two_mul_mass {L : IntegralLattice V} (hL : 0 < finrank ℤ L) :
    L.properMass = 2 * L.mass := by
  set f : IsometryQuotient V → ℚ := fun c ↦ (Nat.card (Isometry c.out c.out) : ℚ)⁻¹
  set g : ProperIsometryQuotient V → ℚ := fun d ↦ (Nat.card (specialOrthogonalGroup d.out) : ℚ)⁻¹
  -- A proper class contributes to the proper mass exactly when its class contributes to the mass.
  have hsupp : L.properGenusClasses ∩ Function.support g =
      toIsometryQuotient ⁻¹' (L.genusClasses ∩ Function.support f) := by
    ext d
    simp only [Set.mem_inter_iff, Set.mem_preimage, Function.mem_support, ne_eq, inv_eq_zero,
      Nat.cast_eq_zero, mem_properGenusClasses_iff, g, f,
      natCard_specialOrthogonalGroup_out_toIsometryQuotient,
      ← (specialOrthogonalGroup d.toIsometryQuotient.out).card_mul_index, mul_eq_zero,
      Subgroup.FiniteIndex.index_ne_zero, or_false]
  have hsupp₂ : Function.support (fun c ↦ 2 * f c) = Function.support f := by
    ext c
    simp
  rw [properMass, mass, mul_finsum_mem]
  by_cases hA : (L.genusClasses ∩ Function.support f).Finite
  · rw [← finsum_mem_inter_support, hsupp, ← finsum_mem_inter_support (fun c ↦ 2 * f c), hsupp₂,
      ← Set.biUnion_preimage_singleton,
      finsum_mem_biUnion (Set.pairwiseDisjoint_fiber _ _) hA fun c _ ↦ ?_]
    · exact finsum_mem_congr rfl fun c hc ↦ finsum_mem_preimage_toIsometryQuotient_singleton
        ((mem_genusClasses_iff.mp hc.1).finrank_eq ▸ hL)
    · obtain ⟨M, rfl⟩ := isometryClass_surjective c
      exact finite_fiber_toIsometryQuotient M
  · have hA' : ¬(toIsometryQuotient ⁻¹' (L.genusClasses ∩ Function.support f)).Finite :=
      fun h ↦ hA (by
        simpa only [Set.image_preimage_eq _ toIsometryQuotient_surjective] using
          h.image toIsometryQuotient)
    rw [finsum_mem_eq_zero_of_infinite (by rwa [hsupp]),
      finsum_mem_eq_zero_of_infinite (by rwa [hsupp₂])]

/-- **Rank zero.** In rank zero the genus is a single class with trivial isometry group, so the
mass is `1`. -/
theorem mass_of_finrank_eq_zero {L : IntegralLattice V} (hL : finrank ℤ L = 0) : L.mass = 1 := by
  have : Subsingleton L := Module.finrank_zero_iff.mp hL
  have : Subsingleton (Isometry L L) :=
    ⟨fun e f ↦ Isometry.carrierEquiv_injective (Subsingleton.elim _ _)⟩
  rw [mass, genusClasses_eq_singleton_of_finrank_le_one (hL ▸ zero_le_one), finsum_mem_singleton,
    natCard_isometry_isometryClass_out, Nat.card_unique, Nat.cast_one, inv_one]

/-- **Rank zero.** In rank zero the genus is a single proper class with trivial special isometry
group, so the proper mass is `1`, and not twice the mass. -/
theorem properMass_of_finrank_eq_zero {L : IntegralLattice V} (hL : finrank ℤ L = 0) :
    L.properMass = 1 := by
  have : Subsingleton L := Module.finrank_zero_iff.mp hL
  have : Subsingleton (Isometry L L) :=
    ⟨fun e f ↦ Isometry.carrierEquiv_injective (Subsingleton.elim _ _)⟩
  have hfib : L.properGenusClasses = {L.properIsometryClass} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨by simp [SameGenus.refl], fun c hc ↦ ?_⟩
    rw [mem_properGenusClasses_iff, genusClasses_eq_singleton_of_finrank_le_one (hL ▸ zero_le_one),
      Set.mem_singleton_iff] at hc
    exact subsingleton_fiber_toIsometryQuotient_of_finrank_eq_zero hL hc
      (toIsometryQuotient_properIsometryClass L)
  rw [properMass, hfib, finsum_mem_singleton,
    natCard_specialOrthogonalGroup_properIsometryClass_out,
    Nat.card_of_subsingleton (1 : specialOrthogonalGroup L), Nat.cast_one, inv_one]

/-- **The mass is an invariant of the genus.** Lattices of the same genus have the same mass, even
when they live in different ambient spaces. -/
theorem SameGenus.mass_eq {L : IntegralLattice V} {M : IntegralLattice W} (h : L.SameGenus M) :
    L.mass = M.mass := by
  obtain ⟨f⟩ := h.nonempty_linearEquiv
  have himage : M.genusClasses = isometryQuotientEquiv f '' L.genusClasses := by
    ext c
    rw [← (isometryQuotientEquiv f).apply_symm_apply c, Set.mem_image_equiv,
      Equiv.symm_apply_apply, isometryQuotientEquiv_mem_genusClasses_iff f h]
  rw [mass, mass, himage, finsum_mem_image (isometryQuotientEquiv f).injective.injOn]
  refine finsum_mem_congr rfl fun c _ ↦ ?_
  obtain ⟨N, rfl⟩ := isometryClass_surjective c
  rw [isometryQuotientEquiv_isometryClass, natCard_isometry_isometryClass_out,
    natCard_isometry_isometryClass_out, (N.transportIsometry f).natCard_eq]

/-- **The proper mass is an invariant of the genus.** Lattices of the same genus have the same
proper mass, even when they live in different ambient spaces. -/
theorem SameGenus.properMass_eq {L : IntegralLattice V} {M : IntegralLattice W}
    (h : L.SameGenus M) : L.properMass = M.properMass := by
  rcases (finrank ℤ L).eq_zero_or_pos with hL | hL
  · rw [properMass_of_finrank_eq_zero hL, properMass_of_finrank_eq_zero (h.finrank_eq ▸ hL)]
  · rw [properMass_eq_two_mul_mass hL, properMass_eq_two_mul_mass (h.finrank_eq ▸ hL), h.mass_eq]

/-- **A positive definite genus has positive mass.** Its class set is finite, and every class has
a finite nonempty isometry group. -/
theorem IsPosDef.mass_pos {L : IntegralLattice V} (hL : L.IsPosDef) : 0 < L.mass := by
  have hO (c : IsometryQuotient V) (hc : c ∈ L.genusClasses) :
      0 < (Nat.card (Isometry c.out c.out) : ℚ)⁻¹ := by
    have := ((mem_genusClasses_iff.mp hc).isPosDef_iff.mp hL).finite_isometry (L := c.out)
    have : Nonempty (Isometry c.out c.out) := ⟨Isometry.refl _⟩
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  exact finsum_cond_pos (fun c hc ↦ (hO c hc).le)
    ⟨_, L.isometryClass_mem_genusClasses, hO _ L.isometryClass_mem_genusClasses⟩
    (hL.finite_genusClasses.subset Set.inter_subset_right)

/-- **A positive definite genus has positive proper mass.** -/
theorem IsPosDef.properMass_pos {L : IntegralLattice V} (hL : L.IsPosDef) : 0 < L.properMass := by
  rcases (finrank ℤ L).eq_zero_or_pos with h | h
  · rw [properMass_of_finrank_eq_zero h]
    exact one_pos
  · rw [properMass_eq_two_mul_mass h]
    exact mul_pos two_pos hL.mass_pos

end TauCeti.IntegralLattice
