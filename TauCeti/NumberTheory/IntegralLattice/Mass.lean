/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.ClassNumber
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.ProperClass
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The mass and the proper mass of a genus

For an integral lattice `L` in a rational space `V`, the **mass** of its genus is

  `m(L) = ∑_{cls M ∈ gen L} 1 / |O(M)|`,

the sum over the classes in the genus of `L` (`TauCeti.IntegralLattice.genusClasses`), and the
**proper mass** is

  `m⁺(L) = ∑_{cls⁺ M ∈ gen L} 1 / |SO(M)|`,

the sum over the proper classes of the lattices in the genus. Both are sums over finite sets when
the genus contains finitely many classes, which holds for definite lattices
(`TauCeti.IntegralLattice.IsPosDef.finite_genusClasses`) and in rank at most one. They are defined
for every lattice, through `finsum`, and the comparison theorems carry the finiteness of the genus
as a hypothesis. A class with infinite isometry group contributes `0`, because `Nat.card` of an
infinite type is `0` and `0⁻¹ = 0`. This happens for every degenerate lattice of rank at least two,
whose shears along the radical are isometries, and for many indefinite lattices, although some
indefinite lattices (such as the hyperbolic plane `xy`, with four isometries) have finite isometry
groups. So the masses have their classical meaning only for definite lattices, where the isometry
groups are always finite.

In positive rank the two masses are related by `m⁺ = 2m`
(`TauCeti.IntegralLattice.properMass_eq_two_mul_mass`). A class `cls M` of the genus either is a
single proper class, when `M` has an improper automorphism and `|O(M)| = 2 |SO(M)|`, or splits
into two proper classes, when `O(M) = SO(M)`; in both cases it contributes `2 / |O(M)|` to the
proper mass. The relation fails in rank zero, where the only lattice is the zero lattice and
`m⁺ = m = 1`. In rank one the genus of `L` is the class of `L` and `O(L) = {±1}`, so `m = 1/2` and
`m⁺ = 1`.

There is no product formula for the mass of an orthogonal sum: the genus of `L ⊕ M` can contain
classes that are not orthogonal sums of classes from the genera of `L` and `M`, such as `D₁₆⁺` in
the genus of `E₈ ⊕ E₈`.

## Main definitions

* `TauCeti.IntegralLattice.properGenusClasses`: the proper classes in the genus of `L`.
* `TauCeti.IntegralLattice.mass`: the mass `m(L)` of the genus of `L`.
* `TauCeti.IntegralLattice.properMass`: the proper mass `m⁺(L)` of the genus of `L`.

## Main results

* `TauCeti.IntegralLattice.finite_properGenusClasses_iff`: the genus has finitely many proper
  classes exactly when it has finitely many classes.
* `TauCeti.IntegralLattice.properMass_eq_two_mul_mass`: in positive rank, `m⁺ = 2m`.
* `TauCeti.IntegralLattice.mass_eq_one_of_finrank_eq_zero` and
  `TauCeti.IntegralLattice.properMass_eq_one_of_finrank_eq_zero`: in rank zero, `m = m⁺ = 1`.
* `TauCeti.IntegralLattice.mass_eq_inv_two_of_finrank_eq_one` and
  `TauCeti.IntegralLattice.properMass_eq_one_of_finrank_eq_one`: in rank one, `m = 1/2` and
  `m⁺ = 1`.

## References

* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), §2, equation (1), and §§3, 6, for the low-rank values.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} {W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L M : IntegralLattice V}

section ProperGenusClasses

/-- The proper classes in the genus of `L`: the proper classes of the lattices in the ambient
space of `L` which have the same genus as `L`. -/
def properGenusClasses (L : IntegralLattice V) : Set (ProperIsometryQuotient V) :=
  ProperIsometryQuotient.toIsometryQuotient ⁻¹' L.genusClasses

/-- A proper class lies in the genus of `L` exactly when its class does. -/
theorem mem_properGenusClasses_iff {c : ProperIsometryQuotient V} :
    c ∈ L.properGenusClasses ↔ c.toIsometryQuotient ∈ L.genusClasses :=
  Iff.rfl

/-- The proper class of `M` lies in the genus of `L` exactly when `M` has the same genus as
`L`. -/
@[simp]
theorem properIsometryClass_mem_properGenusClasses_iff :
    M.properIsometryClass ∈ L.properGenusClasses ↔ L.SameGenus M := by
  rw [mem_properGenusClasses_iff, toIsometryQuotient_properIsometryClass,
    isometryClass_mem_genusClasses_iff]

/-- Lattices of the same genus have the same proper classes in their genus. -/
theorem SameGenus.properGenusClasses_eq (h : L.SameGenus M) :
    L.properGenusClasses = M.properGenusClasses := by
  rw [properGenusClasses, properGenusClasses, h.genusClasses_eq]

/-- Every class in the genus of `L` is the class of a proper class in the genus of `L`. -/
theorem image_toIsometryQuotient_properGenusClasses (L : IntegralLattice V) :
    ProperIsometryQuotient.toIsometryQuotient '' L.properGenusClasses = L.genusClasses :=
  Set.image_preimage_eq _ ProperIsometryQuotient.toIsometryQuotient_surjective

/-- The genus of `L` contains finitely many proper classes exactly when it contains finitely many
classes. -/
theorem finite_properGenusClasses_iff : L.properGenusClasses.Finite ↔ L.genusClasses.Finite := by
  refine ⟨fun h ↦ L.image_toIsometryQuotient_properGenusClasses ▸ h.image _, fun h ↦ ?_⟩
  exact h.preimage' fun c _ ↦ finite_preimage_toIsometryQuotient c

end ProperGenusClasses

section Mass

/-- The **mass** of the genus of `L`: the sum of `1 / |O(M)|` over the classes `cls M` in the genus
of `L`. It is a finite sum when the genus contains finitely many classes.

Since `Nat.card` of an infinite type is `0` and `0⁻¹ = 0`, a class whose isometry group is infinite
contributes `0`, and `finsum` makes the mass of a genus with infinitely many classes `0`. The mass
therefore has its classical meaning only for definite lattices, where `O(M)` is finite. -/
noncomputable def mass (L : IntegralLattice V) : ℚ :=
  ∑ᶠ c ∈ L.genusClasses, ((Nat.card (Isometry c.out c.out) : ℚ))⁻¹

/-- The **proper mass** of the genus of `L`: the sum of `1 / |SO(M)|` over the proper classes
`cls⁺ M` of the lattices `M` in the genus of `L`.

As for `TauCeti.IntegralLattice.mass`, a proper class whose special isometry group is infinite
contributes `0`, and a genus with infinitely many proper classes has proper mass `0`, so the
proper mass has its classical meaning only for definite lattices. -/
noncomputable def properMass (L : IntegralLattice V) : ℚ :=
  ∑ᶠ c ∈ L.properGenusClasses, ((Nat.card (specialOrthogonalGroup c.out) : ℚ))⁻¹

theorem mass_def (L : IntegralLattice V) :
    L.mass = ∑ᶠ c ∈ L.genusClasses, ((Nat.card (Isometry c.out c.out) : ℚ))⁻¹ :=
  (rfl)

theorem properMass_def (L : IntegralLattice V) :
    L.properMass =
      ∑ᶠ c ∈ L.properGenusClasses, ((Nat.card (specialOrthogonalGroup c.out) : ℚ))⁻¹ :=
  (rfl)

/-- **The mass is an invariant of the genus.** Lattices of the same genus have the same mass, even
when they live in different ambient spaces. -/
theorem SameGenus.mass_eq {M : IntegralLattice W} (h : L.SameGenus M) : L.mass = M.mass := by
  obtain ⟨f⟩ := h.nonempty_linearEquiv
  refine finsum_mem_eq_of_bijOn (isometryQuotientEquiv f)
    ((Equiv.image_eq_iff_bijOn _).mp <| Set.ext fun c ↦ by
      rw [Set.mem_image_equiv, ← isometryQuotientEquiv_mem_genusClasses_iff f h,
        Equiv.apply_symm_apply]) fun c _ ↦ ?_
  obtain ⟨e⟩ := c.nonempty_isometry_transport_out f
  rw [((c.out.transportIsometry f).trans e).natCard_isometry_eq]

/-- **The proper mass is an invariant of the genus.** Lattices of the same genus have the same
proper mass, even when they live in different ambient spaces. -/
theorem SameGenus.properMass_eq {M : IntegralLattice W} (h : L.SameGenus M) :
    L.properMass = M.properMass := by
  obtain ⟨f⟩ := h.nonempty_linearEquiv
  refine finsum_mem_eq_of_bijOn (properIsometryQuotientEquiv f)
    ((Equiv.image_eq_iff_bijOn _).mp <| Set.ext fun d ↦ ?_) fun d _ ↦ ?_
  · rw [Set.mem_image_equiv, mem_properGenusClasses_iff, mem_properGenusClasses_iff,
      ← isometryQuotientEquiv_mem_genusClasses_iff f h,
      ← toIsometryQuotient_properIsometryQuotientEquiv, Equiv.apply_symm_apply]
  · obtain ⟨e, -⟩ := d.exists_isProper_transport_out f
    rw [((d.out.transportIsometry f).trans e).natCard_specialOrthogonalGroup_eq]

/-- A class of the genus contributes `2 / |O(M)|` to the proper mass: it splits into
`2 / [O(M) : SO(M)]` proper classes, each contributing `1 / |SO(M)|`. -/
private theorem ncard_mul_inv_natCard_specialOrthogonalGroup (hV : 0 < finrank ℚ V)
    (c : IsometryQuotient V) :
    ((ProperIsometryQuotient.toIsometryQuotient ⁻¹' {c}).ncard : ℚ) *
        ((Nat.card (specialOrthogonalGroup c.out) : ℚ))⁻¹ =
      2 * ((Nat.card (Isometry c.out c.out) : ℚ))⁻¹ := by
  have h := ncard_preimage_toIsometryQuotient_mul_index hV c.out
  rw [isometryClass_out] at h
  have hi : ((specialOrthogonalGroup c.out).index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h₀ ↦ by rw [h₀, mul_zero] at h; omega
  have h' : ((ProperIsometryQuotient.toIsometryQuotient ⁻¹' {c}).ncard : ℚ) *
      (specialOrthogonalGroup c.out).index = 2 := by
    exact_mod_cast h
  rw [← (specialOrthogonalGroup c.out).card_mul_index, Nat.cast_mul, ← h']
  field_simp

/-- **The proper mass is twice the mass** in positive rank, for a genus with finitely many
classes. -/
theorem properMass_eq_two_mul_mass (hL : L.genusClasses.Finite) (hn : 0 < finrank ℤ L) :
    L.properMass = 2 * L.mass := by
  classical
  have hV : 0 < finrank ℚ V := L.finrank_carrier ▸ hn
  have hP := finite_properGenusClasses_iff.mpr hL
  rw [properMass_def, mass_def, finsum_mem_eq_finite_toFinset_sum _ hP,
    finsum_mem_eq_finite_toFinset_sum _ hL, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (g := ProperIsometryQuotient.toIsometryQuotient)
      (t := hL.toFinset) fun d hd ↦ by simpa [mem_properGenusClasses_iff] using hd]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  -- Every proper class over `c` has a special isometry group of the same order as `c.out`.
  have hfib : ∀ d ∈ {d ∈ hP.toFinset | d.toIsometryQuotient = c},
      ((Nat.card (specialOrthogonalGroup d.out) : ℚ))⁻¹ =
        ((Nat.card (specialOrthogonalGroup c.out) : ℚ))⁻¹ := by
    intro d hd
    obtain ⟨e⟩ := d.nonempty_isometry_out
    rw [(Finset.mem_filter.mp hd).2] at e
    rw [e.natCard_specialOrthogonalGroup_eq]
  have hcard : (({d ∈ hP.toFinset | d.toIsometryQuotient = c} : Finset _) :
      Set (ProperIsometryQuotient V)) = ProperIsometryQuotient.toIsometryQuotient ⁻¹' {c} := by
    ext d
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff]
    refine ⟨fun hd ↦ hd.2, fun hd ↦ ⟨mem_properGenusClasses_iff.mpr ?_, hd⟩⟩
    rw [hd]
    exact hL.mem_toFinset.mp hc
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hcard,
    ncard_mul_inv_natCard_specialOrthogonalGroup hV c]

end Mass

section LowRank

/-- In rank zero the mass is `1`: the genus is the single class of the zero lattice, whose
isometry group is trivial. -/
theorem mass_eq_one_of_finrank_eq_zero (h : finrank ℤ L = 0) : L.mass = 1 := by
  have := subsingleton_of_finrank_eq_zero h
  rw [mass_def, genusClasses_eq_singleton_of_finrank_le_one (h.trans_le zero_le_one),
    finsum_mem_singleton, Nat.card_unique, Nat.cast_one, inv_one]

/-- In rank zero the proper mass is `1`, so `m⁺ = 2m` fails there. -/
theorem properMass_eq_one_of_finrank_eq_zero (h : finrank ℤ L = 0) : L.properMass = 1 := by
  have := subsingleton_of_finrank_eq_zero h
  have hP : L.properGenusClasses = {L.properIsometryClass} :=
    Set.Subsingleton.eq_singleton_of_mem Set.subsingleton_of_subsingleton
      (properIsometryClass_mem_properGenusClasses_iff.mpr (SameGenus.refl L))
  rw [properMass_def, hP, finsum_mem_singleton, Nat.card_unique, Nat.cast_one, inv_one]

/-- In rank one the mass is `1/2`: the genus is the single class of `L`, and `O(L) = {±1}`. -/
theorem mass_eq_inv_two_of_finrank_eq_one (h : finrank ℤ L = 1) : L.mass = 2⁻¹ := by
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp (isometryClass_out L.isometryClass)
  rw [mass_def, genusClasses_eq_singleton_of_finrank_le_one h.le, finsum_mem_singleton,
    e.natCard_isometry_eq, natCard_isometry_of_finrank_eq_one h, Nat.cast_ofNat]

/-- In rank one the proper mass is `1`. -/
theorem properMass_eq_one_of_finrank_eq_one (h : finrank ℤ L = 1) : L.properMass = 1 := by
  rw [properMass_eq_two_mul_mass ((genusClasses_eq_singleton_of_finrank_le_one h.le) ▸
      Set.finite_singleton _) (h ▸ one_pos), mass_eq_inv_two_of_finrank_eq_one h,
    mul_inv_cancel₀ two_ne_zero]

end LowRank

end TauCeti.IntegralLattice
