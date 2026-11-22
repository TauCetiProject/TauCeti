/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Prime avoidance for the translates of a prime

Let a monoid `G` act on a commutative ring `A` by ring endomorphisms and let `Q` be a prime of `A`.
The preimages `{a | g • a ∈ Q}` are primes, the translates `g⁻¹ • Q` when `G` is a group. If only
finitely many of them occur, prime avoidance gives an element of an ideal outside all of them as
soon as the ideal lies in none of them. For a group `G`, if such an element `u` has finite orbit,
for instance when `G` is finite, its invariant norm, the product of the elements of its orbit, lies
outside `Q`; applied to the annihilator of an invariant, which is `G`-stable, this shows that an
invariant killed by an element outside `Q` is killed by an invariant outside `Q`.

## Main results

* `Ideal.exists_mem_forall_smul_notMem`: prime avoidance for finitely many preimages
  `{a | g • a ∈ Q}` of a prime `Q`.
* `Ideal.exists_notMem_dvd_of_forall_smul_notMem`: for a group `G` acting on a commutative semiring,
  an element with finite orbit outside every `g⁻¹ • Q` divides an invariant outside `Q`.
* `TauCeti.FixedPoints.exists_mul_eq_zero_of_mul_eq_zero`: for a finite group `G`, an invariant
  killed by an element outside a prime `Q` is killed by an invariant outside `Q`.
-/

public section

namespace TauCeti.FixedPoints

/-- **Prime avoidance for the preimages of a prime.** If only finitely many preimages
`{a | g • a ∈ Q}` of a prime `Q` occur, for instance when `G` is finite, and an ideal `I` of `A` is
contained in none of them, then some `u ∈ I` satisfies `g • u ∉ Q` for every `g`. For a group `G`
these preimages are the translates `g⁻¹ • Q`. -/
theorem _root_.Ideal.exists_mem_forall_smul_notMem {G A : Type*} [Monoid G] [CommRing A]
    [MulSemiringAction G A] (Q : Ideal A) [Q.IsPrime]
    (hQ : (Set.range fun g : G ↦ Q.comap (MulSemiringAction.toRingHom G A g)).Finite)
    {I : Ideal A} (hI : ∀ g : G, ¬ I ≤ Q.comap (MulSemiringAction.toRingHom G A g)) :
    ∃ u ∈ I, ∀ g : G, g • u ∉ Q := by
  by_contra! h
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := (Ideal.subset_union_prime_finite hQ (f := id) Q Q
    fun _ ⟨g, hg⟩ _ _ ↦ hg ▸ Ideal.comap_isPrime (MulSemiringAction.toRingHom G A g) Q).mp
      fun u hu ↦ by
        obtain ⟨g, hg⟩ := h u hu
        exact Set.mem_biUnion (Set.mem_range_self g) hg
  exact hI g hg

/-- **Norms of elements avoiding every translate of a prime.** For a group `G`, if the orbit of
`u` is finite and `g • u ∉ Q` for every `g`, then the invariant norm of `u`, the product of the
elements of its orbit, lies outside `Q` and is divisible by `u`. -/
theorem _root_.Ideal.exists_notMem_dvd_of_forall_smul_notMem {G A : Type*} [Group G]
    [CommSemiring A] [MulSemiringAction G A] (Q : Ideal A) [Q.IsPrime] {u : A}
    (hfin : (MulAction.orbit G u).Finite) (hu : ∀ g : G, g • u ∉ Q) :
    ∃ r ∈ FixedPoints.submonoid G A, r ∉ Q ∧ u ∣ r := by
  refine ⟨∏ v ∈ hfin.toFinset, v, fun g ↦ ?_, fun hmem ↦ ?_,
    Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr (MulAction.mem_orbit_self u))⟩
  · -- `g` permutes the orbit of `u`.
    rw [Finset.smul_prod']
    exact Finset.prod_nbij' (g • ·) (g⁻¹ • ·)
      (fun v hv ↦ hfin.mem_toFinset.mpr <|
        MulAction.mapsTo_smul_orbit g u <| hfin.mem_toFinset.mp hv)
      (fun v hv ↦ hfin.mem_toFinset.mpr <|
        MulAction.mapsTo_smul_orbit g⁻¹ u <| hfin.mem_toFinset.mp hv)
      (fun v _ ↦ inv_smul_smul g v) (fun v _ ↦ smul_inv_smul g v) fun _ _ ↦ rfl
  · obtain ⟨v, hv, hvQ⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hmem
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (hfin.mem_toFinset.mp hv)
    exact hu g hvQ

section Group

variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]

/-- If an invariant `x` is killed by an element outside a prime `Q`, it is killed by an invariant
element outside `Q`. This is prime avoidance for the `G`-stable annihilator of `x` and the
finitely many primes `g⁻¹ • Q`. -/
theorem exists_mul_eq_zero_of_mul_eq_zero (Q : Ideal A) [Q.IsPrime] (x : FixedPoints.subring A G)
    {t : A} (htQ : t ∉ Q) (htx : t * x = 0) :
    ∃ s ∈ FixedPoints.subring A G, s ∉ Q ∧ s * x = 0 := by
  set I : Ideal A := (Ideal.span {(x : A)}).annihilator
  have hI (u : A) : u ∈ I ↔ u * x = 0 := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  obtain ⟨u, huI, hu⟩ := Q.exists_mem_forall_smul_notMem (G := G) (I := I) (Set.finite_range _)
    fun g hg ↦ by
      -- The annihilator of `x` is `G`-stable, so it contains `g⁻¹ • t`, and then `t ∈ Q`.
      have hmem : g⁻¹ • t ∈ I := by
        rw [hI, ← x.property g⁻¹, ← smul_mul', htx, smul_zero]
      exact htQ (by simpa using hg hmem)
  obtain ⟨r, hr, hrQ, hur⟩ := Q.exists_notMem_dvd_of_forall_smul_notMem (Set.finite_range _) hu
  exact ⟨r, hr, hrQ, (hI r).mp (I.mem_of_dvd hur huI)⟩

end Group

end TauCeti.FixedPoints
