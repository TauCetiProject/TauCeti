/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Res
import TauCeti.GroupTheory.Solvable
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction

/-!
# Bounding `H²` of a finite solvable group from its cyclic subquotients

Let `A` be a representation of a finite solvable group `G`. Suppose that `H¹(H, A) = 0` for every
subgroup `H` of `G`, and that for every normal subgroup `N` of prime index in such an `H` the
order of `H²(H ⧸ N, A^N)` divides `[H : N]`. Then the order of `H²(G, A)` divides `#G`
(`natCard_groupCohomology_two_dvd_natCard`); in particular `H²(G, A)` is finite.

This is how the upper bound `#H²(Gal(L/K), Lˣ) ≤ [L : K]` for a finite Galois extension of local
fields is reduced to cyclic extensions of prime degree: `Gal(L/K)` is solvable, Hilbert's
Theorem 90 gives the vanishing of `H¹`, and the cyclic case is a Herbrand quotient computation.

## Main statements

* `TauCeti.groupCohomology.natCard_groupCohomology_two_dvd_natCard`: the order of `H²(G, A)`
  divides `#G`.

## References

* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VI, §1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter III, §2.
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/- The proof is by induction on `#H`. A nontrivial finite solvable group `H` has a normal subgroup
`N` of prime index (`Group.IsSolvable.exists_normal_index_prime`). Since `H¹(N, A) = 0`, the
inflation-restriction sequence `0 ⟶ H²(H ⧸ N, A^N) ⟶ H²(H, A) ⟶ H²(N, A)` is exact, so the order
of `H²(H, A)` divides `[H : N] * #H²(N, A)`, and `#H²(N, A)` divides `#N` by induction.

The subgroups of `G` enter through injective homomorphisms `H →* G` rather than through
`Subgroup G`. A subgroup of a subgroup is then again such a homomorphism, by composition, and the
induction needs no identification of `Subgroup ↥H` with a subgroup of `G`. -/

/-- The induction behind `natCard_groupCohomology_two_dvd_natCard`, on the order `n` of a group
`H` mapping injectively to `G`. -/
private theorem natCard_groupCohomology_two_res_dvd [Finite G] [Group.IsSolvable G]
    (A : Rep k G)
    (h1 : ∀ (H : Type u) [Group H] (f : H →* G), Function.Injective f →
      IsZero (groupCohomology (res f A) 1))
    (hcyc : ∀ (H : Type u) [Group H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        Nat.card (groupCohomology ((res f A).quotientToInvariants N) 2) ∣ N.index)
    (n : ℕ) : ∀ (H : Type u) [Group H] (f : H →* G), Function.Injective f → Nat.card H = n →
      Nat.card (groupCohomology (res f A) 2) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ f hf hn
  have : Finite H := Finite.of_injective f hf
  have : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective hf
  rcases subsingleton_or_nontrivial H with hH | hH
  · -- the cohomology of the trivial group vanishes in positive degree
    have := ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton (res f A) 1)
    rw [Nat.card_unique]
    exact one_dvd n
  obtain ⟨N, hN, hp⟩ := Group.IsSolvable.exists_normal_index_prime H
  have hfN : Function.Injective (f.comp N.subtype) := hf.comp Subtype.val_injective
  -- Restricting along a composite is restricting twice, definitionally: both sides are the
  -- representation `A.ρ.comp (f.comp N.subtype)` on `A.V`.
  have hres : res (f.comp N.subtype) A = res N.subtype (res f A) := rfl
  have hcard : Nat.card N * N.index = n := hn ▸ N.card_mul_index
  have hlt : Nat.card N < n := by
    have := hp.two_le
    have : 0 < Nat.card N := Nat.card_pos
    nlinarith
  refine (natCard_groupCohomology_succ_dvd_mul (res f A) (S := N) 1 fun i hi => ?_).trans ?_
  · obtain rfl : i = 0 := by omega
    exact hres ▸ h1 N _ hfN
  · rw [← hcard, mul_comm (Nat.card N)]
    exact mul_dvd_mul (hcyc H f hf N hp) (hres ▸ ih _ hlt N _ hfN rfl)

/-- **`H²` of a finite solvable group is bounded by its cyclic subquotients.** Let `A` be a
representation of a finite solvable group `G`. Suppose that `H¹(H, A) = 0` for every subgroup `H`
of `G` (given as an injective homomorphism `f : H →* G`), and that for every normal subgroup `N`
of prime index in such an `H`, the order of `H²(H ⧸ N, A^N)` divides `[H : N]`. Then the order of
`H²(G, A)` divides `#G`; in particular `H²(G, A)` is finite. -/
theorem natCard_groupCohomology_two_dvd_natCard [Finite G] [Group.IsSolvable G] (A : Rep k G)
    (h1 : ∀ (H : Type u) [Group H] (f : H →* G), Function.Injective f →
      IsZero (groupCohomology (res f A) 1))
    (hcyc : ∀ (H : Type u) [Group H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        Nat.card (groupCohomology ((res f A).quotientToInvariants N) 2) ∣ N.index) :
    Nat.card (groupCohomology A 2) ∣ Nat.card G := by
  have h := natCard_groupCohomology_two_res_dvd A h1 hcyc _ G (MonoidHom.id G)
    Function.injective_id rfl
  rwa [res_id] at h

end TauCeti.groupCohomology
