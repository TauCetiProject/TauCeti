/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Solvable
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Sylow
import Mathlib.GroupTheory.Nilpotent
import TauCeti.GroupTheory.Solvable
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction

/-!
# Reducing `H¹ = 0` and `#H² ∣ #G` to subquotients of prime order

Let `A` be a representation of a finite group `G`. Suppose that for every solvable subgroup `H` of
`G` and every normal subgroup `N` of prime index in `H`,

```text
H¹(H ⧸ N, A^N) = 0    and    #H²(H ⧸ N, A^N) ∣ [H : N].
```

Then `H¹(G, A) = 0` (`isZero_groupCohomology_one_of_prime_index`) and the order of `H²(G, A)`
divides `#G` (`natCard_groupCohomology_two_dvd_natCard_of_prime_index`). No solvability of `G`
is assumed.

This is the Sylow and tower argument by which, for the idele classes `C_L` of a finite Galois
extension `L/K` of number fields, the vanishing of `H¹(Gal(L/K), C_L)` and the second fundamental
inequality in its cohomological form `#H²(Gal(L/K), C_L) ∣ [L : K]` are reduced to cyclic
extensions of prime degree. For those, the two hypotheses follow from the two fundamental
inequalities through the Herbrand quotient.

## Main statements

* `TauCeti.groupCohomology.isZero_groupCohomology_one_of_prime_index`: `H¹(G, A) = 0`.
* `TauCeti.groupCohomology.natCard_groupCohomology_two_dvd_natCard_of_prime_index`: the order of
  `H²(G, A)` divides `#G`; in particular `H²(G, A)` is finite.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §5 (the proof of Theorem 5.1), and
  Chapter II, §1 (restriction to Sylow subgroups and the inflation-restriction sequence).
-/

public section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/- The proof first treats a solvable group by induction on its order: it has a normal subgroup of
prime index, the inflation-restriction sequence `0 ⟶ H¹(H ⧸ N, A^N) ⟶ H¹(H, A) ⟶ H¹(N, A)` is
always exact, and `natCard_groupCohomology_two_dvd_natCard` bounds `H²` once `H¹` vanishes on
every subgroup. A Sylow subgroup is solvable, and the restrictions to one Sylow `p`-subgroup for
each prime `p` together detect every class in positive degree
(`eq_zero_of_map_sylow_eq_zero`). So `H¹(G, A)` vanishes, and `H²(G, A)` embeds in the product
of the `H²(P, A)` over these Sylow subgroups `P`, whose order divides `∏ #P = #G`.

As in `TauCeti.RepresentationTheory.Homological.GroupCohomology.Solvable`, subgroups of `G` enter
through injective homomorphisms `H →* G`, so that a subgroup of a subgroup is again one, by
composition. -/

/-- The solvable case of `isZero_groupCohomology_one_of_prime_index`: `H¹(H, A)` vanishes for
every solvable group `H` of order `n` mapping injectively to `G`. -/
private theorem isZero_groupCohomology_one_res_of_isSolvable [Finite G] (A : Rep k G)
    (h1 : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        IsZero (groupCohomology ((res f A).quotientToInvariants N) 1))
    (n : ℕ) : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G),
      Function.Injective f → Nat.card H = n → IsZero (groupCohomology (res f A) 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ f hf hn
  have : Finite H := Finite.of_injective f hf
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact isZero_groupCohomology_succ_of_subsingleton (res f A) 0
  obtain ⟨N, hN, hp⟩ := Group.IsSolvable.exists_normal_index_prime H
  have hlt : Nat.card N < n := by
    have := hp.two_le
    have : 0 < Nat.card N := Nat.card_pos
    have := hn ▸ N.card_mul_index
    nlinarith
  -- `H¹(H ⧸ N, A^N) ⟶ H¹(H, A) ⟶ H¹(N, A)` is exact with vanishing outer terms
  have hS := infRes_exact (res f A) (S := N) 0 fun i hi => absurd hi (Nat.not_lt_zero i)
  exact hS.isZero_X₂ ((h1 H f hf N hp).eq_of_src _ _)
    ((ih _ hlt N (f.comp N.subtype) (hf.comp Subtype.val_injective) rfl).eq_of_tgt _ _)

/-- The solvable case of `natCard_groupCohomology_two_dvd_natCard_of_prime_index`, for a solvable
group `H` mapping injectively to `G`. -/
private theorem natCard_groupCohomology_two_res_dvd_of_isSolvable [Finite G] (A : Rep k G)
    (h1 : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        IsZero (groupCohomology ((res f A).quotientToInvariants N) 1))
    (h2 : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        Nat.card (groupCohomology ((res f A).quotientToInvariants N) 2) ∣ N.index)
    (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G) (hf : Function.Injective f) :
    Nat.card (groupCohomology (res f A) 2) ∣ Nat.card H := by
  have : Finite H := Finite.of_injective f hf
  refine natCard_groupCohomology_two_dvd_natCard (res f A) (fun H' _ f' hf' => ?_)
    (fun H' _ f' hf' =>
      have := Group.isSolvable_of_isSolvable_injective hf'; h2 H' (f.comp f') (hf.comp hf'))
  have : Group.IsSolvable H' := Group.isSolvable_of_isSolvable_injective hf'
  exact isZero_groupCohomology_one_res_of_isSolvable A h1 _ H' (f.comp f') (hf.comp hf') rfl

/-- **`H¹` vanishes if it does on the subquotients of prime order.** Let `A` be a representation
of a finite group `G`. Suppose that for every solvable subgroup `H` of `G` (given as an injective
homomorphism `f : H →* G`) and every normal subgroup `N` of prime index in `H`,
`H¹(H ⧸ N, A^N) = 0`. Then `H¹(G, A) = 0`. -/
theorem isZero_groupCohomology_one_of_prime_index [Finite G] (A : Rep k G)
    (h1 : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        IsZero (groupCohomology ((res f A).quotientToInvariants N) 1)) :
    IsZero (groupCohomology A 1) := by
  refine isZero_of_isZero_sylow A 0 fun p _ _ => ?_
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have : Group.IsSolvable P := have := P.isPGroup'.isNilpotent; inferInstance
  exact ⟨P, isZero_groupCohomology_one_res_of_isSolvable A h1 _ P (P : Subgroup G).subtype
    Subtype.val_injective rfl⟩

/-- **The order of `H²` divides that of the group if it does on the subquotients of prime
order.** Let `A` be a representation of a finite group `G`. Suppose that for every solvable
subgroup `H` of `G` (given as an injective homomorphism `f : H →* G`) and every normal subgroup `N`
of prime index in `H`, `H¹(H ⧸ N, A^N) = 0` and the order of `H²(H ⧸ N, A^N)` divides `[H : N]`.
Then the order of `H²(G, A)` divides `#G`; in particular `H²(G, A)` is finite. -/
theorem natCard_groupCohomology_two_dvd_natCard_of_prime_index [Finite G] (A : Rep k G)
    (h1 : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        IsZero (groupCohomology ((res f A).quotientToInvariants N) 1))
    (h2 : ∀ (H : Type u) [Group H] [Group.IsSolvable H] (f : H →* G), Function.Injective f →
      ∀ (N : Subgroup H) [N.Normal], N.index.Prime →
        Nat.card (groupCohomology ((res f A).quotientToInvariants N) 2) ∣ N.index) :
    Nat.card (groupCohomology A 2) ∣ Nat.card G := by
  classical
  -- one Sylow subgroup for each prime factor of `#G`
  have hprime (p : (Nat.card G).primeFactors) : Fact (p : ℕ).Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  let P (p : (Nat.card G).primeFactors) : Sylow p G := Classical.arbitrary _
  -- the restrictions to these Sylow subgroups, which are jointly injective
  let Φ : groupCohomology A 2 →+
      ∀ p, groupCohomology (res (P p : Subgroup G).subtype A) 2 :=
    AddMonoidHom.pi fun p => (map (P p : Subgroup G).subtype (𝟙 _) 2).hom.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun x hx => eq_zero_of_map_sylow_eq_zero A 1 ?_
    intro p _ hp
    exact ⟨P ⟨p, Nat.mem_primeFactors.2 ⟨Fact.out, hp, Nat.card_pos.ne'⟩⟩, congrFun hx _⟩
  have hP (p : (Nat.card G).primeFactors) :
      Nat.card (groupCohomology (res (P p : Subgroup G).subtype A) 2) ∣ Nat.card (P p) := by
    have : Group.IsSolvable (P p) := have := (P p).isPGroup'.isNilpotent; inferInstance
    exact natCard_groupCohomology_two_res_dvd_of_isSolvable A h1 h2 _ (P p : Subgroup G).subtype
      Subtype.val_injective
  calc Nat.card (groupCohomology A 2)
      = Nat.card Φ.range := Nat.card_congr (AddMonoidHom.ofInjective hΦ).toEquiv
    _ ∣ Nat.card (∀ p, groupCohomology (res (P p : Subgroup G).subtype A) 2) :=
      Φ.range.card_addSubgroup_dvd_card
    _ = ∏ p, Nat.card (groupCohomology (res (P p : Subgroup G).subtype A) 2) := Nat.card_pi
    _ ∣ ∏ p, Nat.card (P p) := Finset.prod_dvd_prod_of_dvd _ _ fun p _ => hP p
    _ = Nat.card G := by
      simp_rw [Sylow.card_eq_multiplicity]
      rw [Finset.prod_coe_sort (Nat.card G).primeFactors fun p => p ^ (Nat.card G).factorization p,
        ← Nat.support_factorization]
      exact Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

end TauCeti.groupCohomology
