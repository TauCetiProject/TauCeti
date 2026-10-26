/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Corestriction
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Lifting
import Mathlib.GroupTheory.Nilpotent

/-!
# Classes with invariant zero, from the layers of prime degree

Let `φ : A → A'` be an equivariant map between the coefficient modules of two formations `F` and
`F'` on `G`, and let `σ` assign to every finite normal layer `L` a homomorphism
`σ_L : H²(L, A) → ℚ/ℤ` that does not change under inflation, multiplies by the relative degree
under restriction, and vanishes on the classes that `φ` kills. For the idele classes of a number
field, `A` is the ideles, `A'` the idele classes and `σ` the sum of the local invariants. The
construction of the invariant map of `F'` from `σ` (`ClassFormation.ofDescendedInv`) needs the
converse: `σ` vanishes *only* on the classes that `φ` kills. For the idele classes of a layer
`L/F` this says that a class of `H²(Gal(L/F), I_L)`, a family of local Brauer classes split by `L`,
whose local invariants sum to zero comes from `H²(Gal(L/F), Lˣ)`: the kernel of the sum of the
local invariants is the image of the Brauer group.

This file reduces that converse to the layers of prime degree, provided that `H¹` of every layer
of `F'` vanishes and that `φ` is surjective on `H²` of every layer of prime degree. The reduction
is by induction on the degree `n` of `L`, with Galois group `Γ`
(`NormalLayer.map_eq_zero_of_prime_degree`). Let `y` be a class of `H²(L, A)` with `σ(y) = 0`, and
`x = φ(y)`.

* If `Γ` is not a `p`-group for any prime `p`, every Sylow subgroup `P` of `Γ` is proper. The
  restriction of `y` to the layer of `P` has `σ = [Γ : P] • 0 = 0`, so by induction `x` restricts
  to zero there, and corestricting back gives `[Γ : P] • x = 0`. The indices of the Sylow
  subgroups have no common prime factor, so `x = 0`.
* If `Γ` is a nontrivial `p`-group, it has a normal subgroup `N` of index `p`, and `L` refines the
  layer `L_N` of `Γ ⧸ N`, of degree `p`. The restriction of `x` to the layer of `N` vanishes by
  induction, so by the inflation-restriction sequence `x` is inflated from a class `x₀` of
  `H²(L_N, A')`. That class is `φ(y₀)` by the surjectivity of `φ` in prime degree, and
  `φ(y - infl y₀) = 0`, so `σ(y₀) = σ(infl y₀) = σ(y) = 0`. The prime-degree case gives
  `x₀ = φ(y₀) = 0`, hence `x = 0`.

The prime-degree case itself is a counting statement
(`NormalLayer.map_eq_zero_of_natCard_H2_dvd_degree`): on a layer `L` of degree `n` carrying a
class `z` with `σ(z) = 1/n`, if `#H²(L, A') ∣ n`, then `φ(z)` generates `H²(L, A')`, so every class
`φ(y)` is a multiple `k • φ(z)`; then `σ(y) = k • (1/n)`, and `σ(y) = 0` forces `n ∣ k`, so
`φ(y) = 0`. For the idele classes the divisibility is the second fundamental inequality, and on a
layer of prime degree `p` a class with `σ = 1/p` comes from a place of local degree `p`.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.map_eq_zero_of_natCard_H2_dvd_degree`: on a layer of
  degree `n` with `#H²(L, A') ∣ n` and a class with `σ = 1/n`, the classes with `σ = 0` are killed
  by `φ`.
* `TauCeti.ClassFieldTheory.NormalLayer.map_eq_zero_of_prime_degree`: if the classes with `σ = 0`
  are killed by `φ` on the layers of prime degree, they are killed by `φ` on every layer.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public section

open CategoryTheory

namespace TauCeti.ClassFieldTheory

namespace NormalLayer

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F F' : Formation G}
  (φ : F.toRep ⟶ F'.toRep) (σ : ∀ L : NormalLayer G, L.H F 2 →+ AddCircle (1 : ℚ))
  (hσ : ∀ {old new : NormalLayer G} (T : LayerRefinement old new) (y : old.H F 2),
    σ new (T.cohomologyInfl F 2 y) = σ old y)
  (hres : ∀ {small big : NormalLayer G} (R : LayerRestriction small big) (y : big.H F 2),
    σ small (R.cohomologyRes F 2 y) = R.relativeDegree • σ big y)
  (hker : ∀ (L : NormalLayer G) (y : L.H F 2),
    groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0 → σ L y = 0)
  (h1 : ∀ L : NormalLayer G, Subsingleton (L.H F' 1))

include hker in
/-- **On a layer with a class of invariant `1/n`, only the classes killed by `φ` have invariant
zero**, when the order of `H²(L, A')` divides the degree `n` of `L`: a class `y` of `H²(L, A)` with
`σ(y) = 0` has `φ(y) = 0`. -/
theorem map_eq_zero_of_natCard_H2_dvd_degree {L : NormalLayer G}
    (h2 : Nat.card (L.H F' 2) ∣ L.degree)
    (hgen : ∃ z : L.H F 2, σ L z = ((1 / L.degree : ℚ) : AddCircle (1 : ℚ))) {y : L.H F 2}
    (hy : σ L y = 0) :
    groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0 := by
  obtain ⟨z, hz⟩ := hgen
  -- `φ(z)` generates `H²(L, A')`, so `φ(y)` is a multiple `k • φ(z)`.
  have hinfl : (LayerRefinement.refl L).cohomologyInfl F' 2
      (groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 z) =
        groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 z := by
    rw [LayerRefinement.cohomologyInfl_self, ConcreteCategory.id_apply]
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1
    ((zmultiples_eq_top_of_cohomologyInfl_eq_map φ σ hker h2 (LayerRefinement.refl L) hz
      hinfl).ge (AddSubgroup.mem_top (groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y)))
  -- Then `σ(y) = k • (1/n)`, so `σ(y) = 0` forces `n ∣ k`.
  have hσk : k • ((1 / L.degree : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    have h := hker L (y - k • z) (by rw [map_sub, map_zsmul, hk, sub_self])
    rwa [map_sub, map_zsmul, hy, hz, zero_sub, neg_eq_zero] at h
  obtain ⟨m, rfl⟩ : (L.degree : ℤ) ∣ k := by
    rw [← AddCircle.addOrderOf_period_div (p := (1 : ℚ)) L.degree_pos]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.2 hσk
  -- The degree of `L` kills `H²(L, A')`.
  rw [← hk, mul_comm, mul_zsmul, natCast_zsmul, L.degree_eq_natCard_gal,
    groupCohomology.natCard_nsmul_eq_zero, zsmul_zero]

include hσ hres hker h1 in
/-- **The classes with invariant zero are killed by `φ`, from the layers of prime degree.** Suppose
that `σ` does not change under inflation, multiplies by the relative degree under restriction and
vanishes on the classes that `φ` kills, and that `H¹` of every layer of `F'` vanishes. If, on every
layer of prime degree, `φ` is surjective on `H²` and kills every class with `σ = 0`, then on every
layer `L` a class `y` of `H²(L, A)` with `σ(y) = 0` has `φ(y) = 0`. -/
theorem map_eq_zero_of_prime_degree
    (hsurj : ∀ L : NormalLayer G, L.degree.Prime → ∀ x : L.H F' 2, ∃ y : L.H F 2,
      groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = x)
    (hprime : ∀ L : NormalLayer G, L.degree.Prime → ∀ y : L.H F 2, σ L y = 0 →
      groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0)
    (L : NormalLayer G) {y : L.H F 2} (hy : σ L y = 0) :
    groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0 := by
  -- Strong induction on the degree of the layer.
  suffices H : ∀ n (L : NormalLayer G), L.degree = n → ∀ y : L.H F 2, σ L y = 0 →
      groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = 0 from H _ L rfl y hy
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn y hy
  -- Restricting `y` to a layer of smaller degree inside `L` kills its image.
  have hres0 {H : Subgroup L.Gal} (hH : (L.subgroupLayer H).degree < n) :
      (L.subgroupRestriction H).cohomologyRes F' 2
        (groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y) = 0 := by
    rw [← LayerRestriction.cohomologyRes_comp_map_repMap_apply]
    exact ih _ hH _ rfl _ (by rw [hres, hy, smul_zero])
  rcases eq_or_ne n 1 with rfl | hn1
  · -- A layer of degree one has no second cohomology.
    rw [← one_smul ℕ (groupCohomology.map _ _ 2 y), ← hn, L.degree_eq_natCard_gal,
      groupCohomology.natCard_nsmul_eq_zero]
  by_cases hpg : ∃ p, p.Prime ∧ IsPGroup p L.Gal
  · -- A `p`-group: `L` refines the layer of a quotient of `Γ` of order `p`.
    obtain ⟨p, hp, hpG⟩ := hpg
    have : Fact p.Prime := ⟨hp⟩
    have hdvd : p ∣ Nat.card L.Gal := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpG
      rcases k with _ | k
      · exact absurd (hk.trans (pow_zero p)) (by rwa [← L.degree_eq_natCard_gal, hn])
      · exact hk ▸ dvd_pow_self p k.succ_ne_zero
    have := IsPGroup.isNilpotent hpG
    obtain ⟨N, hNi, hN⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
    let T := L.quotientRefinement N
    have hQ : (L.quotientLayer N).degree.Prime := (L.degree_quotientLayer N).trans hNi ▸ hp
    -- The restriction of `φ(y)` to the layer of `N` vanishes, so `φ(y)` is inflated from `L_N`.
    have hlt : (L.subgroupLayer T.galHom.ker).degree < n := by
      have h := (L.subgroupRestriction T.galHom.ker).degree_mul_relativeDegree
      rw [T.relativeDegree_subgroupRestriction_ker, hn] at h
      have hn0 : 0 < n := hn ▸ L.degree_pos
      nlinarith [hQ.two_le]
    obtain ⟨x₀, hx₀⟩ := T.exists_cohomologyInfl_eq_of_cohomologyRes_eq_zero F' (h1 _) (hres0 hlt)
    obtain ⟨y₀, rfl⟩ := hsurj _ hQ x₀
    -- `φ(y - infl y₀) = 0`, so `σ(y₀) = σ(y) = 0`, and the prime-degree case kills `φ(y₀)`.
    have hσ₀ : σ _ y₀ = 0 := by
      have h := hker L (y - T.cohomologyInfl F 2 y₀) (by
        rw [map_sub, LayerRefinement.cohomologyInfl_comp_map_repMap_apply, hx₀, sub_self])
      rwa [map_sub, hy, hσ, zero_sub, neg_eq_zero] at h
    rw [← hx₀, hprime _ hQ y₀ hσ₀, map_zero]
  · -- Not a `p`-group: the index of every Sylow subgroup kills `φ(y)`.
    have hsyl (q : ℕ) [Fact q.Prime] (P : Sylow q L.Gal) :
        (P : Subgroup L.Gal).index • groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y =
          0 := by
      have hP : (P : Subgroup L.Gal).index ≠ 1 := fun h ↦ by
        have hpq := P.isPGroup
        rw [Subgroup.index_eq_one.1 h] at hpq
        exact hpg ⟨q, Fact.out, hpq.of_equiv Subgroup.topEquiv⟩
      have hlt : (L.subgroupLayer (P : Subgroup L.Gal)).degree < n := by
        rw [degree_subgroupLayer, ← hn, degree_eq_natCard_gal,
          ← (P : Subgroup L.Gal).card_mul_index]
        exact lt_mul_right Nat.card_pos
          (lt_of_le_of_ne (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hP.symm)
      have h := (L.subgroupRestriction (P : Subgroup L.Gal)).cohomologyCor_cohomologyRes_apply F' 2
        (groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y)
      rwa [hres0 hlt, map_zero, ← (L.subgroupRestriction (P : Subgroup L.Gal)).relativeDegree_def,
        relativeDegree_subgroupRestriction, eq_comm] at h
    -- No prime divides the order of `φ(y)`, since none divides the indices of all Sylow subgroups.
    generalize groupCohomology.map (MonoidHom.id L.Gal) (L.repMap φ) 2 y = x at hsyl ⊢
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    by_contra hne
    have : Fact (addOrderOf x).minFac.Prime := ⟨Nat.minFac_prime hne⟩
    exact (Classical.arbitrary (Sylow (addOrderOf x).minFac L.Gal)).not_dvd_index
      ((Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero (hsyl _ _)))

end NormalLayer

end TauCeti.ClassFieldTheory
