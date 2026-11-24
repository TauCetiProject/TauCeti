/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.GroupTheory.Finiteness
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Lifting polynomials over monoid algebras along monoid homomorphisms

For any homomorphism `f : M →* N` of monoids (or `f : M →+ N` of additive monoids), a polynomial
over `R[N]` lies in `Polynomial.lifts (mapDomainRingHom R f)` if and only if the support of each
nonzero coefficient lies in `Set.range f` (`MonoidHom.mem_lifts_mapDomainRingHom_iff` and
`AddMonoidHom.mem_lifts_mapDomainRingHom_iff`). For a group `G`, any finite subset `s ⊆ G` and
polynomial `p` over `R[G]` therefore lift together to a finitely generated subgroup `H ≤ G`
(`Set.Finite.exists_fg_subgroup_subset_exists_map_mapDomainRingHom_eq` and
`Set.Finite.exists_fg_addSubgroup_subset_exists_map_mapDomainRingHom_eq`), packaging the
finite-support subgroup reduction for polynomial equations over group algebras.

## Main results

* `MonoidHom.mem_lifts_mapDomainRingHom_iff` and `AddMonoidHom.mem_lifts_mapDomainRingHom_iff`:
  support characterization of polynomials over `R[N]` lifting along `mapDomainRingHom R f`.
* `Set.Finite.exists_fg_subgroup_subset_exists_map_mapDomainRingHom_eq` and
  `Set.Finite.exists_fg_addSubgroup_subset_exists_map_mapDomainRingHom_eq`: simultaneous lifting of
  a finite set of exponents and a polynomial over `R[G]` to a finitely generated subgroup.
-/

public section

open MonoidAlgebra

variable {R M N : Type*} [Semiring R] [Monoid M] [Monoid N]

/-- For any monoid homomorphism `f : M →* N`, a polynomial over `R[N]` lifts to `R[M]` along
`mapDomainRingHom R f` if and only if the support of each of its coefficients lies in
`Set.range f`. -/
@[to_additive (dont_translate := R)
/-- For any additive monoid homomorphism `f : M →+ N`, a polynomial over `R[N]` lifts to `R[M]`
along `mapDomainRingHom R f` if and only if the support of each of its coefficients lies in
`Set.range f`. -/]
theorem MonoidHom.mem_lifts_mapDomainRingHom_iff (f : M →* N)
    (p : Polynomial (MonoidAlgebra R N)) :
    p ∈ Polynomial.lifts (mapDomainRingHom R f) ↔
      ∀ i ∈ p.support, ∀ n ∈ (p.coeff i).coeff.support, n ∈ Set.range f := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  refine ⟨fun h i _ ↦ (mem_range_mapDomain_iff (p.coeff i)).mp (by simpa using h i),
    fun h i ↦ ?_⟩
  by_cases hi : i ∈ p.support
  · simpa using (mem_range_mapDomain_iff (p.coeff i)).mpr (h i hi)
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hi]⟩

/-- Given a finite subset `s` of a group `G` and a polynomial `p` over `R[G]`, there is a finitely
generated subgroup `H` of `G` containing `s` such that `p` is the image along
`mapDomainRingHom R H.subtype` of a polynomial over `R[H]`. -/
@[to_additive (dont_translate := R)
/-- Given a finite subset `s` of an additive group `G` and a polynomial `p` over `R[G]`, there is a
finitely generated additive subgroup `H` of `G` containing `s` such that `p` is the image along
`mapDomainRingHom R H.subtype` of a polynomial over `R[H]`. -/]
theorem Set.Finite.exists_fg_subgroup_subset_exists_map_mapDomainRingHom_eq {G : Type*} [Group G]
    {s : Set G} (hs : s.Finite) (p : Polynomial (MonoidAlgebra R G)) :
    ∃ H : Subgroup G, H.FG ∧ s ⊆ H ∧
      ∃ p₀ : Polynomial (MonoidAlgebra R H),
        p₀.map (mapDomainRingHom R H.subtype) = p := by
  let t : Set G := s ∪ ⋃ i ∈ (p.support : Set ℕ), ((p.coeff i).coeff.support : Set G)
  have ht : t.Finite :=
    hs.union (p.support.finite_toSet.biUnion fun i _ ↦ (p.coeff i).coeff.support.finite_toSet)
  let H : Subgroup G := Subgroup.closure t
  have hlifts : p ∈ Polynomial.lifts (mapDomainRingHom R H.subtype) :=
    (H.subtype.mem_lifts_mapDomainRingHom_iff p).mpr fun i hi g hg ↦
      ⟨⟨g, Subgroup.subset_closure (.inr (Set.mem_biUnion hi hg))⟩, rfl⟩
  exact ⟨H, (Subgroup.fg_iff H).mpr ⟨t, rfl, ht⟩,
    Set.subset_union_left.trans Subgroup.subset_closure, (Polynomial.mem_lifts p).mp hlifts⟩
