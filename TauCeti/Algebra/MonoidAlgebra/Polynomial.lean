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

For an injective homomorphism `f : M →* N` of monoids (or `f : M →+ N` of additive monoids), a
polynomial over `R[N]` lies in `Polynomial.lifts (mapDomainRingHom R f)` if and only if the support
of each nonzero coefficient lies in `Set.range f` (`MonoidAlgebra.mem_lifts_mapDomainRingHom_iff`
and `AddMonoidAlgebra.mem_lifts_mapDomainRingHom_iff`). For a group `G`, any finite subset `s ⊆ G`
and monic polynomial `p` over `R[G]` therefore lift together to a finitely generated subgroup
`H ≤ G` (`MonoidAlgebra.exists_fg_subgroup_lifts` and
`AddMonoidAlgebra.exists_fg_addSubgroup_lifts`), packaging the finite-support subgroup reduction for
polynomial equations over group algebras.
-/

public section

namespace MonoidAlgebra

variable {R M N : Type*} [Semiring R] [Monoid M] [Monoid N]

/-- For an injective monoid homomorphism `f : M →* N`, a polynomial over `R[N]` lifts to `R[M]`
along `mapDomainRingHom R f` if and only if the support of each of its coefficients lies in
`Set.range f`. -/
@[to_additive (dont_translate := R)
/-- For an injective additive monoid homomorphism `f : M →+ N`, a polynomial over `R[N]` lifts to
`R[M]` along `mapDomainRingHom R f` if and only if the support of each of its coefficients lies in
`Set.range f`. -/]
theorem mem_lifts_mapDomainRingHom_iff {f : M →* N} (hf : Function.Injective f)
    (p : Polynomial (MonoidAlgebra R N)) :
    p ∈ Polynomial.lifts (mapDomainRingHom R f) ↔
      ∀ i ∈ p.support, ∀ n ∈ (p.coeff i).coeff.support, n ∈ Set.range f := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  refine ⟨fun h i _ ↦ (mem_range_mapDomain_iff hf (p.coeff i)).mp (by simpa using h i),
    fun h i ↦ ?_⟩
  by_cases hi : i ∈ p.support
  · simpa using (mem_range_mapDomain_iff hf (p.coeff i)).mpr (h i hi)
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hi]⟩

/-- Given a finite subset `s` of a group `G` and a monic polynomial `p` over `R[G]`, there is a
finitely generated subgroup `H` of `G` containing `s` such that `p` lifts along
`mapDomainRingHom R H.subtype` to a monic polynomial over `R[H]` of the same degree. -/
@[to_additive (dont_translate := R)
/-- Given a finite subset `s` of an additive group `G` and a monic polynomial `p` over `R[G]`,
there is a finitely generated additive subgroup `H` of `G` containing `s` such that `p` lifts along
`mapDomainRingHom R H.subtype` to a monic polynomial over `R[H]` of the same degree. -/]
theorem exists_fg_subgroup_lifts {G : Type*} [Group G] {s : Set G} (hs : s.Finite)
    {p : Polynomial (MonoidAlgebra R G)} (hp : p.Monic) :
    ∃ H : Subgroup G, H.FG ∧ s ⊆ H ∧
      ∃ p₀ : Polynomial (MonoidAlgebra R H),
        p₀.map (mapDomainRingHom R H.subtype) = p ∧ p₀.natDegree = p.natDegree ∧ p₀.Monic := by
  let t : Set G := s ∪ ⋃ i ∈ (p.support : Set ℕ), ((p.coeff i).coeff.support : Set G)
  have ht : t.Finite :=
    hs.union (p.support.finite_toSet.biUnion fun i _ ↦ (p.coeff i).coeff.support.finite_toSet)
  let H : Subgroup G := Subgroup.closure t
  have hlifts : p ∈ Polynomial.lifts (mapDomainRingHom R H.subtype) :=
    (mem_lifts_mapDomainRingHom_iff H.subtype_injective p).mpr fun i hi g hg ↦
      ⟨⟨g, Subgroup.subset_closure (.inr (Set.mem_biUnion hi hg))⟩, rfl⟩
  exact ⟨H, (Subgroup.fg_iff H).mpr ⟨t, rfl, ht⟩,
    Set.subset_union_left.trans Subgroup.subset_closure,
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp⟩

end MonoidAlgebra
