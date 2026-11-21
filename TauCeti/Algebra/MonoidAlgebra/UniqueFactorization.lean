/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial

/-!
# Factoriality of group algebras of torsion-free abelian groups

Let `R` be a unique factorization domain. The group algebra `R[N]` of a free abelian group `N`,
of any rank, is again a unique factorization domain: a basis of `N` identifies `R[N]` with a
Laurent ring, which is the localization of a polynomial ring at its variables. In particular the
Laurent rings `ℤ[N]` and `ℤ[v^{±1}][N]` of a lattice `N` are factorial.

For an arbitrary torsion-free abelian group `G`, such as the multiplicative group of a
coefficient semifield, `R[G]` need not be factorial: in `ℤ[ℚ]` the monomial `X^1` is the square
of `X^{1/2}`, which is the square of `X^{1/4}`, and so on, so it has no factorization into
irreducibles. What survives is the divisibility property that relatively prime elements are
used for: `R[G]` is a decomposition monoid, so `a ∣ b * c` splits as `a = a₁ * a₂` with
`a₁ ∣ b` and `a₂ ∣ c`. Indeed finitely many elements of `R[G]`, together with the witnesses of a
divisibility among them, lie in the group algebra of a finitely generated subgroup, which is free
because `G` is torsion-free, so that its group algebra is factorial. The same holds for Laurent
rings `(R[G])[N]` over such group algebras, which are group algebras of `N × G` over `R`.

Consequently, in all of these rings two relatively prime elements `a` and `b` satisfy
`(a) ∩ (b) = (a b)`, by
`Ideal.span_singleton_inf_span_singleton_eq_span_singleton_mul_of_isRelPrime`.

## Main results

* `AddMonoidAlgebra.uniqueFactorizationMonoid`: the group algebra of a free abelian group over a
  unique factorization domain is a unique factorization domain. This covers the Laurent rings
  `TauCeti.LaurentRing R K` in any set of variables.
* `MonoidAlgebra.exists_fg_forall_mem_range_mapDomain`: finitely many elements of a group algebra
  lie in the image of the group algebra of a finitely generated subgroup, with additive form
  `AddMonoidAlgebra.exists_fg_forall_mem_range_mapDomain`.
* `AddMonoidAlgebra.decompositionMonoid` and `MonoidAlgebra.decompositionMonoid`: the group
  algebra of a torsion-free abelian group over a unique factorization domain is a decomposition
  monoid.
* `AddMonoidAlgebra.decompositionMonoid_monoidAlgebra`: so is a Laurent ring over such a group
  algebra.

## Implementation notes

Gilmer and Parker show more: for `R` a GCD domain and `G` torsion-free abelian, `R[G]` is a GCD
domain. The decomposition property proved here is the part needed to turn relative primality
into the intersection of principal ideals.

## References

* R. Gilmer and T. Parker, *Divisibility properties in semigroup rings*, Michigan Math. J. 21
  (1974), 65–86, for unique factorization and GCD properties of group rings of torsion-free
  abelian groups.
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Math. J. 126 (2005), §1, for relatively prime exchange polynomials in
  Laurent rings over `ℤ[P]`.
-/

public section

namespace MonoidAlgebra

variable {R : Type*} [Semiring R] {G : Type*} [Group G]

/-- Finitely many elements of a group algebra `R[G]` lie in the image of the group algebra of a
finitely generated subgroup of `G`. -/
@[to_additive
/-- Finitely many elements of a group algebra `R[G]` lie in the image of the group algebra of a
finitely generated subgroup of `G`. -/]
theorem exists_fg_forall_mem_range_mapDomain (s : Finset (MonoidAlgebra R G)) :
    ∃ H : Subgroup G, H.FG ∧ ∀ x ∈ s, x ∈ Set.range (mapDomain (R := R) H.subtype) := by
  classical
  refine ⟨.closure ↑(s.biUnion fun x ↦ x.coeff.support),
    (Subgroup.fg_iff _).mpr ⟨_, rfl, Finset.finite_toSet _⟩, fun x hx ↦ ?_⟩
  refine (mem_range_mapDomain_iff Subtype.val_injective x).mpr fun g hg ↦ ?_
  exact ⟨⟨g, Subgroup.subset_closure (Finset.mem_biUnion.mpr ⟨x, hx, hg⟩)⟩, rfl⟩

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {R : Type*} [CommRing R] [UniqueFactorizationMonoid R]

/-- The group algebra of a free abelian group, of any rank, over a unique factorization domain is
a unique factorization domain. -/
instance uniqueFactorizationMonoid {N : Type*} [AddCommGroup N] [Module.Free ℤ N] :
    UniqueFactorizationMonoid (AddMonoidAlgebra R N) := by
  -- A basis identifies `R[N]` with a Laurent ring, a localization of a polynomial ring.
  let b := Module.Free.chooseBasis ℤ N
  have : UniqueFactorizationMonoid (TauCeti.LaurentRing R (Module.Free.ChooseBasisIndex ℤ N)) :=
    .of_isLocalization (Submonoid.closure (Set.range
      (MvPolynomial.X : _ → MvPolynomial (Module.Free.ChooseBasisIndex ℤ N) R))) _
  exact (mapDomainRingEquiv R b.repr.toAddEquiv).toMulEquiv.symm.uniqueFactorizationMonoid this

variable {G : Type*} [AddCommGroup G] [HasUniqueDiv G]

/-- The group algebra of a torsion-free abelian group over a unique factorization domain is a
decomposition monoid: if `a ∣ b * c` then `a = a₁ * a₂` with `a₁ ∣ b` and `a₂ ∣ c`. The group
need not be finitely generated, and then the group algebra need not be factorial. -/
instance decompositionMonoid : DecompositionMonoid (AddMonoidAlgebra R G) where
  primal a b c := by
    rintro ⟨d, hd⟩
    classical
    -- `a`, `b`, `c` and `d` come from the group algebra of a finitely generated subgroup `H`,
    -- which is free since `G` is torsion-free, so that its group algebra is factorial.
    obtain ⟨H, hH, hmem⟩ := exists_fg_forall_mem_range_mapDomain (R := R) {a, b, c, d}
    have : Module.Finite ℤ H :=
      Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg H).mpr hH)
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    have hc := hmem c (by simp)
    have hd' := hmem d (by simp)
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    obtain ⟨c, rfl⟩ := hc
    obtain ⟨d, rfl⟩ := hd'
    simp only [← mapDomainRingHom_apply, ← map_mul] at hd
    obtain ⟨a₁, a₂, h₁, h₂, rfl⟩ :=
      exists_dvd_and_dvd_of_dvd_mul ⟨d, mapDomain_injective Subtype.val_injective hd⟩
    exact ⟨_, _, map_dvd _ h₁, map_dvd _ h₂, map_mul (mapDomainRingHom R H.subtype) a₁ a₂⟩

/-- A Laurent ring `(R[G])[N]` over the group algebra of a torsion-free abelian group `G`, with
`R` a unique factorization domain and `N` torsion-free, is a decomposition monoid: it is the group
algebra of `N × G` over `R`. This covers Laurent rings over `ℤ[P]` for the multiplicative group of
a coefficient semifield `P`. -/
instance decompositionMonoid_monoidAlgebra {G N : Type*} [CommGroup G] [HasUniqueRoots G]
    [AddCommGroup N] [HasUniqueDiv N] :
    DecompositionMonoid (AddMonoidAlgebra (MonoidAlgebra R G) N) :=
  MulEquiv.decompositionMonoid (β := AddMonoidAlgebra R (N × Additive G))
    ((mapRingEquiv N (MonoidAlgebra.toAdditive R G)).trans (curryAlgEquiv R).symm.toRingEquiv)

end AddMonoidAlgebra

namespace MonoidAlgebra

variable {R : Type*} [CommRing R] [UniqueFactorizationMonoid R]

/-- The group algebra of a torsion-free abelian group over a unique factorization domain is a
decomposition monoid. This covers `ℤ[P]` for the multiplicative group of a coefficient
semifield `P`. -/
instance decompositionMonoid {G : Type*} [CommGroup G] [HasUniqueRoots G] :
    DecompositionMonoid (MonoidAlgebra R G) :=
  MulEquiv.decompositionMonoid (toAdditive R G)

end MonoidAlgebra

/-! Factoriality covers Laurent rings over `ℤ` in any set of variables, and Laurent rings over
`ℤ[v^{±1}]`. The decomposition property covers the group algebra of the non-finitely-generated
group `ℚ` and the Laurent rings over it. -/

example (K : Type) : UniqueFactorizationMonoid (TauCeti.LaurentRing ℤ K) := inferInstance

example : UniqueFactorizationMonoid
    (TauCeti.LaurentRing (TauCeti.LaurentRing ℤ Unit) (Fin 2)) := inferInstance

example : DecompositionMonoid (AddMonoidAlgebra ℤ ℚ) := inferInstance

example : DecompositionMonoid
    (TauCeti.LaurentRing (MonoidAlgebra ℤ (Multiplicative ℚ)) (Fin 2)) := inferInstance
