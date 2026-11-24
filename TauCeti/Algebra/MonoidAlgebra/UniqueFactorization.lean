/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
# Factoriality of free abelian group algebras and decomposition in the torsion-free case

Let `R` be a unique factorization domain. The group algebra `R[N]` of a free abelian group `N`,
of any rank, is again a unique factorization domain: a basis of `N` identifies `R[N]` with a
Laurent ring, which is the localization of a polynomial ring at its variables. In particular the
Laurent rings `ℤ[N]` and `ℤ[v^{±1}][N]` of a lattice `N` are factorial.

For an arbitrary torsion-free abelian group `G`, such as the multiplicative group of a
coefficient semifield, `R[G]` need not be factorial. In `ℤ[ℚ]` the non-unit `X^1 - 1` is
`(X^{1/2} - 1) (X^{1/2} + 1)`, and `X^{1/2} - 1` splits in the same way, so the principal ideals
`(X^1 - 1) ⊊ (X^{1/2} - 1) ⊊ (X^{1/4} - 1) ⊊ ⋯` form an infinite strictly ascending chain,
which a factorial ring cannot contain. What survives is the divisibility property that relatively
prime elements are used for: `R[G]` is a decomposition monoid, so `a ∣ b * c` splits as
`a = a₁ * a₂` with `a₁ ∣ b` and `a₂ ∣ c`. Indeed finitely many elements of `R[G]`, together with
the witnesses of a divisibility among them, lie in the group algebra of a finitely generated
subgroup, which is free because `G` is torsion-free, so that its group algebra is factorial. The
same holds for the group algebras `(R[G])[N]` of torsion-free abelian groups `N` over such group
algebras, which include the Laurent rings over them, since they are group algebras of `N × G`
over `R`.

Consequently, in all of these rings two relatively prime elements `a` and `b` satisfy
`(a) ∩ (b) = (a b)`, by
`Ideal.span_singleton_inf_span_singleton_eq_span_singleton_mul_of_isRelPrime`.

## Main results

* `AddMonoidAlgebra.uniqueFactorizationMonoid`: the group algebra of a free abelian group over a
  unique factorization domain is a unique factorization domain. This covers the Laurent rings
  `TauCeti.LaurentRing R K` in any set of variables.
* `AddMonoidAlgebra.decompositionMonoid` and `MonoidAlgebra.decompositionMonoid`: the group
  algebra of a torsion-free abelian group over a unique factorization domain is a decomposition
  monoid.
* `AddMonoidAlgebra.decompositionMonoid_addMonoidAlgebra` and
  `AddMonoidAlgebra.decompositionMonoid_monoidAlgebra`: so is the group algebra `(R[G])[N]` of a
  torsion-free abelian group `N` over such a group algebra `R[G]`. This covers Laurent rings over
  `R[G]`, to which `AddMonoidAlgebra.decompositionMonoid` does not apply directly since `R[G]`
  need not be factorial.

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

/-- The group algebra `(R[G])[N]` of a torsion-free abelian group `N` over the group algebra of a
torsion-free abelian group `G`, with `R` a unique factorization domain, is a decomposition monoid.
This covers Laurent rings over `R[G]`, to which `decompositionMonoid` does not apply directly since
`R[G]` need not be factorial. -/
instance decompositionMonoid_addMonoidAlgebra {N : Type*} [AddCommGroup N] [HasUniqueDiv N] :
    DecompositionMonoid (AddMonoidAlgebra (AddMonoidAlgebra R G) N) :=
  MulEquiv.decompositionMonoid (β := AddMonoidAlgebra R (N × G)) curryRingEquiv.symm

/-- The group algebra `(R[G])[N]` of a torsion-free abelian group `N` over the group algebra of a
torsion-free multiplicative abelian group `G`, with `R` a unique factorization domain, is a
decomposition monoid. This covers Laurent rings over `ℤ[P]` for the multiplicative group of a
coefficient semifield `P`. -/
instance decompositionMonoid_monoidAlgebra {G N : Type*} [CommGroup G] [HasUniqueRoots G]
    [AddCommGroup N] [HasUniqueDiv N] :
    DecompositionMonoid (AddMonoidAlgebra (MonoidAlgebra R G) N) :=
  MulEquiv.decompositionMonoid (mapRingEquiv N (MonoidAlgebra.toAdditive R G))

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

example : DecompositionMonoid (TauCeti.LaurentRing (AddMonoidAlgebra ℤ ℚ) (Fin 2)) := inferInstance

example : DecompositionMonoid
    (TauCeti.LaurentRing (MonoidAlgebra ℤ (Multiplicative ℚ)) (Fin 2)) := inferInstance
