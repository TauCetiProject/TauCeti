/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.Module.Torsion.Subgroup
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Finiteness.Defs
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.Algebra.MonoidAlgebra.Polynomial
import TauCeti.Algebra.MvPolynomial.Laurent.IntegrallyClosed
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closedness of monoid and torsion-free abelian group algebras

For any commutative monoid `M`, the coefficient ring `R` is a ring retract of `R[M]` along the
scalar inclusion and the bialgebra counit, and scalar inclusion sends nonzerodivisors to
nonzerodivisors. Consequently, whenever `R[M]` is integrally closed, `R` is itself integrally closed
(`IsIntegrallyClosed.of_monoidAlgebra` and `IsIntegrallyClosed.of_addMonoidAlgebra`), with no domain
assumption on `R` or `R[M]`.

Conversely, when `G` is a torsion-free abelian group (`[Module.IsTorsionFree ℤ G]`, which includes
all free `ℤ`-modules of arbitrary rank) and `R` is an integrally closed domain, `R[G]` is
integrally closed (`AddMonoidAlgebra.isIntegrallyClosed`, Gilmer's theorem). First, for a free
`ℤ`-module `G`, choosing a `ℤ`-basis identifies `R[G]` with a multivariable Laurent polynomial ring
`LaurentRing R ι` (`TauCeti.LaurentRing.isIntegrallyClosed`). In general, any integral equation over
`R[G]` for a fraction `a / b` involves only finitely many exponents, reducing to a finitely
generated—and therefore free—subgroup of `G`. Together these give the exact characterization
`IsIntegrallyClosed (AddMonoidAlgebra R G) ↔ IsIntegrallyClosed R` over any integral domain `R`
(`AddMonoidAlgebra.isIntegrallyClosed_iff`).

## Main results

* `IsIntegrallyClosed.of_monoidAlgebra` and `IsIntegrallyClosed.of_addMonoidAlgebra`: if a
  commutative (additive) monoid algebra `R[M]` is integrally closed, then `R` is integrally closed.
* `AddMonoidAlgebra.isIntegrallyClosed`: the group algebra `R[G]` of a torsion-free abelian group
  `G` over an integrally closed domain `R` is integrally closed.
* `AddMonoidAlgebra.isIntegrallyClosed_iff`: over a domain `R`, `R[G]` is integrally closed if and
  only if `R` is integrally closed.

## References

* R. Gilmer, *Commutative Semigroup Rings*, Theorem 12.10.
* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Theorem 4.40.
-/

public section

/-- If a commutative monoid algebra `R[M]` is integrally closed, then its coefficient ring `R` is
integrally closed, as `R` is a ring retract of `R[M]` via the bialgebra counit and scalar inclusion
carries nonzerodivisors to nonzerodivisors. -/
@[to_additive (dont_translate := R)
/-- If a commutative additive monoid algebra `R[M]` is integrally closed, then its coefficient ring
`R` is integrally closed, as `R` is a ring retract of `R[M]` via the bialgebra counit and scalar
inclusion carries nonzerodivisors to nonzerodivisors. -/]
theorem IsIntegrallyClosed.of_monoidAlgebra (R M : Type*) [CommRing R] [CommMonoid M]
    [IsIntegrallyClosed (MonoidAlgebra R M)] : IsIntegrallyClosed R := by
  refine IsIntegrallyClosed.of_leftInverse_of_nonZeroDivisors_le
    (i := algebraMap R (MonoidAlgebra R M))
    (π := (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).toRingHom)
    (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).commutes fun r hr ↦ ?_
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_left]
  intro x hx
  rw [← Algebra.smul_def] at hx
  ext m
  exact mem_nonZeroDivisors_iff_left.mp hr (x.coeff m) (by simpa using congr(($hx).coeff m))

namespace AddMonoidAlgebra

private theorem isIntegrallyClosed_of_free {R G : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [AddCommGroup G] [Module.Free ℤ G] :
    IsIntegrallyClosed (AddMonoidAlgebra R G) :=
  let e : (Module.Free.ChooseBasisIndex ℤ G →₀ ℤ) ≃+ G :=
    (Module.Free.chooseBasis ℤ G).repr.toAddEquiv.symm
  IsIntegrallyClosed.of_equiv (mapDomainRingEquiv R e)

/-- **Gilmer's theorem for torsion-free abelian group algebras.** The group algebra `R[G]` of any
torsion-free abelian group `G` over an integrally closed domain `R` is integrally closed. -/
instance isIntegrallyClosed {R G : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [AddCommGroup G] [Module.IsTorsionFree ℤ G] :
    IsIntegrallyClosed (AddMonoidAlgebra R G) := by
  refine (isIntegrallyClosed_iff (FractionRing (AddMonoidAlgebra R G))).mpr
    fun {z} ⟨p, hp, hpz⟩ ↦ ?_
  obtain ⟨⟨a, b⟩, hzb⟩ := IsLocalization.surj (nonZeroDivisors (AddMonoidAlgebra R G)) z
  obtain ⟨H, hH, hsH, p₀, hp₀, -, hp₀_monic⟩ := exists_fg_addSubgroup_lifts
    (a.coeff.support.finite_toSet.union b.1.coeff.support.finite_toSet) hp
  have : H.FG := hH
  have : IsIntegrallyClosed (AddMonoidAlgebra R H) := isIntegrallyClosed_of_free
  let j : AddMonoidAlgebra R H →+* AddMonoidAlgebra R G := mapDomainRingHom R H.subtype
  have hj : Function.Injective j := mapDomain_injective H.subtype_injective
  obtain ⟨a₀, ha₀⟩ : a ∈ Set.range j :=
    (mem_range_mapDomain_iff H.subtype_injective a).mpr fun g hg ↦ ⟨⟨g, hsH (.inl hg)⟩, rfl⟩
  obtain ⟨b₀, hb₀⟩ : b.1 ∈ Set.range j :=
    (mem_range_mapDomain_iff H.subtype_injective b.1).mpr fun g hg ↦ ⟨⟨g, hsH (.inr hg)⟩, rfl⟩
  have hb₀_nzd : b₀ ∈ nonZeroDivisors (AddMonoidAlgebra R H) :=
    mem_nonZeroDivisors_of_injective hj (hb₀.symm ▸ b.2)
  have hnzd := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj
  let f : FractionRing (AddMonoidAlgebra R H) →+* FractionRing (AddMonoidAlgebra R G) :=
    IsLocalization.map _ j hnzd
  let z₀ : FractionRing (AddMonoidAlgebra R H) := IsLocalization.mk' _ a₀ ⟨b₀, hb₀_nzd⟩
  have hfz₀ : f z₀ = z := by
    simpa [z₀, f, IsLocalization.map_mk', ha₀, hb₀] using
      (IsLocalization.eq_mk'_iff_mul_eq.mpr hzb).symm
  have hz₀_int : IsIntegral (AddMonoidAlgebra R H) z₀ :=
    RingHom.IsIntegralElem.of_map (g := f) f.injective ⟨p₀, hp₀_monic, by
      dsimp only [f]
      rw [IsLocalization.map_comp (S := FractionRing (AddMonoidAlgebra R H)) hnzd,
        ← Polynomial.eval₂_map, hp₀, hfz₀, hpz]⟩
  obtain ⟨y₀, hy₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hz₀_int
  exact ⟨j y₀, by
    rw [← IsLocalization.map_eq (S := FractionRing (AddMonoidAlgebra R H)) hnzd, hy₀, hfz₀]⟩

/-- Over an integral domain `R`, the group algebra `R[G]` of a torsion-free abelian group `G` is
integrally closed if and only if `R` is integrally closed. -/
@[simp]
theorem isIntegrallyClosed_iff {R G : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup G] [Module.IsTorsionFree ℤ G] :
    IsIntegrallyClosed (AddMonoidAlgebra R G) ↔ IsIntegrallyClosed R :=
  ⟨fun _ ↦ .of_addMonoidAlgebra R G, fun _ ↦ inferInstance⟩

end AddMonoidAlgebra
