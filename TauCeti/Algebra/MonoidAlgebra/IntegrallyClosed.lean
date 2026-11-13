/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.MonoidAlgebra.MapDomain
import TauCeti.Algebra.MvPolynomial.Laurent.IntegrallyClosed
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral closedness of monoid and torsion-free abelian group algebras

For any commutative monoid `M`, the coefficient ring `R` is a ring retract of `R[M]` along the
scalar inclusion and the coefficient-sum augmentation. Consequently, whenever `R[M]` is an
integrally closed domain, `R` is itself integrally closed
(`MonoidAlgebra.isIntegrallyClosed_coeffRing` and `AddMonoidAlgebra.isIntegrallyClosed_coeffRing`).

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

* `MonoidAlgebra.isIntegrallyClosed_coeffRing` and
  `AddMonoidAlgebra.isIntegrallyClosed_coeffRing`: if a commutative monoid algebra `R[M]` is an
  integrally closed domain, then `R` is integrally closed.
* `AddMonoidAlgebra.isIntegrallyClosed`: the group algebra `R[G]` of a torsion-free abelian group
  `G` over an integrally closed domain `R` is integrally closed.
* `AddMonoidAlgebra.isIntegrallyClosed_iff`: over a domain `R`, `R[G]` is integrally closed if and
  only if `R` is integrally closed.

## References

* R. Gilmer, *Commutative Semigroup Rings*, Theorem 12.10.
* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Theorem 4.40.
-/

public section

namespace MonoidAlgebra

/-- If a commutative monoid algebra `R[M]` is an integrally closed domain, then its coefficient
ring `R` is integrally closed, as `R` is a ring retract of `R[M]` via the augmentation map. -/
theorem isIntegrallyClosed_coeffRing (R M : Type*) [CommRing R] [CommMonoid M]
    [IsDomain (MonoidAlgebra R M)] [IsIntegrallyClosed (MonoidAlgebra R M)] :
    IsIntegrallyClosed R :=
  let π : MonoidAlgebra R M →+* R := liftNCRingHom (.id R) 1 fun _ _ ↦ Commute.one_right _
  IsIntegrallyClosed.of_leftInverse (i := singleOneRingHom) (π := π) fun r ↦ by simp [π]

end MonoidAlgebra

namespace AddMonoidAlgebra

/-- If a commutative additive monoid algebra `R[M]` is an integrally closed domain, then its
coefficient ring `R` is integrally closed, as `R` is a ring retract of `R[M]` via the augmentation
map. -/
theorem isIntegrallyClosed_coeffRing (R M : Type*) [CommRing R] [AddCommMonoid M]
    [IsDomain (AddMonoidAlgebra R M)] [IsIntegrallyClosed (AddMonoidAlgebra R M)] :
    IsIntegrallyClosed R :=
  let π : AddMonoidAlgebra R M →+* R := liftNCRingHom (.id R) 1 fun _ _ ↦ Commute.one_right _
  IsIntegrallyClosed.of_leftInverse (i := singleZeroRingHom) (π := π) fun r ↦ by simp [π]

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
  classical
  refine (isIntegrallyClosed_iff (FractionRing (AddMonoidAlgebra R G))).mpr
    fun {z} ⟨p, hp, hpz⟩ ↦ ?_
  obtain ⟨⟨a, b⟩, hzb⟩ := IsLocalization.surj (nonZeroDivisors (AddMonoidAlgebra R G)) z
  -- Restrict to the finitely generated (hence free) subgroup spanned by the supports of `a`, `b`
  -- and the coefficients of `p`.
  let F : Finset G :=
    a.coeff.support ∪ b.1.coeff.support ∪ p.support.biUnion fun i ↦ (p.coeff i).coeff.support
  let H : AddSubgroup G := AddSubgroup.closure (F : Set G)
  have hH_fg : H.FG := AddSubgroup.isAddFG_iff.mpr ⟨F, rfl⟩
  have : AddGroup.FG H := (AddGroup.fg_iff_addSubgroup_fg H).mpr hH_fg
  have : Module.Finite ℤ H := Module.Finite.iff_addGroup_fg.mpr this
  have : Module.IsTorsionFree ℤ H :=
    H.subtype_injective.moduleIsTorsionFree H.subtype fun _ _ ↦ rfl
  have : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  have : IsIntegrallyClosed (AddMonoidAlgebra R H) := isIntegrallyClosed_of_free
  let j : AddMonoidAlgebra R H →+* AddMonoidAlgebra R G := mapDomainRingHom R H.subtype
  have hj : Function.Injective j := mapDomain_injective H.subtype_injective
  have hlift (w : AddMonoidAlgebra R G) (hw : w.coeff.support ⊆ F) : w ∈ Set.range j :=
    (mem_range_mapDomain_iff H.subtype_injective w).mpr fun g hg ↦
      ⟨⟨g, AddSubgroup.subset_closure (hw hg)⟩, rfl⟩
  obtain ⟨a₀, ha₀⟩ := hlift a (Finset.subset_union_left.trans Finset.subset_union_left)
  obtain ⟨b₀, hb₀⟩ := hlift b.1 (Finset.subset_union_right.trans Finset.subset_union_left)
  have hb₀_nzd : b₀ ∈ nonZeroDivisors (AddMonoidAlgebra R H) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 ↦
      mem_nonZeroDivisors_iff_ne_zero.mp b.2 (by rw [← hb₀, h0, map_zero])
  have hlifts : p ∈ Polynomial.lifts j := (Polynomial.lifts_iff_coeff_lifts p).mpr fun i ↦ by
    by_cases hi : i ∈ p.support
    · exact hlift (p.coeff i)
        ((Finset.subset_biUnion_of_mem (fun k ↦ (p.coeff k).coeff.support) hi).trans
          Finset.subset_union_right)
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hi]⟩
  obtain ⟨p₀, hp₀, -, hp₀_monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have h_nzd :
      nonZeroDivisors (AddMonoidAlgebra R H) ≤
        (nonZeroDivisors (AddMonoidAlgebra R G)).comap j := fun x hx ↦
    mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff j hj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  obtain ⟨f, hf_eq⟩ :
      ∃ f : FractionRing (AddMonoidAlgebra R H) →+* FractionRing (AddMonoidAlgebra R G),
        ∀ r, f (algebraMap _ _ r) = algebraMap _ _ (j r) :=
    ⟨IsLocalization.map _ j h_nzd, IsLocalization.map_eq h_nzd⟩
  let z₀ : FractionRing (AddMonoidAlgebra R H) := IsLocalization.mk' _ a₀ ⟨b₀, hb₀_nzd⟩
  have hfz₀ : f z₀ = z := by
    apply (IsLocalization.map_units (FractionRing (AddMonoidAlgebra R G)) b).mul_right_cancel
    rw [← hb₀, ← hf_eq b₀, ← map_mul, IsLocalization.mk'_spec, hf_eq a₀, ha₀, hf_eq b₀, hb₀, hzb]
  have hcomp :
      (algebraMap (AddMonoidAlgebra R G) (FractionRing (AddMonoidAlgebra R G))).comp j =
        f.comp (algebraMap (AddMonoidAlgebra R H) (FractionRing (AddMonoidAlgebra R H))) :=
    RingHom.ext fun r ↦ (hf_eq r).symm
  have hz₀_int : IsIntegral (AddMonoidAlgebra R H) z₀ := ⟨p₀, hp₀_monic, f.injective <| by
    rw [map_zero, Polynomial.hom_eval₂, ← hcomp, ← Polynomial.eval₂_map, hp₀, hfz₀, hpz]⟩
  obtain ⟨y₀, hy₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hz₀_int
  exact ⟨j y₀, by rw [← hf_eq, hy₀, hfz₀]⟩

/-- Over an integral domain `R`, the group algebra `R[G]` of a torsion-free abelian group `G` is
integrally closed if and only if `R` is integrally closed. -/
@[simp]
theorem isIntegrallyClosed_iff {R G : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup G] [Module.IsTorsionFree ℤ G] :
    IsIntegrallyClosed (AddMonoidAlgebra R G) ↔ IsIntegrallyClosed R :=
  ⟨fun _ ↦ isIntegrallyClosed_coeffRing R G, fun _ ↦ inferInstance⟩

end AddMonoidAlgebra
