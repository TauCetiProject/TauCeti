/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence
import TauCeti.Algebra.AlgebraicGroup.Borel.ProjectiveOrbit
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Proper homogeneous quotients have parabolic stabilizers

Let `G` be an affine group of finite type over an algebraically closed field `k` and let `N` be a
closed subgroup. Realize the homogeneous quotient `G/N` as the projective orbit scheme of a line
in a finite-dimensional representation of `G`, by an isomorphism of fppf sheaves compatible with
the projections from `G`. When `G` is reduced, every closed subgroup admits such a realization
by `HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints`; for non-reduced `G`
the theorems apply whenever such a realization is supplied. If this orbit scheme is proper over
`k`, then `N` contains a conjugate of every Borel subgroup of `G`; if `N` is moreover smooth, it
is parabolic. This is the implication from properness to parabolicity in the
characterization of parabolic subgroups by complete homogeneous quotients.

Properness makes the orbit closed in projective space. A Borel subgroup `B` acts on this closed
orbit through the ambient group, and by the Borel fixed-point theorem it fixes a rational point
`g • x` of the orbit, where `x` is the base point. The compatibility of the representing
isomorphism identifies the rational stabilizer of `x` with `N(k)`, so `g⁻¹ B(k) g ⊆ N(k)`, and
reducedness of `B` upgrades this to containment of closed subgroup schemes.

The theorems themselves impose no smoothness, reducedness or connectedness on `G`, and the
containment statement imposes none on `N`. In characteristic zero, Cartier's theorem makes every
closed subgroup smooth, so properness of the representing orbit alone makes `N` parabolic.

## Main declarations

* `TauCeti.HopfIdeal.exists_conjugate_le_of_isProper_projectiveOrbitToSpec`: if the representing
  orbit is proper, every Borel candidate, in particular every Borel subgroup, lies in a conjugate
  of `N`.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec`: a smooth closed
  subgroup whose representing orbit is proper is parabolic.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec_of_charZero`: the
  same conclusion in characteristic zero, for every closed subgroup.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.16.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.HopfIdeal

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Borel subgroups lie in conjugates of a subgroup with proper quotient.** Let the projective
orbit of the line through `m` represent the homogeneous quotient `G/N` compatibly with the
projections from `G`. If this orbit scheme is proper over the base field, then every Borel
candidate, in particular every Borel subgroup, is contained in a conjugate of `N`. -/
theorem exists_conjugate_le_of_isProper_projectiveOrbitToSpec
    (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (e : CommHopfAlgCat.fppfHomogeneousQuotient (.of k H) I ≅
      Comodule.projectiveOrbitPointsSheaf (H := .of k H) m hm)
    (he : CommHopfAlgCat.fppfHomogeneousQuotientProjection (.of k H) I ≫ e.hom.hom =
      Comodule.toProjectiveOrbitPoints m hm)
    (hproper : IsProper (Comodule.projectiveOrbitToSpec (H := H) m hm))
    {J : HopfIdeal k H} (hJ : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g ≤ J := by
  have hclosed := (Comodule.isProper_projectiveOrbitToSpec_iff_isClosed M m hm).mp hproper
  have hstab := Comodule.projectiveOrbitMap_kernelPoint_eq_one_iff_mem_quotientPointsSubgroup
    (H := .of k H) I m hm e he
  exact hJ.exists_conjugate_le fun J _ _ _ ↦
    exists_conjugate_le_of_isClosed_projectiveOrbit (H := FiniteTypeCommHopfAlgCat.of k H) I J m hm
      hclosed fun a ↦ (hstab a).symm

/-- **Proper homogeneous quotients have parabolic stabilizers.** Let the projective orbit of the
line through `m` represent the homogeneous quotient `G/N` compatibly with the projections from
`G`. If `N` is smooth and this orbit scheme is proper over the base field, then `N` is a parabolic
subgroup. -/
theorem isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec
    (I : HopfIdeal k H)
    (hI : smoothCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I).obj)
    (m : M) (hm : Module.IsUnimodular k m)
    (e : CommHopfAlgCat.fppfHomogeneousQuotient (.of k H) I ≅
      Comodule.projectiveOrbitPointsSheaf (H := .of k H) m hm)
    (he : CommHopfAlgCat.fppfHomogeneousQuotientProjection (.of k H) I ≫ e.hom.hom =
      Comodule.toProjectiveOrbitPoints m hm)
    (hproper : IsProper (Comodule.projectiveOrbitToSpec (H := H) m hm)) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I := by
  obtain ⟨B, hB⟩ := exists_minimal_isBorelCandidate (FiniteTypeCommHopfAlgCat.of k H)
  exact (isParabolicOverAlgClosed_iff_exists_conjugate_le (J := B)
    ((isBorelOverAlgClosed_iff _ _ _).mpr ⟨inferInstance, hB⟩)).mpr
    ⟨hI, exists_conjugate_le_of_isProper_projectiveOrbitToSpec I m hm e he hproper hB.prop⟩

/-- **Proper homogeneous quotients in characteristic zero.** Over an algebraically closed field
of characteristic zero, if the projective orbit of the line through `m` represents `G/N`
compatibly with the projections from `G` and is proper over the base field, then the closed
subgroup `N` is parabolic. Smoothness of `N` is automatic by Cartier's theorem. -/
theorem isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec_of_charZero [CharZero k]
    (I : HopfIdeal k H) (m : M) (hm : Module.IsUnimodular k m)
    (e : CommHopfAlgCat.fppfHomogeneousQuotient (.of k H) I ≅
      Comodule.projectiveOrbitPointsSheaf (H := .of k H) m hm)
    (he : CommHopfAlgCat.fppfHomogeneousQuotientProjection (.of k H) I ≫ e.hom.hom =
      Comodule.toProjectiveOrbitPoints m hm)
    (hproper : IsProper (Comodule.projectiveOrbitToSpec (H := H) m hm)) :
    IsParabolicOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I :=
  isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec I
    (smoothCommHopfAlgProperty_of_charZero k _) m hm e he hproper

end TauCeti.HopfIdeal
