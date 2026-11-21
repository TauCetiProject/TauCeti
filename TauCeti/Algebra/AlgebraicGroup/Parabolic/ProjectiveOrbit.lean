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
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ProperDescent
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.SolvableSubgroup
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Proper homogeneous quotients and parabolic subgroups

Let `G` be a reduced affine group of finite type over an algebraically closed field `k` and let
`H` be a closed subgroup. The homogeneous quotient `G/H` is represented by a projective orbit
scheme, locally closed in the projective space of a finite-dimensional representation
(`HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints`). If that scheme is proper
over `k`, then `H` contains a conjugate of every Borel subgroup of `G`; when `H` is moreover
smooth, it is parabolic. In characteristic zero every closed subgroup is smooth by Cartier's
theorem, so properness of `G/H` alone makes `H` parabolic.

The proof follows Borel's argument. Properness, which does not depend on the chosen
representing orbit, transfers to an orbit of Chevalley's coset criterion, whose line has
stabilizer exactly `H` on rational points. A proper orbit scheme is closed in projective space,
so the Borel fixed-point theorem gives every connected solvable subgroup a fixed point on the
orbit, that is, a conjugate of it lies in the stabilizer `H`.

This is the direction "proper implies parabolic" of the characterization of parabolic subgroups
by completeness of `G/H`. Connectedness of `G` is not needed for it. Reducedness of `G`, which
over the algebraically closed field `k` amounts to smoothness, is assumed; in characteristic zero
it is automatic.

## Main declarations

* `TauCeti.HopfIdeal.exists_conjugate_le_of_isProper_projectiveOrbitToSpec`: if a projective
  orbit representing `G/H` is proper, every Borel candidate lies in a conjugate of `H`.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec`: a smooth
  closed subgroup with proper homogeneous quotient is parabolic.
* `TauCeti.HopfIdeal.isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec_of_charZero`:
  in characteristic zero, a closed subgroup with proper homogeneous quotient is parabolic.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Corollary 11.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.16.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §21.3.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {G : FiniteTypeCommHopfAlgCat.{u, u} k}
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k G M] [Module.Finite k M]

attribute [local instance] Comodule.exteriorPower

/-- **If `G/N` is proper, `N` contains a conjugate of every Borel subgroup.** Let `I`
define a closed subgroup `N` of a reduced affine group `G` of finite type over an algebraically
closed field. If some projective orbit scheme representing `G/N` is proper over the base field,
then every Borel candidate, in particular every Borel subgroup, lies in a conjugate of `N`. -/
theorem exists_conjugate_le_of_isProper_projectiveOrbitToSpec [IsReduced G]
    (I : HopfIdeal k G) {J : HopfIdeal k G} (hJ : IsBorelCandidate k G J)
    {m : M} {hm : Module.IsUnimodular k m}
    (e : CommHopfAlgCat.fppfHomogeneousQuotient G.obj I ≅
      Comodule.projectiveOrbitPointsSheaf (H := G.obj) m hm)
    [IsProper (Comodule.projectiveOrbitToSpec (H := G) m hm)] :
    ∃ g : WithConv (G →ₐ[k] k), I.conjugate g ≤ J := by
  have := Algebra.FiniteType.isNoetherianRing k G
  -- Chevalley's coset criterion supplies an orbit whose line has stabilizer `N`.
  obtain ⟨V, n, hV, m', hm', hcoset⟩ :=
    I.exists_finite_subcomodule_exteriorPower_coset_matrixCoefficient.{u, u, u}
      (IsNoetherian.noetherian I.toIdeal)
  let : Module.Finite k V := hV
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  -- Properness does not depend on the orbit representing `G/N`, and makes that orbit closed.
  have : IsProper (Comodule.projectiveOrbitToSpec (H := G) m' hm') :=
    Comodule.isProper_projectiveOrbitToSpec_of_le le_rfl e
      (Comodule.fppfHomogeneousQuotientIsoProjectiveOrbitPoints I m' hm' hcoset)
  have hclosed := Comodule.isClosed_range_projectiveOrbitMap_of_isProper (H := G) m' hm'
  -- The rational points of `N` are exactly the stabilizer of the base point `[m']`.
  have hstab := Comodule.mem_quotientPointsSubgroup_iff_projectiveOrbitMap_kernelPoint_eq hm'
    (hcoset (CommAlgCat.of k k))
  exact hJ.exists_conjugate_le fun K _ _ _ ↦
    exists_conjugate_le_of_isClosed_projectiveOrbit I K m' hm' hclosed hstab

/-- **Proper implies parabolic.** Over an algebraically closed field, a smooth closed subgroup of
a reduced affine group of finite type is parabolic as soon as some projective orbit scheme
representing its homogeneous quotient is proper over the base field. -/
theorem isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec [IsReduced G]
    (I : HopfIdeal k G)
    (hI : smoothCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient G I).obj)
    {m : M} {hm : Module.IsUnimodular k m}
    (e : CommHopfAlgCat.fppfHomogeneousQuotient G.obj I ≅
      Comodule.projectiveOrbitPointsSheaf (H := G.obj) m hm)
    [IsProper (Comodule.projectiveOrbitToSpec (H := G) m hm)] :
    IsParabolicOverAlgClosed k G I := by
  obtain ⟨J, hJ⟩ := exists_minimal_isBorelCandidate G
  have hJB : IsBorelOverAlgClosed k G J := (isBorelOverAlgClosed_iff k G J).mpr ⟨inferInstance, hJ⟩
  exact (isParabolicOverAlgClosed_iff_exists_conjugate_le hJB).mpr
    ⟨hI, exists_conjugate_le_of_isProper_projectiveOrbitToSpec I hJ.prop e⟩

/-- **Proper implies parabolic in characteristic zero.** Over an algebraically closed field of
characteristic zero, every closed subgroup of an affine group of finite type whose homogeneous
quotient is represented by a proper projective orbit scheme is parabolic. Cartier's theorem
supplies the smoothness of the group and of the subgroup. -/
theorem isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec_of_charZero [CharZero k]
    (I : HopfIdeal k G) {m : M} {hm : Module.IsUnimodular k m}
    (e : CommHopfAlgCat.fppfHomogeneousQuotient G.obj I ≅
      Comodule.projectiveOrbitPointsSheaf (H := G.obj) m hm)
    [IsProper (Comodule.projectiveOrbitToSpec (H := G) m hm)] :
    IsParabolicOverAlgClosed k G I := by
  have := (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k G.obj)
  have : IsReduced G := isReduced_of_smooth k G
  exact isParabolicOverAlgClosed_of_isProper_projectiveOrbitToSpec I
    (smoothCommHopfAlgProperty_of_charZero k _) e

end TauCeti.HopfIdeal
