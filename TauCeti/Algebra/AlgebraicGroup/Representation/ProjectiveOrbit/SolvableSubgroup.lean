/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.FixedPoint.Existence
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Naturality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-!
# Solvable subgroups and closed projective orbits

A reduced connected solvable group mapping to an affine group fixes a rational point of
every closed projective orbit of the latter. The ambient group need not be connected or
reduced. Restriction of the representation makes the orbit an invariant closed subset for
the solvable group, so the projective Borel fixed-point theorem applies.

Consequently a reduced connected solvable closed subgroup is contained in a conjugate of
the stabilizer of such an orbit's base point. The conclusion is an inclusion of closed
subgroup schemes: reducedness of the solvable subgroup upgrades rational-point containment
to an inclusion of defining Hopf ideals. This is the fixed-point step in conjugacy of Borel
subgroups with projective homogeneous space.

The proof uses `Comodule.exists_fixed_mem_of_isClosed_of_isSolvable`, the rational-point
description of projective orbits, and `HopfIdeal.le_of_quotientPointsSubgroup_le`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§10--11.
* J. S. Milne, *Algebraic Groups* (2017), Theorems 17.5--17.6.
-/

public section

open CategoryTheory AlgebraicGeometry WithConv TopologicalSpace

open TauCeti TauCeti.Comodule

namespace BialgHom

universe u

variable {k H K M : Type u} [Field k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
  [IsReduced K] [ConnectedSpace (PrimeSpectrum K)]
  [Group.IsSolvable (WithConv (K →ₐ[k] k))]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- A morphism from a reduced connected solvable group fixes a rational point of every
closed projective orbit of the target group. The fixed point is exhibited as the orbit
image of an ambient rational group point. -/
theorem exists_projectiveOrbitMap_kernelPoint_fixed_of_isClosed_of_isSolvable
    (f : H →ₐc[k] K) (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm))) :
    ∃ g : WithConv (H →ₐ[k] k), ∀ h : WithConv (K →ₐ[k] k),
      (projectivePointTranslation (M := M) (BialgHom.mapDomain f h)).hom
          (projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) =
        projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv) := by
  let : Comodule k K M := Corestrict f.toCoalgHom
  have hinvariant : ∀ h : WithConv (K →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) h).hom
        (Set.range (projectiveOrbitMap (H := H) m hm))
        (Set.range (projectiveOrbitMap (H := H) m hm)) := by
    intro h
    rw [BialgHom.projectivePointTranslation_corestrict]
    exact Set.mapsTo_iff_image_subset.mpr
      (image_projectivePointTranslation_range_projectiveOrbitMap
        (BialgHom.mapDomain f h) m hm).le
  obtain ⟨x, hx, hxc, hfixed⟩ := exists_fixed_mem_of_isClosed_of_isSolvable
    (H := K) hclosed ⟨_, Set.mem_range_self
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))⟩ hinvariant
  have hx' : x ∈ Set.range (fun g : WithConv (H →ₐ[k] k) ↦
      projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint g.ofConv)) := by
    rw [range_projectiveOrbitMap_kernelPoint_eq_range_inter_closedPoints]
    exact ⟨hx, hxc⟩
  obtain ⟨g, rfl⟩ := hx'
  exact ⟨g, fun h ↦ by
    simpa only [BialgHom.projectivePointTranslation_corestrict] using hfixed h⟩

end BialgHom

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- A reduced connected solvable closed subgroup is contained scheme-theoretically in a
conjugate of the stabilizer of a point in a closed projective orbit. The stabilizer is
specified by its rational-point fiber; no smoothness of that stabilizer is required. -/
theorem exists_conjugate_le_of_isClosed_projectiveOrbit
    (D I : HopfIdeal k H) [IsReduced (FiniteTypeCommHopfAlgCat.quotient H I)]
    [ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I))]
    [Group.IsSolvable (WithConv ((FiniteTypeCommHopfAlgCat.quotient H I) →ₐ[k] k))]
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (Comodule.projectiveOrbitMap (H := H) m hm)))
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj D (CommAlgCat.of k k) ↔
        Comodule.projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          Comodule.projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) :
    ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I := by
  let q := (CommHopfAlgCat.mkQuotient H.obj I).hom
  obtain ⟨g, hg⟩ :=
    q.exists_projectiveOrbitMap_kernelPoint_fixed_of_isClosed_of_isSolvable m hm hclosed
  refine ⟨g, le_of_quotientPointsSubgroup_le (K := k) ?_⟩
  intro a ha
  obtain ⟨h, rfl⟩ := ha
  let b := BialgHom.mapDomain q h
  have hb : (CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)).hom h = b := by
    dsimp only [b]
    rw [BialgHom.mapDomain_apply]
    exact CommHopfAlgCat.quotientPointsHom_apply H.obj I (CommAlgCat.of k k) h
  rw [hb]
  have hfix := hg h
  rw [Comodule.projectivePointTranslation_projectiveOrbitMap_kernelPoint] at hfix
  have hconj := congrArg (fun x ↦ (Comodule.projectivePointTranslation (M := M) g⁻¹).hom x) hfix
  simp only [Comodule.projectivePointTranslation_projectiveOrbitMap_kernelPoint,
    ← mul_assoc, inv_mul_cancel] at hconj
  have hmem : g⁻¹ * b * g ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj D (CommAlgCat.of k k) := by
    apply (hstab _).mpr
    simpa only [b, mul_assoc, AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] using hconj
  have hc := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff D g
    (CommAlgCat.of k k) (g⁻¹ * b * g)).mpr hmem
  have hc' := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hc
  apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj _ _ b).mpr
  simpa [Algebra.ofId_self, AlgHom.mapValue_id, mul_assoc] using hc'

end TauCeti.HopfIdeal
