/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Polygon
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Finite
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.HalfPlaneIntersection
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Dirichlet polygons of Fuchsian groups with cusps

Let `Γ ≤ PSL(2, ℝ)` be discrete. If the Dirichlet domain of `Γ` centred at `p` becomes bounded
after removing finitely many cusp horodiscs, then it is the carrier of a convex polygon, possibly
with ideal vertices, and every ideal vertex is the point of one of the cusp data
(`Subgroup.exists_convexPolygon_carrier_eq_dirichletDomain_of_isBounded_truncation`). The sides of
such a polygon are Dirichlet faces, by `ConvexPolygon.exists_side_eq_dirichletFace`, and for a
centre with trivial stabilizer it has a unique side pairing by elements of `Γ`, by
`ConvexPolygon.existsUnique_sidePairing_of_carrier_eq_dirichletDomain`.

Since a Dirichlet domain meets every orbit, the cusp compactification of `Γ` is then compact as
soon as `Γ` has finitely many cusp orbits
(`Subgroup.compactSpace_compactifiedQuotient_of_isBounded_truncation`).

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §§3.2 and 4.2.
-/

public section

open Set UpperHalfPlane TauCeti TauCeti.UpperHalfPlane MulAction
open scoped MatrixGroups OnePoint

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ] {ι : Type*} [Finite ι]

/-- **Dirichlet polygons with cusps.** If the Dirichlet domain of a discrete subgroup `Γ` centred
at `p` is bounded after removing finitely many cusp horodiscs of positive heights, it is the
carrier of a convex polygon, possibly with ideal vertices. Each ideal vertex is the cusp point of
one of the cusp data. -/
theorem exists_convexPolygon_carrier_eq_dirichletDomain_of_isBounded_truncation (p : ℍ)
    (D : ι → Γ.CuspDatum) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (dirichletDomain Γ p \ ⋃ i, (D i).horodisc (A i))) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n), P.carrier = dirichletDomain Γ p ∧
      ∀ i c, P.vertex i = .inr c → ∃ j, (D j).cusp = c := by
  obtain ⟨s, hmove, hD⟩ :=
    Γ.exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane_of_isBounded_truncation
      p D hA hb
  -- the centre lies strictly inside every bisector half-plane
  have hint :
      (interior (⋂ g ∈ s, _root_.closure (leftHalfPlane (perpBisector p (g • p))))).Nonempty := by
    refine ⟨p, ?_⟩
    simp only [Finset.interior_iInter, interior_closure_leftHalfPlane, mem_iInter₂]
    intro g hg
    rw [mem_leftHalfPlane_perpBisector_iff (hmove g hg), dist_self]
    exact dist_pos.2 (hmove g hg)
  have hH (i : ι) : (D i).horodisc (A i) = {z : ℍ | A i < ((D i).scaling • z).im} :=
    Set.ext fun _ ↦ TauCeti.Subgroup.CuspDatum.mem_horodisc _
  simp_rw [hH, hD] at hb
  obtain ⟨n, _, P, hP, -, hcusp⟩ := exists_convexPolygon_carrier_eq_iInter_closure_leftHalfPlane
    s (fun g ↦ perpBisector p (g • p)) hint (fun i ↦ (D i).scaling) hA hb
  refine ⟨n, inferInstance, P, hP.trans hD.symm, fun i c hi ↦ ?_⟩
  obtain ⟨j, hj⟩ := hcusp i c hi
  exact ⟨j, MulAction.injective (D j).scaling ((D j).scaling_smul_cusp.trans hj.symm)⟩

/-- **Compactness from a Dirichlet domain with a bounded cusp truncation.** If a discrete
subgroup `Γ` has finitely many cusp orbits, and some Dirichlet domain of `Γ` is bounded after
removing finitely many cusp horodiscs of positive heights, then the quotient `Γ \ ℍ` with its cusp
orbits adjoined is compact. -/
theorem compactSpace_compactifiedQuotient_of_isBounded_truncation [Finite Γ.CuspOrbit] (p : ℍ)
    (D : ι → Γ.CuspDatum) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (dirichletDomain Γ p \ ⋃ i, (D i).horodisc (A i))) :
    CompactSpace Γ.CompactifiedQuotient := by
  obtain ⟨n, _, P, hP, hcusp⟩ :=
    Γ.exists_convexPolygon_carrier_eq_dirichletDomain_of_isBounded_truncation p D hA hb
  refine P.compactSpace_compactifiedQuotient (fun q ↦ ?_) fun i c hi ↦ ?_
  · obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain (G := Γ) p z
    exact ⟨γ • z, hP ▸ hγ, Quotient.sound ⟨γ, rfl⟩⟩
  · obtain ⟨j, rfl⟩ := hcusp i c hi
    exact (D j).isCuspPoint

end Subgroup
