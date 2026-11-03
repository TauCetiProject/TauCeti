/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Polygon
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.SidePairing
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
import TauCeti.Analysis.Complex.Fuchsian.Cusp.DirichletDomain
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Elliptic
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Thick
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.Polygon.LocallyFinite
import TauCeti.Analysis.Complex.Fuchsian.Systole
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.ParabolicCycle
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Stabilizer

/-!
# Dirichlet polygons of cofinite Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be cofinite and `p ∈ ℍ`. This file shows that the Dirichlet domain of `Γ`
centred at `p` becomes bounded after removing finitely many cusp horodiscs. Consequently it is
the carrier of a finite-sided convex polygon whose ideal vertices are cusp points of `Γ`, and, if
`p` has trivial stabilizer, this polygon carries a side pairing by elements of `Γ`. Conversely,
the area of a convex polygon with finitely many vertices is finite by the Gauss–Bonnet formula,
so a discrete group is cofinite exactly when one (equivalently, every) Dirichlet domain centred at
a point with trivial stabilizer is such a polygon. Its translates are locally finite with disjoint
interiors, so its side pairing satisfies the hypotheses of Poincaré's polygon theorem, generates
`Γ`, and presents it.

The bounded truncation also gives compactness of the cusp compactification of `Γ`: the polygon
minus cusp horodiscs is a compact set meeting every orbit outside the corresponding cusp
neighbourhoods, and there are finitely many cusp orbits.

Fix `δ > 0` so that every element of `Γ` moving some point less than `δ` fixes a point of `ℍ` or
is parabolic (`Subgroup.IsCofinite.exists_pos_exists_smul_eq_or_isParabolic_of_dist_smul_lt`).
A point of the Dirichlet domain lies in one of three parts.

* **Thick part.** The points moved at least `δ` by every nonidentity element form a bounded part
  of the domain, by a packing argument
  (`Subgroup.IsCofinite.isBounded_dirichletDomain_inter_thickPart`).
* **Elliptic part.** A nonidentity element fixing a point `w` moves only a bounded set of points
  less than `δ`. There are finitely many elliptic orbits
  (`Subgroup.IsCofinite.finite_ellipticOrbits`), and each stabilizer is finite, so the points
  moved less than `δ` by a nonidentity element fixing a point lie in the `Γ`-orbit of a bounded
  set. Its intersection with the Dirichlet domain is bounded, because a point of the domain is
  the point of its orbit closest to `p`
  (`Subgroup.isBounded_dirichletDomain_inter_setOf_dist_smul_le`).
* **Parabolic part.** A parabolic element fixes a cusp point. There are finitely many cusp orbits
  (`Subgroup.IsCofinite.finite_cuspOrbit`), and for a cusp datum of each of them the points of the
  domain moved less than `δ` by a parabolic element fixing a cusp of that orbit lie in finitely
  many translates of a horodisc, apart from a bounded set, by the lemma
  `CuspDatum.exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff`.
  The translate of a horodisc by an element of `Γ` is a horodisc of the transported cusp datum.

No hypothesis that `Γ` is non-elementary is needed, and the centre `p` is arbitrary except where
the side pairing and the characterization of cofiniteness are concerned.

## Main results

* `Subgroup.IsCofinite.exists_isBounded_dirichletDomain_diff_iUnion_horodisc`: a Dirichlet domain of
  a cofinite group is bounded outside finitely many cusp horodiscs.
* `Subgroup.IsCofinite.exists_convexPolygon_carrier_eq_dirichletDomain`: a Dirichlet domain of a
  cofinite group is a finite-sided convex polygon whose ideal vertices are cusp points.
* `Subgroup.IsCofinite.compactSpace_compactifiedQuotient`: the cusp compactification of a
  cofinite group is compact.
* `Subgroup.IsCofinite.exists_sidePairing_of_mem_freeLocus`: for a centre with trivial
  stabilizer this polygon has a side pairing by elements of `Γ`.
* `Subgroup.isCofinite_iff_exists_convexPolygon_carrier_eq_dirichletDomain`: a discrete group is
  cofinite exactly when its Dirichlet domain at a point with trivial stabilizer is a finite-sided
  convex polygon.
* `Subgroup.IsCofinite.exists_sidePairing_closure_range_map_eq`: the converse of Poincaré's
  polygon theorem; the side pairing of this polygon generates `Γ` and satisfies the angle
  condition at finite vertex cycles and the parabolic condition at ideal vertex cycles.
* `Subgroup.IsCofinite.exists_sidePairing_relatorQuotientTo_bijective`: `Γ` is presented by the
  side pairing of this polygon.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§9.4 and 10.1 (geometrically finite groups; finite area implies finitely many
  sides) and §9.8 (Poincaré's theorem; the side pairing of a Dirichlet polygon generates and
  presents the group).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Theorem 4.1.1 (Siegel's theorem), §4.2, and §4.3 (the converse of Poincaré's
  theorem and the presentation by side pairings).
* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick-thin decomposition of a finite-volume hyperbolic
  manifold).
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti TauCeti.UpperHalfPlane
open Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups OnePoint Pointwise Real

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- **Dirichlet domains of cofinite groups have bounded cusp truncations.** For a cofinite
`Γ ≤ PSL(2, ℝ)` and any centre `p`, the Dirichlet domain of `Γ` centred at `p` is bounded after
removing finitely many horodiscs of cusp data of `Γ`, at positive heights. -/
theorem IsCofinite.exists_isBounded_dirichletDomain_diff_iUnion_horodisc (hΓ : Γ.IsCofinite)
    (p : ℍ) :
    ∃ (n : ℕ) (D : Fin n → Γ.CuspDatum) (A : Fin n → ℝ), (∀ i, 0 < A i) ∧
      Bornology.IsBounded (dirichletDomain Γ p \ ⋃ i, (D i).horodisc (A i)) := by
  have := hΓ.discreteTopology
  have := hΓ.finite_cuspOrbit
  obtain ⟨δ, hδ, hδΓ⟩ := hΓ.exists_pos_exists_smul_eq_or_isParabolic_of_dist_smul_lt
  -- at a cusp datum of each cusp orbit, finitely many translates of a horodisc of height `A C`
  -- cover the parabolic part of the domain, apart from a bounded set
  let A (C : Γ.CuspOrbit) : ℝ := (C.cuspDatum.scaling • p).im + C.cuspDatum.width / 2
  have hA (C : Γ.CuspOrbit) : 0 < A C := add_pos (im_pos _) (half_pos C.cuspDatum.width_pos)
  choose s hs using fun C : Γ.CuspOrbit ↦
    C.cuspDatum.exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff p hδ
  -- these translates are the horodiscs of the transported cusp data
  let E (i : Σ C : Γ.CuspOrbit, s C) : Γ.CuspDatum :=
    i.1.cuspDatum.conj (conjAct_pointwise_smul_eq_self (le_normalizer i.2.1.2))
  have hE (i : Σ C : Γ.CuspOrbit, s C) :
      (E i).horodisc (A i.1) = (i.2 : Γ) • i.1.cuspDatum.horodisc (A i.1) :=
    i.1.cuspDatum.horodisc_conj _ _
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Σ C : Γ.CuspOrbit, s C)
  refine ⟨n, E ∘ e.symm, fun j ↦ A (e.symm j).1, fun j ↦ hA _, ?_⟩
  refine ((hΓ.isBounded_dirichletDomain_inter_thickPart p hδ).union
    ((isBounded_dirichletDomain_inter_setOf_dist_smul_le hΓ.finite_ellipticOrbits p δ).union
      (Bornology.isBounded_iUnion.2 fun C ↦ hs C (A C) le_rfl))).subset ?_
  rintro z ⟨hz, hzA⟩
  by_cases hthick : z ∈ thickPart Γ δ
  · exact Or.inl ⟨hz, hthick⟩
  right
  simp only [mem_thickPart, not_forall, not_le, exists_prop] at hthick
  obtain ⟨g, hg₁, hgz⟩ := hthick
  rcases hδΓ g g.2 z hgz with ⟨w, hw⟩ | hpar
  · exact Or.inl ⟨hz, g, hg₁, ⟨w, hw⟩, hgz.le⟩
  -- a parabolic element fixes a cusp point, in the orbit of the cusp of a chosen datum
  right
  obtain ⟨D₀, hD₀⟩ := (isCuspPoint_iff_exists_parabolicFixedPoint_eq.2
    ⟨g, hpar, rfl⟩).exists_cuspDatum_cusp_eq
  obtain ⟨γ, hγ : γ • _ = D₀.cusp⟩ := (D₀.cuspOrbit_eq_iff D₀.cuspOrbit.cuspDatum).1
    D₀.cuspOrbit.cuspOrbit_cuspDatum.symm
  have hgγ : g ∈ stabilizer Γ (γ • D₀.cuspOrbit.cuspDatum.cusp) := by
    rw [mem_stabilizer_iff, hγ, hD₀]
    exact hpar.smul_parabolicFixedPoint
  refine mem_iUnion.2 ⟨D₀.cuspOrbit, ⟨hz, γ, g, hgγ, hg₁, hgz⟩, fun hzs ↦ hzA ?_⟩
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hzs
  refine mem_iUnion.2 ⟨e ⟨D₀.cuspOrbit, k, hk⟩, ?_⟩
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hE]
  exact hzk

/-- **Compactness for cofinite groups.** For a cofinite `Γ ≤ PSL(2, ℝ)`, the quotient `Γ \ ℍ`
with its finitely many cusp orbits adjoined is compact. Together with
`Subgroup.CompactifiedQuotient.instT2Space` and
`Subgroup.CompactifiedQuotient.instSecondCountableTopology`, it is a compact Hausdorff
second-countable space. The discreteness instance is part of `Γ.IsCofinite`; it is assumed
separately only because the topology on `Γ.CompactifiedQuotient` is defined from it. -/
theorem IsCofinite.compactSpace_compactifiedQuotient [DiscreteTopology Γ] (hΓ : Γ.IsCofinite) :
    CompactSpace Γ.CompactifiedQuotient := by
  have := hΓ.finite_cuspOrbit
  obtain ⟨n, D, A, hA, hb⟩ := hΓ.exists_isBounded_dirichletDomain_diff_iUnion_horodisc I
  exact Γ.compactSpace_compactifiedQuotient_of_isBounded_truncation I D hA hb

/-- **Dirichlet polygons of cofinite groups.** For a cofinite `Γ ≤ PSL(2, ℝ)` and any centre `p`,
the Dirichlet domain of `Γ` centred at `p` is the carrier of a convex polygon with finitely many
vertices, possibly ideal. Every ideal vertex is a cusp point of `Γ`. -/
theorem IsCofinite.exists_convexPolygon_carrier_eq_dirichletDomain (hΓ : Γ.IsCofinite) (p : ℍ) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n), P.carrier = dirichletDomain Γ p ∧
      ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c := by
  have := hΓ.discreteTopology
  obtain ⟨m, D, A, hA, hb⟩ := hΓ.exists_isBounded_dirichletDomain_diff_iUnion_horodisc p
  obtain ⟨n, hn, P, hP, hcusp⟩ :=
    Γ.exists_convexPolygon_carrier_eq_dirichletDomain_of_isBounded_truncation p D hA hb
  refine ⟨n, hn, P, hP, fun i c hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := hcusp i c hi
  exact (D j).isCuspPoint

/-- **Side pairings of Dirichlet polygons of cofinite groups.** For a cofinite `Γ ≤ PSL(2, ℝ)` and
a centre `p` with trivial stabilizer, the Dirichlet domain of `Γ` centred at `p` is the carrier of
a convex polygon with finitely many vertices, whose ideal vertices are cusp points of `Γ`, and
whose sides are paired by elements of `Γ`. This side pairing is unique, by
`TauCeti.UpperHalfPlane.ConvexPolygon.existsUnique_sidePairing_of_carrier_eq_dirichletDomain`. -/
theorem IsCofinite.exists_sidePairing_of_mem_freeLocus (hΓ : Γ.IsCofinite) {p : ℍ}
    (hp : p ∈ freeLocus Γ ℍ) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n) (σ : P.SidePairing),
      (∀ i, σ.map i ∈ Γ) ∧ P.carrier = dirichletDomain Γ p ∧
        ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c := by
  have := hΓ.discreteTopology
  obtain ⟨n, hn, P, hP, hcusp⟩ := hΓ.exists_convexPolygon_carrier_eq_dirichletDomain p
  obtain ⟨σ, hσ, -⟩ := ConvexPolygon.existsUnique_sidePairing_of_carrier_eq_dirichletDomain hP hp
  exact ⟨n, hn, P, σ, hσ, hP, hcusp⟩

/-- **The converse of Poincaré's polygon theorem.** Every cofinite `Γ ≤ PSL(2, ℝ)` arises from
Poincaré's polygon theorem. For a centre `p` with trivial stabilizer, the Dirichlet domain of `Γ`
centred at `p` is the carrier of a convex polygon with finitely many vertices and a side pairing
whose maps generate `Γ`. The cycle transformation of each finite vertex has finite order `m` and
the interior angles along its cycle add up to `2π / m`, and the cycle transformation of each ideal
vertex is parabolic. These are the hypotheses of
`TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing.isCofinite_of_isParabolic`. -/
theorem IsCofinite.exists_sidePairing_closure_range_map_eq (hΓ : Γ.IsCofinite) {p : ℍ}
    (hp : p ∈ freeLocus Γ ℍ) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n) (σ : P.SidePairing),
      P.carrier = dirichletDomain Γ p ∧ closure (range σ.map) = Γ ∧
        (∀ j (z : ℍ), P.vertex j = .inl z →
          (orderOf (σ.cycleMap j) : ℝ) * σ.cycleAngleSum j = 2 * π) ∧
        ∀ j ξ, P.vertex j = .inr ξ → IsParabolic (σ.cycleMap j) := by
  have := hΓ.discreteTopology
  obtain ⟨n, hn, P, σ, hσ, hP, hcusp⟩ := hΓ.exists_sidePairing_of_mem_freeLocus hp
  have hlf := P.locallyFinite_smul_carrier_of_isCuspPoint hcusp
  have hdisj := ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain hP hp
  exact ⟨n, hn, P, σ, hP, σ.closure_range_map_eq hσ hlf hdisj,
    fun _ _ hz ↦ σ.orderOf_cycleMap_mul_cycleAngleSum hz hσ hdisj,
    fun _ _ hj ↦ σ.isParabolic_cycleMap_of_locallyFinite hj (σ.cycleMap_mem hσ _) hlf⟩

/-- **Dirichlet presentations of cofinite Fuchsian groups.** For a cofinite `Γ ≤ PSL(2, ℝ)` and a
centre `p` with trivial stabilizer, the Dirichlet domain of `Γ` centred at `p` is the carrier of a
convex polygon with finitely many vertices and a side pairing by elements of `Γ`, and `Γ` is
presented by the side-pairing maps, subject to the side relations and the finite-vertex cycle
relations. -/
theorem IsCofinite.exists_sidePairing_relatorQuotientTo_bijective (hΓ : Γ.IsCofinite) {p : ℍ}
    (hp : p ∈ freeLocus Γ ℍ) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n) (σ : P.SidePairing)
      (hmap : ∀ i, σ.map i ∈ Γ),
      P.carrier = dirichletDomain Γ p ∧ Function.Bijective (σ.relatorQuotientTo hmap) := by
  have := hΓ.discreteTopology
  obtain ⟨n, hn, P, σ, hσ, hP, hcusp⟩ := hΓ.exists_sidePairing_of_mem_freeLocus hp
  exact ⟨n, hn, P, σ, hσ, hP, σ.relatorQuotientTo_bijective hσ
    (P.locallyFinite_smul_carrier_of_isCuspPoint hcusp)
    (ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain hP hp)⟩

/-- **Cofiniteness from Dirichlet polygons.** A discrete subgroup `Γ ≤ PSL(2, ℝ)` is cofinite
exactly when its Dirichlet domain centred at a point `p` with trivial stabilizer is the carrier
of a convex polygon with finitely many vertices, possibly ideal. The converse direction is the
Gauss–Bonnet formula: such a polygon has finite area. -/
theorem isCofinite_iff_exists_convexPolygon_carrier_eq_dirichletDomain [DiscreteTopology Γ]
    {p : ℍ} (hp : p ∈ freeLocus Γ ℍ) :
    Γ.IsCofinite ↔
      ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n), P.carrier = dirichletDomain Γ p := by
  refine ⟨fun hΓ ↦ ?_, fun ⟨n, _, P, hP⟩ ↦ ?_⟩
  · obtain ⟨n, hn, P, hP, -⟩ := hΓ.exists_convexPolygon_carrier_eq_dirichletDomain p
    exact ⟨n, hn, P, hP⟩
  · refine (Γ.isFundamentalDomain_dirichletDomain hp).isCofinite_of_volume_ne_top ?_
    rw [← hP, ConvexPolygon.volume_carrier]
    exact ENNReal.ofReal_ne_top

end Subgroup
