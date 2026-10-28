/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Polygon
public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.SidePairing
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
import TauCeti.Analysis.Complex.Fuchsian.Cusp.DirichletDomain
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Thick
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Cofinite
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Analysis.Complex.Fuchsian.Systole
import TauCeti.Analysis.Complex.UpperHalfPlane.Displacement
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Dirichlet polygons of cofinite Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be cofinite and `p ∈ ℍ`. This file shows that the Dirichlet domain of `Γ`
centred at `p` becomes bounded after removing finitely many cusp horodiscs. Consequently it is
the carrier of a finite-sided convex polygon whose ideal vertices are cusp points of `Γ`, and, if
`p` has trivial stabilizer, this polygon carries a side pairing by elements of `Γ`. Conversely,
the area of a convex polygon with finitely many vertices is finite by the Gauss–Bonnet formula,
so a discrete group is cofinite exactly when one (equivalently, every) Dirichlet domain centred at
a point with trivial stabilizer is such a polygon.

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
  the point of its orbit closest to `p`.
* **Parabolic part.** A parabolic element fixes a cusp point. There are finitely many cusp orbits
  (`Subgroup.IsCofinite.finite_cuspOrbit`), and for a cusp datum of each of them the points of the
  domain moved less than `δ` by a parabolic element fixing a cusp of that orbit lie in finitely
  many translates of a horodisc, apart from a bounded set, by the lemma
  `CuspDatum.exists_finset_isBounded_dirichletDomain_inter_setOf_dist_smul_lt_diff`.
  The translate of a horodisc by an element of `Γ` is a horodisc of the transported cusp datum.

No hypothesis that `Γ` is non-elementary is needed, and the centre `p` is arbitrary except where
the side pairing and the characterization of cofiniteness are concerned.

## Main results

* `Subgroup.isBounded_dirichletDomain_inter_setOf_dist_smul_le`: for a discrete group with finitely
  many elliptic orbits, the points of a Dirichlet domain moved a bounded distance by a nonidentity
  element fixing a point form a bounded set.
* `Subgroup.IsCofinite.exists_isBounded_dirichletDomain_diff_iUnion_horodisc`: a Dirichlet domain of
  a cofinite group is bounded outside finitely many cusp horodiscs.
* `Subgroup.IsCofinite.exists_convexPolygon_carrier_eq_dirichletDomain`: a Dirichlet domain of a
  cofinite group is a finite-sided convex polygon whose ideal vertices are cusp points.
* `Subgroup.IsCofinite.exists_sidePairing_of_mem_freeLocus`: for a centre with trivial
  stabilizer this polygon has a side pairing by elements of `Γ`.
* `Subgroup.isCofinite_iff_exists_convexPolygon_carrier_eq_dirichletDomain`: a discrete group is
  cofinite exactly when its Dirichlet domain at a point with trivial stabilizer is a finite-sided
  convex polygon.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§9.4 and 10.1 (geometrically finite groups; finite area implies finitely many
  sides).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Theorem 4.1.1 (Siegel's theorem) and §4.2.
* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick-thin decomposition of a finite-volume hyperbolic
  manifold).
-/

public section

open MeasureTheory MulAction Set UpperHalfPlane TauCeti TauCeti.UpperHalfPlane
open Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups OnePoint Pointwise

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- **The elliptic part of a Dirichlet domain is bounded.** Let `Γ ≤ PSL(2, ℝ)` be discrete with
finitely many elliptic orbits. For every centre `p` and every `ε`, the points of the Dirichlet
domain of `Γ` centred at `p` moved a distance at most `ε` by some nonidentity element of `Γ`
fixing a point of `ℍ` form a bounded set. -/
theorem isBounded_dirichletDomain_inter_setOf_dist_smul_le [DiscreteTopology Γ]
    (hΓ : Γ.ellipticOrbits.Finite) (p : ℍ) (ε : ℝ) :
    Bornology.IsBounded (dirichletDomain Γ p ∩
      {z | ∃ g : Γ, g ≠ 1 ∧ (∃ w : ℍ, g • w = w) ∧ dist (g • z) z ≤ ε}) := by
  -- the points moved at most `ε` by a nonidentity element fixing a chosen orbit representative
  let K : Set ℍ := ⋃ q ∈ Γ.ellipticOrbits, ⋃ g ∈ {g : Γ | g • q.out = q.out},
    {y | g ≠ 1 ∧ dist (g • y) y ≤ ε}
  have hK : Bornology.IsBounded K := by
    refine (Bornology.isBounded_biUnion hΓ).2 fun q _ ↦
      (Bornology.isBounded_biUnion (ProperlyDiscontinuousSMul.finite_stabilizer' Γ q.out)).2
        fun g hg ↦ ?_
    by_cases hg₁ : g = 1
    · simp [hg₁]
    · exact (isBounded_setOf_dist_smul_le_of_smul_eq_self
        (fun h ↦ hg₁ (Subtype.ext h)) hg ε).subset fun y hy ↦ hy.2
  refine (isBounded_dirichletDomain_inter_iUnion_smul (G := Γ) p hK).subset ?_
  rintro z ⟨hz, g, hg₁, ⟨w, hgw⟩, hgz⟩
  refine ⟨hz, ?_⟩
  -- move `w` to the chosen representative of its orbit, which is elliptic
  set q := Quotient.mk (orbitRel Γ ℍ) w
  have hq : q ∈ Γ.ellipticOrbits := by
    rw [quotientMk_mem_ellipticOrbits_iff, mem_freeLocus]
    exact fun h ↦ hg₁ ((Subgroup.eq_bot_iff_forall _).1 h g (mem_stabilizer_iff.2 hgw))
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, γ • w = q.out :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  refine mem_iUnion.2 ⟨γ⁻¹, γ • z, mem_iUnion₂.2 ⟨q, hq, mem_iUnion₂.2
    ⟨γ * g * γ⁻¹, ?_, ?_, ?_⟩⟩, inv_smul_smul γ z⟩
  · rw [mem_ofPred_eq, ← hγ, mul_smul, mul_smul, inv_smul_smul, hgw]
  · rwa [Ne, mul_inv_eq_one, mul_eq_left]
  · rwa [mul_smul, mul_smul, inv_smul_smul, dist_smul]

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
