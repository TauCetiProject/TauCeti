/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Polygon
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Presentation
import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Faces
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides

/-!
# The side pairing of a Dirichlet polygon

Let `Γ ≤ PSL(2, ℝ)` be discrete, let `p ∈ ℍ` have trivial stabilizer in `Γ`, and let `P` be a
convex polygon, possibly with ideal vertices, whose carrier is the Dirichlet domain of `Γ`
centred at `p`. Every side of `P` is the Dirichlet face `dirichletFace p g` of a unique `g ≠ 1`,
the part of the domain equidistant from `p` and `g • p`, and `g⁻¹` carries it onto the face of
`g⁻¹`, again a side. This file shows that these identifications form a side pairing of `P` in
the sense of `ConvexPolygon.SidePairing`: `g⁻¹` reverses the orientation of the sides, since it
moves the centre `p` across the bisector of `p` and `g⁻¹ • p`. It is the only side pairing of `P`
by elements of `Γ`.

The translates of a Dirichlet polygon by `Γ` are locally finite, and, since the centre has
trivial stabilizer, every nonidentity element of `Γ` moves its interior off itself. These are
the tessellation hypotheses of Poincaré's polygon theorem, under which the side-pairing maps
generate `Γ` and present it, subject to the side relations and the vertex-cycle relations. For a
cocompact group every Dirichlet domain is a compact convex polygon, so every cocompact group has
such a Dirichlet presentation.

## Main results

* `ConvexPolygon.existsUnique_sidePairing_of_carrier_eq_dirichletDomain`: a Dirichlet polygon
  has exactly one side pairing whose maps lie in `Γ`.
* `ConvexPolygon.SidePairing.side_eq_dirichletFace`: for that side pairing, side `i` is the
  Dirichlet face of the inverse of the side-pairing map of `i`.
* `ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain`: the translates of
  a Dirichlet polygon have disjoint interiors.
* `Subgroup.exists_sidePairing_relatorQuotientTo_bijective_of_compactSpace`: a cocompact
  Fuchsian group is presented by the side pairing of a compact Dirichlet polygon.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4 (Dirichlet polygons and their side pairings).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.2 and 4.1 (generators of a Fuchsian group from its Dirichlet region).
-/

public section

open MulAction Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {Γ : Subgroup PSL(2, ℝ)} {p : ℍ} {n : ℕ} [NeZero n] {P : ConvexPolygon n}

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- If side `i` of a Dirichlet polygon is the face of `h⁻¹` and side `j` the face of `h`, then
`h` carries side `i` onto side `j` with the orientation reversed. The same orientation would put
both `p` and `h • p` strictly on one side of their perpendicular bisector. -/
private theorem smul_vertex_eq (hP : P.carrier = dirichletDomain Γ p)
    (hp : p ∈ TauCeti.freeLocus Γ ℍ) {h : Γ} (hh : h ≠ 1) {i j : Fin n}
    (hi : P.side i = dirichletFace p h⁻¹) (hj : P.side j = dirichletFace p h) :
    (h : PSL(2, ℝ)) • P.vertex i = P.vertex (j + 1) ∧
      (h : PSL(2, ℝ)) • P.vertex (i + 1) = P.vertex j := by
  have hhp := TauCeti.smul_ne_of_ne_one Γ ℍ hp hh
  have hside : ((h : PSL(2, ℝ)) • P).side i = P.side j := by
    have hinv := inv_smul_dirichletFace p h⁻¹
    rw [inv_inv, Set.subtype_smul_set] at hinv
    rw [side_smul, hi, hj, hinv]
  -- the supporting lines of side `i` of the translate and of side `j` coincide
  obtain ⟨x, hx, y, hy, hxy⟩ := P.side_nontrivial j
  have hlines : range (geodesicLine (((h : PSL(2, ℝ)) • P).sideGeodesic i)) =
      range (geodesicLine (P.sideGeodesic j)) :=
    range_geodesicLine_eq_of_mem hxy
      (((h : PSL(2, ℝ)) • P).side_subset_range_sideGeodesic i (hside ▸ hx))
      (((h : PSL(2, ℝ)) • P).side_subset_range_sideGeodesic i (hside ▸ hy))
      (P.side_subset_range_sideGeodesic j hx) (P.side_subset_range_sideGeodesic j hy)
  rcases exists_eq_mul_dilation_or_eq_mul_pslS_mul_dilation_of_range_eq hlines with
    ⟨s, hs⟩ | ⟨s, hs⟩
  · -- the same orientation puts `p` and `h • p` on the same side of their bisector
    exfalso
    have hx' := hj ▸ hx
    have hy' := hj ▸ hy
    rw [dirichletFace_eq_inter_range_geodesicLine hhp] at hx' hy'
    have hbis : range (geodesicLine (perpBisector p (h • p))) =
        range (geodesicLine (P.sideGeodesic j)) :=
      range_geodesicLine_eq_of_mem hxy hx'.2 hy'.2 (P.side_subset_range_sideGeodesic j hx)
        (P.side_subset_range_sideGeodesic j hy)
    have hpint : p ∈ interior P.carrier := by
      rw [hP, mem_interior_dirichletDomain_iff]
      intro g hg
      rw [dist_self]
      exact dist_pos.2 hg.symm
    have hleft : leftHalfPlane (P.sideGeodesic j) =
        (h : PSL(2, ℝ)) • leftHalfPlane (P.sideGeodesic i) := by
      rw [hs, leftHalfPlane_mul_dilation, sideGeodesic_def, sideGeodesic_def, vertex_smul,
        vertex_smul, leftHalfPlane_geodesicFromTo_smul _ (P.vertex_ne_vertex_add_one i)]
    refine notMem_leftHalfPlane_of_range_eq_perpBisector hhp.symm hbis
      ((P.mem_interior_carrier_iff p).1 hpint j) ?_
    rw [hleft]
    exact smul_mem_smul_set ((P.mem_interior_carrier_iff p).1 hpint i)
  · -- the reversed orientation identifies the endpoints
    have hfrom : IsGeodesicFromTo (P.sideGeodesic j) ((h : PSL(2, ℝ)) • P.vertex (i + 1))
        ((h : PSL(2, ℝ)) • P.vertex i) := by
      have hQ := (((h : PSL(2, ℝ)) • P).isGeodesicFromTo_sideGeodesic i)
      rw [vertex_smul, vertex_smul] at hQ
      rw [hs]
      exact (isGeodesicFromTo_mul_pslS_iff.2 hQ).mul_dilation s
    have hseg : extGeodesicSegment ((h : PSL(2, ℝ)) • P.vertex (i + 1))
        ((h : PSL(2, ℝ)) • P.vertex i) = extGeodesicSegment (P.vertex j) (P.vertex (j + 1)) := by
      rw [← side_def, ← hside, side_def, vertex_smul, vertex_smul, extGeodesicSegment_comm]
    exact ⟨hfrom.right_eq_of_extGeodesicSegment_eq (P.isGeodesicFromTo_sideGeodesic j) hseg,
      hfrom.left_eq_of_extGeodesicSegment_eq (P.isGeodesicFromTo_sideGeodesic j) hseg⟩

/-- **Sides of a Dirichlet polygon are paired along Dirichlet faces.** If the carrier of `P` is
the Dirichlet domain of a properly discontinuous `Γ`, centred at a point with trivial stabilizer,
and `σ` is a side pairing of `P` by elements of `Γ`, then side `i` is the Dirichlet face of the
inverse of the side-pairing map of `i`: the points of the domain equidistant from the centre and
its translate by that inverse. -/
theorem SidePairing.side_eq_dirichletFace (σ : P.SidePairing) (hmap : ∀ i, σ.map i ∈ Γ)
    (hP : P.carrier = dirichletDomain Γ p) (hp : p ∈ TauCeti.freeLocus Γ ℍ) (i : Fin n) :
    P.side i = dirichletFace p (⟨σ.map i, hmap i⟩ : Γ)⁻¹ := by
  set t : Γ := ⟨σ.map i, hmap i⟩
  have ht : t⁻¹ ≠ 1 := inv_ne_one.2 fun h ↦ σ.map_ne_one i (congrArg Subtype.val h)
  -- side `i` is carried by `σ.map i` into the domain, so it lies in the face of `t⁻¹`
  have hsub : P.side i ⊆ dirichletFace p t⁻¹ := fun x hx ↦ by
    have hxD : x ∈ dirichletDomain Γ p := hP ▸ P.side_subset_carrier i hx
    refine (inv_smul_mem_dirichletDomain_iff hxD t⁻¹).1 ?_
    rw [inv_inv, ← hP]
    exact P.side_subset_carrier _ (σ.map_smul_mem_side hx)
  obtain ⟨j, hj⟩ := exists_side_eq_dirichletFace_of_nontrivial hP
    (TauCeti.smul_ne_of_ne_one Γ ℍ hp ht) ((P.side_nontrivial i).mono hsub)
  rw [← hj, P.eq_of_nontrivial_side_inter_side (i := j) (j := i)
    (by rw [hj, inter_eq_right.2 hsub]; exact P.side_nontrivial i)]

/-- **The side pairing of a Dirichlet polygon.** Let `Γ ≤ PSL(2, ℝ)` act properly discontinuously
and let the carrier of a convex polygon `P`, possibly with ideal vertices, be the Dirichlet domain
of `Γ` centred at a point with trivial stabilizer. Then `P` has exactly one side pairing whose
maps lie in `Γ`: the element `g⁻¹` pairs the Dirichlet face of `g` with that of `g⁻¹`. -/
theorem existsUnique_sidePairing_of_carrier_eq_dirichletDomain
    (hP : P.carrier = dirichletDomain Γ p) (hp : p ∈ TauCeti.freeLocus Γ ℍ) :
    ∃! σ : P.SidePairing, ∀ i, σ.map i ∈ Γ := by
  -- each side is the face of a unique nontrivial element `g i`
  choose g hg using fun i ↦ (existsUnique_side_eq_dirichletFace hP hp i).exists
  have hg_inv (i : Fin n) : (g i)⁻¹ ≠ 1 := inv_ne_one.2 (hg i).1
  -- the face of `(g i)⁻¹` is a side `pair i`, whose element is `(g i)⁻¹`
  have hpair (i : Fin n) : ∃ j, P.side j = dirichletFace p (g i)⁻¹ := by
    refine exists_side_eq_dirichletFace_of_nontrivial hP
      (TauCeti.smul_ne_of_ne_one Γ ℍ hp (hg_inv i)) ?_
    have hinv := inv_smul_dirichletFace p (g i)
    rw [Set.subtype_smul_set] at hinv
    rw [← hinv, ← (hg i).2, ← side_smul]
    exact ((((g i)⁻¹ : Γ) : PSL(2, ℝ)) • P).side_nontrivial i
  choose pair hpair using hpair
  have hg_pair (i : Fin n) : g (pair i) = (g i)⁻¹ :=
    (existsUnique_side_eq_dirichletFace hP hp (pair i)).unique (hg (pair i))
      ⟨hg_inv i, hpair i⟩
  have hpair_pair (i : Fin n) : pair (pair i) = i :=
    P.side_injective (by rw [hpair, hg_pair, inv_inv, (hg i).2])
  have hvert (i : Fin n) :=
    smul_vertex_eq hP hp (hg_inv i) (by rw [inv_inv]; exact (hg i).2) (hpair i)
  let e : Equiv.Perm (Fin n) := Function.Involutive.toPerm pair hpair_pair
  have he (i : Fin n) : e i = pair i := congrFun (Function.Involutive.coe_toPerm _) i
  let σ : P.SidePairing :=
    { pair := e
      pair_pair := hpair_pair
      map := fun i ↦ ((g i)⁻¹ : Γ)
      map_pair := fun i ↦ by rw [he, hg_pair, inv_inv, Subgroup.coe_inv, inv_inv]
      map_smul_vertex := fun i ↦ (hvert i).1
      map_smul_vertex_add_one := fun i ↦ (hvert i).2 }
  refine ⟨σ, fun i ↦ ((g i)⁻¹ : Γ).2, fun τ hτ ↦ ?_⟩
  -- a side pairing by elements of `Γ` pairs each side along the face of the inverse map
  have hmap (i : Fin n) : τ.map i = σ.map i := by
    have hti := (existsUnique_side_eq_dirichletFace hP hp i).unique (hg i)
      ⟨inv_ne_one.2 fun h ↦ τ.map_ne_one i (congrArg Subtype.val h),
        τ.side_eq_dirichletFace hτ hP hp i⟩
    have hinv : (g i)⁻¹ = ⟨τ.map i, hτ i⟩ := by rw [hti, inv_inv]
    exact (congrArg Subtype.val hinv).symm
  have hpairτ (i : Fin n) : τ.pair i = σ.pair i :=
    P.side_injective (by rw [← τ.map_smul_side, ← σ.map_smul_side, hmap])
  exact SidePairing.ext (Equiv.ext hpairτ) (funext hmap)

/-- **Distinct translates of the interior of a Dirichlet polygon are disjoint.** If the carrier
of `P` is the Dirichlet domain of a properly discontinuous `Γ`, centred at a point with trivial
stabilizer, then every nonidentity element of `Γ` moves the interior of `P` off itself. -/
theorem disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain
    (hP : P.carrier = dirichletDomain Γ p) (hp : p ∈ TauCeti.freeLocus Γ ℍ) (γ : Γ)
    (hγ : γ ≠ 1) : Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier) := by
  rw [hP]
  exact disjoint_smul_interior_dirichletDomain (TauCeti.smul_ne_of_ne_one Γ ℍ hp hγ)

end TauCeti.UpperHalfPlane.ConvexPolygon

namespace Subgroup

open TauCeti TauCeti.UpperHalfPlane

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]

/-- **Dirichlet presentations of cocompact Fuchsian groups.** Let `Γ ≤ PSL(2, ℝ)` be discrete
with compact orbit space, and let `p ∈ ℍ` have trivial stabilizer. The Dirichlet domain of `Γ`
centred at `p` is a compact convex polygon `P` with a side pairing by elements of `Γ`, and `Γ` is
presented by the side-pairing maps, subject to the side relations and the vertex-cycle
relations. -/
theorem exists_sidePairing_relatorQuotientTo_bijective_of_compactSpace
    [CompactSpace (MulAction.orbitRel.Quotient Γ ℍ)] {p : ℍ} (hp : p ∈ freeLocus Γ ℍ) :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n) (σ : P.toConvexPolygon.SidePairing)
      (hmap : ∀ i, σ.map i ∈ Γ),
      P.carrier = dirichletDomain Γ p ∧ Function.Bijective (σ.relatorQuotientTo hmap) := by
  obtain ⟨n, _, P, hP, -⟩ := exists_compactConvexPolygon_carrier_eq_dirichletDomain_of_compactSpace
    Γ p
  have hP' : P.toConvexPolygon.carrier = dirichletDomain Γ p := by
    rw [CompactConvexPolygon.carrier_toConvexPolygon, hP]
  obtain ⟨σ, hσ, -⟩ := ConvexPolygon.existsUnique_sidePairing_of_carrier_eq_dirichletDomain hP' hp
  exact ⟨n, ‹NeZero n›, P, σ, hσ, hP, σ.relatorQuotientTo_bijective hσ
    (hP' ▸ locallyFinite_smul_dirichletDomain p)
    (ConvexPolygon.disjoint_smul_interior_carrier_of_carrier_eq_dirichletDomain hP' hp)⟩

end Subgroup
