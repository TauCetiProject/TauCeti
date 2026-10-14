/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Tessellation
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
import TauCeti.GroupTheory.GroupAction.Stabilizer

/-!
# Elliptic points on the sides of a fundamental polygon

For a side-paired convex hyperbolic polygon with disjoint translated interiors, an interior
point has trivial stabilizer. At a side point other than its finite endpoints, only the two
adjacent tiles can occur. Its stabilizer is therefore trivial unless the side is self-paired
and the pairing map fixes that point; in that case it is cyclic of order two.

If the translates cover the upper half-plane, every elliptic orbit has a representative at a finite
vertex or at such a fixed point of a self-paired side. This supplies the side-point case needed
in addition to vertex cycles when extracting elliptic orbits from a fundamental polygon. No
claim that all elliptic points are represented by vertices is made.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapter 3.
-/

public section

open MulAction Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} {Γ : Subgroup PSL(2, ℝ)}

namespace SidePairing

variable (σ : P.SidePairing)

/-- A transformation carrying a point of the polygon to a nonendpoint point of side `i` is
one of the two adjacent tile transformations: the identity or the map of the paired side. -/
theorem eq_one_or_eq_map_pair_of_smul_mem_side {i : Fin n}
    (hmap : σ.map (σ.pair i) ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {g : PSL(2, ℝ)} (hg : g ∈ Γ) {z w : ℍ} (hz : z ∈ P.carrier)
    (hw : w ∈ P.side i) (hwp : P.vertex i ≠ .inl w)
    (hwq : P.vertex (i + 1) ≠ .inl w) (hgz : g • z = w) :
    g = 1 ∨ g = σ.map (σ.pair i) := by
  have hcover : w ∈ interior (P.carrier ∪ σ.map (σ.pair i) • P.carrier) := by
    exact σ.mem_interior_union_smul_carrier_of_mem_side (σ.pair i)
      (by simpa using hw) (by simpa using hwp) (by simpa using hwq)
  have hwcl : w ∈ closure (g • interior P.carrier) := by
    rw [closure_smul, P.closure_interior_carrier, ← hgz]
    exact smul_mem_smul_set hz
  obtain ⟨v, hv, hvg⟩ := mem_closure_iff.mp hwcl _ isOpen_interior hcover
  rcases interior_subset hv with hvP | hvP
  · exact Or.inl (P.eq_of_smul_interior_inter_smul_carrier_nonempty hdisj hg Γ.one_mem
      ⟨v, hvg, by simpa using hvP⟩)
  · exact Or.inr (P.eq_of_smul_interior_inter_smul_carrier_nonempty hdisj hg
      hmap ⟨v, hvg, hvP⟩)

/-- If a side-pairing map fixes a nonendpoint point of its side, that side is self-paired. -/
theorem pair_eq_self_of_map_smul_eq_self {i : Fin n} {z : ℍ} (hz : z ∈ P.side i)
    (hzp : P.vertex i ≠ .inl z) (hzq : P.vertex (i + 1) ≠ .inl z)
    (hfix : σ.map i • z = z) : σ.pair i = i := by
  have hzpair : z ∈ P.side (σ.pair i) := by
    rw [← σ.map_smul_side, ← hfix]
    exact smul_mem_smul_set hz
  by_contra hne
  exact disjoint_left.mp (disjoint_leftHalfPlane_range_geodesicLine _)
    (P.mem_leftHalfPlane_of_mem_side hz hzp hzq hne)
    (P.side_subset_range_sideGeodesic _ hzpair)

/-- At a nonendpoint side point, an element of the acting group fixes the point exactly when
it is the identity or the side-pairing map fixing that point. -/
theorem smul_eq_self_iff_of_mem_side {i : Fin n}
    (hmap : σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {z : ℍ} (hz : z ∈ P.side i)
    (hzp : P.vertex i ≠ .inl z) (hzq : P.vertex (i + 1) ≠ .inl z)
    {g : PSL(2, ℝ)} (hg : g ∈ Γ) :
    g • z = z ↔ g = 1 ∨ g = σ.map i ∧ σ.map i • z = z := by
  refine ⟨fun hfix ↦ ?_, fun h ↦ ?_⟩
  · rcases σ.eq_one_or_eq_map_pair_of_smul_mem_side
      (by simpa only [σ.map_pair] using Γ.inv_mem hmap) hdisj hg
      (P.side_subset_carrier i hz) hz hzp hzq hfix with h | h
    · exact Or.inl h
    · have hfix' : σ.map i • z = z := by
        rw [h, σ.map_pair, inv_smul_eq_iff] at hfix
        exact hfix.symm
      rw [σ.pair_eq_self_of_map_smul_eq_self hz hzp hzq hfix'] at h
      exact Or.inr ⟨h, hfix'⟩
  · rcases h with rfl | ⟨rfl, hfix⟩
    · exact one_smul _ _
    · exact hfix

/-- A self-paired side has a nonidentity pairing map of order two. -/
theorem orderOf_map_of_pair_eq_self {i : Fin n} (hi : σ.pair i = i) :
    orderOf (σ.map i) = 2 := by
  have hinv : σ.map i = (σ.map i)⁻¹ := by simpa only [hi] using σ.map_pair i
  exact orderOf_eq_prime (by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hinv)
    (σ.map_ne_one i)

/-- Every self-paired side has exactly one fixed point of its pairing map. It lies on the
side away from the finite endpoints. This includes sides with two ideal endpoints. -/
theorem existsUnique_mem_side_map_smul_eq_self_of_pair_eq_self {i : Fin n}
    (hi : σ.pair i = i) :
    ∃! z : ℍ, z ∈ P.side i ∧ P.vertex i ≠ .inl z ∧ P.vertex (i + 1) ≠ .inl z ∧
      σ.map i • z = z := by
  -- In a side parameter the endpoint-reversing map is `t ↦ -(s + t)`.
  have hg := (P.isGeodesicFromTo_sideGeodesic i).smul (σ.map i)
  rw [σ.map_smul_vertex, σ.map_smul_vertex_add_one, hi] at hg
  obtain ⟨s, hs⟩ := (isGeodesicFromTo_mul_pslS_iff.mpr
    (P.isGeodesicFromTo_sideGeodesic i)).exists_eq_mul_dilation hg
  have hact (t : ℝ) : σ.map i • geodesicLine (P.sideGeodesic i) t =
      geodesicLine (P.sideGeodesic i) (-(s + t)) := by
    rw [smul_geodesicLine, hs, geodesicLine_mul_dilation, geodesicLine_mul_pslS]
  let z := geodesicLine (P.sideGeodesic i) (-s / 2)
  have hfix : σ.map i • z = z := by
    rw [hact]
    congr 1
    ring
  -- The fixed parameter is the midpoint of a side point and its image, so remains on the side.
  obtain ⟨v, hv, -, -⟩ := P.exists_mem_side_ne_endpoints i
  obtain ⟨t, rfl⟩ := P.side_subset_range_sideGeodesic i hv
  have hv' : geodesicLine (P.sideGeodesic i) (-(s + t)) ∈ P.side i := by
    have h := smul_mem_smul_set (a := σ.map i) hv
    rwa [σ.map_smul_side, hi, hact] at h
  have hzseg : z ∈ geodesicSegment (geodesicLine (P.sideGeodesic i) t)
      (geodesicLine (P.sideGeodesic i) (-(s + t))) := by
    rw [geodesicSegment_geodesicLine]
    refine mem_image_of_mem _ ?_
    constructor <;>
      linarith [min_le_left t (-(s + t)), min_le_right t (-(s + t)),
        le_max_left t (-(s + t)), le_max_right t (-(s + t))]
  have hz : z ∈ P.side i := by
    rw [← P.carrier_inter_range_sideGeodesic]
    exact ⟨P.geodesicSegment_subset_carrier
      (P.side_subset_carrier i hv) (P.side_subset_carrier i hv') hzseg, mem_range_self _⟩
  have hzp : P.vertex i ≠ .inl z := by
    intro hp
    apply P.vertex_ne_vertex_add_one i
    have h := σ.map_smul_vertex i
    rw [hi, hp, Sum.smul_inl, hfix] at h
    exact hp.trans h
  have hzq : P.vertex (i + 1) ≠ .inl z := by
    intro hq
    apply P.vertex_ne_vertex_add_one i
    have h := σ.map_smul_vertex_add_one i
    rw [hi, hq, Sum.smul_inl, hfix] at h
    exact h.symm.trans hq.symm
  refine ⟨z, ⟨hz, hzp, hzq, hfix⟩, fun w hw ↦ ?_⟩
  by_contra hwz
  exact σ.map_ne_one i
    (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self
      hw.2.2.2 hfix (Ne.symm hwz))

/-- The unique fixed point of the involution pairing a side with itself. It is an interior
point of that side even when both endpoints are ideal. -/
noncomputable def selfPairedSideFixedPoint (i : {i : Fin n // σ.pair i = i}) : ℍ :=
  Classical.choose (σ.existsUnique_mem_side_map_smul_eq_self_of_pair_eq_self i.2)

/-- The fixed point of a self-paired side lies on the side, avoids its endpoints, and is
fixed by the pairing map. -/
theorem selfPairedSideFixedPoint_spec (i : {i : Fin n // σ.pair i = i}) :
    σ.selfPairedSideFixedPoint i ∈ P.side i ∧
      P.vertex i ≠ .inl (σ.selfPairedSideFixedPoint i) ∧
      P.vertex (i + 1) ≠ .inl (σ.selfPairedSideFixedPoint i) ∧
      σ.map i • σ.selfPairedSideFixedPoint i = σ.selfPairedSideFixedPoint i := by
  exact (Classical.choose_spec
    (σ.existsUnique_mem_side_map_smul_eq_self_of_pair_eq_self i.2)).1

/-- The self-pairing involution fixes its distinguished side point. -/
@[simp]
theorem map_smul_selfPairedSideFixedPoint (i : {i : Fin n // σ.pair i = i}) :
    σ.map i • σ.selfPairedSideFixedPoint i = σ.selfPairedSideFixedPoint i :=
  (σ.selfPairedSideFixedPoint_spec i).2.2.2

/-- Any fixed point of a self-pairing map is its distinguished side fixed point. -/
theorem selfPairedSideFixedPoint_eq (i : {i : Fin n // σ.pair i = i}) {z : ℍ}
    (hfix : σ.map i • z = z) :
    σ.selfPairedSideFixedPoint i = z := by
  by_contra hne
  exact σ.map_ne_one i
    (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smul_eq_self
      hfix (σ.map_smul_selfPairedSideFixedPoint i) hne)

/-- The stabilizer of a nonendpoint side point is trivial exactly when the side-pairing map
does not fix it. -/
theorem stabilizer_eq_bot_iff_of_mem_side {i : Fin n}
    (hmap : σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {z : ℍ} (hz : z ∈ P.side i)
    (hzp : P.vertex i ≠ .inl z) (hzq : P.vertex (i + 1) ≠ .inl z) :
    stabilizer Γ z = ⊥ ↔ σ.map i • z ≠ z := by
  refine ⟨fun h hfix ↦ ?_, fun h ↦ ?_⟩
  · have hg : (⟨σ.map i, hmap⟩ : Γ) ∈ stabilizer Γ z := mem_stabilizer_iff.mpr hfix
    rw [h, Subgroup.mem_bot] at hg
    exact σ.map_ne_one i (congrArg Subtype.val hg)
  · apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    have hfix := (σ.smul_eq_self_iff_of_mem_side hmap hdisj hz hzp hzq g.2).mp
      (mem_stabilizer_iff.mp hg)
    exact Subtype.ext (hfix.resolve_right fun hc ↦ h hc.2)

/-- The nontrivial stabilizer of a nonendpoint side point, viewed in `PSL(2, ℝ)`, is generated
by its side-pairing involution. -/
theorem map_stabilizer_eq_zpowers_map_of_mem_side {i : Fin n}
    (hmap : σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {z : ℍ} (hz : z ∈ P.side i)
    (hzp : P.vertex i ≠ .inl z) (hzq : P.vertex (i + 1) ≠ .inl z)
    (hfix : σ.map i • z = z) :
    (stabilizer Γ z).map Γ.subtype = Subgroup.zpowers (σ.map i) := by
  apply le_antisymm
  · rintro g ⟨γ, hγ, rfl⟩
    rcases (σ.smul_eq_self_iff_of_mem_side hmap hdisj hz hzp hzq γ.2).mp
        (mem_stabilizer_iff.mp hγ) with h | ⟨h, -⟩
    · simpa only [Subgroup.coe_subtype, h] using (Subgroup.zpowers (σ.map i)).one_mem
    · simpa only [Subgroup.coe_subtype, h] using Subgroup.mem_zpowers (σ.map i)
  · apply Subgroup.zpowers_le.mpr
    exact ⟨⟨σ.map i, hmap⟩, mem_stabilizer_iff.mpr hfix, rfl⟩

/-- A nonendpoint side point fixed by its side-pairing map has stabilizer order two. -/
theorem natCard_stabilizer_eq_two_of_mem_side {i : Fin n}
    (hmap : σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {z : ℍ} (hz : z ∈ P.side i)
    (hzp : P.vertex i ≠ .inl z) (hzq : P.vertex (i + 1) ≠ .inl z)
    (hfix : σ.map i • z = z) : Nat.card (stabilizer Γ z) = 2 := by
  rw [← Subgroup.card_map_of_injective Γ.subtype_injective,
    σ.map_stabilizer_eq_zpowers_map_of_mem_side hmap hdisj hz hzp hzq hfix, Nat.card_zpowers]
  exact σ.orderOf_map_of_pair_eq_self (σ.pair_eq_self_of_map_smul_eq_self hz hzp hzq hfix)

/-- A nonendpoint fixed point of a self-paired side is the only point of the polygon in its
group orbit. Thus it cannot be identified with a vertex or a fixed point of another side. -/
theorem mem_orbit_iff_eq_of_mem_side_map_smul_eq_self {i : Fin n}
    (hmap : σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {z w : ℍ} (hz : z ∈ P.carrier) (hw : w ∈ P.side i)
    (hwp : P.vertex i ≠ .inl w) (hwq : P.vertex (i + 1) ≠ .inl w)
    (hfix : σ.map i • w = w) : w ∈ orbit Γ z ↔ z = w := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ mem_orbit_self _⟩
  obtain ⟨g, hgz⟩ := mem_orbit_iff.mp h
  rcases σ.eq_one_or_eq_map_pair_of_smul_mem_side
    (by simpa only [σ.map_pair] using Γ.inv_mem hmap) hdisj g.2 hz hw hwp hwq hgz with hg | hg
  · simpa only [Subgroup.smul_def, hg, one_smul] using hgz
  · have hgw : g • w = w := by
      rw [Subgroup.smul_def, hg, σ.map_pair, inv_smul_eq_iff]
      exact hfix.symm
    exact (MulAction.injective g) (hgz.trans hgw.symm)

/-- In a fundamental polygon whose translates cover the upper half-plane, every point with
nontrivial stabilizer is represented either by a finite vertex or by a nonendpoint fixed point
of a self-paired side.
In the latter case its representative has stabilizer order two. -/
theorem exists_vertex_or_self_paired_side_of_stabilizer_ne_bot
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hcover : ⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier = univ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    {z : ℍ} (hz : stabilizer Γ z ≠ ⊥) :
    ∃ w ∈ orbit Γ z,
      (∃ i, P.vertex i = .inl w) ∨
        ∃ i, w ∈ P.side i ∧ P.vertex i ≠ .inl w ∧ P.vertex (i + 1) ≠ .inl w ∧
          σ.pair i = i ∧ σ.map i • w = w ∧ Nat.card (stabilizer Γ w) = 2 := by
  obtain ⟨γ, hγ⟩ := mem_iUnion.mp (hcover ▸ mem_univ z)
  obtain ⟨w, hw, hwz⟩ := mem_smul_set.mp hγ
  rw [← Subgroup.smul_def γ] at hwz
  have hworb : w ∈ orbit Γ z := mem_orbit_iff.mpr ⟨γ⁻¹, by rw [← hwz, inv_smul_smul]⟩
  have hwne : stabilizer Γ w ≠ ⊥ := by
    intro h
    apply hz
    rw [← hwz, stabilizer_smul_eq_stabilizer_map_conj, h, Subgroup.map_bot]
  refine ⟨w, hworb, ?_⟩
  by_cases hv : ∃ i, P.vertex i = .inl w
  · exact Or.inl hv
  · have hwi : w ∉ interior P.carrier := fun h ↦
      hwne (stabilizer_eq_bot_of_disjoint_smul hdisj h)
    have hwf : w ∈ frontier P.carrier := ⟨subset_closure hw, hwi⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (P.frontier_carrier ▸ hwf)
    have hv' : ∀ i, P.vertex i ≠ .inl w := not_exists.mp hv
    have hfix : σ.map i • w = w := not_not.mp fun h ↦
      hwne ((σ.stabilizer_eq_bot_iff_of_mem_side (hmap i) hdisj hi (hv' i) (hv' (i + 1))).mpr h)
    exact Or.inr ⟨i, hi, hv' i, hv' (i + 1),
      σ.pair_eq_self_of_map_smul_eq_self hi (hv' i) (hv' (i + 1)) hfix, hfix,
      σ.natCard_stabilizer_eq_two_of_mem_side (hmap i) hdisj hi (hv' i) (hv' (i + 1)) hfix⟩

end SidePairing

end TauCeti.UpperHalfPlane.ConvexPolygon
