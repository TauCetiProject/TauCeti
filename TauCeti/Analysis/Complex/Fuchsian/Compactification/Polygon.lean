/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Compactness
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Quotient
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Truncation
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.ParabolicCycle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Tessellation
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Compactifying a quotient with a cuspidal fundamental polygon

A finite-sided convex polygon whose ideal vertices are cusp points supplies compact
representatives for the complement of arbitrary cusp neighbourhoods, provided its carrier
meets every orbit. The cusp data defining those neighbourhoods need not use the polygon's
vertices as representatives, nor agree with the scalings chosen at those vertices.

If there are finitely many cusp orbits, these compact representatives imply compactness of
the cusp compactification. In particular, this applies to a cofinite group with such a polygon.
The polygon need only meet every orbit: neither uniqueness of representatives nor a
side pairing is needed for this compactness argument. Existence of a polygon for an arbitrary
cofinite group is not asserted here.

A side-paired polygon whose translates under a group `Γ` containing the side-pairing maps form a
locally finite family satisfies these hypotheses. Its translates cover `ℍ`, and each ideal vertex
is fixed by its cycle transformation, which is parabolic. Conversely, every cusp point of `Γ` is
`Γ`-equivalent to an ideal vertex, so `Γ` has finitely many cusp orbits and its compactified
quotient is compact. Disjointness of the translated interiors is not needed for any of this.

## Main results

* `ConvexPolygon.exists_cuspDatum_isCompact_carrier_diff_iUnion_horodisc`: a cuspidal polygon
  minus horodiscs at its ideal vertices is compact.
* `ConvexPolygon.exists_isCompact_cover_quotient_horodiscs`: compact representatives outside
  an arbitrary family of cusp horodiscs.
* `ConvexPolygon.compactSpace_compactifiedQuotient`: compactness with finitely many cusp orbits.
* `ConvexPolygon.isCompact_compl_iUnion_image_horodisc`: compactness of the truncated
  coarse quotient.
* `ConvexPolygon.SidePairing.isCuspPoint_of_vertex_eq_inr`: the ideal vertices of a locally
  finite side-paired polygon are cusp points.
* `ConvexPolygon.SidePairing.exists_vertex_eq_inr_smul_of_isCuspPoint`: every cusp point is
  equivalent to an ideal vertex.
* `ConvexPolygon.SidePairing.finite_cuspOrbit`,
  `ConvexPolygon.SidePairing.compactSpace_compactifiedQuotient`: finitely many cusp orbits, and
  a compact compactified quotient.

## References

Katok, *Fuchsian Groups*, §4.2; Beardon, *The Geometry of Discrete Groups*, Chapter 9;
Diamond–Shurman, *A First Course in Modular Forms*, §2.4.
The geometric input is `ConvexPolygon.isCompact_carrier_diff_iUnion`, and the topological
input is `Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations`.
-/

public section

open MulAction Set UpperHalfPlane
open TauCeti.Subgroup.CuspDatum
open scoped MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n) {Γ : Subgroup PSL(2, ℝ)}

section Discrete

variable [DiscreteTopology Γ]

/-- **Truncating a cuspidal polygon at its ideal vertices.** If every ideal vertex of a convex
polygon is a cusp point of `Γ`, then the ideal vertices carry cusp data based at them such that
the polygon minus horodiscs at these data, of arbitrary heights, is compact. -/
theorem exists_cuspDatum_isCompact_carrier_diff_iUnion_horodisc
    (hcusp : ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c) :
    ∃ E : {i : Fin n // (P.vertex i).isRight} → Γ.CuspDatum,
      (∀ i : {i : Fin n // (P.vertex i).isRight}, P.vertex i = .inr (E i).cusp) ∧
        ∀ B : {i : Fin n // (P.vertex i).isRight} → ℝ,
          IsCompact (P.carrier \ ⋃ i, horodisc (E i) (B i)) := by
  classical
  -- Choose data only at ideal vertices; finite vertices carry no auxiliary cusp data.
  have hex (i : {i : Fin n // (P.vertex i).isRight}) :
      ∃ E : Γ.CuspDatum, P.vertex i = .inr E.cusp := by
    obtain ⟨c, hc⟩ := Sum.isRight_iff.mp i.property
    obtain ⟨E, hE⟩ := (hcusp i c hc).exists_cuspDatum_cusp_eq
    exact ⟨E, by rw [hE]; exact hc⟩
  choose E hE using hex
  refine ⟨E, hE, fun B ↦ ?_⟩
  let g (i : Fin n) : PSL(2, ℝ) :=
    if hi : (P.vertex i).isRight then (E ⟨i, hi⟩).scaling else 1
  let B' (i : Fin n) : ℝ := if hi : (P.vertex i).isRight then B ⟨i, hi⟩ else 0
  have hg (i : Fin n) (c : OnePoint ℝ) (hi : P.vertex i = .inr c) : g i • c = ∞ := by
    have hright : (P.vertex i).isRight := by simp [hi]
    have heq : (E ⟨i, hright⟩).cusp = c := Sum.inr.inj ((hE ⟨i, hright⟩).symm.trans hi)
    simpa only [g, dite_eq_left hright, heq] using (E ⟨i, hright⟩).scaling_smul_cusp
  convert P.isCompact_carrier_diff_iUnion g hg B' using 2
  ext z
  simp only [mem_iUnion, mem_horodisc, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨i, hi⟩, hz⟩
    exact ⟨i, hi, by simpa only [g, B', dite_eq_left hi] using hz⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨⟨i, hi⟩, by simpa only [g, B', dite_eq_left hi] using hz⟩

/-- A convex polygon meeting every orbit and having only cuspidal ideal vertices gives a
compact set of representatives outside any prescribed family of cusp horodiscs. The family
may use arbitrary representatives and scalings, and its heights may be any real numbers. -/
theorem exists_isCompact_cover_quotient_horodiscs
    (hcover : ∀ q : orbitRel.Quotient Γ ℍ, q ∈ Quotient.mk (orbitRel Γ ℍ) '' P.carrier)
    (hcusp : ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c)
    (D : Γ.CuspOrbit → Γ.CuspDatum) (hD : ∀ C, (D C).cuspOrbit = C)
    (A : Γ.CuspOrbit → ℝ) :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ q : orbitRel.Quotient Γ ℍ,
      q ∈ Quotient.mk (orbitRel Γ ℍ) '' K ∨
        ∃ C : Γ.CuspOrbit, q ∈ Quotient.mk (orbitRel Γ ℍ) '' horodisc (D C) (A C) := by
  obtain ⟨E, -, hK⟩ := P.exists_cuspDatum_isCompact_carrier_diff_iUnion_horodisc hcusp
  -- Match each vertex datum to the prescribed datum of its orbit, rescaling heights.
  have hscale (i : {i : Fin n // (P.vertex i).isRight}) : ∃ a : ℝ, 0 < a ∧ ∀ B : ℝ,
      Quotient.mk (orbitRel Γ ℍ) '' horodisc (E i) (a * B) =
        Quotient.mk (orbitRel Γ ℍ) '' horodisc (D (E i).cuspOrbit) B :=
    exists_image_quotientMk_horodisc_eq _ _
      (((E i).cuspOrbit_eq_iff _).mp (hD (E i).cuspOrbit).symm)
  choose a _ hscale using hscale
  let H : Set ℍ := ⋃ i, horodisc (E i) (a i * A (E i).cuspOrbit)
  refine ⟨P.carrier \ H, hK _, fun q ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := hcover q
  by_cases hzH : z ∈ H
  · obtain ⟨i, hzi⟩ := mem_iUnion.mp hzH
    exact Or.inr ⟨(E i).cuspOrbit, hscale i _ ▸ mem_image_of_mem _ hzi⟩
  · exact Or.inl ⟨z, ⟨hz, hzH⟩, rfl⟩

/-- Removing the images of a family of cusp horodiscs from the coarse quotient leaves a
compact set when a cuspidal convex polygon meets every orbit. No finiteness assumption on
the cusp set is needed for this truncated quotient. -/
theorem isCompact_compl_iUnion_image_horodisc
    (hcover : ∀ q : orbitRel.Quotient Γ ℍ, q ∈ Quotient.mk (orbitRel Γ ℍ) '' P.carrier)
    (hcusp : ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c)
    (D : Γ.CuspOrbit → Γ.CuspDatum) (hD : ∀ C, (D C).cuspOrbit = C)
    (A : Γ.CuspOrbit → ℝ) :
    IsCompact ((⋃ C, Quotient.mk (orbitRel Γ ℍ) '' horodisc (D C) (A C))ᶜ) := by
  obtain ⟨K, hK, hcoverK⟩ := P.exists_isCompact_cover_quotient_horodiscs hcover hcusp D hD A
  refine (hK.image continuous_quotient_mk').of_isClosed_subset
    (isOpen_iUnion fun C ↦ isOpen_image_quotientMk_horodisc (D C) (A C)).isClosed_compl ?_
  intro q hq
  rcases hcoverK q with hqK | ⟨C, hqC⟩
  · exact hqK
  · exact False.elim (hq (mem_iUnion.mpr ⟨C, hqC⟩))

/-- A discrete group's cusp compactification is compact if it has finitely many cusp orbits and a
finite-sided convex polygon with cuspidal ideal vertices meets every upper-half-plane orbit. -/
theorem compactSpace_compactifiedQuotient [Finite Γ.CuspOrbit]
    (hcover : ∀ q : orbitRel.Quotient Γ ℍ, q ∈ Quotient.mk (orbitRel Γ ℍ) '' P.carrier)
    (hcusp : ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c) :
    CompactSpace Γ.CompactifiedQuotient := by
  apply Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations
    (fun C ↦ C.cuspDatum) (fun C ↦ C.cuspOrbit_cuspDatum)
  exact P.exists_isCompact_cover_quotient_horodiscs hcover hcusp
    (fun C ↦ C.cuspDatum) (fun C ↦ C.cuspOrbit_cuspDatum)

end Discrete

namespace SidePairing

variable {P} (σ : P.SidePairing)

/-- **Ideal vertices of a locally finite side-paired polygon are cusp points.** If a subgroup `Γ`
of `PSL(2, ℝ)` contains the cycle transformation at the ideal vertex `vertex j` and its translates
of `P` form a locally finite family, then `vertex j` is fixed by a parabolic element of `Γ`, namely
this cycle transformation. -/
theorem isCuspPoint_of_vertex_eq_inr {j : Fin n} {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ)
    (hcycle : σ.cycleMap j ∈ Γ) (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    Γ.IsCuspPoint ξ :=
  Subgroup.isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mpr
    ⟨⟨σ.cycleMap j, hcycle⟩, σ.cycleMap_smul_eq_self_of_vertex_eq_inr hj,
      σ.isParabolic_cycleMap_of_locallyFinite hj hcycle hlf⟩

/-- **Every cusp of a locally finite side-paired polygon is equivalent to an ideal vertex.** If a
subgroup `Γ` of `PSL(2, ℝ)` contains every side-pairing map and its translates of `P` form a
locally finite family, then every cusp point of `Γ` is carried to an ideal vertex of `P` by an
element of `Γ`. Disjointness of the translated interiors is not needed. -/
theorem exists_vertex_eq_inr_smul_of_isCuspPoint (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    {c : OnePoint ℝ} (hc : Γ.IsCuspPoint c) : ∃ γ : Γ, ∃ j, P.vertex j = .inr (γ • c) := by
  classical
  have : DiscreteTopology Γ := TauCeti.discreteTopology_of_locallyFinite_smul
    (P.nonempty_interior_carrier.mono interior_subset) hlf
  by_contra hne
  simp only [not_exists] at hne
  obtain ⟨D, rfl⟩ := hc.exists_cuspDatum_cusp_eq
  obtain ⟨E, hE, hK⟩ := P.exists_cuspDatum_isCompact_carrier_diff_iUnion_horodisc
    fun i ξ hi ↦ σ.isCuspPoint_of_vertex_eq_inr hi (σ.cycleMap_mem hmap _) hlf
  -- no cusp at an ideal vertex is equivalent to `D.cusp`, so their horodiscs stay apart
  have hdisj (i : {i : Fin n // (P.vertex i).isRight}) :
      Disjoint (Quotient.mk (orbitRel Γ ℍ) '' horodisc D D.width)
        (Quotient.mk (orbitRel Γ ℍ) '' horodisc (E i) (E i).width) := by
    refine (disjoint_image_quotientMk_horodisc_iff D (E i) D.width_pos.le le_rfl).mpr ?_
    rintro ⟨γ, hγ⟩
    exact hne γ i (by rw [hE, ← hγ])
  -- hence every orbit meeting the horodisc at `D` meets the truncated polygon `K`
  let K : Set ℍ := P.carrier \ ⋃ i, horodisc (E i) (E i).width
  have hsub : horodisc D D.width ⊆ Quotient.mk (orbitRel Γ ℍ) ⁻¹' (Quotient.mk _ '' K) := by
    intro z hz
    obtain ⟨γ, hγ⟩ := mem_iUnion.mp (σ.iUnion_smul_carrier_eq_univ hmap hlf ▸ mem_univ z)
    have hzw : Quotient.mk (orbitRel Γ ℍ) (γ⁻¹ • z) = Quotient.mk _ z :=
      Quotient.sound ⟨γ⁻¹, rfl⟩
    refine ⟨γ⁻¹ • z, ⟨mem_smul_set_iff_inv_smul_mem.mp hγ, fun hH ↦ ?_⟩, hzw⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hH
    exact (hdisj i).ne_of_mem ⟨z, hz, rfl⟩ ⟨_, hi, rfl⟩ hzw.symm
  -- the image of `K` is closed in the compactification, but its points accumulate at the cusp
  -- orbit of `D`
  have hclosed : IsClosed (Subgroup.CompactifiedQuotient.ofQuotient ''
      (Quotient.mk (orbitRel Γ ℍ) '' K)) :=
    (((hK _).image continuous_quotient_mk').image
      Subgroup.CompactifiedQuotient.continuous_ofQuotient).isClosed
  have : (Filter.comap (fun z : ℍ ↦ (D.scaling • z).im) Filter.atTop).NeBot := by
    refine Filter.comap_neBot fun t ht ↦ ?_
    obtain ⟨A, hA⟩ := Filter.mem_atTop_sets.mp ht
    obtain ⟨z, hz⟩ := nonempty_horodisc D A
    exact ⟨z, hA _ ((mem_horodisc D).mp hz).le⟩
  obtain ⟨p, -, hp⟩ := hclosed.mem_of_tendsto
    (Subgroup.CompactifiedQuotient.tendsto_ofQuotient_quotientMk_nhds_ofCusp D)
    ((Filter.tendsto_comap.eventually (Filter.eventually_gt_atTop D.width)).mono fun z hz ↦
      mem_image_of_mem _ (hsub ((mem_horodisc D).mpr hz)))
  cases hp

/-- **A locally finite side-paired polygon has finitely many cusp orbits.** If a subgroup `Γ` of
`PSL(2, ℝ)` contains every side-pairing map and its translates of `P` form a locally finite
family, then `Γ` has finitely many cusp orbits. -/
theorem finite_cuspOrbit (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) : Finite Γ.CuspOrbit := by
  have hex (C : Γ.CuspOrbit) : ∃ j : Fin n, ∃ γ : Γ, ∃ c : Γ.cuspPoints,
      Γ.cuspOrbitMk c = C ∧ P.vertex j = .inr (γ • (c : OnePoint ℝ)) := by
    obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
    obtain ⟨γ, j, hj⟩ := σ.exists_vertex_eq_inr_smul_of_isCuspPoint hmap hlf
      (Subgroup.mem_cuspPoints.mp c.property)
    exact ⟨j, γ, c, rfl, hj⟩
  choose j γ c hC hj using hex
  -- distinct cusp orbits contain distinct ideal vertices
  refine Finite.of_injective j fun C C' h ↦ ?_
  have h' : γ C • (c C : OnePoint ℝ) = γ C' • (c C' : OnePoint ℝ) :=
    Sum.inr.inj ((hj C).symm.trans (h ▸ hj C'))
  rw [← hC C, ← hC C', Subgroup.cuspOrbitMk_eq_iff, mem_orbit_iff]
  exact ⟨(γ C)⁻¹ * γ C', by rw [mul_smul, ← h', inv_smul_smul]⟩

/-- **A locally finite side-paired polygon gives a compact compactified quotient.** If a subgroup
`Γ` of `PSL(2, ℝ)` contains every side-pairing map and its translates of `P` form a locally finite
family, then the quotient `Γ \ ℍ` with its cusp orbits adjoined is compact. -/
theorem compactSpace_compactifiedQuotient [DiscreteTopology Γ] (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    CompactSpace Γ.CompactifiedQuotient := by
  have := σ.finite_cuspOrbit hmap hlf
  refine P.compactSpace_compactifiedQuotient (fun q ↦ ?_)
    (fun i c hi ↦ σ.isCuspPoint_of_vertex_eq_inr hi (σ.cycleMap_mem hmap _) hlf)
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
  obtain ⟨γ, hγ⟩ := mem_iUnion.mp (σ.iUnion_smul_carrier_eq_univ hmap hlf ▸ mem_univ z)
  exact ⟨γ⁻¹ • z, mem_smul_set_iff_inv_smul_mem.mp hγ, Quotient.sound ⟨γ⁻¹, rfl⟩⟩

end SidePairing

end TauCeti.UpperHalfPlane.ConvexPolygon
