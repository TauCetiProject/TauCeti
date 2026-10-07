/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Compactness
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Quotient
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Truncation

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

## Main results

* `ConvexPolygon.exists_isCompact_cover_quotient_horodiscs`: compact representatives outside
  an arbitrary family of cusp horodiscs.
* `ConvexPolygon.compactSpace_compactifiedQuotient`: compactness with finitely many cusp orbits.
* `ConvexPolygon.isCompact_compl_iUnion_image_horodisc`: compactness of the truncated
  coarse quotient.

## References

Katok, *Fuchsian Groups*, §4.2; Diamond–Shurman, *A First Course in Modular Forms*, §2.4.
The geometric input is `ConvexPolygon.isCompact_carrier_diff_iUnion`, and the topological
input is `Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations`.
-/

public section

open MulAction Set UpperHalfPlane
open TauCeti.Subgroup.CuspDatum
open scoped MatrixGroups OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)
variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]

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
  classical
  -- Choose data only at ideal vertices; finite vertices carry no auxiliary cusp data.
  let I := {i : Fin n // (P.vertex i).isRight}
  have hex (i : I) : ∃ E : Γ.CuspDatum, P.vertex i = .inr E.cusp := by
    obtain ⟨c, hc⟩ := Sum.isRight_iff.mp i.property
    obtain ⟨E, hE⟩ := (hcusp i c hc).exists_cuspDatum_cusp_eq
    exact ⟨E, by rw [hE]; exact hc⟩
  choose E hE using hex
  -- Match each vertex datum to the prescribed datum of its orbit, rescaling heights.
  have hscale (i : I) : ∃ a : ℝ, 0 < a ∧ ∀ B : ℝ,
      Quotient.mk (orbitRel Γ ℍ) '' horodisc (E i) (a * B) =
        Quotient.mk (orbitRel Γ ℍ) '' horodisc (D (E i).cuspOrbit) B := by
    exact exists_image_quotientMk_horodisc_eq _ _
      (((E i).cuspOrbit_eq_iff _).mp (hD (E i).cuspOrbit).symm)
  choose a _ hscale using hscale
  let g (i : Fin n) : PSL(2, ℝ) :=
    if hi : (P.vertex i).isRight then (E ⟨i, hi⟩).scaling else 1
  let B (i : Fin n) : ℝ :=
    if hi : (P.vertex i).isRight then a ⟨i, hi⟩ * A (E ⟨i, hi⟩).cuspOrbit else 0
  have hg (i : Fin n) (c : OnePoint ℝ) (hi : P.vertex i = .inr c) : g i • c = ∞ := by
    have hright : (P.vertex i).isRight := by simp [hi]
    have heq : (E ⟨i, hright⟩).cusp = c := Sum.inr.inj ((hE ⟨i, hright⟩).symm.trans hi)
    simpa only [g, dite_eq_left hright, heq] using (E ⟨i, hright⟩).scaling_smul_cusp
  let H : Set ℍ := ⋃ i, ⋃ (_ : (P.vertex i).isRight), {z : ℍ | B i < (g i • z).im}
  refine ⟨P.carrier \ H, P.isCompact_carrier_diff_iUnion g hg B, fun q ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := hcover q
  by_cases hzH : z ∈ H
  · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzH
    have hhor : z ∈ horodisc (E ⟨i, hi⟩) (a ⟨i, hi⟩ * A (E ⟨i, hi⟩).cuspOrbit) := by
      simpa only [mem_horodisc, B, g, dite_eq_left hi, mem_ofPred_eq] using hzi
    refine Or.inr ⟨(E ⟨i, hi⟩).cuspOrbit, ?_⟩
    rw [← hscale ⟨i, hi⟩]
    exact mem_image_of_mem _ hhor
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

end TauCeti.UpperHalfPlane.ConvexPolygon
