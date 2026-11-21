/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Finite
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.DualGraph.Basic

/-!
# Finitely many combinatorial types of stable maps

For a fixed finite marking set, arithmetic genus `g` and bound `d` on the total degree there are
only finitely many stable degree-decorated dual graphs up to isomorphism. This is the discrete
finiteness behind Gromov compactness: a sequence of stable maps of bounded energy has a
subsequence of constant combinatorial type.

In the symplectic setting the degree is not measured by an ample polarization. One decorates
instead by `1` on the components on which the map is nonconstant and `0` on the contracted ones.
By `TauCeti.DualGraph.DegreeDecoration.isStable_congr` only the set of contracted components
matters for stability, and the total degree of that decoration is the number `a` of nonconstant
components. An energy threshold `ε > 0` for nonconstant components bounds `a` by the energy
divided by `ε`, so the theorem below with `d` that bound applies.

The vertex and edge bounds come from
`TauCeti.DualGraph.DegreeDecoration.IsStable.card_vertex_le` and
`TauCeti.DualGraph.DegreeDecoration.IsStable.card_edge_le`, and the underlying graphs are
enumerated by `TauCeti.DualGraph.exists_finset_representatives_of_bounds`. Every component degree
is at most the total degree, so the decorations of each representative are drawn from a finite
set.

## Main results

* `TauCeti.DualGraph.DegreeDecoration.exists_finset_stable_representatives`: finitely many stable
  decorated graphs of genus `g` and total degree at most `d` represent every such decorated graph
  up to a degree-preserving isomorphism.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, Proc. Sympos.
  Pure Math. 62 (1997), Part 2, 45--96, Section 1, on degree-decorated graphs of stable maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Chapter 5, on stable maps and the number of their components.
-/

public noncomputable section

namespace TauCeti.DualGraph.DegreeDecoration

open Finset

universe u v

variable {ι : Type v}

/-- For fixed arithmetic genus `g`, bound `d` on the total degree, and finite marking set,
finitely many stable decorated graphs represent all stable decorated graphs of genus `g` and total
degree at most `d`, up to a label-preserving isomorphism of graphs carrying one decoration to the
other. Every representative is itself stable, of genus `g` and of total degree at most `d`. The
input graphs may have vertex and edge types in an arbitrary universe. -/
theorem exists_finset_stable_representatives [Fintype ι] (g d : ℕ) :
    ∃ S : Finset (Σ H : DualGraph.{0} ι, H.DegreeDecoration),
      (∀ x ∈ S, x.2.IsStable ∧ x.1.arithmeticGenus = g ∧ x.2.totalDegree ≤ d) ∧
      ∀ (G : DualGraph.{u} ι) (D : G.DegreeDecoration), D.IsStable → G.arithmeticGenus = g →
        D.totalDegree ≤ d → ∃ x ∈ S, ∃ f : G.Iso x.1,
          ∀ v, x.2.componentDegree (f.vertexEquiv v) = D.componentDegree v := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_representatives_of_bounds (ι := ι)
    (2 * g + Fintype.card ι + 3 * d - 2) (3 * g + Fintype.card ι + 3 * d - 3) g
  -- On each representative graph, the decorations with all component degrees at most `d`.
  let decorations (H : DualGraph.{0} ι) : Finset (Σ H : DualGraph.{0} ι, H.DegreeDecoration) :=
    univ.image fun c : H.Vertex → Fin (d + 1) ↦ ⟨H, ⟨fun w ↦ c w⟩⟩
  refine ⟨(T.biUnion decorations).filter
      (fun x ↦ x.2.IsStable ∧ x.1.arithmeticGenus = g ∧ x.2.totalDegree ≤ d),
    fun x hx ↦ (mem_filter.mp hx).2, fun G D hD hgenus hdeg ↦ ?_⟩
  have ha := D.card_filter_componentDegree_ne_zero_le_totalDegree
  have hV := hD.card_vertex_le
  have hE := hD.card_edge_le
  rw [hgenus] at hV hE
  obtain ⟨H, hH, ⟨f⟩⟩ := hT G (by omega) (by omega) fun x ↦ by
    rw [← hgenus]
    exact G.genus_le_arithmeticGenus x
  -- The decoration `D` transported to `H` along `f`.
  let D' : H.DegreeDecoration := ⟨fun w ↦ D.componentDegree (f.vertexEquiv.symm w)⟩
  have hD' : ∀ v, D'.componentDegree (f.vertexEquiv v) = D.componentDegree v := fun v ↦ by
    simp [D']
  have htotal : D'.totalDegree = D.totalDegree := by
    rw [totalDegree_def, totalDegree_def, ← f.vertexEquiv.sum_comp]
    exact sum_congr rfl fun v _ ↦ hD' v
  have hle : ∀ w, D'.componentDegree w ≤ d := fun w ↦ by
    have := single_le_sum (fun v _ ↦ Nat.zero_le (D'.componentDegree v)) (mem_univ w)
    rw [← totalDegree_def, htotal] at this
    exact this.trans hdeg
  refine ⟨⟨H, D'⟩, mem_filter.mpr ⟨mem_biUnion.mpr ⟨H, hH, ?_⟩, ?_, ?_, ?_⟩, f, hD'⟩
  · exact mem_image.mpr ⟨fun w ↦ ⟨D'.componentDegree w, Nat.lt_succ_of_le (hle w)⟩,
      mem_univ _, rfl⟩
  · refine (isStable_iff D').mpr fun w hw ↦ ?_
    rw [← f.vertexEquiv.apply_symm_apply w, f.logCanonicalDegree_vertexEquiv]
    exact (isStable_iff D).mp hD _ hw
  · exact f.arithmeticGenus_eq.symm.trans hgenus
  · exact htotal.trans_le hdeg

end TauCeti.DualGraph.DegreeDecoration
