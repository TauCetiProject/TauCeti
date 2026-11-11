/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Basic
public import TauCeti.Combinatorics.Graph.Serre.Cycle.Forest

/-!
# Independence of forest incidence columns

The signed incidence boundary of a loopless, parallel-free, acyclic dart set is injective
over any ring. In particular a cycle supported on a spanning forest vanishes, and two cycles
are equal if their coordinates agree off the forest. These are the independence and uniqueness
statements for fundamental cycle bases, simultaneously for integral and binary coefficients.

No finiteness or connectedness assumption is needed: chains are finitely supported even when
the graph is infinite. To detect the coefficient of a forest edge, delete that edge and pair
the boundary with the indicator of the component containing its source.

## References

* R. Diestel, *Graph Theory*, §1.9 (fundamental cycle bases).
* A. Hatcher, *Algebraic Topology*, §2.2 (signed incidence boundaries).
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {O F : Set Γ.E} {R : Type*} [Ring R]

/-- The signed incidence columns of a loopless, parallel-free forest are independent:
its boundary map is injective, over any ring and without finiteness assumptions. -/
theorem incidenceBoundary_injective_of_isAcyclic
    (hloop : ∀ e ∈ F, Γ.src e ≠ Γ.tgt e)
    (hinj : Set.InjOn (fun e => s(Γ.src e, Γ.tgt e)) F)
    (hacyc : (Γ.supportGraph F).IsAcyclic) :
    Function.Injective (Γ.incidenceBoundary F R) := by
  classical
  apply (injective_iff_map_eq_zero (Γ.incidenceBoundary F R)).mpr
  intro c hc
  ext e
  let H := Γ.supportGraph F
  let D := H.deleteEdges {s(Γ.src e.val, Γ.tgt e.val)}
  have hadj : H.Adj (Γ.src e.val) (Γ.tgt e.val) :=
    (Γ.supportGraph_adj F _ _).mpr ⟨hloop e.val e.property,
      Or.inl ⟨e.val, e.property, rfl, rfl⟩⟩
  have hsep : ¬D.Reachable (Γ.src e.val) (Γ.tgt e.val) :=
    SimpleGraph.isBridge_iff.mp
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hacyc hadj)
  let p : Γ.V → R := fun x => if D.Reachable (Γ.src e.val) x then 1 else 0
  let cut : (Γ.V →₀ R) →ₗ[R] R := Finsupp.linearCombination R p
  have hcol (f : F) : p (Γ.tgt f.val) - p (Γ.src f.val) =
      if f = e then -1 else 0 := by
    by_cases hfe : f = e
    · subst f
      simp [p, hsep]
    · have hends : s(Γ.src f.val, Γ.tgt f.val) ≠
          s(Γ.src e.val, Γ.tgt e.val) := by
        intro h
        exact hfe (Subtype.ext (hinj f.property e.property h))
      have hfadj : D.Adj (Γ.src f.val) (Γ.tgt f.val) :=
        SimpleGraph.deleteEdges_adj.mpr
          ⟨(Γ.supportGraph_adj F _ _).mpr ⟨hloop f.val f.property,
            Or.inl ⟨f.val, f.property, rfl, rfl⟩⟩, by simpa using hends⟩
      have hreach : D.Reachable (Γ.src e.val) (Γ.tgt f.val) ↔
          D.Reachable (Γ.src e.val) (Γ.src f.val) :=
        ⟨fun h => h.trans hfadj.symm.reachable, fun h => h.trans hfadj.reachable⟩
      simp [p, hreach, hfe]
  have hcut : cut.comp (Γ.incidenceBoundary F R) = -(Finsupp.lapply e) := by
    apply Finsupp.lhom_ext
    intro f r
    simp only [LinearMap.comp_apply, incidenceBoundary_single, map_smul, map_sub,
      cut, Finsupp.linearCombination_single, smul_eq_mul, one_mul, LinearMap.neg_apply,
      Finsupp.lapply_apply]
    rw [hcol]
    by_cases h : f = e <;> simp [h]
  have he := congrArg (fun l : (F →₀ R) →ₗ[R] R => l c) hcut
  simpa [hc] using he.symm

/-- A cycle supported on forest edges vanishes. The cycle can be written in the larger
ambient dart coordinates; only its support is required to lie in the forest. -/
theorem IsSpanningForest.eq_zero_of_incidenceBoundary_eq_zero
    (hF : Γ.IsSpanningForest O F) (c : O →₀ R)
    (hc : Γ.incidenceBoundary O R c = 0) (hs : ∀ e ∈ c.support, e.val ∈ F) :
    c = 0 :=
  SerreGraph.eq_zero_of_incidenceBoundary_eq_zero hF.subset
    (incidenceBoundary_injective_of_isAcyclic hF.src_ne_tgt hF.endpoints_injOn hF.isAcyclic)
    c hc hs

/-- Two chains with equal boundaries and equal chord coordinates are equal. Thus on every
fibre of the boundary map, the non-forest coordinates determine a chain uniquely. -/
theorem IsSpanningForest.eq_of_incidenceBoundary_eq_of_forall_notMem
    (hF : Γ.IsSpanningForest O F) (c d : O →₀ R)
    (hboundary : Γ.incidenceBoundary O R c = Γ.incidenceBoundary O R d)
    (hchord : ∀ e : O, e.val ∉ F → c e = d e) : c = d :=
  SerreGraph.eq_of_incidenceBoundary_eq_of_forall_notMem hF.subset
    (incidenceBoundary_injective_of_isAcyclic hF.src_ne_tgt hF.endpoints_injOn hF.isAcyclic)
    c d hboundary hchord

/-- Integral cycles are determined by their coordinates off a spanning forest. -/
theorem IsSpanningForest.cycleLattice_ext (hF : Γ.IsSpanningForest O F)
    (c d : Γ.cycleLattice O) (h : ∀ e : O, e.val ∉ F → c.val e = d.val e) : c = d := by
  apply Subtype.ext
  exact hF.eq_of_incidenceBoundary_eq_of_forall_notMem c.val d.val
    ((mem_cycleLattice_iff c.val).mp c.property |>.trans
      ((mem_cycleLattice_iff d.val).mp d.property).symm) h

/-- Binary cycles are determined by their coordinates off a spanning forest. -/
theorem IsSpanningForest.modTwoCycleSpace_ext (hF : Γ.IsSpanningForest O F)
    (c d : Γ.modTwoCycleSpace O) (h : ∀ e : O, e.val ∉ F → c.val e = d.val e) : c = d := by
  apply Subtype.ext
  exact hF.eq_of_incidenceBoundary_eq_of_forall_notMem c.val d.val
    ((mem_modTwoCycleSpace_iff c.val).mp c.property |>.trans
      ((mem_modTwoCycleSpace_iff d.val).mp d.property).symm) h

end TauCeti.SerreGraph
