/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.DominatedVertex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.Product
import Mathlib.Data.Finset.Max

/-!
# A finite ordered cylinder collapses onto its terminal endpoint

The staircase triangulation of `K × [0,1]` collapses onto the copy of `K` at time one.
Remove the lower vertices in decreasing order. At each stage a lower vertex is dominated by
its upper partner, so dominated-vertex deletion supplies a sequence of elementary collapses.
All faces of the terminal copy are retained throughout. In particular, the cylinder on any
finite collapsible complex is collapsible, without a cone or apex-order hypothesis.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapters 2–3 (staircase products and simplicial collapse).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι]

/-- The intermediate cylinder with lower vertices restricted to `R`, and all upper vertices
retained. This is only used to specify the stages of the collapse. -/
private def trimmedCylinder (K : PreAbstractSimplicialComplex ι) (R : Finset ι) :
    PreAbstractSimplicialComplex (ι × Fin 2) where
  faces := {σ | σ ∈ orderedProd K ⊤ ∧ ∀ p ∈ σ, p.2 = 0 → p.1 ∈ R}
  isRelLowerSet_faces := by
    intro σ hσ
    exact ⟨((orderedProd K ⊤).isRelLowerSet_faces hσ.1).1,
      fun τ hτσ hτ => ⟨((orderedProd K ⊤).isRelLowerSet_faces hσ.1).2 hτσ hτ,
        fun p hp => hσ.2 p (hτσ hp)⟩⟩

private theorem mem_trimmedCylinder {K : PreAbstractSimplicialComplex ι} {R : Finset ι}
    {σ : Finset (ι × Fin 2)} :
    σ ∈ trimmedCylinder K R ↔
      σ ∈ orderedProd K ⊤ ∧ ∀ p ∈ σ, p.2 = 0 → p.1 ∈ R := Iff.rfl

private theorem trimmedCylinder_erase (K : PreAbstractSimplicialComplex ι)
    (R : Finset ι) (v : ι) :
    trimmedCylinder K (R.erase v) = deletion (trimmedCylinder K R) {(v, (0 : Fin 2))} := by
  apply SetLike.ext
  intro σ
  simp only [mem_trimmedCylinder, mem_deletion, Finset.singleton_subset_iff,
    Finset.mem_erase]
  constructor
  · rintro ⟨hσ, hR⟩
    refine ⟨⟨hσ, fun p hp hzero => (hR p hp hzero).2⟩, ?_⟩
    intro hv
    exact (hR (v, 0) hv rfl).1 rfl
  · rintro ⟨⟨hσ, hR⟩, hv⟩
    refine ⟨hσ, fun p hp hzero => ⟨?_, hR p hp hzero⟩⟩
    intro heq
    apply hv
    have hpv : p = (v, 0) := Prod.ext heq hzero
    exact hpv ▸ hp

private theorem dominated_trimmedCylinder {K : PreAbstractSimplicialComplex ι}
    {R : Finset ι} {v : ι} (hv : ∀ a ∈ R, a ≤ v) :
    ∀ σ ∈ trimmedCylinder K R, (v, (0 : Fin 2)) ∈ σ →
      insert (v, (1 : Fin 2)) σ ∈ trimmedCylinder K R := by
  intro σ hσ hvσ
  obtain ⟨hσprod, hR⟩ := mem_trimmedCylinder.mp hσ
  obtain ⟨hK, _, hchain⟩ := mem_orderedProd_iff.mp hσprod
  refine mem_trimmedCylinder.mpr ⟨mem_orderedProd_iff.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · have hvfst : v ∈ σ.image Prod.fst := Finset.mem_image.mpr ⟨(v, 0), hvσ, rfl⟩
    simpa only [Finset.image_insert, Prod.fst, Finset.insert_eq_of_mem hvfst] using hK
  · exact Finset.image_nonempty.mpr (Finset.insert_nonempty _ _)
  · rw [Finset.coe_insert]
    apply hchain.insert
    intro p hp _
    by_cases hpzero : p.2 = 0
    · exact Or.inr ⟨hv p.1 (hR p hp hpzero), Fin.le_last _⟩
    · have hpone : p.2 = 1 := by omega
      rcases le_total v p.1 with hle | hle
      · exact Or.inl ⟨hle, by omega⟩
      · exact Or.inr ⟨hle, Fin.le_last _⟩
  · intro p hp hpzero
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simp at hpzero
    · exact hR p hp hpzero

private theorem trimmedCylinder_empty (K : PreAbstractSimplicialComplex ι) :
    trimmedCylinder K ∅ = K.map (fun a => (a, (1 : Fin 2))) := by
  apply SetLike.ext
  intro σ
  constructor
  · intro hσ
    obtain ⟨hprod, hR⟩ := mem_trimmedCylinder.mp hσ
    have hone : ∀ p ∈ σ, p.2 = 1 := by
      intro p hp
      have hzero : p.2 ≠ 0 := fun h => Finset.notMem_empty _ (hR p hp h)
      omega
    refine mem_map_iff.mpr ⟨σ.image Prod.fst, (mem_orderedProd_iff.mp hprod).1, ?_⟩
    ext p
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨q, hq, rfl⟩, rfl⟩
      have heq : (q.1, (1 : Fin 2)) = q := Prod.ext rfl (hone q hq).symm
      exact heq.symm ▸ hq
    · intro hp
      exact ⟨p.1, ⟨p, hp, rfl⟩, Prod.ext rfl (hone p hp).symm⟩
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := mem_map_iff.mp hσ
    refine mem_trimmedCylinder.mpr ⟨?_, ?_⟩
    · exact SimplicialMap.map_prodMkLeft_le_orderedProd K ⊤ 1
        (Finset.singleton_nonempty _) (mem_map_iff.mpr ⟨τ, hτ, rfl⟩)
    · intro p hp hzero
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      simp at hzero

private theorem collapsesTo_trimmedCylinder_empty (K : PreAbstractSimplicialComplex ι)
    (hfin : K.faces.Finite) (R : Finset ι) :
    CollapsesTo (trimmedCylinder K R) (trimmedCylinder K ∅) := by
  refine Finset.strongInductionOn R ?_
  intro R ih
  by_cases hR : R.Nonempty
  · let v := R.max' hR
    have hv : v ∈ R := R.max'_mem hR
    have hstep : CollapsesTo (trimmedCylinder K R)
        (trimmedCylinder K (R.erase v)) := by
      rw [trimmedCylinder_erase]
      apply collapsesTo_deletion_vertex_of_dominated (w := (v, (1 : Fin 2)))
      · intro heq
        have hne : (1 : Fin 2) = 0 := congrArg Prod.snd heq
        simp at hne
      · have htop : (⊤ : PreAbstractSimplicialComplex (Fin 2)).faces.Finite := by
          simpa only [simplex_univ] using
            (finite_faces_simplex (Finset.univ : Finset (Fin 2)))
        have hprod : (orderedProd K (⊤ : PreAbstractSimplicialComplex (Fin 2))).faces.Finite :=
          finite_faces_orderedProd hfin htop
        exact hprod.subset (fun σ hσ => (mem_trimmedCylinder.mp hσ.1).1)
      · exact dominated_trimmedCylinder (fun a ha => R.le_max' a ha)
    exact hstep.trans (ih _ (Finset.erase_ssubset hv))
  · have heq : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    subst R
    exact CollapsesTo.refl _

/-- The staircase cylinder of a finite complex collapses onto its terminal endpoint copy.
The ambient vertex type can be infinite; only the face set is required to be finite. -/
theorem collapsesTo_orderedProd_interval_one (K : PreAbstractSimplicialComplex ι)
    (hfin : K.faces.Finite) :
    CollapsesTo (orderedProd K (⊤ : PreAbstractSimplicialComplex (Fin 2)))
      (K.map (fun a => (a, (1 : Fin 2)))) := by
  classical
  let R : Finset ι := hfin.toFinset.biUnion id
  have hR : trimmedCylinder K R = orderedProd K ⊤ := by
    apply SetLike.ext
    intro σ
    refine ⟨fun h => (mem_trimmedCylinder.mp h).1, fun h => mem_trimmedCylinder.mpr ⟨h, ?_⟩⟩
    intro p hp _
    apply Finset.mem_biUnion.mpr
    exact ⟨σ.image Prod.fst, hfin.mem_toFinset.mpr (mem_orderedProd_iff.mp h).1,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  rw [← hR, ← trimmedCylinder_empty]
  exact collapsesTo_trimmedCylinder_empty K hfin R

/-- Taking a staircase cylinder preserves collapsibility. -/
theorem Collapsible.orderedProd_interval {K : PreAbstractSimplicialComplex ι}
    (h : Collapsible K) :
    Collapsible (orderedProd K (⊤ : PreAbstractSimplicialComplex (Fin 2))) := by
  apply Collapsible.of_collapsesTo (collapsesTo_orderedProd_interval_one K h.finite_faces)
  exact (Collapsible.map_iff_of_injective (fun a => (a, (1 : Fin 2)))
    (fun _ _ h => congrArg Prod.fst h)).mpr h

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι]

/-- A finite ordered cylinder collapses onto the copy of its base at time one. -/
theorem collapsesTo_orderedCylinder_one (K : AbstractSimplicialComplex ι)
    (hfin : K.faces.Finite) :
    PreAbstractSimplicialComplex.CollapsesTo K.orderedCylinder.toPreAbstractSimplicialComplex
      (K.toPreAbstractSimplicialComplex.map (fun a => (a, (1 : Fin 2)))) := by
  rw [orderedCylinder_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.collapsesTo_orderedProd_interval_one
    K.toPreAbstractSimplicialComplex hfin

/-- The ordered cylinder of a collapsible complex is collapsible. This supplies the
collapsible-base case of the cylinder collapsibility problem. -/
theorem collapsible_orderedCylinder_of_collapsible (K : AbstractSimplicialComplex ι)
    (h : PreAbstractSimplicialComplex.Collapsible K.toPreAbstractSimplicialComplex) :
    PreAbstractSimplicialComplex.Collapsible K.orderedCylinder.toPreAbstractSimplicialComplex := by
  rw [orderedCylinder_toPreAbstractSimplicialComplex]
  exact h.orderedProd_interval

end AbstractSimplicialComplex
