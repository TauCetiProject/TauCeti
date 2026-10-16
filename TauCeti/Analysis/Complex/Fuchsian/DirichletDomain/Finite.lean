/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.DirichletDomain
public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Finite
import TauCeti.Analysis.Complex.Fuchsian.ProperAction

/-!
# Finite descriptions of cusp-truncated Dirichlet domains

If a Dirichlet domain of a discrete Fuchsian group is bounded outside finitely many cusp
horodiscs of positive heights, it is globally defined by finitely many distance inequalities.
These inequalities are the closed geodesic half-planes bounded by perpendicular bisectors of
the centre and its translates. This supplies the finite intersection needed to construct the
Dirichlet polygon, including domains with unbounded cusp ends.

Boundedness of the truncation is independent of its positive heights: the constraints from a
cusp generator bound the horizontal coordinate, so changing a height only adds bounded bands.
The finite constraints on the bounded core and the cusp ends agree with the domain on an open
neighbourhood. Geodesic convexity then gives equality globally, via
`UpperHalfPlane.dirichletDomain_eq_iInter_of_inter_eq`.

No finite-area hypothesis is used, and no assertion that finite area alone provides a bounded
truncation is made. The cusp data need not have distinct cusp orbits, and the index type may be
empty, in which case the hypothesis is boundedness of the whole domain.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §§3.2 and 4.2.

We combine `TauCeti.exists_finset_dirichletDomain_inter_eq` with
`TauCeti.Subgroup.CuspDatum.exists_finset_dirichletDomain_inter_horodisc_eq`.
-/

public section

open Metric Set UpperHalfPlane TauCeti
open TauCeti.UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) {ι : Type*} [Finite ι]

/-- A bounded truncation of a Dirichlet domain at positive cusp heights remains bounded after
changing any of the heights. The new heights need not be positive. -/
theorem isBounded_dirichletDomain_diff_iUnion_horodisc (p : ℍ) (D : ι → Γ.CuspDatum)
    {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (sdiff (dirichletDomain Γ p) (⋃ i, (D i).horodisc (A i))))
    (B : ι → ℝ) :
    Bornology.IsBounded (sdiff (dirichletDomain Γ p) (⋃ i, (D i).horodisc (B i))) := by
  classical
  refine (hb.union (Bornology.isBounded_iUnion.mpr fun i ↦
    (D i).isBounded_dirichletDomain_inter_horodisc_diff p (hA i) (B i))).subset ?_
  rintro z ⟨hz, hzB⟩
  by_cases hzA : z ∈ ⋃ i, (D i).horodisc (A i)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hzA
    exact Or.inr (mem_iUnion.mpr ⟨i, ⟨⟨hz, hi⟩, fun h ↦ hzB (mem_iUnion.mpr ⟨i, h⟩)⟩⟩)
  · exact Or.inl ⟨hz, hzA⟩

variable [DiscreteTopology Γ]

/-- If a Dirichlet domain has a bounded truncation outside finitely many cusp horodiscs of
positive heights, finitely many of its distance inequalities define it on all of `ℍ`.
The result omits elements fixing the centre and expresses the remaining constraints as closed
geodesic half-planes. Neither a trivial centre stabilizer nor distinct cusp data is required. -/
theorem exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane_of_isBounded_truncation
    (p : ℍ) (D : ι → Γ.CuspDatum) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (sdiff (dirichletDomain Γ p) (⋃ i, (D i).horodisc (A i)))) :
    ∃ s : Finset Γ, (∀ g ∈ s, p ≠ g • p) ∧
      dirichletDomain Γ p =
        ⋂ g ∈ s, _root_.closure (leftHalfPlane (perpBisector p (g • p))) := by
  classical
  let := Fintype.ofFinite ι
  -- Raise the cusp heights to where a fixed finite family describes every cusp end.
  let B (i : ι) := max (A i) (((D i).scaling • p).im + (D i).width / 2)
  have hbB := Γ.isBounded_dirichletDomain_diff_iUnion_horodisc p D hA hb B
  obtain ⟨r, hr⟩ := hbB.subset_closedBall p
  obtain ⟨s₀, hs₀⟩ := exists_finset_dirichletDomain_inter_eq (G := Γ) p
    (K := closedBall p (r + 1)) isBounded_closedBall
  have hends := fun i ↦ (D i).exists_finset_dirichletDomain_inter_horodisc_eq p
  choose t ht using hends
  let s := s₀ ∪ Finset.univ.biUnion t
  let U := ball p (r + 1) ∪ ⋃ i, (D i).horodisc (B i)
  have hU : IsOpen U := isOpen_ball.union (isOpen_iUnion fun i ↦ (D i).isOpen_horodisc _)
  have hDU : dirichletDomain Γ p ⊆ U := by
    intro z hz
    by_cases hends : z ∈ ⋃ i, (D i).horodisc (B i)
    · exact Or.inr hends
    · have hzr : dist z p ≤ r := hr ⟨hz, hends⟩
      exact Or.inl (mem_ball.mpr (by linarith))
  -- The core and ends form an open neighbourhood; agreement there gives global equality.
  have heq : dirichletDomain Γ p =
      ⋂ g ∈ s, {z : ℍ | dist z p ≤ dist z (g • p)} := by
    apply UpperHalfPlane.dirichletDomain_eq_iInter_of_inter_eq p s hU hDU
    apply subset_antisymm
    · rintro z ⟨hz, hzU⟩
      exact ⟨mem_iInter₂.mpr fun g _ ↦ mem_dirichletDomain.mp hz g, hzU⟩
    · rintro z ⟨hz, hzU⟩
      refine ⟨?_, hzU⟩
      rcases hzU with hzball | hzends
      · have hz₀ : z ∈ ⋂ g ∈ s₀, {z : ℍ | dist z p ≤ dist z (g • p)} :=
          mem_iInter₂.mpr fun g hg ↦ mem_iInter₂.mp hz g (Finset.mem_union_left _ hg)
        have hzD : z ∈ dirichletDomain Γ p ∩ closedBall p (r + 1) := by
          rw [hs₀]
          exact ⟨hz₀, ball_subset_closedBall hzball⟩
        exact hzD.1
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hzends
        have hzi : z ∈ ⋂ g ∈ t i, {z : ℍ | dist z p ≤ dist z (g • p)} :=
          mem_iInter₂.mpr fun g hg ↦ mem_iInter₂.mp hz g (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hg⟩))
        have hzD : z ∈ dirichletDomain Γ p ∩ (D i).horodisc (B i) := by
          rw [ht i (B i) (le_max_right _ _)]
          exact ⟨hzi, hi⟩
        exact hzD.1
  -- Remove inequalities from the centre stabilizer and express the others as half-planes.
  refine ⟨s.filter (fun g ↦ p ≠ g • p), fun g hg ↦ (Finset.mem_filter.mp hg).2, ?_⟩
  rw [heq]
  ext z
  simp only [mem_iInter, Finset.mem_filter]
  constructor
  · intro hz g hg
    exact (mem_closure_leftHalfPlane_perpBisector_iff hg.2 z).mpr (hz g hg.1)
  · intro hz g hg
    by_cases hgp : p = g • p
    · simp [← hgp]
    · exact (mem_closure_leftHalfPlane_perpBisector_iff hgp z).mp (hz g ⟨hg, hgp⟩)

end Subgroup
