/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Presentation
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Ideal

/-!
# One relation per finite vertex cycle

The polygon presentation initially imposes a cycle relation at every finite vertex. Those
relations are conjugate along a vertex cycle, with the same exponent. Thus it suffices to
retain one relation per finite cycle. This is the reduction that lets a polygon presentation
record a single elliptic relation for each elliptic vertex cycle, rather than repeating it at
every vertex of that cycle. Relations at ordinary finite cycles are retained too; ideal cycles
contribute no power relation.

`SidePairing.relatorsAt` restricts the finite-vertex relations to a specified set of vertices,
without changing the side-identification relations. If that set meets every finite vertex
cycle, its normal closure equals the original relator normal closure. The resulting
`SidePairing.relatorQuotientAtEquiv` preserves every side word. No tessellation hypotheses are
needed for this algebraic reduction. For a locally finite fundamental polygon,
`SidePairing.relatorQuotientAtEquivGroup` identifies the reduced presentation with the acting
group, with its evaluation on each generator specified.

`SidePairing.cycleRepresentatives` supplies a concrete transversal: the least side index on
each vertex cycle. Each cycle meets this set exactly once.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9 (polygon presentations).
* Svetlana Katok, *Fuchsian Groups*, Chapters 3–4 (vertex cycles and presentations).
-/

public noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- Side-identification relations, and finite-vertex cycle relations only at vertices in `s`.
An ideal vertex contributes no relation even if it belongs to `s`. -/
def relatorsAt (s : Set (Fin n)) : Set (FreeGroup (Fin n)) :=
  range σ.sideRelator ∪
    {w | ∃ (j : Fin n) (z : ℍ), j ∈ s ∧ P.vertex j = .inl z ∧
      w = σ.cycleWord j ^ orderOf (σ.cycleMap j)}

/-- Membership in the restricted relator set. -/
@[simp]
theorem mem_relatorsAt_iff {s : Set (Fin n)} {w : FreeGroup (Fin n)} :
    w ∈ σ.relatorsAt s ↔
      (∃ i, σ.sideRelator i = w) ∨
        (∃ (j : Fin n) (z : ℍ), j ∈ s ∧ P.vertex j = .inl z ∧
          w = σ.cycleWord j ^ orderOf (σ.cycleMap j)) := by
  simp [relatorsAt]

/-- A side-identification word belongs to every restricted relator set. -/
theorem sideRelator_mem_relatorsAt (s : Set (Fin n)) (i : Fin n) :
    σ.sideRelator i ∈ σ.relatorsAt s :=
  Or.inl ⟨i, rfl⟩

/-- The order relation at a retained finite vertex belongs to the restricted relator set. -/
theorem cycleWord_pow_mem_relatorsAt {s : Set (Fin n)} {j : Fin n} {z : ℍ}
    (hjs : j ∈ s) (hj : P.vertex j = .inl z) :
    σ.cycleWord j ^ orderOf (σ.cycleMap j) ∈ σ.relatorsAt s :=
  Or.inr ⟨j, z, hjs, hj, rfl⟩

/-- Every side-identification word is trivial in the reduced presentation. -/
@[simp]
theorem relatorQuotientAt_sideRelator (s : Set (Fin n)) (i : Fin n) :
    PresentedGroup.mk (σ.relatorsAt s) (σ.sideRelator i) = 1 :=
  PresentedGroup.one_of_mem (σ.sideRelator_mem_relatorsAt s i)

/-- A retained finite-vertex cycle word has order dividing that of its cycle transformation
in the reduced presentation. -/
@[simp]
theorem relatorQuotientAt_cycleWord_pow {s : Set (Fin n)} {j : Fin n} {z : ℍ}
    (hjs : j ∈ s) (hj : P.vertex j = .inl z) :
    PresentedGroup.mk (σ.relatorsAt s) (σ.cycleWord j) ^ orderOf (σ.cycleMap j) = 1 := by
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (σ.cycleWord_pow_mem_relatorsAt hjs hj)

/-- Restricting the vertices only removes relators. -/
theorem relatorsAt_subset_relators (s : Set (Fin n)) : σ.relatorsAt s ⊆ σ.relators := by
  rintro w (hw | ⟨j, z, -, hj, rfl⟩)
  · exact σ.mem_relators_iff.mpr (Or.inl hw)
  · exact σ.cycleWord_pow_mem_relators hj

/-- Retaining a relation at any one vertex of each finite cycle gives exactly the same normal
closure of relators. This holds for side-pairing data without any tessellation assumptions. -/
theorem normalClosure_relatorsAt_eq {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j) :
    Subgroup.normalClosure (σ.relatorsAt s) = Subgroup.normalClosure σ.relators := by
  apply le_antisymm (Subgroup.normalClosure_mono (σ.relatorsAt_subset_relators s))
  apply Subgroup.normalClosure_le_normal
  intro w hw
  rcases σ.mem_relators_iff.mp hw with ⟨i, rfl⟩ | ⟨j, z, hj, rfl⟩
  · exact Subgroup.subset_normalClosure (σ.sideRelator_mem_relatorsAt s i)
  · obtain ⟨i, his, hi⟩ := hs j (by simp [hj])
    have hfinite : (P.vertex i).isLeft := (σ.isLeft_vertex_eq_of_mem_cycle hi).trans
      (by simp [hj])
    obtain ⟨zi, hzi⟩ := Sum.isLeft_iff.mp hfinite
    have hrel : σ.cycleWord i ^ orderOf (σ.cycleMap i) ∈ σ.relatorsAt s :=
      σ.cycleWord_pow_mem_relatorsAt his hzi
    have hc := (σ.isConj_cycleWord_of_mem_cycle hi).symm.pow (orderOf (σ.cycleMap j))
    rw [σ.orderOf_cycleMap_eq_of_mem_cycle hi] at hrel
    exact Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨_, hrel, hc⟩)

/-- The reduced and original polygon presentations are canonically isomorphic, by the identity
on all side words, whenever the retained vertices meet each finite cycle. -/
def relatorQuotientAtEquiv {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j) :
    PresentedGroup (σ.relatorsAt s) ≃* σ.RelatorQuotient :=
  QuotientGroup.quotientMulEquivOfEq (σ.normalClosure_relatorsAt_eq hs)

/-- The presentation reduction preserves every side word. -/
@[simp]
theorem relatorQuotientAtEquiv_mk {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j)
    (w : FreeGroup (Fin n)) :
    σ.relatorQuotientAtEquiv hs (PresentedGroup.mk _ w) = PresentedGroup.mk _ w :=
  QuotientGroup.quotientMulEquivOfEq_mk _ w

/-- The presentation reduction preserves the side generators. -/
@[simp]
theorem relatorQuotientAtEquiv_of {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j) (i : Fin n) :
    σ.relatorQuotientAtEquiv hs (PresentedGroup.of i) = PresentedGroup.of i := by
  exact σ.relatorQuotientAtEquiv_mk hs (FreeGroup.of i)

/-- The inverse presentation reduction also preserves every side word. -/
@[simp]
theorem relatorQuotientAtEquiv_symm_mk {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j)
    (w : FreeGroup (Fin n)) :
    (σ.relatorQuotientAtEquiv hs).symm (PresentedGroup.mk _ w) = PresentedGroup.mk _ w := by
  apply (σ.relatorQuotientAtEquiv hs).injective
  simp

/-- The inverse presentation reduction preserves the side generators. -/
@[simp]
theorem relatorQuotientAtEquiv_symm_of {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j) (i : Fin n) :
    (σ.relatorQuotientAtEquiv hs).symm (PresentedGroup.of i) = PresentedGroup.of i := by
  exact σ.relatorQuotientAtEquiv_symm_mk hs (FreeGroup.of i)

/-- For a locally finite fundamental polygon, one finite-vertex relation per cycle, together
with the side relations, presents the acting group. -/
def relatorQuotientAtEquivGroup {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j)
    {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    PresentedGroup (σ.relatorsAt s) ≃* Γ :=
  (σ.relatorQuotientAtEquiv hs).trans
    (MulEquiv.ofBijective _ (σ.relatorQuotientTo_bijective hmap hlf hdisj))

/-- Evaluation from the reduced presentation agrees with evaluation of every free side word. -/
@[simp]
theorem relatorQuotientAtEquivGroup_mk {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j)
    {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (w : FreeGroup (Fin n)) :
    σ.relatorQuotientAtEquivGroup hs hmap hlf hdisj (PresentedGroup.mk _ w) =
      FreeGroup.lift (σ.generatorsIn hmap) w := by
  simp [relatorQuotientAtEquivGroup]

/-- A side generator in the reduced presentation evaluates to its actual side-pairing map. -/
@[simp]
theorem relatorQuotientAtEquivGroup_of {s : Set (Fin n)}
    (hs : ∀ j, (P.vertex j).isLeft → ∃ i ∈ s, i ∈ σ.cycle j)
    {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) (i : Fin n) :
    σ.relatorQuotientAtEquivGroup hs hmap hlf hdisj (PresentedGroup.of i) =
      σ.generatorsIn hmap i := by
  simp [relatorQuotientAtEquivGroup]

/-- In particular, the least-index representatives suffice for all finite-cycle relations. -/
theorem normalClosure_relatorsAt_cycleRepresentatives :
    Subgroup.normalClosure (σ.relatorsAt σ.cycleRepresentatives) =
      Subgroup.normalClosure σ.relators := by
  apply σ.normalClosure_relatorsAt_eq
  intro j _
  obtain ⟨i, hi, -⟩ := σ.existsUnique_mem_cycleRepresentatives j
  exact ⟨i, hi⟩

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
