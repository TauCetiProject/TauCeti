/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Basic

/-!
# Partial normalization of glued nodal curves

Cutting a set of nodes retains the normalization components and glues only the uncut flag
pairs. Each cut node is replaced by two distinct labelled smooth marks, even at a self-node.
The resulting curve need not be connected. Its map back to the original curve is a quotient
map whose only nontrivial fibres are the pairs of new marks. Maps out of the partial
normalization descend precisely when they agree on these pairs.

The special points on each normalization component are unchanged: a cut branch changes from
a node flag to a mark. This is the curve-level cutting operation used to decompose a nodal
curve into pointed pieces. No smoothing or analytic family is constructed here.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, for partial normalization and its branch markings.
-/

public noncomputable section

open Set Topology

namespace TauCeti.NodalGluing

variable {ι Flag : Type*} {X : ι → Type*} (d : FlagPairData ι Flag X) (S : Set Flag)

/-- The partial normalization at `S`: retain just the flag pairs outside `S`. -/
def FlagPairData.cut : FlagPairData ι {f // f ∉ S} X where
  fst f := d.fst f.1
  snd f := d.snd f.1
  fstPt f := d.fstPt f.1
  sndPt f := d.sndPt f.1
  flagPointOf_injective' := by
    have heq (p : {f // f ∉ S} × Bool) :
        flagPointOf (fun f ↦ d.fst f.1) (fun f ↦ d.snd f.1)
          (fun f ↦ d.fstPt f.1) (fun f ↦ d.sndPt f.1) p =
        flagPointOf d.fst d.snd d.fstPt d.sndPt (p.1.1, p.2) := by
      rcases p with ⟨f, b⟩
      cases b <;> simp only [flagPointOf_false, flagPointOf_true]
    intro p q hpq
    have h := d.flagPointOf_injective' ((heq p).symm.trans (hpq.trans (heq q)))
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun p : Flag × Bool ↦ p.2) h)

/-- Cutting does not change the first point of an uncut pair. -/
@[simp]
theorem fstPoint_cut (f : {f // f ∉ S}) : fstPoint (d.cut S) f = fstPoint d f.1 := by
  simp only [fstPoint_def, FlagPairData.cut]

/-- Cutting does not change the second point of an uncut pair. -/
@[simp]
theorem sndPoint_cut (f : {f // f ∉ S}) : sndPoint (d.cut S) f = sndPoint d f.1 := by
  simp only [sndPoint_def, FlagPairData.cut]

/-- An uncut branch retains its point in the normalization. -/
@[simp]
theorem flagPoint_cut (p : {f // f ∉ S} × Bool) :
    flagPoint (d.cut S) p = flagPoint d (p.1.1, p.2) := by
  rcases p with ⟨f, b⟩
  cases b <;> simp only [flagPoint_false, flagPoint_true, fstPoint_cut, sndPoint_cut]

/-- The remaining flag points are exactly the branches of uncut nodes. -/
theorem mem_flagPointSet_cut_iff (x : Σ i, X i) :
    x ∈ flagPointSet (d.cut S) ↔ ∃ f, f ∉ S ∧
      (x = fstPoint d f ∨ x = sndPoint d f) := by
  simp only [mem_flagPointSet, fstPoint_cut, sndPoint_cut, Subtype.exists, exists_prop]

/-- Every remaining flag point was an original flag point. -/
theorem flagPointSet_cut_subset : flagPointSet (d.cut S) ⊆ flagPointSet d := by
  intro x hx
  obtain ⟨f, _, hf⟩ := (mem_flagPointSet_cut_iff d S x).mp hx
  exact (mem_flagPointSet d x).mpr ⟨f, hf⟩

/-- The generating relation for the cut curve uses exactly the uncut pairs. -/
theorem flagRel_cut_iff (x y : Σ i, X i) :
    flagRel (d.cut S) x y ↔ ∃ f, f ∉ S ∧
      ((x = fstPoint d f ∧ y = sndPoint d f) ∨
        (x = sndPoint d f ∧ y = fstPoint d f)) := by
  simp only [flagRel_def, fstPoint_cut, sndPoint_cut, Subtype.exists, exists_prop]

/-- Cutting only removes identifications. -/
theorem gluedRel_cut_le : gluedRel (d.cut S) ≤ gluedRel d := by
  intro x y h
  rw [gluedRel_def, flagRel_def]
  rcases (gluedRel_def _ _ _).mp h with h | h
  · exact Or.inl h
  · obtain ⟨f, _, hf⟩ := (flagRel_cut_iff d S x y).mp h
    exact Or.inr ⟨f, hf⟩

/-- An original branch point remains a flag point exactly when its node was not cut. -/
-- Simplify before the general membership lemma expands flag points into an existential.
@[simp↓]
theorem flagPoint_mem_flagPointSet_cut_iff (p : Flag × Bool) :
    flagPoint d p ∈ flagPointSet (d.cut S) ↔ p.1 ∉ S := by
  rw [flagPointSet_eq_range]
  constructor
  · rintro ⟨q, hq⟩
    rw [flagPoint_cut] at hq
    exact (congrArg Prod.fst (flagPoint_injective d hq)) ▸ q.1.2
  · intro hp
    exact ⟨(⟨p.1, hp⟩, p.2), flagPoint_cut d S _⟩

/-- The map regluing the two branches of each cut node. -/
def reglueMap : GluedCurve (d.cut S) → GluedCurve d :=
  GluedCurve.lift (d.cut S) (Quotient.mk (gluedRelSetoid d)) (fun f ↦ by simp)

/-- Regluing is the identity on normalization representatives. -/
@[simp]
theorem reglueMap_mk (x : Σ i, X i) :
    reglueMap d S (Quotient.mk _ x) = Quotient.mk (gluedRelSetoid d) x := by
  simp [reglueMap]

/-- Every point of the original curve has a preimage under regluing. -/
theorem reglueMap_surjective : Function.Surjective (reglueMap d S) := by
  intro z
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
  exact ⟨Quotient.mk _ x, reglueMap_mk d S x⟩

/-- Distinct points have the same image under regluing exactly when they are the two branches
of one of the cut nodes, in either order. -/
theorem reglueMap_eq_reglueMap_iff (x y : GluedCurve (d.cut S)) :
    reglueMap d S x = reglueMap d S y ↔ x = y ∨ ∃ f ∈ S,
      (x = Quotient.mk _ (fstPoint d f) ∧ y = Quotient.mk _ (sndPoint d f)) ∨
      (x = Quotient.mk _ (sndPoint d f) ∧ y = Quotient.mk _ (fstPoint d f)) := by
  induction x using Quotient.inductionOn with | _ x =>
  induction y using Quotient.inductionOn with | _ y =>
  simp only [reglueMap_mk]
  constructor
  · intro h
    rw [Quotient.eq, gluedRelSetoid_r, gluedRel_def, flagRel_def] at h
    rcases h with h | ⟨f, hf⟩
    · exact Or.inl (congrArg (Quotient.mk _) h)
    · by_cases hs : f ∈ S
      · exact Or.inr ⟨f, hs, hf.imp
          (fun h ↦ ⟨congrArg (Quotient.mk _) h.1, congrArg (Quotient.mk _) h.2⟩)
          (fun h ↦ ⟨congrArg (Quotient.mk _) h.1, congrArg (Quotient.mk _) h.2⟩)⟩
      · exact Or.inl ((Quotient.eq.trans (gluedRelSetoid_r _ _ _)).mpr
          ((gluedRel_def _ _ _).mpr (Or.inr ((flagRel_cut_iff d S x y).mpr ⟨f, hs, hf⟩))))
  · rintro (h | ⟨f, _, h | h⟩)
    · simpa only [reglueMap_mk] using congrArg (reglueMap d S) h
    · have h₁ := congrArg (reglueMap d S) h.1
      have h₂ := congrArg (reglueMap d S) h.2
      simp only [reglueMap_mk, mk_fstPoint, mk_sndPoint] at h₁ h₂
      exact h₁.trans h₂.symm
    · have h₁ := congrArg (reglueMap d S) h.1
      have h₂ := congrArg (reglueMap d S) h.2
      simp only [reglueMap_mk, mk_fstPoint, mk_sndPoint] at h₁ h₂
      exact h₁.trans h₂.symm

/-- The two branches of a node are distinct in the partial normalization exactly when that
node was cut. This includes self-nodes. -/
@[simp]
theorem mk_fstPoint_ne_mk_sndPoint_cut_iff (f : Flag) :
    (Quotient.mk (gluedRelSetoid (d.cut S)) (fstPoint d f) ≠
      Quotient.mk _ (sndPoint d f)) ↔ f ∈ S := by
  constructor
  · intro h
    by_contra hf
    exact h (by simpa only [fstPoint_cut, sndPoint_cut] using
      (mk_fstPoint (d.cut S) ⟨f, hf⟩).trans (mk_sndPoint (d.cut S) ⟨f, hf⟩).symm)
  · intro hf h
    have hx : fstPoint d f ∉ flagPointSet (d.cut S) := by
      simpa only [← flagPoint_false, flagPoint_mem_flagPointSet_cut_iff, not_not] using hf
    exact fstPoint_ne_sndPoint d f f (eq_of_mk_eq_of_notMem_flagPointSet hx h)

/-- A function on the partial normalization descends uniquely to the original curve exactly
when its values agree on the two branches of each cut node. -/
theorem existsUnique_comp_reglueMap_eq_iff {Y : Type*} (h : GluedCurve (d.cut S) → Y) :
    (∃! g : GluedCurve d → Y, g ∘ reglueMap d S = h) ↔
      ∀ f ∈ S, h (Quotient.mk _ (fstPoint d f)) = h (Quotient.mk _ (sndPoint d f)) := by
  constructor
  · rintro ⟨g, hg, _⟩ f _
    rw [← hg]
    simp
  · intro hh
    have hpairs (f : Flag) : h (Quotient.mk _ (fstPoint d f)) =
        h (Quotient.mk _ (sndPoint d f)) := by
      by_cases hf : f ∈ S
      · exact hh f hf
      · exact congrArg h (by simpa only [fstPoint_cut, sndPoint_cut] using
          (mk_fstPoint (d.cut S) ⟨f, hf⟩).trans (mk_sndPoint (d.cut S) ⟨f, hf⟩).symm)
    let g := GluedCurve.lift d (fun x ↦ h (Quotient.mk _ x)) hpairs
    have hg : g ∘ reglueMap d S = h := by
      funext x
      induction x using Quotient.inductionOn with | _ x =>
      simp [g]
    exact ⟨g, hg, fun g' hg' ↦ (reglueMap_surjective d S).injective_comp_right
      (hg'.trans hg.symm)⟩

section Topology

variable [∀ i, TopologicalSpace (X i)]

/-- Regluing is continuous for the normalization quotient topologies. -/
theorem continuous_reglueMap : Continuous (reglueMap d S) :=
  GluedCurve.continuous_lift _ _ _ continuous_quotient_mk'

/-- The original curve has precisely the quotient topology for regluing the cut branches.
No compactness or separation hypothesis is necessary. -/
theorem isQuotientMap_reglueMap : IsQuotientMap (reglueMap d S) := by
  have hcomp : reglueMap d S ∘ Quotient.mk (gluedRelSetoid (d.cut S)) =
      Quotient.mk (gluedRelSetoid d) := funext (reglueMap_mk d S)
  apply IsQuotientMap.of_comp (f := Quotient.mk (gluedRelSetoid (d.cut S)))
    continuous_quotient_mk' (continuous_reglueMap d S)
  rw [hcomp]
  exact isQuotientMap_quotient_mk'

/-- Continuous maps descend uniquely through regluing exactly when they agree on each cut
branch pair. The descended map is continuous in the quotient topology. -/
theorem existsUnique_continuous_comp_reglueMap_eq_iff {Y : Type*} [TopologicalSpace Y]
    (h : GluedCurve (d.cut S) → Y) (hc : Continuous h) :
    (∃! g : GluedCurve d → Y, Continuous g ∧ g ∘ reglueMap d S = h) ↔
      ∀ f ∈ S, h (Quotient.mk _ (fstPoint d f)) = h (Quotient.mk _ (sndPoint d f)) := by
  constructor
  · rintro ⟨g, ⟨_, hg⟩, _⟩
    exact (existsUnique_comp_reglueMap_eq_iff d S h).mp
      ⟨g, hg, fun g' hg' ↦ (reglueMap_surjective d S).injective_comp_right
        (hg'.trans hg.symm)⟩
  · intro hh
    obtain ⟨g, hg, huniq⟩ := (existsUnique_comp_reglueMap_eq_iff d S h).mpr hh
    exact ⟨g, ⟨(isQuotientMap_reglueMap d S).continuous_iff.mpr (hg.symm ▸ hc), hg⟩,
      fun g' hg' ↦ huniq g' hg'.2⟩

end Topology

variable {d S} {L : Type*}

/-- Marks on a partial normalization: retain the old labels and add a separate label for
each of the two branches of every cut node. -/
def Marking.cut (m : Marking d L) (S : Set Flag) : Marking (d.cut S) (L ⊕ (S × Bool)) where
  point := Sum.elim m.point (fun p ↦ flagPoint d (p.1.1, p.2))
  point_injective := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (m.point_injective h)
      | inr b =>
        exact (m.point_notMem_flagPointSet a ((flagPointSet_eq_range d).symm ▸ ⟨_, h.symm⟩)).elim
    | inr a =>
      cases b with
      | inl b =>
        exact (m.point_notMem_flagPointSet b ((flagPointSet_eq_range d).symm ▸ ⟨_, h⟩)).elim
      | inr b =>
        have hab := flagPoint_injective d h
        exact congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg Prod.fst hab))
          (congrArg (fun p : Flag × Bool ↦ p.2) hab))
  point_notMem_flagPointSet := by
    intro a
    cases a with
    | inl a => exact fun h ↦ m.point_notMem_flagPointSet a (flagPointSet_cut_subset d S h)
    | inr a => exact fun h ↦ ((flagPoint_mem_flagPointSet_cut_iff d S _).mp h) a.1.2

variable (m : Marking d L) (S)

/-- Old marks retain their points. -/
@[simp]
theorem Marking.point_cut_inl (l : L) : (m.cut S).point (.inl l) = m.point l := (rfl)

/-- A new mark is the corresponding branch point of the cut node. -/
@[simp]
theorem Marking.point_cut_inr (p : S × Bool) :
    (m.cut S).point (.inr p) = flagPoint d (p.1.1, p.2) := (rfl)

/-- Cutting preserves every special point on every normalization component: cut branches
become marks, and all other node flags and marks remain. -/
@[simp]
theorem Marking.specialPoints_cut (i : ι) : (m.cut S).specialPoints i = m.specialPoints i := by
  ext x
  simp only [Marking.mem_specialPoints_iff]
  constructor
  · rintro (hx | ⟨l | p, hp⟩)
    · exact Or.inl (flagPointSet_cut_subset d S hx)
    · exact Or.inr ⟨l, hp⟩
    · exact Or.inl ((flagPointSet_eq_range d).symm ▸ ⟨_, hp⟩)
  · rintro (hx | ⟨l, hl⟩)
    · rw [flagPointSet_eq_range] at hx
      obtain ⟨⟨f, b⟩, hx⟩ := hx
      rw [← hx]
      by_cases hf : f ∈ S
      · exact Or.inr ⟨.inr (⟨f, hf⟩, b), rfl⟩
      · exact Or.inl ((flagPoint_mem_flagPointSet_cut_iff d S _).mpr hf)
    · exact Or.inr ⟨.inl l, hl⟩

end TauCeti.NodalGluing
