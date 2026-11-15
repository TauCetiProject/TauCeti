/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Presentation
import TauCeti.GroupTheory.Presentation.Tietze
import TauCeti.GroupTheory.PresentedGroup

/-!
# One generator per paired side

The presentation of a side-paired polygon initially has one generator for every side and
relations identifying paired generators as inverses. Here the larger index in each distinct
pair is eliminated. A side paired with itself retains its generator and its square relation;
such sides cannot simply be discarded. The remaining relators are the finite-vertex cycle
relations with this substitution performed.

`SidePairing.sidePresentationEquiv` identifies the resulting presentation with the original
polygon presentation. `SidePairing.sidePresentationEquivGroup` identifies it with the acting
group when the polygon has locally finite translates and disjoint translated interiors.
The generator and word formulas specify the maps in both directions.

The construction uses `PresentedGroup.eliminateGenerators`, the Tietze transformation that
substitutes defining words for auxiliary generators.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapters 3–4.
* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Chapter II, §2.
-/

public section

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- The smaller side in each pair, including every side paired with itself. -/
abbrev SideRepresentative := {i : Fin n // i ≤ σ.pair i}

/-- There is one representative for each pair of sides, so twice the number of representatives
is the number of sides plus the number of self-paired sides. -/
theorem two_mul_natCard_sideRepresentative :
    2 * Nat.card σ.SideRepresentative = n + Nat.card {i : Fin n // σ.pair i = i} := by
  classical
  have hlt : Nat.card {i : Fin n // ¬ i ≤ σ.pair i} = Nat.card {i : Fin n // i < σ.pair i} :=
    Nat.card_congr (σ.pair.subtypeEquiv fun i ↦ by rw [not_le, σ.pair_pair])
  have hle : Nat.card σ.SideRepresentative =
      Nat.card {i : Fin n // i < σ.pair i} + Nat.card {i : Fin n // σ.pair i = i} := by
    simp only [Nat.card_eq_fintype_card]
    rw [← Fintype.card_subtype_or_disjoint _ _ fun p hlt heq i hi ↦
      (hlt i hi).ne (heq i hi).symm]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun i ↦ by rw [le_iff_lt_or_eq, eq_comm])
  have hsum : Nat.card σ.SideRepresentative + Nat.card {i : Fin n // ¬ i ≤ σ.pair i} = n := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl _), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  omega

private abbrev DiscardedSide := {i : Fin n // ¬ i ≤ σ.pair i}

private def sideSplit : Fin n ≃ σ.SideRepresentative ⊕ σ.DiscardedSide :=
  (Equiv.sumCompl fun i : Fin n ↦ i ≤ σ.pair i).symm

private def replacement (i : σ.DiscardedSide) : FreeGroup σ.SideRepresentative :=
  (FreeGroup.of ⟨σ.pair i, by simpa using le_of_lt (lt_of_not_ge i.2)⟩)⁻¹

/-- Substitute the retained side generator or its inverse for each original side generator. -/
def sideSubstitution : FreeGroup (Fin n) →* FreeGroup σ.SideRepresentative :=
  (FreeGroup.lift (Sum.elim FreeGroup.of σ.replacement)).comp
    (FreeGroup.freeGroupCongr σ.sideSplit).toMonoidHom

/-- A retained side is sent to its generator. -/
@[simp]
theorem sideSubstitution_of_le {i : Fin n} (hi : i ≤ σ.pair i) :
    σ.sideSubstitution (FreeGroup.of i) = FreeGroup.of ⟨i, hi⟩ := by
  simp [sideSubstitution, sideSplit,
    Equiv.sumCompl_symm_apply_of_pos (p := fun i : Fin n ↦ i ≤ σ.pair i) hi]

/-- An eliminated side is sent to the inverse generator of its paired side. -/
@[simp]
theorem sideSubstitution_of_not_le {i : Fin n} (hi : ¬ i ≤ σ.pair i) :
    σ.sideSubstitution (FreeGroup.of i) =
      (FreeGroup.of ⟨σ.pair i, by simpa using le_of_lt (lt_of_not_ge hi)⟩)⁻¹ := by
  simp [sideSubstitution, sideSplit, replacement,
    Equiv.sumCompl_symm_apply_of_neg (p := fun i : Fin n ↦ i ≤ σ.pair i) hi]

/-- The relators after eliminating inverse-paired side generators: squares at self-paired
sides and substituted finite-vertex cycle powers. Ideal vertices contribute no relator. -/
def sidePresentationRelators : Set (FreeGroup σ.SideRepresentative) :=
  {w | ∃ i : σ.SideRepresentative, σ.pair i = i ∧ w = FreeGroup.of i ^ 2} ∪
    {w | ∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
      w = σ.sideSubstitution (σ.cycleWord j) ^ orderOf (σ.cycleMap j)}

/-- Membership in the presentation with one generator per side pair. -/
@[simp]
theorem mem_sidePresentationRelators_iff {w : FreeGroup σ.SideRepresentative} :
    w ∈ σ.sidePresentationRelators ↔
      (∃ i : σ.SideRepresentative, σ.pair i = i ∧ w = FreeGroup.of i ^ 2) ∨
      (∃ (j : Fin n) (z : ℍ), P.vertex j = .inl z ∧
        w = σ.sideSubstitution (σ.cycleWord j) ^ orderOf (σ.cycleMap j)) := Iff.rfl

/-- The polygon presentation with one generator per side pair. -/
abbrev SidePresentation := PresentedGroup σ.sidePresentationRelators

/-- A self-paired side retains its square relation after elimination. -/
@[simp]
theorem sidePresentation_of_sq (i : σ.SideRepresentative) (hi : σ.pair i = i) :
    (PresentedGroup.of i : σ.SidePresentation) ^ 2 = 1 := by
  rw [PresentedGroup.of, ← map_pow]
  exact PresentedGroup.one_of_mem (Or.inl ⟨i, hi, rfl⟩)

/-- The substituted cycle word at a finite vertex retains its order relation. -/
@[simp]
theorem sidePresentation_cycleWord_pow {j : Fin n} {z : ℍ} (hj : P.vertex j = .inl z) :
    PresentedGroup.mk σ.sidePresentationRelators (σ.sideSubstitution (σ.cycleWord j)) ^
      orderOf (σ.cycleMap j) = 1 := by
  rw [← map_pow]
  exact PresentedGroup.one_of_mem (Or.inr ⟨j, z, hj, rfl⟩)

private theorem sideSubstitution_sideRelator (i : Fin n) :
    σ.sideSubstitution (σ.sideRelator i) =
      if h : σ.pair i = i then FreeGroup.of ⟨i, by simp [h]⟩ ^ 2 else 1 := by
  rw [sideRelator_def, map_mul]
  split_ifs with h
  · simp [h, pow_two]
  · by_cases hi : i ≤ σ.pair i
    · have hp : ¬ σ.pair i ≤ σ.pair (σ.pair i) := by
        simpa using (lt_of_le_of_ne hi (Ne.symm h)).not_ge
      simp [σ.sideSubstitution_of_le hi, σ.sideSubstitution_of_not_le hp]
    · have hp : σ.pair i ≤ σ.pair (σ.pair i) := by
        simpa using le_of_lt (lt_of_not_ge hi)
      simp [σ.sideSubstitution_of_le hp, σ.sideSubstitution_of_not_le hi]

private theorem normalClosure_sideSubstitution_relators :
    Subgroup.normalClosure (σ.sideSubstitution '' σ.relators) =
      Subgroup.normalClosure σ.sidePresentationRelators := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, hw, rfl⟩
    rcases σ.mem_relators_iff.mp hw with ⟨i, rfl⟩ | ⟨j, z, hj, rfl⟩
    · rw [σ.sideSubstitution_sideRelator]
      split_ifs with h
      · exact Subgroup.subset_normalClosure (Or.inl ⟨_, h, rfl⟩)
      · exact Subgroup.one_mem _
    · exact Subgroup.subset_normalClosure (Or.inr ⟨j, z, hj, map_pow _ _ _⟩)
  · apply Subgroup.normalClosure_mono
    rintro w (⟨i, hi, rfl⟩ | ⟨j, z, hj, rfl⟩)
    · exact ⟨σ.sideRelator i, σ.sideRelator_mem_relators i, by
        simp [σ.sideSubstitution_sideRelator, hi]⟩
    · exact ⟨_, σ.cycleWord_pow_mem_relators hj, map_pow _ _ _⟩

private theorem split_relators_eq :
    range (fun i : σ.DiscardedSide ↦ FreeGroup.of (Sum.inr i) *
        (FreeGroup.map Sum.inl (σ.replacement i))⁻¹) ∪
      (FreeGroup.freeGroupCongr σ.sideSplit '' σ.relators) =
        FreeGroup.freeGroupCongr σ.sideSplit '' σ.relators := by
  apply union_eq_right.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨σ.sideRelator (σ.pair i), σ.sideRelator_mem_relators _, ?_⟩
  have hp : σ.pair i ≤ σ.pair (σ.pair i) := by
    simpa using le_of_lt (lt_of_not_ge i.2)
  simp [sideRelator_def, sideSplit, replacement,
    Equiv.sumCompl_symm_apply_of_pos (p := fun i : Fin n ↦ i ≤ σ.pair i) hp,
    Equiv.sumCompl_symm_apply_of_neg (p := fun i : Fin n ↦ i ≤ σ.pair i) i.2]

private def splitEquiv : σ.RelatorQuotient ≃*
    PresentedGroup (range (fun i : σ.DiscardedSide ↦ FreeGroup.of (Sum.inr i) *
        (FreeGroup.map Sum.inl (σ.replacement i))⁻¹) ∪
      (FreeGroup.freeGroupCongr σ.sideSplit '' σ.relators)) :=
  (PresentedGroup.equivPresentedGroup σ.relators σ.sideSplit).trans
    (PresentedGroup.equivOfNormalClosureEq (congrArg Subgroup.normalClosure
      σ.split_relators_eq.symm))

private theorem splitEquiv_mk (w : FreeGroup (Fin n)) :
    σ.splitEquiv (PresentedGroup.mk _ w) =
      PresentedGroup.mk _ (FreeGroup.freeGroupCongr σ.sideSplit w) := by
  simp [splitEquiv]

private theorem substituted_relators_eq :
    FreeGroup.lift (Sum.elim FreeGroup.of σ.replacement) ''
        (FreeGroup.freeGroupCongr σ.sideSplit '' σ.relators) =
      σ.sideSubstitution '' σ.relators := by
  rw [← image_comp]
  rfl

/-- **Elimination of inverse-paired side generators.** The original polygon presentation is
isomorphic to the presentation with one generator per side pair, square relations for
self-paired sides, and the substituted finite-vertex cycle relations. -/
def sidePresentationEquiv : σ.RelatorQuotient ≃* σ.SidePresentation :=
  σ.splitEquiv |>.trans
    (PresentedGroup.eliminateGenerators σ.replacement
      (FreeGroup.freeGroupCongr σ.sideSplit '' σ.relators)) |>.trans
    (PresentedGroup.equivOfNormalClosureEq (by
      rw [σ.substituted_relators_eq, σ.normalClosure_sideSubstitution_relators]))

/-- On any side word, the presentation equivalence performs the explicit substitution. -/
@[simp]
theorem sidePresentationEquiv_mk (w : FreeGroup (Fin n)) :
    σ.sidePresentationEquiv (PresentedGroup.mk _ w) =
      PresentedGroup.mk _ (σ.sideSubstitution w) := by
  simp only [sidePresentationEquiv, MulEquiv.trans_apply, σ.splitEquiv_mk,
    PresentedGroup.eliminateGenerators_mk, PresentedGroup.equivOfNormalClosureEq_mk]
  rfl

/-- A retained side generator is preserved by elimination. -/
@[simp]
theorem sidePresentationEquiv_of (i : σ.SideRepresentative) :
    σ.sidePresentationEquiv (PresentedGroup.of (i : Fin n)) = PresentedGroup.of i := by
  simpa only [PresentedGroup.of, σ.sideSubstitution_of_le i.2] using
    σ.sidePresentationEquiv_mk (FreeGroup.of (i : Fin n))

/-- The inverse equivalence includes every retained generator as its original side generator. -/
@[simp]
theorem sidePresentationEquiv_symm_of (i : σ.SideRepresentative) :
    σ.sidePresentationEquiv.symm (PresentedGroup.of i) = PresentedGroup.of (i : Fin n) :=
  σ.sidePresentationEquiv.symm_apply_eq.mpr (σ.sidePresentationEquiv_of i).symm

/-- The inverse equivalence includes words in retained side generators. -/
@[simp]
theorem sidePresentationEquiv_symm_mk (w : FreeGroup σ.SideRepresentative) :
    σ.sidePresentationEquiv.symm (PresentedGroup.mk _ w) =
      PresentedGroup.mk _ (FreeGroup.map Subtype.val w) := by
  have h : σ.sidePresentationEquiv.symm.toMonoidHom.comp (PresentedGroup.mk _) =
      (PresentedGroup.mk _).comp (FreeGroup.map Subtype.val) := by
    ext i
    exact σ.sidePresentationEquiv_symm_of i
  exact DFunLike.congr_fun h w

/-- **The polygon presentation with one generator per paired side.** For a locally finite
fundamental polygon, the reduced presentation is the actual acting group. -/
def sidePresentationEquivGroup {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.SidePresentation ≃* Γ :=
  σ.sidePresentationEquiv.symm.trans
    (MulEquiv.ofBijective _ (σ.relatorQuotientTo_bijective hmap hlf hdisj))

/-- The reduced presentation sends each retained generator to its side-pairing transformation. -/
@[simp]
theorem sidePresentationEquivGroup_of {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (i : σ.SideRepresentative) :
    σ.sidePresentationEquivGroup hmap hlf hdisj (PresentedGroup.of i) =
      σ.generatorsIn hmap i := by
  simp [sidePresentationEquivGroup]

/-- On a word in retained generators, the acting-group isomorphism evaluates those generators
at their side-pairing transformations. -/
@[simp]
theorem sidePresentationEquivGroup_mk {Γ : Subgroup PSL(2, ℝ)}
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (w : FreeGroup σ.SideRepresentative) :
    σ.sidePresentationEquivGroup hmap hlf hdisj (PresentedGroup.mk _ w) =
      FreeGroup.lift (fun i : σ.SideRepresentative ↦ σ.generatorsIn hmap i) w := by
  exact FreeGroup.lift_unique
    ((σ.sidePresentationEquivGroup hmap hlf hdisj).toMonoidHom.comp (PresentedGroup.mk _))
    (fun i ↦ σ.sidePresentationEquivGroup_of hmap hlf hdisj i)

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
