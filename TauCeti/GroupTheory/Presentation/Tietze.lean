/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Basic
public import TauCeti.GroupTheory.PresentedGroup

/-!
# Changing generators of a group presentation

Suppose auxiliary generators `b : β` have definitions `b = w b`, where each `w b` is a word
in the retained generators `α`. Substituting those words in every other relator gives an
isomorphic presented group. The other relators may involve both kinds of generators.

`PresentedGroup.eliminateGenerators` implements this Tietze transformation for an arbitrary
family of auxiliary generators. Its generator equations specify both directions of the
isomorphism, so it can be composed with presentation dictionaries without choosing an
unspecified isomorphism. Neither generator type nor the relator set needs to be finite.

`PresentedGroup.equivOfGeneratorWords` handles a general change of generators: forward and
recovery words must preserve the relations and recover each generator modulo the original
relations. The words need not be inverse substitutions in the free groups. Its evaluation
lemmas retain both dictionaries on arbitrary words, not merely an unspecified isomorphism.

`PresentedGroup.adjoinGenerators` is the converse move for relators in the old generators: new
generators with defining words in the old generators may be added to any presentation.
`PresentedGroup.splitRelator` replaces a relator `u * v` by the two relators `u * d` and
`d⁻¹ * v` for a new generator `d`. This is the presentation counterpart of cutting a polygonal
face with boundary word `u v` into the faces `u d` and `d⁻¹ v` along a new side `d`.

## References

* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Chapter II, §2
  (Tietze transformations).
* J. Gallier and D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*,
  Chapter 6, Definition 6.3, operation (P2) (cutting a face along a new edge).
-/

public section

namespace PresentedGroup

variable {α β : Type*}

private def generatorWordHom {R : Set (FreeGroup α)} {S : Set (FreeGroup β)}
    (u : α → FreeGroup β) (hu : ∀ r ∈ R, mk S (FreeGroup.lift u r) = 1) :
    PresentedGroup R →* PresentedGroup S :=
  QuotientGroup.map _ _ (FreeGroup.lift u)
    (Subgroup.normalClosure_le_normal fun r hr ↦ mk_eq_one_iff.mp (hu r hr))

private theorem generatorWordHom_mk {R : Set (FreeGroup α)} {S : Set (FreeGroup β)}
    (u : α → FreeGroup β) (hu : ∀ r ∈ R, mk S (FreeGroup.lift u r) = 1)
    (w : FreeGroup α) : generatorWordHom u hu (mk R w) = mk S (FreeGroup.lift u w) :=
  QuotientGroup.map_mk _ _ _ _ w

section GeneratorWords

variable {R : Set (FreeGroup α)} {S : Set (FreeGroup β)}
  (u : α → FreeGroup β) (v : β → FreeGroup α)
  (hu : ∀ r ∈ R, mk S (FreeGroup.lift u r) = 1)
  (hv : ∀ s ∈ S, mk R (FreeGroup.lift v s) = 1)
  (hvu : ∀ a, mk R (FreeGroup.lift v (u a)) = of a)
  (huv : ∀ b, mk S (FreeGroup.lift u (v b)) = of b)

/-- **A change of generators specified by forward and recovery words.** If both word
substitutions preserve the defining relations and the two composite substitutions recover
every generator in its presented group, they induce inverse group isomorphisms.

All four checks take place modulo the actual defining relations. Recovery only in a finite
image is insufficient, while equality of the substitutions in the free groups is unnecessary.
Neither the generator types nor the relation sets need to be finite. -/
def equivOfGeneratorWords : PresentedGroup R ≃* PresentedGroup S := by
  let f := generatorWordHom u hu
  let g := generatorWordHom v hv
  have hf (w : FreeGroup α) : f (mk R w) = mk S (FreeGroup.lift u w) :=
    generatorWordHom_mk u hu w
  have hg (w : FreeGroup β) : g (mk S w) = mk R (FreeGroup.lift v w) :=
    generatorWordHom_mk v hv w
  apply MonoidHom.toMulEquiv f g
  · apply PresentedGroup.ext
    intro a
    calc
      (g.comp f) (of a) = g (f (mk R (FreeGroup.of a))) := by
        rw [MonoidHom.comp_apply, of]
      _ = mk R (FreeGroup.lift v (u a)) := by rw [hf, FreeGroup.lift_apply_of, hg]
      _ = of a := hvu a
  · apply PresentedGroup.ext
    intro b
    calc
      (f.comp g) (of b) = f (g (mk S (FreeGroup.of b))) := by
        rw [MonoidHom.comp_apply, of]
      _ = mk S (FreeGroup.lift u (v b)) := by rw [hg, FreeGroup.lift_apply_of, hf]
      _ = of b := huv b

/-- On a free word, the forward isomorphism substitutes the forward generator words. -/
@[simp]
theorem equivOfGeneratorWords_mk (w : FreeGroup α) :
    equivOfGeneratorWords u v hu hv hvu huv (mk R w) = mk S (FreeGroup.lift u w) := by
  rw [equivOfGeneratorWords, MonoidHom.toMulEquiv_apply, generatorWordHom_mk]

/-- The forward generator dictionary of a change of presentation. -/
@[simp]
theorem equivOfGeneratorWords_of (a : α) :
    equivOfGeneratorWords u v hu hv hvu huv (of a) = mk S (u a) := by
  rw [of, equivOfGeneratorWords_mk, FreeGroup.lift_apply_of]

/-- On a free word, the inverse isomorphism substitutes the recovery generator words. -/
@[simp]
theorem equivOfGeneratorWords_symm_mk (w : FreeGroup β) :
    (equivOfGeneratorWords u v hu hv hvu huv).symm (mk S w) = mk R (FreeGroup.lift v w) := by
  rw [equivOfGeneratorWords, MonoidHom.toMulEquiv_symm_apply, generatorWordHom_mk]

/-- The recovery generator dictionary of a change of presentation. -/
@[simp]
theorem equivOfGeneratorWords_symm_of (b : β) :
    (equivOfGeneratorWords u v hu hv hvu huv).symm (of b) = mk R (v b) := by
  rw [of, equivOfGeneratorWords_symm_mk, FreeGroup.lift_apply_of]

end GeneratorWords

/-- Eliminate auxiliary generators with defining words in the retained generators.

The source presentation has generators `α ⊕ β`, the defining relators
`b * (w b)⁻¹`, and arbitrary additional relators `R`. The target has generators `α`
and the relators obtained from `R` by substituting `w b` for every auxiliary generator.
The forward map performs that substitution; the inverse includes the retained generators. -/
def eliminateGenerators (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β))) :
    PresentedGroup
      (Set.range (fun b ↦ FreeGroup.of (Sum.inr b) * (FreeGroup.map Sum.inl (w b))⁻¹) ∪ R) ≃*
    PresentedGroup (FreeGroup.lift (Sum.elim FreeGroup.of w) '' R) := by
  let σ : FreeGroup (α ⊕ β) →* FreeGroup α := FreeGroup.lift (Sum.elim FreeGroup.of w)
  let ι : FreeGroup α →* FreeGroup (α ⊕ β) := FreeGroup.map Sum.inl
  let S := Set.range (fun b ↦ FreeGroup.of (Sum.inr b) * (ι (w b))⁻¹) ∪ R
  let Q := σ '' R
  have hσι : σ.comp ι = MonoidHom.id _ := by
    ext a
    simp [σ, ι]
  have hdef (b : β) : mk S (FreeGroup.of (Sum.inr b)) = mk S (ι (w b)) :=
    mk_eq_mk_of_mul_inv_mem (Or.inl ⟨b, rfl⟩)
  -- In the source quotient, inclusion after substitution is the identity on every word.
  have hισ : ((mk S).comp ι).comp σ = mk S := by
    ext x
    cases x with
    | inl a => simp [σ, ι]
    | inr b => simpa [σ] using (hdef b).symm
  have hf : ∀ r ∈ S, ((mk Q).comp σ) r = 1 := by
    intro r hr
    rcases hr with ⟨b, rfl⟩ | hr
    · simp only [MonoidHom.comp_apply, map_mul, map_inv]
      have hw : σ (ι (w b)) = w b := DFunLike.congr_fun hσι (w b)
      simp [σ, hw]
    · exact one_of_mem ⟨r, hr, rfl⟩
  have hg : ∀ r ∈ Q, ((mk S).comp ι) r = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← MonoidHom.comp_apply, hισ]
    exact one_of_mem (Or.inr hr)
  have hι : FreeGroup.lift (fun a ↦ FreeGroup.of (Sum.inl a)) = ι :=
    FreeGroup.map_eq_lift.symm
  refine equivOfGeneratorWords (Sum.elim FreeGroup.of w) (fun a ↦ FreeGroup.of (Sum.inl a))
    hf ?_ ?_ ?_
  · simpa only [hι, MonoidHom.comp_apply] using hg
  · intro x
    simpa only [hι, MonoidHom.comp_apply, σ, FreeGroup.lift_apply_of, of]
      using DFunLike.congr_fun hισ (FreeGroup.of x)
  · intro a
    simp [of]

/-- A retained generator maps to the corresponding generator after elimination. -/
@[simp]
theorem eliminateGenerators_of_inl (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (a : α) : eliminateGenerators w R (of (Sum.inl a)) = of a := by
  dsimp only [eliminateGenerators]
  apply equivOfGeneratorWords_of

/-- An auxiliary generator maps to its defining word after elimination. -/
@[simp]
theorem eliminateGenerators_of_inr (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (b : β) : eliminateGenerators w R (of (Sum.inr b)) =
      mk (FreeGroup.lift (Sum.elim FreeGroup.of w) '' R) (w b) := by
  dsimp only [eliminateGenerators]
  apply equivOfGeneratorWords_of

/-- The inverse of elimination includes the retained generators in the original presentation. -/
@[simp]
theorem eliminateGenerators_symm_of (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (a : α) : (eliminateGenerators w R).symm (of a) = of (Sum.inl a) := by
  dsimp only [eliminateGenerators]
  apply equivOfGeneratorWords_symm_of

/-- On an arbitrary word, elimination evaluates the word after substituting the definitions. -/
@[simp]
theorem eliminateGenerators_mk (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (r : FreeGroup (α ⊕ β)) :
    eliminateGenerators w R (mk _ r) =
      mk _ (FreeGroup.lift (Sum.elim FreeGroup.of w) r) := by
  dsimp only [eliminateGenerators]
  apply equivOfGeneratorWords_mk

/-- On an arbitrary word in the retained generators, the inverse is induced by inclusion. -/
@[simp]
theorem eliminateGenerators_symm_mk (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (r : FreeGroup α) :
    (eliminateGenerators w R).symm (mk _ r) = mk _ (FreeGroup.map Sum.inl r) := by
  conv_rhs => arg 2; rw [FreeGroup.map_eq_lift]
  dsimp only [eliminateGenerators]
  apply equivOfGeneratorWords_symm_mk

section AdjoinGenerators

variable (w : β → FreeGroup α) (R : Set (FreeGroup α))

/-- **Adjoining generators defined by words.** New generators `b : β`, each with a defining
relator `b * (w b)⁻¹` for a word `w b` in the old generators `α`, do not change the group
presented by relators `R` in the old generators.

The forward map includes the old generators; the inverse substitutes `w b` for each new
generator `b`. This is the inverse of
`PresentedGroup.eliminateGenerators w (FreeGroup.map Sum.inl '' R)`, after identifying its
substituted relators `FreeGroup.lift (Sum.elim FreeGroup.of w) '' (FreeGroup.map Sum.inl '' R)`
with `R`. -/
def adjoinGenerators : PresentedGroup R ≃* PresentedGroup
    (Set.range (fun b ↦ FreeGroup.of (Sum.inr b) * (FreeGroup.map Sum.inl (w b))⁻¹) ∪
      FreeGroup.map Sum.inl '' R) :=
  (equivOfNormalClosureEq (congrArg _ (FreeGroup.lift_sumElim_image_map_inl w R).symm)).trans
    (eliminateGenerators w (FreeGroup.map Sum.inl '' R)).symm

/-- On a word in the old generators, adjoining generators is induced by inclusion. -/
@[simp]
theorem adjoinGenerators_mk (r : FreeGroup α) :
    adjoinGenerators w R (mk R r) = mk _ (FreeGroup.map Sum.inl r) := by
  simp [adjoinGenerators]

/-- An old generator maps to the same generator after adjoining generators. -/
@[simp]
theorem adjoinGenerators_of (a : α) : adjoinGenerators w R (of a) = of (Sum.inl a) := by
  simp [of]

/-- On an arbitrary word, the inverse substitutes the defining words of the new generators. -/
@[simp]
theorem adjoinGenerators_symm_mk (r : FreeGroup (α ⊕ β)) :
    (adjoinGenerators w R).symm (mk _ r) = mk R (FreeGroup.lift (Sum.elim FreeGroup.of w) r) := by
  simp [adjoinGenerators]

/-- The inverse of adjoining generators sends an old generator to itself. -/
@[simp]
theorem adjoinGenerators_symm_of_inl (a : α) :
    (adjoinGenerators w R).symm (of (Sum.inl a)) = of a := by
  simp [of]

/-- The inverse of adjoining generators sends a new generator to its defining word. -/
@[simp]
theorem adjoinGenerators_symm_of_inr (b : β) :
    (adjoinGenerators w R).symm (of (Sum.inr b)) = mk R (w b) := by
  simp [of]

end AdjoinGenerators

section SplitRelator

variable (R : Set (FreeGroup α)) (u v : FreeGroup α)

private theorem normalClosure_adjoin_eq_split : Subgroup.normalClosure
        (Set.range (fun _ : Unit ↦ FreeGroup.of (Sum.inr ()) * (FreeGroup.map Sum.inl v)⁻¹) ∪
          FreeGroup.map Sum.inl '' insert (u * v) R) =
      Subgroup.normalClosure ({FreeGroup.map Sum.inl u * FreeGroup.of (Sum.inr () : α ⊕ Unit),
          (FreeGroup.of (Sum.inr () : α ⊕ Unit))⁻¹ * FreeGroup.map Sum.inl v} ∪
        FreeGroup.map Sum.inl '' R) := by
  set d : FreeGroup (α ⊕ Unit) := FreeGroup.of (Sum.inr ())
  set ι : FreeGroup α →* FreeGroup (α ⊕ Unit) := FreeGroup.map Sum.inl
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalClosure_le_normal ?_)
  · -- In the split presentation `d = v` and `u * d = 1`, hence `u * v = 1`.
    have hd : mk ({ι u * d, d⁻¹ * ι v} ∪ ι '' R) d = mk _ (ι v) :=
      mk_eq_mk_of_inv_mul_mem (Or.inl (Or.inr rfl))
    have hu : mk ({ι u * d, d⁻¹ * ι v} ∪ ι '' R) (ι u) * mk _ d = 1 := by
      rw [← map_mul]
      exact one_of_mem (Or.inl (Or.inl rfl))
    rintro _ (⟨_, rfl⟩ | ⟨r, rfl | hr, rfl⟩)
    · rw [SetLike.mem_coe, ← mk_eq_one_iff, map_mul, map_inv, hd, mul_inv_cancel]
    · rw [SetLike.mem_coe, ← mk_eq_one_iff, map_mul ι, map_mul, ← hd, hu]
    · exact Subgroup.subset_normalClosure (Or.inr ⟨r, hr, rfl⟩)
  · -- After adjoining `d` with defining word `v`, `d = v` and `u * v = 1`.
    have hd : mk (Set.range (fun _ : Unit ↦ d * (ι v)⁻¹) ∪ ι '' insert (u * v) R) d =
        mk _ (ι v) :=
      mk_eq_mk_of_mul_inv_mem (Or.inl ⟨(), rfl⟩)
    have huv : mk (Set.range (fun _ : Unit ↦ d * (ι v)⁻¹) ∪ ι '' insert (u * v) R) (ι u) *
        mk _ (ι v) = 1 := by
      rw [← map_mul, ← map_mul]
      exact one_of_mem (Or.inr ⟨_, Set.mem_insert _ _, rfl⟩)
    rintro _ ((rfl | rfl) | ⟨r, hr, rfl⟩)
    · rw [SetLike.mem_coe, ← mk_eq_one_iff, map_mul, hd, huv]
    · rw [SetLike.mem_coe, ← mk_eq_one_iff, map_mul, map_inv, hd, inv_mul_cancel]
    · exact Subgroup.subset_normalClosure (Or.inr ⟨r, Set.mem_insert_of_mem _ hr, rfl⟩)

/-- **Splitting a relator along a fresh generator.** Replacing a relator `u * v` by the two
relators `u * d` and `d⁻¹ * v`, where `d` is a new generator, does not change the presented
group. Geometrically, a face with boundary word `u v` is cut into the two faces `u d` and
`d⁻¹ v` along a new side `d`.

The forward map includes the old generators; the inverse sends `d` to `v`. -/
def splitRelator : PresentedGroup (insert (u * v) R) ≃* PresentedGroup
    ({FreeGroup.map Sum.inl u * FreeGroup.of (Sum.inr () : α ⊕ Unit),
        (FreeGroup.of (Sum.inr () : α ⊕ Unit))⁻¹ * FreeGroup.map Sum.inl v} ∪
      FreeGroup.map Sum.inl '' R) :=
  -- Adjoin `d` with defining word `v`, then exchange `u * v`, `d * v⁻¹` for `u * d`, `d⁻¹ * v`.
  (adjoinGenerators (fun _ ↦ v) _).trans
    (equivOfNormalClosureEq (normalClosure_adjoin_eq_split R u v))

/-- On a word in the old generators, splitting a relator is induced by inclusion. -/
@[simp]
theorem splitRelator_mk (r : FreeGroup α) :
    splitRelator R u v (mk _ r) = mk _ (FreeGroup.map Sum.inl r) := by
  simp [splitRelator]

/-- An old generator maps to the same generator after splitting a relator. -/
@[simp]
theorem splitRelator_of (a : α) : splitRelator R u v (of a) = of (Sum.inl a) := by
  simp [of]

/-- On an arbitrary word, the inverse of splitting a relator substitutes `v` for the new
generator. -/
@[simp]
theorem splitRelator_symm_mk (r : FreeGroup (α ⊕ Unit)) : (splitRelator R u v).symm (mk _ r) =
    mk _ (FreeGroup.lift (Sum.elim FreeGroup.of fun _ ↦ v) r) := by
  simp [splitRelator]

/-- The inverse of splitting a relator sends an old generator to itself. -/
@[simp]
theorem splitRelator_symm_of_inl (a : α) : (splitRelator R u v).symm (of (Sum.inl a)) = of a := by
  simp [of]

/-- The inverse of splitting a relator sends the new generator to `v`. -/
@[simp]
theorem splitRelator_symm_of_inr (x : Unit) :
    (splitRelator R u v).symm (of (Sum.inr x)) = mk _ v := by
  simp [of]

end SplitRelator

end PresentedGroup
