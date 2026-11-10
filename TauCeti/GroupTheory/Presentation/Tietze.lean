/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup

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

## References

* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Chapter II, §2
  (Tietze transformations).
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

end PresentedGroup
