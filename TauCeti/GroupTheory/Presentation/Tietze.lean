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
  let f : PresentedGroup R →* PresentedGroup S :=
    QuotientGroup.map _ _ (FreeGroup.lift u)
      (Subgroup.normalClosure_le_normal fun r hr ↦ mk_eq_one_iff.mp (hu r hr))
  let g : PresentedGroup S →* PresentedGroup R :=
    QuotientGroup.map _ _ (FreeGroup.lift v)
      (Subgroup.normalClosure_le_normal fun s hs ↦ mk_eq_one_iff.mp (hv s hs))
  have hf (w : FreeGroup α) : f (mk R w) = mk S (FreeGroup.lift u w) := rfl
  have hg (w : FreeGroup β) : g (mk S w) = mk R (FreeGroup.lift v w) := rfl
  apply MonoidHom.toMulEquiv f g
  · apply PresentedGroup.ext
    intro a
    calc
      (g.comp f) (of a) = g (f (mk R (FreeGroup.of a))) := rfl
      _ = mk R (FreeGroup.lift v (u a)) := by rw [hf, FreeGroup.lift_apply_of, hg]
      _ = of a := hvu a
  · apply PresentedGroup.ext
    intro b
    calc
      (f.comp g) (of b) = f (g (mk S (FreeGroup.of b))) := rfl
      _ = mk S (FreeGroup.lift u (v b)) := by rw [hg, FreeGroup.lift_apply_of, hf]
      _ = of b := huv b

/-- On a free word, the forward isomorphism substitutes the forward generator words. -/
@[simp]
theorem equivOfGeneratorWords_mk (w : FreeGroup α) :
    equivOfGeneratorWords u v hu hv hvu huv (mk R w) = mk S (FreeGroup.lift u w) := by
  rfl

/-- The forward generator dictionary of a change of presentation. -/
@[simp]
theorem equivOfGeneratorWords_of (a : α) :
    equivOfGeneratorWords u v hu hv hvu huv (of a) = mk S (u a) := by
  rw [of, equivOfGeneratorWords_mk, FreeGroup.lift_apply_of]

/-- On a free word, the inverse isomorphism substitutes the recovery generator words. -/
@[simp]
theorem equivOfGeneratorWords_symm_mk (w : FreeGroup β) :
    (equivOfGeneratorWords u v hu hv hvu huv).symm (mk S w) = mk R (FreeGroup.lift v w) := by
  rfl

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
  let f : PresentedGroup S →* PresentedGroup Q :=
    toGroup (f := fun x ↦ ((mk Q).comp σ) (FreeGroup.of x)) (by
      have h : FreeGroup.lift (fun x ↦ ((mk Q).comp σ) (FreeGroup.of x)) =
          (mk Q).comp σ := by ext x; simp
      simpa only [h] using hf)
  let g : PresentedGroup Q →* PresentedGroup S :=
    toGroup (f := fun a ↦ ((mk S).comp ι) (FreeGroup.of a)) (by
      have h : FreeGroup.lift (fun a ↦ ((mk S).comp ι) (FreeGroup.of a)) =
          (mk S).comp ι := by ext a; simp
      simpa only [h] using hg)
  -- Compare the two composites on free words, then on the presented generators.
  have hfmk : f.comp (mk S) = (mk Q).comp σ := by
    apply FreeGroup.ext_hom
    intro x
    dsimp only [f, MonoidHom.comp_apply]
    rw [← of, toGroup.of]
  have hgmk : g.comp (mk Q) = (mk S).comp ι := by
    apply FreeGroup.ext_hom
    intro a
    dsimp only [g, MonoidHom.comp_apply]
    rw [← of, toGroup.of]
  apply MonoidHom.toMulEquiv f g
  · have h : (g.comp f).comp (mk S) = mk S := by
      rw [MonoidHom.comp_assoc, hfmk, ← MonoidHom.comp_assoc, hgmk, hισ]
    exact PresentedGroup.ext fun x ↦ DFunLike.congr_fun h (FreeGroup.of x)
  · have h : (f.comp g).comp (mk Q) = mk Q := by
      rw [MonoidHom.comp_assoc, hgmk, ← MonoidHom.comp_assoc, hfmk,
        MonoidHom.comp_assoc, hσι, MonoidHom.comp_id]
    exact PresentedGroup.ext fun a ↦ DFunLike.congr_fun h (FreeGroup.of a)

/-- A retained generator maps to the corresponding generator after elimination. -/
@[simp]
theorem eliminateGenerators_of_inl (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (a : α) : eliminateGenerators w R (of (Sum.inl a)) = of a := by
  simp [eliminateGenerators, MonoidHom.toMulEquiv]
  rfl

/-- An auxiliary generator maps to its defining word after elimination. -/
@[simp]
theorem eliminateGenerators_of_inr (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (b : β) : eliminateGenerators w R (of (Sum.inr b)) =
      mk (FreeGroup.lift (Sum.elim FreeGroup.of w) '' R) (w b) := by
  simp [eliminateGenerators, MonoidHom.toMulEquiv]

/-- The inverse of elimination includes the retained generators in the original presentation. -/
@[simp]
theorem eliminateGenerators_symm_of (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (a : α) : (eliminateGenerators w R).symm (of a) = of (Sum.inl a) := by
  simp [eliminateGenerators, MonoidHom.toMulEquiv]
  rfl

/-- On an arbitrary word, elimination evaluates the word after substituting the definitions. -/
@[simp]
theorem eliminateGenerators_mk (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (r : FreeGroup (α ⊕ β)) :
    eliminateGenerators w R (mk _ r) =
      mk _ (FreeGroup.lift (Sum.elim FreeGroup.of w) r) := by
  have h : (eliminateGenerators w R).toMonoidHom.comp (mk _) =
      (mk _).comp (FreeGroup.lift (Sum.elim FreeGroup.of w)) := by
    apply FreeGroup.ext_hom
    rintro (a | b)
    · simpa [of] using eliminateGenerators_of_inl w R a
    · simpa [of] using eliminateGenerators_of_inr w R b
  exact DFunLike.congr_fun h r

/-- On an arbitrary word in the retained generators, the inverse is induced by inclusion. -/
@[simp]
theorem eliminateGenerators_symm_mk (w : β → FreeGroup α) (R : Set (FreeGroup (α ⊕ β)))
    (r : FreeGroup α) :
    (eliminateGenerators w R).symm (mk _ r) = mk _ (FreeGroup.map Sum.inl r) := by
  have h : (eliminateGenerators w R).symm.toMonoidHom.comp (mk _) =
      (mk _).comp (FreeGroup.map Sum.inl) := by
    apply FreeGroup.ext_hom
    intro a
    simpa [of] using eliminateGenerators_symm_of w R a
  exact DFunLike.congr_fun h r

end PresentedGroup
