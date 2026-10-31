/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.Enumeration
public import TauCeti.ModelTheory.ModelExistence.TermModel

/-!
# Model existence for consistency properties

A countable member of a consistency property over a countable language has a countable,
nonempty model in every universe, with every element named by a Henkin constant. The fair
enumeration supplies a Henkin-complete superset without contradictions; its quotient term model
satisfies the starting set by the two-polarity truth lemma. Moving this model to another universe
preserves both satisfaction and the surjectivity of the interpretations of the constants.

The limit need not itself belong to the consistency property. No decision clause or closure
under unions of increasing chains is used.

## Main results

* `FirstOrder.Language.ConsistencyProperty.limit_henkinComplete`: the limit of a surjective
  request schedule, starting from an enumerated member, is Henkin complete.
* `FirstOrder.Language.ConsistencyProperty.model_existence`: a countable member has a countable
  nonempty model, in any universe, whose elements are all named by Henkin constants.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, §4.1.
* H. J. Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.

This assembles the fair enumeration and quotient truth lemma of the imported modules; their
module docstrings record the relationship to Cameron Freer's `cameronfreer/infinitary-logic`.
-/

public section

universe u v w

namespace FirstOrder.Language.ConsistencyProperty

variable {L : FirstOrder.Language.{u, v}}

/-- The limit of a fair enumeration starting from a member of a consistency property is
Henkin complete. The enumeration of the starting set may include sentences outside it. -/
theorem limit_henkinComplete (C : ConsistencyProperty L) {s : L[[ℕ]].Theoryω}
    (hs : s ∈ C.sets) {e : ℕ → L[[ℕ]].Sentenceω} (he : s ⊆ Set.range e)
    {q : ℕ → Request L} (hq : Function.Surjective q) : HenkinComplete (C.limit s e q) where
  imp _ _ := C.limit_imp hs he hq
  not_imp _ _ := C.limit_not_imp hs he hq
  iInf _ := C.limit_iInf hs he hq
  not_iInf _ := C.limit_not_iInf hs he hq
  iSup _ := C.limit_iSup hs he hq
  not_iSup _ := C.limit_not_iSup hs he hq
  all _ := C.limit_all hs he hq
  not_all _ := C.limit_not_all hs he hq
  eq_refl := C.limit_eq_refl hs hq
  eq_subst _ _ _ := C.limit_eq_subst hs he hq
  eq_name := C.limit_eq_name hs hq

/-- **Model existence.** Every countable member of a consistency property over a language with
countably many function and relation symbols has a countable nonempty model in any universe.
Every element of the model is the interpretation of a Henkin constant. -/
theorem model_existence [Countable (Σ n, L.Functions n)] [Countable (Σ n, L.Relations n)]
    (C : ConsistencyProperty L) {s : L[[ℕ]].Theoryω} (hs : s ∈ C.sets) (hsc : s.Countable) :
    ∃ (M : Type w) (_ : L[[ℕ]].Structure M), Countable M ∧ Nonempty M ∧ s.Model M ∧
      Function.Surjective (fun c : ℕ => (L.con c : M)) := by
  obtain ⟨e, he⟩ := Set.countable_iff_exists_subset_range.1 hsc
  obtain ⟨q, hq⟩ := exists_surjective_nat (Request L)
  have hH := C.limit_henkinComplete hs he hq
  have hM : s.Model hH.TermModel :=
    (hH.model (C.bot_notMem_limit hs) (fun _ => C.not_notMem_limit hs)).mono C.subset_limit
  -- The term model lives in `Type`; lifting it realizes the arbitrary target universe.
  let eM : hH.TermModel ≃ ULift.{w} hH.TermModel := Equiv.ulift.symm
  let : L[[ℕ]].Structure (ULift.{w} hH.TermModel) := eM.inducedStructure
  let f : hH.TermModel ≃[L[[ℕ]]] ULift.{w} hH.TermModel := eM.inducedStructureEquiv
  refine ⟨ULift.{w} hH.TermModel, inferInstance, inferInstance, inferInstance,
    (StrongHomClass.theoryω_model_iff f s).1 hM, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := hH.con_surjective (f.symm x)
  refine ⟨c, ?_⟩
  exact (f.map_constants (L.con c)).symm.trans ((congrArg f hc).trans (f.apply_symm_apply x))

end FirstOrder.Language.ConsistencyProperty
