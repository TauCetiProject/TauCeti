/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Classes
public import TauCeti.ModelTheory.Infinitary.SmallPresentation
public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap

/-!
# Counting countable models along a language equivalence

The number of countable models of a sentence, and the existence of a perfect set of pairwise
non-isomorphic ones, do not depend on how the language is presented. A language equivalence
`e : L ≃ᴸ L'` of relational languages transports configurations by a homeomorphism
(`FirstOrder.Language.LEquiv.onConfiguration`) on every carrier, which preserves and reflects
isomorphism and carries the model class of a sentence `φ` onto the model class of its translation
`e.toLHom.onBoundedFormulaInf φ`. Hence:

* `FirstOrder.Language.LEquiv.countableModelClassesEquiv`: the isomorphism classes of the
  countable models of `φ` correspond, tier by tier, to those of its translation; a countable model
  is sent to the same structure read along `e` (`countableModelClassesEquiv_classOf`);
* `FirstOrder.Language.LEquiv.lift_countableModelCount_onBoundedFormulaInf`: the two counts agree,
  after lifting to a common universe;
* `FirstOrder.Language.LEquiv.hasPerfectlyManyCountableModels_onBoundedFormulaInf_iff`: one
  sentence has perfectly many countable models exactly when the other does.

With the small presentation `L.smallPresentationEquiv`, every sentence of a relational language
with countably many relation symbols has a counterpart over a relational language in
`Language.{0, 0}` with countably many relation symbols, with the same number of countable models
and the same perfect-set alternative (`TauCeti.exists_language_zero_countableModelCount`).
Statements quantifying over countable languages can therefore be made over `Language.{0, 0}`
without loss; models in other universes are handled by `TauCeti.classOf`.

## Main results

* `FirstOrder.Language.LEquiv.lift_countableModelCount_onBoundedFormulaInf`
* `FirstOrder.Language.LEquiv.hasPerfectlyManyCountableModels_onBoundedFormulaInf_iff`
* `TauCeti.exists_language_zero_countableModelCount`
-/

public section

universe u v u' v' w uι

open TauCeti TauCeti.RelationalConfiguration Cardinal

namespace FirstOrder.Language.LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (e : L ≃ᴸ L') {ι : Type uι}

/-- Transport along `e` identifies the isomorphism classes of the models of `φ` on `V` with those
of the models of its translation on `V`. -/
noncomputable def quotientIsoSetoidOnEquiv (V : Type w) (φ : L.SentenceInf ι) :
    Quotient (isoSetoidOn V φ) ≃ Quotient (isoSetoidOn V (e.toLHom.onBoundedFormulaInf φ)) :=
  Quotient.congr
    (e.onConfiguration.toEquiv.subtypeEquiv fun c => by
      rw [← Set.mem_preimage, Homeomorph.coe_toEquiv, preimage_onConfiguration_modelsOf])
    fun _ _ => e.isoSetoid_onConfiguration_iff.symm

/-- The class of a model `c` of `φ` is sent to the class of its transport along `e`. -/
@[simp]
theorem quotientIsoSetoidOnEquiv_mk {V : Type w} {φ : L.SentenceInf ι} (c : modelsOf (V := V) φ) :
    e.quotientIsoSetoidOnEquiv V φ ⟦c⟧ =
      ⟦⟨e.onConfiguration c, by rw [← image_onConfiguration_modelsOf]; exact ⟨c, c.2, rfl⟩⟩⟧ :=
  (rfl)

/-- Transport along `e` identifies the isomorphism classes of the countable models of `φ`, tier by
tier, with those of its translation. -/
noncomputable def countableModelClassesEquiv (φ : L.SentenceInf ι) :
    CountableModelClasses φ ≃ CountableModelClasses (e.toLHom.onBoundedFormulaInf φ) :=
  (e.quotientIsoSetoidOnEquiv ℕ φ).sumCongr
    (Equiv.sigmaCongrRight fun n => e.quotientIsoSetoidOnEquiv (Fin n) φ)

/-- On the tier `ℕ`, `countableModelClassesEquiv` is transport of classes along `e`. -/
@[simp]
theorem countableModelClassesEquiv_inl {φ : L.SentenceInf ι} (q : Quotient (isoSetoidOn ℕ φ)) :
    e.countableModelClassesEquiv φ (.inl q) = .inl (e.quotientIsoSetoidOnEquiv ℕ φ q) :=
  (rfl)

/-- On the tier `Fin n`, `countableModelClassesEquiv` is transport of classes along `e`. -/
@[simp]
theorem countableModelClassesEquiv_inr {φ : L.SentenceInf ι} {n : ℕ}
    (q : Quotient (isoSetoidOn (Fin n) φ)) :
    e.countableModelClassesEquiv φ (.inr ⟨n, q⟩) =
      .inr ⟨n, e.quotientIsoSetoidOnEquiv (Fin n) φ q⟩ :=
  (rfl)

/-- `countableModelClassesEquiv` sends the class of a countable model `M` of `φ` to the class of
`M` read as an `L'`-structure along `e`, a model of the translation of `φ`. -/
theorem countableModelClassesEquiv_classOf {φ : L.SentenceInf ι} {M : Type w} [L.Structure M]
    [Countable M] (hM : φ.Realize M)
    (hM' : @SentenceInf.Realize L' ι (e.toLHom.onBoundedFormulaInf φ) M (e.invLHom.reduct M)) :
    e.countableModelClassesEquiv φ (classOf φ hM) =
      @classOf L' _ ι _ M (e.invLHom.reduct M) _ hM' := by
  let := e.invLHom.reduct M
  -- Transport along `e` of the encoding of `M` is the encoding of `M` read along `e`.
  have hcode {V : Type} (f : M ≃ V) :
      e.onConfiguration (f.encodeVia (L := L)) = f.encodeVia (L := L') := by
    rw [coe_onConfiguration, e.invLHom.reductConfiguration_encodeVia f]
  rcases finite_or_infinite M with _ | _
  · rw [classOf_eq_inr hM (Finite.equivFin M), classOf_eq_inr hM' (Finite.equivFin M),
      countableModelClassesEquiv_inr, quotientIsoSetoidOnEquiv_mk]
    simp_rw [hcode]
  · let f : M ≃ ℕ := nonempty_equiv_of_countable.some
    rw [classOf_eq_inl hM f, classOf_eq_inl hM' f, countableModelClassesEquiv_inl,
      quotientIsoSetoidOnEquiv_mk]
    simp_rw [hcode]

/-- **Counting along a language equivalence.** A sentence and its translation along a language
equivalence of relational languages have the same number of countable models, after lifting both
counts to a common universe. -/
theorem lift_countableModelCount_onBoundedFormulaInf (φ : L.SentenceInf ι) :
    lift.{v'} (countableModelCount φ) =
      lift.{v} (countableModelCount (e.toLHom.onBoundedFormulaInf φ)) := by
  rw [countableModelCount_def, countableModelCount_def]
  exact lift_mk_eq'.2 ⟨e.countableModelClassesEquiv φ⟩

/-- **Perfect sets along a language equivalence.** The translation of a sentence along a language
equivalence of relational languages has perfectly many countable models exactly when the sentence
does. -/
theorem hasPerfectlyManyCountableModels_onBoundedFormulaInf_iff (φ : L.SentenceInf ι) :
    HasPerfectlyManyCountableModels (e.toLHom.onBoundedFormulaInf φ) ↔
      HasPerfectlyManyCountableModels φ := by
  simp only [hasPerfectlyManyCountableModels_iff, ← image_onConfiguration_modelsOf,
    Setoid.hasPerfectAntichainOn_image_homeomorph_iff _
      (fun _ _ => e.isoSetoid_onConfiguration_iff)]

end FirstOrder.Language.LEquiv

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ n, L.Relations n)] {ι : Type uι}

/-- **Presentation in universe `0`.** A sentence of a relational language with countably many
relation symbols has a counterpart over a relational language in `Language.{0, 0}` with countably
many relation symbols, with the same number of countable models (after lifting) and perfectly many
countable models exactly when the original has. The counterpart is the translation into the small
presentation of the language. -/
theorem exists_language_zero_countableModelCount (φ : L.SentenceInf ι) :
    ∃ (L₀ : Language.{0, 0}) (_ : L₀.IsRelational) (_ : Countable (Σ n, L₀.Relations n))
      (φ₀ : L₀.SentenceInf ι),
      lift.{0} (countableModelCount φ) = lift.{v} (countableModelCount φ₀) ∧
        (HasPerfectlyManyCountableModels φ₀ ↔ HasPerfectlyManyCountableModels φ) :=
  ⟨L.smallPresentation, inferInstance, inferInstance,
    L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ,
    L.smallPresentationEquiv.lift_countableModelCount_onBoundedFormulaInf φ,
    L.smallPresentationEquiv.hasPerfectlyManyCountableModels_onBoundedFormulaInf_iff φ⟩

end TauCeti
