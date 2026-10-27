/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import Mathlib.Logic.Small.Defs
public import Mathlib.Basic.Countable.Small

/-!
# The small presentation of a countable language

A first-order language `L : Language.{u, v}` with countably many function symbols and countably
many relation symbols has a copy in `Language.{0, 0}`: its **small presentation**
`L.smallPresentation`, whose symbols of each arity are `Shrink.{0}` of those of `L`. The two are
equivalent languages, `L.smallPresentationEquiv : L ≃ᴸ L.smallPresentation`, built from
`equivShrink`. Function symbols are allowed.

Translating an infinitary formula along a language equivalence preserves its meaning: an
`L`-structure, reinterpreted along the inverse map, realizes the translated formula exactly when
it realizes the original. For the small presentation this moves any formula of a countable
language into `Language.{0, 0}`, where constructions that live in a fixed universe can run.

## Main definitions

* `FirstOrder.Language.smallPresentation`: the small presentation of a countable language.
* `FirstOrder.Language.smallPresentationEquiv`: its equivalence with the original language.

## Main results

* `FirstOrder.Language.LEquiv.realize_onBoundedFormulaInf`: realization is preserved by
  translation along a language equivalence, the target structure being the reduct along the
  inverse map.
* `FirstOrder.Language.realize_smallPresentation`: the case of the small presentation.

## References

* Follows the roadmap signatures of `TauCetiRoadmap/InfinitaryModelExistence/README.md`, §0.3.
-/

public section

universe u v u' v' uι uα w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-- A language with countably many function symbols has countably many of each arity. -/
instance countable_functions_of_countable_sigma [Countable (Σ n, L.Functions n)] (n : ℕ) :
    Countable (L.Functions n) :=
  (sigma_mk_injective (i := n)).countable

/-- A language with countably many relation symbols has countably many of each arity. -/
instance countable_relations_of_countable_sigma [Countable (Σ n, L.Relations n)] (n : ℕ) :
    Countable (L.Relations n) :=
  (sigma_mk_injective (i := n)).countable

namespace LEquiv

variable {L' : Language.{u', v'}} {ι : Type uι} {α : Type uα}

/-- **Realization along a language equivalence.** An `L`-structure, reinterpreted as an
`L'`-structure along the inverse map, realizes the translation of an infinitary formula exactly
when it realizes the formula. -/
theorem realize_onBoundedFormulaInf (e : L ≃ᴸ L') {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    letI := e.invLHom.reduct M
    (e.toLHom.onBoundedFormulaInf φ).Realize v xs ↔ φ.Realize v xs := by
  let := e.invLHom.reduct M
  -- translating back along the inverse map, an expansion of the reduct, gives `φ` again
  rw [← LHom.realize_onBoundedFormulaInf e.invLHom, ← LHom.comp_onBoundedFormulaInf, e.left_inv,
    LHom.id_onBoundedFormulaInf]

end LEquiv

variable (L) [Countable (Σ n, L.Functions n)] [Countable (Σ n, L.Relations n)]

/-- The **small presentation** of a language with countably many function and relation symbols:
the language in `Language.{0, 0}` whose symbols of each arity are `Shrink.{0}` of those of `L`. -/
def smallPresentation : Language.{0, 0} where
  Functions n := Shrink.{0} (L.Functions n)
  Relations n := Shrink.{0} (L.Relations n)

/-- The function symbols of the small presentation of each arity are those of `L`, shrunk. -/
theorem smallPresentation_functions (n : ℕ) :
    L.smallPresentation.Functions n = Shrink.{0} (L.Functions n) :=
  (rfl)

/-- The relation symbols of the small presentation of each arity are those of `L`, shrunk. -/
theorem smallPresentation_relations (n : ℕ) :
    L.smallPresentation.Relations n = Shrink.{0} (L.Relations n) :=
  (rfl)

/-- The equivalence of a countable language with its small presentation, built from
`equivShrink`. -/
noncomputable def smallPresentationEquiv : L ≃ᴸ L.smallPresentation where
  toLHom := ⟨fun {n} f => equivShrink.{0} (L.Functions n) f,
    fun {n} R => equivShrink.{0} (L.Relations n) R⟩
  invLHom := ⟨fun {n} f => (equivShrink.{0} (L.Functions n)).symm f,
    fun {n} R => (equivShrink.{0} (L.Relations n)).symm R⟩
  left_inv := LHom.funext
    (funext fun _ => funext fun f => (equivShrink.{0} _).symm_apply_apply f)
    (funext fun _ => funext fun R => (equivShrink.{0} _).symm_apply_apply R)
  right_inv := LHom.funext
    (funext fun _ => funext fun f => (equivShrink.{0} _).apply_symm_apply f)
    (funext fun _ => funext fun R => (equivShrink.{0} _).apply_symm_apply R)

/-- The small presentation of a relational language is relational. -/
instance isRelational_smallPresentation [L.IsRelational] : L.smallPresentation.IsRelational :=
  fun n => (equivShrink.{0} (L.Functions n)).symm.isEmpty

/-- The small presentation has countably many function symbols. -/
instance countable_functions_smallPresentation :
    Countable (Σ n, L.smallPresentation.Functions n) :=
  Countable.of_equiv _ (Equiv.sigmaCongrRight fun n => equivShrink.{0} (L.Functions n))

/-- The small presentation has countably many relation symbols. -/
instance countable_relations_smallPresentation :
    Countable (Σ n, L.smallPresentation.Relations n) :=
  Countable.of_equiv _ (Equiv.sigmaCongrRight fun n => equivShrink.{0} (L.Relations n))

/-- **Realization in the small presentation.** An `L`-structure, reinterpreted along the inverse
of `L.smallPresentationEquiv`, realizes the translation of an infinitary formula exactly when it
realizes the formula. -/
theorem realize_smallPresentation {ι : Type uι} {α : Type uα} {M : Type w} [L.Structure M]
    {n : ℕ} (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    letI := L.smallPresentationEquiv.invLHom.reduct M
    (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ).Realize v xs ↔ φ.Realize v xs :=
  L.smallPresentationEquiv.realize_onBoundedFormulaInf φ v xs

end Language

end FirstOrder
