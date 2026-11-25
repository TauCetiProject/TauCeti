/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import Mathlib.Logic.Small.Defs
public import Mathlib.Basic.Countable.Small
public import TauCeti.ModelTheory.Basic

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

* `FirstOrder.Language.realize_smallPresentation`: an `L`-structure, reinterpreted along the
  inverse map, realizes the translation of a formula into the small presentation exactly when it
  realizes the formula. It is the case of `FirstOrder.Language.LEquiv.realize_onBoundedFormulaInf`
  for the small presentation.
-/

public section

universe u v u' v' uι uα w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable (L) [Countable (Σ n, L.Functions n)] [Countable (Σ n, L.Relations n)]

/-- The **small presentation** of a language with countably many function and relation symbols:
the language in `Language.{0, 0}` whose symbols of each arity are `Shrink.{0}` of those of `L`.
The definition is exposed so that the symbol maps of `smallPresentationEquiv` can be stated
through `equivShrink`. -/
@[expose] def smallPresentation : Language.{0, 0} where
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

/-- The equivalence sends a function symbol to its shrunk copy. -/
@[simp]
theorem smallPresentationEquiv_toLHom_onFunction {n : ℕ} (f : L.Functions n) :
    L.smallPresentationEquiv.toLHom.onFunction f = equivShrink.{0} (L.Functions n) f :=
  (rfl)

/-- The equivalence sends a relation symbol to its shrunk copy. -/
@[simp]
theorem smallPresentationEquiv_toLHom_onRelation {n : ℕ} (R : L.Relations n) :
    L.smallPresentationEquiv.toLHom.onRelation R = equivShrink.{0} (L.Relations n) R :=
  (rfl)

/-- The inverse equivalence sends a shrunk function symbol back. -/
@[simp]
theorem smallPresentationEquiv_invLHom_onFunction {n : ℕ}
    (f : L.smallPresentation.Functions n) :
    L.smallPresentationEquiv.invLHom.onFunction f = (equivShrink.{0} (L.Functions n)).symm f :=
  (rfl)

/-- The inverse equivalence sends a shrunk relation symbol back. -/
@[simp]
theorem smallPresentationEquiv_invLHom_onRelation {n : ℕ}
    (R : L.smallPresentation.Relations n) :
    L.smallPresentationEquiv.invLHom.onRelation R = (equivShrink.{0} (L.Relations n)).symm R :=
  (rfl)

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
