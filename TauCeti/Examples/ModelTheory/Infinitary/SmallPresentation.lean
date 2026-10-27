/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.SmallPresentation

/-!
# Regression examples: small presentations

These examples exercise the small presentation from a downstream module, through public
statements only, for a language in the universes `(1, 1)` with a unary function symbol and a
binary relation symbol for every natural number:

* its small presentation is a language in `Language.{0, 0}` with countably many symbols;
* a sentence keeps its meaning in the small presentation: an `L`-structure, reinterpreted along
  the inverse map, satisfies the translation of `∀ x, R₀ (f₀ x) x` exactly when it satisfies the
  sentence, so function symbols are transported too;
* the small presentation of a relational language is relational.
-/

universe w

open FirstOrder FirstOrder.Language

-- The small presentation lives in `Language.{0, 0}` and has countably many relation symbols.
example : Countable (Σ n, (Language.mk.{1, 1} (fun _ => ULift.{1} ℕ) fun _ =>
    ULift.{1} ℕ).smallPresentation.Relations n) :=
  inferInstance

-- A sentence with a function symbol keeps its meaning in the small presentation.
example {M : Type w}
    [(Language.mk.{1, 1} (fun _ => ULift.{1} ℕ) fun _ => ULift.{1} ℕ).Structure M] :
    let L := Language.mk.{1, 1} (fun _ => ULift.{1} ℕ) fun _ => ULift.{1} ℕ
    let φ : L.BoundedFormulaω Empty 0 :=
      (BoundedFormulaInf.rel (l := 2) (⟨0⟩ : ULift.{1} ℕ)
        ![Term.func (l := 1) (⟨0⟩ : ULift.{1} ℕ) ![Term.var (Sum.inr 0)],
          Term.var (Sum.inr 0)]).all
    letI := L.smallPresentationEquiv.invLHom.reduct M
    (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ).Realize (Empty.elim : Empty → M)
        (default : Fin 0 → M) ↔
      φ.Realize (Empty.elim : Empty → M) (default : Fin 0 → M) :=
  realize_smallPresentation _ _ _ _

-- The small presentation of a relational language is relational.
example :
    (Language.mk.{1, 1} (fun _ => ULift.{1} Empty) fun _ =>
      ULift.{1} ℕ).smallPresentation.IsRelational :=
  inferInstance
