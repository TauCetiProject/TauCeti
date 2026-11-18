/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.Sublanguage

/-!
# Regression examples: expanding structures of symbol sublanguages

These examples exercise `expandSymbStructure` from a downstream module, through public statements
only:

* on a nonempty carrier, a structure of a symbol sublanguage expands to an `L`-structure along
  which the inclusion is an expansion, and an `L`-formula whose symbols lie in the sublanguage has
  the same truth value in the expansion as its restriction has in the sublanguage structure;
* for a relational language no element is needed: the same holds on every carrier, including the
  empty type.
-/

universe u v w

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}

-- On a nonempty carrier, a formula with symbols in the sublanguage keeps its truth value in the
-- expansion.
example {M : Type w} [Nonempty M] [(symbSublang F R).Structure M] {n : ℕ}
    (φ : L.BoundedFormulaω Empty n) (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R)
    (xs : Fin n → M) :
    letI := expandSymbStructure F R M
    φ.Realize Empty.elim xs ↔ (φ.restrictSymbols hF hR).Realize Empty.elim xs := by
  let := expandSymbStructure F R M
  exact (BoundedFormulaInf.realize_restrictSymbols φ hF hR _ xs).symm

-- For a relational language the carrier may be empty.
example [L.IsRelational] [(symbSublang F R).Structure Empty] :
    letI := expandSymbStructure F R Empty
    (symbSublangIncl F R).IsExpansionOn Empty :=
  inferInstance

-- For a relational language, truth transfers to the expansion on an arbitrary carrier.
example [L.IsRelational] {M : Type w} [(symbSublang F R).Structure M] (φ : L.Sentenceω)
    (hF : φ.functionsIn ⊆ F) (hR : φ.relationsIn ⊆ R) :
    letI := expandSymbStructure F R M
    SentenceInf.Realize φ M ↔ SentenceInf.Realize (φ.restrictSymbols hF hR) M := by
  let := expandSymbStructure F R M
  simp only [SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_restrictSymbols]
