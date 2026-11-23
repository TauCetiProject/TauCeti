/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Multiplier

/-!
# Basic double centralizer lemmas

Minimal extensionality lemma `DoubleCentralizer.ext_fst_snd` for multiplier algebras.
-/

public section

open scoped MultiplierAlgebra

namespace DoubleCentralizer

/-- Two multipliers are equal if their left and right centralizers agree pointwise. -/
theorem ext_fst_snd {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] {m n : 𝓜(𝕜, A)}
    (h₁ : ∀ a, m.fst a = n.fst a) (h₂ : ∀ a, m.snd a = n.snd a) : m = n :=
  DoubleCentralizer.ext _ _ _ _ <|
    Prod.ext (ContinuousLinearMap.ext h₁) (ContinuousLinearMap.ext h₂)

end DoubleCentralizer
