/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.RingTheory.Idempotents.Clopen.RankModule

/-!
# Prescribed-rank finitely generated projective modules

For a commutative ring `R`, this file packages `TauCeti.ClopenRankModule R f` attached to a
locally constant `ℕ`-valued rank function as an object of
`(TauCeti.finiteProjectiveModules R).FullSubcategory`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.clopenRankObj`: `TauCeti.ClopenRankModule R f` as an object of
  `(TauCeti.finiteProjectiveModules R).FullSubcategory`.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.FiniteProjectiveModules

variable (R : Type u) [CommRing R]

/-- `ClopenRankModule R f` as an object of `(finiteProjectiveModules R).FullSubcategory`. -/
noncomputable def clopenRankObj (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (ClopenRankModule R f),
    finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩

/-- `(clopenRankObj R f).obj` is `ModuleCat.of R (ClopenRankModule R f)`. -/
@[simp]
theorem clopenRankObj_obj (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    (clopenRankObj R f).obj = ModuleCat.of R (ClopenRankModule R f) :=
  (rfl)

end TauCeti.FiniteProjectiveModules
