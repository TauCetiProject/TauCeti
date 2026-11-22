/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.RingTheory.Idempotents.Clopen.Basic
public import TauCeti.RingTheory.Idempotents.Clopen.RankModule

import TauCeti.RingTheory.Idempotents.Projective

/-!
# Clopen and prescribed-rank finitely generated projective modules

For a commutative ring `R`, this file packages the finitely generated projective `R`-modules
attached to clopen subsets of `Spec R` and to locally constant `ℕ`-valued rank functions as objects
of `(TauCeti.finiteProjectiveModules R).FullSubcategory`.

## Main definitions

* `TauCeti.FiniteProjectiveModules.clopenObj`: the finitely generated projective `R`-module
  `R e_U` attached to a clopen subset `U ⊆ Spec R`.
* `TauCeti.FiniteProjectiveModules.clopenRankObj`: `TauCeti.ClopenRankModule R f` as an object of
  `(TauCeti.finiteProjectiveModules R).FullSubcategory`.
-/

public section

open CategoryTheory TopologicalSpace
open PrimeSpectrum (isIdempotentElemEquivClopens)

universe u

namespace TauCeti.FiniteProjectiveModules

variable (R : Type u) [CommRing R]

/-- The finitely generated projective `R`-module `R e_U` attached to a clopen subset
`U ⊆ Spec R`. -/
noncomputable def clopenObj (U : Clopens (PrimeSpectrum R)) :
    (finiteProjectiveModules R).FullSubcategory :=
  ⟨ModuleCat.of R (Ideal.span {(isIdempotentElemEquivClopens.symm U).val} : Ideal R),
    finiteProjectiveModules_iff.2 ⟨Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _),
      (isIdempotentElemEquivClopens.symm U).property.projective_span_singleton⟩⟩

/-- `clopenObj R U` has underlying module
`Ideal.span {(isIdempotentElemEquivClopens.symm U).val}`. -/
@[simp]
theorem clopenObj_obj (U : Clopens (PrimeSpectrum R)) :
    (clopenObj R U).obj =
      ModuleCat.of R (Ideal.span {(isIdempotentElemEquivClopens.symm U).val} : Ideal R) :=
  (rfl)

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
