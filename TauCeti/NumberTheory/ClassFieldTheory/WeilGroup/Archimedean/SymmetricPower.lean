/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic
public import TauCeti.RepresentationTheory.SymmetricPower.Semisimple

/-!
# Symmetric powers of semisimple representations of `W_ℂ`

The Weil group `W_ℂ = ℂˣ` of `ℂ` is commutative and `ℂ` is algebraically closed, so the symmetric
powers of a finite-dimensional semisimple complex representation of `W_ℂ` are semisimple
(`Representation.isSemisimpleRepresentation_symmetricPower`). For a representation of dimension
`n`, the symmetric power `Sym^m` has dimension `binom(n + m - 1, m)`
(`SymmetricPower.finrank_eq_choose`).

## Main results

* `Representation.isSemisimpleRepresentation_symmetricPower_weilGroupComplex_and_finrank_eq`: for a
  finite-dimensional semisimple complex representation of `W_ℂ`, `Sym^m` is semisimple of
  dimension `binom(n + m - 1, m)`.
-/

public section

open scoped TensorProduct

namespace Representation

open TauCeti.ClassFieldTheory

/-- **Symmetric powers of semisimple representations of `W_ℂ = ℂˣ`**: for a finite-dimensional
semisimple complex representation `ρ` of `W_ℂ` of dimension `n`, the symmetric power `Sym^m ρ` is
semisimple of dimension `binom(n + m - 1, m)`. -/
theorem isSemisimpleRepresentation_symmetricPower_weilGroupComplex_and_finrank_eq {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ WeilGroupComplex V)
    [ρ.IsSemisimpleRepresentation] (m : ℕ) :
    IsSemisimpleRepresentation (k := ℂ) (G := WeilGroupComplex) (V := Sym[ℂ]^m V)
        (ρ.symmetricPower m) ∧
      Module.finrank ℂ (Sym[ℂ]^m V) = (Module.finrank ℂ V + m - 1).choose m :=
  ⟨isSemisimpleRepresentation_symmetricPower ρ m, SymmetricPower.finrank_eq_choose⟩

end Representation
