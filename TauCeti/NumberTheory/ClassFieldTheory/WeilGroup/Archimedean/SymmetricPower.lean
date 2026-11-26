/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic
public import TauCeti.RepresentationTheory.Semisimple.Restriction
public import TauCeti.RepresentationTheory.SymmetricPower.Semisimple

/-!
# Symmetric powers of semisimple representations of the archimedean Weil groups

For every `m`, the `m`-th symmetric power `w ↦ Sym^m (r w)` of a semisimple finite-dimensional
complex representation `r` of `W_ℂ = ℂˣ` or of `W_ℝ = ℂˣ ⊔ jℂˣ` is again semisimple, and has
dimension `binom(n + m - 1, m)` when `r` has dimension `n` (`SymmetricPower.finrank_eq_choose`).

For `W_ℂ` this is `Representation.isSemisimpleRepresentation_symmetricPower`: `ℂˣ` is commutative,
so a semisimple representation is diagonalizable, and the symmetric power of a diagonalizable
action is diagonalizable. For `W_ℝ`, restriction to the subgroup `ℂˣ` of index two detects
semisimplicity in characteristic zero
(`TauCeti.ClassFieldTheory.WeilGroupReal.isSemisimpleRepresentation_comp_includeComplex_iff`):
restriction to a normal subgroup whose index is invertible detects semisimplicity
(`Representation.isSemisimpleRepresentation_comp_subtype_iff`), and the index `2` is invertible in
`ℂ`. Symmetric powers commute with restriction, so the `W_ℂ` case gives the
`W_ℝ` case.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.isSemisimpleRepresentation_comp_includeComplex_iff`: a
  finite-dimensional complex representation of `W_ℝ` is semisimple if and only if its
  restriction to `ℂˣ` is.
* `TauCeti.ClassFieldTheory.WeilGroupReal.isSemisimpleRepresentation_symmetricPower`: the
  symmetric powers of a semisimple finite-dimensional complex representation of `W_ℝ` are
  semisimple.
-/

public section

namespace TauCeti.ClassFieldTheory

open Representation

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

namespace WeilGroupReal

omit [FiniteDimensional ℂ V] in
/-- Restriction along `includeComplex` factors through the restriction to its range. -/
private theorem comp_includeComplex_eq (ρ : Representation ℂ WeilGroupReal V) :
    ρ.comp includeComplex = (ρ.comp includeComplex.range.subtype).comp
      includeComplex.rangeRestrict :=
  MonoidHom.ext fun _ ↦ rfl

/-- **Restriction to `ℂˣ` detects semisimplicity.** A finite-dimensional complex representation of
`W_ℝ` is semisimple if and only if its restriction to `W_ℂ = ℂˣ` is: `ℂˣ` is a normal subgroup of
index two, and `2` is invertible in `ℂ`. -/
@[simp]
theorem isSemisimpleRepresentation_comp_includeComplex_iff
    (ρ : Representation ℂ WeilGroupReal V) :
    IsSemisimpleRepresentation (ρ.comp includeComplex) ↔ IsSemisimpleRepresentation ρ := by
  rw [comp_includeComplex_eq, MonoidHom.isSemisimpleRepresentation_comp_surjective_iff _
    includeComplex.rangeRestrict_surjective]
  have : NeZero (includeComplex.range.index : ℂ) := ⟨by simp [index_range_includeComplex]⟩
  exact isSemisimpleRepresentation_comp_subtype_iff ρ _

/-- The restriction to `ℂˣ` of a semisimple finite-dimensional complex representation of `W_ℝ` is
semisimple. -/
instance isSemisimpleRepresentation_comp_includeComplex (ρ : Representation ℂ WeilGroupReal V)
    [ρ.IsSemisimpleRepresentation] : IsSemisimpleRepresentation (ρ.comp includeComplex) :=
  (isSemisimpleRepresentation_comp_includeComplex_iff ρ).mpr ‹_›

/-- **Symmetric powers of semisimple representations of `W_ℝ` are semisimple.** The restriction
of `Sym^m ρ` to `ℂˣ` is the `m`-th symmetric power of the restriction of `ρ`, which is
semisimple because `ℂˣ` is commutative. -/
instance isSemisimpleRepresentation_symmetricPower (ρ : Representation ℂ WeilGroupReal V)
    [ρ.IsSemisimpleRepresentation] (m : ℕ) :
    IsSemisimpleRepresentation (ρ.symmetricPower m) := by
  rw [← isSemisimpleRepresentation_comp_includeComplex_iff, ← symmetricPower_comp]
  infer_instance

end WeilGroupReal

end TauCeti.ClassFieldTheory
