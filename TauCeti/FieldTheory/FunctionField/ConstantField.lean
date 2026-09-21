/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# The constant field of an algebraic function field

The *field of constants* of an algebraic function field `F / k` is the relative algebraic closure
`algebraicClosure k F` of `k` in `F`: the elements of `F` that are algebraic over `k`. This file
proves that it is a finite extension of `k`, records the dictionary for the hypothesis that it is
no larger than `k` (the literature's "`k` is the full field of constants"), and shows that
replacing `k` by the field of constants normalizes any function field to one whose field of
constants is exact.

It then follows the field of constants along a change of the base field.  An intermediate base
field `k'` of `F / k` — one over which `F` is again a function field, which by
`TauCeti.isFunctionField_base_iff_isAlgebraic` means exactly that `k' / k` is algebraic — is
automatically finite over `k`, and as soon as `k'` is its own field of constants it *is* the
field of constants of `F / k`.  In the tower of an extension `F' / k'` of `F / k`, the field of
constants of `F' / k'` cuts down along `F ⊆ F'` to the field of constants of `F / k`; when both
bases are exact this says that `k' ∩ F = k`, so the tower map `k → k'` is the induced inclusion
of the two fields of constants.  The base extension `k' / k` is always algebraic, and finite
once `F' / F` is — a theorem, not a hypothesis, and the finiteness that makes the factor
`[k' : k]` in the conorm degree identity and in the Hurwitz genus formula meaningful.

## Main results

* `TauCeti.IsFunctionField.finiteDimensional_of_isAlgebraic`: an intermediate extension of a
  function field `F / k` which is algebraic over `k` is finite over `k`.
* `TauCeti.IsFunctionField.finiteDimensional_algebraicClosure`: the field of constants of a
  function field is finite over the base field.
* `TauCeti.algebraicClosure_eq_bot_iff_isIntegrallyClosedIn`,
  `TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic`,
  `TauCeti.isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one`: the three faces of the
  exactness hypothesis on the field of constants.
* `TauCeti.IsFunctionField.algebraicClosure` and
  `TauCeti.isIntegrallyClosedIn_algebraicClosure`: `F` is a function field over its field of
  constants, and there the field of constants is exact; the two are packaged as
  `TauCeti.IsFunctionField.exists_intermediateField_isIntegrallyClosedIn`.
* `TauCeti.IsFunctionField.finiteDimensional_base` and
  `TauCeti.IsFunctionField.algebraicClosure_eq_restrictScalars_bot`: an intermediate base field
  of `F / k` is finite over `k`, and is the field of constants of `F / k` as soon as it is its
  own; `TauCeti.IsFunctionField.isAlgebraic_iff_mem_range_algebraMap` is the elementwise form.
* `TauCeti.IsFunctionField.isAlgebraic_baseExtension` and
  `TauCeti.IsFunctionField.finiteDimensional_baseExtension`: in an extension `F' / k'` of
  `F / k`, the base extension `k' / k` is algebraic, and finite once `F' / F` is (Stichtenoth,
  Definition 3.1.1).
* `TauCeti.IsFunctionField.isAlgebraic_algebraMap_iff_isAlgebraic`: the field of constants of
  `F' / k'` cuts down along `F ⊆ F'` to the field of constants of `F / k`; for exact bases
  `TauCeti.IsFunctionField.algebraMap_mem_range_algebraMap_iff` reads this as `k' ∩ F = k`.
* `TauCeti.algebraicClosure_ratFunc`: `k` is the field of constants of `k(x)`.

## References

The statements follow Stichtenoth, *Algebraic Function Fields and Codes*, second edition:
Corollary 1.1.16 for the finiteness of the field of constants, the standing hypothesis of
Section 1.4 for its exactness, Proposition 1.2.1(d) for the rational function field, and
Definition 3.1.1 for an extension of function fields.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField Polynomial

open scoped RatFunc

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-! ### Finiteness of the field of constants -/

namespace IsFunctionField

/-- An intermediate extension of an algebraic function field `F / k` which is algebraic over `k`
is a finite extension of `k` (Stichtenoth, Corollary 1.1.16). -/
theorem finiteDimensional_of_isAlgebraic (hF : IsFunctionField k F) (E : Type*) [Field E]
    [Algebra k E] [Algebra E F] [IsScalarTower k E F] [Algebra.IsAlgebraic k E] :
    FiniteDimensional k E := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  let : Algebra k[X] F := (Polynomial.aeval x).toRingHom.toAlgebra
  have : IsScalarTower k k[X] F := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have : FaithfulSMul k[X] F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (transcendental_iff_injective.1 hx)
  let : Algebra E[X] F := (Polynomial.aeval x (R := E)).toRingHom.toAlgebra
  have : FaithfulSMul E[X] F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (transcendental_iff_injective.1 (hx.extendScalars (S := E)))
  let : Algebra k[X] E[X] := Polynomial.algebra k E
  have : IsScalarTower k[X] E[X] F := .of_algebraMap_eq fun p ↦
    (Polynomial.aeval_map_algebraMap E x p).symm
  have : FunctionField k F := isFunctionField_iff_functionField.1 hF
  exact FunctionField.finiteDimensional_of_constantExtension F

/-- The field of constants of an algebraic function field is a finite extension of the base
field (Stichtenoth, Corollary 1.1.16). -/
theorem finiteDimensional_algebraicClosure (hF : IsFunctionField k F) :
    FiniteDimensional k (_root_.algebraicClosure k F) :=
  hF.finiteDimensional_of_isAlgebraic _

end IsFunctionField

/-! ### Exactness of the field of constants -/

/-- `k` is integrally closed in `F` exactly when no element of `F` outside `k` is algebraic over
`k`, that is, when the field of constants of `F / k` is `k` itself. -/
theorem algebraicClosure_eq_bot_iff_isIntegrallyClosedIn :
    algebraicClosure k F = ⊥ ↔ IsIntegrallyClosedIn k F := by
  rw [← IsIntegrallyClosedIn.integralClosure_eq_bot_iff F (algebraMap k F).injective,
    ← algebraicClosure_toSubalgebra, ← IntermediateField.bot_toSubalgebra,
    IntermediateField.toSubalgebra_inj]

/-- The elementwise form of the exactness hypothesis on the field of constants: every element of
`F` algebraic over `k` is already a constant. This is the field-extension reading of Mathlib's
`isIntegrallyClosedIn_iff`, whose injectivity clause is automatic here. -/
theorem isIntegrallyClosedIn_iff_forall_isAlgebraic :
    IsIntegrallyClosedIn k F ↔ ∀ x : F, IsAlgebraic k x → ∃ c : k, algebraMap k F c = x := by
  rw [← algebraicClosure_eq_bot_iff_isIntegrallyClosedIn, eq_bot_iff, SetLike.le_def]
  simp [mem_algebraicClosure_iff, IntermediateField.mem_bot]

/-- The exactness hypothesis on the field of constants, read off its degree. -/
theorem isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one :
    IsIntegrallyClosedIn k F ↔ Module.finrank k (algebraicClosure k F) = 1 := by
  rw [IntermediateField.finrank_eq_one_iff, algebraicClosure_eq_bot_iff_isIntegrallyClosedIn]

/-- The field of constants is exact in itself: nothing in `F` outside `algebraicClosure k F` is
algebraic over `algebraicClosure k F`. -/
instance isIntegrallyClosedIn_algebraicClosure :
    IsIntegrallyClosedIn (algebraicClosure k F) F :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.1 (algebraicClosure.algebraicClosure_eq_bot k F)

/-! ### The normalization device -/

/-- An algebraic function field is a function field over its own field of constants, and by
`TauCeti.isIntegrallyClosedIn_algebraicClosure` the field of constants is exact there.

This is the device that lets a statement needing an exact field of constants be applied to an
arbitrary function field. -/
theorem IsFunctionField.algebraicClosure (hF : IsFunctionField k F) :
    IsFunctionField (_root_.algebraicClosure k F) F :=
  hF.of_isAlgebraic

/-- The normalization device: every algebraic function field is, over a finite extension of its
base field, an algebraic function field with an exact field of constants. Results stated under
the exactness hypothesis can therefore be applied to a general function field through this. -/
theorem IsFunctionField.exists_intermediateField_isIntegrallyClosedIn (hF : IsFunctionField k F) :
    ∃ k' : IntermediateField k F,
      FiniteDimensional k k' ∧ IsFunctionField k' F ∧ IsIntegrallyClosedIn k' F :=
  ⟨_root_.algebraicClosure k F, hF.finiteDimensional_algebraicClosure, hF.algebraicClosure,
    inferInstance⟩

/-! ### Intermediate base fields -/

section IntermediateBase

variable {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' F] [IsScalarTower k k' F]

/-- An intermediate base field of an algebraic function field is a finite extension of the
original base field (Stichtenoth, Corollary 1.1.16). -/
theorem IsFunctionField.finiteDimensional_base (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) : FiniteDimensional k k' :=
  have := hF.isAlgebraic_base hF'
  hF.finiteDimensional_of_isAlgebraic k'

/-- **The field of constants of `F / k` is the intermediate base field `k'`**, whenever `k'` is
its own field of constants in `F`. -/
theorem IsFunctionField.algebraicClosure_eq_restrictScalars_bot (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) (hex : IsIntegrallyClosedIn k' F) :
    _root_.algebraicClosure k F = (⊥ : IntermediateField k' F).restrictScalars k := by
  have := hF.isAlgebraic_base hF'
  rw [_root_.algebraicClosure.eq_restrictScalars_of_isAlgebraic k k' F,
    algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.2 hex]

/-- The elementwise form of `TauCeti.IsFunctionField.algebraicClosure_eq_restrictScalars_bot`: an
element of `F` is algebraic over `k` exactly when it is one of the constants `k'`. -/
theorem IsFunctionField.isAlgebraic_iff_mem_range_algebraMap (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F) (hex : IsIntegrallyClosedIn k' F) {x : F} :
    IsAlgebraic k x ↔ x ∈ Set.range (algebraMap k' F) := by
  rw [← mem_algebraicClosure_iff, hF.algebraicClosure_eq_restrictScalars_bot hF' hex,
    IntermediateField.mem_restrictScalars, IntermediateField.mem_bot]

end IntermediateBase

/-! ### Extensions of function fields -/

section Extension

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra F F']
variable [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

section IsAlgebraic

variable [Algebra.IsAlgebraic F F']

/-- **The field of constants of `F' / k'` cuts down along `F ⊆ F'` to the field of constants of
`F / k`**: a function of `F` is algebraic over `k'` exactly when it is algebraic over `k`.  The
bases need not be exact, since either field of constants is a relative algebraic closure and not
a base field. -/
theorem IsFunctionField.isAlgebraic_algebraMap_iff_isAlgebraic (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') {a : F} :
    IsAlgebraic k' (algebraMap F F' a) ↔ IsAlgebraic k a := by
  have := hF.isAlgebraic_baseExtension hF'
  rw [← mem_algebraicClosure_iff, ← IntermediateField.mem_restrictScalars (K := k),
    ← _root_.algebraicClosure.eq_restrictScalars_of_isAlgebraic k k' F',
    mem_algebraicClosure_iff]
  exact isAlgebraic_algebraMap_iff (FaithfulSMul.algebraMap_injective F F')

/-- **The fields of constants of an extension of function fields are identified along the tower
map `k → k'`** (Stichtenoth, Definition 3.1.1 and the remark following it).  Once `k` is the full
field of constants of `F / k` and `k'` the full field of constants of `F' / k'`, a function of
`F` is a constant of `F' / k'` exactly when it is already a constant of `F / k`: inside `F'` the
two fields of constants meet in `k`, so `k → k'` is the induced inclusion of fields of
constants. -/
theorem IsFunctionField.algebraMap_mem_range_algebraMap_iff (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (hk : IsIntegrallyClosedIn k F)
    (hk' : IsIntegrallyClosedIn k' F') {a : F} :
    algebraMap F F' a ∈ Set.range (algebraMap k' F') ↔ a ∈ Set.range (algebraMap k F) := by
  rw [← IntermediateField.mem_bot (F := k'), ← IntermediateField.mem_bot (F := k),
    ← algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.2 hk',
    ← algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.2 hk]
  simp only [mem_algebraicClosure_iff]
  exact hF.isAlgebraic_algebraMap_iff_isAlgebraic hF'

end IsAlgebraic

/-- **The base field of an extension of function fields is a finite extension of the base field
below** (Stichtenoth, Corollary 1.1.16 applied in the tower of Definition 3.1.1).  This is the
finiteness that makes the factor `[k' : k]` of the conorm degree identity and of the Hurwitz
genus formula meaningful.

Unlike `TauCeti.IsFunctionField.isAlgebraic_baseExtension`, this does need `F' / F` to be finite
and not merely algebraic: for an algebraic closure `k'` of a finite field `k`, the extension
`k'(x) / k(x)` is algebraic while `k' / k` is infinite. -/
theorem IsFunctionField.finiteDimensional_baseExtension [FiniteDimensional F F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') : FiniteDimensional k k' :=
  (hF.finite_extension (E := F')).finiteDimensional_base hF'

end Extension

/-! ### The rational function field -/

/-- The field of constants of the rational function field `k(x)` is `k`
(Stichtenoth, Proposition 1.2.1(d)). -/
theorem algebraicClosure_ratFunc (K : Type*) [Field K] :
    algebraicClosure K (RatFunc K) = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  obtain ⟨c, rfl⟩ := not_not.1 fun h ↦
    RatFunc.transcendental_of_ne_C f h (mem_algebraicClosure_iff.1 hf)
  rw [← RatFunc.algebraMap_eq_C]
  exact IntermediateField.algebraMap_mem _ _

/-- `k` is integrally closed in the rational function field `k(x)`. -/
instance isIntegrallyClosedIn_ratFunc : IsIntegrallyClosedIn k (RatFunc k) :=
  algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.1 (algebraicClosure_ratFunc k)

end TauCeti
