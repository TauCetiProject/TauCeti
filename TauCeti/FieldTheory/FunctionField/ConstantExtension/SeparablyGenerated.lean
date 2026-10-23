/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Degrees under algebraic extensions of constants for separably generated fields

If `F / E` is separable algebraic, adjoining purely inseparable constants preserves its degree:
`[F · k' : E · k'] = [F : E]`. In particular, for a separating variable `x` of a function field,
`[F · k' : k'(x)] = [F : k(x)]`, even over an imperfect constant field and without assuming that
its constants are exact. Factoring an arbitrary algebraic extension of constants through its
separable closure then proves the same degree identity for a separating variable when the
original constants are exact. Thus separable generation, rather than perfectness, suffices for
the degree comparison. The extension of constants need not be finite.

The proof uses Mathlib's linear disjointness of separable and purely inseparable extensions,
not a perfectness assumption. First, a purely inseparable extension of constants gives a purely
inseparable compositum over any field containing the original constants.

## Main results

* `TauCeti.finrank_over_adjoin_simple_eq_of_separating`: an arbitrary algebraic extension of
  exact constants preserves the degree over a separating rational subfield.
* `TauCeti.finrank_over_adjoin_simple_eq_of_isPurelyInseparable`: purely inseparable
  constants preserve the degree over a separating rational subfield, without an exactness
  assumption.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Proposition 3.6.1(c), and Section III.10 for separating elements.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A purely inseparable extension of constants preserves the degree over a separating rational
subfield: `[F · k' : k'(x)] = [F : k(x)]`. The constants need not be perfect or exact. -/
theorem finrank_over_adjoin_simple_eq_of_isPurelyInseparable
    [IsPurelyInseparable k k'] (h : constantCompositum F k' F' = ⊤)
    (x : F) [Algebra.IsSeparable k⟮x⟯ F] :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  have heq := finrank_over_constantCompositum_eq_finrank_of_isPurelyInseparable
    (k := k) (E := k⟮x⟯) h
  have hsubfield : (constantCompositum k⟮x⟯ k' F').toSubfield =
      k'⟮algebraMap F F' x⟯.toSubfield := by
    rw [constantCompositum_def, IntermediateField.adjoin_toSubfield,
      Set.union_comm, ← IntermediateField.adjoin_toSubfield,
      IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right]
  -- The subfield congruence fixes ambient elements, hence intertwines both algebra maps.
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.subfieldCongr hsubfield)
    (RingEquiv.refl F') rfl).symm.trans heq

/-- An arbitrary algebraic extension of an exact constant field preserves the degree over a
separating rational subfield. This is the conserved, or separably generated, form of the degree
identity in Stichtenoth, Proposition 3.6.1(c); perfectness of the constants is unnecessary. -/
theorem finrank_over_adjoin_simple_eq_of_separating [Algebra.IsAlgebraic k k']
    (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (x : F) [Algebra.IsSeparable k⟮x⟯ F] :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  -- First adjoin the separable constants; the remaining constant extension is purely inseparable.
  let L := separableClosure k k'
  let E := constantCompositum F L F'
  let : Algebra L E := constantCompositumAlgebra F L F'
  have : IsScalarTower L E F' := isScalarTower_constantCompositum F L F'
  have : IsScalarTower k L E := isScalarTower_base_constantCompositum k F L F'
  have hE : constantCompositum F L E = ⊤ := (constantCompositum_eq_top_iff F L F' E).mpr rfl
  have htop : constantCompositum E k' F' = ⊤ :=
    constantCompositum_eq_top_of_eq_top F k' F' E h
  have : Algebra.IsSeparable L⟮algebraMap F E x⟯ E :=
    isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) hE
  calc
    Module.finrank k'⟮algebraMap F F' x⟯ F' =
        Module.finrank k'⟮algebraMap E F' (algebraMap F E x)⟯ F' := by
      rw [IsScalarTower.algebraMap_apply F E F']
    _ = Module.finrank L⟮algebraMap F E x⟯ E :=
      finrank_over_adjoin_simple_eq_of_isPurelyInseparable (k := L) htop _
    _ = Module.finrank k⟮x⟯ F :=
      finrank_over_adjoin_simple_eq_of_constantCompositum_eq_top (k := k) hex hE x

end TauCeti
