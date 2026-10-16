/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
public import Mathlib.FieldTheory.PurelyInseparable.Tower
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
* `TauCeti.finrank_over_constantCompositum_eq_finrank_of_isPurelyInseparable`: purely
  inseparable constants preserve degrees over any subfield over which the original field is
  separable algebraic, without an exactness assumption.

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

/-- Adjoining purely inseparable constants produces a purely inseparable extension of the
original field, whether or not the constant extension is finite. -/
theorem isPurelyInseparable_of_constantCompositum_eq_top [IsPurelyInseparable k k']
    (h : constantCompositum F k' F' = ⊤) : IsPurelyInseparable F F' := by
  obtain ⟨q, _⟩ := ExpChar.exists k
  have := expChar_of_injective_algebraMap (algebraMap k F).injective q
  rw [isPurelyInseparable_iff_perfectClosure_eq_top]
  apply top_le_iff.mp
  rw [← h, constantCompositum_def]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q c
  exact (mem_perfectClosure_iff_pow_mem q).mpr ⟨n, algebraMap k F a, by
    rw [← map_pow, ← ha, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩

/-- A purely inseparable constant extension preserves the degree of a separable algebraic
extension `F / E`. No exactness assumption on the constants is needed. -/
theorem finrank_over_constantCompositum_eq_finrank_of_isPurelyInseparable {E : Type*}
    [Field E] [Algebra k E] [Algebra E F] [IsScalarTower k E F] [Algebra E F']
    [IsScalarTower E F F'] [IsPurelyInseparable k k'] [Algebra.IsSeparable E F]
    (h : constantCompositum F k' F' = ⊤) :
    Module.finrank (constantCompositum E k' F') F' = Module.finrank E F := by
  have : IsScalarTower k E F' := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply E F F', ← IsScalarTower.algebraMap_apply k E F,
      ← IsScalarTower.algebraMap_apply k F F']
  let C := constantCompositum E k' F'
  let : Algebra k' C := constantCompositumAlgebra E k' F'
  have : IsScalarTower k' C F' := isScalarTower_constantCompositum E k' F'
  have : IsScalarTower k k' C := isScalarTower_base_constantCompositum k E k' F'
  have hC : constantCompositum E k' C = ⊤ := (constantCompositum_eq_top_iff E k' F' C).mpr rfl
  have : IsPurelyInseparable E C := isPurelyInseparable_of_constantCompositum_eq_top (k := k) hC
  let f := IsScalarTower.toAlgHom E F F'
  have : Algebra.IsSeparable E f.fieldRange := AlgEquiv.Algebra.isSeparable f.equivFieldRange
  -- The two fields over `E` are respectively separable and purely inseparable.
  have hd := f.fieldRange.linearDisjoint_of_isPurelyInseparable_of_isSeparable C
  have hrank := hd.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have htop : IntermediateField.adjoin C (f.fieldRange : Set F') = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    have hle : constantCompositum F k' F' ≤
        (IntermediateField.adjoin C (f.fieldRange : Set F')).toSubfield.toIntermediateField
          (fun a ↦ IntermediateField.subset_adjoin C _ ⟨a, rfl⟩) := by
      apply (constantCompositum_le_iff F k' F').mpr
      intro c
      exact (IntermediateField.adjoin C (f.fieldRange : Set F')).algebraMap_mem
        ⟨_, algebraMap_mem_constantCompositum E k' F' c⟩
    exact hle (h ▸ IntermediateField.mem_top)
  rw [htop, IntermediateField.rank_top'] at hrank
  exact (congrArg Cardinal.toNat hrank).trans f.equivFieldRange.toLinearEquiv.finrank_eq.symm

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
