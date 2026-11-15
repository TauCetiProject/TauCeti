/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Algebra.GelfandMazur
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real
import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace

/-!
# Absolute values of a field extension lying over an infinite place

Let `F / K` be an extension of fields and `v` an infinite place of `K`. This file classifies the
absolute values `w : AbsoluteValue F ℝ` lying over `v` in the sense of `AbsoluteValue.LiesOver`:
every such `w` is the underlying absolute value of a unique infinite place `w'` of `F` lying over
`v` (`NumberField.isInfinitePlace_of_liesOver`,
`NumberField.existsUnique_infinitePlace_eq_of_liesOver`).
Unlike at a finite place, where an absolute value lying over the base place is in general a root of
a finite place (`NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`), no fractional power
occurs at an infinite place, and neither algebraicity nor finite-dimensionality of `F / K` is
required for the classification.

The proof passes to the completion `w.Completion`. Composing `InfinitePlace.Completion.ofReal v`
with the isometric completion map `AbsoluteValue.Completion.map v.1 w` embeds `ℝ` isometrically into
`w.Completion`. The isometric Gelfand–Mazur theorem
(`NormedAlgebra.Real.exists_ringHom_complex_norm_eq_of_ringHom`) then embeds `w.Completion`
isometrically into `ℂ`, and restricting to `F` exhibits `w` as the absolute value of a complex
embedding of `F`.

Combining the infinite-place and finite-place classifications shows that an infinite place and a
finite place of a number field never share the same underlying absolute value
(`NumberField.InfinitePlace.val_ne_finitePlace_val`), that an absolute value over a place `v` is
nonarchimedean if and only if `v` is finite
(`NumberField.isNonarchimedean_iff_isFinitePlace_of_liesOver`), and that over a finite extension of
number fields the fibre `{w : AbsoluteValue F ℝ | w.LiesOver v}` above any place is finite and
nonempty (`NumberField.finite_setOf_liesOver`, `NumberField.nonempty_setOf_liesOver`).

## Main definitions

* `NumberField.InfinitePlace.placesOverEquivAbsValues`: the equivalence between `v.placesOver F` and
  `{w : AbsoluteValue F ℝ // w.LiesOver v.1}` for any field extension `F / K`.

## Main results

* `NumberField.isInfinitePlace_of_liesOver` and `NumberField.IsInfinitePlace.of_liesOver`: an
  absolute value of `F` lying over an infinite place of `K` is an infinite place of `F`.
* `NumberField.existsUnique_infinitePlace_eq_of_liesOver` and
  `NumberField.liesOver_infinitePlace_iff`: the classification of absolute values lying over an
  infinite place.
* `NumberField.exists_injective_infinitePlace_eq_of_liesOver`: absolute values over distinct
  infinite places come from distinct infinite places of the extension.
* `NumberField.nonempty_setOf_liesOver_infinitePlace` and
  `NumberField.finite_setOf_liesOver_infinitePlace`: nonemptiness (for algebraic extensions) and
  finiteness (when the top field is a number field) of the fibre over an infinite place.
* `NumberField.InfinitePlace.val_ne_finitePlace_val`: an infinite place and a finite place never
  have the same underlying absolute value.
* `NumberField.isNonarchimedean_iff_isFinitePlace_of_liesOver`: for an absolute value `w` lying over
  a place `v` of a number field, `w` is nonarchimedean if and only if `v` is finite.
* `NumberField.finite_setOf_liesOver` and `NumberField.nonempty_setOf_liesOver`: above any place
  (infinite or finite) of a number field, a finite extension has finitely many absolute values, and
  at least one.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section FieldExtension

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Absolute values over an infinite place.** For any field extension `F / K`, an absolute value
`w` of `F` lying over an infinite place `v` of `K` is the underlying absolute value of an infinite
place of `F`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  let f : ℝ →+* w.Completion :=
    (AbsoluteValue.Completion.map v.1 w).comp (InfinitePlace.Completion.ofReal v)
  have hf (r : ℝ) : ‖f r‖ ≤ ‖r‖ := by
    rw [RingHom.comp_apply, AbsoluteValue.Completion.norm_map,
      InfinitePlace.Completion.norm_ofReal, Real.norm_eq_abs]
  obtain ⟨φ, -, hφ⟩ := NormedAlgebra.Real.exists_ringHom_complex_norm_eq_of_ringHom f hf
  refine ⟨φ.comp (algebraMap F w.Completion), AbsoluteValue.ext fun y ↦ ?_⟩
  calc
    place (φ.comp (algebraMap F w.Completion)) y
      = ‖φ (algebraMap F w.Completion y)‖ := place_apply _ y
    _ = ‖algebraMap F w.Completion y‖ := hφ _
    _ = w y := by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, AbsoluteValue.Completion.norm_coe, WithAbs.ofAbs_toAbs]

/-- An absolute value of a field extension lying over an infinite place of the base is itself an
infinite place. -/
theorem IsInfinitePlace.of_liesOver {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] : IsInfinitePlace w := by
  obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hv
  exact isInfinitePlace_of_liesOver v' w

/-- **Classification of absolute values over an infinite place.** For any field extension `F / K`,
an absolute value `w` of `F` lying over an infinite place `v` of `K` is the underlying absolute
value of a unique infinite place `w'` of `F` lying over `v`. -/
theorem existsUnique_infinitePlace_eq_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃! w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w :=
  ⟨⟨w, isInfinitePlace_of_liesOver v w⟩, ⟨inferInstance, rfl⟩, fun _ ⟨_, hw'⟩ ↦ Subtype.ext hw'⟩

/-- An absolute value of `F` lying over an infinite place `v` of `K` comes from an infinite place of
`F` lying over `v`. -/
theorem exists_infinitePlace_eq_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w :=
  (existsUnique_infinitePlace_eq_of_liesOver v w).exists

/-- An absolute value `w` of `F` lies over an infinite place `v` of `K` if and only if it is the
underlying absolute value of an infinite place of `F` lying over `v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} {w : AbsoluteValue F ℝ} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w :=
  ⟨fun _ ↦ exists_infinitePlace_eq_of_liesOver v w, fun ⟨_, hw', h⟩ ↦ h ▸ hw'⟩

namespace InfinitePlace

variable (F) in
/-- Infinite places of `F` above `v` correspond bijectively to absolute values of `F` restricting to
`v` on the nose, by taking the underlying absolute value. -/
def placesOverEquivAbsValues (v : InfinitePlace K) :
    v.placesOver F ≃ {w : AbsoluteValue F ℝ // w.LiesOver v.1} where
  toFun w := ⟨w.val.1, w.prop⟩
  invFun w :=
    let := w.prop
    ⟨⟨w.val, isInfinitePlace_of_liesOver v w.val⟩, w.prop⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- The forward correspondence takes the underlying absolute value of the infinite place. -/
@[simp]
theorem placesOverEquivAbsValues_apply (v : InfinitePlace K) (w : v.placesOver F) :
    (placesOverEquivAbsValues F v w).val = w.val.1 :=
  (rfl)

/-- The inverse correspondence recovers an infinite place with the same underlying absolute
value. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) :
    ((placesOverEquivAbsValues F v).symm w).val.1 = w.val :=
  (rfl)

/-- Evaluating the infinite place recovered by the inverse correspondence agrees with evaluating the
absolute value. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply_apply (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) (y : F) :
    ((placesOverEquivAbsValues F v).symm w).val y = w.val y :=
  (rfl)

/-- When `F` is a number field, only finitely many absolute values of `F` lie over a given infinite
place of `K`. -/
instance [NumberField F] (v : InfinitePlace K) : Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1} :=
  Finite.of_equiv _ (placesOverEquivAbsValues F v)

end InfinitePlace

/-- Absolute values over distinct infinite places are the underlying absolute values of distinct
infinite places of the extension. -/
theorem exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (w : S → AbsoluteValue F ℝ)
    (hw : ∀ v, (w v).LiesOver v.val.1) :
    ∃ V : S → InfinitePlace F, Function.Injective V ∧
      ∀ v, (V v).LiesOver v.val ∧ (V v).1 = w v := by
  let V : S → InfinitePlace F := fun v ↦
    let := hw v
    ⟨w v, isInfinitePlace_of_liesOver v.val (w v)⟩
  have hV (v : S) : (V v).LiesOver v.val := hw v
  refine ⟨V, fun v u hvu ↦ Subtype.ext ?_, fun v ↦ ⟨hV v, rfl⟩⟩
  let := hV v
  let := hV u
  rw [← InfinitePlace.LiesOver.comap_eq (V v) v.val,
    ← InfinitePlace.LiesOver.comap_eq (V u) u.val, hvu]

variable (F)

/-- Over an algebraic field extension `F / K`, every infinite place of `K` has an absolute value of
`F` lying over it. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w', rfl⟩ := InfinitePlace.comap_surjective (K := F) v
  exact ⟨w'.1, w'.liesOver_comap⟩

/-- A number field `F` over an arbitrary base field `K` has only finitely many absolute values lying
over a given infinite place of `K`. -/
theorem finite_setOf_liesOver_infinitePlace [NumberField F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite :=
  Set.finite_coe_iff.mp (Finite.of_equiv _ (InfinitePlace.placesOverEquivAbsValues F v))

end FieldExtension

section DisjointAndCharacterization

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- An infinite place of a field is archimedean. -/
theorem IsInfinitePlace.not_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v) :
    ¬IsNonarchimedean v := by
  obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hv
  exact v'.not_isNonarchimedean

variable [NumberField K]

/-- Every finite place of a number field is nonarchimedean. -/
theorem IsFinitePlace.isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsFinitePlace v) :
    IsNonarchimedean v := by
  obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hv
  exact u.add_le

/-- An infinite place and a finite place of a number field never have the same underlying absolute
value: an infinite place is archimedean whereas a finite place is nonarchimedean. -/
theorem InfinitePlace.val_ne_finitePlace_val (v : InfinitePlace K) (u : FinitePlace K) :
    v.1 ≠ u.1 := fun h ↦
  v.not_isNonarchimedean (h ▸ u.add_le)

/-- An infinite place of a number field is not a finite place. -/
theorem IsInfinitePlace.not_isFinitePlace {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v) :
    ¬IsFinitePlace v := fun hfin ↦
  hv.not_isNonarchimedean hfin.isNonarchimedean

/-- A finite place of a number field is not an infinite place. -/
theorem IsFinitePlace.not_isInfinitePlace {v : AbsoluteValue K ℝ} (hv : IsFinitePlace v) :
    ¬IsInfinitePlace v := fun hinf ↦
  hinf.not_isFinitePlace hv

/-- For a field extension `F / K` of a number field `K` and a place `v` of `K`, an absolute value
`w` of `F` lying over `v` is nonarchimedean if and only if `v` is a finite place. -/
theorem isNonarchimedean_iff_isFinitePlace_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean w ↔ IsFinitePlace v := by
  rw [AbsoluteValue.isNonarchimedean_iff_of_liesOver v w]
  exact ⟨fun hna ↦ hv.resolve_left fun hinf ↦ hinf.not_isNonarchimedean hna,
    IsFinitePlace.isNonarchimedean⟩

/-- For a field extension `F / K` of a number field `K` and a place `v` of `K`, an absolute value
`w` of `F` lying over `v` is archimedean if and only if `v` is an infinite place. -/
theorem not_isNonarchimedean_iff_isInfinitePlace_of_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    ¬IsNonarchimedean w ↔ IsInfinitePlace v := by
  rw [isNonarchimedean_iff_isFinitePlace_of_liesOver hv w]
  exact ⟨fun h ↦ hv.resolve_right h, IsInfinitePlace.not_isFinitePlace⟩

variable (F) [NumberField F]

/-- A finite extension of number fields has only finitely many absolute values lying over a given
finite place of the base. -/
theorem finite_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  simpa only [v.mk_maximalIdeal] using finite_setOf_liesOver_finitePlace_mk F v.maximalIdeal

/-- Every finite place of a number field has an absolute value of a finite extension of number
fields lying over it. -/
theorem nonempty_setOf_liesOver_finitePlace (v : FinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  simpa only [v.mk_maximalIdeal] using nonempty_setOf_liesOver_finitePlace_mk F v.maximalIdeal

/-- A finite extension of number fields has only finitely many absolute values lying over any given
place (infinite or finite) of the base. -/
theorem finite_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact finite_setOf_liesOver_infinitePlace F v'
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact finite_setOf_liesOver_finitePlace F v'

/-- Above every place (infinite or finite) of a number field, a finite extension has at least one
absolute value lying over it. -/
theorem nonempty_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with hinf | hfin
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hinf
    exact nonempty_setOf_liesOver_infinitePlace F v'
  · obtain ⟨v', rfl⟩ := (isFinitePlace_iff v).mp hfin
    exact nonempty_setOf_liesOver_finitePlace F v'

end DisjointAndCharacterization

end NumberField
