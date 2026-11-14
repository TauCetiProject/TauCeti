/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Algebra.RealField
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real

/-!
# Absolute values of a field extension lying over an infinite place

Let `F / K` be a field extension and `v` an infinite place of `K`. Unlike at finite places, where
an absolute value `w : AbsoluteValue F ℝ` lying over a finite place of `K` is in general a
fractional power `FinitePlace.mk 𝔓 ^ (e * f)⁻¹`, an absolute value of `F` lying over `v` is
already the underlying absolute value of a unique infinite place of `F` lying over `v`
(`NumberField.isInfinitePlace_of_liesOver`, `NumberField.existsUnique_infinitePlace_of_liesOver`).
No algebraicity or number-field hypothesis on `F / K` is required: in fact, an absolute value on
`F` lying over an absolute value on `K` is an infinite place of `F` if and only if the base
absolute value is an infinite place of `K` (`NumberField.isInfinitePlace_iff_of_liesOver`).

The proof embeds `ℝ` isometrically into `v.Completion` via
`NumberField.InfinitePlace.Completion.ofReal`, composes with the isometric completion map
`v.Completion →+* w.Completion` (`AbsoluteValue.Completion.norm_map`), and applies the isometric
real Gelfand–Mazur embedding `NormedAlgebra.Real.exists_ringHom_complex_norm_eq` to obtain a
complex embedding of `w.Completion`, whose restriction to `F` realizes `w`.

When `F / K` is algebraic, every infinite place of `K` has an absolute value of `F` lying over it
(`NumberField.nonempty_setOf_liesOver_infinitePlace`); when `F` is a number field, only finitely
many do (`NumberField.finite_setOf_liesOver_infinitePlace`).

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value on `F` lying over an infinite place
  of `K` is an infinite place of `F`.
* `NumberField.isInfinitePlace_iff_of_liesOver`: for `w` on `F` lying over `v` on `K`, `w` is an
  infinite place of `F` if and only if `v` is an infinite place of `K`.
* `NumberField.existsUnique_infinitePlace_of_liesOver` and
  `NumberField.liesOver_infinitePlace_iff`: `w` lies over `v : InfinitePlace K` if and only if it
  is `w'.1` for a (unique) `w' : InfinitePlace F` lying over `v`.
* `NumberField.exists_injective_infinitePlace_eq_of_liesOver`: absolute values over distinct
  infinite places of `K` come from distinct infinite places of `F`.
* `NumberField.nonempty_setOf_liesOver_infinitePlace` and
  `NumberField.finite_setOf_liesOver_infinitePlace`: nonemptiness (for algebraic extensions) and
  finiteness (over number fields) of `{w : AbsoluteValue F ℝ | w.LiesOver v.1}`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section Field

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Absolute values over an infinite place.** For any field extension `F / K`, an absolute value
on `F` lying over an infinite place of `K` is an infinite place of `F`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  let ι : ℝ →+* w.Completion :=
    (AbsoluteValue.Completion.map v.1 w).comp (InfinitePlace.Completion.ofReal v)
  have hι (r : ℝ) : ‖ι r‖ = |r| := by
    simp [ι, AbsoluteValue.Completion.norm_map, InfinitePlace.Completion.norm_ofReal]
  obtain ⟨φ, -, hφ⟩ := NormedAlgebra.Real.exists_ringHom_complex_norm_eq ι hι
  refine ⟨φ.comp (algebraMap F w.Completion), AbsoluteValue.ext fun y ↦ ?_⟩
  rw [place_apply, RingHom.comp_apply, hφ, AbsoluteValue.Completion.algebraMap_def,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
    AbsoluteValue.Completion.norm_coe, WithAbs.ofAbs_toAbs]

/-- For any field extension `F / K` and absolute values `w` on `F` lying over `v` on `K`, `w` is
an infinite place of `F` if and only if `v` is an infinite place of `K`. -/
theorem isInfinitePlace_iff_of_liesOver {v : AbsoluteValue K ℝ} {w : AbsoluteValue F ℝ}
    [w.LiesOver v] : IsInfinitePlace w ↔ IsInfinitePlace v := by
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨φ.comp (algebraMap K F), AbsoluteValue.ext fun x ↦ ?_⟩
    rw [place_apply, RingHom.comp_apply, ← place_apply,
      ← LiesOver.apply_algebraMap (w := place φ) v]
  · obtain ⟨v', rfl⟩ := (isInfinitePlace_iff v).mp hv
    exact isInfinitePlace_of_liesOver v' w

/-- **Unique infinite place representing a restricted absolute value.** An absolute value `w` on
`F` lying over an infinite place `v` of `K` is the underlying absolute value of a unique infinite
place of `F` lying over `v`. -/
theorem existsUnique_infinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] :
    ∃! w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  exact ⟨w', ⟨inferInstance, rfl⟩, fun u ⟨_, hu⟩ ↦ Subtype.ext hu⟩

/-- An absolute value `w` on `F` lies over an infinite place `v` of `K` if and only if `w` is the
underlying absolute value of an infinite place of `F` lying over `v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} {w : AbsoluteValue F ℝ} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨fun _ ↦ (existsUnique_infinitePlace_of_liesOver v w).exists, ?_⟩
  rintro ⟨w', hw', rfl⟩
  exact hw'

/-- An absolute value lying over an infinite place is archimedean. -/
theorem not_isNonarchimedean_of_liesOver_infinitePlace (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : ¬ IsNonarchimedean w := by
  obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  exact w'.not_isNonarchimedean

/-- Absolute values over distinct infinite places of the base are distinct infinite places of the
extension. This permits comparing products of archimedean local factors without counting an
extension place twice. -/
theorem exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (w : S → AbsoluteValue F ℝ)
    (hw : ∀ v, (w v).LiesOver v.val.1) :
    ∃ W : S → InfinitePlace F, Function.Injective W ∧
      ∀ v, (W v).LiesOver v.val ∧ (W v).1 = w v := by
  have hclass (v : S) := by
    let := hw v
    exact (existsUnique_infinitePlace_of_liesOver v.val (w v)).exists
  choose W hW heq using hclass
  refine ⟨W, fun v u h ↦ Subtype.ext ?_, fun v ↦ ⟨hW v, heq v⟩⟩
  let := hW v
  let := hW u
  rw [← InfinitePlace.LiesOver.comap_eq (W v) v.val,
    ← InfinitePlace.LiesOver.comap_eq (W u) u.val, h]

variable (F) in
/-- Every infinite place of the base has an absolute value of an algebraic field extension lying
over it. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w', rfl⟩ := InfinitePlace.comap_surjective (K := F) v
  exact ⟨w'.1, InfinitePlace.liesOver_comap w'⟩

variable (F) in
/-- A number field has only finitely many absolute values lying over a given infinite place of a
subfield. -/
theorem finite_setOf_liesOver_infinitePlace [NumberField F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  have : Finite (InfinitePlace F) := inferInstance
  refine (Set.finite_range fun u : InfinitePlace F ↦ u.1).subset
    fun w (hw : w.LiesOver v.1) ↦ (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)

end Field

end NumberField
