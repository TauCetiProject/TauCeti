/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import TauCeti.Analysis.AbsoluteValue.Complex
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real

/-!
# Absolute values of a field extension lying over an infinite place

Let `F / K` be an arbitrary extension of fields and `v` an infinite place of `K`. This file
classifies the absolute values `w : AbsoluteValue F ℝ` lying over `v.1` in the sense of Mathlib's
`AbsoluteValue.LiesOver`, that is, whose restriction to `K` equals `v` on the nose: they are
precisely the underlying absolute values of the infinite places `w' : InfinitePlace F` lying over
`v` (`NumberField.isInfinitePlace_of_liesOver`, `NumberField.liesOver_infinitePlace_iff`).

In contrast to finite places (`TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace`), where a
ramified or nonsplit prime requires taking a root of a finite place of `F`, an infinite place `w'`
of `F` above `v` already restricts to `v` without an exponent: the local degree `[F_{w'} : K_v]`
appears instead in the multiplicity `w'.mult`.

## Proof outline

No algebraicity or finite-dimensionality hypothesis on `F / K` is needed for the classification.
The completion `v.Completion` contains an isometric copy of `ℝ`
(`NumberField.InfinitePlace.Completion.ofReal`), which maps isometrically into `w.Completion` along
`AbsoluteValue.Completion.map v.1 w`. By the isometric Gelfand–Mazur theorem over `ℝ`
(`NormedAlgebra.Real.exists_ringHom_complex_isometry`), `w.Completion` embeds isometrically into
`ℂ`, and restricting this embedding to `F` exhibits `w` as `NumberField.place ψ`.

## Main definitions and results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value of `F` lying over an infinite place
  of `K` is an infinite place of `F`.
* `NumberField.isInfinitePlace_iff_forall_natCast_eq`: an absolute value on a field is an infinite
  place if and only if it sends every natural number `n` to `n`.
* `NumberField.existsUnique_infinitePlace_eq_of_liesOver` and
  `NumberField.liesOver_infinitePlace_iff`: an absolute value of `F` lies over `v.1` if and only if
  it is the underlying absolute value of a unique infinite place of `F` over `v`.
* `NumberField.InfinitePlace.placesOverEquivAbsValues`: the equivalence between `v.placesOver F`
  and `{w : AbsoluteValue F ℝ // w.LiesOver v.1}`.
* `NumberField.exists_injective_infinitePlace_eq_of_liesOver`: absolute values chosen over distinct
  infinite places of `K` come from distinct infinite places of `F`.
* `NumberField.finite_setOf_liesOver_infinitePlace` and
  `NumberField.nonempty_setOf_liesOver_infinitePlace`: finiteness (when `InfinitePlace F` is
  finite, in particular for number fields) and nonemptiness (for algebraic extensions, in
  particular for number fields) of the fibre above an infinite place.

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
`w` of `F` lying over an infinite place `v` of `K` is an infinite place of `F`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  let f : ℝ →+* w.Completion :=
    (AbsoluteValue.Completion.map v.1 w).comp (InfinitePlace.Completion.ofReal v)
  have hf : Isometry f :=
    (AbsoluteValue.Completion.isometry_map v.1 w).comp (InfinitePlace.Completion.isometry_ofReal v)
  obtain ⟨φ, -, hφ⟩ := NormedAlgebra.Real.exists_ringHom_complex_isometry f hf
  refine ⟨φ.comp (algebraMap F w.Completion), AbsoluteValue.ext fun y ↦ ?_⟩
  rw [place_apply, RingHom.comp_apply, hφ.norm_map_of_map_zero (map_zero φ),
    AbsoluteValue.Completion.algebraMap_def, AbsoluteValue.Completion.norm_coe,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Absolute values over an infinite place.** An absolute value `w` of `F` lying over an infinite
place `v` of `K` is the underlying absolute value of a unique infinite place `w'` of `F` lying over
`v`. -/
theorem existsUnique_infinitePlace_eq_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃! w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  exact ⟨w', ⟨inferInstance, rfl⟩, fun u ⟨_, hu⟩ ↦ Subtype.ext hu⟩

/-- An absolute value `w` of `F` lying over an infinite place `v` of `K` is the underlying absolute
value of an infinite place `w'` of `F` lying over `v`. -/
theorem exists_infinitePlace_eq_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w :=
  (existsUnique_infinitePlace_eq_of_liesOver v w).exists

/-- An absolute value `w` of `F` lies over the infinite place `v` of `K` if and only if `w` is the
underlying absolute value of an infinite place of `F` lying over `v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} {w : AbsoluteValue F ℝ} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w :=
  ⟨fun _ ↦ exists_infinitePlace_eq_of_liesOver v w, fun ⟨_, hw', h⟩ ↦ h ▸ hw'⟩

/-- An absolute value lying over an infinite place is archimedean. -/
theorem not_isNonarchimedean_of_liesOver_infinitePlace (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : ¬IsNonarchimedean w := by
  obtain ⟨w', -, rfl⟩ := exists_infinitePlace_eq_of_liesOver v w
  exact w'.not_isNonarchimedean

/-- Absolute values chosen over distinct infinite places of `K` are the underlying absolute values
of distinct infinite places of `F` lying over them. -/
theorem exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (w : S → AbsoluteValue F ℝ)
    (hw : ∀ v, (w v).LiesOver v.val.1) :
    ∃ V : S → InfinitePlace F, Function.Injective V ∧
      ∀ v, (V v).LiesOver v.val ∧ (V v).1 = w v := by
  choose V hV hval using fun v : S ↦
    @exists_infinitePlace_eq_of_liesOver K F _ _ _ v.val (w v) (hw v)
  refine ⟨V, fun v u h ↦ Subtype.ext ?_, fun v ↦ ⟨hV v, hval v⟩⟩
  let _ := hV v
  let _ := hV u
  rw [← InfinitePlace.LiesOver.comap_eq (V v) v.val,
    ← InfinitePlace.LiesOver.comap_eq (V u) u.val, h]

namespace InfinitePlace

variable (F) in
/-- Infinite places of `F` above `v` correspond bijectively to absolute values of `F` restricting
to `v` on the nose, by forgetting that the absolute value comes from a complex embedding. -/
def placesOverEquivAbsValues (v : InfinitePlace K) :
    v.placesOver F ≃ {w : AbsoluteValue F ℝ // w.LiesOver v.1} where
  toFun w := ⟨w.val.1, w.property⟩
  invFun w :=
    have := w.property
    ⟨⟨w.val, isInfinitePlace_of_liesOver v w.val⟩, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem placesOverEquivAbsValues_apply (v : InfinitePlace K) (w : v.placesOver F) :
    (placesOverEquivAbsValues F v w).val = w.val.1 :=
  (rfl)

@[simp]
theorem placesOverEquivAbsValues_symm_apply_coe (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) :
    ((placesOverEquivAbsValues F v).symm w).val.1 = w.val :=
  (rfl)

@[simp]
theorem placesOverEquivAbsValues_symm_apply_apply (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) (y : F) :
    ((placesOverEquivAbsValues F v).symm w).val y = w.val y :=
  (rfl)

/-- When `F` has finitely many infinite places (in particular when `F` is a number field), the
fibre of absolute values of `F` above an infinite place of `K` is finite. -/
instance [Finite (InfinitePlace F)] (v : InfinitePlace K) :
    Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1} :=
  Finite.of_equiv _ (placesOverEquivAbsValues F v)

end InfinitePlace

variable (F)

/-- When `F` has finitely many infinite places (in particular when `F` is a number field), `F` has
only finitely many absolute values lying over a given infinite place of `K`. -/
theorem finite_setOf_liesOver_infinitePlace [Finite (InfinitePlace F)] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite :=
  Set.finite_coe_iff.mp (inferInstanceAs (Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1}))

/-- Every infinite place of `K` extends to an absolute value of any algebraic extension `F / K`. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w', rfl⟩ := InfinitePlace.comap_surjective (K := F) v
  exact ⟨w'.1, InfinitePlace.liesOver_comap w'⟩

/-- Every infinite place of `K` extends to an absolute value of a number field `F` over `K`. -/
theorem nonempty_setOf_liesOver_infinitePlace_of_numberField [NumberField F]
    (v : InfinitePlace K) : {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  have : CharZero K := (algebraMap K F).charZero
  have := Algebra.IsAlgebraic.tower_top (K := ℚ) (L := K) (A := F)
  exact nonempty_setOf_liesOver_infinitePlace F v

end Field

/-- An absolute value on a field is an infinite place if and only if it agrees with the canonical
cast on every natural number. -/
theorem isInfinitePlace_iff_forall_natCast_eq {F : Type*} [Field F] {w : AbsoluteValue F ℝ} :
    IsInfinitePlace w ↔ ∀ n : ℕ, w n = n := by
  refine ⟨fun hw n ↦ ?_, fun hw ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := (isInfinitePlace_iff w).mp hw
    exact v.map_natCast n
  · have : CharZero F :=
      ⟨fun m n h ↦ Nat.cast_injective ((hw m).symm.trans ((congrArg w h).trans (hw n)))⟩
    have hint (z : ℤ) : w z = |z| := by
      obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
      · simp [hw n]
      · simp [hw n]
    have hlo : w.LiesOver Rat.infinitePlace.1 := by
      refine ⟨AbsoluteValue.ext fun q ↦ ?_⟩
      rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, eq_ratCast,
        ← InfinitePlace.coe_apply, Rat.infinitePlace_apply, ← Rat.num_div_den q]
      simp [hint, hw, abs_div]
    exact isInfinitePlace_of_liesOver Rat.infinitePlace w

-- On `ℚ`, `|·| ^ (1 / 2)` is an archimedean absolute value that is not an infinite place, showing
-- `isInfinitePlace_of_liesOver` requires `w.LiesOver v.1` on the nose rather than equivalence.
example : ∃ w : AbsoluteValue ℚ ℝ, ¬IsNonarchimedean w ∧ ¬IsInfinitePlace w := by
  refine ⟨{
    toFun := fun q ↦ |(q : ℝ)| ^ (1 / 2 : ℝ)
    map_mul' := fun x y ↦ by push_cast; rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    nonneg' := fun _ ↦ by positivity
    eq_zero' := fun x ↦ by simp
    add_le' := fun x y ↦ by
      push_cast
      exact (Real.rpow_le_rpow (abs_nonneg _) (abs_add_le _ _) (by norm_num)).trans
        (Real.rpow_add_le_add_rpow (abs_nonneg _) (abs_nonneg _) (by norm_num) (by norm_num))
  }, fun hna ↦ ?_, fun hinf ↦ ?_⟩
  · have h4 : |(4 : ℝ)| ^ (1 / 2 : ℝ) ≤ 1 := by
      simpa using hna.apply_natCast_le_one (n := 4) (by simp) (by simp)
    have : |(4 : ℝ)| ^ (1 / 2 : ℝ) = 2 := by
      rw [abs_of_pos (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  · have h4 : |(4 : ℝ)| ^ (1 / 2 : ℝ) = 4 := by
      simpa using (isInfinitePlace_iff_forall_natCast_eq.mp hinf) 4
    have : |(4 : ℝ)| ^ (1 / 2 : ℝ) = 2 := by
      rw [abs_of_pos (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith

end NumberField
