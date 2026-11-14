/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.FinitePlace
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Mult

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Algebra.Real
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real

/-!
# Absolute values of a field extension lying over an infinite place

Let `F / K` be an arbitrary extension of fields and `v` an infinite place of `K`. This file
classifies the absolute values `w : AbsoluteValue F ℝ` lying over `v.1` in the sense of Mathlib's
`AbsoluteValue.LiesOver`, that is, whose restriction to `K` equals `v.1` on the nose: they are
precisely the underlying absolute values of the infinite places `w' : InfinitePlace F` lying over
`v` (`NumberField.isInfinitePlace_of_liesOver`,
`NumberField.existsUnique_infinitePlace_of_liesOver`, `NumberField.liesOver_infinitePlace_iff`).

In contrast to the finite-place case
(`TauCeti/NumberTheory/NumberField/PlacesOver/FinitePlace.lean`), no fractional root appears here:
`InfinitePlace F` stores unnormalized complex-modulus absolute values while the local degree `1` or
`2` is carried separately by `InfinitePlace.mult` and `InfinitePlace.inertiaDeg`. Moreover, the
classification itself requires neither `K` nor `F` to be a number field and does not even assume
`F / K` to be algebraic.

When `F / K` is algebraic, the fibre over `v` is nonempty
(`NumberField.InfinitePlace.nonempty_placesOver`,
`NumberField.nonempty_setOf_liesOver_infinitePlace`); when `F` is a number field, the fibre is
finite (`NumberField.InfinitePlace.finite_placesOver`,
`NumberField.finite_setOf_liesOver_infinitePlace`) and satisfies the local extension formulas
weighted either by `InfinitePlace.inertiaDeg` or by `InfinitePlace.mult`.

## Main definitions

* `NumberField.InfinitePlace.placesOverEquivAbsValues`: the equivalence between `v.placesOver F`
  and `{w : AbsoluteValue F ℝ // w.LiesOver v.1}` for an arbitrary field extension `F / K`.

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value of `F` lying over an infinite place
  of `K` is an infinite place of `F`.
* `NumberField.existsUnique_infinitePlace_of_liesOver` and `NumberField.liesOver_infinitePlace_iff`:
  bijective classification by infinite places of `F` lying over `v`.
* `NumberField.not_isNonarchimedean_of_liesOver_infinitePlace`: every absolute value lying over an
  infinite place is archimedean.
* `NumberField.exists_injective_infinitePlace_eq_of_liesOver`: absolute values chosen above a set
  of infinite places come from injective infinite places of `F`.
* `NumberField.InfinitePlace.nonempty_placesOver`,
  `NumberField.nonempty_setOf_liesOver_infinitePlace`,
  `NumberField.InfinitePlace.finite_placesOver`, and
  `NumberField.finite_setOf_liesOver_infinitePlace`: nonemptiness (for algebraic extensions) and
  finiteness (for number fields) of the fibre above an infinite place.
* `NumberField.InfinitePlace.prod_algebraMap_pow_inertiaDeg` and
  `NumberField.InfinitePlace.prod_algebraMap_pow_mult`: local extension formulas on base-field
  elements.

## Implementation notes

The completion `w.Completion` inherits a norm-preserving embedding of `ℝ` from `v.Completion` via
`NumberField.InfinitePlace.Completion.ofReal` and `AbsoluteValue.Completion.map`. The isometric
Gelfand–Mazur theorem (`NormedAlgebra.Real.exists_ringHom_complex_norm_eq`) then embeds
`w.Completion` isometrically into `ℂ`, realizing `w` as the infinite place attached to the
composite embedding `F →+* w.Completion →+* ℂ`.

The archimedean place classification via Gelfand–Mazur on `w.Completion` also appears in Ralf
Stephan's `rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file
`DiophantineApproximation/PlacesOverInfinite.lean` (Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §4 and §8.
-/

public section

open AbsoluteValue

namespace NumberField

section ArbitraryExtension

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Absolute values over an infinite place.** Let `F / K` be any field extension and `v` an
infinite place of `K`. Every absolute value `w` of `F` lying over `v.1` is an infinite place of
`F`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  let ι : ℝ →+* w.Completion :=
    (AbsoluteValue.Completion.map v.1 w).comp (InfinitePlace.Completion.ofReal v)
  let : Algebra ℝ w.Completion := ι.toAlgebra
  let : NormedAlgebra ℝ w.Completion :=
    { ι.toAlgebra with
      norm_smul_le r x := by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, norm_mul, RingHom.coe_comp,
          Function.comp_apply, AbsoluteValue.Completion.norm_map,
          InfinitePlace.Completion.norm_ofReal, Real.norm_eq_abs] }
  obtain ⟨ψ, -, hψ⟩ := NormedAlgebra.Real.exists_ringHom_complex_norm_eq w.Completion
  refine ⟨ψ.comp (algebraMap F w.Completion), AbsoluteValue.ext fun y ↦ ?_⟩
  rw [place_apply, RingHom.comp_apply, hψ, AbsoluteValue.Completion.algebraMap_def,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
    AbsoluteValue.Completion.norm_coe, WithAbs.ofAbs_toAbs]

/-- **Absolute values over an infinite place.** Let `F / K` be any field extension and `v` an
infinite place of `K`. An absolute value `w` of `F` lying over `v.1` is the underlying absolute
value of a unique infinite place `w'` of `F` lying over `v`. -/
theorem existsUnique_infinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ∃! w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  obtain ⟨w', hw'⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  have hlo : w'.LiesOver v := by
    rw [InfinitePlace.LiesOver, hw']
    infer_instance
  exact ⟨w', ⟨hlo, hw'⟩, fun u hu ↦ Subtype.ext (hu.2.trans hw'.symm)⟩

/-- An absolute value `w` of `F` lies over an infinite place `v` of `K` if and only if `w` is the
underlying absolute value of an infinite place of `F` lying over `v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} {w : AbsoluteValue F ℝ} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨fun _ ↦ (existsUnique_infinitePlace_of_liesOver v w).exists, ?_⟩
  rintro ⟨w', hw', rfl⟩
  exact hw'

/-- Every absolute value of `F` lying over an infinite place of `K` is archimedean. -/
theorem not_isNonarchimedean_of_liesOver_infinitePlace (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : ¬ IsNonarchimedean ⇑w :=
  (isInfinitePlace_of_liesOver v w).not_isNonarchimedean

/-- Absolute values chosen over distinct infinite places of `K` are the underlying absolute values
of distinct infinite places of `F` lying over them. -/
theorem exists_injective_infinitePlace_eq_of_liesOver
    (S : Set (InfinitePlace K)) (w : S → AbsoluteValue F ℝ)
    (hw : ∀ v, (w v).LiesOver v.val.1) :
    ∃ W : S → InfinitePlace F, Function.Injective W ∧
      ∀ v, (W v).LiesOver v.val ∧ (W v).1 = w v := by
  have hclass (v : S) :=
    let := hw v
    (existsUnique_infinitePlace_of_liesOver v.val (w v)).exists
  choose W hW using hclass
  refine ⟨W, fun v u hWu ↦ Subtype.ext ?_, hW⟩
  let := (hW v).1
  let := (hW u).1
  rw [← InfinitePlace.LiesOver.comap_eq (W v) v.val,
    ← InfinitePlace.LiesOver.comap_eq (W u) u.val, hWu]

namespace InfinitePlace

variable (F) in
/-- Infinite places of `F` above `v` correspond bijectively to absolute values of `F` restricting
to `v.1` on `K`, by taking the underlying absolute value. -/
def placesOverEquivAbsValues (v : InfinitePlace K) :
    v.placesOver F ≃ {w : AbsoluteValue F ℝ // w.LiesOver v.1} where
  toFun w := ⟨w.val.1, mem_placesOver.mp w.prop⟩
  invFun u :=
    let := u.prop
    ⟨⟨u.val, isInfinitePlace_of_liesOver v u.val⟩, u.prop⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- The forward direction of `placesOverEquivAbsValues` takes the underlying absolute value. -/
@[simp]
theorem placesOverEquivAbsValues_apply (v : InfinitePlace K) (w : v.placesOver F) :
    (placesOverEquivAbsValues F v w).val = w.val.1 :=
  (rfl)

/-- The inverse of `placesOverEquivAbsValues` produces an infinite place with the same underlying
absolute value. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply_val (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) :
    ((placesOverEquivAbsValues F v).symm w).val.1 = w.val :=
  (rfl)

/-- Evaluating the infinite place produced by `(placesOverEquivAbsValues F v).symm w` agrees with
evaluating `w`. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply_apply (v : InfinitePlace K)
    (w : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) (y : F) :
    ((placesOverEquivAbsValues F v).symm w).val y = w.val y :=
  (rfl)

end InfinitePlace

end ArbitraryExtension

section Algebraic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra.IsAlgebraic K F]

variable (F) in
/-- Every infinite place of `K` has an infinite place of an algebraic extension `F / K` lying over
it. -/
theorem InfinitePlace.nonempty_placesOver (v : InfinitePlace K) : (v.placesOver F).Nonempty := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := F) v
  exact ⟨w, InfinitePlace.mem_placesOver.mpr (InfinitePlace.liesOver_iff_comap_eq.mpr hw)⟩

variable (F) in
/-- Every infinite place of `K` has an absolute value of an algebraic extension `F / K` lying over
it. -/
theorem nonempty_setOf_liesOver_infinitePlace (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w, hw⟩ := v.nonempty_placesOver F
  exact ⟨w.1, InfinitePlace.mem_placesOver.mp hw⟩

end Algebraic

section NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]

variable (F) in
/-- Only finitely many infinite places of a number field `F` lie over a given infinite place of
`K`. -/
theorem InfinitePlace.finite_placesOver (v : InfinitePlace K) : (v.placesOver F).Finite :=
  Set.toFinite _

/-- When `F` is a number field, only finitely many absolute values of `F` lie over a given infinite
place of `K`. -/
instance InfinitePlace.instFiniteSubtypeLiesOver (v : InfinitePlace K) :
    Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1} :=
  Finite.of_equiv _ (InfinitePlace.placesOverEquivAbsValues F v)

variable (F) in
/-- A number field `F` over `K` has only finitely many absolute values lying over a given infinite
place of `K`. -/
theorem finite_setOf_liesOver_infinitePlace (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite :=
  Set.finite_coe_iff.mp (InfinitePlace.instFiniteSubtypeLiesOver v)

namespace InfinitePlace

attribute [local instance] Fintype.ofFinite

open scoped Classical in
/-- A multiplicity-weighted product over the absolute values of `F` above `v` equals the
multiplicity-weighted product over the infinite places of `F` above `v`. -/
theorem prod_apply_pow_mult (v : InfinitePlace K) (y : F) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val y ^ ((placesOverEquivAbsValues F v).symm w).val.mult) =
        ∏ w ∈ (v.placesOver F).toFinset, w y ^ w.mult := by
  classical
  have h := (placesOverEquivAbsValues F v).symm.prod_comp
    (fun w : v.placesOver F ↦ w.val y ^ w.val.mult)
  simpa only [placesOverEquivAbsValues_symm_apply_apply] using
    h.trans (Finset.prod_set_coe (f := fun w : InfinitePlace F ↦ w y ^ w.mult) (v.placesOver F))

open scoped Classical in
/-- A local-degree weighted product over the absolute values of `F` above `v` equals the
local-degree weighted product over the infinite places of `F` above `v`. -/
theorem prod_apply_pow_inertiaDeg (v : InfinitePlace K) (y : F) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val y ^ v.inertiaDeg ((placesOverEquivAbsValues F v).symm w).val) =
        ∏ w ∈ (v.placesOver F).toFinset, w y ^ v.inertiaDeg w := by
  classical
  have h := (placesOverEquivAbsValues F v).symm.prod_comp
    (fun w : v.placesOver F ↦ w.val y ^ v.inertiaDeg w.val)
  simpa only [placesOverEquivAbsValues_symm_apply_apply] using
    h.trans
      (Finset.prod_set_coe (f := fun w : InfinitePlace F ↦ w y ^ v.inertiaDeg w) (v.placesOver F))

open scoped Classical in
/-- **The local extension formula, multiplicity form.** On a base-field element, the product over
all absolute values of `F` above an infinite place `v`, weighted by `InfinitePlace.mult`, equals
`v x ^ (v.mult * [F : K])`. -/
theorem prod_algebraMap_pow_mult (v : InfinitePlace K) (x : K) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val (algebraMap K F x) ^ ((placesOverEquivAbsValues F v).symm w).val.mult) =
        v x ^ (v.mult * Module.finrank K F) := by
  classical
  have : CharZero K := (algebraMap K F).charZero
  have : NumberField K := NumberField.of_tower ℚ F K
  rw [prod_apply_pow_mult]
  calc
    ∏ w ∈ (v.placesOver F).toFinset, w (algebraMap K F x) ^ w.mult =
        ∏ w ∈ (v.placesOver F).toFinset, v x ^ w.mult := by
      refine Finset.prod_congr rfl fun w hw ↦ ?_
      have hlo : w.LiesOver v := mem_placesOver.mp (Set.mem_toFinset.mp hw)
      rw [InfinitePlace.coe_apply, LiesOver.apply_algebraMap v.1, ← InfinitePlace.coe_apply]
    _ = v x ^ (v.mult * Module.finrank K F) := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      convert sum_mult_eq_mult_mul_finrank F v

open scoped Classical in
/-- **The local extension formula, local-degree form.** On a base-field element, the product over
all absolute values of `F` above an infinite place `v`, weighted by the local degree
`v.inertiaDeg`, equals `v x ^ [F : K]`. -/
theorem prod_algebraMap_pow_inertiaDeg (v : InfinitePlace K) (x : K) :
    (∏ w : {w : AbsoluteValue F ℝ // w.LiesOver v.1},
      w.val (algebraMap K F x) ^ v.inertiaDeg ((placesOverEquivAbsValues F v).symm w).val) =
        v x ^ Module.finrank K F := by
  classical
  have : CharZero K := (algebraMap K F).charZero
  have : NumberField K := NumberField.of_tower ℚ F K
  rw [prod_apply_pow_inertiaDeg]
  calc
    ∏ w ∈ (v.placesOver F).toFinset, w (algebraMap K F x) ^ v.inertiaDeg w =
        ∏ w ∈ (v.placesOver F).toFinset, v x ^ v.inertiaDeg w := by
      refine Finset.prod_congr rfl fun w hw ↦ ?_
      have hlo : w.LiesOver v := mem_placesOver.mp (Set.mem_toFinset.mp hw)
      rw [InfinitePlace.coe_apply, LiesOver.apply_algebraMap v.1, ← InfinitePlace.coe_apply]
    _ = v x ^ Module.finrank K F := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      convert sum_inertiaDeg_eq_finrank K F v

end InfinitePlace

end NumberField

end NumberField
