/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import TauCeti.Analysis.AbsoluteValue.Complex
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real
import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace

/-!
# Absolute values lying over an infinite place

Let `F / K` be an extension of fields and `v` an infinite place of `K`. Every real-valued absolute
value `w` of `F` lying over `v.1` (`[w.LiesOver v.1]`) is the underlying absolute value of a unique
infinite place `w'` of `F` lying over `v` (`NumberField.isInfinitePlace_of_liesOver`,
`NumberField.existsUnique_infinitePlace_eq_of_liesOver`). Unlike at finite places
(`NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`), no fractional exponent appears:
archimedean places restrict without local-degree powers, while multiplicities enter only in global
products.

## Proof outline

The classification runs in the completion `w.Completion`, without assuming `K` or `F` to be number
fields or `F / K` to be algebraic:
1. `InfinitePlace.Completion.ofReal v : ℝ →+* v.Completion` embeds `ℝ` isometrically into `v`'s
   completion, and `AbsoluteValue.Completion.map v.1 w : v.Completion →+* w.Completion` is an
   isometric ring homomorphism, giving a norm-preserving ring homomorphism `ℝ →+* w.Completion`.
2. By `NormedField.exists_ringHom_complex_norm_eq` (the real Gelfand–Mazur theorem combined with
   `AbsoluteValue.eq_norm_of_apply_ofReal`), `w.Completion` admits a norm-preserving ring
   homomorphism into `ℂ`.
3. Composing with `algebraMap F w.Completion` gives a complex embedding `φ : F →+* ℂ` with
   `place φ = w`.

Combining the archimedean and nonarchimedean classifications gives the place-level consequences for
extensions of number fields: disjointness of infinite and finite places
(`NumberField.InfinitePlace.val_ne_finitePlace_val`), characterization of nonarchimedean extensions
(`NumberField.isNonarchimedean_iff_isFinitePlace_of_liesOver`), and finiteness and nonemptiness of
the fibre `{w : AbsoluteValue F ℝ | w.LiesOver v}` above every place of `K`.

The classification statement `NumberField.isInfinitePlace_of_liesOver` and the place-level
consequences correspond to those in Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, files
`DiophantineApproximation/PlacesOverInfinite.lean` and `DiophantineApproximation/PlacesOver.lean`
(Apache 2.0), proved here for arbitrary field extensions via `InfinitePlace.Completion.ofReal` and
`NormedField.exists_ringHom_complex_norm_eq`.

## Main definitions

* `NumberField.InfinitePlace.placesOverEquivAbsValues`: the bijection between `v.placesOver F` and
  `{w : AbsoluteValue F ℝ // w.LiesOver v.1}` for an infinite place `v` of `K` and any field
  extension `F / K`.

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value of `F` lying over an infinite place
  of `K` is an infinite place of `F`, for any field extension `F / K`.
* `NumberField.existsUnique_infinitePlace_eq_of_liesOver`,
  `NumberField.liesOver_infinitePlace_iff`,
  `NumberField.exists_injective_infinitePlace_eq_of_liesOver`, and
  `NumberField.InfinitePlace.image_val_placesOver`: characterization of absolute values of a field
  extension `F / K` lying over infinite places of `K`.
* `NumberField.InfinitePlace.finite_placesOver` and
  `NumberField.finite_setOf_liesOver_infinitePlace`: finiteness of infinite places and absolute
  values above `v` for a finite field extension `F / K` (`[FiniteDimensional K F]`).
* `NumberField.InfinitePlace.nonempty_placesOver` and
  `NumberField.nonempty_setOf_liesOver_infinitePlace`: nonemptiness above `v` for an algebraic
  field extension `F / K` (`[Algebra.IsAlgebraic K F]`).
* `NumberField.InfinitePlace.val_ne_finitePlace_val` and
  `NumberField.IsInfinitePlace.not_isFinitePlace`: an infinite place and a finite place of a number
  field never have the same underlying absolute value.
* `NumberField.not_isNonarchimedean_of_liesOver_infinitePlace` and
  `NumberField.isNonarchimedean_iff_isFinitePlace_of_liesOver`: an absolute value on a faithful
  `K`-algebra lying over an infinite place of `K` is archimedean, and for an infinite or finite
  place `v` of a number field `K` and an absolute value `w` on a field extension `F / K` lying over
  `v`, `w` is nonarchimedean if and only if `v` is a finite place.
* `NumberField.finite_setOf_liesOver` and `NumberField.nonempty_setOf_liesOver`: finiteness and
  nonemptiness of `{w : AbsoluteValue F ℝ | w.LiesOver v}` for an infinite or finite place `v` of a
  number field `K` and a number field extension `F / K`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

namespace NumberField

section FieldExtension

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Absolute values over an infinite place.** For any field extension `F / K`, an absolute value
`w` of `F` lying over an infinite place `v` of `K` is an infinite place of `F`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  let f : ℝ →+* w.Completion :=
    (AbsoluteValue.Completion.map v.1 w).comp (InfinitePlace.Completion.ofReal v)
  obtain ⟨φ, hφ⟩ := NormedField.exists_ringHom_complex_norm_eq f fun r ↦ by
    rw [RingHom.comp_apply, AbsoluteValue.Completion.norm_map,
      InfinitePlace.Completion.norm_ofReal]
  refine ⟨φ.comp (algebraMap F w.Completion), AbsoluteValue.ext fun x ↦ ?_⟩
  rw [place_apply, RingHom.comp_apply, hφ, AbsoluteValue.Completion.algebraMap_def]
  exact AbsoluteValue.Completion.norm_coe (WithAbs.toAbs w x)

/-- An absolute value `w` of a field extension `F / K` lying over an infinite place `v` of `K` is
the underlying absolute value of a unique infinite place of `F` lying over `v`. -/
theorem existsUnique_infinitePlace_eq_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] :
    ∃! w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨⟨w, isInfinitePlace_of_liesOver v w⟩, ⟨⟨‹w.LiesOver v.1›.1⟩, rfl⟩, ?_⟩
  rintro w' ⟨-, rfl⟩
  rfl

/-- An absolute value `w` of a field extension `F / K` lies over `v.1` for an infinite place `v` of
`K` if and only if it is the underlying absolute value of an infinite place of `F` lying over
`v`. -/
theorem liesOver_infinitePlace_iff (v : InfinitePlace K) (w : AbsoluteValue F ℝ) :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨fun _ ↦ (existsUnique_infinitePlace_eq_of_liesOver v w).exists, ?_⟩
  rintro ⟨w', hw', rfl⟩
  have := hw'
  infer_instance

/-- Absolute values of a field extension `F / K` lying over distinct infinite places in a set `S`
come from distinct infinite places of `F` lying over them. -/
theorem exists_injective_infinitePlace_eq_of_liesOver (S : Set (InfinitePlace K))
    (w : S → AbsoluteValue F ℝ) (hw : ∀ v, (w v).LiesOver v.val.1) :
    ∃ V : S → InfinitePlace F, Function.Injective V ∧
      ∀ v, (V v).LiesOver v.val ∧ (V v).1 = w v := by
  let V : S → InfinitePlace F := fun v ↦
    ⟨w v, @isInfinitePlace_of_liesOver K F _ _ _ v.val (w v) (hw v)⟩
  have hover (v : S) : (V v).LiesOver v.val := ⟨(hw v).1⟩
  refine ⟨V, fun v u h ↦ Subtype.ext ?_, fun v ↦ ⟨hover v, rfl⟩⟩
  let := hover v
  let := hover u
  rw [← InfinitePlace.LiesOver.comap_eq (V v) v.val,
    ← InfinitePlace.LiesOver.comap_eq (V u) u.val, h]

end FieldExtension

namespace InfinitePlace

section FieldExtension

variable {K : Type*} [Field K]

/-- Infinite places of a field extension `F` above an infinite place `v` of `K` correspond
bijectively to absolute values of `F` lying over `v.1`, by taking the underlying absolute value. -/
def placesOverEquivAbsValues (F : Type*) [Field F] [Algebra K F] (v : InfinitePlace K) :
    v.placesOver F ≃ {w : AbsoluteValue F ℝ // w.LiesOver v.1} where
  toFun w := ⟨w.1.1, ⟨w.2.1⟩⟩
  invFun u :=
    letI : u.1.LiesOver v.1 := u.2
    ⟨⟨u.1, NumberField.isInfinitePlace_of_liesOver v u.1⟩, ⟨u.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `placesOverEquivAbsValues` sends an infinite place over `v` to its underlying absolute value. -/
@[simp]
theorem placesOverEquivAbsValues_apply {F : Type*} [Field F] [Algebra K F]
    (v : InfinitePlace K) (w : v.placesOver F) :
    (v.placesOverEquivAbsValues F w).1 = w.1.1 :=
  (rfl)

/-- The inverse of `placesOverEquivAbsValues` recovers the given absolute value. -/
@[simp]
theorem placesOverEquivAbsValues_symm_apply {F : Type*} [Field F] [Algebra K F]
    (v : InfinitePlace K) (u : {w : AbsoluteValue F ℝ // w.LiesOver v.1}) :
    ((v.placesOverEquivAbsValues F).symm u).1.1 = u.1 :=
  (rfl)

/-- The image of `v.placesOver F` under `Subtype.val` is the set of absolute values of `F` lying
over `v.1`. -/
theorem image_val_placesOver (F : Type*) [Field F] [Algebra K F] (v : InfinitePlace K) :
    (Subtype.val : InfinitePlace F → AbsoluteValue F ℝ) '' v.placesOver F =
      {w : AbsoluteValue F ℝ | w.LiesOver v.1} :=
  Set.ext fun w ↦ (liesOver_infinitePlace_iff v w).symm

/-- Only finitely many infinite places of a finite field extension `F / K` lie over a given
infinite place of `K`. -/
theorem finite_placesOver (F : Type*) [Field F] [Algebra K F] [FiniteDimensional K F]
    (v : InfinitePlace K) : (v.placesOver F).Finite := by
  let : Algebra K ℂ := v.embedding.toAlgebra
  refine (Set.finite_range fun σ : F →ₐ[K] ℂ ↦ mk σ.toRingHom).subset fun w hw ↦ ?_
  let : w.LiesOver v := hw
  rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
  · exact ⟨⟨w.embedding, fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← h]⟩, mk_embedding w⟩
  · exact ⟨⟨ComplexEmbedding.conjugate w.embedding,
      fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← h]⟩,
      (mk_conjugate_eq w.embedding).trans (mk_embedding w)⟩

/-- The type of infinite places of a finite field extension `F / K` above an infinite place of `K`
is finite. -/
instance {F : Type*} [Field F] [Algebra K F] [FiniteDimensional K F] (v : InfinitePlace K) :
    Finite (v.placesOver F) :=
  (v.finite_placesOver F).to_subtype

/-- The fibre of absolute values of a finite field extension `F / K` above an infinite place of `K`
is finite. -/
instance {F : Type*} [Field F] [Algebra K F] [FiniteDimensional K F] (v : InfinitePlace K) :
    Finite {w : AbsoluteValue F ℝ // w.LiesOver v.1} :=
  Finite.of_equiv _ (v.placesOverEquivAbsValues F)

/-- Every infinite place of `K` has an infinite place of an algebraic field extension `F / K` lying
over it. -/
theorem nonempty_placesOver (F : Type*) [Field F] [Algebra K F] [Algebra.IsAlgebraic K F]
    (v : InfinitePlace K) : (v.placesOver F).Nonempty := by
  obtain ⟨w, rfl⟩ := comap_surjective (K := F) v
  exact ⟨w, liesOver_comap w⟩

end FieldExtension

/-- An infinite place and a finite place of a number field never have the same underlying absolute
value. -/
theorem val_ne_finitePlace_val {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) (u : FinitePlace K) : v.1 ≠ u.1 :=
  fun h ↦ v.not_isNonarchimedean (h ▸ u.add_le)

end InfinitePlace

/-- A finite field extension `F / K` has only finitely many absolute values lying over a given
infinite place of `K`. -/
theorem finite_setOf_liesOver_infinitePlace {K : Type*} [Field K] (F : Type*) [Field F]
    [Algebra K F] [FiniteDimensional K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  rw [← v.image_val_placesOver F]
  exact (v.finite_placesOver F).image _

/-- Every infinite place of `K` has an absolute value of an algebraic field extension `F / K` lying
over it. -/
theorem nonempty_setOf_liesOver_infinitePlace {K : Type*} [Field K] (F : Type*) [Field F]
    [Algebra K F] [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  rw [← v.image_val_placesOver F]
  exact (v.nonempty_placesOver F).image _

/-- An absolute value on a faithful `K`-algebra lying over an infinite place of `K` is archimedean
(not nonarchimedean). -/
theorem not_isNonarchimedean_of_liesOver_infinitePlace {K F : Type*} [Field K] [Semiring F]
    [Algebra K F] [FaithfulSMul K F] (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ¬ IsNonarchimedean w := by
  intro hw
  have : Nontrivial F := (FaithfulSMul.algebraMap_injective K F).nontrivial
  have h2 : w (algebraMap K F (2 : ℕ)) ≤ 1 := by
    rw [map_natCast]
    exact hw.apply_natCast_le_one (n := 2) (by simp) w.map_one
  rw [AbsoluteValue.LiesOver.apply_algebraMap v.1, ← InfinitePlace.coe_apply, v.map_natCast] at h2
  norm_num at h2

/-- An infinite place of a number field is not a finite place. -/
theorem IsInfinitePlace.not_isFinitePlace {K : Type*} [Field K] [NumberField K]
    {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v) : ¬ IsFinitePlace v := by
  rintro ⟨𝔭, rfl⟩
  obtain ⟨w, h⟩ := (isInfinitePlace_iff _).mp hv
  exact w.val_ne_finitePlace_val (FinitePlace.mk 𝔭) h

/-- Let `v` be an infinite or finite place of a number field `K` and `w` an absolute value on a
field extension `F / K` lying over `v`. Then `w` is nonarchimedean if and only if `v` is a finite
place. -/
theorem isNonarchimedean_iff_isFinitePlace_of_liesOver {K F : Type*} [Field K] [NumberField K]
    [Field F] [Algebra K F] {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] :
    IsNonarchimedean w ↔ IsFinitePlace v := by
  rw [isFinitePlace_iff]
  refine ⟨fun hw ↦ (hv.imp (isInfinitePlace_iff v).mp (isFinitePlace_iff v).mp).resolve_left ?_,
    ?_⟩
  · rintro ⟨u, rfl⟩
    exact not_isNonarchimedean_of_liesOver_infinitePlace u w hw
  · rintro ⟨u, rfl⟩
    exact AbsoluteValue.isNonarchimedean_of_liesOver u.add_le

section NumberFieldExtension

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

variable (F) in
/-- For a finite extension `F / K` of number fields, only finitely many absolute values of `F` lie
over a given infinite or finite place of `K`. -/
theorem finite_setOf_liesOver {v : AbsoluteValue K ℝ} (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite := by
  rcases hv with ⟨φ, rfl⟩ | ⟨𝔭, rfl⟩
  · exact finite_setOf_liesOver_infinitePlace F (InfinitePlace.mk φ)
  · exact finite_setOf_liesOver_finitePlace_mk F 𝔭

variable (F) in
/-- For a finite extension `F / K` of number fields, every infinite or finite place of `K` has an
absolute value of `F` lying over it. -/
theorem nonempty_setOf_liesOver {v : AbsoluteValue K ℝ}
    (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with ⟨φ, rfl⟩ | ⟨𝔭, rfl⟩
  · exact nonempty_setOf_liesOver_infinitePlace F (InfinitePlace.mk φ)
  · exact nonempty_setOf_liesOver_finitePlace_mk F 𝔭

end NumberFieldExtension

end NumberField
