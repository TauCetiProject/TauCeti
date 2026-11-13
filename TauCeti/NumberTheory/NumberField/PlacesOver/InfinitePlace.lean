/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Algebra.GelfandMazur

/-!
# Absolute values of an extension lying over an infinite place

Let `F / K` be a field extension and `v` an infinite place of `K`. This file shows that every
absolute value `w : AbsoluteValue F ℝ` lying over `v`, in the sense of Mathlib's
`AbsoluteValue.LiesOver`, is an infinite place of `F`: it is `x ↦ ‖φ x‖` for a ring homomorphism
`φ : F →+* ℂ`. So the absolute values over `v` are exactly the underlying absolute values of the
infinite places of `F` over `v`. Unlike the case of a finite place, no root is taken: restricting
an infinite place of `F` to `K` gives an infinite place of `K` on the nose.

The argument runs in the completion `F_w` of `F` at `w`. Through `v`, the completion contains an
isometric copy of `K_v`, which is `ℝ` or `ℂ` by `InfinitePlace.Completion.ringEquivRealOfIsReal`
and `InfinitePlace.Completion.ringEquivComplexOfIsComplex`; in both cases `F_w` is a normed field
which is a normed `ℝ`-algebra. The isometric form of the Gelfand–Mazur theorem,
`NormedAlgebra.Real.exists_algHom_complex_norm_eq`, then embeds `F_w` isometrically into `ℂ`.
Neither `F` nor the completion is assumed finite-dimensional.

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value lying over an infinite place is an
  infinite place.
* `NumberField.InfinitePlace.image_val_placesOver`: the absolute values of `F` lying over `v` are
  exactly the underlying absolute values of the infinite places of `F` over `v`.
* `NumberField.finite_setOf_liesOver_infinitePlace` and
  `NumberField.nonempty_setOf_liesOver_infinitePlace`: for a number field, respectively an
  algebraic extension, these absolute values form a finite, respectively nonempty, set.
* `NumberField.InfinitePlace.exists_liesOver_of_liesOver`: such an absolute value extends to every
  algebraic extension of `F`.
* `NumberField.not_isNonarchimedean_of_liesOver_infinitePlace`: such an absolute value is
  archimedean.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The completion of `F` at an absolute value lying over an infinite place contains a copy of
`ℝ` on which its norm is the absolute value of `ℝ`. -/
private theorem exists_ringHom_real_completion_norm_eq (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ ψ : ℝ →+* w.Completion, ∀ r, ‖ψ r‖ = ‖r‖ := by
  -- The completion of `K` at `v` embeds isometrically into the completion of `F` at `w`.
  let ι : v.Completion →+* w.Completion :=
    (Completion.map v.1 w).comp (InfinitePlace.Completion.equiv v).toRingHom
  have hι (x : v.Completion) : ‖ι x‖ = ‖x‖ :=
    (Completion.isometry_map v.1 w).norm_map_of_map_zero (map_zero _) _
  rcases v.isReal_or_isComplex with hv | hv
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    refine ⟨ι.comp e.symm.toRingHom, fun r ↦ ?_⟩
    rw [RingHom.comp_apply, hι,
      ← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _),
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, e.apply_symm_apply]
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    refine ⟨ι.comp (e.symm.toRingHom.comp Complex.ofRealHom), fun r ↦ ?_⟩
    rw [RingHom.comp_apply, hι,
      ← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
      ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, e.apply_symm_apply, Complex.ofRealHom_eq_coe,
      Complex.norm_real]

/-- An absolute value of `F` lying over an infinite place of `K` is an infinite place of `F`:
it is `x ↦ ‖φ x‖` for a ring homomorphism `φ : F →+* ℂ`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  obtain ⟨ψ, hψ⟩ := exists_ringHom_real_completion_norm_eq v w
  let _ : Algebra ℝ w.Completion := ψ.toAlgebra
  let _ : NormedAlgebra ℝ w.Completion :=
    { norm_smul_le r x := by
        rw [Algebra.smul_def, norm_mul, RingHom.algebraMap_toAlgebra, hψ] }
  obtain ⟨φ, hφ⟩ := NormedAlgebra.Real.exists_algHom_complex_norm_eq w.Completion
  refine ⟨φ.toRingHom.comp (algebraMap F w.Completion), AbsoluteValue.ext fun x ↦ ?_⟩
  rw [place_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφ,
    Completion.algebraMap_def, Completion.norm_coe, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, WithAbs.ofAbs_toAbs]

namespace InfinitePlace

variable (F) in
/-- The absolute values of `F` lying over an infinite place `v` of `K` are exactly the underlying
absolute values of the infinite places of `F` over `v`. -/
theorem image_val_placesOver (v : InfinitePlace K) :
    Subtype.val '' v.placesOver F = {w : AbsoluteValue F ℝ | w.LiesOver v.1} := by
  ext w
  refine ⟨fun ⟨_, hw', hw⟩ ↦ hw ▸ hw', fun (hw : w.LiesOver v.1) ↦ ?_⟩
  obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  exact ⟨w', hw, rfl⟩

end InfinitePlace

variable (F)

/-- A number field has only finitely many absolute values lying over a given infinite place of
a subfield. -/
theorem finite_setOf_liesOver_infinitePlace [NumberField F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite := by
  rw [← InfinitePlace.image_val_placesOver]
  exact ((Set.finite_univ (α := InfinitePlace F)).subset (Set.subset_univ _)).image _

/-- Every infinite place of the base has an absolute value of an algebraic extension lying over
it. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := F) v
  refine ⟨w.1, ⟨AbsoluteValue.ext fun x ↦ ?_⟩⟩
  rw [under_apply, ← hw, ← InfinitePlace.coe_apply, ← InfinitePlace.coe_apply,
    InfinitePlace.comap_apply]

variable {F}

/-- An absolute value lying over an infinite place extends to every algebraic extension. -/
theorem InfinitePlace.exists_liesOver_of_liesOver {E : Type*} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] (v : InfinitePlace K) (w : AbsoluteValue F ℝ) [w.LiesOver v.1] :
    ∃ u : AbsoluteValue E ℝ, u.LiesOver w := by
  obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
  exact nonempty_setOf_liesOver_infinitePlace E w'

/-- An absolute value lying over an infinite place is archimedean: it takes the value `2`
at `2`. -/
theorem not_isNonarchimedean_of_liesOver_infinitePlace (v : InfinitePlace K)
    (w : AbsoluteValue F ℝ) [w.LiesOver v.1] : ¬IsNonarchimedean w := fun hw ↦ by
  have h2 : w 2 = 2 := by
    rw [← map_ofNat (algebraMap K F), LiesOver.apply_algebraMap v.1, ← InfinitePlace.coe_apply,
      ← v.norm_embedding_eq, map_ofNat, Complex.norm_ofNat]
  have := (isNonarchimedean_iff_forall_natCast_le_one.mp hw) 2
  norm_num [Nat.cast_ofNat, h2] at this

end NumberField
