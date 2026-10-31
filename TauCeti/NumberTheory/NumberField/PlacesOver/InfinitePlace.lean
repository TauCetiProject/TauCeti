/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Algebra.GelfandMazur
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real
import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace

/-!
# Absolute values of an extension lying over an infinite place

Let `K` be a field, `v` an infinite place of `K` and `F / K` an arbitrary field extension. This file
shows that an absolute value `w : AbsoluteValue F ℝ` lying over `v`, in the sense of Mathlib's
`AbsoluteValue.LiesOver`, is an infinite place of `F` in the sense of Mathlib's `IsInfinitePlace`:
it is the absolute value `x ↦ ‖φ x‖` of a complex embedding `φ : F →+* ℂ`. Unlike over a finite
place, no root of a place is needed.

Together with the classification over a finite place in
`TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace`, this describes the absolute values of a
finite extension `F / K` of number fields lying over any place `v` of `K`: they form a finite
nonempty set, and they are nonarchimedean exactly when `v` is a finite place.

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value of a field extension `F / K` lying
  over an infinite place of `K` is an infinite place of `F`;
  `NumberField.liesOver_infinitePlace_iff` is the resulting classification.
* `NumberField.not_isNonarchimedean_of_liesOver_infinitePlace`: such an absolute value is
  archimedean.
* `NumberField.InfinitePlace.val_ne_finitePlace_val`: an infinite place and a finite place of a
  number field never have the same underlying absolute value.
* `NumberField.finite_setOf_liesOver` and `NumberField.nonempty_setOf_liesOver`: over a place of
  `K`, finite or infinite, a finite extension of number fields has a finite nonempty set of
  absolute values.
* `NumberField.isNonarchimedean_iff_isFinitePlace_of_liesOver`: an absolute value lying over a
  place `v` is nonarchimedean exactly when `v` is finite.

## Implementation notes

The completion `F_w` of `F` at `w` contains the completion `K_v` of `K` at `v` isometrically,
because `w` lies over `v`, and `K_v` contains `ℝ` isometrically, `InfinitePlace.Completion.ofReal`.
So `F_w` is a normed `ℝ`-algebra, and the isometric form of the Gelfand–Mazur theorem,
`NormedAlgebra.Real.exists_algHom_complex_isometry`, embeds it isometrically into `ℂ`. That theorem
asks neither for completeness nor for finite dimension, which is why `F / K` may be arbitrary.

The same classification, along the same route through the completion and Gelfand–Mazur, is
formalized in Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/PlacesOverInfinite.lean`
(Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open AbsoluteValue

namespace NumberField

section InfinitePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The real numbers inside the completion of `F` at an absolute value `w` lying over an infinite
place `v` of `K`, through the completion of `K` at `v`. -/
private noncomputable def ofRealCompletion (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ℝ →+* w.Completion :=
  (UniformSpace.Completion.mapRingHom (WithAbs.map v.1 w (algebraMap K F))
    (WithAbs.isometry_map v.1 w).continuous).comp
    ((InfinitePlace.Completion.equiv v : _ →+* _).comp (InfinitePlace.Completion.ofReal v))

private theorem norm_ofRealCompletion (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] (r : ℝ) : ‖ofRealCompletion v w r‖ = |r| := by
  simp only [ofRealCompletion, RingHom.comp_apply]
  rw [(UniformSpace.Completion.isometry_mapRingHom
    (WithAbs.isometry_map v.1 w)).norm_map_of_map_zero (map_zero _)]
  simp

/-- **Absolute values over an infinite place.** An absolute value `w` of a field extension `F` of
`K` lying over an infinite place of `K` is an infinite place of `F`, that is, the absolute value
`x ↦ ‖φ x‖` of a complex embedding `φ : F →+* ℂ`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  -- The completion of `F` at `w` is a normed `ℝ`-algebra through `ofRealCompletion`.
  let : Algebra ℝ w.Completion := (ofRealCompletion v w).toAlgebra
  let : NormedAlgebra ℝ w.Completion :=
    { norm_smul_le r y := by
        rw [Algebra.smul_def, norm_mul, RingHom.algebraMap_toAlgebra, norm_ofRealCompletion,
          Real.norm_eq_abs] }
  obtain ⟨ψ, hψ⟩ := NormedAlgebra.Real.exists_algHom_complex_isometry w.Completion
  refine ⟨(ψ : w.Completion →+* ℂ).comp
    (UniformSpace.Completion.coeRingHom.comp ((WithAbs.equiv w).symm : _ →+* _)),
    AbsoluteValue.ext fun x ↦ ?_⟩
  -- `coeRingHom` is the coercion into the completion, bundled as a ring homomorphism.
  have hcoe (y : WithAbs w) : UniformSpace.Completion.coeRingHom y = (y : w.Completion) := rfl
  simp only [place_apply, RingHom.comp_apply, AlgHom.coe_toRingHom]
  rw [hψ.norm_map_of_map_zero (map_zero ψ)]
  simp [hcoe, WithAbs.norm_toAbs_eq]

/-- An absolute value lying over an infinite place is archimedean. -/
theorem not_isNonarchimedean_of_liesOver_infinitePlace (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : ¬IsNonarchimedean w := fun hw ↦ by
  apply v.not_isNonarchimedean
  intro x y
  simpa only [← map_add, LiesOver.apply_algebraMap v.1] using
    hw (algebraMap K F x) (algebraMap K F y)

/-- **Absolute values over an infinite place.** An absolute value of a field extension `F` of `K`
lies over an infinite place `v` of `K` if and only if it is an infinite place of `F` lying over
`v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} {w : AbsoluteValue F ℝ} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨w', hw'⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
    subst hw'
    exact ⟨w', ‹_›, rfl⟩
  · rintro ⟨w', hw', rfl⟩
    exact hw'

variable (F)

/-- Every infinite place of a field `K` has an absolute value of any algebraic extension `F`
lying over it. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w', rfl⟩ := InfinitePlace.comap_surjective (K := F) v
  exact ⟨w'.1, InfinitePlace.liesOver_comap w'⟩

variable [NumberField F]

/-- A number field `F` has only finitely many absolute values lying over a given infinite place of
a field `K` below it. -/
theorem finite_setOf_liesOver_infinitePlace (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite :=
  (Set.finite_range fun w' : InfinitePlace F ↦ w'.1).subset fun _ hw ↦
    (liesOver_infinitePlace_iff.mp hw).imp fun _ ↦ And.right

end InfinitePlace

/-- An infinite place and a finite place of a number field never have the same underlying absolute
value: the first takes the value `2` at `2`, the second is at most `1` there. -/
theorem InfinitePlace.val_ne_finitePlace_val {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) (u : FinitePlace K) : v.1 ≠ u.1 :=
  fun h ↦ v.not_isNonarchimedean (h ▸ u.add_le)

section Place

variable {K F : Type*} [Field K] [Field F] [NumberField K] [Algebra K F] {v : AbsoluteValue K ℝ}

/-- An absolute value of a field extension of a number field lying over a place `v` of the base is
nonarchimedean if and only if `v` is a finite place. -/
theorem isNonarchimedean_iff_isFinitePlace_of_liesOver (hv : IsInfinitePlace v ∨ IsFinitePlace v)
    (w : AbsoluteValue F ℝ) [w.LiesOver v] : IsNonarchimedean w ↔ IsFinitePlace v := by
  rcases hv with ⟨φ, rfl⟩ | hv
  · -- The underlying absolute value of `InfinitePlace.mk φ` is `place φ` by definition.
    have : w.LiesOver (InfinitePlace.mk φ).1 := ‹_›
    refine iff_of_false (not_isNonarchimedean_of_liesOver_infinitePlace (InfinitePlace.mk φ) w) ?_
    rintro ⟨𝔭, h𝔭⟩
    exact InfinitePlace.val_ne_finitePlace_val (InfinitePlace.mk φ) (FinitePlace.mk 𝔭) h𝔭.symm
  · obtain ⟨u, rfl⟩ := (isFinitePlace_iff v).mp hv
    exact iff_of_true (isNonarchimedean_of_liesOver u.add_le) hv

variable (F) [NumberField F]

/-- A finite extension of number fields has only finitely many absolute values lying over a given
place, finite or infinite, of the base. -/
theorem finite_setOf_liesOver (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Finite := by
  rcases hv with ⟨φ, rfl⟩ | ⟨𝔭, rfl⟩
  · exact finite_setOf_liesOver_infinitePlace F (InfinitePlace.mk φ)
  · exact finite_setOf_liesOver_finitePlace_mk F 𝔭

/-- Every place, finite or infinite, of a number field `K` has an absolute value of a finite
extension of number fields lying over it. -/
theorem nonempty_setOf_liesOver (hv : IsInfinitePlace v ∨ IsFinitePlace v) :
    {w : AbsoluteValue F ℝ | w.LiesOver v}.Nonempty := by
  rcases hv with ⟨φ, rfl⟩ | ⟨𝔭, rfl⟩
  · exact nonempty_setOf_liesOver_infinitePlace F (InfinitePlace.mk φ)
  · exact nonempty_setOf_liesOver_finitePlace_mk F 𝔭

end Place

end NumberField
