/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Analysis.AbsoluteValue.Complex
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Real

/-!
# Absolute values of an extension lying over an infinite place

Let `F / K` be a field extension and `v` an infinite place of `K`. This file shows that an
absolute value `w : AbsoluteValue F ℝ` lying over `v`, in the sense of Mathlib's
`AbsoluteValue.LiesOver`, that is, whose restriction to `K` is `v` on the nose, is the absolute
value of an infinite place of `F`: there is a ring homomorphism `φ : F →+* ℂ` with
`w = ‖φ ·‖`. Unlike the classification over a finite place, no power of a place appears, and no
finiteness or algebraicity of `F / K` is needed.

Together with the classification over a finite place this lets statements about a finite
extension take an absolute value lying over a place of the base without passing to a completion.

## Main results

* `NumberField.isInfinitePlace_of_liesOver`: an absolute value lying over an infinite place is an
  infinite place.
* `NumberField.liesOver_infinitePlace_iff`: the absolute values of `F` lying over an infinite
  place `v` of `K` are exactly the underlying absolute values of the infinite places of `F` lying
  over `v`.
* `NumberField.finite_setOf_liesOver_infinitePlace` and
  `NumberField.nonempty_setOf_liesOver_infinitePlace`: when `F` is a number field, they form a
  finite set, and when `F / K` is algebraic, a nonempty one.

## Implementation notes

The argument takes place in the completion `F_w` of `F` at `w`. The completion `K_v` of `K` at `v`
contains a copy of `ℝ`, `NumberField.InfinitePlace.Completion.ofReal`, and since `w` lies over `v`
the inclusion `K → F` extends to an isometry `K_v → F_w`. This makes `F_w` a normed `ℝ`-algebra
and a normed field, hence isometric to a subfield of `ℂ` by the isometric form of the
Gelfand–Mazur theorem, `NormedAlgebra.Real.exists_algHom_complex_isometry`, which asks neither for
completeness nor for finite dimension.

The same argument through the completion and Gelfand–Mazur is formalized in Ralf Stephan's
`rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file
`DiophantineApproximation/PlacesOverInfinite.lean` (Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Absolute values over an infinite place.** An absolute value of an extension field `F` of `K`
lying over an infinite place of `K` is the absolute value of an infinite place of `F`. -/
theorem isInfinitePlace_of_liesOver (v : InfinitePlace K) (w : AbsoluteValue F ℝ)
    [w.LiesOver v.1] : IsInfinitePlace w := by
  -- The copy of `ℝ` in `K_v`, carried into `F_w` along the completion of `K → F`.
  let ι : ℝ →+* w.Completion :=
    (UniformSpace.Completion.mapRingHom (WithAbs.map v.1 w (algebraMap K F))
      (WithAbs.isometry_map v.1 w).continuous).comp
        ((InfinitePlace.Completion.equiv v).toRingHom.comp (InfinitePlace.Completion.ofReal v))
  have hι (r : ℝ) : ‖ι r‖ = ‖r‖ := by
    rw [RingHom.comp_apply, (UniformSpace.Completion.isometry_mapRingHom
      (WithAbs.isometry_map v.1 w)).norm_map_of_map_zero (map_zero _)]
    simp
  let _ : Algebra ℝ w.Completion := ι.toAlgebra
  let _ : NormedAlgebra ℝ w.Completion :=
    { norm_smul_le r x := by
        rw [Algebra.smul_def, norm_mul, RingHom.algebraMap_toAlgebra, hι] }
  obtain ⟨ψ, hψ⟩ := NormedAlgebra.Real.exists_algHom_complex_isometry w.Completion
  refine ⟨ψ.toRingHom.comp
    (UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv w).symm.toRingHom), ?_⟩
  ext x
  simp [hψ.norm_map_of_map_zero (map_zero ψ), UniformSpace.Completion.coeRingHom,
    WithAbs.norm_toAbs_eq]

/-- **Absolute values over an infinite place.** The absolute values of an extension field `F` of
`K` lying over an infinite place `v` of `K` are exactly the underlying absolute values of the
infinite places of `F` lying over `v`. -/
theorem liesOver_infinitePlace_iff {v : InfinitePlace K} {w : AbsoluteValue F ℝ} :
    w.LiesOver v.1 ↔ ∃ w' : InfinitePlace F, w'.LiesOver v ∧ w'.1 = w := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨w', rfl⟩ := (isInfinitePlace_iff w).mp (isInfinitePlace_of_liesOver v w)
    exact ⟨w', ‹_›, rfl⟩
  · rintro ⟨w', hw', rfl⟩
    exact hw'

/-- An extension `F` of `K` that is a number field has only finitely many absolute values lying
over a given infinite place of `K`. -/
theorem finite_setOf_liesOver_infinitePlace [NumberField F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Finite :=
  (Set.finite_range fun w' : InfinitePlace F ↦ w'.1).subset
    fun _ hw ↦ by
      obtain ⟨w', -, rfl⟩ := liesOver_infinitePlace_iff.mp hw
      exact ⟨w', rfl⟩

/-- Every infinite place of `K` has an absolute value of an algebraic extension lying over it,
namely the absolute value of an infinite place of the extension. -/
theorem nonempty_setOf_liesOver_infinitePlace [Algebra.IsAlgebraic K F] (v : InfinitePlace K) :
    {w : AbsoluteValue F ℝ | w.LiesOver v.1}.Nonempty := by
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := F) v
  exact ⟨w.1, InfinitePlace.liesOver_iff_comap_eq.mpr rfl⟩

end NumberField
