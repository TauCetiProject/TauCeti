/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Currying continuous alternating maps without domain norms

This file provides the pointwise interior product for continuous alternating maps on topological
modules. It keeps the domain norm-free while retaining the algebraic linearity in the inserted
vector from `AlternatingMap.curryLeft`.

## Main declarations

* `ContinuousAlternatingMap.map_insertNth'`: the alternating insertion-sign formula.
* `ContinuousAlternatingMap.curryLeftTopological`: the norm-free interior product.
* `ContinuousAlternatingMap.curryLeftTopological_curryLeftTopological`: inserting the same vector
  twice gives zero.

The construction follows Mathlib's `AlternatingMap.curryLeft` and `map_insertNth`.

## References

* Yury Kudryashov's `DeRhamCohomology` project, whose alternating-map design informs the
  surrounding differential-form API.
-/

public section

namespace ContinuousAlternatingMap

section MapInsert
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- Inserting a vector into a continuous alternating map gives the usual alternating sign. -/
theorem map_insertNth' {n : ℕ} (f : M [⋀^Fin (n + 1)]→L[R] N) (p : Fin (n + 1))
    (x : M) (v : Fin n → M) :
    f (p.insertNth x v) = (-1 : ℤ) ^ (p : ℕ) • f (Matrix.vecCons x v) := by
  exact f.toAlternatingMap.map_insertNth p x v
end MapInsert

section Curry
variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousConstSMul R N]

/-- The pointwise interior product obtained by fixing the first vector argument.

This is the norm-free companion to Mathlib's normed `ContinuousAlternatingMap.curryLeft`: it is
linear in the inserted vector because it is bundled as a linear map, while continuity is required
only in the remaining alternating arguments. -/
noncomputable def curryLeftTopological {n : ℕ}
    (f : M [⋀^Fin (n + 1)]→L[R] N) : M →ₗ[R] M [⋀^Fin n]→L[R] N where
  toFun x :=
    { toMultilinearMap :=
        (AlternatingMap.curryLeft (R := R) f.toAlternatingMap x).toMultilinearMap
      cont := by
        apply f.cont.comp
        exact continuous_const.matrixVecCons continuous_id
      map_eq_zero_of_eq' :=
        (AlternatingMap.curryLeft (R := R) f.toAlternatingMap x).map_eq_zero_of_eq' }
  map_add' x y := by
    ext v
    exact f.toAlternatingMap.map_vecCons_add v x y
  map_smul' c x := by
    ext v
    exact f.toAlternatingMap.map_vecCons_smul v c x

@[simp]
theorem curryLeftTopological_apply_apply {n : ℕ} (f : M [⋀^Fin (n + 1)]→L[R] N) (x : M)
    (v : Fin n → M) : curryLeftTopological f x v = f (Matrix.vecCons x v) := by
  rfl

@[simp]
theorem toAlternatingMap_curryLeftTopological {n : ℕ} (f : M [⋀^Fin (n + 1)]→L[R] N) (x : M) :
    (curryLeftTopological f x).toAlternatingMap = f.toAlternatingMap.curryLeft x := by
  rfl

@[simp]
theorem curryLeftTopological_zero {n : ℕ} :
    curryLeftTopological (0 : M [⋀^Fin (n + 1)]→L[R] N) = 0 := by
  ext x v
  simp

@[simp]
theorem curryLeftTopological_add {n : ℕ} (f g : M [⋀^Fin (n + 1)]→L[R] N) :
    curryLeftTopological (f + g) = curryLeftTopological f + curryLeftTopological g := by
  ext x v
  simp

@[simp]
theorem curryLeftTopological_smul {n : ℕ} (c : R) (f : M [⋀^Fin (n + 1)]→L[R] N) :
    curryLeftTopological (c • f) = c • curryLeftTopological f := by
  ext x v
  simp

@[simp]
theorem curryLeftTopological_curryLeftTopological {n : ℕ}
    (f : M [⋀^Fin (n + 2)]→L[R] N) (x : M) :
    curryLeftTopological (curryLeftTopological f x) x = 0 := by
  apply toAlternatingMap_injective
  simp

end Curry

end ContinuousAlternatingMap
