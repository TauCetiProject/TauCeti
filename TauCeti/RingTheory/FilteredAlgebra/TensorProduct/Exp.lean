/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic

import TauCeti.RingTheory.FilteredAlgebra.Exp.Map

/-!
# Completed exponentials and logarithms in completed tensor products

For two filtered `R`-algebras `A` and `B`, the completed tensor inclusions `includeLeftCompletion`
and `includeRightCompletion` preserve every filtration order and therefore commute with
`completedExp` and `completedLog` whenever the source and tensor algebras are rational algebras.
Since the images of the two completed inclusions commute, completed pure tensors send pairs of
completed exponentials to the completed exponential of the sum of their completed inclusions, and
completed logarithms turn completed pure tensors of elements congruent to one into sums of
completed inclusions.

## Main results

* `TauCeti.AlgFiltration.includeLeftCompletion_completedExp` and
  `TauCeti.AlgFiltration.includeRightCompletion_completedExp`: the completed tensor inclusions
  commute with `completedExp`.
* `TauCeti.AlgFiltration.includeLeftCompletion_completedLog` and
  `TauCeti.AlgFiltration.includeRightCompletion_completedLog`: the completed tensor inclusions
  commute with `completedLog`.
* `TauCeti.AlgFiltration.completedTensor_completedExp`:
  `completedTensor (completedExp x) (completedExp y) = completedExp (ι₁ x + ι₂ y)`.
* `TauCeti.AlgFiltration.completedLog_completedTensor`:
  `completedLog (completedTensor u v) = ι₁ (completedLog u) + ι₂ (completedLog v)`.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

variable (R : Type*) {A B : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] (F : AlgFiltration A) (G : AlgFiltration B)

/-- The completed left tensor inclusion commutes with the completed exponential. -/
@[simp]
theorem includeLeftCompletion_completedExp [Algebra ℚ A] [Algebra ℚ (A ⊗[R] B)]
    (x : F.completionIdeal 1) :
    F.includeLeftCompletion R G (F.completedExp x) = (F.tensorProduct R G).completedExp
      ⟨F.includeLeftCompletion R G x,
        F.includeLeftCompletion_mem_completionIdeal R G x.property⟩ := by
  simpa only [includeLeftCompletion_eq_mapCompletionₐ] using F.mapCompletionₐ_completedExp
    (F.tensorProduct R G) Algebra.TensorProduct.includeLeft id monotone_id
    (fun k => F.ideal_le_comap_includeLeft R G (k + 1)) (F.ideal_le_comap_includeLeft R G 1) x

/-- The completed right tensor inclusion commutes with the completed exponential. -/
@[simp]
theorem includeRightCompletion_completedExp [Algebra ℚ B] [Algebra ℚ (A ⊗[R] B)]
    (y : G.completionIdeal 1) :
    F.includeRightCompletion R G (G.completedExp y) = (F.tensorProduct R G).completedExp
      ⟨F.includeRightCompletion R G y,
        F.includeRightCompletion_mem_completionIdeal R G y.property⟩ := by
  simpa only [includeRightCompletion_eq_mapCompletionₐ] using G.mapCompletionₐ_completedExp
    (F.tensorProduct R G) Algebra.TensorProduct.includeRight id monotone_id
    (fun k => F.ideal_le_comap_includeRight R G (k + 1)) (F.ideal_le_comap_includeRight R G 1) y

/-- The completed left tensor inclusion commutes with the completed logarithm. -/
@[simp]
theorem includeLeftCompletion_completedLog [Algebra ℚ A] [Algebra ℚ (A ⊗[R] B)]
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1}) :
    F.includeLeftCompletion R G (F.completedLog u) = (F.tensorProduct R G).completedLog
      ⟨F.includeLeftCompletion R G u, by
        simpa only [map_sub, map_one] using
          F.includeLeftCompletion_mem_completionIdeal R G u.property⟩ := by
  simpa only [includeLeftCompletion_eq_mapCompletionₐ] using F.mapCompletionₐ_completedLog
    (F.tensorProduct R G) Algebra.TensorProduct.includeLeft id monotone_id
    (fun k => F.ideal_le_comap_includeLeft R G (k + 1)) (F.ideal_le_comap_includeLeft R G 1) u

/-- The completed right tensor inclusion commutes with the completed logarithm. -/
@[simp]
theorem includeRightCompletion_completedLog [Algebra ℚ B] [Algebra ℚ (A ⊗[R] B)]
    (v : {v : G.completion // v - 1 ∈ G.completionIdeal 1}) :
    F.includeRightCompletion R G (G.completedLog v) = (F.tensorProduct R G).completedLog
      ⟨F.includeRightCompletion R G v, by
        simpa only [map_sub, map_one] using
          F.includeRightCompletion_mem_completionIdeal R G v.property⟩ := by
  simpa only [includeRightCompletion_eq_mapCompletionₐ] using G.mapCompletionₐ_completedLog
    (F.tensorProduct R G) Algebra.TensorProduct.includeRight id monotone_id
    (fun k => F.ideal_le_comap_includeRight R G (k + 1)) (F.ideal_le_comap_includeRight R G 1) v

/-- The completed pure tensor of two completed exponentials is the completed exponential of
the sum of their completed inclusions. -/
theorem completedTensor_completedExp [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ (A ⊗[R] B)]
    (x : F.completionIdeal 1) (y : G.completionIdeal 1) :
    F.completedTensor R G (F.completedExp x) (G.completedExp y) = (F.tensorProduct R G).completedExp
      (⟨F.includeLeftCompletion R G x,
          F.includeLeftCompletion_mem_completionIdeal R G x.property⟩ +
        ⟨F.includeRightCompletion R G y,
          F.includeRightCompletion_mem_completionIdeal R G y.property⟩) := by
  rw [completedTensor_apply, includeLeftCompletion_completedExp,
    includeRightCompletion_completedExp, ← (F.tensorProduct R G).completedExp_add _ _
      (F.commute_includeLeftCompletion_includeRightCompletion R G x y)]

/-- The completed logarithm of a completed pure tensor of elements congruent to one is the sum
of the completed inclusions of their completed logarithms. -/
theorem completedLog_completedTensor [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ (A ⊗[R] B)]
    (u : {u : F.completion // u - 1 ∈ F.completionIdeal 1})
    (v : {v : G.completion // v - 1 ∈ G.completionIdeal 1}) :
    (F.tensorProduct R G).completedLog ⟨F.completedTensor R G u v,
      F.completedTensor_sub_one_mem_completionIdeal R G u.property v.property⟩ =
      F.includeLeftCompletion R G (F.completedLog u) +
        F.includeRightCompletion R G (G.completedLog v) := by
  rw [includeLeftCompletion_completedLog, includeRightCompletion_completedLog]
  simpa only [completedTensor_apply] using (F.tensorProduct R G).completedLog_mul
    ⟨F.includeLeftCompletion R G u, by
      simpa only [map_sub, map_one] using
        F.includeLeftCompletion_mem_completionIdeal R G u.property⟩
    ⟨F.includeRightCompletion R G v, by
      simpa only [map_sub, map_one] using
        F.includeRightCompletion_mem_completionIdeal R G v.property⟩
    (F.commute_includeLeftCompletion_includeRightCompletion R G u v)

end TauCeti.AlgFiltration
