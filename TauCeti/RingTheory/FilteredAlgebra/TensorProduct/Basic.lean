/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.AlgHom
public import TauCeti.RingTheory.TensorProduct.Filtration
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Completed tensor products of filtered algebras

The tensor product `A ⊗[R] B` of two filtered `R`-algebras carries the total-degree
filtration `AlgFiltration.tensorProduct`, whose order-`n` term is spanned by the pure
tensors `x ⊗ y` with `x` of order `a`, `y` of order `b` and `n ≤ a + b`. Its completion
is the completed tensor product.

Both algebra inclusions `A → A ⊗[R] B` and `B → A ⊗[R] B` preserve filtration orders, so
they extend to the completions. The images of the two completed inclusions commute, and
`AlgFiltration.completedTensor` sends a pair `(x, y)` to the product of the images of `x`
and `y`. It is `R`-bilinear and multiplicative, and its order-`k` component is computed
from the order-`k` classes of its arguments by `(a, b) ↦ a ⊗ b`. The algebras may be
noncommutative, and no flatness or separatedness is assumed.

Adapted from `yuma-mizuno-lean/Mei`, commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`,
`Mei/RingTheory/FilteredAlgebra/TensorProduct/Basic.lean` and `Completion.lean`
(Apache 2.0). Filtration bounds for the completed inclusions and pairing are adapted
from the same files at commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`.
-/

public section

open scoped TensorProduct

namespace TauCeti.AlgFiltration

section Filtration

variable (R : Type*) {A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (F : TauCeti.AlgFiltration A) (G : TauCeti.AlgFiltration B)

private theorem restrictScalars_ideal_mul_le {A : Type*} [Semiring A] [Algebra R A]
    (F : TauCeti.AlgFiltration A) (a b : ℕ) :
    (F.ideal a).restrictScalars R * (F.ideal b).restrictScalars R ≤
      (F.ideal (a + b)).restrictScalars R :=
  Submodule.mul_le.mpr fun _ hx _ hy => F.mul_mem hx hy

/-- The total-degree filtration on the tensor product of two filtered algebras. -/
noncomputable def tensorProduct : TauCeti.AlgFiltration (A ⊗[R] B) where
  ideal := tensorFiltrationTailIdeal (fun n => (F.ideal n).restrictScalars R)
    (fun n => (G.ideal n).restrictScalars R)
    (restrictScalars_ideal_mul_le R F) (restrictScalars_ideal_mul_le R G)
    (by simp) (by simp)
  isTwoSided _ := inferInstance
  antitone := tensorFiltrationTailIdeal_antitone _ _ _ _ _ _
  ideal_zero := tensorFiltrationTailIdeal_zero _ _ _ _ _ _
  mul_mem hx hy := by
    rw [mem_tensorFiltrationTailIdeal] at hx hy ⊢
    exact tensorFiltrationTail_mul_le _ _ (restrictScalars_ideal_mul_le R F)
      (restrictScalars_ideal_mul_le R G) _ _ (Submodule.mul_mem_mul hx hy)

/-- Membership in the total-degree filtration is membership in the sum of tensor images. -/
@[simp]
theorem mem_tensorProduct_ideal_iff {n : ℕ} {t : A ⊗[R] B} :
    t ∈ (F.tensorProduct R G).ideal n ↔
      t ∈ tensorFiltrationTail (fun n => (F.ideal n).restrictScalars R)
        (fun n => (G.ideal n).restrictScalars R) n :=
  mem_tensorFiltrationTailIdeal _ _ _ _ _ _

/-- Pure tensors have at least the sum of the filtration orders of their factors. -/
theorem tmul_mem_tensorProduct_ideal {a b n : ℕ} {x : A} {y : B} (h : n ≤ a + b)
    (hx : x ∈ F.ideal a) (hy : y ∈ G.ideal b) :
    x ⊗ₜ[R] y ∈ (F.tensorProduct R G).ideal n :=
  (F.mem_tensorProduct_ideal_iff R G).mpr (tmul_mem_tensorFiltrationTail _ _ h hx hy)

/-- The left inclusion preserves filtration orders. -/
theorem ideal_le_comap_includeLeft (k : ℕ) :
    F.ideal k ≤ ((F.tensorProduct R G).ideal k).comap
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) :=
  fun _ ha => F.tmul_mem_tensorProduct_ideal R G (a := k) (b := 0) (by omega) ha (by simp)

/-- The right inclusion preserves filtration orders. -/
theorem ideal_le_comap_includeRight (k : ℕ) :
    G.ideal k ≤ ((F.tensorProduct R G).ideal k).comap
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) :=
  fun _ hb => F.tmul_mem_tensorProduct_ideal R G (a := 0) (b := k) (by omega) (by simp) hb

end Filtration

section Completion

variable (R : Type*) {A B : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] (F : TauCeti.AlgFiltration A) (G : TauCeti.AlgFiltration B)

/-- The left inclusion into the completed tensor product. -/
noncomputable def includeLeftCompletion :
    F.completion →ₐ[R] (F.tensorProduct R G).completion :=
  F.mapCompletionₐ (F.tensorProduct R G) (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
    id monotone_id fun k => F.ideal_le_comap_includeLeft R G (k + 1)

/-- The right inclusion into the completed tensor product. -/
noncomputable def includeRightCompletion :
    G.completion →ₐ[R] (F.tensorProduct R G).completion :=
  G.mapCompletionₐ (F.tensorProduct R G) (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
    id monotone_id fun k => F.ideal_le_comap_includeRight R G (k + 1)

/-- The completed left inclusion extends the ordinary tensor inclusion. -/
@[simp]
theorem includeLeftCompletion_toCompletion (a : A) :
    F.includeLeftCompletion R G (F.toCompletion a) =
      (F.tensorProduct R G).toCompletion (a ⊗ₜ[R] (1 : B)) :=
  F.mapCompletionₐ_toCompletion _ _ _ monotone_id _ a

/-- The completed right inclusion extends the ordinary tensor inclusion. -/
@[simp]
theorem includeRightCompletion_toCompletion (b : B) :
    F.includeRightCompletion R G (G.toCompletion b) =
      (F.tensorProduct R G).toCompletion ((1 : A) ⊗ₜ[R] b) :=
  G.mapCompletionₐ_toCompletion _ _ _ monotone_id _ b

/-- The order-`k` component of the completed left inclusion is the induced quotient map. -/
@[simp]
theorem projection_includeLeftCompletion (k : ℕ) (x : F.completion) :
    (F.tensorProduct R G).projection k (F.includeLeftCompletion R G x) =
      Ideal.quotientMapₐ ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
        (F.ideal_le_comap_includeLeft R G (k + 1)) (F.projection k x) :=
  F.projection_mapCompletionₐ _ _ _ monotone_id _ k x

/-- The order-`k` component of the completed right inclusion is the induced quotient map. -/
@[simp]
theorem projection_includeRightCompletion (k : ℕ) (y : G.completion) :
    (F.tensorProduct R G).projection k (F.includeRightCompletion R G y) =
      Ideal.quotientMapₐ ((F.tensorProduct R G).ideal (k + 1))
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
        (F.ideal_le_comap_includeRight R G (k + 1)) (G.projection k y) :=
  G.projection_mapCompletionₐ _ _ _ monotone_id _ k y

/-- The images of the two completed tensor inclusions commute. -/
theorem commute_includeLeftCompletion_includeRightCompletion
    (x : F.completion) (y : G.completion) :
    Commute (F.includeLeftCompletion R G x) (F.includeRightCompletion R G y) := by
  refine (F.tensorProduct R G).completion_ext fun k => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (G.projection k y)
  simp only [map_mul, projection_includeLeftCompletion, projection_includeRightCompletion,
    ← ha, ← hb]
  simp [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The pure-tensor pairing of completions, sending `(x, y)` to the product of the images of
`x` and `y` under the completed tensor inclusions. -/
noncomputable def completedTensor :
    F.completion →ₗ[R] G.completion →ₗ[R] (F.tensorProduct R G).completion :=
  (LinearMap.mul R (F.tensorProduct R G).completion).compl₁₂
    (F.includeLeftCompletion R G).toLinearMap (F.includeRightCompletion R G).toLinearMap

/-- The completed tensor of two elements is the product of their completed inclusions. -/
theorem completedTensor_apply (x : F.completion) (y : G.completion) :
    F.completedTensor R G x y =
      F.includeLeftCompletion R G x * F.includeRightCompletion R G y := (rfl)

/-- The order-`k` component of a completed tensor is computed by `(a, b) ↦ a ⊗ b` on any
representatives of the order-`k` components of its arguments. -/
theorem projection_completedTensor_of_representatives (k : ℕ) (x : F.completion)
    (y : G.completion) (a : A) (b : B)
    (ha : Ideal.Quotient.mk (F.ideal (k + 1)) a = F.projection k x)
    (hb : Ideal.Quotient.mk (G.ideal (k + 1)) b = G.projection k y) :
    (F.tensorProduct R G).projection k (F.completedTensor R G x y) =
      Ideal.Quotient.mk ((F.tensorProduct R G).ideal (k + 1)) (a ⊗ₜ[R] b) := by
  rw [completedTensor_apply, map_mul, projection_includeLeftCompletion,
    projection_includeRightCompletion, ← ha, ← hb]
  simp [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- Completing an ordinary pure tensor agrees with the completed tensor of the canonical
images. -/
@[simp]
theorem completedTensor_toCompletion (a : A) (b : B) :
    F.completedTensor R G (F.toCompletion a) (G.toCompletion b) =
      (F.tensorProduct R G).toCompletion (a ⊗ₜ[R] b) := by
  simp [completedTensor_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The completed tensor is multiplicative in pairs of factors. -/
theorem completedTensor_mul (x x' : F.completion) (y y' : G.completion) :
    F.completedTensor R G (x * x') (y * y') =
      F.completedTensor R G x y * F.completedTensor R G x' y' := by
  simp only [completedTensor_apply, map_mul]
  exact ((F.commute_includeLeftCompletion_includeRightCompletion R G x' y).symm.mul_mul_mul_comm
    _ _).symm

/-- Tensoring with the unit of the right factor is the completed left inclusion. -/
@[simp]
theorem completedTensor_one_right (x : F.completion) :
    F.completedTensor R G x 1 = F.includeLeftCompletion R G x := by
  simp [completedTensor_apply]

/-- Tensoring with the unit of the left factor is the completed right inclusion. -/
@[simp]
theorem completedTensor_one_left (y : G.completion) :
    F.completedTensor R G 1 y = F.includeRightCompletion R G y := by
  simp [completedTensor_apply]

/-- The completed left inclusion preserves every filtration order. -/
theorem includeLeftCompletion_mem_completionIdeal {k : ℕ} {x : F.completion}
    (hx : x ∈ F.completionIdeal k) :
    F.includeLeftCompletion R G x ∈ (F.tensorProduct R G).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    exact F.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hx

/-- The completed right inclusion preserves every filtration order. -/
theorem includeRightCompletion_mem_completionIdeal {k : ℕ} {y : G.completion}
    (hy : y ∈ G.completionIdeal k) :
    F.includeRightCompletion R G y ∈ (F.tensorProduct R G).completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    exact G.mapCompletionₐ_mem_completionIdeal _ _ id monotone_id _ k hy

/-- Completed pure tensors add the filtration orders of their factors. -/
@[grind .]
theorem completedTensor_mem_completionIdeal {a b : ℕ}
    {x : F.completion} {y : G.completion}
    (hx : x ∈ F.completionIdeal a) (hy : y ∈ G.completionIdeal b) :
    F.completedTensor R G x y ∈ (F.tensorProduct R G).completionIdeal (a + b) := by
  rw [completedTensor_apply]
  exact (F.tensorProduct R G).mul_mem_completionIdeal
    (F.includeLeftCompletion_mem_completionIdeal R G hx)
    (F.includeRightCompletion_mem_completionIdeal R G hy)

end Completion

end TauCeti.AlgFiltration
