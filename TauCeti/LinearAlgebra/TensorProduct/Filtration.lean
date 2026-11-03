/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Total-degree filtrations on tensor products

The total tensor filtration of two families of submodules is the sum of the images of
`F i ⊗ G j` with `i + j ≤ n`. Using images avoids any flatness assumption. This construction
transports multiplicativity and exhaustivity to tensor products, for example for order
filtrations on enveloping algebras and their integral forms.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {R M N : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (F : ℕ → Submodule R M) (G : ℕ → Submodule R N)

/-- The total-degree tensor filtration, formed from tensor images rather than embeddings. -/
def filtration (n : ℕ) : Submodule R (M ⊗[R] N) :=
  ⨆ (i : ℕ) (j : ℕ) (_ : i + j ≤ n),
    Submodule.map₂ (_root_.TensorProduct.mk R M N) (F i) (G j)

/-- The total-degree tensor filtration is the sum of its bounded-degree tensor images. -/
theorem filtration_def (n : ℕ) : filtration F G n =
    ⨆ (i : ℕ) (j : ℕ) (_ : i + j ≤ n),
      Submodule.map₂ (_root_.TensorProduct.mk R M N) (F i) (G j) := (rfl)

/-- A total tensor step is contained in a submodule exactly when its pure tensors are. -/
theorem filtration_le_iff {n : ℕ} {P : Submodule R (M ⊗[R] N)} :
    filtration F G n ≤ P ↔
      ∀ i j, i + j ≤ n → ∀ x ∈ F i, ∀ y ∈ G j, x ⊗ₜ[R] y ∈ P := by
  simp only [filtration_def, iSup_le_iff, Submodule.map₂_le,
    _root_.TensorProduct.mk_apply]

/-- A pure tensor has total degree bounded by the sum of its factor degrees. -/
theorem tmul_mem_filtration {i j : ℕ} {x : M} {y : N}
    (hx : x ∈ F i) (hy : y ∈ G j) : x ⊗ₜ[R] y ∈ filtration F G (i + j) :=
  (filtration_le_iff F G).1 le_rfl i j le_rfl x hx y hy

/-- Total tensor steps increase with the degree bound. -/
theorem filtration_mono : Monotone (filtration F G) := by
  intro m n hmn
  refine (filtration_le_iff F G).2 fun i j hij x hx y hy => ?_
  exact (filtration_le_iff F G).1 le_rfl i j (hij.trans hmn) x hx y hy

/-- Increasing exhaustive factor filtrations give an exhaustive total tensor filtration. -/
theorem iSup_filtration_eq_top (hF : Monotone F) (hG : Monotone G)
    (hFtop : ⨆ i, F i = ⊤) (hGtop : ⨆ j, G j = ⊤) :
    ⨆ n, filtration F G n = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  induction z using _root_.TensorProduct.inductionOn with
  | tmul x y =>
    have hx : x ∈ ⨆ i, F i := by rw [hFtop]; exact Submodule.mem_top
    have hy : y ∈ ⨆ j, G j := by rw [hGtop]; exact Submodule.mem_top
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ hF.directed_le).1 hx
    obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed _ hG.directed_le).1 hy
    exact Submodule.mem_iSup_of_mem (i + j) (tmul_mem_filtration F G hi hj)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Every tensor has finite total degree for increasing exhaustive factor filtrations. -/
theorem exists_mem_filtration (hF : Monotone F) (hG : Monotone G)
    (hFtop : ⨆ i, F i = ⊤) (hGtop : ⨆ j, G j = ⊤) (z : M ⊗[R] N) :
    ∃ n, z ∈ filtration F G n := by
  rw [← Submodule.mem_iSup_of_directed _ (filtration_mono F G).directed_le,
    iSup_filtration_eq_top F G hF hG hFtop hGtop]
  exact Submodule.mem_top

section Algebra

variable {A B : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)

/-- If both factor filtrations start at the scalars, so does the tensor filtration. -/
@[simp]
theorem filtration_zero (hF : F 0 = 1) (hG : G 0 = 1) : filtration F G 0 = 1 := by
  have hblock : Submodule.map₂ (_root_.TensorProduct.mk R A B) (F 0) (G 0) = 1 := by
    simp [hF, hG, Submodule.one_eq_span, Submodule.map₂_span_span,
      Algebra.TensorProduct.one_def]
  apply le_antisymm
  · refine (filtration_le_iff F G).2 fun i j hij => ?_
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    exact Submodule.map₂_le.1 hblock.le
  · rw [← hblock, filtration_def]
    exact le_iSup_of_le 0 (le_iSup_of_le 0 (le_iSup_of_le le_rfl le_rfl))

/-- The tensor unit belongs to every total step of unital factor filtrations. -/
theorem one_mem_filtration [SetLike.GradedOne F] [SetLike.GradedOne G] (n : ℕ) :
    (1 : A ⊗[R] B) ∈ filtration F G n := by
  simpa only [Algebra.TensorProduct.one_def] using
    (filtration_le_iff F G).1 le_rfl 0 0 (Nat.zero_le n)
      1 (SetLike.one_mem_graded F) 1 (SetLike.one_mem_graded G)

/-- Multiplication adds total degrees for multiplicative factor filtrations. -/
theorem mul_mem_filtration [SetLike.GradedMul F] [SetLike.GradedMul G]
    {m n : ℕ} {x y : A ⊗[R] B}
    (hx : x ∈ filtration F G m) (hy : y ∈ filtration F G n) :
    x * y ∈ filtration F G (m + n) := by
  have hleft : filtration F G m ≤
      (filtration F G (m + n)).comap ((LinearMap.mul R (A ⊗[R] B)).flip y) := by
    refine (filtration_le_iff F G).2 fun i j hij a ha b hb => ?_
    have hright : filtration F G n ≤
        (filtration F G (m + n)).comap (LinearMap.mul R (A ⊗[R] B) (a ⊗ₜ[R] b)) := by
      refine (filtration_le_iff F G).2 fun k l hkl c hc d hd => ?_
      simp only [Submodule.mem_comap, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul]
      have hdegree : (i + k) + (j + l) ≤ m + n := by omega
      exact filtration_mono F G hdegree
        (tmul_mem_filtration F G (SetLike.mul_mem_graded ha hc) (SetLike.mul_mem_graded hb hd))
    exact hright hy
  exact hleft hx

/-- The product of total tensor steps is contained in the step of summed degree. -/
theorem filtration_mul_le [SetLike.GradedMul F] [SetLike.GradedMul G] (m n : ℕ) :
    filtration F G m * filtration F G n ≤ filtration F G (m + n) :=
  Submodule.mul_le.2 fun _ hx _ hy => mul_mem_filtration F G hx hy

end Algebra

end TensorProduct
