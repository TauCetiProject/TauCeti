/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Total filtration on a tensor product

For submodule families `F` and `G`, the total degree `n` part of their tensor product is
spanned by `x ⊗ y` with `x ∈ F i`, `y ∈ G j`, and `i + j ≤ n`. No flatness is needed:
we use the images of the tensor factors, not an asserted embedding of their tensor product.
Multiplicative families give a multiplicative total filtration. This allows coproduct degree
bounds to be stated with the sum of the two degrees, rather than separate bounds on each leg.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M N : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Total tensor degree at most `n`, formed from two families of submodules. -/
def tensorFiltration (F : ℕ → Submodule R M) (G : ℕ → Submodule R N)
    (n : ℕ) : Submodule R (M ⊗[R] N) :=
  ⨆ (i : ℕ) (j : ℕ) (_ : i + j ≤ n),
    Submodule.map₂ (TensorProduct.mk R M N) (F i) (G j)

/-- A submodule contains a total filtration step exactly when it contains its pure tensors. -/
theorem tensorFiltration_le_iff {F : ℕ → Submodule R M} {G : ℕ → Submodule R N}
    {n : ℕ} {P : Submodule R (M ⊗[R] N)} :
    tensorFiltration F G n ≤ P ↔
      ∀ i j, i + j ≤ n → ∀ x ∈ F i, ∀ y ∈ G j, x ⊗ₜ[R] y ∈ P := by
  simp only [tensorFiltration, iSup_le_iff, Submodule.map₂_le, TensorProduct.mk_apply]

/-- Pure tensors whose degrees sum to at most `n` belong to total degree `n`. -/
theorem tmul_mem_tensorFiltration {F : ℕ → Submodule R M} {G : ℕ → Submodule R N}
    {i j n : ℕ} {x : M} {y : N} (hij : i + j ≤ n) (hx : x ∈ F i) (hy : y ∈ G j) :
    x ⊗ₜ[R] y ∈ tensorFiltration F G n :=
  tensorFiltration_le_iff.mp le_rfl i j hij x hx y hy

/-- Total degree is increasing, even if the input families are not increasing. -/
theorem tensorFiltration_mono (F : ℕ → Submodule R M) (G : ℕ → Submodule R N) :
    Monotone (tensorFiltration F G) := by
  intro m n hmn
  exact tensorFiltration_le_iff.mpr fun i j hij x hx y hy ↦
    tmul_mem_tensorFiltration (hij.trans hmn) hx hy

/-- Degree zero is the image of the tensor product of the degree-zero submodules. -/
@[simp]
theorem tensorFiltration_zero (F : ℕ → Submodule R M) (G : ℕ → Submodule R N) :
    tensorFiltration F G 0 = Submodule.map₂ (TensorProduct.mk R M N) (F 0) (G 0) := by
  apply le_antisymm
  · apply tensorFiltration_le_iff.mpr
    intro i j hij x hx y hy
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    exact Submodule.apply_mem_map₂ _ hx hy
  · exact Submodule.map₂_le.mpr fun x hx y hy ↦ tmul_mem_tensorFiltration (by omega) hx hy

section Algebra

variable {A B : Type*} [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable {F : ℕ → Submodule R A} {G : ℕ → Submodule R B}

/-- Multiplicativity of the two families implies multiplicativity in total tensor degree. -/
theorem tensorFiltration_mul_le
    (hF : ∀ i j, F i * F j ≤ F (i + j))
    (hG : ∀ i j, G i * G j ≤ G (i + j)) (m n : ℕ) :
    tensorFiltration F G m * tensorFiltration F G n ≤ tensorFiltration F G (m + n) := by
  rw [tensorFiltration, tensorFiltration]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
  intro k l hkl i j hij
  refine (Submodule.map₂_tmul_mul_le (F i) (F k) (G j) (G l)).trans ?_
  refine (Submodule.map₂_le_map₂ (hF i k) (hG j l)).trans ?_
  exact Submodule.map₂_le.mpr fun x hx y hy ↦
    tmul_mem_tensorFiltration (by omega) hx hy

end Algebra

end TauCeti
