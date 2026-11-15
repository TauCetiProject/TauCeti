/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.CoaugmentedBar
public import TauCeti.LinearAlgebra.TensorCoalgebra.Completed.LengthBound

/-!
# Completing finite-arity bar differentials

If an `A∞` algebra has no operations above arity `c + 1`, its coaugmented bar
differential extends to the product of all tensor powers. The resulting linear
endomorphism is square-zero, agrees with the finite bar differential, and lowers
the descending length filtration by at most `c`. It is independent of the chosen
arity bound and is unique among extensions admitting any uniform length bound.

The completed co-Leibniz identity is separate from this square-zero linear extension.
Arbitrary unbounded-arity operations require additional convergence data to define
an endomorphism of this product.

The bar convention follows Getzler--Jones, *A-infinity algebras and the cyclic bar
complex*, Sections 1--2, and Keller, *Introduction to A-infinity algebras and modules*,
Section 3.6. The completion follows Loday--Vallette, *Algebraic Operads*, Chapters 9--10.
-/

public section

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- A finite arity bound gives a uniform length bound for the coaugmented bar differential. -/
theorem hasLengthBound_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) (c : ℕ)
    (h𝒜 : ∀ n, c + 1 < n → 𝒜.m n = 0) :
    CompletedTensorWords.HasLengthBound c 𝒜.coaugmentedBarDifferential := by
  rw [coaugmentedBarDifferential_def, barDifferential_def]
  exact TensorWords.hasLengthBound_extendReduced_gradedCoderiv
    (𝒜.grading.shift 1) 𝒜.taylor 1 c fun n hn ↦
      𝒜.taylor_comp_of_eq_zero_of_m_eq_zero n (h𝒜 n.1 hn)

/-- The finite-prefix extension of the coaugmented bar differential to completed tensor words.
When operations above arity `c + 1` vanish, it agrees with the original differential on finite
words and squares to zero. -/
noncomputable def completedBarDifferential (𝒜 : AInfinityAlgebra R A) (c : ℕ) :
    CompletedTensorWords R A →ₗ[R] CompletedTensorWords R A :=
  CompletedTensorWords.extend c 𝒜.coaugmentedBarDifferential

/-- The completed bar differential is the finite-prefix extension at length bound `c`. -/
theorem completedBarDifferential_def (𝒜 : AInfinityAlgebra R A) (c : ℕ) :
    𝒜.completedBarDifferential c =
      CompletedTensorWords.extend c 𝒜.coaugmentedBarDifferential := by
  rw [completedBarDifferential]

/-- Each output coordinate of the completed differential reads a finite input prefix. -/
@[simp]
theorem completedBarDifferential_apply (𝒜 : AInfinityAlgebra R A) (c : ℕ)
    (x : CompletedTensorWords R A) (k : ℕ) :
    𝒜.completedBarDifferential c x k =
      𝒜.coaugmentedBarDifferential (CompletedTensorWords.truncate R A (k + 1 + c) x) k := by
  rw [completedBarDifferential_def, CompletedTensorWords.extend_apply]

/-- On finite tensor words, the completed differential is the original bar differential. -/
@[simp]
theorem completedBarDifferential_coe (𝒜 : AInfinityAlgebra R A) (c : ℕ)
    (h𝒜 : ∀ n, c + 1 < n → 𝒜.m n = 0) (x : TensorWords R A) :
    𝒜.completedBarDifferential c x =
      (𝒜.coaugmentedBarDifferential x : CompletedTensorWords R A) := by
  rw [completedBarDifferential_def]
  exact CompletedTensorWords.extend_coe c _ (𝒜.hasLengthBound_coaugmentedBarDifferential c h𝒜) x

/-- The completed bar differential lowers the descending length filtration by at most `c`. -/
theorem map_completedBarDifferential_filtration_le (𝒜 : AInfinityAlgebra R A) (c : ℕ)
    (n : ℕ) :
    Submodule.map (𝒜.completedBarDifferential c)
      (CompletedTensorWords.filtration R A (n + c)) ≤ CompletedTensorWords.filtration R A n := by
  rw [completedBarDifferential_def]
  exact CompletedTensorWords.map_extend_filtration_le c _ n

/-- The completed bar differential is independent of its arity bound. -/
theorem completedBarDifferential_eq (𝒜 : AInfinityAlgebra R A) (c d : ℕ)
    (hc : ∀ n, c + 1 < n → 𝒜.m n = 0) (hd : ∀ n, d + 1 < n → 𝒜.m n = 0) :
    𝒜.completedBarDifferential c = 𝒜.completedBarDifferential d := by
  rw [completedBarDifferential_def, completedBarDifferential_def]
  exact CompletedTensorWords.extend_eq c d _
    (𝒜.hasLengthBound_coaugmentedBarDifferential c hc)
    (𝒜.hasLengthBound_coaugmentedBarDifferential d hd)

/-- The completed bar differential squares to zero on infinite-support words as well. -/
@[simp]
theorem completedBarDifferential_sq (𝒜 : AInfinityAlgebra R A) (c : ℕ)
    (h𝒜 : ∀ n, c + 1 < n → 𝒜.m n = 0) :
    𝒜.completedBarDifferential c ∘ₗ 𝒜.completedBarDifferential c = 0 := by
  rw [completedBarDifferential_def]
  exact CompletedTensorWords.extend_comp_self_eq_zero c _
    (𝒜.hasLengthBound_coaugmentedBarDifferential c h𝒜) 𝒜.coaugmentedBarDifferential_sq

/-- Agreement on finite words and any uniform length-filtration bound characterize
the completed bar differential uniquely. -/
theorem completedBarDifferential_unique (𝒜 : AInfinityAlgebra R A) (c : ℕ)
    (h𝒜 : ∀ n, c + 1 < n → 𝒜.m n = 0)
    (b : CompletedTensorWords R A →ₗ[R] CompletedTensorWords R A) (d : ℕ)
    (hb : ∀ n, Submodule.map b (CompletedTensorWords.filtration R A (n + d)) ≤
      CompletedTensorWords.filtration R A n)
    (hb𝒜 : ∀ x : TensorWords R A, b x =
      (𝒜.coaugmentedBarDifferential x : CompletedTensorWords R A)) :
    b = 𝒜.completedBarDifferential c := by
  rw [completedBarDifferential_def]
  exact CompletedTensorWords.extend_unique c _
    (𝒜.hasLengthBound_coaugmentedBarDifferential c h𝒜) b d hb fun x ↦ by
      simpa only [DFinsupp.coeFnLinearMap_apply] using hb𝒜 x

end TauCeti.AInfinityAlgebra
