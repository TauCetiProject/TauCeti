/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# Completely bounded maps between C⋆-algebras

For a complex-linear map `φ : A → B` between C⋆-algebras and `n : ℕ`, the amplification
`φₙ : M_n(A) → M_n(B)` applies `φ` entrywise, where `M_n(A) = CStarMatrix (Fin n) (Fin n) A`
carries its C⋆-norm (the operator norm on the Hilbert `A`-module `Aⁿ`), never an entrywise norm.
The map `φ` is **completely bounded** when the amplifications are uniformly bounded, and its
**cb norm** `‖φ‖_cb = sup_n ‖φₙ‖` is the least uniform bound.

This file treats C⋆-algebras only, with the operator-space structure they carry through
`CStarMatrix`; abstract operator spaces are not used.

## Main declarations

* `TauCeti.IsCompletelyBounded`, `TauCeti.cbNorm`: complete boundedness and the cb norm, with
  `TauCeti.norm_map_le_cbNorm_mul` (`‖φₙ x‖ ≤ ‖φ‖_cb ‖x‖`), `TauCeti.cbNorm_le_of_bound`, and
  `TauCeti.norm_apply_le_cbNorm_mul` (`‖φ‖ ≤ ‖φ‖_cb`, the level-one comparison).
* `TauCeti.IsCompletelyBounded.comp`, `TauCeti.cbNorm_comp_le`: composition, and
  `TauCeti.cbNorm_id_le_one`.
* `TauCeti.isCompletelyBounded_nonUnitalStarAlgHom`, `TauCeti.cbNorm_nonUnitalStarAlgHom_le_one`:
  star homomorphisms are complete contractions.
* `TauCeti.norm_sum_mul_mul_sq_le`: `‖∑ aₖ x bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖x‖² ‖∑ bₖ⋆ bₖ‖` in a
  C⋆-algebra, from the Cauchy–Schwarz inequality of the Hilbert module `Dⁿ`.
* `CStarMatrix.transposeₗ`: the transpose of C⋆-matrices as a linear map.
* `TauCeti.isCompletelyBounded_transposeₗ`, `TauCeti.cbNorm_transposeₗ`: the transpose on
  `M_n(ℂ)` is completely bounded with cb norm `n`. At level `n` it sends the flip unitary
  `[E l k]_{k l}`, of norm `1`, to `[E k l]_{k l}`, which is `n` times a rank-one projection; the
  bound `n` at every level comes from writing the transpose as `y ↦ ∑ E i j * y * E i j`.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3 and Exercise 3.11.
* G. Pisier, *Introduction to Operator Space Theory*, §1.2.
-/

public section

open scoped InnerProductSpace WithCStarModule ComplexOrder

namespace CStarMatrix

variable {m n R A : Type*}

variable (R) in
/-- The transpose of C⋆-matrices, as a linear map. -/
@[expose] def transposeₗ [Semiring R] [AddCommMonoid A] [Module R A] :
    CStarMatrix m n A →ₗ[R] CStarMatrix n m A where
  toFun M := M.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem transposeₗ_apply [Semiring R] [AddCommMonoid A] [Module R A] (M : CStarMatrix m n A)
    (i : n) (j : m) : transposeₗ R M i j = M j i :=
  rfl

/-- Entries of a finite sum of C⋆-matrices are the sums of the entries. -/
theorem sum_apply [AddCommMonoid A] {ι : Type*} (s : Finset ι) (f : ι → CStarMatrix m n A)
    (i : m) (j : n) : (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => simp [Finset.sum_insert hk, ih]

end CStarMatrix

namespace TauCeti

section Defs

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A linear map between C⋆-algebras is **completely bounded** when its matrix amplifications
are uniformly bounded, for the C⋆-norms of `CStarMatrix` rather than an entrywise matrix
norm. -/
def IsCompletelyBounded (φ : A →ₗ[ℂ] B) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖

/-- The **cb norm** `‖φ‖_cb = sup_n ‖φₙ‖` of a linear map between C⋆-algebras: the least
uniform bound on the norms of its matrix amplifications. It is `0` when `φ` is not completely
bounded; the results about it assume `IsCompletelyBounded φ` where needed. -/
noncomputable def cbNorm (φ : A →ₗ[ℂ] B) : ℝ :=
  sInf {C | 0 ≤ C ∧ ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖}

theorem cbNorm_nonneg (φ : A →ₗ[ℂ] B) : 0 ≤ cbNorm φ :=
  Real.sInf_nonneg fun _ h => h.1

/-- A uniform bound on the amplifications bounds the cb norm. -/
theorem cbNorm_le_of_bound {φ : A →ₗ[ℂ] B} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ c * ‖x‖) : cbNorm φ ≤ c :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hc, h⟩

/-- The cb norm bounds every amplification of a completely bounded map. -/
theorem norm_map_le_cbNorm_mul {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) {n : ℕ}
    (x : CStarMatrix (Fin n) (Fin n) A) : ‖x.map φ‖ ≤ cbNorm φ * ‖x‖ := by
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx, norm_eq_zero.mp hx.symm]
    have : (0 : CStarMatrix (Fin n) (Fin n) A).map φ = 0 := by ext; simp [CStarMatrix.map_apply]
    simp [this]
  rw [← div_le_iff₀ hx]
  obtain ⟨c, hc, hb⟩ := hφ
  exact le_csInf ⟨c, hc, hb⟩ fun d hd => (div_le_iff₀ hx).mpr (hd.2 n x)

/-- Complete boundedness only needs some uniform bound on the amplifications. -/
theorem isCompletelyBounded_iff_exists_bound {φ : A →ₗ[ℂ] B} :
    IsCompletelyBounded φ ↔
      ∃ C : ℝ, ∀ (n : ℕ) (x : CStarMatrix (Fin n) (Fin n) A), ‖x.map φ‖ ≤ C * ‖x‖ := by
  refine ⟨fun ⟨C, _, h⟩ => ⟨C, h⟩, fun ⟨C, h⟩ => ⟨max C 0, le_max_right _ _, fun n x => ?_⟩⟩
  exact (h n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- The level-one comparison `‖φ a‖ ≤ ‖φ‖_cb ‖a‖`: the cb norm dominates the operator norm. -/
theorem norm_apply_le_cbNorm_mul {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyBounded φ) (a : A) :
    ‖φ a‖ ≤ cbNorm φ * ‖a‖ := by
  let e := (CStarMatrix.toOneByOne (Fin 1) ℂ A).toNonUnitalStarAlgHom
  let f := (CStarMatrix.toOneByOne (Fin 1) ℂ B).toNonUnitalStarAlgHom
  have he := NonUnitalStarAlgHom.norm_map e (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective a
  have hf := NonUnitalStarAlgHom.norm_map f (CStarMatrix.toOneByOne (Fin 1) ℂ B).injective (φ a)
  have hfa : f (φ a) = (e a).map φ := rfl
  rw [hfa] at hf
  rw [← hf, ← he]
  exact norm_map_le_cbNorm_mul hφ _

/-- The identity map is completely bounded. -/
theorem isCompletelyBounded_id : IsCompletelyBounded (LinearMap.id : A →ₗ[ℂ] A) :=
  ⟨1, zero_le_one, fun n x => by simp⟩

/-- The identity map has cb norm at most `1`. -/
theorem cbNorm_id_le_one : cbNorm (LinearMap.id : A →ₗ[ℂ] A) ≤ 1 :=
  cbNorm_le_of_bound zero_le_one fun n x => by simp

/-- The composite of completely bounded maps is completely bounded. -/
theorem IsCompletelyBounded.comp {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompletelyBounded ψ)
    (hφ : IsCompletelyBounded φ) : IsCompletelyBounded (ψ ∘ₗ φ) :=
  ⟨cbNorm ψ * cbNorm φ, mul_nonneg (cbNorm_nonneg ψ) (cbNorm_nonneg φ), fun n x => by
    have : x.map (ψ ∘ₗ φ) = (x.map φ).map ψ := by ext; simp [CStarMatrix.map_apply]
    rw [this, mul_assoc]
    exact (norm_map_le_cbNorm_mul hψ _).trans
      (mul_le_mul_of_nonneg_left (norm_map_le_cbNorm_mul hφ x) (cbNorm_nonneg ψ))⟩

/-- The cb norm is submultiplicative. -/
theorem cbNorm_comp_le {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsCompletelyBounded ψ)
    (hφ : IsCompletelyBounded φ) : cbNorm (ψ ∘ₗ φ) ≤ cbNorm ψ * cbNorm φ :=
  cbNorm_le_of_bound (mul_nonneg (cbNorm_nonneg ψ) (cbNorm_nonneg φ)) fun n x => by
    have : x.map (ψ ∘ₗ φ) = (x.map φ).map ψ := by ext; simp [CStarMatrix.map_apply]
    rw [this, mul_assoc]
    exact (norm_map_le_cbNorm_mul hψ _).trans
      (mul_le_mul_of_nonneg_left (norm_map_le_cbNorm_mul hφ x) (cbNorm_nonneg ψ))

/-- A star homomorphism of C⋆-algebras is completely bounded: each amplification is again a star
homomorphism, hence contractive. -/
theorem isCompletelyBounded_nonUnitalStarAlgHom (π : A →⋆ₙₐ[ℂ] B) :
    IsCompletelyBounded (π : A →ₗ[ℂ] B) :=
  ⟨1, zero_le_one, fun n x => by
    simpa using NonUnitalStarAlgHom.norm_apply_le (CStarMatrix.mapₙₐ (n := Fin n) π) x⟩

/-- A star homomorphism of C⋆-algebras is a complete contraction. -/
theorem cbNorm_nonUnitalStarAlgHom_le_one (π : A →⋆ₙₐ[ℂ] B) : cbNorm (π : A →ₗ[ℂ] B) ≤ 1 :=
  cbNorm_le_of_bound zero_le_one fun n x => by
    simpa using NonUnitalStarAlgHom.norm_apply_le (CStarMatrix.mapₙₐ (n := Fin n) π) x

end Defs

section CauchySchwarz

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- The Cauchy–Schwarz bound `‖∑ aₖ x bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖x‖² ‖∑ bₖ⋆ bₖ‖` in a C⋆-algebra:
`∑ aₖ x bₖ` is the inner product of the columns `(bₖ⋆)` and `(aₖ x)` of the Hilbert module
`Dⁿ`. -/
theorem norm_sum_mul_mul_sq_le {ι : Type*} [Fintype ι] (a b : ι → D) (x : D) :
    ‖∑ k, a k * x * b k‖ ^ 2 ≤ ‖∑ k, a k * star (a k)‖ * ‖x‖ ^ 2 * ‖∑ k, star (b k) * b k‖ := by
  let u : C⋆ᵐᵒᵈ(D, ι → D) := (WithCStarModule.equiv D (ι → D)).symm fun k => star (b k)
  let v : C⋆ᵐᵒᵈ(D, ι → D) := (WithCStarModule.equiv D (ι → D)).symm fun k => a k * x
  have huv : ⟪u, v⟫_D = ∑ k, a k * x * b k := by
    simp [u, v, WithCStarModule.pi_inner, WithCStarModule.inner_def]
  have hu : ‖u‖ ^ 2 = ‖∑ k, star (b k) * b k‖ := by
    simp [u, WithCStarModule.pi_norm_sq, WithCStarModule.inner_def]
  have hv : ‖v‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖∑ k, a k * star (a k)‖ := by
    rw [WithCStarModule.pi_norm_sq]
    have hle : ∑ k, ⟪v k, v k⟫_D ≤ ‖x * star x‖ • ∑ k, a k * star (a k) := by
      rw [Finset.smul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have := CStarAlgebra.star_right_conjugate_le_norm_smul (a k) (x * star x)
      simpa [v, WithCStarModule.inner_def, mul_assoc] using this
    have h0 : 0 ≤ ∑ k, ⟪v k, v k⟫_D := Finset.sum_nonneg fun k _ => CStarModule.inner_self_nonneg
    refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0).trans_eq ?_
    rw [norm_smul, norm_norm, CStarRing.norm_self_mul_star, sq]
  rw [← huv]
  calc ‖⟪u, v⟫_D‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
        gcongr
        exact CStarModule.norm_inner_le (C⋆ᵐᵒᵈ(D, ι → D))
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ ≤ ‖∑ k, star (b k) * b k‖ * (‖x‖ ^ 2 * ‖∑ k, a k * star (a k)‖) := by
        rw [hu]
        gcongr
    _ = _ := by ring

end CauchySchwarz

section Transpose

open CStarMatrix hiding sum_apply mul_apply one_apply

variable {m n : ℕ}

/-- The matrix unit `E i j` of `M_n(ℂ)`. -/
private def matrixUnit (i j : Fin n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  ofMatrix (Matrix.of fun r s => if r = i ∧ s = j then 1 else 0)

private theorem matrixUnit_apply (i j r s : Fin n) :
    matrixUnit i j r s = if r = i ∧ s = j then 1 else 0 :=
  rfl

/-- The transpose on `M_n(ℂ)` is `y ↦ ∑ E i j * y * E i j`. -/
private theorem transposeₗ_eq_sum (y : CStarMatrix (Fin n) (Fin n) ℂ) :
    transposeₗ ℂ y = ∑ p : Fin n × Fin n, matrixUnit p.1 p.2 * y * matrixUnit p.1 p.2 := by
  ext r s
  simp [CStarMatrix.sum_apply, CStarMatrix.mul_apply, matrixUnit_apply, Fintype.sum_prod_type,
    ite_and]

/-- The block-diagonal matrix `diag(E i j, …, E i j)` in `M_m(M_n(ℂ))`. -/
private def blockMatrixUnit (m : ℕ) (i j : Fin n) :
    CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) ℂ) :=
  ofMatrix (Matrix.of fun k l => if k = l then matrixUnit i j else 0)

private theorem blockMatrixUnit_apply (i j : Fin n) (k l : Fin m) :
    blockMatrixUnit m i j k l = if k = l then matrixUnit i j else 0 :=
  rfl

private theorem blockMatrixUnit_apply_apply (i j : Fin n) (k l : Fin m) (r s : Fin n) :
    blockMatrixUnit m i j k l r s = if k = l ∧ r = i ∧ s = j then 1 else 0 := by
  rw [blockMatrixUnit_apply]
  split_ifs <;> simp_all [matrixUnit_apply]

private theorem blockMatrixUnit_mul_mul_apply (i j : Fin n)
    (x : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) ℂ)) (k l : Fin m) :
    (blockMatrixUnit m i j * x * blockMatrixUnit m i j) k l =
      matrixUnit i j * x k l * matrixUnit i j := by
  simp [CStarMatrix.mul_apply, blockMatrixUnit_apply]

/-- The amplification of the transpose is `x ↦ ∑ diag(E i j) * x * diag(E i j)`. -/
private theorem map_transposeₗ_eq_sum
    (x : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) ℂ)) :
    x.map (transposeₗ ℂ) =
      ∑ p : Fin n × Fin n, blockMatrixUnit m p.1 p.2 * x * blockMatrixUnit m p.1 p.2 := by
  refine CStarMatrix.ext fun k l => ?_
  rw [CStarMatrix.sum_apply, map_apply]
  simp_rw [blockMatrixUnit_mul_mul_apply]
  exact transposeₗ_eq_sum _

private theorem sum_blockMatrixUnit_mul_star :
    ∑ p : Fin n × Fin n, blockMatrixUnit m p.1 p.2 * star (blockMatrixUnit m p.1 p.2) =
      (n : ℂ) • 1 := by
  ext k l r s
  simp [CStarMatrix.sum_apply, CStarMatrix.mul_apply, star_apply, blockMatrixUnit_apply_apply,
    CStarMatrix.one_apply, Fintype.sum_prod_type, ite_and]
  by_cases hkl : k = l <;> by_cases hrs : r = s <;>
    simp [hkl, hrs, CStarMatrix.one_apply, eq_comm]


private theorem sum_star_blockMatrixUnit_mul :
    ∑ p : Fin n × Fin n, star (blockMatrixUnit m p.1 p.2) * blockMatrixUnit m p.1 p.2 =
      (n : ℂ) • 1 := by
  ext k l r s
  simp [CStarMatrix.sum_apply, CStarMatrix.mul_apply, star_apply, blockMatrixUnit_apply_apply,
    CStarMatrix.one_apply, Fintype.sum_prod_type, ite_and]
  by_cases hkl : k = l <;> by_cases hrs : r = s <;>
    simp [hkl, hrs, CStarMatrix.one_apply, eq_comm]

private theorem norm_natCast_smul_one_le {D : Type*} [CStarAlgebra D] (n : ℕ) :
    ‖(n : ℂ) • (1 : D)‖ ≤ n := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · simp [Subsingleton.elim ((n : ℂ) • (1 : D)) 0]
  · simp [norm_smul]

/-- Every amplification of the transpose on `M_n(ℂ)` is bounded by `n`: write the transpose as
`∑ E i j * y * E i j` and apply `norm_sum_mul_mul_sq_le`, with
`∑ E i j * (E i j)⋆ = ∑ (E i j)⋆ * E i j = n • 1`. -/
theorem norm_map_transposeₗ_le (x : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) ℂ)) :
    ‖x.map (transposeₗ ℂ)‖ ≤ n * ‖x‖ := by
  have h := norm_sum_mul_mul_sq_le (fun p : Fin n × Fin n => blockMatrixUnit m p.1 p.2)
    (fun p : Fin n × Fin n => blockMatrixUnit m p.1 p.2) x
  rw [sum_blockMatrixUnit_mul_star, sum_star_blockMatrixUnit_mul, ← map_transposeₗ_eq_sum] at h
  have hn := norm_natCast_smul_one_le
    (D := CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) ℂ)) n
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans ?_)
  calc _ ≤ (n : ℝ) * ‖x‖ ^ 2 * n := by gcongr
    _ = (n * ‖x‖) ^ 2 := by ring

/-- The flip unitary `[E l k]_{k l}` in `M_n(M_n(ℂ))`. -/
private def flipMatrix (n : ℕ) : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin n) (Fin n) ℂ) :=
  ofMatrix (Matrix.of fun k l => matrixUnit l k)

private theorem flipMatrix_apply_apply (k l r s : Fin n) :
    flipMatrix n k l r s = if r = l ∧ s = k then 1 else 0 :=
  rfl

private theorem flipMatrix_mem_unitary :
    flipMatrix n ∈ unitary (CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin n) (Fin n) ℂ)) := by
  rw [Unitary.mem_iff]
  constructor <;>
  · ext k l r s
    simp [CStarMatrix.sum_apply, CStarMatrix.mul_apply, star_apply, flipMatrix_apply_apply,
      CStarMatrix.one_apply, ite_and]
    by_cases hkl : k = l <;> by_cases hrs : r = s <;>
      simp [hkl, hrs, CStarMatrix.one_apply, eq_comm]

private theorem map_transposeₗ_flipMatrix_apply_apply (k l r s : Fin n) :
    (flipMatrix n).map (transposeₗ ℂ) k l r s = if r = k ∧ s = l then 1 else 0 := by
  simp [map_apply, flipMatrix_apply_apply, and_comm]

/-- The transpose of the flip unitary has norm `n`: it is `n` times a rank-one projection. -/
private theorem norm_map_transposeₗ_flipMatrix :
    ‖(flipMatrix n).map (transposeₗ ℂ)‖ = n := by
  set P := (flipMatrix n).map (transposeₗ ℂ)
  have hstar : star P = P := by
    ext k l r s
    simp [P, star_apply, flipMatrix_apply_apply, eq_comm, and_comm]
  have hsq : P * P = (n : ℂ) • P := by
    ext k l r s
    simp [P, CStarMatrix.sum_apply, CStarMatrix.mul_apply, flipMatrix_apply_apply, ite_and]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [show P = 0 from CStarMatrix.ext fun k => k.elim0]
  have hP : P ≠ 0 := fun h => by
    have := congrArg (fun Q : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin n) (Fin n) ℂ) =>
      Q ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, hn⟩) h
    simp [P, map_transposeₗ_flipMatrix_apply_apply] at this
  have hnorm : ‖P‖ * ‖P‖ = n * ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar, hsq, norm_smul, Complex.norm_natCast]
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hP) hnorm

/-- The transpose on `M_n(ℂ)` is completely bounded. -/
theorem isCompletelyBounded_transposeₗ (n : ℕ) :
    IsCompletelyBounded (transposeₗ ℂ : CStarMatrix (Fin n) (Fin n) ℂ →ₗ[ℂ] _) :=
  ⟨n, n.cast_nonneg, fun _ x => norm_map_transposeₗ_le x⟩

/-- **The transpose on `M_n(ℂ)` has cb norm `n`.** At level `n` it sends the flip unitary
`[E l k]_{k l}`, of norm `1`, to `[E k l]_{k l}`, of norm `n`. -/
theorem cbNorm_transposeₗ (n : ℕ) :
    cbNorm (transposeₗ ℂ : CStarMatrix (Fin n) (Fin n) ℂ →ₗ[ℂ] _) = n := by
  refine le_antisymm (cbNorm_le_of_bound n.cast_nonneg fun _ x => norm_map_transposeₗ_le x) ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simpa [hn] using cbNorm_nonneg _
  have : NeZero n := ⟨hn.ne'⟩
  have hU := CStarRing.norm_of_mem_unitary (flipMatrix_mem_unitary (n := n))
  have := norm_map_le_cbNorm_mul (isCompletelyBounded_transposeₗ n) (flipMatrix n)
  rwa [norm_map_transposeₗ_flipMatrix, hU, mul_one] at this
end Transpose

end TauCeti
