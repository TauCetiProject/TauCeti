/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# Real-linear complex structures are conjugate to multiplication by `i`

On a finite-dimensional complex normed space `V`, every real-linear `A` with `A² = -1` is
conjugate to multiplication by `i` through a real-linear automorphism: it sends an adapted basis
`(v₁, i v₁, …, vₙ, i vₙ)` of `i` (`TauCeti.AlmostComplexStructure.exists_basis_apply_one_eq`) to
one `(w₁, A w₁, …, wₙ, A wₙ)` of `A`. This is the pointwise normal form behind the reduction of a
variable complex structure to the standard one in the vector similarity principle.

The same argument applies on a finite-dimensional *real* normed space `V` with a complex structure
`A`: sending an adapted basis of `A` to the standard adapted basis `(e₁, i e₁, …, eₙ, i eₙ)` of
`ℂⁿ` gives real-linear coordinates `T : V ≃L[ℝ] EuclideanSpace ℂ (Fin n)` in which `A` is
multiplication by `i`. These are the coordinates in which estimates for the Cauchy–Riemann operator
`∂ₛ + i ∂ₜ` apply to a target carrying a variable complex structure that equals `A` at one point.

## Main declarations

* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`: `A Φ₁ = Φ₁ i` for some
  real-linear automorphism `Φ₁`.
* `ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_I_smul_comp`:
  `T A = i T` for some real-linear isomorphism `T` onto a complex Euclidean space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (proof of Theorem 2.3.5).
-/

public section

open Complex TauCeti

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Adapted frames at a point.** A real-linear `A` with `A² = -1` on a finite-dimensional complex
vector space is conjugate to multiplication by `i`: some real-linear automorphism `Φ₁` satisfies
`A Φ₁ = Φ₁ i`. It sends an adapted basis `(v₁, i v₁, …, vₙ, i vₙ)` to an adapted basis
`(w₁, A w₁, …, wₙ, A wₙ)`. -/
theorem exists_continuousLinearEquiv_comp_eq_comp_I_smul (A : V →L[ℝ] V)
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) :
    ∃ Φ₁ : V ≃L[ℝ] V,
      A ∘L (Φ₁ : V →L[ℝ] V) = (Φ₁ : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V) := by
  have hA' (v : V) : A (A v) = -v := congr($hA v)
  let JA : AlmostComplexStructure V := ⟨A.toLinearMap, by ext v; exact hA' v⟩
  obtain ⟨n, bA, hbA⟩ := JA.exists_basis_apply_one_eq
  obtain ⟨m, bI, hbI⟩ := (AlmostComplexStructure.ofComplexModule V).exists_basis_apply_one_eq
  obtain rfl : n = m := by
    have h := (Module.finrank_eq_card_basis bA).symm.trans (Module.finrank_eq_card_basis bI)
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    omega
  have hbA' (i : Fin n) : bA (i, 1) = A (bA (i, 0)) := hbA i
  have hbI₀ (i : Fin n) : I • bI (i, 0) = bI (i, 1) := by
    rw [hbI i]
    exact (AlmostComplexStructure.ofComplexModule_apply _).symm
  have hbI₁ (i : Fin n) : I • bI (i, 1) = -bI (i, 0) := by
    rw [← hbI₀, smul_smul, I_mul_I, neg_one_smul]
  let e := (bI.equiv bA (Equiv.refl _)).toContinuousLinearEquiv
  have he (x) : e (bI x) = bA x := bI.equiv_apply x bA (Equiv.refl _)
  refine ⟨e, coe_injective (bI.ext fun ⟨i, k⟩ => ?_)⟩
  -- Both sides send `bI (i, 0)` to `bA (i, 1)` and `bI (i, 1)` to `-bA (i, 0)`.
  fin_cases k <;> simp [he, hbI₀, hbI₁, hbA', hA']

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] in
/-- **Complex coordinates for a complex structure.** A real-linear `A` with `A² = -1` on a
finite-dimensional real normed space is multiplication by `i` in suitable coordinates: some
real-linear isomorphism `T` onto a complex Euclidean space satisfies `T A = i T`. It sends an
adapted basis `(w₁, A w₁, …, wₙ, A wₙ)` of `A` to the adapted basis `(e₁, i e₁, …, eₙ, i eₙ)`. -/
theorem exists_continuousLinearEquiv_euclideanSpace_comp_eq_I_smul_comp [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) :
    ∃ (n : ℕ) (T : V ≃L[ℝ] EuclideanSpace ℂ (Fin n)),
      (T : V →L[ℝ] EuclideanSpace ℂ (Fin n)) ∘L A =
        (I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))) ∘L
          (T : V →L[ℝ] EuclideanSpace ℂ (Fin n)) := by
  have hA' (v : V) : A (A v) = -v := congr($hA v)
  let JA : AlmostComplexStructure V := ⟨A.toLinearMap, by ext v; exact hA' v⟩
  obtain ⟨n, bA, hbA⟩ := JA.exists_basis_apply_one_eq
  obtain ⟨m, bI, hbI⟩ :=
    (AlmostComplexStructure.ofComplexModule (EuclideanSpace ℂ (Fin n))).exists_basis_apply_one_eq
  obtain rfl : m = n := by
    have h := Module.finrank_eq_card_basis bI
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin] at h
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    omega
  have hbA' (i : Fin m) : bA (i, 1) = A (bA (i, 0)) := hbA i
  have hbI₀ (i : Fin m) : I • bI (i, 0) = bI (i, 1) := by
    rw [hbI i]
    exact (AlmostComplexStructure.ofComplexModule_apply _).symm
  have hbI₁ (i : Fin m) : I • bI (i, 1) = -bI (i, 0) := by
    rw [← hbI₀, smul_smul, I_mul_I, neg_one_smul]
  let T := (bA.equiv bI (Equiv.refl _)).toContinuousLinearEquiv
  have hT (x) : T (bA x) = bI x := bA.equiv_apply x bI (Equiv.refl _)
  refine ⟨m, T, coe_injective (bA.ext fun ⟨i, k⟩ => ?_)⟩
  -- Both sides send `bA (i, 0)` to `bI (i, 1)` and `bA (i, 1)` to `-bI (i, 0)`.
  have hAbA : A (bA (i, 1)) = -bA (i, 0) := by rw [hbA', hA']
  fin_cases k
  · simp [← hbA', hT, hbI₀]
  · simp [hAbA, hT, hbI₁]

end ContinuousLinearMap
