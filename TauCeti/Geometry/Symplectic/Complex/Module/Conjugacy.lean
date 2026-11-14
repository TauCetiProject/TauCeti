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

On a finite-dimensional real normed space `E` the same normal form holds with a complex
coordinate space as the model: every real-linear `A` with `A² = -1` is multiplication by `i` in
some real-linear frame `ℂⁿ → E`. Such frames turn an equation involving a variable complex
structure near one point into an equation on a complex inner product space whose structure is
close to `i`.

## Main declarations

* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`: `A Φ₁ = Φ₁ i` for some
  real-linear automorphism `Φ₁`.
* `ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`:
  `A Φ = Φ i` for some real-linear isomorphism `Φ : ℂⁿ → E`, on a real normed space `E`.

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

/-- **Complex frames of a complex structure.** A real-linear `A` with `A² = -1` on a
finite-dimensional real normed space `E` is multiplication by `i` in a complex coordinate frame:
some real-linear isomorphism `Φ : ℂⁿ → E` satisfies `A Φ = Φ i`. -/
theorem exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (A : E →L[ℝ] E)
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ E) :
    ∃ (n : ℕ) (Φ : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E),
      A ∘L (Φ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) =
        (Φ : EuclideanSpace ℂ (Fin n) →L[ℝ] E) ∘L
          (I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))) := by
  have hA' (v : E) : A (A v) = -v := congr($hA v)
  obtain ⟨n, b, -⟩ := (⟨A.toLinearMap, by ext v; exact hA' v⟩ : AlmostComplexStructure E)
    |>.exists_basis_apply_one_eq
  -- Any real-linear isomorphism `Ψ : ℂⁿ → E` carries `A` to a complex structure on `ℂⁿ`, which is
  -- conjugate to `i` there.
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = Module.finrank ℝ E := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, Module.finrank_eq_card_basis b]
    simp [mul_comm]
  let Ψ := ContinuousLinearEquiv.ofFinrankEq hdim
  let B : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) := Ψ.symm.arrowCongr Ψ.symm A
  obtain ⟨Φ₁, hΦ₁⟩ := B.exists_continuousLinearEquiv_comp_eq_comp_I_smul (by ext v; simp [B, hA'])
  refine ⟨n, Φ₁.trans Ψ, ContinuousLinearMap.ext fun v ↦ ?_⟩
  have h := congr(Ψ ($hΦ₁ v))
  simpa [B] using h

end ContinuousLinearMap
