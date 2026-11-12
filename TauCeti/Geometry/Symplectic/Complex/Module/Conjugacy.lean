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

On a finite-dimensional real normed space `V` there is no multiplication by `i` to compare with,
but a real-linear `A` with `A² = -1` makes `V` a complex vector space
(`TauCeti.AlmostComplexStructure.complexModule`), and a basis of it identifies `V` with complex
coordinate space. This gives a real-linear isomorphism `Φ` from `V` onto the Hilbert space
`EuclideanSpace ℂ (Fin m)` with `Φ (A v) = i Φ v`: complex coordinates in which `A` is the
standard complex structure. Such coordinates bring a nonlinear Cauchy–Riemann equation
`∂ₛu + J(z, u) ∂ₜu = h(z, u)` on a real target into the standard form at one point.

## Main declarations

* `ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`: `A Φ₁ = Φ₁ i` for some
  real-linear automorphism `Φ₁`.
* `ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_apply_eq_I_smul`: on a real
  space, `Φ (A v) = i Φ v` for some real-linear isomorphism `Φ` onto `EuclideanSpace ℂ (Fin m)`.

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

section Real

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Complex coordinates for a real complex structure.** A real-linear `A` with `A² = -1` on a
finite-dimensional real normed space `V` is multiplication by `i` in suitable complex coordinates:
some real-linear isomorphism `Φ` from `V` onto `EuclideanSpace ℂ (Fin m)` satisfies
`Φ (A v) = i Φ v`. -/
theorem exists_continuousLinearEquiv_euclideanSpace_apply_eq_I_smul (A : V →L[ℝ] V)
    (hA : ∀ v, A (A v) = -v) :
    ∃ (m : ℕ) (Φ : V ≃L[ℝ] EuclideanSpace ℂ (Fin m)), ∀ v, Φ (A v) = I • Φ v := by
  let JA : AlmostComplexStructure V := ⟨A.toLinearMap, by ext v; exact hA v⟩
  let := JA.complexModule
  have := JA.complexModule_isScalarTower
  have : Module.Finite ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  -- A complex basis of `(V, A)` gives complex coordinates, which are real-linear in particular.
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    (Module.finBasis ℂ V).equivFun.trans (EuclideanSpace.equiv (Fin _) ℂ).symm.toLinearEquiv
  refine ⟨_, (e.restrictScalars ℝ).toContinuousLinearEquiv, fun v ↦ ?_⟩
  have hv : I • v = A v := JA.complexModule_I_smul v
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.restrictScalars_apply, ← hv,
    map_smul]

end Real

end ContinuousLinearMap
