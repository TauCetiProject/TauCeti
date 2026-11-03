/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.AdicCompletion.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.Matrix.AdicComplete
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# Approximate isometries over an adically complete ring

Let `R` be `π`-adically complete, for instance `ℤ_[p]` with `π = p`, and let `C'` be a symmetric
bilinear form on a finite free `R`-module whose Gram matrix `G` admits a symmetric matrix `H` with
even diagonal and `G * H = π ^ j • 1`. Thus `π ^ j • G⁻¹` is integral and *even*: the scales of
`C'` are at most `π ^ j`, and its constituent of scale `π ^ j` is even at its own scale. This
file proves that a linear map `φ` carrying `C'` to a symmetric form `C` modulo `π ^ (j + 1)`, and
the self-pairings modulo `2 π ^ (j + 1)`, is congruent modulo `π` to a linear map carrying `C'`
exactly to `C` (`LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`). Consequently two such
forms related by approximate isometries in both directions are isometric
(`LinearMap.BilinForm.IsSymm.equivalent_of_dvd_sub`).

When `2` is a unit the parity conditions are automatic, and this is the classical statement that a
lattice whose discriminant group is killed by `π ^ j` is determined by its Gram matrix modulo
`π ^ (j + 1)`. At `π = 2` the hypothesis on `C'` holds for a dyadic lattice whose Jordan
constituents have scale at most `2 ^ j`, the one of scale `2 ^ j` being of type II, and the
precision required is the Gram matrix modulo `2 ^ (j + 1)` together with the self-pairings modulo
`2 ^ (j + 2)` (`LinearMap.BilinForm.IsJordanSplitting.exists_isometry_of_dvd_sub`). For `j = 0` this
is the analogue over complete rings of the reduction theorem for even unimodular forms
`LinearMap.BilinForm.IsSymm.equivalent_of_sub_mem_maximalIdeal_of_even`. Without the parity
condition on `C'` the statement fails: the forms `⟨1⟩` and `⟨5⟩` over `ℤ_[2]` agree modulo `2`,
with self-pairings agreeing modulo `4`, but they are not isometric.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`: an approximate isometry is congruent
  modulo `π` to an exact one.
* `LinearMap.BilinForm.IsSymm.equivalent_of_dvd_sub`: two forms satisfying the hypotheses, with
  approximate isometries in both directions, are isometric.

## Implementation notes

In a basis, the statement is Newton's method for Gram matrices,
`Matrix.exists_transpose_mul_mul_eq_of_sub_eq`, applied to the Gram matrix of `C` pulled back along
`φ`. The parity conditions are what allow the error to be written as `π ^ (j + 1) • (D + Dᵀ)`.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace LinearMap.BilinForm

variable {R M M' n : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Fintype n] [DecidableEq n] {C : BilinForm R M} {C' : BilinForm R M'}

/-- **Approximate isometries over an adically complete ring.** Let `R` be `π`-adically complete,
let `C` and `C'` be symmetric, and let `b` be a basis of the domain of `C'`. Suppose that the Gram
matrix of `C'` times some symmetric matrix `H` with even diagonal is `π ^ j • 1`. If a linear map
`φ` carries `C'` to `C` modulo `π ^ (j + 1)`, and the self-pairings modulo `2 * π ^ (j + 1)`, then a
linear map `ψ ≡ φ` modulo `π` carries `C'` exactly to `C`. -/
theorem IsSymm.exists_isometry_of_dvd_sub (π : R) [IsAdicComplete (Ideal.span {π}) R]
    (hC : C.IsSymm) (hC' : C'.IsSymm) (b : Basis n R M') {j : ℕ} {H : Matrix n n R}
    (hH : C'.toMatrix b * H = π ^ j • 1) (hHs : H.IsSymm) (hHd : ∀ i, 2 ∣ H i i)
    (φ : M' →ₗ[R] M) (h₁ : ∀ x y, π ^ (j + 1) ∣ C' x y - C (φ x) (φ y))
    (h₂ : ∀ x, 2 * π ^ (j + 1) ∣ C' x x - C (φ x) (φ x)) :
    ∃ τ : M' →ₗ[R] M', ∀ x y, C (φ (x + π • τ x)) (φ (y + π • τ y)) = C' x y := by
  obtain ⟨H₀, hH₀⟩ := hHs.exists_eq_smul_add_transpose 1 (fun _ _ ↦ one_dvd _)
    (fun i ↦ by simpa using hHd i)
  rw [one_smul] at hH₀
  set G := C'.toMatrix b
  set A := BilinForm.toMatrix b (C.comp φ φ)
  have hG : G.IsSymm := by
    ext i i'
    simp [G, toMatrix_apply, hC'.eq (b i') (b i)]
  have hE : (G - A).IsSymm := by
    ext i i'
    simp [G, A, toMatrix_apply, hC'.eq (b i') (b i), hC.eq (φ (b i')) (φ (b i))]
  obtain ⟨D, hD⟩ := hE.exists_eq_smul_add_transpose (π ^ (j + 1))
    (fun i i' ↦ by simpa [G, A, toMatrix_apply] using h₁ (b i) (b i'))
    (fun i ↦ by simpa [G, A, toMatrix_apply] using h₂ (b i))
  obtain ⟨V, hV⟩ := Matrix.exists_transpose_mul_mul_eq_of_sub_eq π hG (hH₀ ▸ hH) hD
  refine ⟨Matrix.toLin b b V, fun x y ↦ ?_⟩
  have hT : (LinearMap.id + π • Matrix.toLin b b V) = Matrix.toLin b b (1 + π • V) := by
    simp [map_add, map_smul, Matrix.toLin_one]
  have hcomp : BilinForm.toMatrix b ((C.comp φ φ).comp (Matrix.toLin b b (1 + π • V))
      (Matrix.toLin b b (1 + π • V))) = BilinForm.toMatrix b C' := by
    rw [toMatrix_comp b b, LinearMap.toMatrix_toLin]
    exact hV
  have := (BilinForm.toMatrix b).injective hcomp
  rw [← hT] at this
  simpa using LinearMap.congr_fun₂ this x y

/-- **Two-sided approximate isometries.** Over a `π`-adically complete domain with `π ≠ 0`, let `C`
and `C'` be symmetric forms on finite free modules, each satisfying the hypothesis of
`LinearMap.BilinForm.IsSymm.exists_isometry_of_dvd_sub`: its Gram matrix times a symmetric matrix
with even diagonal is `π ^ j • 1`. If linear maps in both directions carry each form to the other
modulo `π ^ (j + 1)`, and the self-pairings modulo `2 * π ^ (j + 1)`, then `C` and `C'` are
isometric. -/
theorem IsSymm.equivalent_of_dvd_sub [IsDomain R] (π : R) [IsAdicComplete (Ideal.span {π}) R]
    (hπ : π ≠ 0) (hC : C.IsSymm) (hC' : C'.IsSymm) {m : Type*} [Fintype m] [DecidableEq m]
    (c : Basis m R M) (b : Basis n R M') {j : ℕ} {H : Matrix m m R} {H' : Matrix n n R}
    (hH : C.toMatrix c * H = π ^ j • 1) (hHs : H.IsSymm) (hHd : ∀ i, 2 ∣ H i i)
    (hH' : C'.toMatrix b * H' = π ^ j • 1) (hH's : H'.IsSymm) (hH'd : ∀ i, 2 ∣ H' i i)
    (φ : M' →ₗ[R] M) (h₁ : ∀ x y, π ^ (j + 1) ∣ C' x y - C (φ x) (φ y))
    (h₂ : ∀ x, 2 * π ^ (j + 1) ∣ C' x x - C (φ x) (φ x))
    (φ' : M →ₗ[R] M') (h₁' : ∀ x y, π ^ (j + 1) ∣ C x y - C' (φ' x) (φ' y))
    (h₂' : ∀ x, 2 * π ^ (j + 1) ∣ C x x - C' (φ' x) (φ' x)) :
    C.Equivalent C' := by
  have : Module.Free R M := .of_basis c
  have : Module.Finite R M := .of_basis c
  have : Module.Free R M' := .of_basis b
  have : Module.Finite R M' := .of_basis b
  obtain ⟨τ, hτ⟩ := hC.exists_isometry_of_dvd_sub π hC' b hH' hH's hH'd φ h₁ h₂
  obtain ⟨τ', hτ'⟩ := hC'.exists_isometry_of_dvd_sub π hC c hH hHs hHd φ' h₁' h₂'
  set ψ : M' →ₗ[R] M := φ ∘ₗ (LinearMap.id + π • τ)
  set ψ' : M →ₗ[R] M' := φ' ∘ₗ (LinearMap.id + π • τ')
  have hψ (x y : M') : C (ψ x) (ψ y) = C' x y := by simpa [ψ] using hτ x y
  have hψ' (x y : M) : C' (ψ' x) (ψ' y) = C x y := by simpa [ψ'] using hτ' x y
  -- The two composites are isometries of nondegenerate forms, hence bijective.
  have hbij : Function.Bijective (ψ ∘ₗ ψ') :=
    TauCeti.BilinForm.IsIsometry.bijective
      (separatingLeft_of_toMatrix_mul_eq_smul c (pow_ne_zero _ hπ) hH)
      ((TauCeti.BilinForm.isIsometry_iff (B := C)).mpr fun x y ↦ by simp [hψ, hψ'])
  have hbij' : Function.Bijective (ψ' ∘ₗ ψ) :=
    TauCeti.BilinForm.IsIsometry.bijective
      (separatingLeft_of_toMatrix_mul_eq_smul b (pow_ne_zero _ hπ) hH')
      ((TauCeti.BilinForm.isIsometry_iff (B := C')).mpr fun x y ↦ by simp [hψ, hψ'])
  rw [LinearMap.coe_comp] at hbij hbij'
  have hψbij : Function.Bijective ψ := ⟨.of_comp hbij'.1, .of_comp hbij.2⟩
  exact ⟨{ (LinearEquiv.ofBijective ψ hψbij).symm with
    map_app' x y := by
      obtain ⟨x, rfl⟩ := hψbij.2 x
      obtain ⟨y, rfl⟩ := hψbij.2 y
      simp [hψ] }⟩

end LinearMap.BilinForm
