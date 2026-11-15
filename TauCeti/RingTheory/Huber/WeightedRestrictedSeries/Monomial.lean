/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Weighted monomials in subrings of `A⟨X⟩_T`

For a weight family `T = (T₁, …, Tₖ)` of subsets of a nonarchimedean ring `A`, the weighted
variables `t Xᵢ` with `t ∈ Tᵢ` generate the weighted monomials `t Xν` with `t ∈ Tν`, and together
with constants from a subring `R ⊆ A` they generate every monomial `a Xν` with `a ∈ Tν · R`. These
membership statements hold for arbitrary subrings of `A⟨X⟩_T` and are the polynomial part of the
generation results for `R⟨X⟩_T`.

## Main results

* `TauCeti.Huber.weightedC_mul_weightedX_mem_weightedSubring`: `R⟨X⟩_T` contains the weighted
  variables `t Xᵢ`.
* `TauCeti.Huber.weightedPolynomialHom_monomial_mem`: a subring containing the weighted variables
  contains the weighted monomials `t Xν`.
* `TauCeti.Huber.weightedPolynomialHom_monomial_mem_of_mem_weightMul`: a subring containing the
  constants from `R` and the weighted monomials contains every monomial `a Xν` with
  `a ∈ Tν · R`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48 for
  `A⟨X⟩_T`.
-/

public section

open Pointwise

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {T : Fin k → Set A} (hT : IsWeightFamily T)

variable {hT} in
/-- `R⟨X⟩_T` contains the weighted variables `t Xᵢ` with `t ∈ Tᵢ`, for any subring `R`. -/
theorem weightedC_mul_weightedX_mem_weightedSubring {R : Subring A} {i : Fin k} {t : A}
    (ht : t ∈ T i) : weightedC T hT t * weightedX T hT i ∈ weightedSubring T hT R := by
  have h : weightedPolynomialHom T hT (MvPolynomial.monomial (Finsupp.single i 1) t) ∈
      weightedSubring T hT R :=
    weightedPolynomialHom_monomial_mem_weightedSubring.mpr <| by
      simpa using mul_mem_weightMul T _ R.toAddSubgroup
        (by rwa [weightPow_single, pow_one]) R.one_mem
  simpa [← MvPolynomial.C_mul_X_eq_monomial] using h

/-- A subring of `A⟨X⟩_T` containing every weighted variable `t Xᵢ` with `t ∈ Tᵢ` contains every
weighted monomial `t Xν` with `t ∈ Tν`. -/
theorem weightedPolynomialHom_monomial_mem {B : Subring (weightedRestrictedSubring T hT)}
    (hX : ∀ i, ∀ t ∈ T i, weightedC T hT t * weightedX T hT i ∈ B) (ν : Fin k →₀ ℕ) :
    ∀ t ∈ weightPow T ν, weightedPolynomialHom T hT (MvPolynomial.monomial ν t) ∈ B := by
  induction ν using Finsupp.induction_linear with
  | zero =>
    intro t ht
    obtain rfl : t = 1 := by simpa using ht
    simp
  | add μ ν hμ hν =>
    intro t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp (weightPow_add T μ ν ▸ ht)
    rw [← MvPolynomial.monomial_mul_monomial, map_mul]
    exact mul_mem (hμ a ha) (hν b hb)
  | single i m =>
    rw [weightPow_single]
    induction m with
    | zero =>
      intro t ht
      obtain rfl : t = 1 := by simpa using ht
      simp
    | succ m ih =>
      intro t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp (pow_succ (T i) m ▸ ht)
      rw [Finsupp.single_add, ← MvPolynomial.monomial_mul_monomial, map_mul,
        ← MvPolynomial.C_mul_X_eq_monomial, map_mul, weightedPolynomialHom_C,
        weightedPolynomialHom_X]
      exact mul_mem (ih a ha) (hX i b hb)

/-- A subring of `A⟨X⟩_T` containing the constants from `R` and every weighted monomial `t Xν`
with `t ∈ Tν` contains every monomial `a Xν` with `a ∈ Tν · R`. -/
theorem weightedPolynomialHom_monomial_mem_of_mem_weightMul
    {Q : Subring (weightedRestrictedSubring T hT)} {R : Subring A}
    (hC : ∀ a ∈ R, weightedC T hT a ∈ Q)
    (hmon : ∀ ν, ∀ t ∈ weightPow T ν, weightedPolynomialHom T hT (MvPolynomial.monomial ν t) ∈ Q)
    {ν : Fin k →₀ ℕ} {a : A} (ha : a ∈ weightMul T ν R.toAddSubgroup) :
    weightedPolynomialHom T hT (MvPolynomial.monomial ν a) ∈ Q := by
  rw [weightMul_def] at ha
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.mp hx
    rw [mul_comm, ← MvPolynomial.C_mul_monomial, map_mul, weightedPolynomialHom_C]
    exact mul_mem (hC u hu) (hmon ν t ht)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, map_neg]; exact neg_mem hx

end TauCeti.Huber
