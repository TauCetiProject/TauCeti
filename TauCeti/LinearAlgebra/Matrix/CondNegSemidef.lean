/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Conditionally negative semidefinite matrices

A matrix `ψ`, read as a kernel on its (possibly infinite) index type, is *conditionally negative
semidefinite* when it is Hermitian and `∑ᵢ ∑ⱼ conj(cᵢ) cⱼ ψ(aᵢ, aⱼ) ≤ 0` for every finitely
supported family of coefficients with `∑ᵢ cᵢ = 0`. In the literature such kernels are called
conditionally negative definite, or of negative type; we follow Mathlib's `Matrix.PosSemidef` in
writing `Semidef` for the non-strict inequality. A typical example is `‖f a - f b‖²` for a map `f`
into an inner product space, and for a group `G` a function `ψ : G → ℂ` is conditionally negative
definite when the kernel `(g, h) ↦ ψ (g⁻¹ * h)` is.

These kernels are the logarithms of positive-semidefinite kernels: by Schoenberg's theorem,
`ψ` is conditionally negative semidefinite exactly when `exp (-t ψ)` is positive semidefinite for
every `t ≥ 0`. This file develops the algebraic side, and in particular the centring criterion
that reduces Schoenberg's theorem to the Schur product theorem: for a Hermitian `ψ` and any
base point `a₀`, `ψ` is conditionally negative semidefinite if and only if the kernel

`(a, b) ↦ ψ a a₀ + ψ a₀ b - ψ a b - ψ a₀ a₀`

is positive semidefinite.

## Main declarations

* `Matrix.CondNegSemidef`: conditionally negative semidefinite matrices.
* `Matrix.condNegSemidef_iff_finite_sum`: the characterization by finite families with
  repetitions.
* `Matrix.PosSemidef.neg_condNegSemidef`, `Matrix.CondNegSemidef.add`,
  `Matrix.CondNegSemidef.smul` and `Matrix.CondNegSemidef.submatrix`: closure properties.
* `Matrix.IsHermitian.condNegSemidef_iff_posSemidef_centered`: the centring criterion.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3, §§1–2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Examples 16.1.2.
-/

public section

namespace Matrix

universe u v w

variable {n : Type v} {R : Type u}

section Ring

variable [Ring R] [PartialOrder R] [StarRing R]

/-- A matrix, read as a kernel on its index type, is *conditionally negative semidefinite* when it
is Hermitian and its quadratic form is nonpositive on every finitely supported vector whose
entries sum to zero. -/
def CondNegSemidef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ ∀ x : n →₀ R, (x.sum fun _ xi ↦ xi) = 0 →
    (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj) ≤ 0

/-- A conditionally negative semidefinite matrix is Hermitian. -/
theorem CondNegSemidef.isHermitian {M : Matrix n n R} (hM : M.CondNegSemidef) : M.IsHermitian :=
  hM.1

/-- The quadratic form of a conditionally negative semidefinite matrix is nonpositive on finitely
supported vectors whose entries sum to zero. -/
theorem CondNegSemidef.finsupp_sum_le_zero {M : Matrix n n R} (hM : M.CondNegSemidef)
    {x : n →₀ R} (hx : (x.sum fun _ xi ↦ xi) = 0) :
    (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj) ≤ 0 :=
  hM.2 x hx

/-- **Finite-family criterion.** A matrix is conditionally negative semidefinite exactly when it is
Hermitian and `∑ᵢ ∑ⱼ conj(xᵢ) ψ(vᵢ, vⱼ) xⱼ ≤ 0` for every finite family of indices `vᵢ`, possibly
with repetitions, and coefficients `xᵢ` summing to zero. -/
theorem condNegSemidef_iff_finite_sum {K : Matrix n n R} :
    K.CondNegSemidef ↔
      (∀ a b, star (K a b) = K b a) ∧
        ∀ {ι : Type w} [Fintype ι] (v : ι → n) (x : ι → R), ∑ i, x i = 0 →
          ∑ i, ∑ j, star (x i) * K (v i) (v j) * x j ≤ 0 := by
  classical
  refine ⟨fun hK ↦ ⟨fun a b ↦ hK.isHermitian.apply b a, fun {ι} _ v x hx ↦ ?_⟩,
    fun ⟨hsymm, hneg⟩ ↦ ⟨?_, fun x hx ↦ ?_⟩⟩
  · -- Collect the family into the finitely supported vector `∑ᵢ single (vᵢ) (xᵢ)`.
    have hsum (f : n → R → R) (hf0 : ∀ a, f a 0 = 0)
        (hfadd : ∀ a r s, f a (r + s) = f a r + f a s) :
        (∑ i, Finsupp.single (v i) (x i)).sum f = ∑ i, f (v i) (x i) := by
      rw [← Finsupp.sum_finsetSum_index hf0 hfadd]
      exact Finset.sum_congr rfl fun i _ ↦ Finsupp.sum_single_index (hf0 _)
    have hinner (a : n) (r : R) :
        ((∑ i, Finsupp.single (v i) (x i)).sum fun b yb ↦ star r * K a b * yb) =
          ∑ j, star r * K a (v j) * x j :=
      hsum _ (fun _ ↦ by simp) fun _ _ _ ↦ by simp [mul_add]
    have h := hK.finsupp_sum_le_zero (x := ∑ i, Finsupp.single (v i) (x i))
      (by rw [hsum (fun _ r ↦ r) (fun _ ↦ rfl) fun _ _ _ ↦ rfl]; exact hx)
    rw [hsum _ (fun _ ↦ by simp) fun _ _ _ ↦ by simp [add_mul, Finsupp.sum_add]] at h
    simpa only [hinner] using h
  · ext a b
    exact hsymm b a
  · -- Realize the support of `x` in the universe quantified over by `hneg`.
    let e : ULift.{w} (Fin (Fintype.card x.support)) ≃ x.support :=
      Equiv.ulift.trans (Fintype.equivFin x.support).symm
    have hsupp (f : n → R) : ∑ i, f (e i : n) = ∑ a ∈ x.support, f a := by
      rw [Fintype.sum_equiv e (fun i ↦ f (e i : n)) (fun a ↦ f (a : n)) fun _ ↦ rfl]
      exact Finset.sum_coe_sort x.support f
    have hform : ∑ i, ∑ j, star (x (e i)) * K (e i) (e j) * x (e j) =
        x.sum fun a xa ↦ x.sum fun b xb ↦ star xa * K a b * xb := by
      rw [Finsupp.sum, ← hsupp]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Finsupp.sum, ← hsupp]
    exact hform ▸ hneg (fun i ↦ (e i : n)) (fun i ↦ x (e i)) (by rw [hsupp x]; exact hx)

/-- The negative of a positive-semidefinite matrix is conditionally negative semidefinite. -/
theorem PosSemidef.neg_condNegSemidef [IsOrderedAddMonoid R] {M : Matrix n n R}
    (hM : M.PosSemidef) : (-M).CondNegSemidef :=
  ⟨hM.isHermitian.neg, fun x _ ↦ by simpa using hM.2 x⟩

/-- The sum of two conditionally negative semidefinite matrices is conditionally negative
semidefinite. -/
theorem CondNegSemidef.add [IsOrderedAddMonoid R] {M N : Matrix n n R}
    (hM : M.CondNegSemidef) (hN : N.CondNegSemidef) : (M + N).CondNegSemidef :=
  ⟨hM.isHermitian.add hN.isHermitian, fun x hx ↦ by
    simpa [mul_add, add_mul] using add_nonpos (hM.2 x hx) (hN.2 x hx)⟩

/-- A nonnegative multiple of a conditionally negative semidefinite matrix is conditionally
negative semidefinite. -/
theorem CondNegSemidef.smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulMono α R] {M : Matrix n n R}
    (hM : M.CondNegSemidef) {a : α} (ha : 0 ≤ a) : (a • M).CondNegSemidef :=
  ⟨IsSelfAdjoint.smul (.of_nonneg ha) hM.1, fun x hx ↦ by
    simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using
      smul_nonpos_of_nonneg_of_nonpos ha (hM.2 x hx)⟩

/-- Restricting a conditionally negative semidefinite kernel along any map of index types gives a
conditionally negative semidefinite kernel. -/
theorem CondNegSemidef.submatrix {m : Type*} {M : Matrix n n R} (hM : M.CondNegSemidef)
    (f : m → n) : (M.submatrix f f).CondNegSemidef :=
  condNegSemidef_iff_finite_sum.mpr ⟨fun a b ↦ hM.isHermitian.apply (f b) (f a),
    fun {_ : Type} _ v x hx ↦ (condNegSemidef_iff_finite_sum.mp hM).2 (f ∘ v) x hx⟩

end Ring

section CommRing

variable [CommRing R] [PartialOrder R] [StarRing R]

omit [PartialOrder R] in
/-- The quadratic form of the centring of `ψ` at `a₀` is the negative of the quadratic form of `ψ`
on the family extended by the base point `a₀` with coefficient `-∑ᵢ xᵢ`. -/
private theorem sum_centered_eq_neg {ι : Type*} [Fintype ι] (ψ : Matrix n n R) (a₀ : n)
    (v : ι → n) (x : ι → R) :
    ∑ i, ∑ j, star (x i) * (ψ (v i) a₀ + ψ a₀ (v j) - ψ (v i) (v j) - ψ a₀ a₀) * x j =
      -∑ i : Option ι, ∑ j : Option ι,
        star (Option.elim i (-∑ k, x k) x) * ψ (Option.elim i a₀ v) (Option.elim j a₀ v) *
          Option.elim j (-∑ k, x k) x := by
  -- Both sides are polynomials in `∑ xᵢ`, its conjugate, the linear forms
  -- `∑ conj(xᵢ) ψ(vᵢ, a₀)` and `∑ ψ(a₀, vⱼ) xⱼ`, and the quadratic form of `ψ`.
  have hA : ∑ i, ∑ j, star (x i) * ψ (v i) a₀ * x j =
      (∑ i, star (x i) * ψ (v i) a₀) * ∑ j, x j := by
    rw [Finset.sum_mul_sum]
  have hB : ∑ i, ∑ j, star (x i) * ψ a₀ (v j) * x j =
      (∑ i, star (x i)) * ∑ j, ψ a₀ (v j) * x j := by
    simp only [Finset.sum_mul_sum, mul_assoc]
  have hC : ∑ i, ∑ j, star (x i) * ψ a₀ a₀ * x j =
      (∑ i, star (x i)) * ψ a₀ a₀ * ∑ j, x j := by
    rw [Finset.sum_mul, Finset.sum_mul_sum]
  have hD : ∑ i, star (x i) * ψ (v i) a₀ * (-∑ k, x k) =
      -((∑ i, star (x i) * ψ (v i) a₀) * ∑ j, x j) := by
    rw [← Finset.sum_mul]
    ring
  have hE : ∑ j, star (-∑ k, x k) * ψ a₀ (v j) * x j =
      -((∑ i, star (x i)) * ∑ j, ψ a₀ (v j) * x j) := by
    simp only [star_neg, star_sum, neg_mul, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, Finset.sum_add_distrib]
  rw [hD, hE]
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hA, hB, hC, star_neg, star_sum]
  ring

/-- **Centring criterion.** For a Hermitian matrix `ψ` and a base point `a₀`, `ψ` is conditionally
negative semidefinite exactly when the centred kernel
`(a, b) ↦ ψ a a₀ + ψ a₀ b - ψ a b - ψ a₀ a₀` is positive semidefinite. -/
theorem IsHermitian.condNegSemidef_iff_posSemidef_centered [IsOrderedAddMonoid R]
    {ψ : Matrix n n R} (hψ : ψ.IsHermitian) (a₀ : n) :
    ψ.CondNegSemidef ↔ PosSemidef (of fun a b ↦ ψ a a₀ + ψ a₀ b - ψ a b - ψ a₀ a₀) := by
  have hsymm (a b : n) : star (ψ a b) = ψ b a := hψ.apply b a
  refine ⟨fun h ↦ TauCeti.posSemidef_iff_finite_sum.mpr ⟨fun a b ↦ ?_, fun {ι : Type} _ v x ↦ ?_⟩,
    fun h ↦ condNegSemidef_iff_finite_sum.mpr ⟨hsymm, fun {ι : Type} _ v x hx ↦ ?_⟩⟩
  · simp only [of_apply, star_sub, star_add, hsymm]
    abel
  · -- Extend the family by the base point with coefficient `-∑ᵢ xᵢ`.
    have h' := (condNegSemidef_iff_finite_sum.mp h).2 (fun i : Option ι ↦ Option.elim i a₀ v)
      (fun i ↦ Option.elim i (-∑ k, x k) x) (by simp [Fintype.sum_option])
    simp only [of_apply, sum_centered_eq_neg]
    exact neg_nonneg.mpr h'
  · have h' := (TauCeti.posSemidef_iff_finite_sum.mp h).2 v x
    simp only [of_apply, sum_centered_eq_neg] at h'
    simpa [Fintype.sum_option, hx] using neg_nonneg.mp h'

end CommRing

end Matrix
