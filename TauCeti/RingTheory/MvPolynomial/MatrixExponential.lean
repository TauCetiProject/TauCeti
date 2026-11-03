/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Exponential.Truncated
public import TauCeti.RingTheory.MvPolynomial.Jacobian
import TauCeti.Algebra.DualNumber.Matrix

/-!
# Polynomial coordinates of ordered products of matrix exponentials

For a list of matrices `A a`, `List.expProdPoly` gives the polynomial coordinates of the
ordered product of their truncated exponentials applied to a vector parametrized by a family
`c` of vectors. Evaluation recovers the matrix-vector product, and
`List.jacobiMatrixAt_expProdPoly_mulVec` computes its differential when the exponential
parameters vanish. The computation uses evaluation at dual numbers and requires each
truncation degree to be at least two, so its constant and linear terms are retained.
-/

public section

namespace List

open MvPolynomial Matrix TrivSqZeroExt TauCeti

section ExpProd

variable {K ι α κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The vector `(∏_{a ∈ l} exp(t_a A_a)) (∑_j s_j c_j)`, with the exponentials truncated below
the degrees `d a`, for coefficients `t` and `s` in a commutative `K`-algebra `S`. -/
noncomputable def expProdVec {S : Type*} [CommRing S] [Algebra K S] (l : List α)
    (A : α → Matrix ι ι K) (d : α → ℕ) (c : κ → ι → K) (t : α → S) (s : κ → S) : ι → S :=
  (l.map fun a ↦ expSeries (A a) (d a) (t a)).prod *ᵥ ∑ j, s j • fun i ↦ algebraMap K S (c j i)

/-- The matrix-vector formula for the product of truncated exponentials. -/
theorem expProdVec_def {S : Type*} [CommRing S] [Algebra K S] (l : List α)
    (A : α → Matrix ι ι K) (d : α → ℕ) (c : κ → ι → K) (t : α → S) (s : κ → S) :
    expProdVec l A d c t s =
      (l.map fun a ↦ expSeries (A a) (d a) (t a)).prod *ᵥ
        ∑ j, s j • fun i ↦ algebraMap K S (c j i) := (rfl)

/-- An algebra map commutes with an ordered product of truncated exponentials acting on a
parametrized vector. -/
@[simp]
theorem _root_.AlgHom.map_expProdVec {S S' : Type*} [CommRing S] [Algebra K S] [CommRing S']
    [Algebra K S'] (f : S →ₐ[K] S') (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (t : α → S) (s : κ → S) (i : ι) :
    f (expProdVec l A d c t s i) = expProdVec l A d c (f ∘ t) (f ∘ s) i := by
  rw [expProdVec, expProdVec, ← f.coe_toRingHom, RingHom.map_mulVec, f.coe_toRingHom,
    ← AlgHom.mapMatrix_apply, map_list_prod, List.map_map]
  congr 1
  · exact congrArg List.prod (List.map_congr_left fun a _ ↦ by
      simpa only [Function.comp_apply, AlgHom.mapMatrix_apply] using
        f.map_expSeries (A a) (d a) (t a))
  · ext i
    simp [map_sum]

/-- The polynomial coordinates of `(t, s) ↦ (∏_{a ∈ l} exp(t_a A_a)) (∑_j s_j c_j)`. -/
noncomputable def expProdPoly (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (i : ι) : MvPolynomial (α ⊕ κ) K :=
  expProdVec l A d c (fun a ↦ X (Sum.inl a)) (fun j ↦ X (Sum.inr j)) i

/-- The polynomial coordinates are obtained by substituting the two families of variables into
`List.expProdVec`. -/
theorem expProdPoly_def (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (i : ι) :
    expProdPoly l A d c i =
      expProdVec l A d c (fun a ↦ X (Sum.inl a)) (fun j ↦ X (Sum.inr j)) i := (rfl)

/-- Evaluating the polynomial coordinates recovers the ordered product of truncated
exponentials applied to the vector with the given coordinates. -/
@[simp]
theorem eval_expProdPoly (l : List α) (A : α → Matrix ι ι K) (d : α → ℕ)
    (c : κ → ι → K) (x : α ⊕ κ → K) (i : ι) :
    eval x (expProdPoly l A d c i) =
      ((l.map fun a ↦ expSeries (A a) (d a) (x (Sum.inl a))).prod *ᵥ
        ∑ j, x (Sum.inr j) • c j) i := by
  have h := AlgHom.map_expProdVec (aeval x : MvPolynomial (α ⊕ κ) K →ₐ[K] K) l A d c
    (fun a ↦ X (Sum.inl a)) (fun j ↦ X (Sum.inr j)) i
  rw [aeval_eq_eval] at h
  rw [expProdPoly, h, expProdVec]
  simp

/-- **The differential of the parametrization at `t = 0`.** If every `d a` is at least `2`, the
Jacobian matrix at a point with vanishing `t`-coordinates sends a tangent vector `w` to
`(∑_{a ∈ l} w_a A_a) (∑_j s_j c_j) + ∑_j w_j c_j`. -/
theorem jacobiMatrixAt_expProdPoly_mulVec [Fintype α] (l : List α)
    (A : α → Matrix ι ι K) {d : α → ℕ} (hd : ∀ a, 2 ≤ d a) (c : κ → ι → K) (s : κ → K)
    (w : α ⊕ κ → K) :
    jacobiMatrixAt (expProdPoly l A d c) (Sum.elim 0 s) *ᵥ w =
      (l.map fun a ↦ w (Sum.inl a) • A a).sum *ᵥ (∑ j, s j • c j) + ∑ j, w (Sum.inr j) • c j := by
  ext i
  rw [jacobiMatrixAt_mulVec_apply_eq_snd_aeval, expProdPoly, AlgHom.map_expProdVec, expProdVec]
  have hexp : ∀ a, expSeries (A a) (d a)
      ((aeval fun j ↦ inl (Sum.elim 0 s j) + inr (w j) : MvPolynomial (α ⊕ κ) K →ₐ[K] _)
        (X (Sum.inl a))) = 1 + (w (Sum.inl a) • A a).map inr := by
    intro a
    rw [aeval_X, Sum.elim_inl, Pi.zero_apply, inl_zero, zero_add, expSeries_inr (hd a)]
  have hvec : (∑ j, ((aeval fun j ↦ inl (Sum.elim 0 s j) + inr (w j) :
      MvPolynomial (α ⊕ κ) K →ₐ[K] _) (X (Sum.inr j))) •
        fun i ↦ algebraMap K (TrivSqZeroExt K K) (c j i)) =
      fun i ↦ inl ((∑ j, s j • c j) i) + inr ((∑ j, w (Sum.inr j) • c j) i) := by
    ext i
    · simp [algebraMap_eq_inl, Finset.sum_apply, fst_sum]
    · simp [algebraMap_eq_inl, Finset.sum_apply, snd_sum]
  simp only [Function.comp_def, hexp, hvec]
  rw [List.prod_map_one_add_map_inr, Matrix.one_add_map_inr_mulVec, snd_add, snd_inl, zero_add,
    snd_inr]

end ExpProd

end List
