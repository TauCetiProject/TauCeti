/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Derivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.SpecialIsogeny

/-!
# The pinned data of type F4 preserves the invariant form

The eight numbered simple root elements `1 + u X + u² X⁽²⁾` of the twenty-six-dimensional module
of type `F₄`, and every point of its weight torus, fix the invariant symmetric bilinear form, over
every commutative ring. Fixing the form means `gᵀ B g = B` for the Gram matrix `B`, the condition
that the bilinear form `(v, w) ↦ vᵀ B w` is unchanged.

The congruence `g B gᵀ = B` is a different condition on `g`, namely that it fixes the form induced
on the dual module, whose Gram matrix is the inverse of `B`; an invertible `g` fixes the one
exactly when it fixes the other with `B` replaced by `B⁻¹`. Since `B` is an involution modulo two,
the two conditions agree there, but they do not agree over the integers, and it is the first that
holds over every commutative ring for the pinned data.

For a root element the verification is the exponential of the statement that its logarithm is
infinitesimally orthogonal, `Xᵀ B + B X = 0`: expanding the invariance equation in the parameter
leaves four coefficient conditions, of which the first is that statement and the remaining three
follow from it together with the divided-power relations. For a torus point the equation is
diagonal and reduces to the cancellation of weights along a nonzero entry of the Gram matrix.

## Main definitions

* `TauCeti.F4ShortRoot.PreservesForm`: invariance of the invariant symmetric bilinear form.

## Main results

* `TauCeti.F4ShortRoot.preservesForm_rootElementMatrix`: **every numbered simple root element
  fixes the invariant form.**
* `TauCeti.F4ShortRoot.preservesForm_weightTorusMatrix`: **every point of the weight torus fixes
  the invariant form.**

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §2.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

universe u

variable {R : Type u} [CommRing R]

/-- A matrix **preserves the invariant form** when it fixes the Gram matrix of the invariant
symmetric bilinear form under the action `g • B = gᵀ B g` on bilinear forms. -/
def PreservesForm (g : Matrix (Fin 26) (Fin 26) R) : Prop :=
  gᵀ * invariantForm.map (Int.cast : ℤ → R) * g = invariantForm.map (Int.cast : ℤ → R)

/-- The defining equation of form invariance. -/
theorem preservesForm_def (g : Matrix (Fin 26) (Fin 26) R) :
    PreservesForm g ↔
      gᵀ * invariantForm.map (Int.cast : ℤ → R) * g = invariantForm.map (Int.cast : ℤ → R) :=
  Iff.rfl

/-- The identity matrix preserves the invariant form. -/
theorem preservesForm_one : PreservesForm (1 : Matrix (Fin 26) (Fin 26) R) := by
  rw [preservesForm_def, Matrix.transpose_one, one_mul, mul_one]

/-- **Matrices preserving the invariant form are closed under multiplication.** -/
theorem PreservesForm.mul {g h : Matrix (Fin 26) (Fin 26) R} (hg : PreservesForm g)
    (hh : PreservesForm h) : PreservesForm (g * h) := by
  rw [preservesForm_def, Matrix.transpose_mul,
    show hᵀ * gᵀ * invariantForm.map (Int.cast : ℤ → R) * (g * h) =
      hᵀ * (gᵀ * invariantForm.map (Int.cast : ℤ → R) * g) * h by noncomm_ring, hg, hh]

/-! ## The infinitesimal condition -/

variable {N P : Matrix (Fin 26) (Fin 26) ℤ}

/-- **The divided square of an infinitesimally orthogonal matrix is self-adjoint** for the
invariant form. -/
theorem transpose_dividedSquare_mul_invariantForm
    (h1 : Nᵀ * invariantForm + invariantForm * N = 0) (hNN : N * N = (2 : ℤ) • P) :
    Pᵀ * invariantForm = invariantForm * P := by
  have hN : Nᵀ * invariantForm = -(invariantForm * N) := by
    rw [← add_eq_zero_iff_eq_neg.mp h1]
  refine smul_right_injective (Matrix (Fin 26) (Fin 26) ℤ) (two_ne_zero (α := ℤ)) ?_
  calc (2 : ℤ) • (Pᵀ * invariantForm)
      = ((2 : ℤ) • P)ᵀ * invariantForm := by rw [Matrix.transpose_smul, Matrix.smul_mul]
    _ = Nᵀ * (Nᵀ * invariantForm) := by rw [← hNN, Matrix.transpose_mul]; noncomm_ring
    _ = Nᵀ * -(invariantForm * N) := by rw [hN]
    _ = -(Nᵀ * invariantForm * N) := by noncomm_ring
    _ = -(-(invariantForm * N) * N) := by rw [hN]
    _ = invariantForm * (N * N) := by noncomm_ring
    _ = (2 : ℤ) • (invariantForm * P) := by rw [hNN, Matrix.mul_smul]

/-- **A divided-power exponential of an infinitesimally orthogonal matrix preserves the invariant
form**, over every commutative ring. -/
theorem preservesForm_one_add_smul_add_smul
    (h1 : Nᵀ * invariantForm + invariantForm * N = 0) (hNN : N * N = (2 : ℤ) • P)
    (hNP : N * P = 0) (hPN : P * N = 0) (hPP : P * P = 0) (t : R) :
    PreservesForm (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R)) := by
  have hN : Nᵀ * invariantForm = -(invariantForm * N) := by
    rw [← add_eq_zero_iff_eq_neg.mp h1]
  have hP : Pᵀ * invariantForm = invariantForm * P :=
    transpose_dividedSquare_mul_invariantForm h1 hNN
  have h2 : Nᵀ * invariantForm * N + (Pᵀ * invariantForm + invariantForm * P) = 0 := by
    rw [hP, hN, Matrix.neg_mul, Matrix.mul_assoc, hNN, Matrix.mul_smul, two_smul]
    abel
  have h3 : Nᵀ * invariantForm * P + Pᵀ * invariantForm * N = 0 := by
    have e1 : Nᵀ * invariantForm * P = 0 := by
      rw [hN, Matrix.neg_mul, Matrix.mul_assoc, hNP, mul_zero, neg_zero]
    have e2 : Pᵀ * invariantForm * N = 0 := by
      rw [hP, Matrix.mul_assoc, hPN, mul_zero]
    rw [e1, e2, add_zero]
  have h4 : Pᵀ * invariantForm * P = 0 := by
    rw [hP, Matrix.mul_assoc, hPP, mul_zero]
  have cast1 : (Nᵀ).map (Int.cast : ℤ → R) * invariantForm.map (Int.cast : ℤ → R) +
      invariantForm.map (Int.cast : ℤ → R) * N.map (Int.cast : ℤ → R) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 26) (Fin 26) ℤ => M.map (Int.cast : ℤ → R)) h1
    rwa [Matrix.map_add _ Int.cast_add, Matrix.map_intCast_mul, Matrix.map_intCast_mul,
      Matrix.map_zero _ Int.cast_zero] at h
  have cast2 : (Nᵀ).map (Int.cast : ℤ → R) * invariantForm.map (Int.cast : ℤ → R) *
        N.map (Int.cast : ℤ → R) +
      ((Pᵀ).map (Int.cast : ℤ → R) * invariantForm.map (Int.cast : ℤ → R) +
        invariantForm.map (Int.cast : ℤ → R) * P.map (Int.cast : ℤ → R)) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 26) (Fin 26) ℤ => M.map (Int.cast : ℤ → R)) h2
    rwa [Matrix.map_add _ Int.cast_add, Matrix.map_add _ Int.cast_add, Matrix.map_intCast_mul,
      Matrix.map_intCast_mul, Matrix.map_intCast_mul, Matrix.map_intCast_mul,
      Matrix.map_zero _ Int.cast_zero] at h
  have cast3 : (Nᵀ).map (Int.cast : ℤ → R) * invariantForm.map (Int.cast : ℤ → R) *
        P.map (Int.cast : ℤ → R) +
      (Pᵀ).map (Int.cast : ℤ → R) * invariantForm.map (Int.cast : ℤ → R) *
        N.map (Int.cast : ℤ → R) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 26) (Fin 26) ℤ => M.map (Int.cast : ℤ → R)) h3
    rwa [Matrix.map_add _ Int.cast_add, Matrix.map_intCast_mul, Matrix.map_intCast_mul,
      Matrix.map_intCast_mul, Matrix.map_intCast_mul, Matrix.map_zero _ Int.cast_zero] at h
  have cast4 : (Pᵀ).map (Int.cast : ℤ → R) * invariantForm.map (Int.cast : ℤ → R) *
      P.map (Int.cast : ℤ → R) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 26) (Fin 26) ℤ => M.map (Int.cast : ℤ → R)) h4
    rwa [Matrix.map_intCast_mul, Matrix.map_intCast_mul, Matrix.map_zero _ Int.cast_zero] at h
  rw [preservesForm_def, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_smul, ← Matrix.transpose_map, ← Matrix.transpose_map,
    Matrix.mul_mul_of_one_add_smul_add_smul, cast1, cast2, cast3, cast4, smul_zero, smul_zero,
    smul_zero, smul_zero, add_zero, add_zero, add_zero, add_zero]

/-! ## The numbered simple root elements -/

/-- **Every numbered simple root generator of the twenty-six-dimensional module of type `F₄` is
infinitesimally orthogonal for the invariant form.** -/
theorem transpose_rootMatrix_mul_invariantForm (k : Fin 4 ⊕ Fin 4) :
    (rootMatrix k)ᵀ * invariantForm + invariantForm * rootMatrix k = 0 := by
  ext p q
  rw [Matrix.add_apply,
    Matrix.IsStep.transpose_mul_apply (M := (rootMatrix k)ᵀ) (isStep_rootMatrix k),
    Matrix.IsStep.mul_apply (isStep_rootMatrix k), Matrix.zero_apply]
  simp only [invariantForm_apply]
  revert k p q
  decide +kernel

/-- **Every numbered simple root element fixes the invariant form**, over every commutative
ring. -/
theorem preservesForm_rootElementMatrix (k : Fin 4 ⊕ Fin 4) (u : R) :
    PreservesForm (rootElementMatrix k u) := by
  rw [rootElementMatrix_def]
  exact preservesForm_one_add_smul_add_smul (transpose_rootMatrix_mul_invariantForm k)
    (rootMatrix_mul_self k) (rootMatrix_mul_rootDividedSquareMatrix k)
    (rootDividedSquareMatrix_mul_rootMatrix k) (rootDividedSquareMatrix_mul_self k) u

/-! ## The weight torus -/

/-- Weights cancel along a nonzero entry of the Gram matrix of the invariant form. -/
private theorem weight_of_invariantForm_ne_zero :
    ∀ p : Fin 26 × Fin 26, invariantForm p.1 p.2 = 0 ∨
      ∀ i : Fin 4, f4ShortRootWeight p.1 i + f4ShortRootWeight p.2 i = 0 := by
  simp only [invariantForm_apply]
  decide +kernel

/-- **A diagonal matrix fixes the invariant form** when its entries are inverse to one another
along every nonzero entry of the Gram matrix. -/
theorem preservesForm_diagonal {d : Fin 26 → R}
    (hd : ∀ m n : Fin 26, invariantForm m n ≠ 0 → d m * d n = 1) :
    PreservesForm (Matrix.diagonal d) := by
  rw [preservesForm_def, Matrix.diagonal_transpose]
  ext m n
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  by_cases hz : invariantForm m n = 0
  · rw [hz, Int.cast_zero, mul_zero, zero_mul]
  · calc d m * ((invariantForm m n : ℤ) : R) * d n
        = d m * d n * ((invariantForm m n : ℤ) : R) := by ring
      _ = ((invariantForm m n : ℤ) : R) := by rw [hd m n hz, one_mul]

/-- **Every point of the weight torus fixes the invariant form**: the weights cancel along a
nonzero entry of the Gram matrix. -/
theorem preservesForm_weightTorusMatrix (s : Fin 4 → Rˣ) :
    PreservesForm (Matrix.diagonal fun a => (torusCharacter s (f4ShortRootWeight a) : R)) := by
  refine preservesForm_diagonal fun m n hz => ?_
  have hw : f4ShortRootWeight m + f4ShortRootWeight n = 0 :=
    funext ((weight_of_invariantForm_ne_zero (m, n)).resolve_left hz)
  rw [← Units.val_mul, ← torusCharacter_add, hw, torusCharacter_zero, Units.val_one]

end TauCeti.F4ShortRoot
