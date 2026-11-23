/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Matrix
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Normalization
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The crossing form formula for the Conley–Zehnder index

Let `Ψ : [0, 1] → Sp(2n, ℝ)` be a path of symplectic matrices. Its *crossings* are the parameters
`t` at which `Ψ t` has the eigenvalue `1`, that is, at which the graph of `Ψ t` meets the diagonal.
At a crossing `t` where `Ψ` has derivative `Ψ' t`, the *crossing form* of Robbin and Salamon is the
quadratic form

`Γ(Ψ, t) (v) = -v ⬝ᵥ J Ψ'(t) v`, `v ∈ ker (Ψ t - 1)`,

that is, `Matrix.crossingForm (Ψ t - 1) (-(J * Ψ' t))`. Writing `Ψ' = J S Ψ` with `S` symmetric,
as for the linearized flow of a Hamiltonian, this is the form `v ↦ v ⬝ᵥ S v` of `S` on the fixed
vectors of `Ψ t` (`Matrix.crossingForm_sub_one_neg_J_mul_J_mul_mul`). A crossing is *regular*
when its crossing form is nondegenerate.

This file proves the crossing form formula for the Conley–Zehnder index
`TauCeti.GLSymplectic.conleyZehnderIndex` of a path that never has the eigenvalue `-1` and whose
crossings are regular
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_crossingForm_add_finsum_of_isUnit_det_add_one`):

`CZ(Ψ) = -((sign Γ(Ψ, 0) + sign Γ(Ψ, 1)) / 2 + ∑ᶠ t ∈ (0, 1), sign Γ(Ψ, t))`.

The crossings at the endpoints count one half, parameters that are not crossings contribute zero,
and the sign is the convention `CZ = -μ_RS` of `TauCeti.GLSymplectic.conleyZehnderIndex`. For the
path `t ↦ exp (t J S)` with `S` small, symmetric and nondegenerate, the only crossing is `t = 0`,
where the crossing form is the form of `S` on the whole space, and the formula returns the
normalization `-signature(S) / 2` of
`TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_signature_div_two`.

The proof runs through the symmetric matrices `K t = (Ψ t)ᵀ J - J Ψ t`. For a path avoiding `-1`,
the index is half the drop of the signature of `K`
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one`), and the change
of the signature of a path of symmetric matrices with regular crossings is given by the signatures
of its crossing forms (`Matrix.signature_sub_signature_eq_crossingForm_add_two_mul_finsum`). The
path `K` is linear in `Ψ`, so its derivative is `(Ψ' t)ᵀ J - J Ψ' t`. Its crossings are those of
`Ψ`: a symplectic `Ψ` satisfies `Ψᵀ J - J Ψ = (Ψ + 1)ᵀ (-J (Ψ - 1))`, so `K t` and `Ψ t - 1`
have the same kernel when `Ψ t + 1` is invertible
(`Matrix.ker_mulVecLin_transpose_mul_J_sub_J_mul`). On every vector `v`,
`v ⬝ᵥ (Bᵀ J - J B) v = 2 (-v ⬝ᵥ J B v)`, so the crossing form of `K` is twice the crossing form
`Γ(Ψ, t)`, with the same signature.

## Main results

* `Matrix.crossingForm_sub_one_neg_J_mul_J_mul_mul`: for `Ψ' = J S Ψ`, the crossing form is the
  form of `S` on the fixed vectors of `Ψ`.
* `TauCeti.GLSymplectic.conleyZehnderIndex_eq_neg_crossingForm_add_finsum_of_isUnit_det_add_one`:
  the crossing form formula for the Conley–Zehnder index of a path avoiding `-1` with regular
  crossings.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index of a path of symplectic matrices, its crossing form
  `Γ(Ψ, t) = ω₀(v, Ψ'(t) v)` on `ker (Ψ(t) - 1)` and the formula for paths with regular
  crossings).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the crossing form of a path `Ψ' = J S Ψ` as the form of
  `S` on the fixed vectors).
-/

public section

open Set
open scoped unitInterval Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- **The crossing form of a Hamiltonian path.** If `Ψ' = J S Ψ`, the crossing form of `Ψ` with
derivative `Ψ'` is the quadratic form of `S` on the fixed vectors of `Ψ`. -/
theorem crossingForm_sub_one_neg_J_mul_J_mul_mul (Ψ S : Matrix (n ⊕ n) (n ⊕ n) R) :
    crossingForm (Ψ - 1) (-(J n R * (J n R * S * Ψ))) = crossingForm (Ψ - 1) S := by
  ext x
  have hfix : Ψ *ᵥ (x : n ⊕ n → R) = x := by
    simpa [sub_mulVec, sub_eq_zero] using LinearMap.mem_ker.1 x.property
  simp [crossingForm_apply, ← Matrix.mul_assoc, J_squared, ← mulVec_mulVec, hfix]

/-- Away from the eigenvalue `-1`, the crossing form of `Ψᵀ J - J Ψ` with derivative
`Ψ'ᵀ J - J Ψ'` is isometric to twice the crossing form of `Ψ` with derivative `Ψ'`. -/
private noncomputable def crossingFormIsometryEquivSymplectic {Ψ : Matrix (n ⊕ n) (n ⊕ n) R}
    (hΨ : Ψ ∈ symplecticGroup n R) (h : IsUnit (Ψ + 1).det) (Ψ' : Matrix (n ⊕ n) (n ⊕ n) R) :
    (crossingForm (Ψᵀ * J n R - J n R * Ψ) (Ψ'ᵀ * J n R - J n R * Ψ')).IsometryEquiv
      ((2 : R) • crossingForm (Ψ - 1) (-(J n R * Ψ'))) :=
  ⟨LinearEquiv.ofEq _ _ (ker_mulVecLin_transpose_mul_J_sub_J_mul hΨ h), fun v ↦ by
    simp [dotProduct_transpose_mul_J_sub_J_mul_mulVec]⟩

end Matrix

open Matrix

namespace TauCeti

namespace GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The signature of the crossing form of `Ψᵀ J - J Ψ` is that of the crossing form of `Ψ`. -/
private theorem sigPos_sub_sigNeg_crossingForm_transpose_mul_J_sub_J_mul
    {Ψ : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨ : Ψ ∈ symplecticGroup n ℝ) (h : IsUnit (Ψ + 1).det)
    (Ψ' : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (sigPos (crossingForm (Ψᵀ * J n ℝ - J n ℝ * Ψ) (Ψ'ᵀ * J n ℝ - J n ℝ * Ψ')) : ℤ) -
        sigNeg (crossingForm (Ψᵀ * J n ℝ - J n ℝ * Ψ) (Ψ'ᵀ * J n ℝ - J n ℝ * Ψ')) =
      (sigPos (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))) : ℤ) -
        sigNeg (crossingForm (Ψ - 1) (-(J n ℝ * Ψ'))) := by
  have e : QuadraticMap.Equivalent _ _ := ⟨crossingFormIsometryEquivSymplectic hΨ h Ψ'⟩
  rw [e.sigPos_eq, e.sigNeg_eq, QuadraticForm.sigPos_smul_of_pos _ two_pos,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]

/-- Along a path `Ψ` of symplectic matrices avoiding the eigenvalue `-1`, with regular crossings,
the signature of `Ψᵀ J - J Ψ` changes by the signatures of the crossing forms of `Ψ`, counted twice
at the interior crossings and once at the endpoints. -/
private theorem signature_transpose_mul_J_sub_J_mul_sub_signature
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ} (hΨc : ContinuousOn Ψ (Icc 0 1))
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, Ψ t ∈ symplecticGroup n ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (Ψ t + 1).det)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    signature ((Ψ 1)ᵀ * J n ℝ - J n ℝ * Ψ 1) - signature ((Ψ 0)ᵀ * J n ℝ - J n ℝ * Ψ 0) =
      (sigPos (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) : ℤ) -
          sigNeg (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) +
        2 * ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
          ((sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
            sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t)))) +
        ((sigPos (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1))) : ℤ) -
          sigNeg (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1)))) := by
  -- The symmetric matrices `K t = Ψᵀ J - J Ψ` and their derivatives.
  obtain ⟨K, hK⟩ : ∃ K : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ, ∀ t, K t = (Ψ t)ᵀ * J n ℝ - J n ℝ * Ψ t :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ,
      ∀ t, K' t = (Ψ' t)ᵀ * J n ℝ - J n ℝ * Ψ' t :=
    ⟨_, fun _ ↦ rfl⟩
  have hKc : ContinuousOn K (Icc 0 1) := by
    have h : ContinuousOn (fun t ↦ (Ψ t)ᵀ * J n ℝ - J n ℝ * Ψ t) (Icc 0 1) :=
      ((continuous_id.matrix_transpose.matrix_mul continuous_const).continuousOn.comp hΨc
        (mapsTo_univ _ _)).sub ((continuous_const.matrix_mul continuous_id).continuousOn.comp hΨc
        (mapsTo_univ _ _))
    exact h.congr fun t _ ↦ hK t
  have hKsymm (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : (K t).IsSymm := by
    rw [hK]
    exact transpose_transpose_mul_J_sub_J_mul (Ψ t)
  -- The crossings of `K` are those of `Ψ`.
  have hdet (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hKt : (K t).det = 0) : (Ψ t - 1).det = 0 := by
    by_contra hne
    have hker : LinearMap.ker (K t).mulVecLin = ⊥ := by
      rw [hK, ker_mulVecLin_transpose_mul_J_sub_J_mul (hmem t ht) (h₁ t ht), LinearMap.ker_eq_bot]
      exact mulVec_injective_of_det_ne_zero hne
    exact ((isUnit_iff_isUnit_det _).1
      (mulVec_injective_iff_isUnit.1 (LinearMap.ker_eq_bot.1 hker))).ne_zero hKt
  have hKd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hKt : (K t).det = 0) (i j : n ⊕ n) :
      HasDerivWithinAt (fun r ↦ K r i j) (K' t i j) (Icc 0 1) t := by
    have hΨd := hd t ht (hdet t ht hKt)
    simp only [hK, hK', Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (HasDerivWithinAt.fun_sum fun k _ ↦ (hΨd k i).mul_const _).sub
      (HasDerivWithinAt.fun_sum fun k _ ↦ (hΨd k j).const_mul _)
  -- The crossing forms of `K` are twice those of `Ψ`.
  have hcross (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (sigPos (crossingForm (K t) (K' t)) : ℤ) - sigNeg (crossingForm (K t) (K' t)) =
        (sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
          sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) := by
    rw [hK, hK']
    exact sigPos_sub_sigNeg_crossingForm_transpose_mul_J_sub_J_mul (hmem t ht) (h₁ t ht) (Ψ' t)
  have hKreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hKt : (K t).det = 0) :
      (crossingForm (K t) (K' t)).Nondegenerate := by
    rw [hK, hK']
    exact (crossingFormIsometryEquivSymplectic (hmem t ht) (h₁ t ht) (Ψ' t)).nondegenerate_iff.2
      ((QuadraticMap.nondegenerate_smul_iff (isUnit_iff_ne_zero.2 two_ne_zero) _).2
        (hreg t ht (hdet t ht hKt)))
  rw [← hK, ← hK, signature_sub_signature_eq_crossingForm_add_two_mul_finsum zero_lt_one hKc
    hKsymm hKd hKreg, hcross 0 (left_mem_Icc.2 zero_le_one), hcross 1 (right_mem_Icc.2 zero_le_one),
    finsum_mem_congr rfl fun t ht ↦ hcross t (Ioo_subset_Icc_self ht)]

/-- **The crossing form formula for the Conley–Zehnder index.** Let `γ` be a path of symplectic
matrices, read on `[0, 1]` as a matrix-valued function `Ψ`, none of which has the eigenvalue `-1`.
Suppose that at every crossing `t ∈ [0, 1]`, where `Ψ t` has the eigenvalue `1`, `Ψ` has entrywise
derivative `Ψ' t` within `[0, 1]` and the crossing form
`Matrix.crossingForm (Ψ t - 1) (-(J * Ψ' t))`, the form `v ↦ -v ⬝ᵥ J Ψ' t v` on the fixed vectors
of `Ψ t`, is nondegenerate. Then the Conley–Zehnder index of `γ` is minus the sum of the
signatures of the crossing forms, the crossings at the endpoints counting one half. Parameters
that are not crossings contribute zero. -/
theorem conleyZehnderIndex_eq_neg_crossingForm_add_finsum_of_isUnit_det_add_one
    {A B : GLSymplectic n ℝ} (γ : Path A B)
    {Ψ Ψ' : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hγ : ∀ t : I, ((γ t : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (Ψ t + 1).det)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ Ψ r i j) (Ψ' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (Ψ t - 1).det = 0 →
      (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))).Nondegenerate) :
    conleyZehnderIndex γ =
      -((((sigPos (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) : ℤ) -
            sigNeg (crossingForm (Ψ 0 - 1) (-(J n ℝ * Ψ' 0))) +
          ((sigPos (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1))) : ℤ) -
            sigNeg (crossingForm (Ψ 1 - 1) (-(J n ℝ * Ψ' 1)))) : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
          ((sigPos (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t))) : ℤ) -
            sigNeg (crossingForm (Ψ t - 1) (-(J n ℝ * Ψ' t)))) : ℤ) : ℝ)) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Ψ t ∈ symplecticGroup n ℝ := by
    simpa [← hγ ⟨t, ht⟩] using mem_iff_mem_symplecticGroup.1 (γ ⟨t, ht⟩).property
  have hΨc : ContinuousOn Ψ (Icc 0 1) := by
    refine (Units.continuous_val.comp (continuous_subtypeVal.comp
      γ.continuous_extend)).continuousOn.congr fun t ht ↦ ?_
    simp [← hγ ⟨t, ht⟩, Path.extend_extends' γ ⟨t, ht⟩]
  have hA : ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ 0 := by
    simpa using hγ 0
  have hB : ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ 1 := by
    simpa using hγ 1
  -- The index of a path avoiding `-1` is half the drop of the signature of `Ψᵀ J - J Ψ`.
  rw [conleyZehnderIndex_eq_signature_sub_of_isUnit_det_add_one γ fun t ↦ by
      simpa [hγ t] using h₁ t t.property, hA, hB, ← Int.cast_sub, ← neg_sub,
    signature_transpose_mul_J_sub_J_mul_sub_signature hΨc hmem h₁ hd hreg]
  push_cast
  ring

end GLSymplectic

end TauCeti
