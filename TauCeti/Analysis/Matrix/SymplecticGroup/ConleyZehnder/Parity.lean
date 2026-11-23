/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder

import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The parity of the Conley–Zehnder index

For a path `Ψ` of symplectic matrices of size `2n` from the identity to a matrix `B` without the
eigenvalue `1`, the Conley–Zehnder index is an integer whose parity is the sign of `det (1 - B)`:

`(-1) ^ (n - CZ(Ψ)) = sign det (1 - B)`

(`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one`). For a path between two such
matrices `A` and `B`, the index is an integer with `(-1) ^ CZ(Ψ) = sign (det (1 - A) det (1 - B))`
(`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq`). These are the forms
`e^{πi CZ(Ψ)} = (-1)ⁿ sign det (1 - B)` (`TauCeti.GLSymplectic.exp_conleyZehnderIndex_of_one`) and
`e^{πi CZ(Ψ)} = sign (det (1 - A) det (1 - B))` (`TauCeti.GLSymplectic.exp_conleyZehnderIndex`).

For `n = 1`, the matrices with `det (1 - B) < 0` are the positive hyperbolic ones: their orbits have
even index, and the elliptic and negative hyperbolic ones have odd index. The sign of `det (1 - B)`
is also the sign by which a fixed point of a map with linearization `B` counts in the Lefschetz
number, so the parity of the index records the local fixed point index.

## Proof

The index is `-μ` for the Maslov index `μ` of the path `t ↦ U (Ψ t)` of unitary graph frames, and
`e^{πi μ}` is the quotient of the endpoint values of `U ↦ det U e^{-πi s(U Uᵀ)}`, where `s` is the
spectral angle sum (`Matrix.UnitaryGroup.exp_maslovIndex_mul_det_mul_exp_spectralAngleSum`).
At the identity the graph frame is a positive multiple of a real positive definite matrix and
`U Uᵀ = 1`, so this value is a positive real number. At a matrix `B`, the number
`e^{-πi s(W)} det (1 - W)` is a nonnegative real number for the unitary `W = U Uᵀ`
(`Matrix.exp_neg_spectralAngleSum_mul_det_one_sub_nonneg`), and
`det (1 - U Uᵀ) = det U det (conj U - U)` (`Matrix.UnitaryGroup.det_one_sub_souriau`). For the
straightened graph frame `T Γ(B)` the difference `conj (T Γ(B)) - T Γ(B)` is `i √2 J (B - 1)`
(`TauCeti.map_star_diagonalStraightening_mul_graphFrame_sub`), and the real orthonormalization
multiplies it by a positive definite real matrix. So `det U e^{-πi s(U Uᵀ)}` is a positive multiple
of `((-2) ^ n det (1 - B))⁻¹`, and `e^{πi CZ(Ψ)}`, a complex number of modulus one, is a real number
with the sign of `(-1) ^ n det (1 - B)`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Section 2.4 (the parity of the Conley–Zehnder index).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
-/

public section

open Matrix Matrix.UnitaryGroup Complex
open scoped ComplexOrder

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace GLSymplectic

/-- The endpoint value `det U e^{-πi s(U Uᵀ)}` of the unitary graph frame `U` of `A`. -/
private noncomputable def frameValue (A : GLSymplectic n ℝ) : ℂ :=
  (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
    exp (-(↑(Real.pi * spectralAngleSum
      (souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) * Complex.I))

/-- At the identity, `det U e^{-πi s(U Uᵀ)}` is a positive real number for the unitary graph
frame `U`. -/
private theorem exists_pos_frameValue_one :
    ∃ r : ℝ, 0 < r ∧ frameValue (1 : GLSymplectic n ℝ) = r := by
  obtain ⟨P, hP, hU⟩ := exists_posDef_coe_graphUnitaryFrame (1 : GLSymplectic n ℝ)
  refine ⟨√2 ^ Fintype.card (n ⊕ n) * P.det, by have := hP.det_pos; positivity, ?_⟩
  have hs : spectralAngleSum
      (souriau (graphUnitaryFrame (1 : GLSymplectic n ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 0 := by
    rw [souriau_graphUnitaryFrame_one, OneMemClass.coe_one, ← diagonal_one,
      spectralAngleSum_diagonal]
    simp
  rw [frameValue, hs, hU, OneMemClass.coe_one, Units.val_one,
    diagonalStraightening_mul_graphFrame_one, det_mul, det_map_ofReal, det_map_ofReal]
  simp

/-- The determinant of `(i √2) J M` for a real matrix `M` on `ℝ^{n ⊕ n}` is `(-2) ^ n det M`. -/
private theorem det_I_mul_sqrt_two_smul_map_J_mul (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    ((Complex.I * ((√2 : ℝ) : ℂ)) • (J n ℝ * M).map ((↑) : ℝ → ℂ)).det =
      ↑((-2) ^ Fintype.card n * M.det) := by
  have h : (Complex.I * ((√2 : ℝ) : ℂ)) ^ 2 = -2 := by
    rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt zero_le_two]
    push_cast
    ring
  rw [det_smul, det_map_ofReal, det_mul, det_J, one_mul, Fintype.card_sum, ← two_mul, pow_mul, h]
  push_cast
  ring

/-- At a symplectic matrix `A`, the number `det U e^{-πi s(U Uᵀ)}` for the unitary graph frame `U`,
times `(-2) ^ n det (1 - A)` and a positive real number `d`, is a nonnegative real number. -/
private theorem exists_pos_frameValue_mul_nonneg (A : GLSymplectic n ℝ) :
    ∃ d : ℝ, 0 < d ∧
      0 ≤ frameValue A *
        ↑((-2) ^ Fintype.card n *
          (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det * d) := by
  obtain ⟨P, hP, hU⟩ := exists_posDef_coe_graphUnitaryFrame A
  refine ⟨P.det, hP.det_pos, ?_⟩
  set B := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  set T := diagonalStraightening n * graphFrame B
  -- `star` on `ℂ` is the ring hom `starRingEnd ℂ`, so it commutes with matrix multiplication,
  -- and it fixes the real factor `P`.
  have hmul : (T * P.map ((↑) : ℝ → ℂ)).map star = T.map star * P.map ((↑) : ℝ → ℂ) := by
    refine (Matrix.map_mul (f := starRingEnd ℂ)).trans (congrArg (T.map star * ·) ?_)
    rw [Matrix.map_map]
    exact congrArg P.map (funext fun x => conj_ofReal x)
  -- The imaginary part of the frame is `i √2 J (B - 1)` times the real factor `P`.
  have hdet : ((graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).map star -
      (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ)).det =
        ↑((-2) ^ Fintype.card n * (1 - B).det * P.det) := by
    rw [hU, hmul, ← Matrix.sub_mul, map_star_diagonalStraightening_mul_graphFrame_sub, det_mul,
      det_I_mul_sqrt_two_smul_map_J_mul, det_map_ofReal, ← neg_sub, det_neg, Fintype.card_sum,
      ← two_mul, pow_mul]
    push_cast
    ring
  have h := exp_neg_spectralAngleSum_mul_det_one_sub_nonneg (souriau (graphUnitaryFrame A)).property
  rw [det_one_sub_souriau, hdet] at h
  convert h using 1
  rw [frameValue]
  ring

/-- A nonzero complex number `p d` with `0 ≤ p d` is a positive real number. -/
private theorem exists_pos_eq_of_zero_le_mul {p : ℂ} {d : ℝ} (hp : p ≠ 0) (hd : d ≠ 0)
    (h : 0 ≤ p * d) : ∃ c : ℝ, 0 < c ∧ p * d = c := by
  have h' : ((0 : ℝ) : ℂ) ≤ p * d := by rwa [ofReal_zero]
  refine ⟨(p * d).re, lt_of_le_of_ne (by simpa using (Complex.le_def.1 h).1) fun h0 => ?_,
    eq_re_of_ofReal_le h'⟩
  have := eq_re_of_ofReal_le h'
  rw [← h0, ofReal_zero, mul_eq_zero] at this
  exact this.elim hp (by exact_mod_cast hd)

/-- If `z` has modulus one, `z pB = pA ≠ 0`, and `pA dA`, `pB dB` are nonnegative real numbers for
nonzero reals `dA`, `dB`, then `z` is the sign of `dA dB`. -/
private theorem eq_sign_mul_of_mul_eq {z pA pB : ℂ} {dA dB : ℝ} (hz : ‖z‖ = 1) (hpA : pA ≠ 0)
    (hdA : dA ≠ 0) (hdB : dB ≠ 0) (hA : 0 ≤ pA * dA) (hB : 0 ≤ pB * dB) (h : z * pB = pA) :
    z = (SignType.sign (dA * dB) : ℂ) := by
  have hpB : pB ≠ 0 := by
    rintro rfl
    exact hpA (by rw [← h, mul_zero])
  obtain ⟨cA, hcA, hpcA⟩ := exists_pos_eq_of_zero_le_mul hpA hdA hA
  obtain ⟨cB, hcB, hpcB⟩ := exists_pos_eq_of_zero_le_mul hpB hdB hB
  -- `z` is the real number `x = (cA dB) / (cB dA)`.
  set x := cA * dB / (cB * dA)
  have hzx : z = x := by
    have hpA' : pA = cA / dA := by rw [eq_div_iff (by exact_mod_cast hdA), hpcA]
    have hpB' : pB = cB / dB := by rw [eq_div_iff (by exact_mod_cast hdB), hpcB]
    rw [← eq_div_iff hpB, hpA', hpB'] at h
    rw [h]
    simp only [x]
    push_cast
    field_simp
  have hx : |x| = 1 := by rwa [hzx, norm_real, Real.norm_eq_abs] at hz
  have hsx : SignType.sign x = SignType.sign (dA * dB) := by
    have hk : 0 < cB * (dA * dA) := mul_pos hcB (mul_self_pos.2 hdA)
    have hxk : x * (cB * (dA * dA)) = cA * (dA * dB) := by
      simp only [x]
      field_simp
    have := congrArg SignType.sign hxk
    rwa [sign_mul, sign_mul cA, sign_pos hk, sign_pos hcA, mul_one, one_mul] at this
  rw [hzx, ← hsx]
  rcases (abs_eq zero_le_one).1 hx with h1 | h1 <;> simp [h1]

/-- Along a path `γ` of symplectic matrices from `A` to `B`, `e^{πi CZ(γ)}` carries the endpoint
value `det U e^{-πi s(U Uᵀ)}` of the unitary graph frame at `B` to the one at `A`. -/
private theorem exp_conleyZehnderIndex_mul_frameValue {A B : GLSymplectic n ℝ} (γ : Path A B) :
    exp (↑(Real.pi * conleyZehnderIndex γ) * Complex.I) * frameValue B = frameValue A := by
  rw [frameValue, frameValue,
    ← exp_maslovIndex_mul_det_mul_exp_spectralAngleSum (γ.map continuous_graphUnitaryFrame),
    ← mul_assoc, ← exp_add, conleyZehnderIndex_def]
  simp

/-- The endpoint value `det U e^{-πi s(U Uᵀ)}` of a unitary graph frame does not vanish. -/
private theorem frameValue_ne_zero (A : GLSymplectic n ℝ) : frameValue A ≠ 0 :=
  mul_ne_zero (UnitaryGroup.det_isUnit _).ne_zero (exp_ne_zero _)

/-- **The parity of the Conley–Zehnder index.** For a path `γ` of symplectic matrices from `A` to
`B`, both without the eigenvalue `1`, `e^{πi CZ(γ)} = sign (det (1 - A) det (1 - B))`. So the index
is an integer, even exactly when `det (1 - A)` and `det (1 - B)` have the same sign
(`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq`). -/
theorem exp_conleyZehnderIndex {A B : GLSymplectic n ℝ} (γ : Path A B)
    (hA : (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0)
    (hB : (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0) :
    exp (↑(Real.pi * conleyZehnderIndex γ) * Complex.I) =
      (SignType.sign ((1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det *
        (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) : ℂ) := by
  set a := (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
  set b := (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
  obtain ⟨dA, hdA, hA'⟩ := exists_pos_frameValue_mul_nonneg A
  obtain ⟨dB, hdB, hB'⟩ := exists_pos_frameValue_mul_nonneg B
  have h2 : ((-2 : ℝ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [eq_sign_mul_of_mul_eq (norm_exp_ofReal_mul_I _) (frameValue_ne_zero A)
    (mul_ne_zero (mul_ne_zero h2 hA) hdA.ne') (mul_ne_zero (mul_ne_zero h2 hB) hdB.ne') hA' hB'
    (exp_conleyZehnderIndex_mul_frameValue γ)]
  congr 1
  rw [show (-2 : ℝ) ^ Fintype.card n * a * dA * ((-2) ^ Fintype.card n * b * dB) =
      ((-2) ^ Fintype.card n) ^ 2 * (dA * dB) * (a * b) by ring,
    sign_mul, sign_pos (by positivity), one_mul]

/-- **The parity of the Conley–Zehnder index, from the identity.** For a path `γ` of symplectic
matrices of size `2n` from the identity to a matrix `B` without the eigenvalue `1`,
`e^{πi CZ(γ)} = (-1) ^ n sign det (1 - B)`. So the index is an integer `k` with
`(-1) ^ (n - k) = sign det (1 - B)`
(`TauCeti.GLSymplectic.exists_int_conleyZehnderIndex_eq_of_one`). -/
theorem exp_conleyZehnderIndex_of_one {B : GLSymplectic n ℝ} (γ : Path 1 B)
    (hB : (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0) :
    exp (↑(Real.pi * conleyZehnderIndex γ) * Complex.I) =
      (-1) ^ Fintype.card n *
        (SignType.sign (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det : ℂ) := by
  obtain ⟨r, hr, hr'⟩ := exists_pos_frameValue_one (n := n)
  obtain ⟨dB, hdB, hB'⟩ := exists_pos_frameValue_mul_nonneg B
  have h2 : ((-2 : ℝ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1 : 0 ≤ frameValue (1 : GLSymplectic n ℝ) * ((1 : ℝ) : ℂ) := by
    rw [hr', ofReal_one, mul_one]
    exact zero_le_real.2 hr.le
  rw [eq_sign_mul_of_mul_eq (norm_exp_ofReal_mul_I _) (frameValue_ne_zero 1) one_ne_zero
    (mul_ne_zero (mul_ne_zero h2 hB) hdB.ne') h1 hB' (exp_conleyZehnderIndex_mul_frameValue γ)]
  simp [sign_mul, sign_pow, sign_pos hdB]

/-- **The parity of the Conley–Zehnder index**, integer form. For a path `γ` of symplectic
matrices from `A` to `B`, both without the eigenvalue `1`, the index is an integer `k` with
`(-1) ^ k = sign (det (1 - A) det (1 - B))`. -/
theorem exists_int_conleyZehnderIndex_eq {A B : GLSymplectic n ℝ} (γ : Path A B)
    (hA : (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0)
    (hB : (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0) :
    ∃ k : ℤ, conleyZehnderIndex γ = k ∧
      (k.negOnePow : ℤ) = SignType.sign ((1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det *
        (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :=
  Complex.exists_int_eq_of_exp_pi_mul_I_eq <| (exp_conleyZehnderIndex γ hA hB).trans <| by
    rcases SignType.sign ((1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det *
      (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) with _ | _ | _ <;> simp

/-- **The parity of the Conley–Zehnder index, from the identity**, integer form. For a path `γ` of
symplectic matrices of size `2n` from the identity to a matrix `B` without the eigenvalue `1`, the
index is an integer `k` with `(-1) ^ (n - k) = sign det (1 - B)`. -/
theorem exists_int_conleyZehnderIndex_eq_of_one {B : GLSymplectic n ℝ} (γ : Path 1 B)
    (hB : (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0) :
    ∃ k : ℤ, conleyZehnderIndex γ = k ∧
      (((Fintype.card n : ℤ) - k).negOnePow : ℤ) =
        SignType.sign (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det := by
  obtain ⟨k, hk, hsign⟩ := Complex.exists_int_eq_of_exp_pi_mul_I_eq
    (u := (Fintype.card n : ℤ).negOnePow *
      SignType.sign (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det)
    ((exp_conleyZehnderIndex_of_one γ hB).trans <| by
      rcases SignType.sign (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
        with _ | _ | _ <;> simp)
  refine ⟨k, hk, ?_⟩
  rw [Int.negOnePow_sub, Units.val_mul, hsign, ← mul_assoc, ← Units.val_mul]
  simp

end GLSymplectic

end TauCeti
