/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder

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
(`Matrix.zero_le_exp_neg_spectralAngleSum_mul_det_one_sub`), and
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

/-- The imaginary part of the straightened graph frame: for every real matrix `A` on
`ℝ^{n ⊕ n}`, `conj (T Γ(A)) - T Γ(A) = i √2 J (A - 1)`, where `T` is the diagonal straightening
and `Γ(A)` the graph frame. So the straightened graph meets the real points nontrivially, that
is, the graph of `A` meets the diagonal, exactly when `A` has the eigenvalue `1`. -/
theorem map_star_diagonalStraightening_mul_graphFrame_sub (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (diagonalStraightening n * graphFrame A).map star - diagonalStraightening n * graphFrame A =
      (Complex.I * ((√2 : ℝ) : ℂ)) • (J n ℝ * (A - 1)).map ((↑) : ℝ → ℂ) := by
  conv_rhs => rw [← fromBlocks_toBlocks (A - 1), J, fromBlocks_multiply]
  rw [diagonalStraightening_def, graphFrame_def, Matrix.smul_mul, fromBlocks_multiply]
  ext (i | i) (j | j) <;>
  simp [Matrix.one_apply, Complex.ext_iff, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂] <;>
  split_ifs <;> simp <;> ring

namespace GLSymplectic

/-- At the identity, `det U e^{-πi s(U Uᵀ)}` is a positive real number for the unitary graph
frame `U`. -/
private theorem exists_pos_det_mul_exp_spectralAngleSum_one :
    ∃ r : ℝ, 0 < r ∧
      (graphUnitaryFrame (1 : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
        exp (-(↑(Real.pi * spectralAngleSum
          (souriau (graphUnitaryFrame (1 : GLSymplectic n ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) *
            Complex.I)) = r := by
  obtain ⟨P, hP, hU⟩ := exists_posDef_coe_graphUnitaryFrame (1 : GLSymplectic n ℝ)
  refine ⟨√2 ^ Fintype.card (n ⊕ n) * P.det, by have := hP.det_pos; positivity, ?_⟩
  have hs : spectralAngleSum
      (souriau (graphUnitaryFrame (1 : GLSymplectic n ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 0 := by
    rw [souriau_graphUnitaryFrame_one, OneMemClass.coe_one, ← diagonal_one,
      spectralAngleSum_diagonal]
    simp
  -- `M.map (↑)` is `Complex.ofRealHom.mapMatrix M`, so its determinant is `↑M.det`.
  have hmap (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) : (M.map ((↑) : ℝ → ℂ)).det = M.det :=
    (Complex.ofRealHom.map_det M).symm
  rw [hs, mul_zero, ofReal_zero, zero_mul, neg_zero, exp_zero, mul_one, hU, OneMemClass.coe_one,
    Units.val_one, diagonalStraightening_mul_graphFrame_one, det_mul, hmap, hmap, det_smul, det_one,
    mul_one, ofReal_mul, ofReal_pow]

/-- At a symplectic matrix `A`, the number `det U e^{-πi s(U Uᵀ)}` for the unitary graph frame `U`,
times `(-2) ^ n det (1 - A)` and a positive real number `d`, is a nonnegative real number. -/
private theorem exists_pos_zero_le_det_mul_exp_spectralAngleSum_mul (A : GLSymplectic n ℝ) :
    ∃ d : ℝ, 0 < d ∧
      0 ≤ (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
        exp (-(↑(Real.pi * spectralAngleSum
          (souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) * Complex.I)) *
        ↑((-2) ^ Fintype.card n *
          (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det * d) := by
  obtain ⟨P, hP, hU⟩ := exists_posDef_coe_graphUnitaryFrame A
  refine ⟨P.det, hP.det_pos, ?_⟩
  set B := ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)
  have hstar : (star : ℂ → ℂ) = ⇑(starRingEnd ℂ) := funext fun z => (starRingEnd_apply z).symm
  -- `M.map (↑)` is `Complex.ofRealHom.mapMatrix M`, so its determinant is `↑M.det`.
  have hmap (M : Matrix (n ⊕ n) (n ⊕ n) ℝ) : (M.map ((↑) : ℝ → ℂ)).det = M.det :=
    (Complex.ofRealHom.map_det M).symm
  have hP' : (P.map ((↑) : ℝ → ℂ)).map star = P.map ((↑) : ℝ → ℂ) := by
    rw [Matrix.map_map]
    exact congrArg P.map (funext fun x => conj_ofReal x)
  -- The imaginary part of the frame is `i √2 J (B - 1)` times the real factor `P`.
  have hdet : ((graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).map star -
      (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ)).det =
        ↑((-2) ^ Fintype.card n * (1 - B).det * P.det) := by
    rw [hU, hstar, Matrix.map_mul, ← hstar, hP', ← Matrix.sub_mul,
      map_star_diagonalStraightening_mul_graphFrame_sub, det_mul, det_smul, hmap, hmap, det_mul,
      det_J, one_mul, ← neg_sub, det_neg, Fintype.card_sum, ← two_mul, pow_mul, pow_mul, mul_pow,
      I_sq, ← ofReal_pow, Real.sq_sqrt zero_le_two]
    push_cast
    ring
  have h := zero_le_exp_neg_spectralAngleSum_mul_det_one_sub (souriau (graphUnitaryFrame A)).2
  rw [det_one_sub_souriau, hdet] at h
  convert h using 1
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
private theorem exp_conleyZehnderIndex_mul_det_mul_exp {A B : GLSymplectic n ℝ} (γ : Path A B) :
    exp (↑(Real.pi * conleyZehnderIndex γ) * Complex.I) *
        ((graphUnitaryFrame B : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
          exp (-(↑(Real.pi * spectralAngleSum
            (souriau (graphUnitaryFrame B) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) * Complex.I))) =
      (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
        exp (-(↑(Real.pi * spectralAngleSum
          (souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) * Complex.I)) := by
  rw [← exp_maslovIndex_mul_det_mul_exp_spectralAngleSum (γ.map continuous_graphUnitaryFrame),
    ← mul_assoc, ← exp_add, conleyZehnderIndex_def, mul_neg, ofReal_neg, neg_mul, neg_add_cancel,
    exp_zero, one_mul]

/-- The endpoint value `det U e^{-πi s(U Uᵀ)}` of a unitary graph frame does not vanish. -/
private theorem det_mul_exp_spectralAngleSum_ne_zero (A : GLSymplectic n ℝ) :
    (graphUnitaryFrame A : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
        exp (-(↑(Real.pi * spectralAngleSum
          (souriau (graphUnitaryFrame A) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) * Complex.I)) ≠ 0 :=
  mul_ne_zero (UnitaryGroup.det_isUnit _).ne_zero (exp_ne_zero _)

/-- If `e^{πi x}` is an integer `u`, then `x` is an integer `k` with `(-1) ^ k = u`. -/
private theorem exists_int_eq_of_exp_eq {x : ℝ} {u : ℤ}
    (h : exp (↑(Real.pi * x) * Complex.I) = u) : ∃ k : ℤ, x = k ∧ (k.negOnePow : ℤ) = u := by
  have hsin : Real.sin (Real.pi * x) = 0 := by
    rw [← exp_ofReal_mul_I_im, h, intCast_im]
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  have hx : x = k := by
    have := Real.pi_pos.ne'
    field_simp at hk
    linarith
  refine ⟨k, hx, ?_⟩
  have h2 : exp (↑(Real.pi * x) * Complex.I) = (k.negOnePow : ℤ) := by
    rw [hx, show (↑(Real.pi * (k : ℝ)) : ℂ) * Complex.I = k * (Real.pi * Complex.I) by
      push_cast; ring, exp_int_mul, exp_pi_mul_I]
    rcases Int.even_or_odd k with hk | hk
    · simp [Int.negOnePow_even _ hk, hk.neg_one_zpow]
    · simp [Int.negOnePow_odd _ hk, hk.neg_one_zpow]
  exact_mod_cast h2.symm.trans h

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
  obtain ⟨dA, hdA, hA'⟩ := exists_pos_zero_le_det_mul_exp_spectralAngleSum_mul A
  obtain ⟨dB, hdB, hB'⟩ := exists_pos_zero_le_det_mul_exp_spectralAngleSum_mul B
  have h2 : ((-2 : ℝ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [eq_sign_mul_of_mul_eq (norm_exp_ofReal_mul_I _) (det_mul_exp_spectralAngleSum_ne_zero A)
    (mul_ne_zero (mul_ne_zero h2 hA) hdA.ne') (mul_ne_zero (mul_ne_zero h2 hB) hdB.ne') hA' hB'
    (exp_conleyZehnderIndex_mul_det_mul_exp γ)]
  congr 1
  rw [show (-2 : ℝ) ^ Fintype.card n *
        (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det * dA *
      ((-2) ^ Fintype.card n * (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det * dB) =
      ((-2) ^ Fintype.card n) ^ 2 * (dA * dB) *
        ((1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det *
          (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) by ring,
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
  obtain ⟨r, hr, hr'⟩ := exists_pos_det_mul_exp_spectralAngleSum_one (n := n)
  obtain ⟨dB, hdB, hB'⟩ := exists_pos_zero_le_det_mul_exp_spectralAngleSum_mul B
  have h2 : ((-2 : ℝ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1 : 0 ≤ (graphUnitaryFrame (1 : GLSymplectic n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ).det *
      exp (-(↑(Real.pi * spectralAngleSum
        (souriau (graphUnitaryFrame (1 : GLSymplectic n ℝ)) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) *
          Complex.I)) * ((1 : ℝ) : ℂ) := by
    rw [hr', ofReal_one, mul_one]
    exact zero_le_real.2 hr.le
  rw [eq_sign_mul_of_mul_eq (norm_exp_ofReal_mul_I _) (det_mul_exp_spectralAngleSum_ne_zero 1)
    one_ne_zero (mul_ne_zero (mul_ne_zero h2 hB) hdB.ne') h1 hB'
    (exp_conleyZehnderIndex_mul_det_mul_exp γ), one_mul, sign_mul, sign_mul, sign_pos hdB,
    mul_one, sign_pow, sign_neg (by norm_num : (-2 : ℝ) < 0), SignType.coe_mul, SignType.coe_pow,
    SignType.coe_neg, SignType.coe_one]

/-- **The parity of the Conley–Zehnder index**, integer form. For a path `γ` of symplectic
matrices from `A` to `B`, both without the eigenvalue `1`, the index is an integer `k` with
`(-1) ^ k = sign (det (1 - A) det (1 - B))`. -/
theorem exists_int_conleyZehnderIndex_eq {A B : GLSymplectic n ℝ} (γ : Path A B)
    (hA : (1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0)
    (hB : (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det ≠ 0) :
    ∃ k : ℤ, conleyZehnderIndex γ = k ∧
      (k.negOnePow : ℤ) = SignType.sign ((1 - ((A : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det *
        (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det) :=
  exists_int_eq_of_exp_eq <| (exp_conleyZehnderIndex γ hA hB).trans <| by
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
  obtain ⟨k, hk, hsign⟩ := exists_int_eq_of_exp_eq (u := (Fintype.card n : ℤ).negOnePow *
    SignType.sign (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det)
    ((exp_conleyZehnderIndex_of_one γ hB).trans <| by
      rcases SignType.sign (1 - ((B : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)).det
        with _ | _ | _ <;> simp)
  refine ⟨k, hk, ?_⟩
  rw [Int.negOnePow_sub, Units.val_mul, hsign, ← mul_assoc, ← Units.val_mul, ← sq,
    Int.units_sq, Units.val_one, one_mul]

end GLSymplectic

end TauCeti
