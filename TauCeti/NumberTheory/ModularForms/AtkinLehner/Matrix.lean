/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.Data.Nat.ExactDivisor

/-!
# Atkin–Lehner matrices

For an exact divisor `Q` of the level `N` — `Q ∣ N` with `Q` coprime to `N / Q`, the notion of
`TauCeti/Data/Nat/ExactDivisor.lean` — an **Atkin–Lehner matrix** is an integral

```text
W = !![Q * a, b; N * c, Q * d]      with      det W = Q.
```

Writing `N = Q * m`, the determinant condition `Q ^ 2 * a * d - Q * m * b * c = Q` is `Q` times
the **reduced determinant equation** `Q * a * d - m * b * c = 1`, which is the identity every
computation below runs on.

Such a `W` exists exactly because `Q` and `m` are coprime: Bézout supplies `Q * x + m * y = 1`,
and `!![Q * x, -y; N, Q]` is an Atkin–Lehner matrix. That is `atkinLehnerMatrix N Q`, a choice
and not a canonical object — but the choice does not matter, because any two Atkin–Lehner
matrices for the same `Q` differ by an element of `Γ₀(N)` on either side
(`IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_left` and its right-handed twin), and a form on
which `Γ₀(N)` acts trivially cannot tell them apart. The two-sided version of that statement is that
`W` **normalizes** `Γ₀(N)`, which is what makes the weight-`k` slash by `W` an operator on
`M_k(Γ₀(N))` at all.

Two degenerate members of the family are worth naming. At `Q = 1` an Atkin–Lehner matrix is
exactly an element of `Γ₀(N)`, so the operator is the identity; at `Q = N` the Fricke matrix
`!![0, -1; N, 0]` of `TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean` is one, so the whole
Fricke theory is the `Q = N` member of this family.

The family is multiplicative in the divisor: whenever `Q * R` divides the level, a product of an
Atkin–Lehner matrix for `Q` and one for `R` is an Atkin–Lehner matrix for `Q * R`
(`IsAtkinLehnerMatrix.mul`). For coprime exact divisors `Q` and `R` the product `Q * R` is again
an exact divisor (`TauCeti.Nat.IsExactDivisor.mul`), so the exact-divisor members of the family are
closed under coprime products. Squaring stays inside `Γ₀(N)` up to the scalar `Q`
(`exists_mem_Gamma0_mul_self`) — the matrix-level source of the involution `𝒲_Q ^ 2 = 1` in even
weight.

## Main definitions

* `TauCeti.IsAtkinLehnerMatrix`: the predicate above.
* `TauCeti.atkinLehnerMatrix`: the Bézout witness `!![Q * x, -y; N, Q]`.

## Main results

* `TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix`: the witness works, for every exact divisor.
* `TauCeti.isAtkinLehnerMatrix_one_iff_mem_Gamma0`, `TauCeti.isAtkinLehnerMatrix_fricke`: the two
  degenerate members, `Q = 1` and `Q = N`.
* `TauCeti.IsAtkinLehnerMatrix.mul_left`, `TauCeti.IsAtkinLehnerMatrix.mul_right`: the family is
  stable under multiplication by `Γ₀(N)` on either side.
* `TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_left`,
  `TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_right`: any two members for the same `Q`
  differ by an element of `Γ₀(N)`, on the left and on the right respectively.
* `TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul`: `W` normalizes `Γ₀(N)`.
* `TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_self`: `W ^ 2 = Q • γ` with `γ ∈ Γ₀(N)`.
* `TauCeti.IsAtkinLehnerMatrix.mul`: the multiplicativity of the family in the divisor.

## Relation to the Atkin–Lehner anti-involution

`TauCeti/NumberTheory/HeckeRing/GL2/Gamma0/AtkinLehner.lean` also carries the name: it conjugates
by `natDiagGL 2 ![1, N]` to repair the transpose's failure to preserve `Γ₀(N)`, proving the
`Γ₀(N)` Hecke ring commutative. That is a different construction from the matrices here, and the
two do not interact.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
-/

public section

open Matrix CongruenceSubgroup

open scoped MatrixGroups TauCeti.ExactDivisor

namespace TauCeti

variable {N Q R : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ}

/-- An **Atkin–Lehner matrix** for the divisor `Q` of the level `N`: an integral matrix
`!![Q * a, b; N * c, Q * d]` of determinant `Q`. -/
structure IsAtkinLehnerMatrix (N Q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  /-- The upper-left entry is divisible by `Q`. -/
  dvd_apply_zero_zero : (Q : ℤ) ∣ M 0 0
  /-- The lower-left entry is divisible by the level `N`. -/
  dvd_apply_one_zero : (N : ℤ) ∣ M 1 0
  /-- The lower-right entry is divisible by `Q`. -/
  dvd_apply_one_one : (Q : ℤ) ∣ M 1 1
  /-- The determinant is `Q`. -/
  det_eq : M.det = Q

/-- **The entries of an Atkin–Lehner matrix, with the reduced determinant equation.** Writing the
level as `N = Q * m`, the determinant condition `det W = Q` divides through by `Q` to
`Q * (a * d) - m * (b * c) = 1`; that equation, and not the determinant itself, is what the
identities below are polynomial consequences of. -/
theorem IsAtkinLehnerMatrix.exists_entries (hQ : Q ≠ 0) {m : ℕ} (hm : N = Q * m)
    (h : IsAtkinLehnerMatrix N Q M) :
    ∃ a b c d : ℤ, M = !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] ∧
      (Q : ℤ) * (a * d) - (m : ℤ) * (b * c) = 1 := by
  obtain ⟨a, ha⟩ := h.dvd_apply_zero_zero
  obtain ⟨c, hc⟩ := h.dvd_apply_one_zero
  obtain ⟨d, hd⟩ := h.dvd_apply_one_one
  have hQ' : (Q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  have hN : (N : ℤ) = (Q : ℤ) * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
  refine ⟨a, M 0 1, c, d, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, hN, mul_assoc]
  · have hdet := h.det_eq
    rw [Matrix.det_fin_two, ha, hc, hd] at hdet
    refine mul_left_cancel₀ hQ' ?_
    rw [mul_one]
    linear_combination hdet + (M 0 1 * c) * hN

/-- **Building an Atkin–Lehner matrix from the reduced determinant equation**, the converse of
`IsAtkinLehnerMatrix.exists_entries`. -/
theorem isAtkinLehnerMatrix_of_entries {m : ℕ} (hm : N = Q * m) (a b c d : ℤ)
    (h : (Q : ℤ) * (a * d) - (m : ℤ) * (b * c) = 1) :
    IsAtkinLehnerMatrix N Q !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] where
  dvd_apply_zero_zero := by simp
  dvd_apply_one_zero := by
    have hN : (N : ℤ) = (Q : ℤ) * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
    rw [hN]
    exact ⟨c, by simp⟩
  dvd_apply_one_one := by simp
  det_eq := by
    rw [Matrix.det_fin_two_of]
    linear_combination (Q : ℤ) * h

/-- The Bézout witness `!![Q * x, -y; N, Q]`, where `Q * x + (N / Q) * y = 1`. It is an
Atkin–Lehner matrix for every exact divisor `Q` of `N` (`isAtkinLehnerMatrix_atkinLehnerMatrix`),
and every other one differs from it by an element of `Γ₀(N)`. -/
def atkinLehnerMatrix (N Q : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Q : ℤ) * Nat.gcdA Q (N / Q), -Nat.gcdB Q (N / Q); (N : ℤ), (Q : ℤ)]

/-- **Every exact divisor carries an Atkin–Lehner matrix.** Coprimality of `Q` and `N / Q` is
exactly what Bézout needs, and it is used nowhere else in this file. -/
theorem isAtkinLehnerMatrix_atkinLehnerMatrix (h : Q ∥ N) :
    IsAtkinLehnerMatrix N Q (atkinLehnerMatrix N Q) := by
  have hbez : (1 : ℤ) = Q * Nat.gcdA Q (N / Q) + (N / Q : ℕ) * Nat.gcdB Q (N / Q) := by
    have := Nat.gcd_eq_gcd_ab Q (N / Q)
    rwa [h.coprime, Nat.cast_one] at this
  have hm : N = Q * (N / Q) := (h.mul_div_cancel').symm
  have key := isAtkinLehnerMatrix_of_entries hm (Nat.gcdA Q (N / Q)) (-Nat.gcdB Q (N / Q)) 1 1
    (by linear_combination -hbez)
  have : atkinLehnerMatrix N Q =
      !![(Q : ℤ) * Nat.gcdA Q (N / Q), -Nat.gcdB Q (N / Q);
         (Q : ℤ) * ((N / Q : ℕ) : ℤ) * 1, (Q : ℤ) * 1] := by
    have hN : (N : ℤ) = (Q : ℤ) * ((N / Q : ℕ) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
    rw [atkinLehnerMatrix, hN]
    norm_num
  rwa [this]

/-- **At `Q = 1` the Atkin–Lehner matrices are exactly `Γ₀(N)`.** The corresponding operator is
the identity, which is why the family is indexed by exact divisors up to this normalization. -/
theorem isAtkinLehnerMatrix_one_iff_mem_Gamma0 (γ : SL(2, ℤ)) :
    IsAtkinLehnerMatrix N 1 (γ : Matrix (Fin 2) (Fin 2) ℤ) ↔ γ ∈ Gamma0 N := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨fun h ↦ h.dvd_apply_one_zero, fun h ↦ ⟨by simp, h, by simp, ?_⟩⟩
  simp [γ.property]

/-- **The Fricke matrix is the Atkin–Lehner matrix at `Q = N`.** The Fricke theory of
`TauCeti/NumberTheory/ModularForms/Fricke/` is therefore the top member of this family. -/
theorem isAtkinLehnerMatrix_fricke : IsAtkinLehnerMatrix N N !![0, -1; (N : ℤ), 0] where
  dvd_apply_zero_zero := by simp
  dvd_apply_one_zero := by simp
  dvd_apply_one_one := by simp
  det_eq := by rw [Matrix.det_fin_two_of]; ring

/-- **Multiplying an Atkin–Lehner matrix by `Γ₀(N)` on the left** gives an Atkin–Lehner matrix
for the same `Q`. -/
theorem IsAtkinLehnerMatrix.mul_left (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    IsAtkinLehnerMatrix N Q ((γ : Matrix (Fin 2) (Fin 2) ℤ) * M) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  have hQN' : (Q : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hQN
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_left h.dvd_apply_zero_zero _)
      (Dvd.dvd.mul_left (hQN'.trans h.dvd_apply_one_zero) _)
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right hγ _) (Dvd.dvd.mul_left h.dvd_apply_one_zero _)
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right (hQN'.trans hγ) _)
      (Dvd.dvd.mul_left h.dvd_apply_one_one _)
  · rw [Matrix.det_mul, γ.property, one_mul, h.det_eq]

/-- **Multiplying an Atkin–Lehner matrix by `Γ₀(N)` on the right** gives an Atkin–Lehner matrix
for the same `Q`. -/
theorem IsAtkinLehnerMatrix.mul_right (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    IsAtkinLehnerMatrix N Q (M * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  have hQN' : (Q : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hQN
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right h.dvd_apply_zero_zero _)
      (Dvd.dvd.mul_left (hQN'.trans hγ) _)
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right h.dvd_apply_one_zero _) (Dvd.dvd.mul_left hγ _)
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right (hQN'.trans h.dvd_apply_one_zero) _)
      (Dvd.dvd.mul_right h.dvd_apply_one_one _)
  · rw [Matrix.det_mul, γ.property, mul_one, h.det_eq]

/-- **Two Atkin–Lehner matrices for the same `Q` differ by `Γ₀(N)` on the left.** The witness is
`W' W⁻¹`, integral because the reduced determinant equation clears the `1 / Q` in `W⁻¹`. -/
theorem IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_left (hQ : Q ≠ 0) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (h' : IsAtkinLehnerMatrix N Q M') :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧ M' = (γ : Matrix (Fin 2) (Fin 2) ℤ) * M := by
  obtain ⟨m, hm⟩ := hQN
  obtain ⟨a, b, c, d, rfl, hred⟩ := h.exists_entries hQ hm
  obtain ⟨a', b', c', d', rfl, -⟩ := h'.exists_entries hQ hm
  have hQ' : (Q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  have hN : (N : ℤ) = (Q : ℤ) * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
  set G : Matrix (Fin 2) (Fin 2) ℤ :=
    !![(Q : ℤ) * (a' * d) - m * (b' * c), a * b' - a' * b;
       (Q : ℤ) * m * (c' * d - c * d'), (Q : ℤ) * (a * d') - m * (b * c')] with hG
  have hmul : G * !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] =
      !![(Q : ℤ) * a', b'; (Q : ℤ) * m * c', (Q : ℤ) * d'] := by
    rw [hG]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ((Q : ℤ) * a') * hred
    · linear_combination b' * hred
    · linear_combination ((Q : ℤ) * m * c') * hred
    · linear_combination ((Q : ℤ) * d') * hred
  have hdetG : G.det = 1 := by
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h.det_eq, h'.det_eq] at hd
    exact mul_right_cancel₀ hQ' (by rw [one_mul]; exact hd)
  have hdvd : (N : ℤ) ∣ G 1 0 := ⟨c' * d - c * d', by rw [hG, hN]; simp⟩
  exact ⟨⟨G, hdetG⟩,
    Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd), hmul.symm⟩

/-- **Two Atkin–Lehner matrices for the same `Q` differ by `Γ₀(N)` on the right**, the mirror of
`IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_left` with witness `W⁻¹ W'`. -/
theorem IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_right (hQ : Q ≠ 0) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (h' : IsAtkinLehnerMatrix N Q M') :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧ M' = M * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨m, hm⟩ := hQN
  obtain ⟨a, b, c, d, rfl, hred⟩ := h.exists_entries hQ hm
  obtain ⟨a', b', c', d', rfl, -⟩ := h'.exists_entries hQ hm
  have hQ' : (Q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hQ
  have hN : (N : ℤ) = (Q : ℤ) * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
  set G : Matrix (Fin 2) (Fin 2) ℤ :=
    !![(Q : ℤ) * (a' * d) - m * (b * c'), b' * d - b * d';
       (Q : ℤ) * m * (a * c' - a' * c), (Q : ℤ) * (a * d') - m * (b' * c)] with hG
  have hmul : !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] * G =
      !![(Q : ℤ) * a', b'; (Q : ℤ) * m * c', (Q : ℤ) * d'] := by
    rw [hG]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ((Q : ℤ) * a') * hred
    · linear_combination b' * hred
    · linear_combination ((Q : ℤ) * m * c') * hred
    · linear_combination ((Q : ℤ) * d') * hred
  have hdetG : G.det = 1 := by
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h.det_eq, h'.det_eq] at hd
    exact mul_left_cancel₀ hQ' (by rw [mul_one]; exact hd)
  have hdvd : (N : ℤ) ∣ G 1 0 := ⟨a * c' - a' * c, by rw [hG, hN]; simp⟩
  exact ⟨⟨G, hdetG⟩,
    Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd), hmul.symm⟩

/-- **An Atkin–Lehner matrix normalizes `Γ₀(N)`**: `W γ = δ W` with `δ ∈ Γ₀(N)`. This is the fact
that turns the weight-`k` slash by `W` into an operator on `M_k(Γ₀(N))`. -/
theorem IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul (hQ : Q ≠ 0) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      M * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * M :=
  h.exists_mem_Gamma0_eq_mul_left hQ hQN (h.mul_right hQN hγ)

/-- **An Atkin–Lehner matrix normalizes `Γ₀(N)`, read the other way**: `γ W = W δ` with
`δ ∈ Γ₀(N)`. -/
theorem IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul' (hQ : Q ≠ 0) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * M = M * (δ : Matrix (Fin 2) (Fin 2) ℤ) :=
  h.exists_mem_Gamma0_eq_mul_right hQ hQN (h.mul_left hQN hγ)

/-- **The square of an Atkin–Lehner matrix is `Q` times an element of `Γ₀(N)`.** Since a scalar
matrix slashes as a constant, this is the matrix-level reason the normalized operator `𝒲_Q` is an
involution in even weight. -/
theorem IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_self (hQ : Q ≠ 0) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧ M * M = (Q : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨m, hm⟩ := hQN
  obtain ⟨a, b, c, d, rfl, hred⟩ := h.exists_entries hQ hm
  have hN : (N : ℤ) = (Q : ℤ) * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
  set G : Matrix (Fin 2) (Fin 2) ℤ :=
    !![(Q : ℤ) * (a * a) + m * (b * c), b * (a + d);
       (Q : ℤ) * m * (c * (a + d)), (m : ℤ) * (b * c) + Q * (d * d)] with hG
  have hdetG : G.det = 1 := by
    rw [hG, Matrix.det_fin_two_of]
    linear_combination ((Q : ℤ) * (a * d) - (m : ℤ) * (b * c) + 1) * hred
  have hdvd : (N : ℤ) ∣ G 1 0 := ⟨c * (a + d), by rw [hG, hN]; simp⟩
  have hsq : !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] *
      !![(Q : ℤ) * a, b; (Q : ℤ) * m * c, (Q : ℤ) * d] = (Q : ℤ) • G := by
    rw [hG]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  exact ⟨⟨G, hdetG⟩,
    Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd), hsq⟩

/-- **Multiplicativity of the family.** As soon as `Q * R` divides the level, an Atkin–Lehner
matrix for `Q` times one for `R` is an Atkin–Lehner matrix for `Q * R`. Coprime exact divisors
`Q` and `R` satisfy the hypothesis and have `Q * R` again an exact divisor
(`TauCeti.Nat.IsExactDivisor.mul`), which is the case the family is indexed by. -/
theorem IsAtkinLehnerMatrix.mul (hQRN : Q * R ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (h' : IsAtkinLehnerMatrix N R M') :
    IsAtkinLehnerMatrix N (Q * R) (M * M') := by
  have hQRN : ((Q * R : ℕ) : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hQRN
  have hmul : ((Q * R : ℕ) : ℤ) = (Q : ℤ) * (R : ℤ) := by push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine dvd_add ?_ (Dvd.dvd.mul_left (hQRN.trans h'.dvd_apply_one_zero) _)
    rw [hmul]
    exact mul_dvd_mul h.dvd_apply_zero_zero h'.dvd_apply_zero_zero
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (Dvd.dvd.mul_right h.dvd_apply_one_zero _)
      (Dvd.dvd.mul_left h'.dvd_apply_one_zero _)
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine dvd_add (Dvd.dvd.mul_right (hQRN.trans h.dvd_apply_one_zero) _) ?_
    rw [hmul]
    exact mul_dvd_mul h.dvd_apply_one_one h'.dvd_apply_one_one
  · rw [Matrix.det_mul, h.det_eq, h'.det_eq, hmul]

end TauCeti
