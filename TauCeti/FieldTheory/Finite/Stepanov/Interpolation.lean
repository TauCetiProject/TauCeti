/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.IntegralDomain
import TauCeti.Algebra.Polynomial.LinearFactor
import TauCeti.Algebra.Polynomial.OfFn
import TauCeti.FieldTheory.Finite.Polynomial
import TauCeti.LinearAlgebra.FiniteDimensional.Kernel

/-!
# The interpolation step of Stepanov's method

Let `F` be a finite field with `q` elements, let `f ∈ F[X]` have degree `m`, and let `c ∈ ℕ`.
Stepanov's method bounds the size of `S = {x ∈ F : f(x)^c = 1}` with an auxiliary polynomial
`R = ∑_{i<e} f^(i c) · A_i(X, X^q)`, for `A_0, …, A_{e-1} ∈ F[X][Y]` that are not all zero, such
that `R` vanishes to order `M` at every point of `S`. This file constructs such `A_i` by linear
algebra.

## Main results

* `Polynomial.exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero`: if `M ≤ q` and
  `∑_{ℓ<M} (ℓ m + D + J) < e J (D + 1)`, then there are `A_0, …, A_{e-1} ∈ F[X][Y]`, not all
  zero, whose coefficients have degree at most `D` and whose `Y`-degrees are less than `J`, such
  that the Hasse derivatives `D^ℓ R` with `ℓ < M` vanish on `S`.

## Implementation notes

Let `B_{ij} ∈ F[X]` be the coefficient of `Y^j` in `A_i`. For `ℓ < q` the Hasse derivative `D^ℓ`
commutes with multiplication by a `q`-th power, so `D^ℓ R = ∑_{i,j} D^ℓ(f^(i c) B_{ij}) X^(q j)`.
Since `f^(N - ℓ)` divides `D^ℓ(f^N B)`, the polynomial `G_{N,ℓ}(B) = f^ℓ D^ℓ(f^N B) / f^N` has
degree at most `ℓ m + deg B`, and it is linear in `B`. At `x ∈ S` we have `x^q = x` and
`f(x)^(i c) = 1`, so `f(x)^ℓ (D^ℓ R)(x) = T_ℓ(x)` for `T_ℓ = ∑_{i,j} G_{i c, ℓ}(B_{ij}) X^j`.
The conditions `T_ℓ = 0` for `ℓ < M` are `∑_{ℓ<M} (ℓ m + D + J)` linear equations in the
`e J (D + 1)` coefficients of the `B_{ij}`, so they have a nonzero solution
(`TauCeti.exists_ne_zero_forall_apply_eq_zero_of_card_lt_finrank`). This argument needs `c > 0`,
so that `f(x) ≠ 0` on `S`. For `c = 0` the sum `R` does not depend on `f`, and the case `f = 1`,
`c = 1` gives the statement. The main result is stated over a domain: a finite domain is a field,
and over an infinite domain `Nat.card` is `0`, so `M = 0` and only the degree conditions remain.

The companion statement, that `R ≠ 0` when the `A_i` are not all zero, needs further hypotheses
on `f`, `e` and the degrees, and it is not part of this file.

## References

* S. A. Stepanov, *On the number of points of a hyperelliptic curve over a finite prime field*,
  Izv. Akad. Nauk SSSR Ser. Mat. 33 (1969), 1171–1181.
* S. Kopparty, *The Weil bounds*, lecture notes, Rutgers University (2013), §2.2, part 2.
* W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, Lecture Notes in
  Mathematics 536, Springer (1976), Chapter I.
-/

public section

open Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- The polynomial `f^ℓ D^ℓ(f^N B) / f^N`, as an `F`-linear map of `B`. Mathlib's
`Polynomial.div_def` writes the division by `f^N` through `divByMonicHom`. -/
private noncomputable def stepanovMap (f : F[X]) (N ℓ : ℕ) : F[X] →ₗ[F] F[X] :=
  LinearMap.mulLeft F (C (f ^ N).leadingCoeff⁻¹) ∘ₗ
    divByMonicHom (f ^ N * C (f ^ N).leadingCoeff⁻¹) ∘ₗ LinearMap.mulLeft F (f ^ ℓ) ∘ₗ
      hasseDeriv ℓ ∘ₗ LinearMap.mulLeft F (f ^ N)

private theorem stepanovMap_apply (f : F[X]) (N ℓ : ℕ) (B : F[X]) :
    stepanovMap f N ℓ B = f ^ ℓ * hasseDeriv ℓ (f ^ N * B) / f ^ N := by
  simp [stepanovMap, div_def]

private theorem pow_mul_stepanovMap (f : F[X]) (N ℓ : ℕ) (B : F[X]) :
    f ^ N * stepanovMap f N ℓ B = f ^ ℓ * hasseDeriv ℓ (f ^ N * B) := by
  rcases eq_or_ne (f ^ N) 0 with hN | hN
  · simp [hN]
  have hdvd : f ^ N ∣ f ^ ℓ * hasseDeriv ℓ (f ^ N * B) := by
    refine (pow_dvd_pow f (by omega : N ≤ ℓ + (N - ℓ))).trans ?_
    rw [pow_add]
    exact mul_dvd_mul_left _ (pow_sub_dvd_hasseDeriv_of_pow_dvd ℓ (dvd_mul_right _ _))
  rw [stepanovMap_apply]
  exact EuclideanDomain.mul_div_cancel' hN hdvd

private theorem natDegree_stepanovMap_le (f : F[X]) (N ℓ : ℕ) (B : F[X]) :
    (stepanovMap f N ℓ B).natDegree ≤ ℓ * f.natDegree + B.natDegree := by
  rcases eq_or_ne (f ^ N) 0 with hN | hN
  · simp [stepanovMap_apply, hN]
  by_cases hG : stepanovMap f N ℓ B = 0
  · simp [hG]
  have h := congrArg natDegree (pow_mul_stepanovMap f N ℓ B)
  rw [natDegree_mul hN hG, natDegree_pow] at h
  have h₁ := natDegree_mul_le (p := f ^ ℓ) (q := hasseDeriv ℓ (f ^ N * B))
  have h₂ := natDegree_hasseDeriv_le (f ^ N * B) ℓ
  have h₃ := natDegree_mul_le (p := f ^ N) (q := B)
  rw [natDegree_pow] at h₁ h₃
  omega

/-- The polynomial `∑_{i,j} G_{i c, ℓ}(B_{ij}) X^j` has degree less than `ℓ m + D + J` when each
`B_{ij}` has degree at most `D`. -/
private theorem natDegree_sum_stepanovMap_mul_X_pow_lt {e J D ℓ c : ℕ} (hJ : 0 < J) (f : F[X])
    (B : Fin e → Fin J → F[X]) (hB : ∀ i j, (B i j).natDegree ≤ D) :
    (∑ i : Fin e, ∑ j : Fin J, stepanovMap f ((i : ℕ) * c) ℓ (B i j) * X ^ (j : ℕ)).natDegree <
      ℓ * f.natDegree + D + J := by
  refine lt_of_le_of_lt (b := ℓ * f.natDegree + D + (J - 1))
    (natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_sum_le_of_forall_le _ _ fun j _ => natDegree_mul_le.trans ?_) (by omega)
  have := natDegree_stepanovMap_le f ((i : ℕ) * c) ℓ (B i j)
  have := hB i j
  have := natDegree_X_pow_le (R := F) (j : ℕ)
  have := j.isLt
  omega

open scoped Classical in
/-- At a point `x` with `f(x)^c = 1`, the value `f(x)^ℓ (D^ℓ R)(x)` is the value at `x` of the
polynomial `∑_{i,j} G_{i c, ℓ}(B_{ij}) X^j`. -/
private theorem pow_mul_eval_hasseDeriv_eq {e J ℓ c : ℕ} (hℓ : ℓ < Nat.card F) (f : F[X])
    {x : F} (hx : f.eval x ^ c = 1) (B : Fin e → Fin J → F[X]) :
    f.eval x ^ ℓ * (hasseDeriv ℓ (∑ i : Fin e, f ^ ((i : ℕ) * c) *
      (ofFn J (B i)).eval (X ^ Nat.card F))).eval x =
      (∑ i : Fin e, ∑ j : Fin J, stepanovMap f ((i : ℕ) * c) ℓ (B i j) * X ^ (j : ℕ)).eval x := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have hq (y : F) : y ^ Nat.card F = y := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card y
  simp only [← eval₂_id, eval₂_ofFn, RingHom.id_apply, Finset.mul_sum, map_sum]
  simp only [eval₂_id, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  -- `(X ^ q) ^ j = (X ^ j) ^ q`, and `D^ℓ` passes through the `q`-th power.
  have hXj : ((X : F[X]) ^ Nat.card F) ^ (j : ℕ) = (X ^ (j : ℕ)) ^ Nat.card F := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hXj, ← mul_assoc, hasseDeriv_mul_pow_natCard hℓ]
  have h := congrArg (eval x) (pow_mul_stepanovMap f ((i : ℕ) * c) ℓ (B i j))
  have hxi : f.eval x ^ ((i : ℕ) * c) = 1 := by rw [pow_mul', hx, one_pow]
  simp only [eval_mul, eval_pow, hxi, one_mul] at h
  simp only [eval_mul, eval_pow, eval_X, hq, h, mul_assoc]

/-- The interpolation step for `c > 0`, where `f(x) ≠ 0` at every `x` with `f(x)^c = 1`. -/
private theorem exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero_of_pos {c e D J M : ℕ}
    (hc : 0 < c) (hM : M ≤ Nat.card F) (f : F[X])
    (hcount : ∑ ℓ ∈ Finset.range M, (ℓ * f.natDegree + D + J) < e * J * (D + 1)) :
    ∃ A : Fin e → F[X][X], (∃ i, A i ≠ 0) ∧ (∀ i j, ((A i).coeff j).natDegree ≤ D) ∧
      (∀ i, (A i).natDegree < J) ∧ ∀ x, f.eval x ^ c = 1 → ∀ ℓ < M,
        (hasseDeriv ℓ (∑ i : Fin e, f ^ ((i : ℕ) * c) * (A i).eval (X ^ Nat.card F))).eval x =
          0 := by
  classical
  have hJ : 0 < J := Nat.pos_of_ne_zero fun h => by simp [h] at hcount
  let K (ℓ : ℕ) := ℓ * f.natDegree + D + J
  have hK (ℓ : ℕ) : K ℓ = ℓ * f.natDegree + D + J := rfl
  let B (i : Fin e) (j : Fin J) : (Fin e × Fin J × Fin (D + 1) → F) →ₗ[F] F[X] :=
    ofFn (D + 1) ∘ₗ LinearMap.funLeft F F fun r : Fin (D + 1) => (i, j, r)
  have hBa (i j a) : B i j a = ofFn (D + 1) fun r => a (i, j, r) := by
    simp only [B, LinearMap.comp_apply]
    exact congrArg _ (_root_.funext fun r => LinearMap.funLeft_apply _ _ _ _ _)
  let T (ℓ : ℕ) : (Fin e × Fin J × Fin (D + 1) → F) →ₗ[F] F[X] :=
    ∑ i : Fin e, ∑ j : Fin J,
      LinearMap.mulRight F (X ^ (j : ℕ)) ∘ₗ stepanovMap f ((i : ℕ) * c) ℓ ∘ₗ B i j
  have hT (ℓ : ℕ) (a) : T ℓ a =
      ∑ i : Fin e, ∑ j : Fin J, stepanovMap f ((i : ℕ) * c) ℓ (B i j a) * X ^ (j : ℕ) := by
    simp [T]
  -- One condition for each coefficient of index `r < K ℓ` of `T ℓ`, for each `ℓ < M`.
  obtain ⟨a, ha, hTa⟩ := TauCeti.exists_ne_zero_forall_apply_eq_zero_of_card_lt_finrank
    (fun k : Σ ℓ : Fin M, Fin (K ℓ) => lcoeff F (k.2 : ℕ) ∘ₗ T k.1) <| by
      simpa [K, Nat.card_sigma, Fin.sum_univ_eq_sum_range (fun ℓ => ℓ * f.natDegree + D + J),
        Module.finrank_fintype_fun_eq_card, mul_assoc] using hcount
  have hB (i j) : (B i j a).natDegree ≤ D := by
    rw [hBa]
    exact Nat.lt_succ_iff.mp (ofFn_natDegree_lt (by omega) _)
  refine ⟨fun i => ofFn J fun j => B i j a, ?_, fun i n => ?_, fun i => ofFn_natDegree_lt hJ _,
    fun x hx ℓ hℓ => ?_⟩
  · by_contra! h
    apply ha
    funext ⟨i, j, r⟩
    have h₁ : (fun j => B i j a) = 0 := injective_ofFn J (by rw [h i, map_zero])
    have h₂ : (fun r => a (i, j, r)) = 0 :=
      injective_ofFn (D + 1) (by rw [← hBa, congrFun h₁ j, Pi.zero_apply, map_zero])
    exact congrFun h₂ r
  · rcases lt_or_ge n J with hn | hn
    · rw [ofFn_coeff_eq_val_of_lt _ hn]; exact hB i _
    · simp [ofFn_coeff_eq_zero_of_ge _ hn]
  have hfx : f.eval x ≠ 0 := fun h => by simp [h, hc.ne'] at hx
  have hdeg : (T ℓ a).natDegree < K ℓ := by
    rw [hT, hK]
    exact natDegree_sum_stepanovMap_mul_X_pow_lt hJ f _ hB
  have hzero : T ℓ a = 0 := by
    have h₀ : toFn (K ℓ) (T ℓ a) = 0 := by
      funext r
      simpa using hTa ⟨⟨ℓ, hℓ⟩, r⟩
    rw [← ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg, h₀, map_zero]
  have h := pow_mul_eval_hasseDeriv_eq (hℓ.trans_le hM) f hx fun i j => B i j a
  rw [← hT, hzero, eval_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hfx)

/-- The interpolation step over a field. -/
private theorem exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero_of_field {c e D J M : ℕ}
    (hM : M ≤ Nat.card F) (f : F[X])
    (hcount : ∑ ℓ ∈ Finset.range M, (ℓ * f.natDegree + D + J) < e * J * (D + 1)) :
    ∃ A : Fin e → F[X][X], (∃ i, A i ≠ 0) ∧ (∀ i j, ((A i).coeff j).natDegree ≤ D) ∧
      (∀ i, (A i).natDegree < J) ∧ ∀ x, f.eval x ^ c = 1 → ∀ ℓ < M,
        (hasseDeriv ℓ (∑ i : Fin e, f ^ ((i : ℕ) * c) * (A i).eval (X ^ Nat.card F))).eval x =
          0 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have h1 : ∑ ℓ ∈ Finset.range M, (ℓ * (1 : F[X]).natDegree + D + J) < e * J * (D + 1) :=
      (Finset.sum_le_sum fun ℓ _ => by simp).trans_lt hcount
    obtain ⟨A, hA0, hAc, hAY, hAx⟩ :=
      exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero_of_pos one_pos hM 1 h1
    exact ⟨A, hA0, hAc, hAY, fun x _ ℓ hℓ => by simpa using hAx x (by simp) ℓ hℓ⟩
  · exact exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero_of_pos hc hM f hcount

/-- **Stepanov's interpolation step.** Let the domain `R` have `q` elements and let `M ≤ q`. If the
`e J (D + 1)` coefficients of `A_0, …, A_{e-1} ∈ R[X][Y]`, with coefficients of degree at most
`D` and `Y`-degree less than `J`, outnumber the `∑_{ℓ<M} (ℓ deg f + D + J)` linear conditions, then
some choice of the `A_i`, not all zero, makes `∑_i f^(i c) · A_i(X, X^q)` vanish to order `M`
at every `x` with `f(x)^c = 1`: its Hasse derivatives of order `ℓ < M` vanish there. -/
theorem exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero {R : Type*} [CommRing R]
    [IsDomain R] {c e D J M : ℕ} (hM : M ≤ Nat.card R) (f : R[X])
    (hcount : ∑ ℓ ∈ Finset.range M, (ℓ * f.natDegree + D + J) < e * J * (D + 1)) :
    ∃ A : Fin e → R[X][X], (∃ i, A i ≠ 0) ∧ (∀ i j, ((A i).coeff j).natDegree ≤ D) ∧
      (∀ i, (A i).natDegree < J) ∧ ∀ x, f.eval x ^ c = 1 → ∀ ℓ < M,
        (hasseDeriv ℓ (∑ i : Fin e, f ^ ((i : ℕ) * c) * (A i).eval (X ^ Nat.card R))).eval x =
          0 := by
  classical
  rcases finite_or_infinite R with hR | hR
  · have := Fintype.ofFinite R
    -- `Fintype.fieldOfDomain` extends the given `CommRing R` structure, so the ring operations
    -- of `hRF` are those of `R`, and the field case is the original goal.
    let hRF : Field R := Fintype.fieldOfDomain R
    exact exists_ne_zero_and_forall_eval_hasseDeriv_sum_eq_zero_of_field hM f hcount
  · obtain rfl : M = 0 := by simpa using hM
    have he : 0 < e ∧ 0 < J := by
      simp only [Finset.range_zero, Finset.sum_empty] at hcount
      exact ⟨Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hcount),
        Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hcount)⟩
    refine ⟨fun _ => 1, ⟨⟨0, he.1⟩, one_ne_zero⟩, fun i j => ?_, fun i => by simpa using he.2,
      fun x _ ℓ hℓ => absurd hℓ (Nat.not_lt_zero ℓ)⟩
    rw [coeff_one]
    split_ifs <;> simp

end Polynomial
