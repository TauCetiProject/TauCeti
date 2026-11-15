/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.KnotTheory.Jimbo.Normalization
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import TauCeti.KnotTheory.Markov.Skein

/-!
# The reduced Jimbo trace

The writhe-normalized Jimbo trace assigns the quantum dimension to the unknot.
Over a field, dividing by that dimension gives the reduced `sl_N` specialization
of HOMFLY, `MarkovBraid.jimboReducedTrace`, with unknot value one whenever the
quantum dimension is nonzero. It retains Markov invariance and the skein relation
with `a = q ^ N` and `z = q - q⁻¹`. The field quotient uses total division, so at
a zero quantum dimension it vanishes rather than giving an unknot-normalized
invariant.

For positive `N`, the writhe-normalized trace at the generic Laurent unit `T` of
`ℤ[T, T⁻¹]` is divisible in `ℤ[T, T⁻¹]` by the nonzero generic quantum dimension
(`[N]_T ≠ 0`, `KnotTheory.jimboWeight_sum_genericUnit_ne_zero`). Its Laurent
polynomial quotient `MarkovBraid.jimboReducedLaurent` evaluates along
`LaurentPolynomial.eval₂ (Int.castRingHom R) q` at every unit `q : Rˣ` of every
commutative ring `R`: over a field with nonzero quantum dimension it agrees with
`MarkovBraid.jimboReducedTrace`, while at zero-factor specializations it remains
regular, evaluating at `q = 1` to `N ^ (β.componentCount - 1)` and at `q = -1` to
`((-1) ^ (N - 1) * N) ^ (β.componentCount - 1)`.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (the normalization of enhanced braid traces).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

The construction uses `MarkovBraid.jimboTrace`, and the calculations use its
skein relation, `jimboWeight_sum`, and `MarkovBraid.eq_of_skein`.
-/

public section

namespace TauCeti

open KnotTheory
open scoped BigOperators

variable {K : Type*} [Field K] {N n : ℕ}

namespace MarkovBraid

/-- Divide the writhe-normalized Jimbo trace by its unknot value. This gives the
reduced `sl_N` specialization when the quantum dimension is nonzero. -/
noncomputable def jimboReducedTrace (β : MarkovBraid) (q : Kˣ) : K :=
  β.jimboTrace (N := N) q / ∑ a : Fin N, jimboWeight q a

/-- The reduced trace is the normalized trace divided by the quantum dimension. -/
theorem jimboReducedTrace_def (β : MarkovBraid) (q : Kˣ) :
    β.jimboReducedTrace (N := N) q =
      β.jimboTrace (N := N) q / ∑ a : Fin N, jimboWeight q a := (rfl)

/-- Conjugation preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_conj (q : Kˣ) (b c : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N) ⟨n, c * b * c⁻¹⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_conj]

/-- Positive Markov stabilization preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_stabilize (q : Kˣ) (b : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_stabilize]

/-- Negative Markov stabilization preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_stabilizeInv (q : Kˣ) (b : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_stabilizeInv]

/-- Multiplying the reduced trace by the nonzero quantum dimension recovers the
writhe-normalized trace. -/
@[simp]
theorem jimboReducedTrace_mul_sum (β : MarkovBraid) (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q * (∑ a : Fin N, jimboWeight q a) =
      β.jimboTrace (N := N) q := by
  rw [jimboReducedTrace_def, div_mul_cancel₀ _ hδ]

/-- The `(n + 1)`-component unlink has reduced trace equal to the `n`-th power
of the quantum dimension. In particular the one-strand unknot has value one. -/
@[simp]
theorem jimboReducedTrace_one (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := N) ⟨n, 1⟩ q = (∑ a : Fin N, jimboWeight q a) ^ n := by
  rw [jimboReducedTrace_def, jimboTrace_one, pow_succ, mul_div_cancel_right₀ _ hδ]

/-- The reduced trace satisfies the oriented HOMFLY skein relation in any braid context. -/
theorem jimboReducedTrace_skein (q : Kˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    ↑(q ^ N) * jimboReducedTrace (N := N)
        ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ q -
      ↑((q⁻¹) ^ N) * jimboReducedTrace (N := N)
        ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ q =
      ((q : K) - ↑(q⁻¹)) * jimboReducedTrace (N := N) ⟨n, b * c⟩ q := by
  simp only [jimboReducedTrace_def, ← mul_div_assoc, ← sub_div]
  rw [jimboTrace_skein]

end MarkovBraid

/-- Markov-equivalent braids have the same reduced Jimbo trace. -/
theorem MarkovEquiv.jimboReducedTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (q : Kˣ) : β.jimboReducedTrace (N := N) q = γ.jimboReducedTrace (N := N) q := by
  rw [MarkovBraid.jimboReducedTrace_def, MarkovBraid.jimboReducedTrace_def,
    h.jimboTrace_eq q]

namespace MarkovBraid

/-- The closure of the positive two-strand braid `σ₀ ^ 3` has the reduced
trefoil value `a⁻² (z² + 2) - a⁻⁴`, where `a = q ^ N` and `z = q - q⁻¹`. -/
theorem jimboReducedTrace_trefoil (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0 ^ 3⟩ q =
      (↑((q⁻¹) ^ N) : K) ^ 2 * (((q : K) - ↑(q⁻¹)) ^ 2 + 2) -
        (↑((q⁻¹) ^ N) : K) ^ 4 := by
  let s : BraidGroup 2 := BraidGroup.sigma 0
  have hs : jimboReducedTrace (N := N) ⟨1, s⟩ q = 1 := by
    simpa [s, Fin.last, hδ] using
      (markovEquiv_sigma_last_one_one.jimboReducedTrace_eq (N := N) q)
  have h₂ := jimboReducedTrace_skein (N := N) q s 1 (0 : Fin 1)
  have h₃ := jimboReducedTrace_skein (N := N) q (s ^ 2) 1 (0 : Fin 1)
  have hsig : BraidGroup.sigma (n := 2) 0 = s := rfl
  rw [hsig] at h₂ h₃
  -- Normalize the braid products to powers before using the two skein equations.
  simp only [mul_one] at h₂
  rw [← pow_two, mul_inv_cancel] at h₂
  simp only [jimboReducedTrace_one q hδ, pow_one, hs, mul_one] at h₂
  have hcancel : s ^ 2 * s⁻¹ = s := by group
  simp only [mul_one, ← pow_succ, hcancel, hs, mul_one] at h₃
  have hdim := jimboWeight_sum (N := N) q
  have ha : (↑(q ^ N) : K) * ↑((q⁻¹) ^ N) = 1 := by
    rw [inv_pow]
    exact Units.mul_inv _
  -- Eliminate the two-crossing value and the quantum dimension from the skein equations.
  linear_combination
    (↑((q⁻¹) ^ N) : K) ^ 2 * ↑(q ^ N) * h₃ +
    (↑((q⁻¹) ^ N) : K) ^ 2 * ((q : K) - ↑(q⁻¹)) * h₂ +
    (↑((q⁻¹) ^ N) : K) ^ 3 * hdim -
    (jimboReducedTrace (N := N) ⟨1, s ^ 3⟩ q *
      (↑(q ^ N) * ↑((q⁻¹) ^ N) + 1) - 2 * (↑((q⁻¹) ^ N) : K) ^ 2) * ha

/-- With two colours the trefoil value is `q⁻² + q⁻⁶ - q⁻⁸`, the Jones value
`t + t³ - t⁴` after the substitution `t = q⁻²`. -/
theorem jimboReducedTrace_trefoil_two (q : Kˣ)
    (hδ : (∑ a : Fin 2, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := 2) ⟨1, BraidGroup.sigma (n := 2) 0 ^ 3⟩ q =
      (↑(q⁻¹) : K) ^ 2 + (↑(q⁻¹) : K) ^ 6 - (↑(q⁻¹) : K) ^ 8 := by
  rw [jimboReducedTrace_trefoil q hδ]
  simp only [Units.val_pow_eq_pow_val]
  have ha : (q : K) * ↑(q⁻¹) = 1 := Units.mul_inv _
  linear_combination
    ((↑(q⁻¹) : K) ^ 2 * ((q : K) * ↑(q⁻¹) + 1) - 2 * (↑(q⁻¹) : K) ^ 4) * ha

end MarkovBraid

/-! ### Universal Laurent polynomial quotient and specializations -/

/-- Ring homomorphisms commute with the Jimbo enhancement weights along `Units.map`. -/
@[simp]
theorem _root_.RingHom.map_jimboWeight {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (q : Rˣ) (a : Fin N) :
    f (jimboWeight q a) = jimboWeight (Units.map (f : R →* S) q) a := by
  simp only [jimboWeight_def, ← map_zpow]
  rfl

namespace KnotTheory

/-- At `q = -1` for positive `N`, every enhancement weight equals `(-1) ^ (N - 1)`. -/
@[simp]
theorem jimboWeight_neg_one {R : Type*} [Ring R] {N : ℕ} [NeZero N] (a : Fin N) :
    jimboWeight (-1 : Rˣ) a = (-1 : R) ^ (N - 1) := by
  have he : (N : ℤ) - 1 - 2 * (a : ℕ) = ((N - 1 : ℕ) : ℤ) - 2 * (a : ℤ) := by
    have := NeZero.ne N
    omega
  have hsq : (-1 : Rˣ) ^ (2 : ℤ) = 1 := Units.ext (by simp)
  rw [jimboWeight_def, he, zpow_sub, zpow_mul, hsq, one_zpow, inv_one, mul_one, zpow_natCast]
  simp

/-- For positive `N` over a nontrivial ring, the generic quantum dimension `[N]_T` in `R[T;T⁻¹]`
is nonzero. -/
theorem jimboWeight_sum_genericUnit_ne_zero (R : Type*) [Ring R] [Nontrivial R]
    (N : ℕ) [NeZero N] :
    (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit R) a) ≠ 0 := by
  intro h
  have hs := jimboWeight_sum (N := N) (LaurentPolynomial.genericUnit R)
  have hN : (N : ℤ) ≠ -(N : ℤ) := by
    have := NeZero.ne N
    omega
  rw [h, mul_zero, inv_pow, ← zpow_natCast, ← zpow_neg,
    LaurentPolynomial.genericUnit_zpow_val, LaurentPolynomial.genericUnit_zpow_val] at hs
  exact LaurentPolynomial.T_sub_T_ne_zero hN hs.symm

/-- Over any commutative ring `R`, the unnormalized weighted Jimbo trace of a nonempty braid at
`LaurentPolynomial.genericUnit R` is divisible by the generic quantum dimension `[N]_T`. -/
private theorem sum_jimboWeight_dvd_jimboWeightedTrace {R : Type*} [CommRing R] (N : ℕ) :
    ∀ {m : ℕ} (b : BraidGroup (m + 1)),
      (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit R) a) ∣
        jimboWeightedTrace (N := N) (LaurentPolynomial.genericUnit R) b := by
  let q₀ := LaurentPolynomial.genericUnit R
  let δ : LaurentPolynomial R := ∑ a : Fin N, jimboWeight q₀ a
  let z₀ : LaurentPolynomial R := (q₀ : LaurentPolynomial R) - ↑q₀⁻¹
  intro m
  induction m with
  | zero =>
    intro b
    rw [BraidGroup.eq_one_of_le_one le_rfl b, jimboWeightedTrace_one, pow_one]
  | succ m ih =>
    let φ : MonoidAlgebra (LaurentPolynomial R) (BraidGroup (m + 2)) →ₗ[LaurentPolynomial R]
        LaurentPolynomial R :=
      Finsupp.linearCombination (LaurentPolynomial R) (jimboWeightedTrace (N := N) q₀) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv (LaurentPolynomial R)).toLinearMap
    have hφ (g : BraidGroup (m + 2)) (r : LaurentPolynomial R) :
        φ (MonoidAlgebra.single g r) = r * jimboWeightedTrace (N := N) q₀ g := by
      simp [φ, MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single]
    have hle : BraidGroup.strandSpan (LaurentPolynomial R) m ⊔
        BraidGroup.heckeSkein (LaurentPolynomial R) z₀ (m + 2) ≤
        Submodule.comap φ (Ideal.span {δ}) := by
      refine sup_le ((BraidGroup.strandSpan_le_iff _).mpr ⟨fun d ↦ ?_, fun d e ↦ ?_⟩)
        ((BraidGroup.heckeSkein_le_iff _ _).mpr fun b c i ↦ ?_) <;>
        simp only [Submodule.mem_comap, Ideal.mem_span_singleton]
      · rw [hφ, one_mul, jimboWeightedTrace_strandIncl]
        exact dvd_mul_left δ _
      · rw [hφ, one_mul, jimboWeightedTrace_mul_comm, ← mul_assoc, ← map_mul,
          jimboWeightedTrace_stabilize]
        exact dvd_mul_of_dvd_right (ih (e * d)) _
      · rw [BraidGroup.heckeRelator_def, map_sub, map_sub, hφ, hφ, hφ,
          one_mul, one_mul, jimboWeightedTrace_skein]
        simp [z₀]
    rw [BraidGroup.strandSpan_sup_heckeSkein_eq_top, top_le_iff] at hle
    intro b
    have hb : MonoidAlgebra.single b 1 ∈ Submodule.comap φ (Ideal.span {δ}) :=
      hle ▸ Submodule.mem_top
    simpa only [Submodule.mem_comap, Ideal.mem_span_singleton, hφ, one_mul] using hb

end KnotTheory

namespace MarkovBraid

/-- Ring homomorphisms commute with the writhe-normalized Jimbo trace, mapping the parameter unit
along `Units.map`. -/
theorem map_jimboTrace {R S : Type*} [CommRing R] [CommRing S] (β : MarkovBraid)
    (f : R →+* S) (q : Rˣ) :
    f (β.jimboTrace (N := N) q) = β.jimboTrace (N := N) (Units.map (f : R →* S) q) := by
  let qS : Sˣ := Units.map (f : R →* S) q
  have hqS : (qS : S) = f q := rfl
  have hqS_inv : (↑qS⁻¹ : S) = f ↑q⁻¹ := by rw [← map_inv]; rfl
  have hsum : f (∑ a : Fin N, jimboWeight q a) = ∑ a : Fin N, jimboWeight qS a := by
    simp [qS]
  refine congrFun (eq_of_skein (qS ^ N) ((qS : S) - ↑qS⁻¹) (∑ a : Fin N, jimboWeight qS a)
    (F := fun γ ↦ f (γ.jimboTrace (N := N) q))
    (G := fun γ ↦ γ.jimboTrace (N := N) qS)
    (fun _ _ h ↦ congrArg f (h.jimboTrace_eq q))
    (fun _ _ h ↦ h.jimboTrace_eq qS) ?_ ?_ ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg f (jimboTrace_skein (N := N) q 1 c i)
    simpa only [one_mul, map_sub, map_mul, Units.val_pow_eq_pow_val, map_pow, ← inv_pow,
      smul_eq_mul, hqS, hqS_inv] using hs
  · intro m c i
    simpa only [one_mul, smul_eq_mul, inv_pow] using jimboTrace_skein (N := N) qS 1 c i
  · intro m b
    simp [smul_eq_mul, hsum]
  · intro m b
    simp [smul_eq_mul]
  · simp [hsum]

/-- Over any commutative ring `R`, the writhe-normalized `N`-colour Jimbo trace at the generic
Laurent unit `T` is divisible in `R[T;T⁻¹]` by the generic quantum dimension `[N]_T`. -/
theorem dvd_jimboTrace_genericUnit {R : Type*} [CommRing R] (β : MarkovBraid) (N : ℕ) :
    (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit R) a) ∣
      β.jimboTrace (N := N) (LaurentPolynomial.genericUnit R) := by
  rw [jimboTrace_def]
  exact dvd_mul_of_dvd_right (sum_jimboWeight_dvd_jimboWeightedTrace N β.braid) _

/-- The universal reduced `N`-colour Jimbo invariant of a braid closure in `ℤ[T;T⁻¹]`, chosen as
a Laurent polynomial quotient of `jimboTrace` at `T` by `[N]_T` (unique when `N ≠ 0`, see
`jimboReducedLaurent_eq_iff`). Evaluating at any unit `q : Rˣ` of a commutative ring specializes
the reduced invariant without dividing by `[N]_q`, so zero-factor specializations such as `q = ±1`
and quantum roots of unity remain regular. -/
noncomputable def jimboReducedLaurent (β : MarkovBraid) (N : ℕ) :
    LaurentPolynomial ℤ :=
  (β.dvd_jimboTrace_genericUnit (R := ℤ) N).choose

/-- Multiplying `jimboReducedLaurent` by the generic quantum dimension recovers `jimboTrace` at
`LaurentPolynomial.genericUnit ℤ`. -/
@[simp]
theorem jimboReducedLaurent_mul_sum (β : MarkovBraid) (N : ℕ) :
    β.jimboReducedLaurent N *
        (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) =
      β.jimboTrace (N := N) (LaurentPolynomial.genericUnit ℤ) :=
  (mul_comm _ _).trans (β.dvd_jimboTrace_genericUnit (R := ℤ) N).choose_spec.symm

/-- A Laurent polynomial equals `β.jimboReducedLaurent N` if and only if its product with the
generic quantum dimension is `β.jimboTrace` at `LaurentPolynomial.genericUnit ℤ`. -/
theorem jimboReducedLaurent_eq_iff (β : MarkovBraid) (N : ℕ) [NeZero N]
    {P : LaurentPolynomial ℤ} :
    β.jimboReducedLaurent N = P ↔
      P * (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) =
        β.jimboTrace (N := N) (LaurentPolynomial.genericUnit ℤ) := by
  rw [← jimboReducedLaurent_mul_sum β N,
    mul_left_inj' (jimboWeight_sum_genericUnit_ne_zero ℤ N), eq_comm]

end MarkovBraid

/-- Markov-equivalent braids have the same universal reduced Jimbo Laurent polynomial. -/
theorem MarkovEquiv.jimboReducedLaurent_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (N : ℕ) [NeZero N] : β.jimboReducedLaurent N = γ.jimboReducedLaurent N := by
  rw [MarkovBraid.jimboReducedLaurent_eq_iff, MarkovBraid.jimboReducedLaurent_mul_sum,
    h.jimboTrace_eq]

namespace MarkovBraid

/-- The `(n + 1)`-component unlink has universal reduced Jimbo Laurent polynomial equal to the
`n`-th power of the generic quantum dimension. -/
@[simp]
theorem jimboReducedLaurent_one (n N : ℕ) [NeZero N] :
    jimboReducedLaurent ⟨n, 1⟩ N =
      (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) ^ n := by
  rw [jimboReducedLaurent_eq_iff, jimboTrace_one, ← pow_succ]

/-- Adding an uncrossed strand multiplies `jimboReducedLaurent` by the generic quantum dimension. -/
@[simp]
theorem jimboReducedLaurent_strandIncl {n : ℕ} (b : BraidGroup (n + 1)) (N : ℕ) [NeZero N] :
    jimboReducedLaurent ⟨n + 1, BraidGroup.strandIncl b⟩ N =
      (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) *
        jimboReducedLaurent ⟨n, b⟩ N := by
  rw [jimboReducedLaurent_eq_iff, jimboTrace_strandIncl, mul_assoc, jimboReducedLaurent_mul_sum]

/-- The universal reduced Jimbo Laurent polynomial satisfies the oriented HOMFLY skein relation
with `a = T ^ N` and `z = T - T⁻¹` in every braid context. -/
theorem jimboReducedLaurent_skein {n : ℕ} (N : ℕ) [NeZero N]
    (b c : BraidGroup (n + 1)) (i : Fin n) :
    LaurentPolynomial.T (N : ℤ) *
        jimboReducedLaurent ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ N -
      LaurentPolynomial.T (-(N : ℤ)) *
        jimboReducedLaurent ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ N =
      (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
        jimboReducedLaurent ⟨n, b * c⟩ N := by
  apply mul_right_cancel₀ (jimboWeight_sum_genericUnit_ne_zero ℤ N)
  have hs := jimboTrace_skein (N := N) (LaurentPolynomial.genericUnit ℤ) b c i
  rw [← zpow_natCast, inv_pow, ← zpow_natCast, ← zpow_neg,
    LaurentPolynomial.genericUnit_zpow_val, LaurentPolynomial.genericUnit_zpow_val,
    LaurentPolynomial.genericUnit_val, LaurentPolynomial.genericUnit_inv] at hs
  simpa only [sub_mul, mul_assoc, jimboReducedLaurent_mul_sum] using hs

/-- Evaluating `jimboReducedLaurent` at any unit `q : Rˣ` and multiplying by `[N]_q` recovers the
writhe-normalized Jimbo trace `β.jimboTrace q` over any commutative ring `R`. -/
theorem eval₂_jimboReducedLaurent_mul_sum {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) (q : Rˣ) :
    LaurentPolynomial.eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) *
        (∑ a : Fin N, jimboWeight q a) =
      β.jimboTrace (N := N) q := by
  let f : LaurentPolynomial ℤ →+* R := LaurentPolynomial.eval₂ (Int.castRingHom R) q
  have hmap : Units.map (f : LaurentPolynomial ℤ →* R) (LaurentPolynomial.genericUnit ℤ) = q :=
    Units.ext (by simp [f])
  have h := congrArg f (β.jimboReducedLaurent_mul_sum N)
  simpa only [f, map_mul, map_sum, RingHom.map_jimboWeight, β.map_jimboTrace, hmap] using h

/-- Over a field with nonzero quantum dimension `[N]_q ≠ 0`, evaluating `jimboReducedLaurent` at
`q` agrees with the field quotient `β.jimboReducedTrace q`. -/
theorem eval₂_jimboReducedLaurent_eq_jimboReducedTrace (β : MarkovBraid) (N : ℕ)
    (q : Kˣ) (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    LaurentPolynomial.eval₂ (Int.castRingHom K) q (β.jimboReducedLaurent N) =
      β.jimboReducedTrace (N := N) q := by
  apply mul_right_cancel₀ hδ
  rw [eval₂_jimboReducedLaurent_mul_sum, jimboReducedTrace_mul_sum β q hδ]

/-- Specializing `jimboReducedLaurent` at the zero-factor parameter `q = 1` gives
`N ^ (β.componentCount - 1)` over any commutative ring, even though `q - q⁻¹ = 0`. -/
@[simp]
theorem eval₂_jimboReducedLaurent_one {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) [NeZero N] :
    LaurentPolynomial.eval₂ (Int.castRingHom R) (1 : Rˣ) (β.jimboReducedLaurent N) =
      (N : R) ^ (β.componentCount - 1) := by
  let f : LaurentPolynomial ℤ →+* R := LaurentPolynomial.eval₂ (Int.castRingHom R) (1 : Rˣ)
  have hmap : Units.map (f : LaurentPolynomial ℤ →* R) (LaurentPolynomial.genericUnit ℤ) =
      (1 : Rˣ) := Units.ext (by simp [f])
  have hsum : f (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) = (N : R) := by
    simp [f, RingHom.map_jimboWeight, hmap]
  refine congrFun (eq_of_skein (1 : Rˣ) (0 : R) (N : R)
    (F := fun γ ↦ f (γ.jimboReducedLaurent N))
    (G := fun γ ↦ (N : R) ^ (γ.componentCount - 1))
    (fun _ _ h ↦ congrArg f (h.jimboReducedLaurent_eq N))
    (fun _ _ h ↦ by rw [h.componentCount_eq]) ?_ ?_ ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg f (jimboReducedLaurent_skein N 1 c i)
    simpa [f, smul_eq_mul] using hs
  · intro m c i
    have hc := componentCount_mul_sigma_inv_mul 1 c i
    simp only [one_mul] at hc
    simp [hc]
  · intro m b
    simp [f, smul_eq_mul, hsum]
  · intro m b
    have hpos : 1 ≤ componentCount ⟨m, b⟩ := componentCount_pos ⟨m, b⟩
    have he : componentCount ⟨m, b⟩ + 1 - 1 = (componentCount ⟨m, b⟩ - 1) + 1 := by omega
    rw [componentCount_strandIncl, he, pow_succ', smul_eq_mul]
  · simp [f]

/-- Specializing `jimboReducedLaurent` at the zero-factor parameter `q = -1` gives
`((-1) ^ (N - 1) * N) ^ (β.componentCount - 1)` over any commutative ring. -/
@[simp]
theorem eval₂_jimboReducedLaurent_neg_one {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) [NeZero N] :
    LaurentPolynomial.eval₂ (Int.castRingHom R) (-1 : Rˣ) (β.jimboReducedLaurent N) =
      ((-1 : R) ^ (N - 1) * (N : R)) ^ (β.componentCount - 1) := by
  let f : LaurentPolynomial ℤ →+* R := LaurentPolynomial.eval₂ (Int.castRingHom R) (-1 : Rˣ)
  have hmap : Units.map (f : LaurentPolynomial ℤ →* R) (LaurentPolynomial.genericUnit ℤ) =
      (-1 : Rˣ) := Units.ext (by simp [f])
  have hsum : f (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) =
      (-1 : R) ^ (N - 1) * (N : R) := by
    simp [f, RingHom.map_jimboWeight, hmap, mul_comm (N : R)]
  have hε : (((-1 : Rˣ) ^ N)⁻¹ : Rˣ) = (-1 : Rˣ) ^ N := Units.ext (by simp [← inv_pow])
  refine congrFun (eq_of_skein ((-1 : Rˣ) ^ N) (0 : R) ((-1 : R) ^ (N - 1) * (N : R))
    (F := fun γ ↦ f (γ.jimboReducedLaurent N))
    (G := fun γ ↦ ((-1 : R) ^ (N - 1) * (N : R)) ^ (γ.componentCount - 1))
    (fun _ _ h ↦ congrArg f (h.jimboReducedLaurent_eq N))
    (fun _ _ h ↦ by rw [h.componentCount_eq]) ?_ ?_ ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg f (jimboReducedLaurent_skein N 1 c i)
    have hT₁ : f (LaurentPolynomial.T (N : ℤ)) = ↑((-1 : Rˣ) ^ N) := by simp [f]
    have hT₂ : f (LaurentPolynomial.T (-(N : ℤ))) = ↑(((-1 : Rˣ) ^ N)⁻¹) := by
      simp [f, zpow_neg]
    have hT₀ : f (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) = 0 := by simp [f]
    simpa only [one_mul, map_sub, map_mul, smul_eq_mul, zero_mul, hT₁, hT₂, hT₀] using hs
  · intro m c i
    have hc := componentCount_mul_sigma_inv_mul 1 c i
    simp only [one_mul] at hc
    simp [hc, hε]
  · intro m b
    simp [f, smul_eq_mul, hsum]
  · intro m b
    have hpos : 1 ≤ componentCount ⟨m, b⟩ := componentCount_pos ⟨m, b⟩
    have he : componentCount ⟨m, b⟩ + 1 - 1 = (componentCount ⟨m, b⟩ - 1) + 1 := by omega
    rw [componentCount_strandIncl, he, pow_succ', smul_eq_mul]
  · simp [f]

end MarkovBraid

end TauCeti
