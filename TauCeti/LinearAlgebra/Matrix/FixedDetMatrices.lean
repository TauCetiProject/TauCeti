/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import TauCeti.Algebra.Module.Primitive
import Mathlib.Tactic.LinearCombination

/-!
# Upper-triangular representatives of integral matrices of fixed determinant

Mathlib's `FixedDetMatrices.reps n` is the set of integral matrices `(a b; 0 d)` with `ad = n`,
`0 < a` and `0 ≤ b < |d|`, and Mathlib proves (`FixedDetMatrices.reduce_mem_reps`) that, for
`n ≠ 0`, the reduction algorithm carries every determinant-`n` matrix into it. This file completes
that to the statement that `FixedDetMatrices.reps n` is a set of representatives for the action of
`SL(2, ℤ)` by left multiplication on the determinant-`n` matrices, `n ≠ 0`, and counts it.
It also records that only finitely many integral matrices of a given determinant have entries
bounded by a given constant. Restricted to the primitive matrices, those whose entries have greatest
common divisor one, the representatives `FixedDetMatrices.primitiveReps n` are the
`(a b; 0 d)` with `gcd(a, b, d) = 1`.

## Main results

* `FixedDetMatrices.exists_smul_mem_reps`: for `n ≠ 0`, every determinant-`n` matrix can be moved
  into `FixedDetMatrices.reps n` by `SL(2, ℤ)`.
* `FixedDetMatrices.eq_one_of_smul_mem_reps`: the only `g ∈ SL(2, ℤ)` moving a matrix of
  `FixedDetMatrices.reps n` into `FixedDetMatrices.reps n` is `g = 1`; hence
  (`FixedDetMatrices.eq_of_smul_eq_of_mem_reps`) two matrices of `FixedDetMatrices.reps n` in the
  same `SL(2, ℤ)`-orbit are equal.
* `FixedDetMatrices.pos_val_one_one_of_mem_reps`: a representative `(a b; 0 d)` of positive
  determinant has `0 < d`.
* `FixedDetMatrices.repsEquiv`: the representatives are parametrized by positive factor pairs
  `(a, d)` of `|n|` and residues `0 ≤ b < d`.
* `FixedDetMatrices.ncard_reps`: `FixedDetMatrices.reps n` has `σ₁(|n|)` elements.
* `FixedDetMatrices.sum_reps_pow`: for even `w`, the sum of `dʷ` over the representatives
  `(a b; 0 d)` is `σ_{w+1}(|n|)`.
* `FixedDetMatrices.finite_setOf_abs_le`: there are only finitely many integral matrices of
  determinant `n` whose entries are at most `B` in absolute value.
* `FixedDetMatrices.toGL`: for `n ≠ 0`, an integral matrix of determinant `n` as an element of
  `GL(m, ℚ)`, on which left multiplication by `SL(m, ℤ)` is multiplication by its image
  (`FixedDetMatrices.toGL_smul`), and `FixedDetMatrices.toGLReal`, its image in `GL(m, ℝ)`.
* `FixedDetMatrices.isPrimitive_smul_iff`: left multiplication by `SL(m, ℤ)` preserves
  primitivity.
* `FixedDetMatrices.primitiveReps`: the primitive matrices of `FixedDetMatrices.reps n`, and
  `FixedDetMatrices.exists_smul_mem_primitiveReps`: for `n ≠ 0` every primitive matrix of
  determinant `n` can be moved into them by `SL(2, ℤ)`.
* `TauCeti.isPrimitive_upperTri_mul_emod_iff`: multiplying the upper-right entry of `(a b; 0 d)` by
  `m` coprime to `gcd(a, d)` modulo `d` preserves and reflects primitivity.
* `FixedDetMatrices.scaleRep`: the action of `(ZMod m)ˣ` on `FixedDetMatrices.reps m` scaling the
  upper-right residue `(a b; 0 d) ↦ (a, u b mod d; 0, d)`, which permutes
  `FixedDetMatrices.primitiveReps m` (`FixedDetMatrices.image_scaleRep_primitiveReps`).

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Sections 1–2: these are the
  representatives `ℳₙ^∞` of `Γ \ ℳₙ` fixing `∞`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

/-- Multiplying the upper-right entry of an upper-triangular `2 × 2` integral matrix
`!![a, b; 0, d]` by `m` coprime to `gcd(a, d)` and reducing modulo `d` preserves and reflects
`IsPrimitive`. -/
theorem isPrimitive_upperTri_mul_emod_iff {a b d m : ℤ} (hm : IsCoprime m (a.gcd d : ℤ)) :
    IsPrimitive !![a, m * b % d; 0, d] ↔ IsPrimitive !![a, b; 0, d] := by
  have hiff (b' : ℤ) :
      IsPrimitive !![a, b'; 0, d] ↔ ∃ c₀₀ c₀₁ c₁₁ : ℤ, a * c₀₀ + b' * c₀₁ + d * c₁₁ = 1 := by
    rw [isPrimitive_def]
    refine ⟨fun ⟨f, hf⟩ ↦ ⟨f !![1, 0; 0, 0], f !![0, 1; 0, 0], f !![0, 0; 0, 1], ?_⟩,
      fun ⟨c₀₀, c₀₁, c₁₁, hc⟩ ↦ ⟨c₀₀ • (entryAddMonoidHom ℤ 0 0).toIntLinearMap +
        c₀₁ • (entryAddMonoidHom ℤ 0 1).toIntLinearMap +
        c₁₁ • (entryAddMonoidHom ℤ 1 1).toIntLinearMap,
        by simpa only [LinearMap.add_apply, LinearMap.smul_apply, AddMonoidHom.coe_toIntLinearMap,
          entryAddMonoidHom_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
          cons_val_fin_one, smul_eq_mul] using by linear_combination hc⟩⟩
    have hmat : !![a, b'; (0 : ℤ), d] =
        a • !![1, 0; 0, 0] + b' • !![0, 1; 0, 0] + d • !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hmat, map_add, map_add, map_zsmul, map_zsmul, map_zsmul] at hf
    simpa only [zsmul_eq_mul, Int.cast_id] using hf
  rw [hiff, hiff]
  have hdiv : m * b % d + d * (m * b / d) = m * b := Int.emod_add_mul_ediv (m * b) d
  constructor
  · rintro ⟨c₀₀, c₀₁, c₁₁, hc⟩
    exact ⟨c₀₀, m * c₀₁, c₁₁ - (m * b / d) * c₀₁, by linear_combination hc - c₀₁ * hdiv⟩
  · rintro ⟨c₀₀, c₀₁, c₁₁, hc⟩
    obtain ⟨x, y, hxy⟩ := hm
    exact ⟨c₀₀ + y * b * a.gcdA d * c₀₁, x * c₀₁,
      c₁₁ + (x * (m * b / d) + y * b * a.gcdB d) * c₀₁,
      by
        linear_combination
          hc + c₀₁ * x * hdiv + c₀₁ * b * hxy - c₀₁ * y * b * Int.gcd_eq_gcd_ab a d⟩

end TauCeti

namespace FixedDetMatrices

variable {n : ℤ}

/-- Every determinant-`n` matrix can be moved into `reps n` by left
multiplication by `SL(2, ℤ)`, when `n ≠ 0`. -/
theorem exists_smul_mem_reps (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) :
    ∃ g : SL(2, ℤ), g • A ∈ reps n := by
  induction A using induction_on hn with
  | h0 A h₁₀ h₀₀ h₀₁ h₁₁ => exact ⟨1, by simpa using ⟨h₁₀, h₀₀, h₀₁, h₁₁⟩⟩
  | hS B hB | hT B hB =>
    obtain ⟨g, hg⟩ := hB
    exact ⟨g * _⁻¹, by rwa [mul_smul, inv_smul_smul]⟩

/-- The entries of `g • A` for `g ∈ SL(2, R)` and a `2 × 2` matrix `A` of fixed determinant. -/
theorem smul_coe_apply {R : Type*} [CommRing R] {m : R} (g : SpecialLinearGroup (Fin 2) R)
    (A : FixedDetMatrix (Fin 2) R m) (i j : Fin 2) :
    (g • A).val i j = g i 0 * A.val 0 j + g i 1 * A.val 1 j := by
  rw [smul_coe, Matrix.mul_apply, Fin.sum_univ_two]

/-- No nontrivial element of `SL(2, ℤ)` moves a representative to a representative: if `A` and
`g • A` both lie in `reps n`, then `g = 1`. -/
theorem eq_one_of_smul_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n} {g : SL(2, ℤ)}
    (hA : A ∈ reps n) (hgA : g • A ∈ reps n) : g = 1 := by
  obtain ⟨hA₁₀, hA₀₀, hA₀₁, hA₁₁⟩ := hA
  obtain ⟨hg₁₀, h₀₀, h₀₁, h₁₁⟩ := hgA
  simp only [smul_coe_apply, hA₁₀, mul_zero, add_zero, mul_eq_zero, hA₀₀.ne', or_false]
    at hg₁₀ h₀₀
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [det_fin_two, hg₁₀, mul_zero, sub_zero] using g.det_coe
  have hg₀₀ := Int.eq_one_of_mul_eq_one_right (nonneg_of_mul_nonneg_left h₀₀.le hA₀₀) hdet
  rw [hg₀₀, one_mul] at hdet
  simp only [smul_coe_apply, hg₀₀, hg₁₀, hdet, one_mul, zero_mul, zero_add] at h₀₁ h₁₁
  -- `g 0 1 * A 1 1` is a multiple of `|A 1 1|` of absolute value less than `|A 1 1|`
  have hg₀₁ : g 0 1 * A.val 1 1 = 0 :=
    Int.eq_zero_of_abs_lt_dvd ((abs_dvd _ _).2 (dvd_mul_left _ _)) <| by
      simpa only [add_sub_cancel_left] using abs_sub_lt_of_nonneg_of_lt h₀₁
        ((le_abs_self _).trans_lt h₁₁) hA₀₁ ((le_abs_self _).trans_lt hA₁₁)
  rw [mul_eq_zero, or_iff_left (abs_pos.mp ((abs_nonneg _).trans_lt hA₁₁))] at hg₀₁
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hg₀₀, hg₀₁, hg₁₀, hdet]

/-- Two matrices of `reps n` in the same `SL(2, ℤ)`-orbit are equal. -/
theorem eq_of_smul_eq_of_mem_reps {A B : FixedDetMatrix (Fin 2) ℤ n} {g : SL(2, ℤ)}
    (hA : A ∈ reps n) (hB : B ∈ reps n) (h : g • A = B) : A = B := by
  subst h
  rw [eq_one_of_smul_mem_reps hA hB, one_smul]

/-- The diagonal entries of an upper-triangular `2 × 2` matrix of determinant `m` multiply to
`m`. -/
lemma apply_zero_zero_mul_apply_one_one {R : Type*} [CommRing R] {m : R}
    {A : FixedDetMatrix (Fin 2) R m} (h : A.val 1 0 = 0) : A.val 0 0 * A.val 1 1 = m := by
  simpa only [det_fin_two, h, mul_zero, sub_zero] using A.property

/-- A representative `(a b; 0 d)` of positive determinant has `0 < d`. -/
theorem pos_val_one_one_of_mem_reps (hn : 0 < n) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps n) : 0 < A.val 1 1 :=
  pos_of_mul_pos_right ((apply_zero_zero_mul_apply_one_one hA.1).symm ▸ hn) hA.2.1.le

/-- A representative `(a b; 0 d) ∈ reps n` has nonzero lower-right entry `d ≠ 0`. -/
theorem apply_one_one_ne_zero_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps n) :
    A.val 1 1 ≠ 0 :=
  abs_pos.mp ((abs_nonneg _).trans_lt hA.2.2.2)

/-- For an upper-triangular `2 × 2` integral matrix of determinant `n`, the absolute values of the
diagonal entries multiply to `|n|`. -/
theorem natAbs_apply_zero_zero_mul_natAbs_apply_one_one {A : FixedDetMatrix (Fin 2) ℤ n}
    (h : A.val 1 0 = 0) : (A.val 0 0).natAbs * (A.val 1 1).natAbs = n.natAbs := by
  rw [← Int.natAbs_mul, apply_zero_zero_mul_apply_one_one h]

/-- For a representative `(a b; 0 d) ∈ reps n`, `|b| < |d|` as natural numbers. -/
theorem natAbs_apply_zero_one_lt_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps n) :
    (A.val 0 1).natAbs < (A.val 1 1).natAbs := by
  zify
  exact hA.2.2.2

/-- An upper-triangular `2 × 2` matrix of fixed determinant is `!![A 0 0, A 0 1; 0, A 1 1]`. -/
theorem val_eq_of_apply_one_zero_eq_zero {R : Type*} [CommRing R] {m : R}
    {A : FixedDetMatrix (Fin 2) R m} (h : A.val 1 0 = 0) :
    A.val = !![A.val 0 0, A.val 0 1; 0, A.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

/-- **The upper-triangular representatives, explicitly parametrized.** For `n ≠ 0`, a
representative `(a b; 0 d)` is recorded by the positive factor pair `(|a|, |d|)` of `|n|`
and the residue `b ∈ Fin |d|`. The inverse gives `d` the sign of `n`.

This is the summation interface for the representatives: an invariant may be summed first over
factor pairs and then over the upper-right entry. -/
def repsEquiv (hn : n ≠ 0) :
    reps n ≃ Σ p : ↥n.natAbs.divisorsAntidiagonal, Fin p.val.2 where
  toFun A :=
    ⟨⟨((A.val.val 0 0).natAbs, (A.val.val 1 1).natAbs), by
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨by rw [← Int.natAbs_mul, apply_zero_zero_mul_apply_one_one A.property.1],
        Int.natAbs_ne_zero.mpr hn⟩⟩,
      ⟨(A.val.val 0 1).natAbs, by
        zify
        exact A.property.2.2.2⟩⟩
  invFun x :=
    ⟨⟨!![(x.1.val.1 : ℤ), (x.2 : ℕ); 0, n.sign * x.1.val.2], by
        calc _ = n.sign * ((x.1.val.1 * x.1.val.2 : ℕ) : ℤ) := by simp [mul_left_comm]
          _ = n := by
            rw [(Nat.mem_divisorsAntidiagonal.mp x.1.property).1, Int.sign_mul_natAbs]⟩,
      by
        refine ⟨rfl, Nat.cast_pos.mpr (Nat.pos_of_ne_zero
          (Nat.left_ne_zero_of_mem_divisorsAntidiagonal x.1.property)), Int.natCast_nonneg _, ?_⟩
        simp [abs_mul, Int.abs_sign_of_ne_zero hn, x.2.isLt]⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    -- the lower-right entry has the sign of `n`, since `n = a * d` with `0 < a`
    exacts [Int.natAbs_of_nonneg A.property.2.1.le, Int.natAbs_of_nonneg A.property.2.2.1,
      A.property.1.symm, by
        simp [← apply_zero_zero_mul_apply_one_one A.property.1,
          Int.sign_eq_one_of_pos A.property.2.1, Int.sign_mul_abs]]
  right_inv x := by
    refine Sigma.ext ?_ ?_
    · apply Subtype.ext
      simp [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn]
    · rw [Fin.heq_ext_iff (by simp [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn])]
      simp

/-- The factor pair recording a representative `(a b; 0 d)` is `(|a|, |d|)`. -/
@[simp]
theorem coe_repsEquiv_apply_fst (hn : n ≠ 0) (A : reps n) :
    ((repsEquiv hn A).1 : ℕ × ℕ) = ((A.val.val 0 0).natAbs, (A.val.val 1 1).natAbs) := (rfl)

/-- The residue recording a representative `(a b; 0 d)` is `|b|`. -/
@[simp]
theorem coe_repsEquiv_apply_snd (hn : n ≠ 0) (A : reps n) :
    ((repsEquiv hn A).2 : ℕ) = (A.val.val 0 1).natAbs := (rfl)

/-- The matrix represented by a factor pair `(a, d)` and a residue `b` is
`(a b; 0, sign(n)d)`. -/
@[simp]
theorem coe_repsEquiv_symm_apply (hn : n ≠ 0)
    (x : Σ p : ↥n.natAbs.divisorsAntidiagonal, Fin p.val.2) :
    ((repsEquiv hn).symm x : FixedDetMatrix (Fin 2) ℤ n).val =
      !![(x.1.val.1 : ℤ), (x.2 : ℕ); 0, n.sign * x.1.val.2] := (rfl)

/-- **The number of upper-triangular representatives**: the set `reps n` has `σ₁(|n|)`
elements, one for each divisor `d` of `|n|` and each `0 ≤ b < d`. -/
@[simp]
theorem ncard_reps (n : ℤ) : (reps n).ncard = ArithmeticFunction.sigma 1 n.natAbs := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [← Nat.card_coe_set_eq, Nat.card_congr (repsEquiv hn), Nat.card_sigma,
    ArithmeticFunction.sigma_one_apply,
    ← Nat.sum_divisorsAntidiagonal' fun _ d ↦ d]
  simp only [Nat.card_fin]
  rw [Finset.sum_coe_sort]

/-- **The divisor sum over the upper-triangular representatives**: for even `w`, the
sum of `dʷ` over the representatives `(a b; 0 d)` in `reps n` is `σ_{w+1}(|n|)`, since each factor
pair `(a, d)` of `|n|` carries `|d|` representatives. -/
theorem sum_reps_pow {R : Type*} [CommRing R] {w : ℕ} (hw : Even w) :
    ∑ A : reps n, ((A.val.val 1 1 : ℤ) : R) ^ w =
      (ArithmeticFunction.sigma (w + 1) n.natAbs : R) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hsign : (n.sign : R) ^ w = 1 := by
    rw [← Int.cast_pow, ← hw.pow_abs, Int.abs_sign_of_ne_zero hn, one_pow, Int.cast_one]
  rw [← (repsEquiv hn).symm.sum_comp, Fintype.sum_sigma]
  simp only [coe_repsEquiv_symm_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_mul,
    Int.cast_natCast, mul_pow, hsign, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_coe_sort n.natAbs.divisorsAntidiagonal
      (fun p ↦ ((p.2 : ℕ) : R) * ((p.2 : ℕ) : R) ^ w),
    Nat.sum_divisorsAntidiagonal' (fun _ d ↦ ((d : ℕ) : R) * (d : R) ^ w),
    ArithmeticFunction.sigma_apply]
  push_cast
  exact Finset.sum_congr rfl fun d _ ↦ by ring

/-- **Finiteness of bounded matrices**: there are only finitely many integral matrices of
determinant `n` whose entries are at most `B` in absolute value. -/
theorem finite_setOf_abs_le {m : Type*} [Fintype m] [DecidableEq m] (n B : ℤ) :
    {A : FixedDetMatrix m ℤ n | ∀ i j, |A.val i j| ≤ B}.Finite :=
  ((Set.Finite.pi' fun _ ↦ Set.Finite.pi' fun _ ↦ Set.finite_Icc (-B) B).preimage
    (f := fun A : FixedDetMatrix m ℤ n ↦ (A.val : m → m → ℤ))
    Subtype.val_injective.injOn).subset fun _ hA i j ↦ abs_le.mp (hA i j)

/-! ### Integral matrices of nonzero determinant as rational invertible matrices -/

section ToGL

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- For `n ≠ 0`, an integral matrix of determinant `n` as an invertible rational matrix, the form
in which it acts on the upper half-plane and on the cusps `ℙ¹(ℚ)`. -/
noncomputable def toGL (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) : GL m ℚ :=
  .mkOfDetNeZero (A.val.map (Int.cast : ℤ → ℚ))
      (by rw [← Int.cast_det, A.property]; exact_mod_cast hn)

/-- The underlying matrix of `toGL hn A` is the entrywise cast of `A`. -/
@[simp]
theorem coe_toGL (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) :
    (toGL hn A : Matrix m m ℚ) = A.val.map (Int.cast : ℤ → ℚ) := (rfl)

/-- The determinant of `toGL hn A` is `n`. -/
theorem det_toGL (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) :
    (toGL hn A : Matrix m m ℚ).det = n := by
  rw [coe_toGL, ← Int.cast_det, A.property]

/-- `toGL hn` is injective: the cast `ℤ → ℚ` is. -/
theorem toGL_injective (hn : n ≠ 0) : Function.Injective (toGL (m := m) hn) := fun A B h ↦
  Subtype.ext <| Matrix.map_injective Int.cast_injective <| by
    simpa only [coe_toGL] using congrArg Units.val h

/-- Left multiplication by `g ∈ SL(m, ℤ)` becomes multiplication by its image in `GL(m, ℚ)`. -/
theorem toGL_smul (hn : n ≠ 0) (g : SpecialLinearGroup m ℤ) (A : FixedDetMatrix m ℤ n) :
    toGL hn (g • A) = SpecialLinearGroup.mapGL ℚ g * toGL hn A := by
  ext : 1
  simpa [smul_coe] using
    Matrix.map_mul (f := Int.castRingHom ℚ) (L := (g : Matrix m m ℤ)) (M := A.val)

/-! ### Integral matrices of nonzero determinant as real invertible matrices -/

/-- For `n ≠ 0`, an integral matrix of determinant `n` as an invertible real matrix. For `2 × 2`
matrices and `0 < n` this is the form in which it acts on the upper half-plane, by the Möbius
transformation `τ ↦ (a τ + b) / (c τ + d)`. -/
noncomputable def toGLReal (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) : GL m ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (toGL hn A)

/-- `toGLReal hn A` is the image of `toGL hn A` under `ℚ → ℝ`. -/
theorem toGLReal_eq_map_toGL (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) :
    toGLReal hn A = GeneralLinearGroup.map (algebraMap ℚ ℝ) (toGL hn A) := (rfl)

/-- The underlying matrix of `toGLReal hn A` is the entrywise cast of `A`. -/
@[simp]
theorem coe_toGLReal (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) :
    (toGLReal hn A : Matrix m m ℝ) = A.val.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [toGLReal_eq_map_toGL]

/-- The entries of `toGLReal hn A` are the casts of the entries of `A`. -/
theorem toGLReal_apply (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) (i j : m) :
    (toGLReal hn A : Matrix m m ℝ) i j = A.val i j := by
  rw [coe_toGLReal, map_apply]

/-- The determinant of `toGLReal hn A` is `n`. -/
theorem det_toGLReal (hn : n ≠ 0) (A : FixedDetMatrix m ℤ n) :
    ((toGLReal hn A).det : ℝ) = n := by
  rw [GeneralLinearGroup.val_det_apply, coe_toGLReal, ← Int.cast_det, A.property]

/-- Left multiplication by `g ∈ SL(m, ℤ)` becomes multiplication by its image in `GL(m, ℝ)`. -/
theorem toGLReal_smul (hn : n ≠ 0) (g : SpecialLinearGroup m ℤ) (A : FixedDetMatrix m ℤ n) :
    toGLReal hn (g • A) = SpecialLinearGroup.mapGL ℝ g * toGLReal hn A := by
  rw [toGLReal_eq_map_toGL, toGL_smul, map_mul, SpecialLinearGroup.map_mapGL,
    toGLReal_eq_map_toGL]

/-- Left multiplication by `SL(m, ℤ)` preserves and reflects primitivity: the greatest common
divisor of the entries is unchanged. -/
@[simp]
theorem isPrimitive_smul_iff (g : SpecialLinearGroup m ℤ) (A : FixedDetMatrix m ℤ n) :
    TauCeti.IsPrimitive (g • A).val ↔ TauCeti.IsPrimitive A.val := by
  rw [smul_coe, ← SpecialLinearGroup.coe_GL_coe_matrix, Units.isPrimitive_units_mul_iff]

end ToGL

/-! ### Primitive representatives -/

open scoped Classical in
/-- The primitive matrices among the upper-triangular representatives `reps n`: the matrices
`(a b; 0 d)` with `ad = n`, `0 < a`, `0 ≤ b < |d|` and `gcd(a, b, d) = 1`. For `n ≠ 0` they
represent the orbits of `SL(2, ℤ)` on the primitive integral matrices of determinant `n`. -/
noncomputable def primitiveReps (n : ℤ) : Finset (FixedDetMatrix (Fin 2) ℤ n) :=
  {A ∈ (reps n).toFinset | TauCeti.IsPrimitive A.val}

/-- A matrix lies in `primitiveReps n` exactly when it is a primitive matrix of `reps n`. -/
@[simp]
theorem mem_primitiveReps {A : FixedDetMatrix (Fin 2) ℤ n} :
    A ∈ primitiveReps n ↔ A ∈ reps n ∧ TauCeti.IsPrimitive A.val := by
  simp [primitiveReps]

/-- For `n ≠ 0`, every primitive matrix of determinant `n` can be moved into
`primitiveReps n` by left multiplication by `SL(2, ℤ)`. -/
theorem exists_smul_mem_primitiveReps (hn : n ≠ 0) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : TauCeti.IsPrimitive A.val) : ∃ g : SL(2, ℤ), g • A ∈ primitiveReps n := by
  obtain ⟨g, hg⟩ := exists_smul_mem_reps hn A
  exact ⟨g, mem_primitiveReps.2 ⟨hg, (isPrimitive_smul_iff g A).2 hA⟩⟩

/-! ### Scaling the upper-right residue of representatives -/

section ScaleRep

variable {m : ℕ}

open scoped Classical in
/-- A unit `u : (ZMod m)ˣ` acts on `reps m` (and `primitiveReps m`) by multiplying the upper-right
residue `b` of `(a b; 0 d)` by `u.val` modulo `d`, and fixes matrices outside `reps m`. -/
noncomputable def scaleRep (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    FixedDetMatrix (Fin 2) ℤ m :=
  if hA : A ∈ reps (m : ℤ) then
    (⟨!![A.val 0 0, ((u : ZMod m).val : ℤ) * A.val 0 1 % A.val 1 1; 0, A.val 1 1],
      by simpa [det_fin_two_of] using apply_zero_zero_mul_apply_one_one hA.1⟩ :
      FixedDetMatrix (Fin 2) ℤ m)
  else A

/-- For `A ∈ reps m`, `scaleRep u A` is `(a, (u.val * b) % d; 0, d)`. -/
theorem val_scaleRep_of_mem_reps (u : (ZMod m)ˣ) {A : FixedDetMatrix (Fin 2) ℤ m}
    (hA : A ∈ reps (m : ℤ)) :
    (scaleRep u A).val =
      !![A.val 0 0, ((u : ZMod m).val : ℤ) * A.val 0 1 % A.val 1 1; 0, A.val 1 1] := by
  classical
  exact congrArg Subtype.val (dite_eq_left hA : scaleRep u A = _)

/-- Outside `reps m`, `scaleRep u` acts as the identity. -/
theorem scaleRep_of_notMem_reps (u : (ZMod m)ˣ) {A : FixedDetMatrix (Fin 2) ℤ m}
    (hA : A ∉ reps (m : ℤ)) : scaleRep u A = A := by
  classical
  exact dite_eq_right hA

/-- `scaleRep u` preserves the `(0, 0)`-entry. -/
@[simp]
theorem scaleRep_apply_zero_zero (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    (scaleRep u A).val 0 0 = A.val 0 0 := by
  by_cases hA : A ∈ reps (m : ℤ)
  · simp [val_scaleRep_of_mem_reps u hA]
  · rw [scaleRep_of_notMem_reps u hA]

/-- `scaleRep u` preserves the `(1, 0)`-entry. -/
@[simp]
theorem scaleRep_apply_one_zero (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    (scaleRep u A).val 1 0 = A.val 1 0 := by
  by_cases hA : A ∈ reps (m : ℤ)
  · simp [val_scaleRep_of_mem_reps u hA, hA.1]
  · rw [scaleRep_of_notMem_reps u hA]

/-- `scaleRep u` preserves the `(1, 1)`-entry. -/
@[simp]
theorem scaleRep_apply_one_one (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    (scaleRep u A).val 1 1 = A.val 1 1 := by
  by_cases hA : A ∈ reps (m : ℤ)
  · simp [val_scaleRep_of_mem_reps u hA]
  · rw [scaleRep_of_notMem_reps u hA]

/-- For `A ∈ reps m`, `scaleRep u A` multiplies the upper-right entry `b` by `u.val` modulo `d`. -/
theorem scaleRep_apply_zero_one_of_mem_reps (u : (ZMod m)ˣ) {A : FixedDetMatrix (Fin 2) ℤ m}
    (hA : A ∈ reps (m : ℤ)) :
    (scaleRep u A).val 0 1 = ((u : ZMod m).val : ℤ) * A.val 0 1 % A.val 1 1 := by
  simp [val_scaleRep_of_mem_reps u hA]

/-- Natural-number form of `scaleRep_apply_zero_one_of_mem_reps`. -/
theorem natAbs_scaleRep_apply_zero_one_of_mem_reps (u : (ZMod m)ˣ)
    {A : FixedDetMatrix (Fin 2) ℤ m} (hA : A ∈ reps (m : ℤ)) :
    ((scaleRep u A).val 0 1).natAbs =
      (u : ZMod m).val * (A.val 0 1).natAbs % (A.val 1 1).natAbs := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp at hA
  have hd : 0 < A.val 1 1 :=
    pos_val_one_one_of_mem_reps (Int.natCast_pos.2 (Nat.pos_of_ne_zero hm0)) hA
  have hcast : ((u : ZMod m).val : ℤ) * A.val 0 1 % A.val 1 1 =
      (((u : ZMod m).val * (A.val 0 1).natAbs % (A.val 1 1).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_emod, Nat.cast_mul, Int.natAbs_of_nonneg hA.2.2.1, Int.natAbs_of_nonneg hd.le]
  rw [scaleRep_apply_zero_one_of_mem_reps u hA, hcast, Int.natAbs_natCast]

/-- `scaleRep u` preserves and reflects membership in `reps m`. -/
@[simp]
theorem scaleRep_mem_reps_iff (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    scaleRep u A ∈ reps (m : ℤ) ↔ A ∈ reps (m : ℤ) := by
  by_cases hA : A ∈ reps (m : ℤ)
  · refine iff_of_true ⟨?_, ?_, ?_, ?_⟩ hA
    · simp [hA.1]
    · simpa using hA.2.1
    · rw [scaleRep_apply_zero_one_of_mem_reps u hA]
      exact Int.emod_nonneg _ (apply_one_one_ne_zero_of_mem_reps hA)
    · rw [scaleRep_apply_zero_one_of_mem_reps u hA, scaleRep_apply_one_one,
        abs_of_nonneg (Int.emod_nonneg _ (apply_one_one_ne_zero_of_mem_reps hA))]
      exact Int.emod_lt_abs _ (apply_one_one_ne_zero_of_mem_reps hA)
  · rw [scaleRep_of_notMem_reps u hA]

/-- `scaleRep u` preserves and reflects primitivity. -/
@[simp]
theorem isPrimitive_scaleRep_iff (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    TauCeti.IsPrimitive (scaleRep u A).val ↔ TauCeti.IsPrimitive A.val := by
  by_cases hA : A ∈ reps (m : ℤ)
  · have hm_mul : (A.val 0 0).natAbs * (A.val 1 1).natAbs = m :=
      (natAbs_apply_zero_zero_mul_natAbs_apply_one_one hA.1).trans (Int.natAbs_natCast m)
    have hdvd_m : (A.val 0 0).gcd (A.val 1 1) ∣ m :=
      ((Int.gcd_dvd_natAbs_left _ _).trans (dvd_mul_right _ _)).trans hm_mul.dvd
    have hcop : IsCoprime ((u : ZMod m).val : ℤ) ((A.val 0 0).gcd (A.val 1 1) : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast, Int.natAbs_natCast]
      exact (ZMod.val_coe_unit_coprime u).coprime_dvd_right hdvd_m
    exact (congrArg TauCeti.IsPrimitive (val_scaleRep_of_mem_reps u hA)).to_iff.trans
      ((TauCeti.isPrimitive_upperTri_mul_emod_iff hcop).trans
        (congrArg TauCeti.IsPrimitive (val_eq_of_apply_one_zero_eq_zero hA.1).symm).to_iff)
  · rw [scaleRep_of_notMem_reps u hA]

/-- `scaleRep u` preserves and reflects membership in `primitiveReps m`. -/
theorem scaleRep_mem_primitiveReps_iff (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    scaleRep u A ∈ primitiveReps (m : ℤ) ↔ A ∈ primitiveReps (m : ℤ) := by
  simp [mem_primitiveReps]

/-- `1 : (ZMod m)ˣ` acts trivially under `scaleRep`. -/
@[simp]
theorem scaleRep_one (A : FixedDetMatrix (Fin 2) ℤ m) : scaleRep 1 A = A := by
  by_cases hA : A ∈ reps (m : ℤ)
  · rcases eq_or_ne m 0 with rfl | hm0
    · simp at hA
    have : NeZero m := ⟨hm0⟩
    have hd : 0 < A.val 1 1 :=
      pos_val_one_one_of_mem_reps (Int.natCast_pos.2 (Nat.pos_of_ne_zero hm0)) hA
    have hdvd : A.val 1 1 ∣ (m : ℤ) :=
      ⟨A.val 0 0, by rw [mul_comm, apply_zero_zero_mul_apply_one_one hA.1]⟩
    have hb_lt : A.val 0 1 < A.val 1 1 := by
      have := hA.2.2.2
      rwa [abs_of_nonneg hA.2.2.1, abs_of_pos hd] at this
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one,
      scaleRep_apply_zero_zero, scaleRep_apply_one_zero, scaleRep_apply_one_one]
    rw [scaleRep_apply_zero_one_of_mem_reps 1 hA, Units.val_one, ZMod.val_one_eq_one_mod,
      Int.natCast_emod, Nat.cast_one]
    calc (1 % (m : ℤ)) * A.val 0 1 % A.val 1 1
        = 1 * A.val 0 1 % A.val 1 1 :=
          (Int.ModEq.of_dvd hdvd (Int.mod_modEq 1 m)).mul_right _
      _ = A.val 0 1 := by rw [one_mul, Int.emod_eq_of_lt hA.2.2.1 hb_lt]
  · exact scaleRep_of_notMem_reps 1 hA

/-- `scaleRep` is compatible with multiplication in `(ZMod m)ˣ`. -/
theorem scaleRep_mul (u v : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    scaleRep (u * v) A = scaleRep u (scaleRep v A) := by
  by_cases hA : A ∈ reps (m : ℤ)
  · rcases eq_or_ne m 0 with rfl | hm0
    · simp at hA
    have : NeZero m := ⟨hm0⟩
    have hAv : scaleRep v A ∈ reps (m : ℤ) := (scaleRep_mem_reps_iff v A).2 hA
    have hdvd : A.val 1 1 ∣ (m : ℤ) :=
      ⟨A.val 0 0, by rw [mul_comm, apply_zero_zero_mul_apply_one_one hA.1]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one,
      scaleRep_apply_zero_zero, scaleRep_apply_one_zero, scaleRep_apply_one_one]
    rw [scaleRep_apply_zero_one_of_mem_reps (u * v) hA,
      scaleRep_apply_zero_one_of_mem_reps u hAv, scaleRep_apply_one_one,
      scaleRep_apply_zero_one_of_mem_reps v hA, Units.val_mul, ZMod.val_mul,
      Int.natCast_emod, Nat.cast_mul]
    calc (((u : ZMod m).val : ℤ) * (v : ZMod m).val % m) * A.val 0 1 % A.val 1 1
        = (((u : ZMod m).val : ℤ) * (v : ZMod m).val) * A.val 0 1 % A.val 1 1 :=
          (Int.ModEq.of_dvd hdvd (Int.mod_modEq _ m)).mul_right _
      _ = ((u : ZMod m).val : ℤ) * ((v : ZMod m).val * A.val 0 1) % A.val 1 1 := by
          rw [mul_assoc]
      _ = ((u : ZMod m).val : ℤ) *
            (((v : ZMod m).val : ℤ) * A.val 0 1 % A.val 1 1) % A.val 1 1 :=
          (Int.mod_modEq _ _).symm.mul_left _
  · rw [scaleRep_of_notMem_reps (u * v) hA, scaleRep_of_notMem_reps v hA,
      scaleRep_of_notMem_reps u hA]

/-- `scaleRep u⁻¹` is a left inverse to `scaleRep u`. -/
@[simp]
theorem scaleRep_inv_scaleRep (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    scaleRep u⁻¹ (scaleRep u A) = A := by
  rw [← scaleRep_mul, inv_mul_cancel, scaleRep_one]

/-- `scaleRep u⁻¹` is a right inverse to `scaleRep u`. -/
@[simp]
theorem scaleRep_scaleRep_inv (u : (ZMod m)ˣ) (A : FixedDetMatrix (Fin 2) ℤ m) :
    scaleRep u (scaleRep u⁻¹ A) = A := by
  rw [← scaleRep_mul, mul_inv_cancel, scaleRep_one]

/-- `scaleRep u` is injective. -/
theorem scaleRep_injective (u : (ZMod m)ˣ) : Function.Injective (scaleRep u) :=
  Function.LeftInverse.injective (scaleRep_inv_scaleRep u)

/-- `scaleRep u` permutes `primitiveReps m`. -/
@[simp]
theorem image_scaleRep_primitiveReps [DecidableEq (FixedDetMatrix (Fin 2) ℤ m)]
    (u : (ZMod m)ˣ) :
    (primitiveReps (m : ℤ)).image (scaleRep u) = primitiveReps (m : ℤ) := by
  refine Finset.eq_of_subset_of_card_le (fun B hB ↦ ?_)
    (Finset.card_image_of_injOn (scaleRep_injective u).injOn).ge
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
  exact (scaleRep_mem_primitiveReps_iff u A).2 hA

end ScaleRep

end FixedDetMatrices
