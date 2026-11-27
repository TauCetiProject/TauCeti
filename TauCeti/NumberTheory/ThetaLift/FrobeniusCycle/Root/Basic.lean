/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.RootSL
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Action
import TauCeti.Data.ZMod.Periodic

/-!
# Roots of a Frobenius cycle and the matrices that exchange them

Let `T` be a Frobenius cycle (`TauCeti.FrobeniusCycle`) with letters `s : ZMod N`. The group
`GL_k(W)` acts on polynomials over `R` in the variables `x (b, s)`, `b : Fin k`, by the twisted
action: `g` acts through the block diagonal matrix of its letter matrices `T.letterMatrix s g`, by
Tau Ceti's substitution of standard vectors `TauCeti.polynomialAction`
(`TauCeti.FrobeniusCycle.polynomialAction_letterMatrix_X`). This file sets up the data for the root
lemma (`TauCeti.FrobeniusCycle.defect_nonpos_of_extreme_term`): a root `(a, a')` and a
letter `i` (`TauCeti.FrobeniusCycle.RootAt`), the variables `X_s = ū_s` and `Y_s = u_s` of the
root at each letter, the orders of poles and zeros of the auxiliary polynomial, and the matrices
`!![0, 1; -1, ±r]` of `SL₂^{a,a'}(W)` that exchange the point at infinity with the finite points
of the projective line.

## Main definitions

* `TauCeti.FrobeniusCycle.RootAt`: a root `(a, a')` and a letter `i`.
* `TauCeti.FrobeniusCycle.RootAt.swapTransvection`: the matrix `!![0, 1; -1, ±r]` in the rows and
  columns `a`, `a'`.
* `TauCeti.FrobeniusCycle.RootAt.mainSubst`, `TauCeti.FrobeniusCycle.RootAt.crossSubst`: the two
  parts of the substitution that defines the auxiliary polynomial.

## Main results

* `TauCeti.FrobeniusCycle.RootAt.defectWeight_eq`: the defect weights in terms of the orders of
  zeros and poles.
* `TauCeti.FrobeniusCycle.RootAt.swapTransvection_mem_rootSL`: the exchanging matrices lie in
  `SL₂^{a,a'}(W)`.
* `TauCeti.FrobeniusCycle.RootAt.polynomialAction_swapTransvection_X`: their twisted action on the
  variables.

The definitions and lemmas are adapted from `New.FrobeniusCycle.RootAt` and its lemmas in the file
`New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open MvPolynomial Matrix Finsupp

namespace FrobeniusCycle

variable {W : Type*} [CommRing W] [IsLocalRing W] {R : Type*} [CommRing R] {N k : ℕ}

private theorem cast_q_pos (T : FrobeniusCycle W R N) : (0 : ℝ) < T.q :=
  Nat.cast_pos.2 (zero_lt_one.trans T.one_lt_q)

/-! ### A root and a letter -/

/-- A root `(a, a')` of `GL_k` and a letter `i`, the data at which a defect is measured. -/
structure RootAt (T : FrobeniusCycle W R N) (k : ℕ) where
  /-- The letter `i`. -/
  letter : ZMod N
  /-- The index `a`. -/
  fst : Fin k
  /-- The index `a'`. -/
  snd : Fin k
  /-- The two indices differ. -/
  ne : fst ≠ snd

namespace RootAt

variable {T : FrobeniusCycle W R N} (D : T.RootAt k) {s : ZMod N} {z : Fin k × ZMod N}

/-- The variable `X_s = ū_s`: index `a` at even and `a'` at odd letters `s`. -/
def varX (s : ZMod N) : Fin k × ZMod N := (T.negIndex D.fst D.snd s, s)

/-- The variable `Y_s = u_s`: index `a'` at even and `a` at odd letters `s`. -/
def varY (s : ZMod N) : Fin k × ZMod N := (T.posIndex D.fst D.snd s, s)

/-- The variables whose index is neither `a` nor `a'`. -/
def IsFixed (z : Fin k × ZMod N) : Prop := z.1 ≠ D.fst ∧ z.1 ≠ D.snd

/-- The permutation of the variables that swaps `X_s` and `Y_s` in each letter. -/
def swapVar (z : Fin k × ZMod N) : Fin k × ZMod N := (Equiv.swap D.fst D.snd z.1, z.2)

/-- The map of variables that sends `Y_i` to `X_i` and fixes the others. -/
def merge (z : Fin k × ZMod N) : Fin k × ZMod N :=
  if z = D.varY D.letter then D.varX D.letter else z

/-- The sign at `Y_s`: `-1` if `s` has the parity of `i` and `1` otherwise; it is `0` at the other
variables. -/
def sign (z : Fin k × ZMod N) : ℤ :=
  if z = D.varY z.2 then if T.isEven z.2 = T.isEven D.letter then -1 else 1 else 0

/-- The power `P_s = P ^ (s - i)`, with `s - i` read in `[0, N)`. -/
def frobPower (s : ZMod N) : ℕ := T.P ^ (s - D.letter).val

/-- The weights `q P_s` at `X_s` and `0` at the other variables: the weight of an exponent bounds
the degree in `t` of the auxiliary polynomial. -/
def poleOrder (z : Fin k × ZMod N) : ℕ := if z = D.varX z.2 then T.q * D.frobPower z.2 else 0

/-- The weights `q` at `Y_i`, `P_s` at `Y_s` for `s ≠ i`, and `0` at the other variables: the
weight of an exponent bounds from below the order of vanishing of the auxiliary polynomial at the
points `t = ι i r`, `r ∈ W`. -/
def zeroOrder (z : Fin k × ZMod N) : ℕ :=
  if z = D.varY z.2 then if z.2 = D.letter then T.q else D.frobPower z.2 else 0

/-- The sign of `Y_s` at both `X_s` and `Y_s` for `s ≠ i`, and `0` at the other variables. -/
def crossSign (z : Fin k × ZMod N) : R :=
  if z.2 = D.letter then 0 else D.sign z + D.sign (D.swapVar z)

theorem varX_def (s : ZMod N) : D.varX s = (T.negIndex D.fst D.snd s, s) := (rfl)

theorem varY_def (s : ZMod N) : D.varY s = (T.posIndex D.fst D.snd s, s) := (rfl)

theorem merge_def (z : Fin k × ZMod N) :
    D.merge z = if z = D.varY D.letter then D.varX D.letter else z :=
  (rfl)

theorem frobPower_def (s : ZMod N) : D.frobPower s = T.P ^ (s - D.letter).val := (rfl)

@[simp] theorem varX_snd : (D.varX s).2 = s := (rfl)

@[simp] theorem varY_snd : (D.varY s).2 = s := (rfl)

@[simp] theorem varX_ne_varY (s t : ZMod N) : D.varX s ≠ D.varY t := by
  have := D.ne
  grind [varX, varY, posIndex_eq_ite, negIndex_eq_ite]

@[simp] theorem varY_ne_varX (s t : ZMod N) : D.varY s ≠ D.varX t := (D.varX_ne_varY t s).symm

@[simp] theorem varY_inj {t : ZMod N} : D.varY s = D.varY t ↔ s = t :=
  ⟨congrArg Prod.snd, congrArg D.varY⟩

@[simp] theorem swapVar_snd : (D.swapVar z).2 = z.2 := (rfl)

@[simp] theorem swapVar_swapVar : D.swapVar (D.swapVar z) = z := by simp [swapVar]

@[simp] theorem swapVar_varX : D.swapVar (D.varX s) = D.varY s := by
  grind [swapVar, varX, varY, posIndex_eq_ite, negIndex_eq_ite]

@[simp] theorem swapVar_varY : D.swapVar (D.varY s) = D.varX s := by
  grind [swapVar, varX, varY, posIndex_eq_ite, negIndex_eq_ite]

/-- Every variable is `Y_i`, `X_i`, some `Y_s` or `X_s` with `s ≠ i`, or lies off the root. -/
theorem var_cases (z : Fin k × ZMod N) : z = D.varY D.letter ∨ z = D.varX D.letter ∨
    (∃ s : ZMod N, s ≠ D.letter ∧ (z = D.varY s ∨ z = D.varX s)) ∨ D.IsFixed z := by
  have h_letter : z = D.varY z.2 ∨ z = D.varX z.2 ∨ D.IsFixed z := by
    grind [varX, varY, posIndex_eq_ite, negIndex_eq_ite, IsFixed]
  grind

@[simp] theorem sign_varX : D.sign (D.varX s) = 0 := by simp [sign]

@[simp] theorem sign_varY_letter : D.sign (D.varY D.letter) = -1 := by simp [sign]

theorem sign_varY_eq_one_or_neg_one (s : ZMod N) :
    D.sign (D.varY s) = 1 ∨ D.sign (D.varY s) = -1 := by
  grind [sign, varY_snd]

@[simp] theorem frobPower_letter : D.frobPower D.letter = 1 := by simp [frobPower]

@[simp] theorem merge_varX : D.merge (D.varX s) = D.varX s := by simp [merge]

@[simp] theorem merge_varY :
    D.merge (D.varY s) = if s = D.letter then D.varX D.letter else D.varY s := by
  simp [merge]

@[simp] theorem poleOrder_varX : D.poleOrder (D.varX s) = T.q * D.frobPower s := by
  simp [poleOrder]

@[simp] theorem poleOrder_varY : D.poleOrder (D.varY s) = 0 := by simp [poleOrder]

@[simp] theorem zeroOrder_varX : D.zeroOrder (D.varX s) = 0 := by simp [zeroOrder]

@[simp] theorem zeroOrder_varY :
    D.zeroOrder (D.varY s) = if s = D.letter then T.q else D.frobPower s :=
  ite_eq_left rfl

@[simp] theorem crossSign_varX : D.crossSign (D.varX s) =
    if s = D.letter then 0 else (D.sign (D.varY s) : R) := by simp [crossSign]

@[simp] theorem crossSign_varY : D.crossSign (D.varY s) =
    if s = D.letter then 0 else (D.sign (D.varY s) : R) := by simp [crossSign]

namespace IsFixed

variable {D}

theorem ne_varX (hz : D.IsFixed z) (s : ZMod N) : z ≠ D.varX s := by
  grind [varX, negIndex_eq_ite, IsFixed]

theorem ne_varY (hz : D.IsFixed z) (s : ZMod N) : z ≠ D.varY s := by
  grind [varY, posIndex_eq_ite, IsFixed]

theorem swapVar_eq (hz : D.IsFixed z) : D.swapVar z = z := by grind [swapVar, IsFixed]

theorem merge_eq (hz : D.IsFixed z) : D.merge z = z := ite_eq_right (hz.ne_varY D.letter)

theorem sign_eq_zero (hz : D.IsFixed z) : D.sign z = 0 := ite_eq_right (hz.ne_varY z.2)

theorem poleOrder_eq_zero (hz : D.IsFixed z) : D.poleOrder z = 0 := ite_eq_right (hz.ne_varX z.2)

theorem zeroOrder_eq_zero (hz : D.IsFixed z) : D.zeroOrder z = 0 := ite_eq_right (hz.ne_varY z.2)

theorem crossSign_eq_zero (hz : D.IsFixed z) : D.crossSign z = 0 := by
  simp [crossSign, hz.swapVar_eq, hz.sign_eq_zero]

end IsFixed

/-- The defect weight of a variable `z` at the letter `i` along `(a, a')` is
`(D.zeroOrder z - D.poleOrder z / q) / (q - 1)`. -/
theorem defectWeight_eq (z : Fin k × ZMod N) :
    T.defectWeight D.fst D.snd D.letter z =
      (D.zeroOrder z - D.poleOrder z / T.q) / (T.q - 1) := by
  have := T.neZero
  have h_q' : (T.q : ℝ) = (T.P : ℝ) ^ N := by exact_mod_cast T.q_def
  have h_q0 : (T.q : ℝ) ≠ 0 := T.cast_q_pos.ne'
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · rw [zeroOrder_varY, poleOrder_varY, varY_def, T.defectWeight_posIndex, sub_right_comm,
      ZMod.one_add_val_sub_one]
    simp [h_q']
  · rw [zeroOrder_varX, poleOrder_varX, varX_def, T.defectWeight_negIndex D.ne]
    simp [frobPower_def, neg_div, h_q0]
  · rw [zeroOrder_varY, poleOrder_varY, varY_def, T.defectWeight_posIndex, sub_right_comm,
      ZMod.one_add_val_sub_one]
    simp [hs, frobPower_def, sub_eq_zero]
  · rw [zeroOrder_varX, poleOrder_varX, varX_def, T.defectWeight_negIndex D.ne]
    simp [frobPower_def, neg_div, h_q0]
  · obtain ⟨b, s⟩ := z
    obtain ⟨h_fst, h_snd⟩ := hz
    have h_pos : b ≠ T.posIndex D.fst D.snd s := by rw [posIndex_eq_ite]; split_ifs <;> assumption
    have h_neg : b ≠ T.negIndex D.fst D.snd s := by rw [negIndex_eq_ite]; split_ifs <;> assumption
    have hz : D.IsFixed (b, s) := ⟨h_fst, h_snd⟩
    simp [T.defectWeight_of_ne h_pos h_neg, hz.zeroOrder_eq_zero, hz.poleOrder_eq_zero]

/-- The diagonal signs `-1` at the index `a` and `1` at the other indices. -/
def signAt (D : T.RootAt k) : Fin k → Wˣ := Function.update 1 D.fst (-1)

/-- The matrix `!![0, 1; -1, x]` in the rows and columns `a`, `a'`, with `x = -r` if `i` is even
and `x = r` otherwise, written as a transposition times a transvection times the diagonal matrix
with `-1` at `a`. It relates the point at infinity of the projective line to the finite point with
the affine coordinate `ι i r`. -/
def swapTransvection (r : W) : GL (Fin k) W :=
  permutationGL (Equiv.swap D.fst D.snd) *
    transvectionUnit D.ne (if T.isEven D.letter then -r else r) * diagGL D.signAt

/-- The sign `-1` at the variables with index `a`, and `1` at the other variables. -/
def moveSign (z : Fin k × ZMod N) : ℤ := if z.1 = D.fst then -1 else 1

theorem signAt_inv : D.signAt⁻¹ = D.signAt := by
  funext b
  by_cases hb : b = D.fst <;> simp [signAt, hb]

/-- `D.swapTransvection r` lies in `SL₂(W)` placed in the rows and columns `a`, `a'`. -/
theorem swapTransvection_mem_rootSL (r : W) : D.swapTransvection r ∈ rootSL W D.fst D.snd := by
  have := D.ne
  set P : Set (Fin k) := {D.fst, D.snd}ᶜ
  have hP {i : Fin k} : i ∈ P ↔ i ≠ D.fst ∧ i ≠ D.snd := by simp [P]
  have h_perm : permutationGL (Equiv.swap D.fst D.snd) ∈ columnRowFixingSubgroup W P P := by
    refine mem_columnRowFixingSubgroup_iff.2 ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;>
      simp only [hP] at * <;>
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply,
        Equiv.swap_apply_def] <;> split_ifs <;> grind
  have h_tr (x : W) : transvectionUnit D.ne x ∈ columnRowFixingSubgroup W P P := by
    refine mem_columnRowFixingSubgroup_iff.2 ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;>
      simp only [hP] at * <;> simp [transvection, Matrix.single_apply] <;> grind
  have h_sign : diagGL D.signAt ∈ columnRowFixingSubgroup W P P := by
    refine mem_columnRowFixingSubgroup_iff.2 ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;>
      simp only [hP] at * <;> by_cases h : i = j <;> simp_all [signAt, Matrix.one_apply]
  rw [rootSL_def]
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem h_perm (h_tr _)) h_sign, ?_⟩
  -- The three factors have determinants `-1`, `1` and `-1`.
  have h_diag : GeneralLinearGroup.det (diagGL D.signAt) = -1 := by
    ext
    simp [signAt, Finset.prod_update_of_mem]
  have h_perm : GeneralLinearGroup.det (permutationGL (k := W) (Equiv.swap D.fst D.snd)) = -1 := by
    ext
    simp [Equiv.Perm.sign_swap D.ne]
  rw [MonoidHom.mem_ker, swapTransvection, map_mul, map_mul, h_diag, h_perm,
    det_transvectionUnit]
  simp

/-- The diagonal factor of `D.swapTransvection r` is its own inverse transpose, and multiplies the
variables with index `a` by `-1`. -/
theorem polynomialAction_signAt_X [NeZero N] (z : Fin k × ZMod N) :
    polynomialAction (blockDiagonal (T.letterMatrix · (diagGL D.signAt))) (X z) =
      D.moveSign z • X z := by
  have h_even : (if T.isEven z.2 then diagGL D.signAt
      else GeneralLinearGroup.inverseTranspose (diagGL D.signAt)) = diagGL D.signAt := by
    split_ifs <;> simp [← Pi.inv_def, signAt_inv]
  rw [polynomialAction_letterMatrix_X, h_even,
    Finset.sum_eq_single z.1 (fun b _ hb ↦ by simp [hb]) (by simp)]
  obtain ⟨b, s⟩ := z
  by_cases h : b = D.fst
  · subst h
    simp [signAt, moveSign]
  · simp [signAt, moveSign, h]

/-- The transposition of `a` and `a'` is its own inverse transpose, and exchanges `X_s` and
`Y_s`. -/
theorem polynomialAction_swap_X [NeZero N] (z : Fin k × ZMod N) :
    polynomialAction (blockDiagonal (T.letterMatrix · (permutationGL (Equiv.swap D.fst D.snd))))
      (X z) = X (D.swapVar z) := by
  have h_even : (if T.isEven z.2 then permutationGL (Equiv.swap D.fst D.snd)
      else GeneralLinearGroup.inverseTranspose (permutationGL (Equiv.swap D.fst D.snd))) =
        permutationGL (k := W) (Equiv.swap D.fst D.snd) := by
    split_ifs <;> simp
  rw [polynomialAction_letterMatrix_X, h_even]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, swapVar, Equiv.swap_apply_eq_iff]

/-- The transvection by `x` at `(a, a')` adds `± ι s x X_s` to `Y_s` and fixes the other
variables: the sign is `+` at even and `-` at odd letters. -/
theorem polynomialAction_transvectionUnit_X [NeZero N] (x : W) (z : Fin k × ZMod N) :
    polynomialAction (blockDiagonal (T.letterMatrix · (transvectionUnit D.ne x))) (X z) =
      X z + C (if z = D.varY z.2 then T.ι z.2 (if T.isEven z.2 then x else -x) else 0) *
        X (D.varX z.2) := by
  rw [polynomialAction_letterMatrix_X]
  obtain ⟨b, s⟩ := z
  have := D.ne
  cases h : T.isEven s <;>
    simp [h, transvection, Matrix.single_apply, Matrix.one_apply, Finset.sum_add_distrib, add_mul,
      varX, varY, apply_ite (T.ι s), apply_ite C, ite_and] <;>
    grind

/-- The action of the matrix `D.swapTransvection r` on the variable `z`. Up to the sign
`D.moveSign z`, which is `-1` if `z` has index `a` and `1` otherwise, it sends `X_s` to `Y_s`,
sends `Y_s` to `X_s + ε_s ι s r Y_s` and fixes the other variables. Here `ε_s = D.sign Y_s` is
`-1` if `s` has the parity of the letter `i` and `1` otherwise. -/
theorem polynomialAction_swapTransvection_X [NeZero N] (r : W) (z : Fin k × ZMod N) :
    polynomialAction (blockDiagonal (T.letterMatrix · (D.swapTransvection r))) (X z) =
      D.moveSign z • (X (D.swapVar z) + C (D.sign z * T.ι z.2 r) * X (D.varY z.2)) := by
  rw [swapTransvection, polynomialAction_letterMatrix_mul, polynomialAction_letterMatrix_mul,
    polynomialAction_signAt_X, map_zsmul, map_zsmul, polynomialAction_transvectionUnit_X, map_add,
    map_mul, algHom_C, algebraMap_eq, polynomialAction_swap_X, polynomialAction_swap_X,
    swapVar_varX]
  congr 3
  obtain ⟨b, s⟩ := z
  by_cases hz : (b, s) = D.varY s
  · rw [hz]
    cases h : T.isEven s <;> cases h' : T.isEven D.letter <;> simp [sign, h, h']
  · simp [hz, sign]

/-! ### Weights with bounded increments -/

/-- The weights `c` of the variables rise from `X_s` to `Y_s` by an amount in `[1 / 2, 1]`. -/
def HasBoundedIncrements (c : Fin k × ZMod N → ℝ) : Prop :=
  ∀ s : ZMod N, c (D.varY s) - c (D.varX s) ∈ Set.Icc 2⁻¹ 1

theorem hasBoundedIncrements_iff {c : Fin k × ZMod N → ℝ} :
    D.HasBoundedIncrements c ↔ ∀ s : ZMod N, c (D.varY s) - c (D.varX s) ∈ Set.Icc 2⁻¹ 1 :=
  Iff.rfl

/-- The slope `ρ = (c Y_i - c X_i) / q` of weights `c` of the variables. The variable `t` of the
auxiliary polynomial weighs `-ρ` in the expansion at infinity and `ρ` in the expansion at a finite
point. -/
noncomputable def slope (c : Fin k × ZMod N → ℝ) : ℝ :=
  (c (D.varY D.letter) - c (D.varX D.letter)) / T.q

theorem slope_def (c : Fin k × ZMod N → ℝ) :
    D.slope c = (c (D.varY D.letter) - c (D.varX D.letter)) / T.q :=
  (rfl)

variable {D} {c : Fin k × ZMod N → ℝ}

/-- The step of weights with bounded increments at the letter `s`. -/
theorem HasBoundedIncrements.sub_mem_Icc (hc : D.HasBoundedIncrements c) (s : ZMod N) :
    c (D.varY s) - c (D.varX s) ∈ Set.Icc 2⁻¹ 1 :=
  hc s

theorem q_mul_slope : T.q * D.slope c = c (D.varY D.letter) - c (D.varX D.letter) := by
  rw [slope_def, mul_div_cancel₀ _ T.cast_q_pos.ne']

theorem HasBoundedIncrements.slope_pos (hc : D.HasBoundedIncrements c) : 0 < D.slope c := by
  rw [slope_def]
  exact div_pos (by linarith [(hc D.letter).1]) T.cast_q_pos

/-- If the steps of `c` lie in `[1 / 2, 1]`, then `P_s` times the slope is at most `1 / 5`, because
`5 P_s ≤ q`. -/
theorem HasBoundedIncrements.frobPower_mul_slope_le (hc : D.HasBoundedIncrements c)
    (s : ZMod N) : D.frobPower s * D.slope c ≤ 1 / 5 := by
  have h_power : (5 * D.frobPower s : ℝ) ≤ T.q := by
    rw [frobPower_def]
    exact_mod_cast T.five_mul_P_pow_le_q (s - D.letter)
  have h_step : T.q * D.slope c ≤ 1 := q_mul_slope.trans_le (hc D.letter).2
  nlinarith [hc.slope_pos]

/-- If the steps of `c` lie in `[1 / 2, 1]` and `s ≠ i`, then `q P_s` times the slope is at least
`2`, because `P_s ≥ 5`. -/
theorem HasBoundedIncrements.two_le_q_mul_frobPower_mul_slope {s : ZMod N}
    (hc : D.HasBoundedIncrements c) (hs : s ≠ D.letter) :
    2 ≤ T.q * D.frobPower s * D.slope c := by
  have := T.neZero
  have h_power : (5 : ℝ) ≤ D.frobPower s := by
    rw [frobPower_def]
    exact_mod_cast T.five_le_P.trans (Nat.le_self_pow (by simpa [sub_eq_zero] using hs) _)
  have h_step : (2⁻¹ : ℝ) ≤ T.q * D.slope c := (hc D.letter).1.trans_eq q_mul_slope.symm
  nlinarith

/-! ### The auxiliary polynomial -/

variable (D) in
/-- The main part of the substitution, with a new variable `t = X ()`: `Y_i ↦ X_i`,
`X_s ↦ t ^ (q P_s) X_s`, and the other variables are fixed. -/
noncomputable def mainSubst (z : Fin k × ZMod N) :
    MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R) :=
  C (monomial (single () (D.poleOrder z)) 1) * X (D.merge z)

theorem mainSubst_apply (z : Fin k × ZMod N) :
    D.mainSubst z = C (monomial (single () (D.poleOrder z)) 1) * X (D.merge z) :=
  (rfl)

variable (D) in
/-- The cross terms: for `s ≠ i`, `Y_s ↦ ε_s X_s` and `X_s ↦ ε_s t ^ P_s Y_s`, where `ε_s` is the
sign `D.sign` at `Y_s`; the other variables go to `0`. The substitution that defines the auxiliary
polynomial is `D.mainSubst - D.crossSubst`. -/
noncomputable def crossSubst (z : Fin k × ZMod N) :
    MvPolynomial (Fin k × ZMod N) (MvPolynomial Unit R) :=
  C (monomial (single () (D.zeroOrder (D.swapVar z))) (D.crossSign z)) * X (D.swapVar z)

theorem crossSubst_apply (z : Fin k × ZMod N) :
    D.crossSubst z =
      C (monomial (single () (D.zeroOrder (D.swapVar z))) (D.crossSign z)) * X (D.swapVar z) :=
  (rfl)

end RootAt

end FrobeniusCycle

end TauCeti
