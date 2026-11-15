/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclotomic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import TauCeti.GroupTheory.Perm.Coxeter

/-!
# Coxeter elements of the classical Cartan matrices

This file computes the order and the characteristic polynomial of the Coxeter element
`c = s₁ s₂ ⋯ sₙ` (`Matrix.coxeterElement`) of each classical Cartan matrix `CartanMatrix.A n`,
`CartanMatrix.B n`, `CartanMatrix.C n`, and `CartanMatrix.D n`, together with the one-degenerate
order of the Bourbaki node numbering `List.finRange n`:

| type | rank condition | `orderOf` | `charpoly` |
|---|---|---|---|
| `Aₙ` | `0 < n` (`charpoly` for all `n`) | `n + 1` | `∑ k < n + 1, X ^ k` |
| `Bₙ` | `0 < n` | `2 * n` | `X ^ n + 1` |
| `Cₙ` | `0 < n` | `2 * n` | `X ^ n + 1` |
| `Dₙ` | `2 ≤ n` | `2 * (n - 1)` | `(X ^ (n - 1) + 1) * (X + 1)` |

Rather than expanding `c` entry by entry, each family is intertwined with its coordinate model:

* In **type `Aₙ`**, the unit lower-triangular basis `ε₀ - ε₁, …, εₙ₋₁ - εₙ, εₙ` of `ℤⁿ⁺¹` turns
  the adjacent transpositions into upper block-triangular matrices with `(1, 1)` block
  `reflMatrix (CartanMatrix.A n) i` and `(2, 2)` block `1`. Their product is `finRotate (n + 1)`
  (`TauCeti.permCoxeterSystem_wordProd_finRange`), whose characteristic polynomial `X ^ (n + 1) - 1`
  factors as `(∑ k < n + 1, X ^ k) * (X - 1)`.
* In **type `Bₙ`** (`n = m + 1`), the same unimodular matrix `ε₀ - ε₁, …, εₘ₋₁ - εₘ, εₘ` conjugates
  `coxB (m + 1)` over `ℤ` to the negacyclic shift `ε₀ ↦ ε₁ ↦ ⋯ ↦ εₘ ↦ -ε₀`, which satisfies
  `N ^ n = -1` and has cyclic vector `ε₀`, giving `charpoly = X ^ n + 1` and `orderOf = 2 * n`.
* **Type `Cₙ`** is intertwined with type `Bₙ` by `diagonal (1, …, 1, 2)`, so `coxC n` and `coxB n`
  have the same order and characteristic polynomial for every `n`.
* In **type `Dₙ`** (`n = m + 2`), the root columns `ε₀ - ε₁, …, εₘ - εₘ₊₁, εₘ + εₘ₊₁` have integer
  quasi-inverse of determinant factor `2` and intertwine `coxD (m + 2)` with the block-diagonal
  matrix `fromBlocks (negShift (m + 1)) 0 0 (-1)` for all `2 ≤ n` (including the reducible `D₂` and
  the `A₃` coincidence `D₃`).

## Main definitions

* `TauCeti.Coxeter.coxA`, `coxB`, `coxC`, `coxD`: the Coxeter elements of the classical Cartan
  matrices.

## Main results

* `TauCeti.Coxeter.isOneDegenerateOrder_A`, `_B`, `_C`, `_D`: `List.finRange n` is a one-degenerate
  order of each classical diagram.
* `TauCeti.Coxeter.orderOf_coxA`, `orderOf_coxB`, `orderOf_coxC`, `orderOf_coxD`: the orders of the
  classical Coxeter elements.
* `TauCeti.Coxeter.charpoly_coxA`, `charpoly_coxB`, `charpoly_coxC`, `charpoly_coxD`: their
  characteristic polynomials over `ℤ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### Coxeter elements of the classical Cartan matrices -/

/-- The Coxeter element of `CartanMatrix.A n`. -/
@[expose] def coxA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.A n)

/-- The Coxeter element of `CartanMatrix.B n`. -/
@[expose] def coxB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.B n)

/-- The Coxeter element of `CartanMatrix.C n`. -/
@[expose] def coxC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.C n)

/-- The Coxeter element of `CartanMatrix.D n`. -/
@[expose] def coxD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.D n)

/-! ### One-degenerate orders of the classical diagrams -/

/-- If every index has at most one strictly smaller neighbour, then `List.finRange n` is a
one-degenerate order. -/
private theorem isOneDegenerateOrder_finRange {n : ℕ} {adj : Fin n → Fin n → Prop}
    (h : ∀ z x y : Fin n, x < z → y < z → adj z x → adj z y → x = y) :
    List.IsOneDegenerateOrder adj (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hp := List.pairwise_lt_finRange n
  rw [hS, List.pairwise_append] at hp
  exact h z x y (hp.2.2 x hx z List.mem_cons_self) (hp.2.2 y hy z List.mem_cons_self) hzx hzy

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.A n`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.B n`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.C n`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.D n`. -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  have _ := z.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-! ### Shared matrix helpers: intertwining, unimodular difference basis, and shifts -/

private theorem list_prod_mul_eq_mul_list_prod {α : Type*} {m k : ℕ} (L : List α)
    (U : Matrix (Fin m) (Fin k) ℤ) (f : α → Matrix (Fin m) (Fin m) ℤ)
    (g : α → Matrix (Fin k) (Fin k) ℤ) (h : ∀ a ∈ L, f a * U = U * g a) :
    (L.map f).prod * U = U * (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    calc ((a :: t).map f).prod * U
        = f a * ((t.map f).prod * U) := by rw [List.map_cons, List.prod_cons, Matrix.mul_assoc]
      _ = f a * (U * (t.map g).prod) := by rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
      _ = (f a * U) * (t.map g).prod := (Matrix.mul_assoc _ _ _).symm
      _ = U * ((a :: t).map g).prod := by
          rw [h a List.mem_cons_self, List.map_cons, List.prod_cons, Matrix.mul_assoc]

private theorem pow_mul_eq_mul_pow {m k : ℕ} {U : Matrix (Fin m) (Fin k) ℤ}
    {S : Matrix (Fin m) (Fin m) ℤ} {T : Matrix (Fin k) (Fin k) ℤ} (h : S * U = U * T) (r : ℕ) :
    S ^ r * U = U * T ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc S ^ (r + 1) * U = S ^ r * (S * U) := by rw [pow_succ, Matrix.mul_assoc]
      _ = (S ^ r * U) * T := by rw [h, Matrix.mul_assoc]
      _ = U * T ^ (r + 1) := by rw [ih, Matrix.mul_assoc, ← pow_succ]

private theorem mul_reflMatrix_apply {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℤ)
    (A : Matrix (Fin k) (Fin k) ℤ) (i : Fin k) (p : Fin m) (q : Fin k) :
    (M * reflMatrix A i) p q = M p q - M p i * A q i := by
  simp [Matrix.mul_apply, reflMatrix_apply, mul_sub, mul_ite]

private theorem finRange_succ_eq_map_castSucc_append_last (m : ℕ) :
    List.finRange (m + 1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by simpa using h₁)) with hi | rfl
  · have hlen : i < ((List.finRange m).map Fin.castSucc).length := by simp [hi]
    rw [List.getElem_append_left hlen]
    simp
  · have hlen : ((List.finRange i).map Fin.castSucc).length ≤ i := by simp
    rw [List.getElem_append_right hlen]
    ext
    simp

private theorem transposition_symm {m : ℕ} (i : Fin m) :
    (BraidGroup.transposition (n := m + 1) i).symm = BraidGroup.transposition (n := m + 1) i := by
  rw [← Equiv.Perm.inv_def, inv_eq_iff_mul_eq_one]
  exact BraidGroup.transposition_mul_self (n := m + 1) i

private theorem permCoxeterSystem_wordProd_finRange_succ (m : ℕ) :
    (permCoxeterSystem (m + 1)).wordProd (List.finRange m) = finRotate (m + 1) :=
  permCoxeterSystem_wordProd_finRange (n := m + 1)

/-- The permutation matrix sending standard basis column `ε_q` to `ε_{σ q}`. -/
private def permMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun p q => if p = σ q then 1 else 0

private theorem permMatrix_one (m : ℕ) : permMatrix (1 : Equiv.Perm (Fin m)) = 1 := by
  ext p q
  simp only [permMatrix, Matrix.of_apply, Matrix.one_apply, Equiv.Perm.one_apply]
  split_ifs <;> simp_all

private theorem permMatrix_mul {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permMatrix (σ * τ) = permMatrix σ * permMatrix τ := by
  ext p q
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ q)]
  · simp only [permMatrix, Matrix.of_apply, Equiv.Perm.mul_apply, ↓reduceIte, mul_one]
    split_ifs <;> simp_all
  · intro r _ hr
    simp [permMatrix, hr]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem permMatrix_list_prod {m : ℕ} (L : List (Equiv.Perm (Fin m))) :
    permMatrix L.prod = (L.map permMatrix).prod := by
  induction L with
  | nil => simp [permMatrix_one]
  | cons σ t ih => rw [List.prod_cons, List.map_cons, List.prod_cons, permMatrix_mul, ih]

private theorem permMatrix_pow {m : ℕ} (σ : Equiv.Perm (Fin m)) (k : ℕ) :
    permMatrix σ ^ k = permMatrix (σ ^ k) := by
  calc permMatrix σ ^ k = ((List.replicate k σ).map permMatrix).prod := by simp
    _ = permMatrix (List.replicate k σ).prod := (permMatrix_list_prod _).symm
    _ = permMatrix (σ ^ k) := by rw [List.prod_replicate]

private theorem permMatrix_mul_apply {m k : ℕ} (σ : Equiv.Perm (Fin m))
    (M : Matrix (Fin m) (Fin k) ℤ) (p : Fin m) (q : Fin k) :
    (permMatrix σ * M) p q = M (σ.symm p) q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm p)]
  · simp [permMatrix]
  · intro r _ hr
    have hp : p ≠ σ r := fun h => hr (by simp [h])
    simp [permMatrix, hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Unit lower-triangular basis `ε₀ - ε₁, …, ε_{m-2} - ε_{m-1}, ε_{m-1}` of `ℤᵐ`. -/
private def diffBasis (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun p q => if p = q then 1 else if p.val = q.val + 1 then -1 else 0

/-- Explicit inverse of `diffBasis m`: lower-triangular matrix of ones. -/
private def sumBasis (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun r p => if p.val ≤ r.val then 1 else 0

private theorem sumBasis_mul_diffBasis (m : ℕ) : sumBasis m * diffBasis m = 1 := by
  ext r q
  rw [Matrix.mul_apply]
  rcases lt_or_ge (q.val + 1) m with hq | hq
  · let q' : Fin m := ⟨q.val + 1, hq⟩
    have hq'v : q'.val = q.val + 1 := rfl
    have hqq' : q ≠ q' := fun h => by have := congrArg Fin.val h; omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hqq'.symm, Finset.mem_univ q'⟩),
      Finset.sum_eq_zero]
    · simp only [sumBasis, diffBasis, Matrix.of_apply, Matrix.one_apply, ↓reduceIte,
        Fin.ext_iff, hq'v]
      split_ifs <;> omega
    · intro p hp
      have hp1 : p ≠ q := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
      have hp2 : p.val ≠ q.val + 1 := fun h => (Finset.mem_erase.mp hp).1 (Fin.ext h)
      simp [diffBasis, hp1, hp2]
  · rw [Finset.sum_eq_single q]
    · have _ := r.isLt
      simp only [sumBasis, diffBasis, Matrix.of_apply, Matrix.one_apply, ↓reduceIte, Fin.ext_iff]
      split_ifs <;> omega
    · intro p _ hp
      have hp2 : p.val ≠ q.val + 1 := by have := p.isLt; omega
      simp [diffBasis, hp, hp2]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem diffBasis_mul_sumBasis (m : ℕ) : diffBasis m * sumBasis m = 1 :=
  mul_eq_one_comm.mp (sumBasis_mul_diffBasis m)

/-- Equivalence induced on `Matrix (Fin m) (Fin m) ℤ` by conjugation with `diffBasis m`. -/
private def conjDiffBasis (m : ℕ) (M : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  sumBasis m * M * diffBasis m

private theorem charpoly_conjDiffBasis {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) :
    (conjDiffBasis m M).charpoly = M.charpoly := by
  rw [conjDiffBasis, Matrix.charpoly_mul_comm, ← mul_assoc, diffBasis_mul_sumBasis, one_mul]

/-! ### Cyclic and negacyclic shift matrices -/

/-- If every `M ^ i *ᵥ e₀` (`i < m`) is `eᵢ`, then no nonzero polynomial of degree `< m`
annihilates `M`. -/
private theorem eq_zero_of_natDegree_lt_of_aeval_eq_zero {m : ℕ} (hm : 0 < m)
    {M : Matrix (Fin m) (Fin m) ℤ}
    (hcyc : ∀ i : Fin m, (M ^ i.val) *ᵥ Pi.single ⟨0, hm⟩ 1 = Pi.single i 1)
    {q : ℤ[X]} (hq : q.natDegree < m) (h0 : aeval M q = 0) : q = 0 := by
  ext j
  rw [coeff_zero]
  rcases lt_or_ge j m with hj | hj
  · have hv := congrFun (congrArg (· *ᵥ Pi.single ⟨0, hm⟩ 1) h0) ⟨j, hj⟩
    rw [aeval_eq_sum_range' hq, Matrix.sum_mulVec] at hv
    simp only [Matrix.zero_mulVec, Pi.zero_apply, Finset.sum_apply, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul] at hv
    rw [Finset.sum_eq_single j] at hv
    · have hc := congrFun (hcyc ⟨j, hj⟩) ⟨j, hj⟩
      simp only [Pi.single_eq_same] at hc
      simpa [hc] using hv
    · intro i hi hij
      have hi' : i < m := Finset.mem_range.mp hi
      have hc := congrFun (hcyc ⟨i, hi'⟩) ⟨j, hj⟩
      have hne : (⟨j, hj⟩ : Fin m) ≠ ⟨i, hi'⟩ := fun h => hij (congrArg Fin.val h).symm
      simp [hc, Pi.single_eq_of_ne hne]
    · intro h
      exact absurd (Finset.mem_range.mpr hj) h
  · exact coeff_eq_zero_of_natDegree_lt (hq.trans_le hj)

private theorem finRotate_pow_apply {m : ℕ} (hm : 0 < m) (k : ℕ) (q : Fin m) :
    ((finRotate m ^ k) q).val = (q.val + k) % m := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  induction k generalizing q with
  | zero => simp [Nat.mod_eq_of_lt q.isLt]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_finRotate, ih]
    have hmod : (q.val + k) % (d + 1) < d + 1 := Nat.mod_lt _ (by omega)
    split_ifs with hlast
    · have heq : (q.val + k) % (d + 1) = d := by
        simpa [Fin.val_last, ih] using congrArg Fin.val hlast
      have hdiv : d + 1 ∣ q.val + (k + 1) := by
        rw [Nat.dvd_iff_mod_eq_zero, show q.val + (k + 1) = (q.val + k) + 1 by omega,
          ← Nat.mod_add_mod, heq]
        simp
      exact (Nat.mod_eq_zero_of_dvd hdiv).symm
    · have hne : (q.val + k) % (d + 1) ≠ d := fun h =>
        hlast (Fin.ext (by simpa [Fin.val_last, ih] using h))
      have hlt : (q.val + k) % (d + 1) + 1 < d + 1 := by omega
      have hadd : q.val + (k + 1) = (q.val + k) + 1 := by omega
      rw [hadd, ← Nat.mod_add_mod (q.val + k) (d + 1) 1, Nat.mod_eq_of_lt hlt]

private theorem charpoly_permMatrix_finRotate {m : ℕ} (hm : 0 < m) :
    (permMatrix (finRotate m)).charpoly = X ^ m - 1 := by
  set M := permMatrix (finRotate m)
  have hpow : M ^ m = 1 := by
    have hrot : finRotate m ^ m = 1 := by
      ext q
      rw [Equiv.Perm.one_apply, finRotate_pow_apply hm, Nat.add_mod_right,
        Nat.mod_eq_of_lt q.isLt]
    rw [permMatrix_pow, hrot, permMatrix_one]
  have hcyc : ∀ i : Fin m, (M ^ i.val) *ᵥ Pi.single ⟨0, hm⟩ 1 = Pi.single i 1 := by
    intro i
    rw [permMatrix_pow]
    ext p
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨0, hm⟩]
    · have h0 : (finRotate m ^ i.val) ⟨0, hm⟩ = i :=
        Fin.ext (by simp [finRotate_pow_apply hm, Nat.mod_eq_of_lt i.isLt])
      simp [permMatrix, h0, Pi.single_apply]
    · intro r _ hr
      simp [Pi.single_eq_of_ne hr]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_of_aeval_eq_zero hm hcyc ?_ ?_
  · exact IsMonicOfDegree.natDegree_sub_lt hm.ne'
      ⟨by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], Matrix.charpoly_monic _⟩
      ((isMonicOfDegree_X_pow ℤ m).sub (by simpa using hm))
  · simp [Matrix.aeval_self_charpoly, hpow]

/-- Negacyclic shift matrix on `Fin n`: `ε₀ ↦ ε₁ ↦ ⋯ ↦ ε_{n-1} ↦ -ε₀`. -/
private def negShift (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun p q =>
    if q.val + 1 < n then (if p.val = q.val + 1 then 1 else 0)
    else (if p.val = 0 then -1 else 0)

private theorem negShift_mulVec_single {n : ℕ} (hn : 0 < n) (q : Fin n) :
    negShift n *ᵥ Pi.single q 1 =
      (if q.val + 1 < n then (1 : ℤ) else -1) •
        Pi.single ⟨(q.val + 1) % n, Nat.mod_lt _ hn⟩ 1 := by
  ext p
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single q]
  · by_cases hlt : q.val + 1 < n
    · simp [negShift, hlt, Nat.mod_eq_of_lt hlt, Pi.single_apply, Fin.ext_iff]
    · have hqn : q.val + 1 = n := by have := q.isLt; omega
      simp [negShift, hqn, Pi.single_apply, Fin.ext_iff]
  · intro r _ hr
    simp [Pi.single_eq_of_ne hr]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem negShift_pow_mulVec_single {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) (q : Fin n) :
    (negShift n ^ k) *ᵥ Pi.single q 1 =
      (if q.val + k < n then (1 : ℤ) else -1) •
        Pi.single ⟨(q.val + k) % n, Nat.mod_lt _ hn⟩ 1 := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec]
    ext p
    simp [q.isLt, Nat.mod_eq_of_lt q.isLt]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega), Matrix.mulVec_smul,
      negShift_mulVec_single hn]
    have hq := q.isLt
    have hmod : ((q.val + k) % n + 1) % n = (q.val + (k + 1)) % n := by
      have hadd : q.val + (k + 1) = (q.val + k) + 1 := by omega
      rw [hadd, ← Nat.mod_add_mod (q.val + k) n 1]
    ext p
    simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, smul_eq_mul, hmod]
    by_cases h1 : q.val + k < n
    · have hrem : (q.val + k) % n = q.val + k := Nat.mod_eq_of_lt h1
      simp only [hrem]
      split_ifs <;> omega
    · have hge : n ≤ q.val + k := by omega
      have hlt2 : q.val + k - n < n := by omega
      have hrem : (q.val + k) % n = q.val + k - n :=
        (Nat.mod_eq_sub_mod hge).trans (Nat.mod_eq_of_lt hlt2)
      simp only [hrem]
      split_ifs <;> omega

private theorem negShift_pow_self {n : ℕ} (hn : 0 < n) : negShift n ^ n = -1 := by
  ext p q
  have hv := congrFun (negShift_pow_mulVec_single hn le_rfl q) p
  have hcol : (negShift n ^ n *ᵥ Pi.single q 1) p = (negShift n ^ n) p q := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single q]
    · simp
    · intro r _ hr; simp [Pi.single_eq_of_ne hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcol] at hv
  have hnot : ¬ q.val + n < n := by omega
  simp only [ite_eq_right hnot, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
    Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt, smul_eq_mul, Matrix.neg_apply, Matrix.one_apply]
    at hv ⊢
  split_ifs at hv ⊢ <;> omega

private theorem charpoly_negShift {n : ℕ} (hn : 0 < n) :
    (negShift n).charpoly = X ^ n + 1 := by
  have hcyc : ∀ i : Fin n, (negShift n ^ i.val) *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single i 1 := by
    intro i
    rw [negShift_pow_mulVec_single hn i.isLt.le]
    simp [i.isLt, Nat.mod_eq_of_lt i.isLt]
  have hmon : (X ^ n + 1 : ℤ[X]).IsMonicOfDegree n :=
    (isMonicOfDegree_iff _ _).mpr
      ⟨(natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le n) (by simp)),
        by simp [coeff_one, hn.ne']⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_of_aeval_eq_zero hn hcyc ?_ ?_
  · exact IsMonicOfDegree.natDegree_sub_lt hn.ne'
      ⟨by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], Matrix.charpoly_monic _⟩ hmon
  · simp [Matrix.aeval_self_charpoly, negShift_pow_self hn]

private theorem orderOf_negShift {n : ℕ} (hn : 0 < n) : orderOf (negShift n) = 2 * n := by
  refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun m hm hpos hm1 => ?_⟩
  · rw [mul_comm, pow_mul, negShift_pow_self hn, neg_one_sq]
  · have hv := congrFun (congrArg (· *ᵥ Pi.single ⟨0, hn⟩ 1) hm1) ⟨0, hn⟩
    simp only [Matrix.one_mulVec, Pi.single_eq_same] at hv
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · have h0 := congrFun (negShift_pow_mulVec_single hn hlt.le ⟨0, hn⟩) ⟨0, hn⟩
      simp only [zero_add, ite_eq_left hlt, one_smul, Pi.single_apply, Fin.ext_iff,
        Nat.mod_eq_of_lt hlt] at h0
      omega
    · rw [negShift_pow_self hn] at hv
      simp at hv
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
      have hklt : k < n := by omega
      rw [pow_add, negShift_pow_self hn, neg_one_mul, Matrix.neg_mulVec, Pi.neg_apply] at hv
      have h0 := congrFun (negShift_pow_mulVec_single hn hklt.le ⟨0, hn⟩) ⟨0, hn⟩
      simp only [zero_add, ite_eq_left hklt, one_smul, Pi.single_apply, Fin.ext_iff,
        Nat.mod_eq_of_lt hklt] at h0
      omega

/-! ### Type `A` -/

/-- Upper block-triangular matrix on `Fin (n + 1)` extending `reflMatrix (CartanMatrix.A n) i`. -/
private def extReflA {n : ℕ} (i : Fin n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  reindex (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1))
    (fromBlocks (reflMatrix (CartanMatrix.A n) i)
      (Matrix.of fun k _ => if k = i ∧ i.val + 1 = n then 1 else 0) 0 1)

private theorem permMatrix_transposition_mul_diffBasis {n : ℕ} (i : Fin n) :
    permMatrix (BraidGroup.transposition (n := n + 1) i) * diffBasis (n + 1) =
      diffBasis (n + 1) * extReflA i := by
  ext p q
  rw [permMatrix_mul_apply, transposition_symm]
  have hp := p.isLt
  have hq := q.isLt
  have hi := i.isLt
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hq) with hqlt | hqlast
  · let jq : Fin n := ⟨q.val, hqlt⟩
    have hjq : jq.val = q.val := rfl
    have hqe : q = finSumFinEquiv (m := n) (n := 1) (Sum.inl jq) := Fin.ext rfl
    rw [Matrix.mul_apply]
    have hsum : ∑ r : Fin (n + 1), diffBasis (n + 1) p r * extReflA i r q =
        diffBasis (n + 1) p (finSumFinEquiv (Sum.inl jq)) -
          diffBasis (n + 1) p (finSumFinEquiv (Sum.inl i)) * CartanMatrix.A n jq i := by
      rw [← (finSumFinEquiv (m := n) (n := 1)).sum_comp]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, hqe, extReflA,
        reindex_apply, submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, add_zero, reflMatrix_apply, mul_sub,
        mul_ite, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hsum, ← hqe]
    simp only [diffBasis, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, finSumFinEquiv_apply_left,
      Fin.val_castAdd, BraidGroup.val_transposition_apply, hjq]
    split_ifs <;> omega
  · have hqe : q = finSumFinEquiv (m := n) (n := 1) (Sum.inr 0) := Fin.ext (by simpa using hqlast)
    rw [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := 1)).sum_comp]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, Fin.default_eq_zero, hqe, extReflA,
      reindex_apply, submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₂,
      fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply, ↓reduceIte, mul_one, mul_ite,
      mul_zero]
    have h1 : (∑ x : Fin n,
        if x = i ∧ i.val + 1 = n then diffBasis (n + 1) p (finSumFinEquiv (Sum.inl x)) else 0) =
        if i.val + 1 = n then diffBasis (n + 1) p (finSumFinEquiv (Sum.inl i)) else 0 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [hki]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, ← hqe]
    simp only [diffBasis, Matrix.of_apply, Fin.ext_iff, finSumFinEquiv_apply_left,
      Fin.val_castAdd, BraidGroup.val_transposition_apply, hqlast]
    split_ifs <;> omega

private theorem list_prod_extReflA {n : ℕ} (L : List (Fin n)) :
    ∃ B : Matrix (Fin n) (Fin 1) ℤ,
      ((L.map extReflA).prod).submatrix
          (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)) =
        fromBlocks ((L.map (reflMatrix (CartanMatrix.A n))).prod) B 0 1 := by
  induction L with
  | nil =>
    refine ⟨0, ?_⟩
    ext (i | i) (j | j)
    · simp [Matrix.one_apply]
    · simp only [List.map_nil, List.prod_nil, submatrix_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.one_apply, Fin.ext_iff, Fin.val_castAdd,
        Fin.val_natAdd, fromBlocks_apply₁₂, Matrix.zero_apply]
      have := i.isLt
      omega
    · simp only [List.map_nil, List.prod_nil, submatrix_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.one_apply, Fin.ext_iff, Fin.val_castAdd,
        Fin.val_natAdd, fromBlocks_apply₂₁, Matrix.zero_apply]
      have := j.isLt
      omega
    · simp [Matrix.one_apply]
  | cons a t ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨reflMatrix (CartanMatrix.A n) a * B +
        Matrix.of (fun k _ => if k = a ∧ a.val + 1 = n then 1 else 0), ?_⟩
    let φ := reindexAlgEquiv ℤ ℤ (finSumFinEquiv (m := n) (n := 1)).symm
    have hmul : (((a :: t).map extReflA).prod).submatrix
          (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)) =
        (extReflA a).submatrix
          (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)) *
          ((t.map extReflA).prod).submatrix
            (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)) := by
      rw [List.map_cons, List.prod_cons]
      exact φ.map_mul _ _
    rw [hmul, hB]
    simp [extReflA, fromBlocks_multiply, List.map_cons, List.prod_cons]

/-- **Characteristic polynomial of the type `A` Coxeter element**: `1 + X + ⋯ + X ^ n` for every
rank `n` (including `n = 0`). -/
theorem charpoly_coxA (n : ℕ) :
    (coxA n).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  have hint := list_prod_mul_eq_mul_list_prod (List.finRange n) (diffBasis (n + 1))
    (permMatrix ∘ BraidGroup.transposition (n := n + 1)) extReflA
    (fun i _ => permMatrix_transposition_mul_diffBasis i)
  rw [← List.map_map, ← permMatrix_list_prod,
    ← permCoxeterSystem_wordProd (n := n + 1),
    permCoxeterSystem_wordProd_finRange_succ] at hint
  have hconj : conjDiffBasis (n + 1) (permMatrix (finRotate (n + 1))) =
      ((List.finRange n).map extReflA).prod := by
    rw [conjDiffBasis, mul_assoc, hint, ← mul_assoc, sumBasis_mul_diffBasis, one_mul]
  obtain ⟨B, hB⟩ := list_prod_extReflA (List.finRange n)
  have hc := charpoly_permMatrix_finRotate (Nat.succ_pos n)
  rw [← charpoly_conjDiffBasis, hconj,
    ← charpoly_reindex (finSumFinEquiv (m := n) (n := 1)).symm, reindex_apply,
    Equiv.symm_symm, hB, charpoly_fromBlocks_zero₂₁] at hc
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℤ).charpoly = X - 1 := by
    rw [Matrix.charpoly, Matrix.det_fin_one]
    simp
  rw [h1, ← geom_sum_mul X (n + 1)] at hc
  have hne : (X - 1 : ℤ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℤ)
  exact mul_right_cancel₀ hne hc

/-- The empty type `A₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxA_zero : orderOf (coxA 0) = 1 := by
  rw [Subsingleton.elim (coxA 0) 1, orderOf_one]

private theorem permMatrix_finRotate_pow_self (m : ℕ) :
    permMatrix (finRotate (m + 1)) ^ (m + 1) = 1 := by
  have hr : finRotate (m + 1) ^ (m + 1) = 1 := by
    ext q
    rw [Equiv.Perm.one_apply, finRotate_pow_apply (Nat.succ_pos m), Nat.add_mod_right,
      Nat.mod_eq_of_lt q.isLt]
  rw [permMatrix_pow, hr, permMatrix_one]

private theorem val_finRotate_pow_symm_zero {n m : ℕ} (hm : m < n + 1) (hpos : 0 < m) :
    ((finRotate (n + 1) ^ m).symm 0).val = n + 1 - m := by
  set s := (finRotate (n + 1) ^ m).symm 0
  have happ := finRotate_pow_apply (Nat.succ_pos n) m s
  rw [Equiv.apply_symm_apply, Fin.val_zero] at happ
  have hlt := s.isLt
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero happ.symm
  rcases k with _ | _ | k
  · rw [Nat.mul_zero] at hk; omega
  · rw [Nat.mul_one] at hk; omega
  · rw [Nat.mul_succ, Nat.mul_succ] at hk; omega

/-- **The Coxeter number of `Aₙ` (`0 < n`) is `n + 1`**: the Coxeter element of `CartanMatrix.A n`
has order `n + 1`. -/
theorem orderOf_coxA {n : ℕ} (hn : 0 < n) : orderOf (coxA n) = n + 1 := by
  have hint := list_prod_mul_eq_mul_list_prod (List.finRange n) (diffBasis (n + 1))
    (permMatrix ∘ BraidGroup.transposition (n := n + 1)) extReflA
    (fun i _ => permMatrix_transposition_mul_diffBasis i)
  rw [← List.map_map, ← permMatrix_list_prod,
    ← permCoxeterSystem_wordProd (n := n + 1),
    permCoxeterSystem_wordProd_finRange_succ] at hint
  obtain ⟨B, hB⟩ := list_prod_extReflA (List.finRange n)
  let U : Matrix (Fin (n + 1)) (Fin n) ℤ :=
    (diffBasis (n + 1)).submatrix id (finSumFinEquiv (m := n) (n := 1) ∘ Sum.inl)
  let W : Matrix (Fin n) (Fin (n + 1)) ℤ :=
    (sumBasis (n + 1)).submatrix (finSumFinEquiv (m := n) (n := 1) ∘ Sum.inl) id
  have hWU : W * U = 1 := by
    ext i j
    simpa [W, U, Matrix.mul_apply, Matrix.one_apply, finSumFinEquiv.injective.eq_iff] using
      congrFun₂ (sumBasis_mul_diffBasis (n + 1))
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
  have hSU : permMatrix (finRotate (n + 1)) * U = U * coxA n := by
    ext p j
    have hj := congrFun₂ hint p (finSumFinEquiv (Sum.inl j))
    have hU : (permMatrix (finRotate (n + 1)) * U) p j =
        (permMatrix (finRotate (n + 1)) * diffBasis (n + 1)) p (finSumFinEquiv (Sum.inl j)) := rfl
    rw [hU, hj, Matrix.mul_apply, Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := 1)).sum_comp]
    have hsub (r : Fin n ⊕ Fin 1) :
        ((List.finRange n).map extReflA).prod (finSumFinEquiv r) (finSumFinEquiv (Sum.inl j)) =
          fromBlocks (coxA n) B 0 1 r (Sum.inl j) :=
      congrFun₂ hB r (Sum.inl j)
    simp_rw [hsub]
    simp [U, Fintype.sum_sum_type, coxA, coxeterElement]
  refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun m hm hpos hm1 => ?_⟩
  · have hpow := pow_mul_eq_mul_pow hSU (n + 1)
    rw [permMatrix_finRotate_pow_self, Matrix.one_mul] at hpow
    calc coxA n ^ (n + 1) = W * (U * coxA n ^ (n + 1)) := by rw [← Matrix.mul_assoc, hWU, one_mul]
      _ = W * U := by rw [← hpow]
      _ = 1 := hWU
  · have hpow := pow_mul_eq_mul_pow hSU m
    rw [hm1, Matrix.mul_one, permMatrix_pow] at hpow
    have h0 := congrFun₂ hpow 0 ⟨0, hn⟩
    rw [permMatrix_mul_apply] at h0
    simp only [U, submatrix_apply, id_eq, Function.comp_apply, finSumFinEquiv_apply_left,
      diffBasis, Matrix.of_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_zero,
      val_finRotate_pow_symm_zero hm hpos] at h0
    split_ifs at h0 <;> omega

/-! ### Type `B` -/

/-- Sign-flip matrix negating the last coordinate `Fin.last m` of `ℤ^{m+1}`. -/
private def lastFlip (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  diagonal fun p => if p = Fin.last m then -1 else 1

private theorem permMatrix_transposition_mul_diffBasis_B {m : ℕ} (i : Fin m) :
    permMatrix (BraidGroup.transposition (n := m + 1) i) * diffBasis (m + 1) =
      diffBasis (m + 1) * reflMatrix (CartanMatrix.B (m + 1)) i.castSucc := by
  ext p q
  rw [permMatrix_mul_apply, transposition_symm, mul_reflMatrix_apply]
  have hi := i.isLt
  simp only [diffBasis, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc,
    BraidGroup.val_transposition_apply, Nat.add_sub_cancel]
  split_ifs <;> omega

private theorem lastFlip_mul_diffBasis (m : ℕ) :
    lastFlip m * diffBasis (m + 1) =
      diffBasis (m + 1) * reflMatrix (CartanMatrix.B (m + 1)) (Fin.last m) := by
  ext p q
  rw [lastFlip, diagonal_mul, mul_reflMatrix_apply]
  have hp := p.isLt
  have hq := q.isLt
  simp only [diffBasis, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
    Nat.add_sub_cancel]
  split_ifs <;> omega

private theorem permMatrix_finRotate_mul_lastFlip (m : ℕ) :
    permMatrix (finRotate (m + 1)) * lastFlip m = negShift (m + 1) := by
  ext p q
  rw [lastFlip, mul_diagonal, permMatrix, negShift, Matrix.of_apply, Matrix.of_apply]
  have hq := q.isLt
  have hrot : ((finRotate (m + 1)) q).val = if q.val = m then 0 else q.val + 1 := by
    simpa [Fin.ext_iff, Fin.val_last] using coe_finRotate q
  simp only [Fin.ext_iff, Fin.val_last, hrot]
  split_ifs <;> omega

private theorem negShift_mul_diffBasis_eq_diffBasis_mul_coxB (m : ℕ) :
    negShift (m + 1) * diffBasis (m + 1) = diffBasis (m + 1) * coxB (m + 1) := by
  have h1 := list_prod_mul_eq_mul_list_prod (List.finRange m) (diffBasis (m + 1))
    (permMatrix ∘ BraidGroup.transposition (n := m + 1))
    (fun i => reflMatrix (CartanMatrix.B (m + 1)) i.castSucc)
    (fun i _ => permMatrix_transposition_mul_diffBasis_B i)
  rw [← List.map_map, ← permMatrix_list_prod,
    ← permCoxeterSystem_wordProd (n := m + 1),
    permCoxeterSystem_wordProd_finRange_succ] at h1
  calc negShift (m + 1) * diffBasis (m + 1)
      = permMatrix (finRotate (m + 1)) * (lastFlip m * diffBasis (m + 1)) := by
          rw [← mul_assoc, permMatrix_finRotate_mul_lastFlip]
    _ = (permMatrix (finRotate (m + 1)) * diffBasis (m + 1)) *
          reflMatrix (CartanMatrix.B (m + 1)) (Fin.last m) := by
          rw [lastFlip_mul_diffBasis, mul_assoc]
    _ = diffBasis (m + 1) * coxB (m + 1) := by
          rw [h1, mul_assoc, coxB, coxeterElement, finRange_succ_eq_map_castSucc_append_last,
            List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
            List.map_map]
          rfl

/-- The empty type `B₀` Coxeter element has characteristic polynomial `1`. -/
theorem charpoly_coxB_zero : (coxB 0).charpoly = 1 := by simp

/-- **Characteristic polynomial of the type `B` Coxeter element** (`0 < n`): `X ^ n + 1`. -/
theorem charpoly_coxB {n : ℕ} (hn : 0 < n) : (coxB n).charpoly = X ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hconj : conjDiffBasis (m + 1) (negShift (m + 1)) = coxB (m + 1) := by
    rw [conjDiffBasis, mul_assoc, negShift_mul_diffBasis_eq_diffBasis_mul_coxB, ← mul_assoc,
      sumBasis_mul_diffBasis, one_mul]
  rw [← hconj, charpoly_conjDiffBasis, charpoly_negShift (Nat.succ_pos m)]

/-- The empty type `B₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxB_zero : orderOf (coxB 0) = 1 := by
  rw [Subsingleton.elim (coxB 0) 1, orderOf_one]

/-- **The Coxeter number of `Bₙ` (`0 < n`) is `2 * n`**: the Coxeter element of `CartanMatrix.B n`
has order `2 * n`. -/
theorem orderOf_coxB {n : ℕ} (hn : 0 < n) : orderOf (coxB n) = 2 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpow (k : ℕ) : negShift (m + 1) ^ k = 1 ↔ coxB (m + 1) ^ k = 1 := by
    have h := pow_mul_eq_mul_pow (negShift_mul_diffBasis_eq_diffBasis_mul_coxB m) k
    constructor <;> intro hk
    · rw [hk, one_mul] at h
      calc coxB (m + 1) ^ k = sumBasis (m + 1) * (diffBasis (m + 1) * coxB (m + 1) ^ k) := by
            rw [← mul_assoc, sumBasis_mul_diffBasis, one_mul]
        _ = sumBasis (m + 1) * diffBasis (m + 1) := by rw [← h]
        _ = 1 := sumBasis_mul_diffBasis (m + 1)
    · rw [hk, mul_one] at h
      calc negShift (m + 1) ^ k
          = (negShift (m + 1) ^ k * diffBasis (m + 1)) * sumBasis (m + 1) := by
            rw [mul_assoc, diffBasis_mul_sumBasis, mul_one]
        _ = diffBasis (m + 1) * sumBasis (m + 1) := by rw [h]
        _ = 1 := diffBasis_mul_sumBasis (m + 1)
  rw [← orderOf_negShift (Nat.succ_pos m)]
  exact orderOf_eq_orderOf_iff.mpr fun k => (hpow k).symm

/-! ### Type `C` -/

/-- Diagonal matrix `diag(1, …, 1, 2)` intertwining `CartanMatrix.C n` and `CartanMatrix.B n`. -/
private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun i => if i.val + 1 = n then 2 else 1

private theorem diagBC_mul_reflMatrix_C (n : ℕ) (i : Fin n) :
    diagBC n * reflMatrix (CartanMatrix.C n) i = reflMatrix (CartanMatrix.B n) i * diagBC n := by
  ext k j
  rw [diagBC, diagonal_mul, mul_diagonal]
  have hk := k.isLt
  have hj := j.isLt
  have hi := i.isLt
  simp only [reflMatrix_apply, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem diagBC_mul_coxC (n : ℕ) : diagBC n * coxC n = coxB n * diagBC n := by
  simpa [coxC, coxB, coxeterElement] using
    (list_prod_mul_eq_mul_list_prod (List.finRange n) (diagBC n)
      (reflMatrix (CartanMatrix.B n)) (reflMatrix (CartanMatrix.C n))
      fun i _ => (diagBC_mul_reflMatrix_C n i).symm).symm

/-- The Coxeter elements of `CartanMatrix.C n` and `CartanMatrix.B n` have the same order for every
`n`. -/
theorem orderOf_coxC_eq_orderOf_coxB (n : ℕ) : orderOf (coxC n) = orderOf (coxB n) := by
  refine orderOf_eq_orderOf_iff.mpr fun k => ?_
  have h := pow_mul_eq_mul_pow (diagBC_mul_coxC n).symm k
  constructor <;> intro hk
  · rw [hk, mul_one] at h
    ext p q
    have hpq := congrFun₂ h p q
    simp only [diagBC, mul_diagonal, diagonal_apply, Matrix.one_apply] at hpq ⊢
    split_ifs at hpq ⊢ <;> omega
  · rw [hk, one_mul] at h
    ext p q
    have hpq := congrFun₂ h p q
    simp only [diagBC, diagonal_mul, diagonal_apply, Matrix.one_apply] at hpq ⊢
    split_ifs at hpq ⊢ <;> omega

/-- The Coxeter elements of `CartanMatrix.C n` and `CartanMatrix.B n` have the same characteristic
polynomial for every `n`. -/
theorem charpoly_coxC_eq_charpoly_coxB (n : ℕ) : (coxC n).charpoly = (coxB n).charpoly := by
  apply charpoly_eq_of_map_rat
  rw [← charpoly_map]
  set Dq : Matrix (Fin n) (Fin n) ℚ :=
    diagonal fun i => if i.val + 1 = n then (2 : ℚ) else 1
  set Dinv : Matrix (Fin n) (Fin n) ℚ :=
    diagonal fun i => if i.val + 1 = n then (2⁻¹ : ℚ) else 1
  have hDD : Dq * Dinv = 1 := by
    rw [diagonal_mul_diagonal]
    ext i j
    simp only [diagonal_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  have hmap : Dq = (diagBC n).map (Int.castRingHom ℚ) := by
    ext i j
    simp only [Dq, diagBC, diagonal_apply, map_apply, eq_intCast]
    split_ifs <;> norm_num
  have hint := congrArg (Matrix.map · (Int.castRingHom ℚ)) (diagBC_mul_coxC n)
  rw [Matrix.map_mul, Matrix.map_mul, ← hmap] at hint
  have hconj : Dinv * (coxB n).map (Int.castRingHom ℚ) * Dq = (coxC n).map (Int.castRingHom ℚ) := by
    rw [mul_assoc, ← hint, ← mul_assoc, mul_eq_one_comm.mp hDD, one_mul]
  rw [← hconj, Matrix.charpoly_mul_comm, ← mul_assoc, hDD, one_mul]

/-- The empty type `C₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxC_zero : orderOf (coxC 0) = 1 := by
  rw [orderOf_coxC_eq_orderOf_coxB, orderOf_coxB_zero]

/-- **The Coxeter number of `Cₙ` (`0 < n`) is `2 * n`**: the Coxeter element of `CartanMatrix.C n`
has order `2 * n`. -/
theorem orderOf_coxC {n : ℕ} (hn : 0 < n) : orderOf (coxC n) = 2 * n :=
  (orderOf_coxC_eq_orderOf_coxB n).trans (orderOf_coxB hn)

/-- The empty type `C₀` Coxeter element has characteristic polynomial `1`. -/
theorem charpoly_coxC_zero : (coxC 0).charpoly = 1 := by simp

/-- **Characteristic polynomial of the type `C` Coxeter element** (`0 < n`): `X ^ n + 1`. -/
theorem charpoly_coxC {n : ℕ} (hn : 0 < n) : (coxC n).charpoly = X ^ n + 1 :=
  (charpoly_coxC_eq_charpoly_coxB n).trans (charpoly_coxB hn)

/-! ### Type `D` -/

/-- Simple-root columns `ε₀ - ε₁, …, εₘ - ε_{m+1}, εₘ + ε_{m+1}` of `D_{m+2}` in `ℤ^{m+2}`. -/
private def basisD (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  diffBasis (m + 2) *
    Matrix.of fun p q =>
      if p = q then (if q.val = m + 1 then 2 else 1)
      else if p.val = m ∧ q.val = m + 1 then 1 else 0

/-- Integer quasi-inverse of `basisD m`, satisfying `adjBasisD m * basisD m = 2 • 1`. -/
private def adjBasisD (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  (Matrix.of fun p q =>
    if p = q then (if q.val = m + 1 then 1 else 2)
    else if p.val = m ∧ q.val = m + 1 then -1 else 0) * sumBasis (m + 2)

private theorem basisD_apply (m : ℕ) (p q : Fin (m + 2)) :
    basisD m p q =
      if q.val < m + 1 then (if p = q then 1 else if p.val = q.val + 1 then -1 else 0)
      else (if p.val = m ∨ p.val = m + 1 then 1 else 0) := by
  rw [basisD, Matrix.mul_apply]
  have hp := p.isLt
  have hq := q.isLt
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hq) with hqlt | hqlast
  · rw [Finset.sum_eq_single q]
    · simp only [diffBasis, Matrix.of_apply, ↓reduceIte, hqlt]
      split_ifs <;> omega
    · intro r _ hr
      have hnot : ¬ (r.val = m ∧ q.val = m + 1) := by omega
      simp [hr, hnot]
    · intro h; exact absurd (Finset.mem_univ _) h
  · let r0 : Fin (m + 2) := ⟨m, by omega⟩
    let r1 : Fin (m + 2) := ⟨m + 1, by omega⟩
    have hr01 : r0 ≠ r1 := fun h => by have := congrArg Fin.val h; dsimp [r0, r1] at this; omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hr01.symm, Finset.mem_univ r1⟩),
      Finset.sum_eq_zero]
    · clear hr01
      simp [diffBasis, Fin.ext_iff, hqlast, r0, r1]
      split_ifs <;> omega
    · intro r hr
      have hr0 : r ≠ r0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      have hr1 : r ≠ r1 := (Finset.mem_erase.mp hr).1
      have hne1 : r ≠ q := fun h => hr1 (Fin.ext (by rw [h]; exact hqlast))
      have hne2 : ¬ (r.val = m ∧ q.val = m + 1) := fun h => hr0 (Fin.ext h.1)
      simp [hne1, hne2]

private theorem adjBasisD_mul_basisD (m : ℕ) : adjBasisD m * basisD m = (2 : ℤ) • 1 := by
  rw [adjBasisD, basisD, mul_assoc, ← mul_assoc (sumBasis (m + 2)), sumBasis_mul_diffBasis, one_mul]
  let r0 : Fin (m + 2) := ⟨m, Nat.lt_succ_of_lt (Nat.lt_succ_self m)⟩
  let r1 : Fin (m + 2) := ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
  have hr01 : r0 ≠ r1 := fun h => by have := congrArg Fin.val h; simp [r0, r1] at this
  ext p q
  rw [Matrix.mul_apply]
  have hp := p.isLt
  by_cases hp0 : p = r0
  · rw [hp0, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hr01.symm, Finset.mem_univ r1⟩),
      Finset.sum_eq_zero]
    · clear hr01 hp0 hp
      simp [Fin.ext_iff, Matrix.one_apply, r0, r1]
      split_ifs <;> omega
    · intro r hr
      have h1 : r0 ≠ r := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1 h.symm
      have h2 : r.val ≠ m + 1 := fun h => (Finset.mem_erase.mp hr).1 (Fin.ext h)
      simp [h1, h2]
  · have hpm : p.val ≠ m := fun h => hp0 (Fin.ext h)
    clear hp0 hr01
    rw [Finset.sum_eq_single p]
    · simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ↓reduceIte,
        Fin.ext_iff]
      split_ifs <;> omega
    · intro r _ hr
      simp [hr.symm, hpm]
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem cartanMatrix_D_apply_succ_succ (m : ℕ) (i j : Fin (m + 2)) :
    CartanMatrix.D (m + 2) i j =
      if i = j then 2
      else if m = 0 then 0
      else if (i.val + 1 = j.val ∧ j.val < m) ∨ (j.val + 1 = i.val ∧ i.val < m) ∨
        (i.val + 1 = m ∧ (j.val = m ∨ j.val = m + 1)) ∨
        (j.val + 1 = m ∧ (i.val = m ∨ i.val = m + 1))
      then -1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> omega

/-- Reflection across `(εₘ + ε_{m+1})⊥` in `ℤ^{m+2}`: fixes `εₖ` (`k < m`) and sends
`εₘ ↦ -ε_{m+1}`, `ε_{m+1} ↦ -εₘ`. -/
private def forkFlip (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  Matrix.of fun p q =>
    if p.val < m then (if p = q then 1 else 0)
    else if p.val = m then (if q.val = m + 1 then -1 else 0)
    else (if q.val = m then -1 else 0)

private theorem permMatrix_transposition_mul_basisD {m : ℕ} (i : Fin (m + 1)) :
    permMatrix (BraidGroup.transposition (n := m + 2) i) * basisD m =
      basisD m * reflMatrix (CartanMatrix.D (m + 2)) i.castSucc := by
  ext p q
  rw [permMatrix_mul_apply, transposition_symm, mul_reflMatrix_apply]
  have hp := p.isLt
  have hq := q.isLt
  have hi := i.isLt
  have hicv : (i.castSucc : Fin (m + 2)).val = i.val := rfl
  have hD : CartanMatrix.D (m + 2) q i.castSucc =
      if q.val = i.val then 2
      else if (q.val < m + 1 ∧ (q.val + 1 = i.val ∨ i.val + 1 = q.val)) ∨
        (q.val = m + 1 ∧ i.val + 1 = m) then -1
      else 0 := by
    rw [cartanMatrix_D_apply_succ_succ]
    simp only [Fin.ext_iff, hicv]
    split_ifs <;> omega
  rw [hD]
  set sp := BraidGroup.transposition (n := m + 2) i p
  have hsp : sp.val =
      if p.val = i.val then i.val + 1 else if p.val = i.val + 1 then i.val else p.val :=
    BraidGroup.val_transposition_apply (n := m + 2) i p
  rcases eq_or_ne q.val i.val with hqi | hqi
  · simp only [hqi, ↓reduceIte, basisD_apply, Fin.ext_iff, hicv, hi]
    split_ifs at hsp ⊢ <;> omega
  · by_cases hadj : (q.val < m + 1 ∧ (q.val + 1 = i.val ∨ i.val + 1 = q.val)) ∨
        (q.val = m + 1 ∧ i.val + 1 = m)
    · simp only [hqi, hadj, ↓reduceIte, basisD_apply, Fin.ext_iff, hicv, hi]
      split_ifs at hsp ⊢ <;> omega
    · simp only [hqi, hadj, ↓reduceIte, mul_zero, sub_zero, basisD_apply, Fin.ext_iff]
      split_ifs at hsp ⊢ <;> omega

private theorem forkFlip_mul_apply {m k : ℕ} (M : Matrix (Fin (m + 2)) (Fin k) ℤ)
    (p : Fin (m + 2)) (q : Fin k) :
    (forkFlip m * M) p q =
      if p.val < m then M p q
      else if p.val = m then -M (Fin.last (m + 1)) q
      else -M (Fin.last m).castSucc q := by
  rw [Matrix.mul_apply]
  split_ifs with hp1 hp2
  · rw [Finset.sum_eq_single p]
    · simp [forkFlip, hp1]
    · intro r _ hr; simp [forkFlip, hp1, hr.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (Fin.last (m + 1))]
    · simp [forkFlip, hp2]
    · intro r _ hr
      have hne : r.val ≠ m + 1 := fun h => hr (Fin.ext (by simpa using h))
      simp [forkFlip, hp2, hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (Fin.last m).castSucc]
    · simp [forkFlip, hp1, hp2]
    · intro r _ hr
      have hne : r.val ≠ m := fun h => hr (Fin.ext (by simpa using h))
      simp [forkFlip, hp1, hp2, hne]
    · intro h; exact absurd (Finset.mem_univ _) h

private theorem forkFlip_mul_basisD (m : ℕ) :
    forkFlip m * basisD m =
      basisD m * reflMatrix (CartanMatrix.D (m + 2)) (Fin.last (m + 1)) := by
  ext p q
  rw [forkFlip_mul_apply, mul_reflMatrix_apply]
  have hq := q.isLt
  have hD : CartanMatrix.D (m + 2) q (Fin.last (m + 1)) =
      if q.val = m + 1 then 2 else if q.val + 1 = m then -1 else 0 := by
    rw [cartanMatrix_D_apply_succ_succ]
    simp [Fin.ext_iff]
    split_ifs <;> omega
  rw [hD]
  have hp := p.isLt
  rcases eq_or_ne q.val (m + 1) with hq1 | hq1
  · simp [hq1, basisD_apply]
    split_ifs <;> omega
  · have hqlt : q.val < m + 1 := by omega
    by_cases hqm : q.val + 1 = m
    · simp [hq1, hqm, hqlt, basisD_apply, Fin.ext_iff]
      split_ifs <;> omega
    · simp [hq1, hqm, hqlt, basisD_apply, Fin.ext_iff]
      split_ifs <;> omega

/-- Block-diagonal model `fromBlocks (negShift (m + 1)) 0 0 (-1)` of `coxD (m + 2)`. -/
private def modelD (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  reindex (finSumFinEquiv (m := m + 1) (n := 1)) (finSumFinEquiv (m := m + 1) (n := 1))
    (fromBlocks (negShift (m + 1)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ))

private theorem permMatrix_finRotate_mul_forkFlip (m : ℕ) :
    permMatrix (finRotate (m + 2)) * forkFlip m = modelD m := by
  ext p q
  rw [permMatrix_mul_apply]
  set s := (finRotate (m + 2)).symm p
  have hs_lt := s.isLt
  have hrot : p.val = if s.val = m + 1 then 0 else s.val + 1 := by
    have h := coe_finRotate s
    rw [Equiv.apply_symm_apply] at h
    simpa [Fin.ext_iff, Fin.val_last] using h
  obtain ⟨sp, rfl⟩ := (finSumFinEquiv (m := m + 1) (n := 1)).surjective p
  obtain ⟨sq, rfl⟩ := (finSumFinEquiv (m := m + 1) (n := 1)).surjective q
  rw [modelD, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases sp with ip | ip <;> rcases sq with iq | iq
  · have hip := ip.isLt
    have hiq := iq.isLt
    simp only [fromBlocks_apply₁₁, forkFlip, negShift, Matrix.of_apply, finSumFinEquiv_apply_left,
      Fin.val_castAdd, Fin.ext_iff] at hrot ⊢
    split_ifs at hrot ⊢ <;> omega
  · fin_cases iq
    have hip := ip.isLt
    simp [forkFlip, Fin.ext_iff] at hrot ⊢
    split_ifs at hrot ⊢ <;> omega
  · fin_cases ip
    have hiq := iq.isLt
    simp [forkFlip, Fin.ext_iff] at hrot ⊢
    split_ifs at hrot ⊢ <;> omega
  · fin_cases ip
    fin_cases iq
    simp [forkFlip] at hrot ⊢
    split_ifs at hrot ⊢ <;> omega

private theorem modelD_mul_basisD_eq_basisD_mul_coxD (m : ℕ) :
    modelD m * basisD m = basisD m * coxD (m + 2) := by
  have h1 := list_prod_mul_eq_mul_list_prod (List.finRange (m + 1)) (basisD m)
    (permMatrix ∘ BraidGroup.transposition (n := m + 2))
    (fun i => reflMatrix (CartanMatrix.D (m + 2)) i.castSucc)
    (fun i _ => permMatrix_transposition_mul_basisD i)
  rw [← List.map_map, ← permMatrix_list_prod,
    ← permCoxeterSystem_wordProd (n := m + 2),
    permCoxeterSystem_wordProd_finRange_succ] at h1
  have hfr : List.finRange (m + 2) =
      (List.finRange (m + 1)).map Fin.castSucc ++ [Fin.last (m + 1)] :=
    finRange_succ_eq_map_castSucc_append_last (m + 1)
  calc modelD m * basisD m
      = permMatrix (finRotate (m + 2)) * (forkFlip m * basisD m) := by
          rw [← mul_assoc, permMatrix_finRotate_mul_forkFlip]
    _ = (permMatrix (finRotate (m + 2)) * basisD m) *
          reflMatrix (CartanMatrix.D (m + 2)) (Fin.last (m + 1)) := by
          rw [forkFlip_mul_basisD, mul_assoc]
    _ = basisD m * coxD (m + 2) := by
          rw [h1, mul_assoc, coxD, coxeterElement, hfr,
            List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
            List.map_map]
          rfl

/-- The empty type `D₀` Coxeter element has characteristic polynomial `1`. -/
theorem charpoly_coxD_zero : (coxD 0).charpoly = 1 := by simp

/-- The degenerate rank-`1` type `D₁` Coxeter element (`-1`) has characteristic polynomial
`X + 1`. -/
@[simp]
theorem charpoly_coxD_one : (coxD 1).charpoly = X + 1 := by
  have h : coxD 1 = -1 := by decide
  rw [h, Matrix.charpoly, Matrix.det_fin_one]
  simp [sub_neg_eq_add]

/-- **Characteristic polynomial of the type `D` Coxeter element** (`2 ≤ n`):
`(X ^ (n - 1) + 1) * (X + 1)`. Holds for `D₂ = A₁ × A₁` and `D₃ = A₃` as well as `n ≥ 4`. -/
theorem charpoly_coxD {n : ℕ} (hn : 2 ≤ n) :
    (coxD n).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hmodel : (modelD m).charpoly = (X ^ (m + 1) + 1) * (X + 1) := by
    rw [modelD, charpoly_reindex, charpoly_fromBlocks_zero₂₁,
      charpoly_negShift (Nat.succ_pos m)]
    congr 1
    rw [Matrix.charpoly, Matrix.det_fin_one]
    simp [sub_neg_eq_add]
  rw [show m + 2 - 1 = m + 1 by omega, ← hmodel]
  apply charpoly_eq_of_map_rat
  rw [← charpoly_map]
  set Uq : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ := (basisD m).map (Int.castRingHom ℚ)
  set Vin : Matrix (Fin (m + 2)) (Fin (m + 2)) ℚ :=
    (2⁻¹ : ℚ) • (adjBasisD m).map (Int.castRingHom ℚ)
  have hVU : Vin * Uq = 1 := by
    have hadj := congrArg (Matrix.map · (Int.castRingHom ℚ)) (adjBasisD_mul_basisD m)
    rw [Matrix.map_mul] at hadj
    ext i j
    have hij := congrFun₂ hadj i j
    simp only [Vin, Uq, Matrix.smul_mul, Matrix.smul_apply, hij, map_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> norm_num
  have hint := congrArg (Matrix.map · (Int.castRingHom ℚ)) (modelD_mul_basisD_eq_basisD_mul_coxD m)
  rw [Matrix.map_mul, Matrix.map_mul] at hint
  have hconj : Vin * (modelD m).map (Int.castRingHom ℚ) * Uq =
      (coxD (m + 2)).map (Int.castRingHom ℚ) := by
    rw [mul_assoc, hint, ← mul_assoc, hVU, one_mul]
  rw [← hconj, Matrix.charpoly_mul_comm, ← mul_assoc, mul_eq_one_comm.mp hVU, one_mul]

/-- The empty type `D₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxD_zero : orderOf (coxD 0) = 1 := by
  rw [Subsingleton.elim (coxD 0) 1, orderOf_one]

/-- The degenerate rank-`1` type `D₁` Coxeter element (`-1`) has order `2`. -/
@[simp]
theorem orderOf_coxD_one : orderOf (coxD 1) = 2 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide +kernel, by decide +kernel⟩

private theorem fromBlocks_negShift_pow (m k : ℕ) :
    (fromBlocks (negShift (m + 1)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ)) ^ k =
      fromBlocks (negShift (m + 1) ^ k) 0 0 ((-1) ^ k) := by
  induction k with
  | zero =>
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  | succ r ih =>
    rw [pow_succ, pow_succ, pow_succ, ih, fromBlocks_multiply]
    simp

private theorem orderOf_modelD (m : ℕ) : orderOf (modelD m) = 2 * (m + 1) := by
  let heqv := (reindexAlgEquiv ℤ ℤ (finSumFinEquiv (m := m + 1) (n := 1))).toRingEquiv.toMulEquiv
  have hmeq : modelD m =
      heqv (fromBlocks (negShift (m + 1)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ)) := rfl
  rw [hmeq, heqv.orderOf_eq]
  refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun k hk hpos hk1 => ?_⟩
  · rw [fromBlocks_negShift_pow, ← orderOf_negShift (Nat.succ_pos m), pow_orderOf_eq_one,
      orderOf_negShift (Nat.succ_pos m), pow_mul, neg_one_sq, one_pow]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  · rw [fromBlocks_negShift_pow] at hk1
    have h11 : negShift (m + 1) ^ k = 1 := by
      ext i j
      simpa [Matrix.one_apply] using congrFun₂ hk1 (Sum.inl i) (Sum.inl j)
    have hle := orderOf_le_of_pow_eq_one hpos h11
    rw [orderOf_negShift (Nat.succ_pos m)] at hle
    omega

private theorem basisD_mul_adjBasisD (m : ℕ) : basisD m * adjBasisD m = (2 : ℤ) • 1 := by
  -- Over `ℚ`, `(1/2 • adjBasisD m) * basisD m = 1`, so left and right inverses commute.
  apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
  have h1 := congrArg (Matrix.map · (Int.castRingHom ℚ)) (adjBasisD_mul_basisD m)
  rw [Matrix.map_mul] at h1
  have hunit : ((2⁻¹ : ℚ) • (adjBasisD m).map (Int.castRingHom ℚ)) *
      (basisD m).map (Int.castRingHom ℚ) = 1 := by
    ext i j
    have hij := congrFun₂ h1 i j
    simp only [Matrix.smul_mul, Matrix.smul_apply, hij, map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  have hcomm := mul_eq_one_comm.mp hunit
  rw [Matrix.mul_smul, ← Matrix.map_mul] at hcomm
  ext i j
  have hij := congrFun₂ hcomm i j
  simp only [Matrix.smul_apply, map_apply, Matrix.one_apply, smul_eq_mul, eq_intCast] at hij ⊢
  split_ifs at hij ⊢ <;> push_cast <;> linarith

/-- **The Coxeter number of `Dₙ` (`2 ≤ n`) is `2 * (n - 1)`**: the Coxeter element of
`CartanMatrix.D n` has order `2 * (n - 1)`. -/
theorem orderOf_coxD {n : ℕ} (hn : 2 ≤ n) : orderOf (coxD n) = 2 * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, ← orderOf_modelD m]
  refine orderOf_eq_orderOf_iff.mpr fun k => ?_
  have h := pow_mul_eq_mul_pow (modelD_mul_basisD_eq_basisD_mul_coxD m) k
  constructor <;> intro hk
  · rw [hk, mul_one] at h
    have h2 : (2 : ℤ) • modelD m ^ k = (2 : ℤ) • 1 := by
      calc (2 : ℤ) • modelD m ^ k = modelD m ^ k * ((2 : ℤ) • 1) := by rw [mul_smul_comm, mul_one]
        _ = (modelD m ^ k * basisD m) * adjBasisD m := by rw [← basisD_mul_adjBasisD, mul_assoc]
        _ = (2 : ℤ) • 1 := by rw [h, basisD_mul_adjBasisD]
    ext i j
    have hij := congrFun₂ h2 i j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    omega
  · rw [hk, one_mul] at h
    have h2 : (2 : ℤ) • coxD (m + 2) ^ k = (2 : ℤ) • 1 := by
      calc (2 : ℤ) • coxD (m + 2) ^ k = ((2 : ℤ) • 1) * coxD (m + 2) ^ k := by
            rw [smul_mul_assoc, one_mul]
        _ = adjBasisD m * (basisD m * coxD (m + 2) ^ k) := by rw [← adjBasisD_mul_basisD, mul_assoc]
        _ = (2 : ℤ) • 1 := by rw [← h, adjBasisD_mul_basisD]
    ext i j
    have hij := congrFun₂ h2 i j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    omega

end TauCeti.Coxeter

end
