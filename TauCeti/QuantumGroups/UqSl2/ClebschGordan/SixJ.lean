/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic
import TauCeti.Algebra.BigOperators.Finset.Filter

/-!
# Quantum 6j change-of-decomposition matrices

At a generic parameter `q`, indexing the triple-product recoupling scalars `recouplingCoeff` and
`invRecouplingCoeff` on `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` by intermediate highest weights `u` and `v` at
fixed total highest weight `k` yields the six-weight change-of-decomposition (`F`-matrix) functions
`sixJ` and `invSixJ` (extended by `0` outside admissible Clebsch–Gordan channels) and the two-sided
inverse matrices `sixJMatrix` and `invSixJMatrix`.

Here `sixJ` is the recoupling entry in the unnormalized `α₀ = 1` highest-weight convention of
`clebschGordanInclusion` (so its value depends on that basis normalization and on the module signs
`ε, δ, ζ`, as in `sixJ_zero_right`), rather than the Racah/Kirillov–Reshetikhin-normalized,
tetrahedrally symmetric 6j symbol.

* `TauCeti.UqSl2.LeftSixJChannel`, `RightSixJChannel`,
  `card_leftSixJChannel_eq_card_rightSixJChannel`: admissible triple-product channels and equality
  of left and right multiplicities.
* `TauCeti.UqSl2.sixJ`, `invSixJ`, `sixJMatrix`, `invSixJMatrix`: `α₀ = 1` change-of-decomposition
  (`F`-matrix) scalars and matrices.
* `TauCeti.UqSl2.invSixJMatrix_mul_sixJMatrix`, `sixJMatrix_mul_invSixJMatrix`: matrix inverses.
* `TauCeti.UqSl2.sixJ_add_add`, `TauCeti.UqSl2.sixJ_zero_left`, `TauCeti.UqSl2.sixJ_zero_right`:
  explicit boundary values.
* `TauCeti.UqSl2.sixJ_one_one_one_zero_zero`, `sixJ_one_one_one_zero_two`,
  `sixJ_one_one_one_two_zero`, `sixJ_one_one_one_two_two`, and `invSixJ` counterparts: closed-form
  `2 × 2` spin-`1/2` evaluations on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at total highest weight `1`.
* `TauCeti.UqSl2.clebschGordanLeftBasis`, `clebschGordanRightBasis`,
  `toMatrix_assoc_clebschGordanBasis`, `toMatrix_assoc_symm_clebschGordanBasis`: coupled normalized
  `F`-ladder bases and block-diagonal matrices of `BialgebraModule.assoc` and `assoc.symm`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, World Scientific, 1989, pp. 285--339
  (for quantum recoupling and 6j theory, up to basis rescaling).
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

/-! ### Admissible triple-product channels -/

/-- Admissible left intermediate highest weights `u` in `(L_m ⊗ L_n) ⊗ L_p` coupling to `k`. -/
abbrev LeftSixJChannel (m n p k : ℕ) : Type :=
  {u : ℕ // IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k}

/-- Admissible right intermediate highest weights `v` in `L_m ⊗ (L_n ⊗ L_p)` coupling to `k`. -/
abbrev RightSixJChannel (m n p k : ℕ) : Type :=
  {v : ℕ // IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k}

instance (m n p k : ℕ) : Fintype (LeftSixJChannel m n p k) :=
  Fintype.ofFinset (p := {u : ℕ | IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k})
    ((Finset.range (m + n + 1)).filter fun u =>
      IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) fun _ => by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

instance (m n p k : ℕ) : Fintype (RightSixJChannel m n p k) :=
  Fintype.ofFinset (p := {v : ℕ | IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k})
    ((Finset.range (n + p + 1)).filter fun v =>
      IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) fun _ => by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

/-! ### Six-weight change-of-decomposition scalars and matrices -/

section SixJ

variable {q : ℂ}

/-- Six-weight change-of-decomposition (`F`-matrix) entry for `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` at total
highest weight `k` in the `α₀ = 1` normalization of `clebschGordanInclusion`, from left
intermediate channel `u` to right intermediate channel `v` (extended by `0` outside admissible
channels). Unlike the Racah/Kirillov–Reshetikhin symbol, it is not rescaled to tetrahedral
symmetry and depends on `ε, δ, ζ`. -/
def sixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k u v : ℕ) : ℂ :=
  if h : (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) ∧
      (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) then
    recouplingCoeff hq ε δ ζ h.1.1.index
      (h.1.2.index.cast (congrArg (min · p + 1) h.1.1.sub_two_mul_index.symm))
      h.2.1.index
      (h.2.2.index.cast (congrArg (min m · + 1) h.2.1.sub_two_mul_index.symm))
  else 0

/-- Inverse six-weight change-of-decomposition (`F`-matrix) entry for `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` at
total highest weight `k` in the `α₀ = 1` normalization of `clebschGordanInclusion`, from right
channel `v` to left channel `u` (extended by `0` outside admissible channels). -/
def invSixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k v u : ℕ) : ℂ :=
  if h : (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) ∧
      (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) then
    invRecouplingCoeff hq ε δ ζ h.1.1.index
      (h.1.2.index.cast (congrArg (min m · + 1) h.1.1.sub_two_mul_index.symm))
      h.2.1.index
      (h.2.2.index.cast (congrArg (min · p + 1) h.2.1.sub_two_mul_index.symm))
  else 0

/-- On any left channel `(i, j)` and right channel `(r, s)` with intermediate weights `u, v` and
common total weight `k`, `sixJ` equals `recouplingCoeff hq ε δ ζ i j r s`. -/
theorem sixJ_eq_recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p k u v : ℕ}
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    (hu : m + n - 2 * (i : ℕ) = u) (hk : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = k)
    (hv : n + p - 2 * (r : ℕ) = v) (hk' : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = k) :
    sixJ hq ε δ ζ m n p k u v = recouplingCoeff hq ε δ ζ i j r s := by
  subst hu hv hk
  have hu₁ := isClebschGordanChannel_sub_two_mul i
  have hu₂ := isClebschGordanChannel_sub_two_mul j
  have hv₁ := isClebschGordanChannel_sub_two_mul r
  have hv₂ : IsClebschGordanChannel m (n + p - 2 * (r : ℕ))
      (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) := isClebschGordanChannel_def.mpr ⟨s, hk'⟩
  rw [sixJ, dite_eq_left ⟨⟨hu₁, hu₂⟩, ⟨hv₁, hv₂⟩⟩]
  exact recouplingCoeff_congr hq ε δ ζ (by simp) (by simp) (by simp)
    (by simp [hv₂.index_eq_of_eq hk'])

/-- On any right channel `(r, s)` and left channel `(i, j)` with intermediate weights `v, u` and
common total weight `k`, `invSixJ` equals `invRecouplingCoeff hq ε δ ζ r s i j`. -/
theorem invSixJ_eq_invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v u : ℕ} {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    (hv : n + p - 2 * (r : ℕ) = v) (hk : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = k)
    (hu : m + n - 2 * (i : ℕ) = u) (hk' : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = k) :
    invSixJ hq ε δ ζ m n p k v u = invRecouplingCoeff hq ε δ ζ r s i j := by
  subst hv hu hk
  have hv₁ := isClebschGordanChannel_sub_two_mul r
  have hv₂ := isClebschGordanChannel_sub_two_mul s
  have hu₁ := isClebschGordanChannel_sub_two_mul i
  have hu₂ : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p
      (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) := isClebschGordanChannel_def.mpr ⟨j, hk'⟩
  rw [invSixJ, dite_eq_left ⟨⟨hv₁, hv₂⟩, ⟨hu₁, hu₂⟩⟩]
  exact invRecouplingCoeff_congr hq ε δ ζ (by simp) (by simp) (by simp)
    (by simp [hu₂.index_eq_of_eq hk'])

/-- `sixJ` vanishes when any of its four binary channel conditions fails. -/
@[simp] theorem sixJ_eq_zero_of_not (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k u v : ℕ}
    (h : ¬ ((IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) ∧
      (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k))) :
    sixJ hq ε δ ζ m n p k u v = 0 := by simp [sixJ, h]

/-- `invSixJ` vanishes when any of its four binary channel conditions fails. -/
@[simp] theorem invSixJ_eq_zero_of_not (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v u : ℕ}
    (h : ¬ ((IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) ∧
      (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k))) :
    invSixJ hq ε δ ζ m n p k v u = 0 := by simp [invSixJ, h]

/-- `recouplingCoeff` equals `sixJ` when the total highest weights agree, and `0` otherwise. -/
theorem recouplingCoeff_eq_ite (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p : ℕ}
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingCoeff hq ε δ ζ i j r s =
      if m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) then
        sixJ hq ε δ ζ m n p (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ))
          (m + n - 2 * (i : ℕ)) (n + p - 2 * (r : ℕ)) else 0 := by
  split_ifs with h
  · exact (sixJ_eq_recouplingCoeff hq ε δ ζ rfl rfl rfl h.symm).symm
  · exact recouplingCoeff_eq_zero_of_ne hq ε δ ζ h

/-- `invRecouplingCoeff` equals `invSixJ` when the total weights agree, and `0` otherwise. -/
theorem invRecouplingCoeff_eq_ite (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p : ℕ}
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingCoeff hq ε δ ζ r s i j =
      if m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) then
        invSixJ hq ε δ ζ m n p (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ))
          (n + p - 2 * (r : ℕ)) (m + n - 2 * (i : ℕ)) else 0 := by
  split_ifs with h
  · exact (invSixJ_eq_invRecouplingCoeff hq ε δ ζ rfl rfl rfl h.symm).symm
  · exact invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ h

/-- Change-of-decomposition (`F`-matrix) at total highest weight `k` from `LeftSixJChannel` to
`RightSixJChannel` in the `α₀ = 1` normalization of `clebschGordanInclusion`. -/
def sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ) :
    Matrix (RightSixJChannel m n p k) (LeftSixJChannel m n p k) ℂ :=
  fun v u => sixJ hq ε δ ζ m n p k u.1 v.1

/-- Inverse change-of-decomposition matrix at total weight `k` from `RightSixJChannel` to
`LeftSixJChannel` in the `α₀ = 1` normalization of `clebschGordanInclusion`. -/
def invSixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ) :
    Matrix (LeftSixJChannel m n p k) (RightSixJChannel m n p k) ℂ :=
  fun u v => invSixJ hq ε δ ζ m n p k v.1 u.1

/-- Entry formula for `sixJMatrix`. -/
@[simp] theorem sixJMatrix_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ)
    (v : RightSixJChannel m n p k) (u : LeftSixJChannel m n p k) :
    sixJMatrix hq ε δ ζ m n p k v u = sixJ hq ε δ ζ m n p k u.1 v.1 := (rfl)

/-- Entry formula for `invSixJMatrix`. -/
@[simp] theorem invSixJMatrix_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ)
    (u : LeftSixJChannel m n p k) (v : RightSixJChannel m n p k) :
    invSixJMatrix hq ε δ ζ m n p k u v = invSixJ hq ε δ ζ m n p k v.1 u.1 := (rfl)

/-! ### Orthogonality and matrix invertibility -/

/-- Orthogonality of `invSixJ` and `sixJ` summed over `v ∈ Finset.range (n + p + 1)`. -/
theorem sum_invSixJ_mul_sixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p k u₁ u₂ : ℕ}
    (hu₁ : IsClebschGordanChannel m n u₁ ∧ IsClebschGordanChannel u₁ p k)
    (hu₂ : IsClebschGordanChannel m n u₂ ∧ IsClebschGordanChannel u₂ p k) :
    ∑ v ∈ Finset.range (n + p + 1), invSixJ hq ε δ ζ m n p k v u₁ * sixJ hq ε δ ζ m n p k u₂ v =
      if u₁ = u₂ then 1 else 0 := by
  let j₁ := hu₁.2.index.cast (congrArg (min · p + 1) hu₁.1.sub_two_mul_index.symm)
  let j₂ := hu₂.2.index.cast (congrArg (min · p + 1) hu₂.1.sub_two_mul_index.symm)
  have horth := sum_invRecouplingCoeff_mul_recouplingCoeff hq ε δ ζ hu₁.1.index hu₂.1.index j₁ j₂
  have hk₁ : m + n - 2 * (hu₁.1.index : ℕ) + p - 2 * (j₁ : ℕ) = k := by
    simp [j₁, hu₁.1.sub_two_mul_index, hu₁.2.sub_two_mul_index]
  have hk₂ : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * (j₂ : ℕ) = k := by
    simp [j₂, hu₂.1.sub_two_mul_index, hu₂.2.sub_two_mul_index]
  have hinner (r : Fin (min n p + 1)) :
      (∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        invRecouplingCoeff hq ε δ ζ r s hu₁.1.index j₁ *
          recouplingCoeff hq ε δ ζ hu₂.1.index j₂ r s) =
        invSixJ hq ε δ ζ m n p k (n + p - 2 * (r : ℕ)) u₁ *
          sixJ hq ε δ ζ m n p k u₂ (n + p - 2 * (r : ℕ)) := by
    by_cases hmv : IsClebschGordanChannel m (n + p - 2 * (r : ℕ)) k
    · rw [Finset.sum_eq_single hmv.index]
      · rw [invSixJ_eq_invRecouplingCoeff hq ε δ ζ rfl hmv.sub_two_mul_index
            hu₁.1.sub_two_mul_index hk₁,
          sixJ_eq_recouplingCoeff hq ε δ ζ hu₂.1.sub_two_mul_index hk₂ rfl
            hmv.sub_two_mul_index]
      · exact fun s _ hs => by
          rw [recouplingCoeff_eq_zero_of_ne_index_right hq ε δ ζ hk₂ hmv hs, mul_zero]
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hmv h.2.2), mul_zero]
      exact Finset.sum_eq_zero fun s _ => by
        rw [recouplingCoeff_eq_zero_of_not_channel_right hq ε δ ζ hk₂ hmv, mul_zero]
  simp_rw [hinner] at horth
  rw [← sum_fin_channel_eq_sum_range n p _ fun v hnp => by
    rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hnp h.2.1), mul_zero], horth]
  have hiff : ((hu₁.1.index : ℕ) = (hu₂.1.index : ℕ) ∧ (j₁ : ℕ) = (j₂ : ℕ)) ↔ u₁ = u₂ :=
    ⟨fun ⟨hi, _⟩ => by rw [← hu₁.1.sub_two_mul_index, ← hu₂.1.sub_two_mul_index, hi],
      by rintro rfl; exact ⟨rfl, rfl⟩⟩
  simp only [hiff]

/-- Orthogonality of `sixJ` and `invSixJ` summed over `u ∈ Finset.range (m + n + 1)`. -/
theorem sum_sixJ_mul_invSixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p k v₁ v₂ : ℕ}
    (hv₁ : IsClebschGordanChannel n p v₁ ∧ IsClebschGordanChannel m v₁ k)
    (hv₂ : IsClebschGordanChannel n p v₂ ∧ IsClebschGordanChannel m v₂ k) :
    ∑ u ∈ Finset.range (m + n + 1), sixJ hq ε δ ζ m n p k u v₁ * invSixJ hq ε δ ζ m n p k v₂ u =
      if v₁ = v₂ then 1 else 0 := by
  let s₁ := hv₁.2.index.cast (congrArg (min m · + 1) hv₁.1.sub_two_mul_index.symm)
  let s₂ := hv₂.2.index.cast (congrArg (min m · + 1) hv₂.1.sub_two_mul_index.symm)
  have horth := sum_recouplingCoeff_mul_invRecouplingCoeff hq ε δ ζ hv₁.1.index hv₂.1.index s₁ s₂
  have hk₁ : m + (n + p - 2 * (hv₁.1.index : ℕ)) - 2 * (s₁ : ℕ) = k := by
    simp [s₁, hv₁.1.sub_two_mul_index, hv₁.2.sub_two_mul_index]
  have hk₂ : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * (s₂ : ℕ) = k := by
    simp [s₂, hv₂.1.sub_two_mul_index, hv₂.2.sub_two_mul_index]
  have hinner (i : Fin (min m n + 1)) :
      (∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        recouplingCoeff hq ε δ ζ i j hv₁.1.index s₁ *
          invRecouplingCoeff hq ε δ ζ hv₂.1.index s₂ i j) =
        sixJ hq ε δ ζ m n p k (m + n - 2 * (i : ℕ)) v₁ *
          invSixJ hq ε δ ζ m n p k v₂ (m + n - 2 * (i : ℕ)) := by
    by_cases hup : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k
    · rw [Finset.sum_eq_single hup.index]
      · rw [sixJ_eq_recouplingCoeff hq ε δ ζ rfl hup.sub_two_mul_index
            hv₁.1.sub_two_mul_index hk₁,
          invSixJ_eq_invRecouplingCoeff hq ε δ ζ hv₂.1.sub_two_mul_index hk₂ rfl
            hup.sub_two_mul_index]
      · exact fun j _ hj => by
          rw [invRecouplingCoeff_eq_zero_of_ne_index_left hq ε δ ζ hk₂ hup hj, mul_zero]
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hup h.1.2), zero_mul]
      exact Finset.sum_eq_zero fun j _ => by
        rw [invRecouplingCoeff_eq_zero_of_not_channel_left hq ε δ ζ hk₂ hup, mul_zero]
  simp_rw [hinner] at horth
  rw [← sum_fin_channel_eq_sum_range m n _ fun u hmn => by
    rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hmn h.1.1), zero_mul], horth]
  have hiff : ((hv₁.1.index : ℕ) = (hv₂.1.index : ℕ) ∧ (s₁ : ℕ) = (s₂ : ℕ)) ↔ v₁ = v₂ :=
    ⟨fun ⟨hr, _⟩ => by rw [← hv₁.1.sub_two_mul_index, ← hv₂.1.sub_two_mul_index, hr],
      by rintro rfl; exact ⟨rfl, rfl⟩⟩
  simp only [hiff]

/-- `invSixJMatrix` is a left inverse to `sixJMatrix`. -/
@[simp] theorem invSixJMatrix_mul_sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (m n p k : ℕ) : invSixJMatrix hq ε δ ζ m n p k * sixJMatrix hq ε δ ζ m n p k = 1 := by
  ext u₁ u₂; simp only [Matrix.mul_apply, Matrix.one_apply, invSixJMatrix_apply, sixJMatrix_apply]
  rw [Finset.sum_subtype_eq_sum_of_mem (Finset.range (n + p + 1))
    (fun _ h => Finset.mem_range.mpr (Nat.lt_succ_of_le h.1.le_add))
    (fun v => invSixJ hq ε δ ζ m n p k v u₁.1 * sixJ hq ε δ ζ m n p k u₂.1 v)
    (fun _ _ hv => by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hv h.2), mul_zero]),
    sum_invSixJ_mul_sixJ hq ε δ ζ u₁.2 u₂.2]; simp [Subtype.ext_iff]

/-- `invSixJMatrix` is a right inverse to `sixJMatrix`. -/
@[simp] theorem sixJMatrix_mul_invSixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (m n p k : ℕ) : sixJMatrix hq ε δ ζ m n p k * invSixJMatrix hq ε δ ζ m n p k = 1 := by
  ext v₁ v₂; simp only [Matrix.mul_apply, Matrix.one_apply, sixJMatrix_apply, invSixJMatrix_apply]
  rw [Finset.sum_subtype_eq_sum_of_mem (Finset.range (m + n + 1))
    (fun _ h => Finset.mem_range.mpr (Nat.lt_succ_of_le h.1.le_add))
    (fun u => sixJ hq ε δ ζ m n p k u v₁.1 * invSixJ hq ε δ ζ m n p k v₂.1 u)
    (fun _ _ hu => by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hu h.1), zero_mul]),
    sum_sixJ_mul_invSixJ hq ε δ ζ v₁.2 v₂.2]; simp [Subtype.ext_iff]

/-- Left and right triple-product decompositions have the same multiplicity at every total
highest weight `k`. -/
theorem card_leftSixJChannel_eq_card_rightSixJChannel (m n p k : ℕ) :
    Fintype.card (LeftSixJChannel m n p k) = Fintype.card (RightSixJChannel m n p k) := by
  -- Specialize `sixJMatrix` and `invSixJMatrix` to `q = 2` with trivial signs: their two-sided
  -- inverse relation has trace `card LeftSixJChannel` in one order and `card RightSixJChannel` in
  -- the other, and `Matrix.trace_mul_comm` equates them in characteristic zero.
  have hq2 : IsGenericQuantumParameter (2 : ℂ) :=
    isGenericQuantumParameter_iff.mpr ⟨by norm_num, fun r hr hpow => by
      have hnat : 2 ^ r = 1 := Nat.cast_injective (R := ℂ) (by simpa using hpow)
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hr; omega⟩
  have htr :=
    Matrix.trace_mul_comm (invSixJMatrix hq2 1 1 1 m n p k) (sixJMatrix hq2 1 1 1 m n p k)
  rw [invSixJMatrix_mul_sixJMatrix, sixJMatrix_mul_invSixJMatrix, Matrix.trace_one,
    Matrix.trace_one] at htr
  exact Nat.cast_injective (R := ℂ) (by simpa using htr)

/-! ### Explicit boundary evaluations -/

/-- On the leading stretched channel `k = m + n + p` (`u = m + n`, `v = n + p`), `sixJ` is `1`. -/
@[simp] theorem sixJ_add_add (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p : ℕ) :
    sixJ hq ε δ ζ m n p (m + n + p) (m + n) (n + p) = 1 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  rw [sixJ_eq_recouplingCoeff (i := 0) (j := 0) (r := 0) (s := 0) hq ε δ ζ
    (by simp) (by simp) (by simp) (by simp [Nat.add_assoc])]
  have h0 : assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)
        (clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq 0 0 (vec q _ _ 0)) =
      clebschGordanRightInclusion hq 0 0 (vec q _ _ 0) := by
    rw [clebschGordanLeftInclusion_zero_vec_zero, clebschGordanRightInclusion_zero_vec_zero]; simp
  rw [recouplingCoeff_def]; refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    h0, clebschGordanRightProjection_inclusion_self, one_smul]

/-- When the first factor is `L_0^ε`, `sixJ` on any admissible channel `k` of `L_n^δ ⊗ L_p^ζ`
equals `1`. -/
@[simp] theorem sixJ_zero_left (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {n p k : ℕ}
    (hk : IsClebschGordanChannel n p k) : sixJ hq ε δ ζ 0 n p k n k = 1 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  let j₀ : Fin (min (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) p + 1) := hk.index.cast (by simp)
  have hj₀ : (j₀ : ℕ) = (hk.index : ℕ) := Fin.val_cast _ _
  rw [sixJ_eq_recouplingCoeff (i := 0) (j := j₀) (r := hk.index) (s := 0) hq ε δ ζ
    (by simp) (by simp [hj₀, hk.sub_two_mul_index]) hk.sub_two_mul_index
    (by simp [hk.sub_two_mul_index])]
  rw [recouplingCoeff_def]; refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hvec : tensorMap ℂ (UqSl2 q)
        (clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0) LinearMap.id
        (clebschGordanVector q _ (ε * δ) p ζ j₀) =
      (assoc ℂ (UqSl2 q) (LadderModule q 0 ε) (LadderModule q n δ) (LadderModule q p ζ)).symm
        (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (clebschGordanVector q n δ p ζ hk.index)) := by
    rw [clebschGordanVector_def, assoc_symm_tmul_clebschGordanVector, hj₀, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_zero_left_vec hq a]; congr 2; simp
  rw [hvec, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    ← clebschGordanRightInclusion_zero_vec_zero (m := 0) (ε := ε) (δ := δ) (ζ := ζ) hq hk.index,
    clebschGordanRightProjection_inclusion_self, one_smul]

/-- When the third factor is `L_0^ζ`, `sixJ` on an admissible channel `k` of `L_m^ε ⊗ L_n^δ`
equals `ζ^((m + n - k) / 2)`, reflecting the `K⁻¹` factor in `ΔF = F ⊗ K⁻¹ + 1 ⊗ F`. -/
@[simp] theorem sixJ_zero_right (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n k : ℕ}
    (hk : IsClebschGordanChannel m n k) :
    sixJ hq ε δ ζ m n 0 k k n = (ζ : ℂ) ^ ((m + n - k) / 2) := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  let s₀ : Fin (min m (n + 0 - 2 * ↑(0 : Fin (min n 0 + 1))) + 1) := hk.index.cast (by simp)
  have hs₀ : (s₀ : ℕ) = (hk.index : ℕ) := Fin.val_cast _ _
  rw [← hk.val_index, sixJ_eq_recouplingCoeff (i := hk.index) (j := 0) (r := 0) (s := s₀)
    hq ε δ ζ hk.sub_two_mul_index (by simp [hk.sub_two_mul_index]) (by simp)
    (by simp [hs₀, hk.sub_two_mul_index])]
  rw [recouplingCoeff_def]; refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_zero_vec_zero, LinearEquiv.coe_toLinearMap,
    assoc_clebschGordanVector_tmul]
  have hright : ((ζ : ℂ) ^ (hk.index : ℕ)) • clebschGordanRightInclusion (m := m) (n := n) (p := 0)
        (ε := ε) (δ := δ) (ζ := ζ) hq 0 s₀ (vec q _ _ 0) =
      ∑ a ∈ Finset.range ((hk.index : ℕ) + 1), clebschGordanCoeff q m n δ hk.index a •
        tmul ℂ (UqSl2 q) (vec q m ε a)
          (tmul ℂ (UqSl2 q) (vec q n δ ((hk.index : ℤ) - a)) (vec q 0 ζ 0)) := by
    have hζsq : ((ζ : ℂ) ^ (hk.index : ℕ)) * ((ζ : ℂ) ^ (hk.index : ℕ)) = 1 := by
      rw [← mul_pow]; rcases Int.units_eq_one_or ζ with rfl | rfl <;> simp
    rw [clebschGordanRightInclusion_vec_zero, clebschGordanVector_def, map_sum, hs₀,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hle := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hpow : (ζ : ℂ) ^ a * (ζ : ℂ) ^ ((hk.index : ℕ) - a) = (ζ : ℂ) ^ (hk.index : ℕ) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    rw [LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply, ← Nat.cast_sub hle,
      clebschGordanInclusion_zero_right_vec (ε := δ) (δ := ζ) hq ((hk.index : ℕ) - a)]
    simp only [Fin.val_zero, mul_zero, add_zero, tsub_zero,
      clebschGordanCoeff_mul_sign m n δ ζ hk.index a, tmul_smul, smul_smul]
    congr 1
    linear_combination (ζ : ℂ) ^ (hk.index : ℕ) * clebschGordanCoeff q m n δ hk.index a * hpow +
      clebschGordanCoeff q m n δ hk.index a * hζsq
  rw [← hright, LinearMap.map_smul_of_tower, clebschGordanRightProjection_inclusion_self]

/-! ### Fundamental `2 × 2` spin-`1/2` evaluation -/

private def tripleRightCoord [Fact (q ≠ 0)] (ε δ ζ : ℤˣ) (i j k : Fin 2) :
    Tensor ℂ (UqSl2 q) (LadderModule q 1 ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ)) →ₗ[ℂ] ℂ :=
  ((Finsupp.lapply (i, (j, k))).comp
    ((basis q 1 ε).tensorProduct ((basis q 1 δ).tensorProduct (basis q 1 ζ))).repr.toLinearMap).comp
    (((TensorProduct.congr (LinearEquiv.refl ℂ _)
      (tensorEquiv ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ))).toLinearMap).comp
      (tensorEquiv ℂ (UqSl2 q) (LadderModule q 1 ε) _).toLinearMap)

private theorem tripleRightCoord_tmul [Fact (q ≠ 0)] (ε δ ζ : ℤˣ) (i j k : Fin 2) (a b c : ℤ) :
    tripleRightCoord ε δ ζ i j k
        (tmul ℂ (UqSl2 q) (vec q 1 ε a) (tmul ℂ (UqSl2 q) (vec q 1 δ b) (vec q 1 ζ c))) =
      (if (i : ℤ) = a then 1 else 0) *
        ((if (j : ℤ) = b then 1 else 0) * (if (k : ℤ) = c then 1 else 0)) := by
  simp only [tripleRightCoord, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, tensorEquiv_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, basis_repr_vec, smul_eq_mul]
  split_ifs <;> simp_all

private def rightVecZero [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :=
  clebschGordanRightInclusion (m := 1) (n := 1) (p := 1) (ε := ε) (δ := δ) (ζ := ζ) hq
    ⟨1, by decide⟩ 0 (vec q _ _ 0)

private def rightVecTwo [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :=
  clebschGordanRightInclusion (m := 1) (n := 1) (p := 1) (ε := ε) (δ := δ) (ζ := ζ) hq
    0 ⟨1, by decide⟩ (vec q _ _ 0)

private theorem assoc_spinHalf_leftInclusion_vec_zero [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min 1 1 + 1)) (j : Fin (min (1 + 1 - 2 * (i : ℕ)) 1 + 1))
    (hk : 1 + 1 - 2 * (i : ℕ) + 1 - 2 * (j : ℕ) = 1) :
    assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ)
        (clebschGordanLeftInclusion (ε := ε) (δ := δ) (ζ := ζ) hq i j (vec q _ _ 0)) =
      sixJ hq ε δ ζ 1 1 1 1 (2 - 2 * (i : ℕ)) 0 • rightVecZero hq ε δ ζ +
        sixJ hq ε δ ζ 1 1 1 1 (2 - 2 * (i : ℕ)) 2 • rightVecTwo hq ε δ ζ := by
  let r₁ : Fin (min 1 1 + 1) := ⟨1, by decide⟩
  let s₀₁ : Fin (min 1 (1 + 1 - 2 * ((0 : Fin (min 1 1 + 1)) : ℕ)) + 1) := ⟨1, by decide⟩
  have hr : (Finset.univ : Finset (Fin (min 1 1 + 1))) = {0, r₁} := by decide
  have hs₀ : (Finset.univ : Finset (Fin (min 1 (1 + 1 - 2 * ((0 : Fin (min 1 1 + 1)) : ℕ)) + 1))) =
      {0, s₀₁} := by decide
  have hs₁ : (Finset.univ : Finset (Fin (min 1 (1 + 1 - 2 * (r₁ : ℕ)) + 1))) = {0} := by decide
  have hne_r : (0 : Fin (min 1 1 + 1)) ≠ r₁ := by decide
  have hne_s : (0 : Fin (min 1 (1 + 1 - 2 * ((0 : Fin (min 1 1 + 1)) : ℕ)) + 1)) ≠ s₀₁ := by decide
  rw [assoc_clebschGordanLeftInclusion_vec, hr, Finset.sum_pair hne_r,
    hs₀, Finset.sum_pair hne_s, hs₁, Finset.sum_singleton,
    recouplingCoeff_eq_zero_of_ne hq ε δ ζ (by simp [hk]), zero_smul, zero_add,
    ← sixJ_eq_recouplingCoeff (k := 1) (u := 2 - 2 * (i : ℕ)) (v := 2)
      (r := 0) (s := s₀₁) hq ε δ ζ rfl hk rfl rfl,
    ← sixJ_eq_recouplingCoeff (k := 1) (u := 2 - 2 * (i : ℕ)) (v := 0)
      (r := r₁) (s := 0) hq ε δ ζ rfl hk rfl rfl,
    add_comm]
  rfl

private theorem spinHalf_clebschGordanVector_one [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanVector q 1 ε₁ 1 ε₂ 1 =
      tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) +
        (-(ε₂ : ℂ) * q) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) := by
  simpa [quantumInteger_one hq.sub_inv_ne_zero] using
    clebschGordanVector_one (q := q) 1 ε₁ 1 ε₂

private theorem spinHalfSym_vec_one [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq 0 (vec q 2 (ε₁ * ε₂) 1) =
      ((ε₂ : ℂ) * q⁻¹) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) +
        tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) := by
  refine (clebschGordanInclusion_vec (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq 0 1).trans ?_
  rw [quantumFactorial_one, clebschGordanVector_def, Fin.val_zero, Finset.sum_range_one]
  simp [quantumInteger_one hq.sub_inv_ne_zero, f_smul_tmul, f_smul_vec, kInv_smul_vec]

private theorem rightVecZero_coords [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tripleRightCoord ε δ ζ 0 0 1 (rightVecZero hq ε δ ζ) = 1 ∧
      tripleRightCoord ε δ ζ 1 0 0 (rightVecZero hq ε δ ζ) = 0 := by
  rw [rightVecZero, clebschGordanRightInclusion_zero_vec_zero, Fin.val_mk,
    spinHalf_clebschGordanVector_one hq δ ζ]
  simp only [tmul_add, tmul_smul, map_add, map_smul, tripleRightCoord_tmul, smul_eq_mul]
  norm_num

private theorem rightVecTwo_coords [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tripleRightCoord ε δ ζ 0 0 1 (rightVecTwo hq ε δ ζ) = 1 ∧
      tripleRightCoord ε δ ζ 1 0 0 (rightVecTwo hq ε δ ζ) =
        -(δ : ℂ) * (ζ : ℂ) * q * quantumInteger q 2 := by
  have hin : clebschGordanVector q 1 ε 2 (δ * ζ) 1 =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0) (vec q 2 (δ * ζ) 1) +
        (-(δ : ℂ) * (ζ : ℂ) * q * quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 1) (vec q 2 (δ * ζ) 0) := by
    simpa [quantumInteger_one hq.sub_inv_ne_zero, mul_assoc] using
      clebschGordanVector_one (q := q) 1 ε 2 (δ * ζ)
  have h00 : clebschGordanInclusion (m := 1) (n := 1) (ε := δ) (δ := ζ) hq 0 (vec q 2 (δ * ζ) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0) := by
    simpa using clebschGordanInclusion_vec_zero (m := 1) (n := 1) (ε := δ) (δ := ζ) hq 0
  rw [rightVecTwo, clebschGordanRightInclusion_vec_zero]
  simp only [Fin.val_zero, hin, map_add, LinearMap.map_smul_of_tower, tensorMap_tmul,
    LinearMap.id_apply]
  rw [spinHalfSym_vec_one, h00]
  simp only [tmul_add, tmul_smul, map_add, map_smul, tripleRightCoord_tmul, smul_eq_mul]
  constructor <;> norm_num

private theorem spinHalf_zero_eq [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0)) +
        (-(δ : ℂ) * q) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) =
      sixJ hq ε δ ζ 1 1 1 1 0 0 • rightVecZero hq ε δ ζ +
        sixJ hq ε δ ζ 1 1 1 1 0 2 • rightVecTwo hq ε δ ζ := by
  have hexp :=
    assoc_spinHalf_leftInclusion_vec_zero hq ε δ ζ ⟨1, by decide⟩ 0 (by simp)
  rw [clebschGordanLeftInclusion_zero_vec_zero, Fin.val_mk,
    spinHalf_clebschGordanVector_one hq ε δ] at hexp
  simpa only [mul_one, tsub_self, add_tmul, ← smul_tmul', map_add,
    LinearMapClass.map_smul_of_tower (S := UqSl2 q), assoc_tmul] using hexp

private theorem spinHalf_two_eq [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 1)) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          (((δ : ℂ) * q⁻¹) •
              tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) +
            tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0))) =
      sixJ hq ε δ ζ 1 1 1 1 2 0 • rightVecZero hq ε δ ζ +
        sixJ hq ε δ ζ 1 1 1 1 2 2 • rightVecTwo hq ε δ ζ := by
  have hexp :=
    assoc_spinHalf_leftInclusion_vec_zero hq ε δ ζ 0 ⟨1, by decide⟩ (by simp)
  have hin : clebschGordanVector q 2 (ε * δ) 1 ζ 1 =
      tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 0) (vec q 1 ζ 1) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 1) (vec q 1 ζ 0) := by
    simpa [quantumInteger_one hq.sub_inv_ne_zero] using
      clebschGordanVector_one (q := q) 2 (ε * δ) 1 ζ
  have h00 : clebschGordanInclusion (m := 1) (n := 1) (ε := ε) (δ := δ) hq 0 (vec q 2 (ε * δ) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0) (vec q 1 δ 0) := by
    simpa using clebschGordanInclusion_vec_zero (m := 1) (n := 1) (ε := ε) (δ := δ) hq 0
  rw [clebschGordanLeftInclusion_vec_zero] at hexp
  simp only [Fin.val_zero, mul_zero, tsub_zero, hin, map_add,
    LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply] at hexp
  rw [h00, spinHalfSym_vec_one] at hexp
  simpa only [add_tmul, ← smul_tmul', map_add, LinearMapClass.map_smul_of_tower (S := UqSl2 q),
    assoc_tmul] using hexp

/-- Entry `(u = 0, v = 2)` of the `2 × 2` spin-`1/2` `sixJ` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total highest weight `1`. -/
@[simp] theorem sixJ_one_one_one_zero_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJ hq ε δ ζ 1 1 1 1 0 2 = (ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hc := congrArg (tripleRightCoord ε δ ζ 1 0 0) (spinHalf_zero_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).2,
    (rightVecTwo_coords hq ε δ ζ).2, tripleRightCoord_tmul, smul_eq_mul] at hc
  norm_num at hc
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  have hζ2 : (ζ : ℂ) * (ζ : ℂ) = 1 := by rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num
  rw [eq_mul_inv_iff_mul_eq₀ hq2]
  apply mul_left_cancel₀ (mul_ne_zero
    (mul_ne_zero (Int.cast_ne_zero.mpr δ.ne_zero) (Int.cast_ne_zero.mpr ζ.ne_zero)) hq.ne_zero)
  linear_combination -hc - (δ : ℂ) * q * hζ2

/-- Entry `(u = 0, v = 0)` of the `2 × 2` spin-`1/2` `sixJ` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total highest weight `1`. -/
@[simp] theorem sixJ_one_one_one_zero_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJ hq ε δ ζ 1 1 1 1 0 0 = -(ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hc := congrArg (tripleRightCoord ε δ ζ 0 0 1) (spinHalf_zero_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).1,
    (rightVecTwo_coords hq ε δ ζ).1, tripleRightCoord_tmul,
    sixJ_one_one_one_zero_two hq ε δ ζ, smul_eq_mul] at hc
  norm_num at hc; linear_combination -hc

/-- Entry `(u = 2, v = 2)` of the `2 × 2` spin-`1/2` `sixJ` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total highest weight `1`. -/
@[simp] theorem sixJ_one_one_one_two_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJ hq ε δ ζ 1 1 1 1 2 2 = (quantumInteger q 2 ^ 2)⁻¹ := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hc := congrArg (tripleRightCoord ε δ ζ 1 0 0) (spinHalf_two_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).2,
    (rightVecTwo_coords hq ε δ ζ).2, tripleRightCoord_tmul, smul_eq_mul] at hc
  norm_num at hc
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  apply mul_left_cancel₀ (mul_ne_zero
    (mul_ne_zero (Int.cast_ne_zero.mpr δ.ne_zero) (Int.cast_ne_zero.mpr ζ.ne_zero))
    (mul_ne_zero hq0 hq2))
  field_simp [hq0, hq2] at hc ⊢; linear_combination hc

/-- Entry `(u = 2, v = 0)` of the `2 × 2` spin-`1/2` `sixJ` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total highest weight `1`. -/
@[simp] theorem sixJ_one_one_one_two_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJ hq ε δ ζ 1 1 1 1 2 0 = 1 - (quantumInteger q 2 ^ 2)⁻¹ := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hc := congrArg (tripleRightCoord ε δ ζ 0 0 1) (spinHalf_two_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).1,
    (rightVecTwo_coords hq ε δ ζ).1, tripleRightCoord_tmul,
    sixJ_one_one_one_two_two hq ε δ ζ, smul_eq_mul] at hc
  norm_num at hc; linear_combination -hc

private theorem sixJ_mul_invSixJ_spinHalf (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {v₁ v₂ : ℕ} (hv₁ : v₁ = 0 ∨ v₁ = 2) (hv₂ : v₂ = 0 ∨ v₂ = 2) :
    sixJ hq ε δ ζ 1 1 1 1 0 v₁ * invSixJ hq ε δ ζ 1 1 1 1 v₂ 0 +
      sixJ hq ε δ ζ 1 1 1 1 2 v₁ * invSixJ hq ε δ ζ 1 1 1 1 v₂ 2 =
      if v₁ = v₂ then 1 else 0 := by
  have hch {v : ℕ} (hv : v = 0 ∨ v = 2) :
      IsClebschGordanChannel 1 1 v ∧ IsClebschGordanChannel 1 v 1 := by
    rcases hv with rfl | rfl <;> decide
  have horth := sum_sixJ_mul_invSixJ hq ε δ ζ (hch hv₁) (hch hv₂)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    sixJ_eq_zero_of_not (u := 1) hq ε δ ζ (fun h => by
      revert h; rcases hv₁ with rfl | rfl <;> decide),
    zero_mul, add_zero] at horth
  exact horth

/-- Entry `(v = 0, u = 2)` of the inverse `2 × 2` spin-`1/2` matrix `invSixJ` on
`L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at total highest weight `1`. -/
@[simp] theorem invSixJ_one_one_one_zero_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    invSixJ hq ε δ ζ 1 1 1 1 0 2 = 1 := by
  have h₀ := sixJ_mul_invSixJ_spinHalf hq ε δ ζ (.inl rfl) (.inl rfl)
  have h₂ := sixJ_mul_invSixJ_spinHalf hq ε δ ζ (.inr rfl) (.inl rfl)
  simp only [sixJ_one_one_one_zero_zero, sixJ_one_one_one_two_zero, sixJ_one_one_one_zero_two,
    sixJ_one_one_one_two_two] at h₀ h₂
  norm_num at h₀ h₂; linear_combination h₀ + h₂

/-- Entry `(v = 2, u = 2)` of the inverse `2 × 2` spin-`1/2` matrix `invSixJ` on
`L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at total highest weight `1`. -/
@[simp] theorem invSixJ_one_one_one_two_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    invSixJ hq ε δ ζ 1 1 1 1 2 2 = 1 := by
  have h₀ := sixJ_mul_invSixJ_spinHalf hq ε δ ζ (.inl rfl) (.inr rfl)
  have h₂ := sixJ_mul_invSixJ_spinHalf hq ε δ ζ (.inr rfl) (.inr rfl)
  simp only [sixJ_one_one_one_zero_zero, sixJ_one_one_one_two_zero, sixJ_one_one_one_zero_two,
    sixJ_one_one_one_two_two] at h₀ h₂
  norm_num at h₀ h₂; linear_combination h₀ + h₂

/-- Entry `(v = 0, u = 0)` of the inverse `2 × 2` spin-`1/2` matrix `invSixJ` on
`L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at total highest weight `1`. -/
@[simp] theorem invSixJ_one_one_one_zero_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    invSixJ hq ε δ ζ 1 1 1 1 0 0 = -(ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  have h₂ := sixJ_mul_invSixJ_spinHalf hq ε δ ζ (.inr rfl) (.inl rfl)
  simp only [sixJ_one_one_one_zero_two, sixJ_one_one_one_two_two,
    invSixJ_one_one_one_zero_two] at h₂
  norm_num at h₂
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  have hζ2 : (ζ : ℂ) * (ζ : ℂ) = 1 := by rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num
  field_simp [hq2] at h₂ ⊢
  linear_combination (ζ : ℂ) * h₂ - quantumInteger q 2 * invSixJ hq ε δ ζ 1 1 1 1 0 0 * hζ2

/-- Entry `(v = 2, u = 0)` of the inverse `2 × 2` spin-`1/2` matrix `invSixJ` on
`L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at total highest weight `1`. -/
@[simp] theorem invSixJ_one_one_one_two_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    invSixJ hq ε δ ζ 1 1 1 1 2 0 = (ζ : ℂ) * (quantumInteger q 2 - (quantumInteger q 2)⁻¹) := by
  have h₂ := sixJ_mul_invSixJ_spinHalf hq ε δ ζ (.inr rfl) (.inr rfl)
  simp only [sixJ_one_one_one_zero_two, sixJ_one_one_one_two_two,
    invSixJ_one_one_one_two_two] at h₂
  norm_num at h₂
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  have hζ2 : (ζ : ℂ) * (ζ : ℂ) = 1 := by rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num
  field_simp [hq2] at h₂ ⊢
  linear_combination (ζ : ℂ) * h₂ - quantumInteger q 2 * invSixJ hq ε δ ζ 1 1 1 1 2 0 * hζ2

end SixJ

/-! ### Coupled normalized `F`-ladder bases and associator matrices -/

/-- Index type `(i, j, l)` for the coupled normalized `F`-ladder basis of
`(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
abbrev ClebschGordanLeftBasisIndex (m n p : ℕ) : Type :=
  Σ i : Fin (min m n + 1),
    Σ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
      Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)

/-- Index type `(r, s, l)` for the coupled normalized `F`-ladder basis of
`L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
abbrev ClebschGordanRightBasisIndex (m n p : ℕ) : Type :=
  Σ r : Fin (min n p + 1),
    Σ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
      Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)

section CoupledBasis

variable {q : ℂ} [Fact (q ≠ 0)]

/-- Coupled normalized `F`-ladder basis of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`, transporting the channelwise
ladder bases across `clebschGordanLeftEquiv`. -/
def clebschGordanLeftBasis (hq : IsGenericQuantumParameter q) (m n p : ℕ) (ε δ ζ : ℤˣ) :
    Module.Basis (ClebschGordanLeftBasisIndex m n p) ℂ
      (Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ)) :=
  (Pi.basis fun i : Fin (min m n + 1) =>
    Pi.basis fun j : Fin (min (m + n - 2 * (i : ℕ)) p + 1) =>
      basis q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)).map
    ((clebschGordanLeftEquiv hq).restrictScalars ℂ)

/-- Coupled normalized `F`-ladder basis of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`, transporting the channelwise
ladder bases across `clebschGordanRightEquiv`. -/
def clebschGordanRightBasis (hq : IsGenericQuantumParameter q) (m n p : ℕ) (ε δ ζ : ℤˣ) :
    Module.Basis (ClebschGordanRightBasisIndex m n p) ℂ
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ))) :=
  (Pi.basis fun r : Fin (min n p + 1) =>
    Pi.basis fun s : Fin (min m (n + p - 2 * (r : ℕ)) + 1) =>
      basis q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))).map
    ((clebschGordanRightEquiv hq).restrictScalars ℂ)

/-- Explicit formula for the `(i, j, l)` element of `clebschGordanLeftBasis`. -/
@[simp] theorem clebschGordanLeftBasis_apply (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (l : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    clebschGordanLeftBasis hq m n p ε δ ζ ⟨i, j, l⟩ =
      clebschGordanLeftInclusion hq i j (vec q _ ((ε * δ) * ζ) l) := by
  simp [clebschGordanLeftBasis, Pi.basis_apply, vec_coe, clebschGordanLeftInclusion_eq_single]

/-- Explicit formula for the `(r, s, l)` element of `clebschGordanRightBasis`. -/
@[simp] theorem clebschGordanRightBasis_apply (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    clebschGordanRightBasis hq m n p ε δ ζ ⟨r, s, l⟩ =
      clebschGordanRightInclusion hq r s (vec q _ (ε * (δ * ζ)) l) := by
  simp [clebschGordanRightBasis, Pi.basis_apply, vec_coe, clebschGordanRightInclusion_eq_single]

/-- Coordinate `(i, j, l)` in `clebschGordanLeftBasis` is the `l`-th ladder coordinate of the
`(i, j)` left-channel projection. -/
@[simp] theorem clebschGordanLeftBasis_repr_apply (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (x : Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
      (LadderModule q p ζ))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (l : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    (clebschGordanLeftBasis hq m n p ε δ ζ).repr x ⟨i, j, l⟩ =
      (basis q _ ((ε * δ) * ζ)).repr (clebschGordanLeftProjection hq i j x) l := by
  simp [clebschGordanLeftBasis, Pi.basis_repr, clebschGordanLeftProjection_eq_symm]

/-- Coordinate `(r, s, l)` in `clebschGordanRightBasis` is the `l`-th ladder coordinate of the
`(r, s)` right-channel projection. -/
@[simp] theorem clebschGordanRightBasis_repr_apply (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ)))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    (clebschGordanRightBasis hq m n p ε δ ζ).repr x ⟨r, s, l⟩ =
      (basis q _ (ε * (δ * ζ))).repr (clebschGordanRightProjection hq r s x) l := by
  simp [clebschGordanRightBasis, Pi.basis_repr, clebschGordanRightProjection_eq_symm]

/-- Matrix of the coproduct tensor associator `BialgebraModule.assoc` in the coupled normalized
`F`-ladder bases: entries are block-diagonal in total highest weight and `F`-ladder index, with
diagonal entries given by `sixJ`. -/
theorem toMatrix_assoc_clebschGordanBasis (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    LinearMap.toMatrix (clebschGordanLeftBasis hq m n p ε δ ζ)
        (clebschGordanRightBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).toLinearMap.restrictScalars ℂ) ⟨r, s, l⟩ ⟨i, j, k⟩ =
      if m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) ∧
          (l : ℕ) = (k : ℕ) then
        sixJ hq ε δ ζ m n p (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ))
          (m + n - 2 * (i : ℕ)) (n + p - 2 * (r : ℕ))
      else 0 := by
  have hrec : clebschGordanRightProjection hq r s
      (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)
        (clebschGordanLeftInclusion hq i j (vec q _ ((ε * δ) * ζ) k))) =
      recouplingCoeff hq ε δ ζ i j r s • vec q _ (ε * (δ * ζ)) k := by
    simpa [recouplingHom_def] using recouplingHom_vec (ε := ε) (δ := δ) (ζ := ζ) hq i j r s k
  rw [LinearMap.toMatrix_apply, clebschGordanLeftBasis_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap, clebschGordanRightBasis_repr_apply, hrec, map_smul,
    Finsupp.smul_apply, basis_repr_vec, smul_eq_mul, recouplingCoeff_eq_ite]
  norm_cast; split_ifs <;> simp_all

/-- Matrix of `(BialgebraModule.assoc).symm` in the coupled normalized `F`-ladder bases: entries
are block-diagonal in total highest weight and `F`-ladder index, with diagonal entries given by
`invSixJ`. -/
theorem toMatrix_assoc_symm_clebschGordanBasis (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    LinearMap.toMatrix (clebschGordanRightBasis hq m n p ε δ ζ)
        (clebschGordanLeftBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).symm.toLinearMap.restrictScalars ℂ) ⟨i, j, k⟩ ⟨r, s, l⟩ =
      if m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) ∧
          (k : ℕ) = (l : ℕ) then
        invSixJ hq ε δ ζ m n p (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ))
          (n + p - 2 * (r : ℕ)) (m + n - 2 * (i : ℕ))
      else 0 := by
  have hinv : clebschGordanLeftProjection hq i j
      ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)).symm
        (clebschGordanRightInclusion hq r s (vec q _ (ε * (δ * ζ)) l))) =
      invRecouplingCoeff hq ε δ ζ r s i j • vec q _ ((ε * δ) * ζ) l := by
    simpa [invRecouplingHom_def] using invRecouplingHom_vec (ε := ε) (δ := δ) (ζ := ζ) hq r s i j l
  rw [LinearMap.toMatrix_apply, clebschGordanRightBasis_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap, clebschGordanLeftBasis_repr_apply, hinv, map_smul,
    Finsupp.smul_apply, basis_repr_vec, smul_eq_mul, invRecouplingCoeff_eq_ite]
  norm_cast; split_ifs <;> simp_all

end CoupledBasis

end TauCeti.UqSl2
