/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling

/-!
# Quantum 6j change-of-decomposition matrices

At a generic parameter `q`, indexing the triple-product recoupling scalars `recouplingCoeff` and
`invRecouplingCoeff` on `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` by intermediate highest weights `u` and `v` at
fixed total highest weight `k` yields the six-weight quantum 6j functions `sixJ` and `invSixJ`
(extended by `0` outside admissible Clebsch–Gordan channels) and the two-sided inverse matrices
`sixJMatrix` and `invSixJMatrix`.

* `TauCeti.UqSl2.IsClebschGordanChannel`, `isClebschGordanChannel_iff`: binary channel predicate.
* `TauCeti.UqSl2.sixJ`, `invSixJ`, `sixJMatrix`, `invSixJMatrix`: quantum 6j scalars and matrices.
* `TauCeti.UqSl2.invSixJMatrix_mul_sixJMatrix`, `sixJMatrix_mul_invSixJMatrix`: matrix inverses.
* `TauCeti.UqSl2.sixJ_add_add`, `sixJ_zero_left`, `sixJ_zero_right`: explicit boundary values.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, World Scientific, 1989, pp. 285--339.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

/-! ### Admissible Clebsch–Gordan channels -/

/-- `IsClebschGordanChannel m n k` holds when `L_k` occurs in the binary Clebsch–Gordan
decomposition of `L_m ⊗ L_n`, i.e., `k = m + n - 2j` for some `j ≤ min m n`. -/
def IsClebschGordanChannel (m n k : ℕ) : Prop :=
  ∃ j : Fin (min m n + 1), m + n - 2 * (j : ℕ) = k

/-- Definitional characterization of `IsClebschGordanChannel`. -/
theorem isClebschGordanChannel_def {m n k : ℕ} :
    IsClebschGordanChannel m n k ↔ ∃ j : Fin (min m n + 1), m + n - 2 * (j : ℕ) = k := Iff.rfl

instance (m n : ℕ) : DecidablePred (IsClebschGordanChannel m n) :=
  fun _ => decidable_of_iff _ isClebschGordanChannel_def.symm

/-- Every Clebsch–Gordan channel of `L_m ⊗ L_n` has highest weight at most `m + n`. -/
theorem IsClebschGordanChannel.le_add {m n k : ℕ} (h : IsClebschGordanChannel m n k) :
    k ≤ m + n := by rcases h with ⟨_, rfl⟩; omega

/-- Triangle and parity characterization of admissible binary Clebsch–Gordan channels. -/
theorem isClebschGordanChannel_iff {m n k : ℕ} :
    IsClebschGordanChannel m n k ↔
      k ≤ m + n ∧ m ≤ n + k ∧ n ≤ m + k ∧ Even (m + n - k) := by
  constructor
  · rintro ⟨j, rfl⟩; have := j.isLt; exact ⟨by omega, by omega, by omega, ⟨j, by omega⟩⟩
  · rintro ⟨_, _, _, r, _⟩; exact ⟨⟨r, by omega⟩, by dsimp only; omega⟩

/-- The unique summand index `j : Fin (min m n + 1)` witnessing `k = m + n - 2j`, computed
explicitly as `(m + n - k) / 2`. -/
def IsClebschGordanChannel.index {m n k : ℕ} (h : IsClebschGordanChannel m n k) :
    Fin (min m n + 1) :=
  ⟨(m + n - k) / 2, by rcases h with ⟨j, rfl⟩; have := j.isLt; omega⟩

/-- The constructive index of an admissible channel recovers its highest weight `k`. -/
@[simp] theorem IsClebschGordanChannel.sub_two_mul_index {m n k : ℕ}
    (h : IsClebschGordanChannel m n k) : m + n - 2 * (h.index : ℕ) = k := by
  rcases h with ⟨j, rfl⟩; have := j.isLt; simp only [index]; omega

/-- Given `hu₁ : IsClebschGordanChannel m n u` and `hu₂ : IsClebschGordanChannel u p k`,
`hu₂.leftIndex hu₁` views `hu₂.index` in `Fin (min (m + n - 2 * ↑hu₁.index) p + 1)`. -/
def IsClebschGordanChannel.leftIndex {m n p u k : ℕ}
    (hu₂ : IsClebschGordanChannel u p k) (hu₁ : IsClebschGordanChannel m n u) :
    Fin (min (m + n - 2 * (hu₁.index : ℕ)) p + 1) :=
  ⟨hu₂.index, by rw [hu₁.sub_two_mul_index]; exact hu₂.index.isLt⟩

/-- Given `hv₁ : IsClebschGordanChannel n p v` and `hv₂ : IsClebschGordanChannel m v k`,
`hv₂.rightIndex hv₁` views `hv₂.index` in `Fin (min m (n + p - 2 * ↑hv₁.index) + 1)`. -/
def IsClebschGordanChannel.rightIndex {m n p v k : ℕ}
    (hv₂ : IsClebschGordanChannel m v k) (hv₁ : IsClebschGordanChannel n p v) :
    Fin (min m (n + p - 2 * (hv₁.index : ℕ)) + 1) :=
  ⟨hv₂.index, by rw [hv₁.sub_two_mul_index]; exact hv₂.index.isLt⟩

/-- `hu₂.leftIndex hu₁` has the same underlying natural-number value as `hu₂.index`. -/
@[simp] theorem IsClebschGordanChannel.val_leftIndex {m n p u k : ℕ}
    (hu₂ : IsClebschGordanChannel u p k) (hu₁ : IsClebschGordanChannel m n u) :
    ((hu₂.leftIndex hu₁) : ℕ) = (hu₂.index : ℕ) := (rfl)

/-- `hv₂.rightIndex hv₁` has the same underlying natural-number value as `hv₂.index`. -/
@[simp] theorem IsClebschGordanChannel.val_rightIndex {m n p v k : ℕ}
    (hv₂ : IsClebschGordanChannel m v k) (hv₁ : IsClebschGordanChannel n p v) :
    ((hv₂.rightIndex hv₁) : ℕ) = (hv₂.index : ℕ) := (rfl)

/-- Uniqueness of the Clebsch–Gordan summand index for a given channel weight `k`. -/
theorem IsClebschGordanChannel.index_eq_of_eq {m n k : ℕ} (h : IsClebschGordanChannel m n k)
    {j : Fin (min m n + 1)} (hj : m + n - 2 * (j : ℕ) = k) : h.index = j := by
  ext; have := j.isLt; simp only [index, ← hj]; omega

/-- `h.index = j` holds exactly when `m + n - 2j = k`. -/
@[simp] theorem IsClebschGordanChannel.index_eq_iff {m n k : ℕ} (h : IsClebschGordanChannel m n k)
    (j : Fin (min m n + 1)) : h.index = j ↔ m + n - 2 * (j : ℕ) = k :=
  ⟨fun hj => hj ▸ h.sub_two_mul_index, h.index_eq_of_eq⟩

/-- Every summand index `j : Fin (min m n + 1)` gives an admissible Clebsch–Gordan channel. -/
theorem isClebschGordanChannel_sub_two_mul {m n : ℕ} (j : Fin (min m n + 1)) :
    IsClebschGordanChannel m n (m + n - 2 * (j : ℕ)) := ⟨j, rfl⟩

/-- The constructive index of `m + n - 2j` is `j`. -/
@[simp] theorem IsClebschGordanChannel.index_sub_two_mul {m n : ℕ} (j : Fin (min m n + 1)) :
    (isClebschGordanChannel_sub_two_mul j).index = j :=
  (isClebschGordanChannel_sub_two_mul j).index_eq_of_eq rfl

/-- The leading channel `m + n` (`j = 0`) is always admissible. -/
theorem isClebschGordanChannel_add (m n : ℕ) : IsClebschGordanChannel m n (m + n) := ⟨0, by simp⟩

/-- Tensoring with `L_0` on the left has `n` as its unique admissible channel. -/
@[simp] theorem isClebschGordanChannel_zero_left {n k : ℕ} :
    IsClebschGordanChannel 0 n k ↔ k = n :=
  ⟨by rintro ⟨j, rfl⟩; have := j.isLt; omega, fun h => h ▸ ⟨0, by simp⟩⟩

/-- Tensoring with `L_0` on the right has `m` as its unique admissible channel. -/
@[simp] theorem isClebschGordanChannel_zero_right {m k : ℕ} :
    IsClebschGordanChannel m 0 k ↔ k = m :=
  ⟨by rintro ⟨j, rfl⟩; have := j.isLt; omega, fun h => h ▸ ⟨0, by simp⟩⟩

/-- Reindexing a sum over channel indices `i : Fin (min m n + 1)` as a sum over weights
`w ∈ Finset.range (m + n + 1)` when `g` vanishes outside admissible channels. -/
theorem sum_fin_channel_eq_sum_range (m n : ℕ) (g : ℕ → ℂ)
    (hg : ∀ w, ¬ IsClebschGordanChannel m n w → g w = 0) :
    (∑ i : Fin (min m n + 1), g (m + n - 2 * (i : ℕ))) = ∑ w ∈ Finset.range (m + n + 1), g w := by
  trans ∑ w ∈ (Finset.range (m + n + 1)).filter (IsClebschGordanChannel m n), g w
  · refine Finset.sum_bij (fun (i : Fin (min m n + 1)) _ => m + n - 2 * (i : ℕ)) ?_ ?_ ?_
      fun _ _ => rfl
    · intro i _; rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, isClebschGordanChannel_sub_two_mul i⟩
    · intro i₁ _ i₂ _ _; have := i₁.isLt; have := i₂.isLt; ext; omega
    · intro w hw; rw [Finset.mem_filter] at hw
      exact ⟨hw.2.index, Finset.mem_univ _, hw.2.sub_two_mul_index⟩
  · exact Finset.sum_filter_of_ne fun w _ hfw => by by_contra h; exact hfw (hg w h)

/-- Admissible left intermediate highest weights `u` in `(L_m ⊗ L_n) ⊗ L_p` coupling to total
highest weight `k`. -/
abbrev LeftSixJChannel (m n p k : ℕ) : Type :=
  {u : ℕ // IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k}

/-- Admissible right intermediate highest weights `v` in `L_m ⊗ (L_n ⊗ L_p)` coupling to total
highest weight `k`. -/
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

/-! ### Six-weight quantum 6j symbols and change-of-decomposition matrices -/

section SixJ

variable {q : ℂ}

/-- The six-weight quantum 6j change-of-decomposition scalar for `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ` at total
highest weight `k`, from left intermediate channel `u` (in `L_m^ε ⊗ L_n^δ`) to right intermediate
channel `v` (in `L_n^δ ⊗ L_p^ζ`). Extended by `0` when any binary coupling is inadmissible. -/
def sixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k u v : ℕ) : ℂ :=
  if h : (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) ∧
      (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) then
    recouplingCoeff hq ε δ ζ h.1.1.index (h.1.2.leftIndex h.1.1)
      h.2.1.index (h.2.2.rightIndex h.2.1)
  else 0

/-- The inverse six-weight quantum 6j change-of-decomposition scalar for `L_m^ε ⊗ L_n^δ ⊗ L_p^ζ`
at total highest weight `k`, from right intermediate channel `v` to left intermediate channel `u`.
Extended by `0` outside admissible channels. -/
def invSixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k v u : ℕ) : ℂ :=
  if h : (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) ∧
      (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) then
    invRecouplingCoeff hq ε δ ζ h.1.1.index (h.1.2.rightIndex h.1.1)
      h.2.1.index (h.2.2.leftIndex h.2.1)
  else 0

/-- `sixJ` on admissible left and right channels equals the corresponding `recouplingCoeff`. -/
theorem sixJ_eq_recouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k u v : ℕ}
    (hu : IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k)
    (hv : IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) :
    sixJ hq ε δ ζ m n p k u v =
      recouplingCoeff hq ε δ ζ hu.1.index (hu.2.leftIndex hu.1)
        hv.1.index (hv.2.rightIndex hv.1) := by simp [sixJ, hu, hv]

/-- `invSixJ` on admissible right and left channels equals the corresponding
`invRecouplingCoeff`. -/
theorem invSixJ_eq_invRecouplingCoeff (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v u : ℕ}
    (hv : IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k)
    (hu : IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) :
    invSixJ hq ε δ ζ m n p k v u =
      invRecouplingCoeff hq ε δ ζ hv.1.index (hv.2.rightIndex hv.1)
        hu.1.index (hu.2.leftIndex hu.1) := by simp [invSixJ, hv, hu]

/-- `sixJ` vanishes when any of its four binary channel conditions fails. -/
theorem sixJ_eq_zero_of_not (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p k u v : ℕ}
    (h : ¬ ((IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k) ∧
      (IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k))) :
    sixJ hq ε δ ζ m n p k u v = 0 := by simp [sixJ, h]

/-- `invSixJ` vanishes when any of its four binary channel conditions fails. -/
theorem invSixJ_eq_zero_of_not (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p k v u : ℕ}
    (h : ¬ ((IsClebschGordanChannel n p v ∧ IsClebschGordanChannel m v k) ∧
      (IsClebschGordanChannel m n u ∧ IsClebschGordanChannel u p k))) :
    invSixJ hq ε δ ζ m n p k v u = 0 := by simp [invSixJ, h]

/-- `recouplingCoeff` equals `sixJ` when the left and right total highest weights agree, and `0`
otherwise. -/
theorem recouplingCoeff_eq_ite (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p : ℕ}
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    recouplingCoeff hq ε δ ζ i j r s =
      if m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) then
        sixJ hq ε δ ζ m n p (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ))
          (m + n - 2 * (i : ℕ)) (n + p - 2 * (r : ℕ))
      else 0 := by
  split_ifs with h
  · have hu₁ := isClebschGordanChannel_sub_two_mul i
    have hu₂ := isClebschGordanChannel_sub_two_mul j
    have hv₁ := isClebschGordanChannel_sub_two_mul r
    have hv₂ : IsClebschGordanChannel m (n + p - 2 * (r : ℕ))
        (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) := ⟨s, h.symm⟩
    rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hu₁, hu₂⟩ ⟨hv₁, hv₂⟩]
    exact recouplingCoeff_congr hq ε δ ζ (congrArg Fin.val (hu₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hu₂.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hv₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hv₂.index_eq_of_eq h.symm)).symm
  · exact recouplingCoeff_eq_zero_of_ne hq ε δ ζ h

/-- `invRecouplingCoeff` equals `invSixJ` when the right and left total highest weights agree, and
`0` otherwise. -/
theorem invRecouplingCoeff_eq_ite (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n p : ℕ}
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    invRecouplingCoeff hq ε δ ζ r s i j =
      if m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) then
        invSixJ hq ε δ ζ m n p (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ))
          (n + p - 2 * (r : ℕ)) (m + n - 2 * (i : ℕ))
      else 0 := by
  split_ifs with h
  · have hv₁ := isClebschGordanChannel_sub_two_mul r
    have hv₂ := isClebschGordanChannel_sub_two_mul s
    have hu₁ := isClebschGordanChannel_sub_two_mul i
    have hu₂ : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p
        (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) := ⟨j, h.symm⟩
    rw [invSixJ_eq_invRecouplingCoeff hq ε δ ζ ⟨hv₁, hv₂⟩ ⟨hu₁, hu₂⟩]
    exact invRecouplingCoeff_congr hq ε δ ζ (congrArg Fin.val (hv₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hv₂.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hu₁.index_eq_of_eq rfl)).symm
      (congrArg Fin.val (hu₂.index_eq_of_eq h.symm)).symm
  · exact invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ h

/-- The quantum 6j change-of-decomposition matrix at fixed total highest weight `k`, mapping
`LeftSixJChannel m n p k` columns to `RightSixJChannel m n p k` rows. -/
def sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p k : ℕ) :
    Matrix (RightSixJChannel m n p k) (LeftSixJChannel m n p k) ℂ :=
  fun v u => sixJ hq ε δ ζ m n p k u.1 v.1

/-- The inverse quantum 6j change-of-decomposition matrix at fixed total highest weight `k`,
mapping `RightSixJChannel m n p k` columns to `LeftSixJChannel m n p k` rows. -/
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

/-- Orthogonality of `invSixJ` and `sixJ` summed over all right intermediate weights
`v ∈ Finset.range (n + p + 1)`. -/
theorem sum_invSixJ_mul_sixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k u₁ u₂ : ℕ}
    (hu₁ : IsClebschGordanChannel m n u₁ ∧ IsClebschGordanChannel u₁ p k)
    (hu₂ : IsClebschGordanChannel m n u₂ ∧ IsClebschGordanChannel u₂ p k) :
    ∑ v ∈ Finset.range (n + p + 1),
        invSixJ hq ε δ ζ m n p k v u₁ * sixJ hq ε δ ζ m n p k u₂ v =
      if u₁ = u₂ then 1 else 0 := by
  have horth := sum_invRecouplingCoeff_mul_recouplingCoeff hq ε δ ζ
    hu₁.1.index hu₂.1.index (hu₁.2.leftIndex hu₁.1) (hu₂.2.leftIndex hu₂.1)
  have hk₂ : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * ((hu₂.2.leftIndex hu₂.1) : ℕ) = k := by
    rw [hu₂.2.val_leftIndex, hu₂.1.sub_two_mul_index, hu₂.2.sub_two_mul_index]
  have hinner (r : Fin (min n p + 1)) :
      (∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        invRecouplingCoeff hq ε δ ζ r s hu₁.1.index (hu₁.2.leftIndex hu₁.1) *
          recouplingCoeff hq ε δ ζ hu₂.1.index (hu₂.2.leftIndex hu₂.1) r s) =
        invSixJ hq ε δ ζ m n p k (n + p - 2 * (r : ℕ)) u₁ *
          sixJ hq ε δ ζ m n p k u₂ (n + p - 2 * (r : ℕ)) := by
    have hvr := isClebschGordanChannel_sub_two_mul r
    by_cases hmv : IsClebschGordanChannel m (n + p - 2 * (r : ℕ)) k
    · rw [Finset.sum_eq_single hmv.index]
      · rw [invSixJ_eq_invRecouplingCoeff hq ε δ ζ ⟨hvr, hmv⟩ hu₁,
          sixJ_eq_recouplingCoeff hq ε δ ζ hu₂ ⟨hvr, hmv⟩]
        have hr : (hvr.index : ℕ) = (r : ℕ) := congrArg Fin.val (hvr.index_eq_of_eq rfl)
        exact congrArg₂ (· * ·) (invRecouplingCoeff_congr hq ε δ ζ hr.symm rfl rfl rfl)
          (recouplingCoeff_congr hq ε δ ζ rfl rfl hr.symm rfl)
      · intro s _ hs
        have hne : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * ((hu₂.2.leftIndex hu₂.1) : ℕ) ≠
            m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) := by
          rw [hk₂]; exact fun heq => hs (hmv.index_eq_of_eq heq.symm).symm
        rw [recouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hmv h.2.2), mul_zero]
      refine Finset.sum_eq_zero fun s _ => ?_
      have hne : m + n - 2 * (hu₂.1.index : ℕ) + p - 2 * ((hu₂.2.leftIndex hu₂.1) : ℕ) ≠
          m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) := by
        rw [hk₂]; exact fun heq => hmv ⟨s, heq.symm⟩
      rw [recouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
  simp_rw [hinner] at horth
  rw [← sum_fin_channel_eq_sum_range n p _ fun v hnp => by
    rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hnp h.2.1), mul_zero], horth]
  have hiff : ((hu₁.1.index : ℕ) = (hu₂.1.index : ℕ) ∧
      ((hu₁.2.leftIndex hu₁.1) : ℕ) = ((hu₂.2.leftIndex hu₂.1) : ℕ)) ↔ u₁ = u₂ :=
    ⟨fun ⟨hi, _⟩ => by rw [← hu₁.1.sub_two_mul_index, ← hu₂.1.sub_two_mul_index, hi],
      by rintro rfl; exact ⟨rfl, rfl⟩⟩
  simp only [hiff]

/-- Orthogonality of `sixJ` and `invSixJ` summed over all left intermediate weights
`u ∈ Finset.range (m + n + 1)`. -/
theorem sum_sixJ_mul_invSixJ (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {m n p k v₁ v₂ : ℕ}
    (hv₁ : IsClebschGordanChannel n p v₁ ∧ IsClebschGordanChannel m v₁ k)
    (hv₂ : IsClebschGordanChannel n p v₂ ∧ IsClebschGordanChannel m v₂ k) :
    ∑ u ∈ Finset.range (m + n + 1),
        sixJ hq ε δ ζ m n p k u v₁ * invSixJ hq ε δ ζ m n p k v₂ u =
      if v₁ = v₂ then 1 else 0 := by
  have horth := sum_recouplingCoeff_mul_invRecouplingCoeff hq ε δ ζ
    hv₁.1.index hv₂.1.index (hv₁.2.rightIndex hv₁.1) (hv₂.2.rightIndex hv₂.1)
  have hk₂ : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * ((hv₂.2.rightIndex hv₂.1) : ℕ) = k := by
    rw [hv₂.2.val_rightIndex, hv₂.1.sub_two_mul_index, hv₂.2.sub_two_mul_index]
  have hinner (i : Fin (min m n + 1)) :
      (∑ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
        recouplingCoeff hq ε δ ζ i j hv₁.1.index (hv₁.2.rightIndex hv₁.1) *
          invRecouplingCoeff hq ε δ ζ hv₂.1.index (hv₂.2.rightIndex hv₂.1) i j) =
        sixJ hq ε δ ζ m n p k (m + n - 2 * (i : ℕ)) v₁ *
          invSixJ hq ε δ ζ m n p k v₂ (m + n - 2 * (i : ℕ)) := by
    have hui := isClebschGordanChannel_sub_two_mul i
    by_cases hup : IsClebschGordanChannel (m + n - 2 * (i : ℕ)) p k
    · rw [Finset.sum_eq_single hup.index]
      · rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hui, hup⟩ hv₁,
          invSixJ_eq_invRecouplingCoeff hq ε δ ζ hv₂ ⟨hui, hup⟩]
        have hi : (hui.index : ℕ) = (i : ℕ) := congrArg Fin.val (hui.index_eq_of_eq rfl)
        exact congrArg₂ (· * ·) (recouplingCoeff_congr hq ε δ ζ hi.symm rfl rfl rfl)
          (invRecouplingCoeff_congr hq ε δ ζ rfl rfl hi.symm rfl)
      · intro j _ hj
        have hne : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * ((hv₂.2.rightIndex hv₂.1) : ℕ) ≠
            m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) := by
          rw [hk₂]; exact fun heq => hj (hup.index_eq_of_eq heq.symm).symm
        rw [invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
      · simp
    · rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hup h.1.2), zero_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : m + (n + p - 2 * (hv₂.1.index : ℕ)) - 2 * ((hv₂.2.rightIndex hv₂.1) : ℕ) ≠
          m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) := by
        rw [hk₂]; exact fun heq => hup ⟨j, heq.symm⟩
      rw [invRecouplingCoeff_eq_zero_of_ne hq ε δ ζ hne, mul_zero]
  simp_rw [hinner] at horth
  rw [← sum_fin_channel_eq_sum_range m n _ fun u hmn => by
    rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hmn h.1.1), zero_mul], horth]
  have hiff : ((hv₁.1.index : ℕ) = (hv₂.1.index : ℕ) ∧
      ((hv₁.2.rightIndex hv₁.1) : ℕ) = ((hv₂.2.rightIndex hv₂.1) : ℕ)) ↔ v₁ = v₂ :=
    ⟨fun ⟨hr, _⟩ => by rw [← hv₁.1.sub_two_mul_index, ← hv₂.1.sub_two_mul_index, hr],
      by rintro rfl; exact ⟨rfl, rfl⟩⟩
  simp only [hiff]

private theorem sum_subtype_eq_sum_range {P : ℕ → Prop} (M : ℕ)
    [Fintype {w : ℕ // P w}] (hM : ∀ w, P w → w ≤ M) (g : ℕ → ℂ)
    (hg : ∀ w, ¬ P w → g w = 0) :
    (∑ x : {w : ℕ // P w}, g x.1) = ∑ w ∈ Finset.range (M + 1), g w := by
  classical
  trans ∑ w ∈ (Finset.range (M + 1)).filter P, g w
  · refine Finset.sum_bij (fun (x : {w : ℕ // P w}) _ => x.1)
      (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hM x.1 x.2)),
        x.2⟩)
      (fun _ _ _ _ => Subtype.ext)
      (fun w hw => ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  · exact Finset.sum_filter_of_ne fun w _ hfw => by by_contra h; exact hfw (hg w h)

/-- `invSixJMatrix` is a left inverse to `sixJMatrix`. -/
@[simp] theorem invSixJMatrix_mul_sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (m n p k : ℕ) :
    invSixJMatrix hq ε δ ζ m n p k * sixJMatrix hq ε δ ζ m n p k = 1 := by
  ext u₁ u₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [invSixJMatrix_apply, sixJMatrix_apply]
  rw [sum_subtype_eq_sum_range (n + p) (fun _ h => h.1.le_add)
    (fun v => invSixJ hq ε δ ζ m n p k v u₁.1 * sixJ hq ε δ ζ m n p k u₂.1 v)
    (fun _ hv => by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hv h.2), mul_zero]),
    sum_invSixJ_mul_sixJ hq ε δ ζ u₁.2 u₂.2]
  simp [Subtype.ext_iff]

/-- `invSixJMatrix` is a right inverse to `sixJMatrix`. -/
@[simp] theorem sixJMatrix_mul_invSixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (m n p k : ℕ) :
    sixJMatrix hq ε δ ζ m n p k * invSixJMatrix hq ε δ ζ m n p k = 1 := by
  ext v₁ v₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [sixJMatrix_apply, invSixJMatrix_apply]
  rw [sum_subtype_eq_sum_range (m + n) (fun _ h => h.1.le_add)
    (fun u => sixJ hq ε δ ζ m n p k u v₁.1 * invSixJ hq ε δ ζ m n p k v₂.1 u)
    (fun _ hu => by rw [sixJ_eq_zero_of_not hq ε δ ζ (fun h => hu h.1), zero_mul]),
    sum_sixJ_mul_invSixJ hq ε δ ζ v₁.2 v₂.2]
  simp [Subtype.ext_iff]

/-! ### Explicit boundary evaluations -/

/-- On the leading stretched channel `k = m + n + p` (`u = m + n`, `v = n + p`), the quantum 6j
coefficient is `1` for all highest weights and signs. -/
@[simp] theorem sixJ_add_add (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (m n p : ℕ) :
    sixJ hq ε δ ζ m n p (m + n + p) (m + n) (n + p) = 1 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hu₁ := isClebschGordanChannel_add m n
  have hu₂ := isClebschGordanChannel_add (m + n) p
  have hv₁ := isClebschGordanChannel_add n p
  have hv₂ : IsClebschGordanChannel m (n + p) (m + n + p) :=
    Nat.add_assoc m n p ▸ isClebschGordanChannel_add m (n + p)
  rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hu₁, hu₂⟩ ⟨hv₁, hv₂⟩]
  trans recouplingCoeff (m := m) (n := n) (p := p) hq ε δ ζ 0 0 0 0
  · exact recouplingCoeff_congr hq ε δ ζ (congrArg Fin.val (hu₁.index_eq_of_eq (by simp)))
      (congrArg Fin.val (hu₂.index_eq_of_eq (by simp)))
      (congrArg Fin.val (hv₁.index_eq_of_eq (by simp)))
      (congrArg Fin.val (hv₂.index_eq_of_eq (by simp [Nat.add_assoc])))
  rw [recouplingCoeff_def]
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hleft : tensorMap ℂ (UqSl2 q) (clebschGordanInclusion (m := m) (n := n)
        (ε := ε) (δ := δ) hq 0) LinearMap.id
      (clebschGordanVector q (m + n - 2 * ↑(0 : Fin (min m n + 1))) (ε * δ) p ζ
        ↑(0 : Fin (min (m + n - 2 * ↑(0 : Fin (min m n + 1))) p + 1))) =
      tmul ℂ (UqSl2 q) (tmul ℂ (UqSl2 q) (vec q m ε 0) (vec q n δ 0)) (vec q p ζ 0) := by
    rw [Fin.val_zero (n := min (m + n - 2 * ↑(0 : Fin (min m n + 1))) p + 1),
      clebschGordanVector_zero, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_vec_zero, Fin.val_zero, clebschGordanVector_zero]
  have hright : tmul ℂ (UqSl2 q) (vec q m ε 0) (tmul ℂ (UqSl2 q) (vec q n δ 0) (vec q p ζ 0)) =
      clebschGordanRightInclusion (m := m) (n := n) (p := p) (ε := ε) (δ := δ) (ζ := ζ)
        hq 0 0 (vec q _ _ 0) := by
    rw [clebschGordanRightInclusion_vec_zero,
      Fin.val_zero (n := min m (n + p - 2 * ↑(0 : Fin (min n p + 1))) + 1),
      clebschGordanVector_zero, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_vec_zero, Fin.val_zero, clebschGordanVector_zero]
  rw [hleft, LinearEquiv.coe_toLinearMap, assoc_tmul, hright,
    clebschGordanRightProjection_inclusion_self, one_smul]

private theorem clebschGordanInclusion_zero_left_vec [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (ε : ℤˣ) (n : ℕ) (δ : ℤˣ) (a : ℕ) :
    clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0 (vec q _ _ a) =
      tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a) := by
  induction a with
  | zero => rw [Nat.cast_zero, clebschGordanInclusion_vec_zero]; simp
  | succ a ih =>
    have hqa : quantumInteger q ((a : ℤ) + 1) ≠ 0 := quantumInteger_ne_zero hq (by omega)
    apply smul_right_injective _ hqa
    dsimp only
    have hfv : quantumInteger q ((a : ℤ) + 1) •
        clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0 (vec q _ _ ((a : ℕ) + 1)) =
        f q • clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0 (vec q _ _ a) := by
      rw [← LinearMap.map_smul_of_tower, ← f_smul_vec, map_smul]
    rw [Nat.cast_succ, hfv, ih, f_smul_tmul]
    have hf0 : f q • vec q 0 ε 0 = 0 := by simp
    rw [hf0, zero_tmul, zero_add, f_smul_vec, tmul_smul]

/-- When the first factor is `L_0^ε`, the quantum 6j coefficient on any admissible channel `k` of
`L_n^δ ⊗ L_p^ζ` equals `1`. -/
theorem sixJ_zero_left (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {n p k : ℕ}
    (hk : IsClebschGordanChannel n p k) :
    sixJ hq ε δ ζ 0 n p k n k = 1 := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hu₁ : IsClebschGordanChannel 0 n n := isClebschGordanChannel_zero_left.mpr rfl
  have hv₂ : IsClebschGordanChannel 0 k k := isClebschGordanChannel_zero_left.mpr rfl
  set j₀ : Fin (min (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) p + 1) :=
    ⟨hk.index, by have := hk.index.isLt; simp; omega⟩
  rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hu₁, hk⟩ ⟨hk, hv₂⟩]
  trans recouplingCoeff (m := 0) (n := n) (p := p) hq ε δ ζ 0 j₀ hk.index 0
  · exact recouplingCoeff_congr hq ε δ ζ (by simp) rfl rfl (by simp)
  rw [recouplingCoeff_def]
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hvec : tensorMap ℂ (UqSl2 q)
        (clebschGordanInclusion (m := 0) (n := n) (ε := ε) (δ := δ) hq 0) LinearMap.id
        (clebschGordanVector q (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) (ε * δ) p ζ j₀) =
      ∑ a ∈ Finset.range ((hk.index : ℕ) + 1), clebschGordanCoeff q n p ζ hk.index a •
        tmul ℂ (UqSl2 q) (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a))
          (vec q p ζ ((hk.index : ℤ) - a)) := by
    rw [clebschGordanVector_def, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply]
    have hcoeff : clebschGordanCoeff q (0 + n - 2 * ↑(0 : Fin (min 0 n + 1))) p ζ hk.index a =
        clebschGordanCoeff q n p ζ hk.index a := by congr 1; simp
    have hj₀ : (j₀ : ℕ) = (hk.index : ℕ) := rfl
    rw [hj₀, hcoeff, clebschGordanInclusion_zero_left_vec hq ε n δ a]
  have hright : assoc ℂ (UqSl2 q) (LadderModule q 0 ε) (LadderModule q n δ) (LadderModule q p ζ)
        (∑ a ∈ Finset.range ((hk.index : ℕ) + 1), clebschGordanCoeff q n p ζ hk.index a •
          tmul ℂ (UqSl2 q) (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a))
            (vec q p ζ ((hk.index : ℤ) - a))) =
      clebschGordanRightInclusion (m := 0) (n := n) (p := p) (ε := ε) (δ := δ) (ζ := ζ)
        hq hk.index 0 (vec q _ _ 0) := by
    rw [map_sum]
    have htmul_sum : tmul ℂ (UqSl2 q) (vec q 0 ε 0) (clebschGordanVector q n δ p ζ hk.index) =
        ∑ a ∈ Finset.range ((hk.index : ℕ) + 1), tmul ℂ (UqSl2 q) (vec q 0 ε 0)
          (clebschGordanCoeff q n p ζ hk.index a •
            tmul ℂ (UqSl2 q) (vec q n δ a) (vec q p ζ ((hk.index : ℤ) - a))) := by
      rw [clebschGordanVector_def]
      exact (tensorEquiv ℂ (UqSl2 q) _ _).injective (by simp [TensorProduct.tmul_sum])
    have hsum : (∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
        (assoc ℂ (UqSl2 q) (LadderModule q 0 ε) (LadderModule q n δ) (LadderModule q p ζ))
          (clebschGordanCoeff q n p ζ hk.index a •
            tmul ℂ (UqSl2 q) (tmul ℂ (UqSl2 q) (vec q 0 ε 0) (vec q n δ a))
              (vec q p ζ ((hk.index : ℤ) - a)))) =
        tmul ℂ (UqSl2 q) (vec q 0 ε 0) (clebschGordanVector q n δ p ζ hk.index) := by
      rw [htmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower, LinearEquiv.coe_toLinearMap,
        assoc_tmul, tmul_smul]
    rw [hsum, clebschGordanRightInclusion_vec_zero]; simp
  rw [hvec, LinearEquiv.coe_toLinearMap, hright, clebschGordanRightProjection_inclusion_self,
    one_smul]

private theorem clebschGordanInclusion_zero_right_vec [Fact (q ≠ 0)]
    (hq : IsGenericQuantumParameter q) (n : ℕ) (δ ζ : ℤˣ) (b : ℕ) :
    clebschGordanInclusion (m := n) (n := 0) (ε := δ) (δ := ζ) hq 0 (vec q _ _ b) =
      ((ζ : ℂ) ^ b) • tmul ℂ (UqSl2 q) (vec q n δ b) (vec q 0 ζ 0) := by
  induction b with
  | zero => rw [Nat.cast_zero, clebschGordanInclusion_vec_zero]; simp
  | succ b ih =>
    have hqb : quantumInteger q ((b : ℤ) + 1) ≠ 0 := quantumInteger_ne_zero hq (by omega)
    apply smul_right_injective _ hqb
    dsimp only
    have hfv : quantumInteger q ((b : ℤ) + 1) •
        clebschGordanInclusion (m := n) (n := 0) (ε := δ) (δ := ζ) hq 0 (vec q _ _ ((b : ℕ) + 1)) =
        f q • clebschGordanInclusion (m := n) (n := 0) (ε := δ) (δ := ζ) hq 0 (vec q _ _ b) := by
      rw [← LinearMap.map_smul_of_tower, ← f_smul_vec, map_smul]
    rw [Nat.cast_succ, hfv, ih, smul_comm, f_smul_tmul]
    have hf0 : f q • vec q 0 ζ 0 = 0 := by simp
    have hk0 : kInv q • vec q 0 ζ 0 = (ζ : ℂ) • vec q 0 ζ 0 := by simp
    rw [hf0, tmul_zero, add_zero, hk0, f_smul_vec, ← smul_tmul', tmul_smul,
      smul_smul, smul_smul, smul_smul, pow_succ]
    congr 1; ring

private theorem clebschGordanCoeff_mul_sign (q : ℂ) (m n : ℕ) (δ ζ : ℤˣ) (i a : ℕ) :
    clebschGordanCoeff q m n (δ * ζ) i a = (ζ : ℂ) ^ a * clebschGordanCoeff q m n δ i a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [clebschGordanCoeff_succ, clebschGordanCoeff_succ, ih, pow_succ, Units.val_mul,
      Int.cast_mul]; ring

/-- When the third factor is `L_0^ζ`, the quantum 6j coefficient on an admissible channel `k` of
`L_m^ε ⊗ L_n^δ` equals `ζ^((m + n - k) / 2)`, reflecting the `K⁻¹` factor in
`ΔF = F ⊗ K⁻¹ + 1 ⊗ F`. -/
theorem sixJ_zero_right (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {m n k : ℕ}
    (hk : IsClebschGordanChannel m n k) :
    sixJ hq ε δ ζ m n 0 k k n = (ζ : ℂ) ^ ((m + n - k) / 2) := by
  let : Fact (q ≠ 0) := ⟨hq.ne_zero⟩
  have hu₂ : IsClebschGordanChannel k 0 k := isClebschGordanChannel_zero_right.mpr rfl
  have hv₁ : IsClebschGordanChannel n 0 n := isClebschGordanChannel_zero_right.mpr rfl
  set s₀ : Fin (min m (n + 0 - 2 * ↑(0 : Fin (min n 0 + 1))) + 1) :=
    ⟨hk.index, by have := hk.index.isLt; simp; omega⟩
  rw [sixJ_eq_recouplingCoeff hq ε δ ζ ⟨hk, hu₂⟩ ⟨hv₁, hk⟩]
  trans recouplingCoeff (m := m) (n := n) (p := 0) hq ε δ ζ hk.index 0 0 s₀
  · exact recouplingCoeff_congr hq ε δ ζ rfl (by simp) (by simp) rfl
  rw [recouplingCoeff_def]
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [recouplingHom_def, LinearMap.comp_apply, LinearMap.comp_apply,
    clebschGordanLeftInclusion_vec_zero]
  have hleft : assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q 0 ζ)
      (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq hk.index) LinearMap.id
        (clebschGordanVector q (m + n - 2 * (hk.index : ℕ)) (ε * δ) 0 ζ
          ↑(0 : Fin (min (m + n - 2 * (hk.index : ℕ)) 0 + 1)))) =
      ∑ a ∈ Finset.range ((hk.index : ℕ) + 1), clebschGordanCoeff q m n δ hk.index a •
        tmul ℂ (UqSl2 q) (vec q m ε a)
          (tmul ℂ (UqSl2 q) (vec q n δ ((hk.index : ℤ) - a)) (vec q 0 ζ 0)) := by
    have hsum_tmul : tmul ℂ (UqSl2 q) (clebschGordanVector q m ε n δ hk.index) (vec q 0 ζ 0) =
        ∑ a ∈ Finset.range ((hk.index : ℕ) + 1),
          tmul ℂ (UqSl2 q) (clebschGordanCoeff q m n δ hk.index a •
            tmul ℂ (UqSl2 q) (vec q m ε a) (vec q n δ ((hk.index : ℤ) - a))) (vec q 0 ζ 0) := by
      rw [clebschGordanVector_def]
      exact (tensorEquiv ℂ (UqSl2 q) _ _).injective (by simp [TensorProduct.sum_tmul])
    rw [Fin.val_zero, clebschGordanVector_zero, tensorMap_tmul, LinearMap.id_apply,
      clebschGordanInclusion_vec_zero, hsum_tmul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_tmul', ← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower,
      LinearEquiv.coe_toLinearMap, assoc_tmul]
  have hright : ((ζ : ℂ) ^ (hk.index : ℕ)) •
        clebschGordanRightInclusion (m := m) (n := n) (p := 0) (ε := ε) (δ := δ) (ζ := ζ)
          hq 0 s₀ (vec q _ _ 0) =
      ∑ a ∈ Finset.range ((hk.index : ℕ) + 1), clebschGordanCoeff q m n δ hk.index a •
        tmul ℂ (UqSl2 q) (vec q m ε a)
          (tmul ℂ (UqSl2 q) (vec q n δ ((hk.index : ℤ) - a)) (vec q 0 ζ 0)) := by
    have hζsq : ∀ k : ℕ, ((ζ : ℂ) ^ k) * ((ζ : ℂ) ^ k) = 1 := fun k => by
      rw [← mul_pow]; rcases Int.units_eq_one_or ζ with rfl | rfl <;> simp
    rw [clebschGordanRightInclusion_vec_zero, clebschGordanVector_def, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    have hs₀ : (s₀ : ℕ) = (hk.index : ℕ) := rfl
    rw [hs₀] at ha ⊢
    have hsub : ((hk.index : ℤ) - a) = (((hk.index : ℕ) - a : ℕ) : ℤ) := by omega
    have hn0 : n + 0 - 2 * ↑(0 : Fin (min n 0 + 1)) = n := by simp
    rw [LinearMap.map_smul_of_tower, tensorMap_tmul, LinearMap.id_apply, hsub,
      clebschGordanInclusion_zero_right_vec hq n δ ζ ((hk.index : ℕ) - a), hn0,
      clebschGordanCoeff_mul_sign q m n δ ζ hk.index a, tmul_smul, smul_smul, smul_smul]
    congr 1; rw [mul_assoc, mul_assoc, mul_comm (clebschGordanCoeff _ _ _ _ _ _),
      ← mul_assoc ((ζ : ℂ) ^ a), ← pow_add, Nat.add_sub_of_le (by omega), ← mul_assoc, hζsq,
      one_mul]
  rw [LinearEquiv.coe_toLinearMap, hleft, ← hright, LinearMap.map_smul_of_tower,
    clebschGordanRightProjection_inclusion_self]; rfl

end SixJ

end TauCeti.UqSl2
