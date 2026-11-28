/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Symmetrizable
public import TauCeti.QuantumGroups.Frobenius.ModifiedDatum

/-!
# Finite-type modified Cartan data and the same-vs-dual dichotomy

When a symmetrizable Cartan datum `A` is of finite type, Lusztig's modified datum `(A*, d*)` at any
parameter order `L ≥ 1` remains of finite type:

* positive definiteness of row-weighted matrices `(dᵢ aᵢⱼ)` (under `dᵢ ↦ ℓᵢ² dᵢ`) and of the
  symmetrized matrix, `Matrix.IsFiniteCartan`, and `TauCeti.IsFiniteType` are all preserved by
  `TauCeti.SymmetrizableDatum.modifiedDatum`
  (`TauCeti.SymmetrizableDatum.posDef_mul_modifiedDatum_cartan_iff`,
  `TauCeti.SymmetrizableDatum.posDef_symmetrizedMatrix_modifiedDatum_iff`,
  `TauCeti.SymmetrizableDatum.isFiniteCartan_modifiedDatum`,
  `TauCeti.SymmetrizableDatum.isFiniteType_modifiedDatum_iff`);
* the diagram of any finite-type Cartan matrix is acyclic and hence bipartite, so the odd-cycle
  clause of `TauCeti.SymmetrizableDatum.LusztigConditions` holds automatically in finite type
  (`TauCeti.SymmetrizableDatum.lusztigConditions_iff_of_isFiniteType`);
* for an indecomposable finite-type datum, whenever `dᵢ ≤ dⱼ` and `L > 0`, one has `dᵢ ∣ dⱼ`,
  `ℓⱼ ∣ ℓᵢ`, and `ℓᵢ / ℓⱼ = gcd(L, dⱼ) / gcd(L, dᵢ) ∈ {1, dⱼ / dᵢ}`
  (`TauCeti.SymmetrizableDatum.symmetrizer_dvd_and_frobeniusOrder_div_mem_of_isFiniteType`);
* **the indecomposable finite-type dichotomy**
  (`TauCeti.SymmetrizableDatum.modifiedDatum_cartan_eq_self_or_transpose`): for an indecomposable
  finite-type datum, either all Frobenius orders `ℓᵢ` are equal and `A* = A` (same type), or the
  Frobenius orders are non-constant and `A* = Aᵀ` (dual type, exchanging `Bₙ` with `Cₙ` and `G₂`,
  `F₄` with their transposes).

The final section verifies the explicit rank-`1` and rank-`2` test cases (`G₂`, `B₂`, `A₁`),
including non-normalized symmetrizers and the failure of Lusztig's second inequality at small
orders.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §2.2.4, §35.1.
* K. McGerty, *Generalized `q`-Schur algebras and quantum Frobenius*, Adv. Math. 214 (2007),
  116–131 (arXiv:math/0601511), §4.
-/

public section

open scoped Matrix

namespace TauCeti.SymmetrizableDatum

variable {I : Type*} (A : SymmetrizableDatum I)

/-! ### Preservation of positive definiteness and finite type -/

/-- Scaling a rational row-weight `d` by `ℓᵢ²` preserves positive definiteness when passing from
`A` to `A*`, since `(ℓᵢ² dᵢ) aᵢⱼ* = ℓᵢ (dᵢ aᵢⱼ) ℓⱼ` is congruent to `(dᵢ aᵢⱼ)` by the invertible
diagonal matrix `diag(ℓᵢ)`. -/
theorem posDef_mul_modifiedDatum_cartan_iff {L : ℕ} (hL : 0 < L) (d : I → ℚ) :
    (_root_.Matrix.of fun i j ↦
      (A.frobeniusOrder L i : ℚ) ^ 2 * d i * ((A.modifiedDatum L hL).cartan i j : ℚ)).PosDef ↔
      (_root_.Matrix.of fun i j ↦ d i * (A.cartan i j : ℚ)).PosDef := by
  classical
  rw [_root_.Matrix.posDef_iff_submatrix_finset, _root_.Matrix.posDef_iff_submatrix_finset]
  refine forall_congr' fun s ↦ ?_
  let U : _root_.Matrix s s ℚ := _root_.Matrix.diagonal fun i ↦ (A.frobeniusOrder L i : ℚ)
  have hU : IsUnit U := _root_.Matrix.isUnit_diagonal.mpr <| Pi.isUnit_iff.mpr fun i ↦
    (Nat.cast_ne_zero.mpr (A.frobeniusOrder_ne_zero hL i)).isUnit
  have hcongr : (_root_.Matrix.of fun i j ↦
      (A.frobeniusOrder L i : ℚ) ^ 2 * d i * ((A.modifiedDatum L hL).cartan i j : ℚ)).submatrix
      (↑) (↑) =
      star U * (_root_.Matrix.of fun i j ↦ d i * (A.cartan i j : ℚ)).submatrix (↑) (↑) * U := by
    ext i j
    have hij : (A.frobeniusOrder L i : ℚ) * ((A.modifiedDatum L hL).cartan i j : ℚ) =
        A.frobeniusOrder L j * (A.cartan i j : ℚ) := by
      exact_mod_cast A.frobeniusOrder_mul_modifiedDatum_cartan L hL i j
    simp only [U, _root_.Matrix.star_eq_conjTranspose, _root_.Matrix.diagonal_conjTranspose,
      star_trivial, _root_.Matrix.diagonal_mul, _root_.Matrix.mul_diagonal,
      _root_.Matrix.submatrix_apply, _root_.Matrix.of_apply]
    linear_combination (A.frobeniusOrder L i : ℚ) * d i * hij
  rw [hcongr, _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff hU]

/-- For any symmetrizable datum and `L > 0`, the symmetrized matrix of the modified datum is
positive definite over `ℤ` if and only if the original symmetrized matrix is positive definite. -/
@[simp]
theorem posDef_symmetrizedMatrix_modifiedDatum_iff {L : ℕ} (hL : 0 < L) :
    (A.modifiedDatum L hL).symmetrizedMatrix.PosDef ↔ A.symmetrizedMatrix.PosDef := by
  rw [← TauCeti.Matrix.posDef_map_intCast_iff, ← TauCeti.Matrix.posDef_map_intCast_iff]
  convert A.posDef_mul_modifiedDatum_cartan_iff hL (fun i ↦ (A.symmetrizer i : ℚ)) using 2 <;>
    ext i j <;> simp

/-- Modifying a symmetrizable datum preserves Mathlib's `Matrix.IsFiniteCartan`. -/
theorem isFiniteCartan_modifiedDatum [Fintype I] [DecidableEq I]
    (hM : A.cartan.IsFiniteCartan) {L : ℕ} (hL : 0 < L) :
    (A.modifiedDatum L hL).cartan.IsFiniteCartan := by
  refine .mk_of_exists_posDef (A.modifiedDatum L hL).isGeneralizedCartan.diag
    (A.modifiedDatum L hL).isGeneralizedCartan.offDiag_nonpos ?_
  obtain ⟨d, hd, hpd⟩ := hM.exists_posDef
  refine ⟨fun i ↦ (A.frobeniusOrder L i : ℤ) ^ 2 * d i,
    fun i ↦ mul_pos (pow_pos (Int.natCast_pos.mpr (A.frobeniusOrder_pos hL i)) 2) (hd i), ?_⟩
  rw [← TauCeti.Matrix.posDef_map_intCast_iff] at hpd ⊢
  have hpd' : (_root_.Matrix.of fun i j ↦ (d i : ℚ) * (A.cartan i j : ℚ)).PosDef := by
    convert hpd using 1; ext i j; simp
  convert (A.posDef_mul_modifiedDatum_cartan_iff hL fun i ↦ (d i : ℚ)).mpr hpd' using 1
  ext i j
  simp [mul_assoc]

/-- Modifying a symmetrizable datum preserves `TauCeti.IsFiniteType`. -/
@[simp]
theorem isFiniteType_modifiedDatum_iff {L : ℕ} (hL : 0 < L) :
    IsFiniteType (A.modifiedDatum L hL).cartan ↔ IsFiniteType A.cartan := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hw (i : I) : (0 : ℚ) < A.frobeniusOrder L i := Nat.cast_pos.mpr (A.frobeniusOrder_pos hL i)
    have := h.finite
    obtain ⟨d, -, hpd⟩ := h.exists_symmetrizer
    refine isFiniteType_of A.isGeneralizedCartan.diag A.isGeneralizedCartan.offDiag_nonpos
      (d := fun i ↦ d i / (A.frobeniusOrder L i : ℚ) ^ 2)
      ((A.posDef_mul_modifiedDatum_cartan_iff hL _).mp ?_)
    convert hpd using 1
    ext i j
    rw [_root_.Matrix.of_apply, _root_.Matrix.of_apply,
      mul_div_cancel₀ _ (pow_ne_zero 2 (hw i).ne')]
  · have := h.finite
    classical
    have _ : Fintype I := Fintype.ofFinite I
    exact (A.isFiniteCartan_modifiedDatum h.isFiniteCartan hL).isFiniteType

/-- In finite type, the diagram is automatically bipartite (since it is acyclic), so Lusztig's
conditions reduce to the inequalities `1 - aᵢⱼ ≤ ℓᵢ` for `i ≠ j` with `2 ≤ ℓⱼ`. -/
theorem lusztigConditions_iff_of_isFiniteType (h : IsFiniteType A.cartan) (L : ℕ) :
    A.LusztigConditions L ↔
      ∀ i j, i ≠ j → 2 ≤ A.frobeniusOrder L j → 1 - A.cartan i j ≤ A.frobeniusOrder L i := by
  rw [lusztigConditions_def]
  exact and_iff_right h.isAcyclic_diagramGraph.isBipartite

/-! ### Short/long Frobenius order ratios and the same-vs-dual dichotomy -/

/-- In an indecomposable finite-type datum, whenever `dᵢ ≤ dⱼ` and `L > 0`, one has `dᵢ ∣ dⱼ`,
`ℓⱼ ∣ ℓᵢ`, and the ratio `ℓᵢ / ℓⱼ = gcd(L, dⱼ) / gcd(L, dᵢ)` is either `1` or `dⱼ / dᵢ`. -/
theorem symmetrizer_dvd_and_frobeniusOrder_div_mem_of_isFiniteType
    (hft : IsFiniteType A.cartan) (hA : A.cartan.IsIndecomposable)
    {i j : I} (hle : A.symmetrizer i ≤ A.symmetrizer j) {L : ℕ} (hL : 0 < L) :
    A.symmetrizer i ∣ A.symmetrizer j ∧
      A.frobeniusOrder L j ∣ A.frobeniusOrder L i ∧
      A.frobeniusOrder L i / A.frobeniusOrder L j ∈
        ({1, A.symmetrizer j / A.symmetrizer i} : Set ℕ) := by
  have := hft.finite
  classical
  have _i : Fintype I := Fintype.ofFinite I
  have : Nonempty I := ⟨i⟩
  obtain ⟨r, hr_mem, -, -, hp⟩ := A.exists_lacing_normalizeSymmetrizer_of_isFiniteType hft hA
  have hr : r = 1 ∨ r = 2 ∨ r = 3 := by simpa using hr_mem
  have hr_pos : 0 < r := by rcases hr with h | h | h <;> omega
  set d' := A.normalizeSymmetrizer.symmetrizer
  have hpi : d' i = 1 ∨ d' i = r := by simpa [d'] using hp i
  have hpj : d' j = 1 ∨ d' j = r := by simpa [d'] using hp j
  have hle_norm : d' i ≤ d' j := by
    have hle' := hle
    rw [A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i,
      A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer j] at hle'
    exact Nat.le_of_mul_le_mul_left hle' A.gcd_symmetrizer_pos
  have hdvd_norm : d' i ∣ d' j ∧ (d' j / d' i = 1 ∨ d' j / d' i = 2 ∨ d' j / d' i = 3) := by
    rcases hpi with hi | hi <;> rcases hpj with hj | hj
    · rw [hi, hj]; simp
    · rw [hi, hj, Nat.div_one]; exact ⟨one_dvd r, hr⟩
    · rw [hi, hj] at hle_norm ⊢
      have hr1 : r = 1 := by omega
      simp [hr1]
    · rw [hi, hj, Nat.div_self hr_pos]; simp
  have hdvd : A.symmetrizer i ∣ A.symmetrizer j := by
    rw [A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i,
      A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer j]
    exact mul_dvd_mul_left _ hdvd_norm.1
  have hdiv_eq : A.symmetrizer j / A.symmetrizer i = d' j / d' i := by
    rw [A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer i,
      A.symmetrizer_eq_gcd_mul_normalizeSymmetrizer j]
    exact Nat.mul_div_mul_left _ _ A.gcd_symmetrizer_pos
  refine ⟨hdvd, A.frobeniusOrder_dvd_of_dvd_symmetrizer hdvd L, ?_⟩
  rw [(A.frobeniusOrder_div_eq_of_dvd_symmetrizer hdvd hL).2, hdiv_eq]
  rcases hdvd_norm.2 with h1 | h2 | h3
  · rw [h1]; simp
  · rw [h2]; simpa using Nat.prime_two.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right _ 2)
  · rw [h3]; simpa using Nat.prime_three.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right _ 3)

/-- **Dual-type branch of the finite-type dichotomy.** In an indecomposable finite-type datum,
whenever two nodes have distinct Frobenius orders `ℓᵢ ≠ ℓⱼ` (`L > 0`), the modified Cartan matrix
is the transpose `Aᵀ` of `A` (the dual root-system type). -/
theorem modifiedDatum_cartan_eq_transpose_of_frobeniusOrder_ne
    (hft : IsFiniteType A.cartan) (hA : A.cartan.IsIndecomposable)
    {L : ℕ} (hL : 0 < L) (hne : ∃ i j, A.frobeniusOrder L i ≠ A.frobeniusOrder L j) :
    (A.modifiedDatum L hL).cartan = A.cartan.transpose := by
  have := hft.finite
  classical
  have _i : Fintype I := Fintype.ofFinite I
  obtain ⟨i₀, j₀, hij₀⟩ := hne
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨r, hr_mem, -, -, hp⟩ := A.exists_lacing_normalizeSymmetrizer_of_isFiniteType hft hA
  have hr : r = 1 ∨ r = 2 ∨ r = 3 := by simpa using hr_mem
  have hp' (k : I) : A.normalizeSymmetrizer.symmetrizer k = 1 ∨
      A.normalizeSymmetrizer.symmetrizer k = r := by simpa using hp k
  have hg_not_one : Nat.gcd (A.reducedOrder L) r ≠ 1 := fun hg1 ↦ hij₀ <| by
    have hconst (k : I) : A.frobeniusOrder L k = A.reducedOrder L := by
      rw [← A.frobeniusOrder_normalizeSymmetrizer L k, frobeniusOrder_def]
      rcases hp' k with hk | hk
      · rw [hk]; simp
      · rw [hk, hg1, Nat.div_one]
    rw [hconst i₀, hconst j₀]
  have hg_eq_r : Nat.gcd (A.reducedOrder L) r = r := by
    have hor : Nat.gcd (A.reducedOrder L) r = 1 ∨ Nat.gcd (A.reducedOrder L) r = r := by
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (Nat.gcd_one_right _)
      · exact Nat.prime_two.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right _ 2)
      · exact Nat.prime_three.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right _ 3)
    exact hor.resolve_left hg_not_one
  have hprod (k : I) :
      A.normalizeSymmetrizer.symmetrizer k * A.frobeniusOrder L k = A.reducedOrder L := by
    rw [← A.frobeniusOrder_normalizeSymmetrizer L k, frobeniusOrder_def]
    rcases hp' k with hk | hk
    · rw [hk, one_mul, Nat.gcd_one_right, Nat.div_one]
    · rw [hk, hg_eq_r]
      exact Nat.mul_div_cancel' (hg_eq_r ▸ Nat.gcd_dvd_left (A.reducedOrder L) r)
  ext i j
  have hli : (A.frobeniusOrder L i : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (A.frobeniusOrder_ne_zero hL i)
  have hL'_ne : (A.reducedOrder L : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (A.reducedOrder_pos hL).ne'
  have hnum : (A.frobeniusOrder L j : ℤ) * A.cartan i j = A.frobeniusOrder L i * A.cartan j i := by
    have hsymm : (A.normalizeSymmetrizer.symmetrizer i : ℤ) * A.cartan i j =
        A.normalizeSymmetrizer.symmetrizer j * A.cartan j i := by
      simpa using A.normalizeSymmetrizer.symmetrizes i j
    have hpi : (A.normalizeSymmetrizer.symmetrizer i : ℤ) * A.frobeniusOrder L i =
        A.reducedOrder L := by exact_mod_cast hprod i
    have hpj : (A.normalizeSymmetrizer.symmetrizer j : ℤ) * A.frobeniusOrder L j =
        A.reducedOrder L := by exact_mod_cast hprod j
    refine mul_left_cancel₀ hL'_ne ?_
    linear_combination (A.frobeniusOrder L i : ℤ) * (A.frobeniusOrder L j : ℤ) * hsymm -
      (A.frobeniusOrder L j : ℤ) * A.cartan i j * hpi +
      (A.frobeniusOrder L i : ℤ) * A.cartan j i * hpj
  rw [modifiedDatum_cartan_apply, hnum, Int.mul_ediv_cancel_left _ hli, Matrix.transpose_apply]

/-- **The indecomposable finite-type dichotomy.** For an indecomposable finite-type datum and
`L > 0`, either all Frobenius orders `ℓᵢ` are equal and `A* = A`, or the Frobenius orders are not
all equal and `A* = Aᵀ` (the dual Dynkin type). -/
theorem modifiedDatum_cartan_eq_self_or_transpose
    (hft : IsFiniteType A.cartan) (hA : A.cartan.IsIndecomposable) {L : ℕ} (hL : 0 < L) :
    ((∀ i j, A.frobeniusOrder L i = A.frobeniusOrder L j) ∧
        (A.modifiedDatum L hL).cartan = A.cartan) ∨
      ((∃ i j, A.frobeniusOrder L i ≠ A.frobeniusOrder L j) ∧
        (A.modifiedDatum L hL).cartan = A.cartan.transpose) := by
  by_cases hall : ∀ i j, A.frobeniusOrder L i = A.frobeniusOrder L j
  · exact Or.inl ⟨hall, A.modifiedDatum_cartan_eq_of_frobeniusOrder_eq hL hall⟩
  · push Not at hall
    exact Or.inr ⟨hall, A.modifiedDatum_cartan_eq_transpose_of_frobeniusOrder_ne hft hA hL hall⟩

end TauCeti.SymmetrizableDatum

/-! ### Explicit rank-1 and rank-2 checks -/

section Checks

open TauCeti TauCeti.SymmetrizableDatum

/-- Normalized `G₂` datum with `A = [[2, -3], [-1, 2]]` and `d = (1, 3)`. -/
private def g2NormDatum : SymmetrizableDatum (Fin 2) where
  cartan := !![2, -3; -1, 2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_two]
      zero_comm := by simp [Fin.forall_fin_two] }
  symmetrizer := ![1, 3]
  symmetrizer_pos := by simp [Fin.forall_fin_two]
  symmetrizes := by decide

/-- Non-normalized `G₂` datum with `d = (2, 6)`. -/
private def g2ScaledDatum : SymmetrizableDatum (Fin 2) where
  cartan := !![2, -3; -1, 2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_two]
      zero_comm := by simp [Fin.forall_fin_two] }
  symmetrizer := ![2, 6]
  symmetrizer_pos := by simp [Fin.forall_fin_two]
  symmetrizes := by decide

/-- Normalized `B₂` datum with `A = [[2, -2], [-1, 2]]` and `d = (1, 2)`. -/
private def b2NormDatum : SymmetrizableDatum (Fin 2) where
  cartan := !![2, -2; -1, 2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_two]
      zero_comm := by simp [Fin.forall_fin_two] }
  symmetrizer := ![1, 2]
  symmetrizer_pos := by simp [Fin.forall_fin_two]
  symmetrizes := by decide

/-- Non-normalized `B₂` datum with `d = (2, 4)`. -/
private def b2ScaledDatum : SymmetrizableDatum (Fin 2) where
  cartan := !![2, -2; -1, 2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_two]
      zero_comm := by simp [Fin.forall_fin_two] }
  symmetrizer := ![2, 4]
  symmetrizer_pos := by simp [Fin.forall_fin_two]
  symmetrizes := by decide

/-- Non-normalized `A₁` datum with `A = [[2]]` and `d = (2)`. -/
private def a1ScaledDatum : SymmetrizableDatum (Fin 1) where
  cartan := !![2]
  isGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp
      zero_comm := by simp }
  symmetrizer := ![2]
  symmetrizer_pos := by simp
  symmetrizes := by decide

-- Check 1: `G₂` with `d = (2, 6)` at `L = 4` has `c = 2`, `d_norm = (1, 3)`, `L' = 2`,
-- `ℓ = (2, 2)`, `A* = A`; `L = 4` is divisible for `d` whereas `L' = 2` is nondivisible for
-- `d_norm`.
example :
    Finset.univ.gcd g2ScaledDatum.symmetrizer = 2 ∧
      g2ScaledDatum.normalizeSymmetrizer = g2NormDatum ∧
      g2ScaledDatum.reducedOrder 4 = 2 ∧
      g2ScaledDatum.frobeniusOrder 4 = ![2, 2] ∧
      (g2ScaledDatum.modifiedDatum 4 (by decide)).cartan = g2ScaledDatum.cartan ∧
      ¬ g2ScaledDatum.Nondivisible 4 ∧
      g2ScaledDatum.normalizeSymmetrizer.Nondivisible (g2ScaledDatum.reducedOrder 4) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    · fin_cases i <;> fin_cases j <;> simp [g2ScaledDatum, g2NormDatum]
    · fin_cases i <;> simp only [normalizeSymmetrizer_symmetrizer, g2ScaledDatum, g2NormDatum] <;>
        decide
  · rw [reducedOrder_def]; decide
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, g2ScaledDatum]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [frobeniusOrder_def, g2ScaledDatum]
  · rw [nondivisible_def]; intro h
    exact absurd (h 0) (by simp only [g2ScaledDatum]; decide)
  · rw [nondivisible_def]; intro i
    fin_cases i <;>
      simp only [reducedOrder_def, normalizeSymmetrizer_symmetrizer, g2ScaledDatum] <;> decide

-- Check 2: `G₂` with `d = (1, 3)` at `L = 3` has `ℓ = (3, 1)`, `A* = [[2, -1], [-3, 2]] = Aᵀ`,
-- `d* = (9, 3)`, symmetrized off-diagonal `-9`, fails `Nondivisible 3`, and fails
-- `LusztigConditions 3` at `(i, j) = (1, 0)`.
example :
    g2NormDatum.frobeniusOrder 3 = ![3, 1] ∧
      (g2NormDatum.modifiedDatum 3 (by decide)).cartan = !![2, -1; -3, 2] ∧
      (g2NormDatum.modifiedDatum 3 (by decide)).symmetrizer = ![9, 3] ∧
      (g2NormDatum.modifiedDatum 3 (by decide)).symmetrizedMatrix 0 1 = -9 ∧
      ¬ g2NormDatum.Nondivisible 3 ∧
      ¬ g2NormDatum.LusztigConditions 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, g2NormDatum]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [frobeniusOrder_def, g2NormDatum]
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, g2NormDatum]
  · simp [frobeniusOrder_def, g2NormDatum]
  · rw [nondivisible_def]; intro h; exact absurd (h 1) (by simp [g2NormDatum])
  · intro h
    have h10 := h.one_sub_cartan_le (i := 1) (j := 0) (by decide)
      (by simp [frobeniusOrder_def, g2NormDatum])
    simp [frobeniusOrder_def, g2NormDatum] at h10

-- Lattice check on simply connected `G₂` at `L = 3`: `α₀* = 3 • α₀`, `α₁* = α₁ ≠ 3 • α₁`.
example :
    let D := g2NormDatum.simplyConnectedCartanDatum (by decide)
    (D.modifiedRoot 3 0 : Module.Dual ℤ (Fin 2 → ℤ)) = 3 • D.root 0 ∧
      (D.modifiedRoot 3 1 : Module.Dual ℤ (Fin 2 → ℤ)) = D.root 1 ∧
      (D.modifiedRoot 3 1 : Module.Dual ℤ (Fin 2 → ℤ)) ≠ 3 • D.root 1 := by
  intro D
  have h0 : D.frobeniusOrder 3 0 = 3 := by
    simp [CartanDatum.frobeniusOrder_def, D, g2NormDatum]
  have h1 : D.frobeniusOrder 3 1 = 1 := by
    simp [CartanDatum.frobeniusOrder_def, D, g2NormDatum]
  refine ⟨by simp [h0], by simp [h1], fun h ↦ ?_⟩
  have heval := congrArg (fun x ↦ D.pairing x (D.coroot 1)) h
  simp [h1, map_nsmul] at heval

-- Check 3: `B₂` with `d = (1, 2)` at `L = 2` has `ℓ = (2, 1)`, `A* = [[2, -1], [-2, 2]] = Aᵀ`,
-- fails `Nondivisible 2`, and fails `LusztigConditions 2` at `(1, 0)`.
example :
    b2NormDatum.frobeniusOrder 2 = ![2, 1] ∧
      (b2NormDatum.modifiedDatum 2 (by decide)).cartan = !![2, -1; -2, 2] ∧
      ¬ b2NormDatum.Nondivisible 2 ∧
      ¬ b2NormDatum.LusztigConditions 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, b2NormDatum]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [frobeniusOrder_def, b2NormDatum]
  · rw [nondivisible_def]; intro h; exact absurd (h 1) (by simp [b2NormDatum])
  · intro h
    have h10 := h.one_sub_cartan_le (i := 1) (j := 0) (by decide)
      (by simp [frobeniusOrder_def, b2NormDatum])
    simp [frobeniusOrder_def, b2NormDatum] at h10

-- Check 4: `G₂` with `d = (1, 3)` at `L = 2` is nondivisible (`ℓ = (2, 2)`, `A* = A`), yet
-- Lusztig's second condition fails (`1 - a₀₁ = 4 > 2 = ℓ₀`).
example :
    g2NormDatum.Nondivisible 2 ∧
      g2NormDatum.frobeniusOrder 2 = ![2, 2] ∧
      ¬ g2NormDatum.LusztigConditions 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nondivisible_def]; intro i
    fin_cases i <;> simp only [g2NormDatum] <;> decide
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, g2NormDatum]
  · intro h
    have h01 := h.one_sub_cartan_le (i := 0) (j := 1) (by decide)
      (by simp [frobeniusOrder_def, g2NormDatum])
    simp [frobeniusOrder_def, g2NormDatum] at h01

-- Check 5: `A₁` with `d = (2)` at `L = 2` (`ζ² = -1`) has `ℓ₀ = 1` and `ζ₀* = ζ² = -1`.
example {R : Type*} [Ring R] {ζ : R} (hζ : ζ ^ 2 = -1) :
    a1ScaledDatum.frobeniusOrder 2 0 = 1 ∧ a1ScaledDatum.frobeniusTarget ζ 2 0 = -1 := by
  have h1 : a1ScaledDatum.frobeniusOrder 2 0 = 1 := by simp [frobeniusOrder_def, a1ScaledDatum]
  refine ⟨h1, ?_⟩
  rw [frobeniusTarget_def, h1]
  simpa [a1ScaledDatum] using hζ

-- Check 6: `B₂` with `d = (2, 4)` at `L = 4` has `ℓ = (2, 1)`, ratio `2 = gcd(4, 4) / gcd(4, 2)`
-- (not `gcd(4, 4) = 4`), dual type `A* = Aᵀ`, and agrees with normalized `d = (1, 2)` at `L' = 2`.
example :
    b2ScaledDatum.frobeniusOrder 4 = ![2, 1] ∧
      b2ScaledDatum.frobeniusOrder 4 0 / b2ScaledDatum.frobeniusOrder 4 1 = 2 ∧
      Nat.gcd 4 (b2ScaledDatum.symmetrizer 1) = 4 ∧
      b2ScaledDatum.reducedOrder 4 = 2 ∧
      b2ScaledDatum.frobeniusOrder 4 = b2NormDatum.frobeniusOrder 2 ∧
      (b2ScaledDatum.modifiedDatum 4 (by decide)).cartan = b2ScaledDatum.cartan.transpose := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, b2ScaledDatum]
  · simp [frobeniusOrder_def, b2ScaledDatum]
  · simp [b2ScaledDatum]
  · rw [reducedOrder_def]; decide
  · funext i; fin_cases i <;> simp [frobeniusOrder_def, b2ScaledDatum, b2NormDatum]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [frobeniusOrder_def, b2ScaledDatum]

end Checks
