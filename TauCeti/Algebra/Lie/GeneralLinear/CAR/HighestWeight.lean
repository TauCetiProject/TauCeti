/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Fock
public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
import TauCeti.LinearAlgebra.CliffordAlgebra.FiltrationGradedEquiv

/-!
# A highest-weight vector in the CAR algebra

For the left `gl_n`-action on the Clifford algebra of the trace quadratic form, this file
constructs the ordered-product candidate

`∏_{i < j} dᵢⱼ`,

where `dᵢⱼ = ι(Eᵢⱼ)`, for any finite linearly ordered index type. Over a field in which
the candidate is nonzero. When `2` is invertible, it is a highest-weight vector of weight
`i ↦ 1/2 * (1 + 2 * #{j | i < j})`. For `n = Fin N` in characteristic zero, this is the
staircase `(N - 1/2, N - 3/2, …, 1/2)` required by the later CAR simple-submodule and isotypy
results.

## Main definitions

* `TauCeti.carPositiveMatrixUnitFamily`: the canonically ordered positive matrix units.
* `TauCeti.carHighestWeightVector`: their ordered Clifford product candidate.

## Main results

* `TauCeti.carHighestWeightVector_ne_zero`: the candidate is nonzero over any field.
* `TauCeti.carHighestWeightVector_eq_one_of_subsingleton`: in ranks zero and one the empty
  ordered product is `1`.
* `TauCeti.isGlHighestWeightVector_carHighestWeightVector`: its direct highest-weight equation.
* `TauCeti.isGlHighestWeightVector_glStaircase_carHighestWeightVector`: the `Fin N` staircase form.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transform. Groups 6
  (2001), Proposition 2.4 and Example 2.5(1). The construction below formalizes its `gl_N` on
  `M_N` worked instance.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open scoped BigOperators

namespace TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
/-! ### The ordered positive-root product -/

/-- The positive roots of `gl_n`, represented by strictly upper-triangular index pairs. -/
def carPositiveRootPairs (n : Type*) [Fintype n] [LinearOrder n] : Finset (n × n) :=
  Finset.univ.filter fun ij => ij.1 < ij.2

/-- Membership in `carPositiveRootPairs` means that the first index is strictly below the second. -/
@[simp]
theorem mem_carPositiveRootPairs {n : Type*} [Fintype n] [LinearOrder n] {i j : n} :
    (i, j) ∈ carPositiveRootPairs n ↔ i < j := by
  rw [carPositiveRootPairs.eq_def]
  simp

/-- The lexicographic linear order used to enumerate pairs of ordered indices. -/
@[instance_reducible] private noncomputable def carPairLinearOrder
    (n : Type*) [LinearOrder n] : LinearOrder (n × n) := by
  let _ : LinearOrder (n ×ₗ n) := Prod.Lex.instLinearOrder n n
  exact LinearOrder.lift' toLex (Equiv.injective toLex)

/-- The increasing enumeration of positive-root pairs, valued in the lexicographically ordered
pair type. -/
noncomputable def carPositiveRootPairOrderEmbedding
    (n : Type*) [Fintype n] [LinearOrder n] :
    Fin (carPositiveRootPairs n).card ↪o n ×ₗ n := by
  let _ : LinearOrder (n ×ₗ n) := Prod.Lex.instLinearOrder n n
  let _ : LinearOrder (n × n) := carPairLinearOrder n
  exact ((carPositiveRootPairs n).orderEmbOfFin rfl).trans
    { toFun := toLex
      inj' := Equiv.injective toLex
      map_rel_iff' := Iff.rfl }

/-- The positive-root pair at a given place in the canonical lexicographic enumeration. -/
noncomputable def carPositiveRootPair (n : Type*) [Fintype n] [LinearOrder n]
    (r : Fin (carPositiveRootPairs n).card) : n × n := by
  let _ := carPairLinearOrder n
  exact (carPositiveRootPairs n).orderEmbOfFin rfl r

/-- The order embedding enumerates the same pair as `carPositiveRootPair`. -/
@[simp]
theorem carPositiveRootPairOrderEmbedding_apply (n : Type*) [Fintype n] [LinearOrder n]
    (r : Fin (carPositiveRootPairs n).card) :
    ofLex (carPositiveRootPairOrderEmbedding n r) = carPositiveRootPair n r := by
  let _ : LinearOrder (n ×ₗ n) := Prod.Lex.instLinearOrder n n
  let _ : LinearOrder (n × n) := carPairLinearOrder n
  rw [carPositiveRootPair.eq_def]
  rfl

/-- Every pair in the canonical enumeration is a positive-root pair. -/
@[simp]
theorem carPositiveRootPair_mem (n : Type*) [Fintype n] [LinearOrder n]
    (r : Fin (carPositiveRootPairs n).card) :
    carPositiveRootPair n r ∈ carPositiveRootPairs n := by
  let _ := carPairLinearOrder n
  rw [carPositiveRootPair.eq_def]
  exact Finset.orderEmbOfFin_mem (carPositiveRootPairs n) rfl r

/-- The canonical enumeration ranges over exactly the positive-root pairs. -/
theorem range_carPositiveRootPair (n : Type*) [Fintype n] [LinearOrder n] :
    Set.range (carPositiveRootPair n) = carPositiveRootPairs n := by
  let _ : LinearOrder (n ×ₗ n) := Prod.Lex.instLinearOrder n n
  let _ : LinearOrder (n × n) := carPairLinearOrder n
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    exact carPositiveRootPair_mem n r
  · intro hp
    have hp' : p ∈ (carPositiveRootPairs n : Set (n × n)) := hp
    rw [← Finset.range_orderEmbOfFin (carPositiveRootPairs n) rfl] at hp'
    obtain ⟨r, hr⟩ := hp'
    refine ⟨r, ?_⟩
    rw [carPositiveRootPair.eq_def]
    exact hr

/-- The positive matrix units in the lexicographic order on their index pairs. -/
noncomputable def carPositiveMatrixUnitFamily (K : Type*) [CommRing K]
    (n : Type*) [Fintype n] [LinearOrder n] :
    Fin (carPositiveRootPairs n).card → Matrix n n K := by
  exact fun r => Matrix.stdBasis K n n (carPositiveRootPair n r)

/-- The positive matrix-unit family is obtained by applying `Matrix.stdBasis` to the canonical
positive-root enumeration. -/
@[simp]
theorem carPositiveMatrixUnitFamily_apply (K : Type*) [CommRing K]
    (n : Type*) [Fintype n] [LinearOrder n] (r : Fin (carPositiveRootPairs n).card) :
    carPositiveMatrixUnitFamily K n r = Matrix.stdBasis K n n (carPositiveRootPair n r) :=
  carPositiveMatrixUnitFamily.eq_def K n r

/-- The ordered product candidate formed from all positive matrix-unit Clifford generators. It is
proved below to be a highest-weight vector over a field when `2` is invertible. -/
noncomputable def carHighestWeightVector (K : Type*) [CommRing K]
    (n : Type*) [Fintype n] [LinearOrder n] :
    CliffordAlgebra (traceQuadraticForm K n) :=
  ((List.ofFn (carPositiveMatrixUnitFamily K n)).map
    (CliffordAlgebra.ι (traceQuadraticForm K n))).prod

/-- The defining ordered-product equation for `carHighestWeightVector`. -/
theorem carHighestWeightVector_def (K : Type*) [CommRing K]
    (n : Type*) [Fintype n] [LinearOrder n] :
    carHighestWeightVector K n =
      ((List.ofFn (carPositiveMatrixUnitFamily K n)).map
        (CliffordAlgebra.ι (traceQuadraticForm K n))).prod :=
  carHighestWeightVector.eq_def K n

/-- If the index type has at most one element, there are no positive roots and the ordered-product
candidate is `1`. This includes both the rank-zero and rank-one boundary cases. -/
@[simp]
theorem carHighestWeightVector_eq_one_of_subsingleton (K : Type*) [CommRing K]
    (n : Type*) [Fintype n] [LinearOrder n] [Subsingleton n] :
    carHighestWeightVector K n = 1 := by
  have hpairs : carPositiveRootPairs n = ∅ := by
    ext ⟨i, j⟩
    simp only [carPositiveRootPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact fun hij => (lt_irrefl j) (Subsingleton.elim i j ▸ hij)
  rw [carHighestWeightVector_def]
  have hroots : List.ofFn (carPositiveMatrixUnitFamily K n) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_ofFn, hpairs, Finset.card_empty]
  rw [hroots]
  simp

/-- Every positive matrix unit occurs in the canonical family. -/
theorem carPositiveMatrixUnitFamily_mem {K n : Type*} [CommRing K] [Fintype n] [LinearOrder n]
    {i j : n} (hij : i < j) :
    Matrix.single i j (1 : K) ∈ List.ofFn (carPositiveMatrixUnitFamily K n) := by
  let _ := carPairLinearOrder n
  rw [List.mem_ofFn]
  have hp : (i, j) ∈ carPositiveRootPairs n := by
    exact mem_carPositiveRootPairs.mpr hij
  have hp' : (i, j) ∈ (carPositiveRootPairs n : Set (n × n)) := hp
  rw [← Finset.range_orderEmbOfFin (carPositiveRootPairs n) rfl] at hp'
  obtain ⟨r, hr⟩ := hp'
  refine ⟨r, ?_⟩
  rw [carPositiveMatrixUnitFamily_apply, carPositiveRootPair.eq_def, hr,
    Matrix.stdBasis_eq_single]

section Field

variable {K n : Type*} [Field K] [Fintype n] [LinearOrder n]

private theorem carPositiveUnits_ortho {i j k l : n}
    (hij : i < j) (hkl : k < l) :
    (traceQuadraticForm K n).IsOrtho
      (Matrix.single i j 1) (Matrix.single k l 1) := by
  rw [← QuadraticMap.isOrtho_polarBilin, polarBilin_traceQuadraticForm,
    Matrix.trace_single_mul, Matrix.single_apply]
  by_cases hpair : j = k ∧ l = i
  · exact absurd (hpair.2 ▸ hpair.1 ▸ hkl) (lt_asymm hij)
  · by_cases hkj : k = j
    · by_cases hli : l = i
      · exact (hpair ⟨hkj.symm, hli⟩).elim
      · simp [hkj, hli]
    · simp [hkj]

omit [LinearOrder n] in
private theorem iota_mul_prod_eq_zero_of_mem
    {a : Matrix n n K} {l : List (Matrix n n K)}
    (ha : a ∈ l) (hQ : traceQuadraticForm K n a = 0)
    (ho : ∀ b ∈ l, (traceQuadraticForm K n).IsOrtho a b) :
    CliffordAlgebra.ι (traceQuadraticForm K n) a
        * (l.map (CliffordAlgebra.ι (traceQuadraticForm K n))).prod = 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [List.map_cons, List.prod_cons]
        rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar, hQ, map_zero, zero_mul]
      · have hab := ho b List.mem_cons_self
        have hol : ∀ c ∈ l, (traceQuadraticForm K n).IsOrtho a c :=
          fun c hc => ho c (List.mem_cons_of_mem b hc)
        simp only [List.map_cons, List.prod_cons]
        rw [← mul_assoc, CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hab, neg_mul,
          mul_assoc, ih ha hol, mul_zero, neg_zero]

/-- The ordered positive-root product is nonzero over any field. -/
theorem carHighestWeightVector_ne_zero :
    carHighestWeightVector K n ≠ 0 := by
  let _ := carPairLinearOrder n
  have hpositive : LinearIndependent K (carPositiveMatrixUnitFamily K n) := by
    convert
      (Matrix.stdBasis K n n).linearIndependent.comp
        ((carPositiveRootPairs n).orderEmbOfFin rfl)
        ((carPositiveRootPairs n).orderEmbOfFin rfl).injective using 1
    rfl
  simpa only [carHighestWeightVector_def, List.map_ofFn] using
    CliffordAlgebra.prod_map_ι_ofFn_ne_zero (traceQuadraticForm K n)
      (carPositiveMatrixUnitFamily K n) hpositive

private theorem positive_iota_mul_carHighestWeightVector_eq_zero
    {i j : n} (hij : i < j) :
    CliffordAlgebra.ι (traceQuadraticForm K n) (Matrix.single i j 1)
        * carHighestWeightVector K n = 0 := by
  apply iota_mul_prod_eq_zero_of_mem (carPositiveMatrixUnitFamily_mem hij)
  · rw [traceQuadraticForm_apply, Matrix.trace_single_mul, Matrix.single_apply]
    simp [ne_of_lt hij]
  · intro b hb
    let _ := carPairLinearOrder n
    rw [List.mem_ofFn] at hb
    obtain ⟨r, rfl⟩ := hb
    have hr := carPositiveRootPair_mem n r
    simp only [carPositiveMatrixUnitFamily_apply]
    generalize hp : carPositiveRootPair n r = p at hr ⊢
    rcases p with ⟨k, l⟩
    rw [Matrix.stdBasis_eq_single]
    apply carPositiveUnits_ortho hij
    simpa only [carPositiveRootPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hr

private noncomputable abbrev carD (i j : n) :
    CliffordAlgebra (traceQuadraticForm K n) :=
  CliffordAlgebra.ι (traceQuadraticForm K n) (Matrix.single i j 1)

private theorem raisingTerm_mul_carHighestWeightVector_eq_zero
    {i j : n} (hij : i < j) (k : n) :
    carD i k * carD k j * carHighestWeightVector K n = 0 := by
  by_cases hkj : k < j
  · rw [mul_assoc, positive_iota_mul_carHighestWeightVector_eq_zero hkj, mul_zero]
  · have hik : i < k := lt_of_lt_of_le hij (le_of_not_gt hkj)
    rw [traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired i k k j 1 1
      (by intro h; exact (ne_of_lt hij) h.2.symm), neg_mul, mul_assoc,
      positive_iota_mul_carHighestWeightVector_eq_zero hik, mul_zero, neg_zero]

private theorem diagonalTerm_mul_carHighestWeightVector (i k : n) :
    carD i k * carD k i * carHighestWeightVector K n =
      if k < i then 0 else if k = i then carHighestWeightVector K n
      else (2 : K) • carHighestWeightVector K n := by
  rcases lt_trichotomy k i with hki | rfl | hik
  · simp only [hki, ↓reduceIte]
    rw [mul_assoc, positive_iota_mul_carHighestWeightVector_eq_zero hki, mul_zero]
  · simp [carD]
  · simp only [not_lt_of_ge hik.le, ne_of_gt hik, ↓reduceIte]
    have hcar := traceQuadraticForm_ι_single_mul_ι_single_add_swap
      (R := K) i k k i 1 1
    have hmul := congrArg
      (fun x : CliffordAlgebra (traceQuadraticForm K n) =>
        x * carHighestWeightVector K n) hcar
    simp only [add_mul, mul_assoc, positive_iota_mul_carHighestWeightVector_eq_zero hik,
      mul_zero, add_zero] at hmul
    rw [mul_assoc]
    simpa [carD, Algebra.smul_def] using hmul

private theorem diagonalScalarSum (i : n) :
    (∑ k : n, if k = i then (1 : K) else if i < k then 2 else 0) =
      1 + 2 * ((Finset.univ.filter fun k : n => i < k).card : K) := by
  calc
    _ = (∑ k : n, if k = i then (1 : K) else 0) +
        ∑ k : n, if i < k then (2 : K) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp_all
    _ = 1 + 2 * ((Finset.univ.filter fun k : n => i < k).card : K) := by
      have hfirst : (∑ k : n, if k = i then (1 : K) else 0) = 1 := by simp
      have hsecond : (∑ k : n, if i < k then (2 : K) else 0) =
          2 * ((Finset.univ.filter fun k : n => i < k).card : K) := by
        rw [← Finset.sum_filter]
        simp [mul_comm]
      rw [hfirst, hsecond]

private theorem diagonalTerm_mul_carHighestWeightVector_eq_smul (i k : n) :
    carD i k * carD k i * carHighestWeightVector K n =
      (if k = i then (1 : K) else if i < k then 2 else 0) •
        carHighestWeightVector K n := by
  rw [diagonalTerm_mul_carHighestWeightVector]
  rcases lt_trichotomy k i with hki | rfl | hik
  · simp [hki, ne_of_lt hki, not_lt_of_ge hki.le]
  · simp
  · simp [hik, ne_of_gt hik, not_lt_of_ge hik.le]

private theorem diagonalSum_mul_carHighestWeightVector (i : n) :
    (∑ k : n, carD i k * carD k i) * carHighestWeightVector K n =
      (1 + 2 * ((Finset.univ.filter fun k : n => i < k).card : K)) •
        carHighestWeightVector K n := by
  rw [Finset.sum_mul]
  simp_rw [diagonalTerm_mul_carHighestWeightVector_eq_smul i]
  rw [← Finset.sum_smul, diagonalScalarSum i]

section Action

variable [h2 : Invertible (2 : K)]

/-- The CAR Lie-ring module instance using the fixed invertibility witness. -/
local instance :
    LieRingModule (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) :=
  @carLieRingModule K n inferInstance inferInstance h2

/-- The CAR Lie-module instance using the fixed invertibility witness. -/
local instance :
    LieModule K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) :=
  @carLieModule K n inferInstance inferInstance h2

private theorem glCliffordHom_single_mul_carHighestWeightVector_eq_zero
    {i j : n} (hij : i < j) :
    (@glCliffordHom K n inferInstance inferInstance h2) (Matrix.single i j 1) *
      carHighestWeightVector K n = 0 := by
  rw [glCliffordHom_single, smul_mul_assoc, Finset.sum_mul]
  simp only [raisingTerm_mul_carHighestWeightVector_eq_zero hij,
    Finset.sum_const_zero, smul_zero]

private theorem raising_lie_carHighestWeightVector_eq_zero
    {i j : n} (hij : i < j) :
    ⁅Matrix.single i j (1 : K), carHighestWeightVector K n⁆ = 0 := by
  rw [car_lie_def]
  exact glCliffordHom_single_mul_carHighestWeightVector_eq_zero hij

private theorem diagonal_lie_carHighestWeightVector (i : n) :
    ⁅Matrix.single i i (1 : K), carHighestWeightVector K n⁆ =
      ((2 : K)⁻¹ * (1 + 2 * ((Finset.univ.filter fun k : n => i < k).card : K))) •
        carHighestWeightVector K n := by
  rw [car_lie_def, glCliffordHom_single, smul_mul_assoc,
    diagonalSum_mul_carHighestWeightVector i, smul_smul]

/-- The ordered product of all positive matrix-unit Clifford generators is a highest-weight vector
for the left `gl_n`-action on the CAR algebra. Its weight at `i` is half of one plus twice the
number of indices strictly above `i`. -/
theorem isGlHighestWeightVector_carHighestWeightVector :
    IsGlHighestWeightVector (fun i : n =>
      (2 : K)⁻¹ * (1 + 2 * ((Finset.univ.filter fun k : n => i < k).card : K)))
      (carHighestWeightVector K n) := by
  rw [isGlHighestWeightVector_iff]
  exact ⟨carHighestWeightVector_ne_zero, diagonal_lie_carHighestWeightVector,
    fun i j hij => raising_lie_carHighestWeightVector_eq_zero hij⟩

section CharZero

variable [CharZero K]

omit h2 in
private theorem half_diagonalScalarSum {N : ℕ} (i : Fin N) :
    (2 : K)⁻¹ *
        (1 + 2 * ((Finset.univ.filter fun k : Fin N => i < k).card : K)) =
      algebraMap ℚ K (glStaircase N i) := by
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi, glStaircase_apply]
  have hi : (i : ℕ) < N := i.isLt
  have hsub : N - 1 - (i : ℕ) = N - ((i : ℕ) + 1) := by omega
  rw [hsub, Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ N)]
  push_cast
  field_simp
  norm_num
  ring

/-- For `Fin N` in characteristic zero, the direct cardinality weight is the scalar extension of
the rational staircase `TauCeti.glStaircase N`. -/
theorem isGlHighestWeightVector_glStaircase_carHighestWeightVector (N : ℕ) :
    IsGlHighestWeightVector (fun i => algebraMap ℚ K (glStaircase N i))
      (carHighestWeightVector K (Fin N)) := by
  have h := isGlHighestWeightVector_carHighestWeightVector (K := K) (n := Fin N)
  rw [isGlHighestWeightVector_iff] at h ⊢
  refine ⟨h.1, ?_, ?_⟩
  · intro i
    simpa [half_diagonalScalarSum, Matrix.single] using h.2.1 i
  · intro i j hij
    simpa [Matrix.single] using h.2.2 i j hij

end CharZero

end Action

end Field

end

end TauCeti
