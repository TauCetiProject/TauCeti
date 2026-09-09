/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Fock
public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
import TauCeti.LinearAlgebra.CliffordAlgebra.FiltrationGradedEquiv
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# A highest-weight vector in the CAR algebra

For the left `gl_N`-action on the Clifford algebra of the trace quadratic form, this file
constructs the ordered product

`d₀₁ d₀₂ ⋯ d₀,N₋₁ d₁₂ ⋯ d_N₋₂,N₋₁`,

where `dᵢⱼ = ι(Eᵢⱼ)`, and proves that it is a highest-weight vector of staircase weight
`(N - 1/2, N - 3/2, …, 1/2)`.

The proof has three ingredients. First, every positive generator `dᵢⱼ`, `i < j`, kills the
product on the left: it anticommutes through the other positive generators until it meets its own
copy, whose square is zero. Consequently every summand in the normal-ordered formula

`Eᵢⱼ ↦ 1/2 ∑ₖ dᵢₖ dₖⱼ`

kills the product when `i < j`. For a diagonal matrix unit, the `k`th summand contributes `0`,
`1`, or `2` according as `k < i`, `k = i`, or `i < k`; after multiplication by `1/2`, this is
`N - 1/2 - i`. Finally, the product is nonzero because its leading Clifford-filtration term is
the exterior product of distinct standard matrix units. The PBW equivalence identifies that
leading term with a nonzero exterior basis vector.

## Main definitions

* `TauCeti.carHighestWeightVector`: the ordered product of the positive matrix-unit Clifford
  generators.

## Main results

* `TauCeti.isGlHighestWeightVector_carHighestWeightVector`: this product is a highest-weight
  vector for the scalar extension of `TauCeti.glStaircase`.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open scoped BigOperators

namespace TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.decEq

/-! ### The ordered positive-root product -/

/-- The strict upper-triangular matrix units, encoded in a finite linearly ordered type so their
Clifford generators have a canonical order. -/
private def carPositiveRootCodes (N : ℕ) : Finset (Fin (N * N)) :=
  Finset.univ.filter fun p =>
    let ij := finProdFinEquiv.symm p
    ij.1 < ij.2

/-- The standard matrix unit indexed by an encoded pair. -/
private noncomputable def carRootMatrix (K : Type*) [CommRing K] (N : ℕ)
    (p : Fin (N * N)) : Matrix (Fin N) (Fin N) K :=
  Matrix.stdBasis K (Fin N) (Fin N) (finProdFinEquiv.symm p)

/-- The increasing enumeration of the positive matrix units. -/
private noncomputable def carPositiveRootFamily (K : Type*) [CommRing K] (N : ℕ) :
    Fin (carPositiveRootCodes N).card → Matrix (Fin N) (Fin N) K := fun r =>
  carRootMatrix K N ((carPositiveRootCodes N).orderEmbOfFin rfl r)

/-- The ordered product of all strictly upper-triangular matrix-unit generators in the Clifford
algebra of the trace quadratic form. This is the canonical highest-weight vector for the left
`gl_N`-action on the CAR algebra. -/
noncomputable def carHighestWeightVector (K : Type*) [CommRing K] (N : ℕ) :
    CliffordAlgebra (traceQuadraticForm K (Fin N)) :=
  ((List.ofFn (carPositiveRootFamily K N)).map
    (CliffordAlgebra.ι (traceQuadraticForm K (Fin N)))).prod

section Field

variable {K : Type*} [Field K]

private theorem carPositiveRootFamily_mem {N : ℕ} {i j : Fin N} (hij : i < j) :
    Matrix.single i j (1 : K) ∈ List.ofFn (carPositiveRootFamily K N) := by
  rw [List.mem_ofFn]
  have hp : finProdFinEquiv (i, j) ∈ carPositiveRootCodes N := by
    simp only [carPositiveRootCodes, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [Equiv.symm_apply_apply] using hij
  have hp' : finProdFinEquiv (i, j) ∈ (carPositiveRootCodes N : Set (Fin (N * N))) := hp
  rw [← Finset.range_orderEmbOfFin (carPositiveRootCodes N) rfl] at hp'
  obtain ⟨r, hr⟩ := hp'
  refine ⟨r, ?_⟩
  simp [carPositiveRootFamily, carRootMatrix, hr, Matrix.stdBasis_eq_single]

private theorem carPositiveUnits_ortho {N : ℕ} {i j k l : Fin N}
    (hij : i < j) (hkl : k < l) :
    (traceQuadraticForm K (Fin N)).IsOrtho
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

private theorem iota_mul_prod_eq_zero_of_mem
    {N : ℕ} {a : Matrix (Fin N) (Fin N) K}
    {l : List (Matrix (Fin N) (Fin N) K)}
    (ha : a ∈ l) (hQ : traceQuadraticForm K (Fin N) a = 0)
    (ho : ∀ b ∈ l, (traceQuadraticForm K (Fin N)).IsOrtho a b) :
    CliffordAlgebra.ι (traceQuadraticForm K (Fin N)) a
        * (l.map (CliffordAlgebra.ι (traceQuadraticForm K (Fin N)))).prod = 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [List.map_cons, List.prod_cons]
        rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar, hQ, map_zero, zero_mul]
      · have hab := ho b List.mem_cons_self
        have hol : ∀ c ∈ l, (traceQuadraticForm K (Fin N)).IsOrtho a c :=
          fun c hc => ho c (List.mem_cons_of_mem b hc)
        simp only [List.map_cons, List.prod_cons]
        rw [← mul_assoc, CliffordAlgebra.ι_mul_ι_comm_of_isOrtho hab, neg_mul,
          mul_assoc, ih ha hol, mul_zero, neg_zero]

private theorem prod_iota_ne_zero [Invertible (2 : K)]
    {M : Type*} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) {n : ℕ} (v : Fin n → M) (hv : LinearIndependent K v) :
    (List.ofFn ((CliffordAlgebra.ι Q) ∘ v)).prod ≠ 0 := by
  cases n with
  | zero => simp
  | succ k =>
      have hx : exteriorPower.ιMulti K (k + 1) v ≠ 0 := by
        have hfamily := exteriorPower.ιMulti_family_linearIndependent_field (K := K)
          (k + 1) hv
        have hne := hfamily.ne_zero
          (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin (k + 1)) (k + 1))
        have hemb : Set.powersetCard.ofFinEmbEquiv.symm
            (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin (k + 1)) (k + 1)) =
            OrderEmbedding.id (Fin (k + 1)) := by
          symm
          exact Finset.orderEmbOfFin_unique' (by simp) (fun _ => by simp)
        simpa [exteriorPower.ιMulti_family, hemb] using hne
      intro hzero
      have hlead := CliffordAlgebra.filtrationLeadingTerm_apply_ιMulti Q k v
      have hmem : (List.ofFn ((CliffordAlgebra.ι Q) ∘ v)).prod ∈
          CliffordAlgebra.filtration Q (k + 1) := by
        rw [← List.map_ofFn]
        exact CliffordAlgebra.prod_map_ι_mem_filtration Q (k := k + 1)
          (l := List.ofFn v) (by simp)
      have hsub : (⟨(List.ofFn ((CliffordAlgebra.ι Q) ∘ v)).prod, hmem⟩ :
          CliffordAlgebra.filtration Q (k + 1)) = 0 := Subtype.ext hzero
      have hquot := congrArg
        (fun x : CliffordAlgebra.filtration Q (k + 1) =>
          (Submodule.Quotient.mk x : TauCeti.Algebra.wordFiltration.GradedPiece
            (CliffordAlgebra.ι Q) (k + 1))) hsub
      have himage : CliffordAlgebra.filtrationLeadingTerm Q k
          (exteriorPower.ιMulti K (k + 1) v) = 0 := hlead.trans (by simpa using hquot)
      rw [CliffordAlgebra.filtrationLeadingTerm_eq_filtrationGradedEquiv_symm] at himage
      apply hx
      apply (CliffordAlgebra.filtrationGradedEquiv Q k).symm.injective
      rw [map_zero]
      exact himage

private theorem carHighestWeightVector_ne_zero [Invertible (2 : K)] (N : ℕ) :
    carHighestWeightVector K N ≠ 0 := by
  have hfull : LinearIndependent K (carRootMatrix K N) := by
    change LinearIndependent K (fun p =>
      Matrix.stdBasis K (Fin N) (Fin N) (finProdFinEquiv.symm p))
    exact (Matrix.stdBasis K (Fin N) (Fin N)).linearIndependent.comp finProdFinEquiv.symm
      finProdFinEquiv.symm.injective
  have hpositive : LinearIndependent K (carPositiveRootFamily K N) := by
    change LinearIndependent K (fun r =>
      carRootMatrix K N ((carPositiveRootCodes N).orderEmbOfFin rfl r))
    exact hfull.comp ((carPositiveRootCodes N).orderEmbOfFin rfl)
      ((carPositiveRootCodes N).orderEmbOfFin rfl).injective
  simpa [carHighestWeightVector, List.map_ofFn] using
    prod_iota_ne_zero (traceQuadraticForm K (Fin N)) (carPositiveRootFamily K N) hpositive

private theorem positive_iota_mul_carHighestWeightVector_eq_zero
    {N : ℕ} {i j : Fin N} (hij : i < j) :
    CliffordAlgebra.ι (traceQuadraticForm K (Fin N)) (Matrix.single i j 1)
        * carHighestWeightVector K N = 0 := by
  apply iota_mul_prod_eq_zero_of_mem (carPositiveRootFamily_mem hij)
  · rw [traceQuadraticForm_apply, Matrix.trace_single_mul, Matrix.single_apply]
    simp [ne_of_lt hij]
  · intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨r, rfl⟩ := hb
    have hr := Finset.orderEmbOfFin_mem (carPositiveRootCodes N) rfl r
    rw [carPositiveRootFamily, carRootMatrix, Matrix.stdBasis_eq_single]
    apply carPositiveUnits_ortho hij
    simpa only [carPositiveRootCodes, Finset.mem_filter, Finset.mem_univ, true_and] using hr

private noncomputable abbrev carD {N : ℕ} (i j : Fin N) :
    CliffordAlgebra (traceQuadraticForm K (Fin N)) :=
  CliffordAlgebra.ι (traceQuadraticForm K (Fin N)) (Matrix.single i j 1)

private theorem raisingTerm_mul_carHighestWeightVector_eq_zero
    {N : ℕ} {i j : Fin N} (hij : i < j) (k : Fin N) :
    carD i k * carD k j * carHighestWeightVector K N = 0 := by
  by_cases hkj : k < j
  · rw [mul_assoc, positive_iota_mul_carHighestWeightVector_eq_zero hkj, mul_zero]
  · have hik : i < k := lt_of_lt_of_le hij (le_of_not_gt hkj)
    rw [traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired i k k j 1 1
      (by intro h; exact (ne_of_lt hij) h.2.symm), neg_mul, mul_assoc,
      positive_iota_mul_carHighestWeightVector_eq_zero hik, mul_zero, neg_zero]

private theorem diagonalTerm_mul_carHighestWeightVector {N : ℕ} (i k : Fin N) :
    carD i k * carD k i * carHighestWeightVector K N =
      if k < i then 0 else if k = i then carHighestWeightVector K N
      else (2 : K) • carHighestWeightVector K N := by
  rcases lt_trichotomy k i with hki | rfl | hik
  · simp only [hki, ↓reduceIte]
    rw [mul_assoc, positive_iota_mul_carHighestWeightVector_eq_zero hki, mul_zero]
  · simp [carD]
  · simp only [not_lt_of_ge hik.le, ne_of_gt hik, ↓reduceIte]
    have hcar := traceQuadraticForm_ι_single_mul_ι_single_add_swap
      (R := K) i k k i 1 1
    have hmul := congrArg
      (fun x : CliffordAlgebra (traceQuadraticForm K (Fin N)) =>
        x * carHighestWeightVector K N) hcar
    simp only [add_mul, mul_assoc, positive_iota_mul_carHighestWeightVector_eq_zero hik,
      mul_zero, add_zero] at hmul
    rw [mul_assoc]
    simpa [carD, Algebra.smul_def] using hmul

private theorem diagonalScalarSum {N : ℕ} (i : Fin N) :
    (∑ k : Fin N, if k = i then (1 : K) else if i < k then 2 else 0) =
      1 + 2 * ((Finset.Ioi i).card : K) := by
  calc
    _ = (∑ k : Fin N, if k = i then (1 : K) else 0) +
        ∑ k : Fin N, if i < k then (2 : K) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp_all
    _ = 1 + 2 * ((Finset.Ioi i).card : K) := by
      have hfirst : (∑ k : Fin N, if k = i then (1 : K) else 0) = 1 := by simp
      have hsecond : (∑ k : Fin N, if i < k then (2 : K) else 0) =
          2 * ((Finset.Ioi i).card : K) := by
        rw [← Finset.sum_filter]
        simp [Finset.filter_lt_eq_Ioi, mul_comm]
      rw [hfirst, hsecond]

private theorem diagonalTerm_mul_carHighestWeightVector_eq_smul {N : ℕ}
    (i k : Fin N) :
    carD i k * carD k i * carHighestWeightVector K N =
      (if k = i then (1 : K) else if i < k then 2 else 0) •
        carHighestWeightVector K N := by
  rw [diagonalTerm_mul_carHighestWeightVector]
  rcases lt_trichotomy k i with hki | rfl | hik
  · simp [hki, ne_of_lt hki, not_lt_of_ge hki.le]
  · simp
  · simp [hik, ne_of_gt hik, not_lt_of_ge hik.le]

private theorem diagonalSum_mul_carHighestWeightVector {N : ℕ} (i : Fin N) :
    (∑ k : Fin N, carD i k * carD k i) * carHighestWeightVector K N =
      (1 + 2 * ((Finset.Ioi i).card : K)) • carHighestWeightVector K N := by
  rw [Finset.sum_mul]
  simp_rw [diagonalTerm_mul_carHighestWeightVector_eq_smul i]
  rw [← Finset.sum_smul, diagonalScalarSum i]

section Action

variable [CharZero K] [h2 : Invertible (2 : K)]

/-- The CAR Lie-ring module instance using the fixed invertibility witness. -/
local instance {N : ℕ} :
    LieRingModule (Matrix (Fin N) (Fin N) K)
      (CliffordAlgebra (traceQuadraticForm K (Fin N))) :=
  @carLieRingModule K (Fin N) inferInstance inferInstance h2

/-- The CAR Lie-module instance using the fixed invertibility witness. -/
local instance {N : ℕ} :
    LieModule K (Matrix (Fin N) (Fin N) K)
      (CliffordAlgebra (traceQuadraticForm K (Fin N))) :=
  @carLieModule K (Fin N) inferInstance inferInstance h2

omit [CharZero K] in
/-- `glCliffordHom_single` restated with this file's matrix-unit decidability instance. -/
private theorem glCliffordHom_single_current {N : ℕ} (i j : Fin N) :
    (@glCliffordHom K (Fin N) inferInstance inferInstance h2) (Matrix.single i j 1) =
      (2 : K)⁻¹ • ∑ k : Fin N, carD i k * carD k j := by
  convert @glCliffordHom_single K (Fin N) inferInstance inferInstance h2 i j using 1
  · apply congrArg (@glCliffordHom K (Fin N) inferInstance inferInstance h2)
    ext a b
    simp [Matrix.single]
  · apply congrArg ((2 : K)⁻¹ • ·)
    apply Finset.sum_congr rfl
    intro k _
    apply congrArg₂ (· * ·)
    · apply congrArg (CliffordAlgebra.ι (traceQuadraticForm K (Fin N)))
      ext a b
      simp [Matrix.single]
    · apply congrArg (CliffordAlgebra.ι (traceQuadraticForm K (Fin N)))
      ext a b
      simp [Matrix.single]

omit [CharZero K] in
private theorem glCliffordHom_single_mul_carHighestWeightVector_eq_zero
    {N : ℕ} {i j : Fin N} (hij : i < j) :
    (@glCliffordHom K (Fin N) inferInstance inferInstance h2) (Matrix.single i j 1) *
      carHighestWeightVector K N = 0 := by
  rw [glCliffordHom_single_current i j, smul_mul_assoc, Finset.sum_mul]
  simp only [raisingTerm_mul_carHighestWeightVector_eq_zero hij,
    Finset.sum_const_zero, smul_zero]

omit [CharZero K] in
private theorem raising_lie_carHighestWeightVector_eq_zero
    {N : ℕ} {i j : Fin N} (hij : i < j) :
    ⁅Matrix.single i j (1 : K), carHighestWeightVector K N⁆ = 0 := by
  rw [car_lie_def]
  exact glCliffordHom_single_mul_carHighestWeightVector_eq_zero hij

omit h2 in
private theorem half_diagonalScalarSum {N : ℕ} (i : Fin N) :
    (2 : K)⁻¹ * (1 + 2 * ((Finset.Ioi i).card : K)) =
      algebraMap ℚ K (glStaircase N i) := by
  rw [Fin.card_Ioi, glStaircase_apply]
  have hi : (i : ℕ) < N := i.isLt
  rw [show N - 1 - (i : ℕ) = N - ((i : ℕ) + 1) by omega,
    Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ N)]
  push_cast
  field_simp
  norm_num
  ring

private theorem diagonal_lie_carHighestWeightVector {N : ℕ} (i : Fin N) :
    ⁅Matrix.single i i (1 : K), carHighestWeightVector K N⁆ =
      algebraMap ℚ K (glStaircase N i) • carHighestWeightVector K N := by
  rw [car_lie_def, glCliffordHom_single_current i i, smul_mul_assoc,
    diagonalSum_mul_carHighestWeightVector i, smul_smul, half_diagonalScalarSum i]

/-- The ordered product of all positive matrix-unit Clifford generators is a highest-weight vector
for the left `gl_N`-action on the CAR algebra. Its weight is the scalar extension of the rational
staircase `TauCeti.glStaircase N`. -/
theorem isGlHighestWeightVector_carHighestWeightVector (N : ℕ) :
    IsGlHighestWeightVector (fun i => algebraMap ℚ K (glStaircase N i))
      (carHighestWeightVector K N) := by
  rw [isGlHighestWeightVector_iff]
  exact ⟨carHighestWeightVector_ne_zero N, diagonal_lie_carHighestWeightVector,
    fun i j hij => raising_lie_carHighestWeightVector_eq_zero hij⟩

end Action

end Field

end

end TauCeti
