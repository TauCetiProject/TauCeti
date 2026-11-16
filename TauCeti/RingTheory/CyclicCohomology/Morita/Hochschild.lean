/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.HochschildCohomology.Complex
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For a unital associative `R`-algebra `A`, an `R`-module `M`, and a finite nonempty index type `ι`,
this file proves that the generalized matrix trace (`TauCeti.matrixCochainExtension`) induces an
isomorphism `HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` on Hochschild
cohomology over every commutative ring `R`.

Fix a corner index `r : ι`. Pullback along the nonunital corner inclusion
`x ↦ Matrix.single r r x` (`TauCeti.matrixCochainCornerRestriction`) is a left inverse to
`matrixCochainExtension` already on cochains and commutes with every Hochschild coface. On the
Hochschild cochain complex of `Matrix ι ι A`, the dual of Loday's matrix-unit homotopy
`(hᵢ* ψ)(a₀, …, aₙ) = ∑_q ψ(a₀ E_{q₀ r}, E_{r q₀} a₁ E_{q₁ r}, …, E_{r q_{i-1}} aᵢ E_{qᵢ r},
E_{r qᵢ}, aᵢ₊₁, …, aₙ)`
satisfies `b H + H b = 1 - tr ∘ res_r` (and `H₀ b₀ = 1 - tr ∘ res_r` in degree zero). Hence
`hochschildCohomology.matrixExtension` is bijective with two-sided inverse
`hochschildCohomology.cornerRestriction r`.

All induced cohomology maps are constructed as `R`-linear maps rather than `ModuleCat R` morphisms,
so the index type `ι` may live in any universe independent of `R`, `A`, and `M`.

## Main definitions

* `TauCeti.matrixCochainCornerRestriction`, `TauCeti.matrixCyclicCochainCornerRestriction`:
  restriction of a matrix cochain (and of a cyclic matrix cochain) to the `(r, r)` corner.
* `TauCeti.hochschildCohomology.matrixExtension`, `TauCeti.hochschildCohomology.cornerRestriction`,
  `TauCeti.hochschildCohomology.matrixEquiv`: matrix extension, corner restriction, and the Morita
  equivalence on Hochschild cohomology.

## Main results

* `TauCeti.matrixCochainCornerRestriction_matrixCochainExtension`: corner restriction is a left
  inverse to matrix extension on cochains.
* `TauCeti.sub_matrixCochainExtension_cornerRestriction_mem_hochschildCoboundaries`: on a
  Hochschild cocycle `ψ` on `Matrix ι ι A`, `ψ - tr (res_r ψ)` is a Hochschild coboundary.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of Hochschild
  cohomology over every commutative ring.

## References

* J.-L. Loday, *Cyclic Homology*, §1.2.4.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
-/

public section

namespace TauCeti

/-! ### Corner restriction on cochains -/

section CornerRestriction

variable {R A M ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a cochain on `Matrix ι ι A` to the `(r, r)` corner `A` via
`x ↦ Matrix.single r r x`. -/
def matrixCochainCornerRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun φ := φ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Corner restriction evaluates a matrix cochain on matrices supported in the `(r, r)` entry. -/
@[simp]
theorem matrixCochainCornerRestriction_apply (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → A) :
    matrixCochainCornerRestriction r n φ a = φ fun j ↦ Matrix.single r r (a j) :=
  (rfl)

/-- Corner restriction is a left inverse to matrix extension on cochains. -/
@[simp]
theorem matrixCochainCornerRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainCornerRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext a
  exact matrixCochainExtension_single ι r n φ a

end CornerRestriction

section CornerRestrictionCyclic

variable {R A M ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Corner restriction maps cyclic cochains to cyclic cochains. -/
theorem matrixCochainCornerRestriction_mem_cyclicCochains (r : ι) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ cyclicCochains R (Matrix ι ι A) M n) :
    matrixCochainCornerRestriction r n φ ∈ cyclicCochains R A M n := by
  have h := (cyclicCochainsMap M (Matrix.singleLinearMap R r r) n ⟨φ, hφ⟩).2
  rwa [coe_cyclicCochainsMap_apply] at h

/-- Restrict a cyclic cochain on `Matrix ι ι A` to the `(r, r)` corner `A`. -/
def matrixCyclicCochainCornerRestriction (r : ι) (n : ℕ) :
    cyclicCochains R (Matrix ι ι A) M n →ₗ[R] cyclicCochains R A M n :=
  (matrixCochainCornerRestriction r n).restrict
    fun _ ↦ matrixCochainCornerRestriction_mem_cyclicCochains r

/-- The underlying cochain of `matrixCyclicCochainCornerRestriction` is
`matrixCochainCornerRestriction`. -/
@[simp]
theorem coe_matrixCyclicCochainCornerRestriction_apply (r : ι) (n : ℕ)
    (φ : cyclicCochains R (Matrix ι ι A) M n) :
    (matrixCyclicCochainCornerRestriction r n φ :
        MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) =
      matrixCochainCornerRestriction r n φ :=
  (rfl)

end CornerRestrictionCyclic

section CornerRestrictionAlgebra

variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

/-- The nonunital corner embedding `x ↦ Matrix.single r r x` into square matrices. -/
private def singleCornerNonUnitalAlgHom (r : ι) : A →ₙₐ[R] Matrix ι ι A where
  __ := Matrix.singleLinearMap R r r
  map_zero' := Matrix.single_zero r r
  map_mul' x y := (Matrix.single_mul_single_same x r r r y).symm

/-- Corner restriction commutes with every Hochschild coface. -/
theorem matrixCochainCornerRestriction_hochschildCoface (r : ι) {n : ℕ} (i : Fin (n + 2))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainCornerRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i φ) =
      hochschildCoface R A M i (matrixCochainCornerRestriction r n φ) := by
  ext a
  simp only [matrixCochainCornerRestriction_apply, hochschildCoface_apply]
  congr 1
  exact (comp_hochschildFace (singleCornerNonUnitalAlgHom (R := R) r) i a).symm

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCochainCornerRestriction_hochschildCoboundary (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainCornerRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n φ) =
      hochschildCoboundary R A M n (matrixCochainCornerRestriction r n φ) := by
  ext a
  simp only [matrixCochainCornerRestriction_apply, hochschildCoboundary_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  exact (comp_hochschildFace (singleCornerNonUnitalAlgHom (R := R) r) i a).symm

end CornerRestrictionAlgebra

section HochschildCocycles

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι]

/-- Matrix extension maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix extension maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainExtension ι n ψ, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩

/-- Corner restriction maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainCornerRestriction_mem_hochschildCocycles [DecidableEq ι] (r : ι) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCochainCornerRestriction r n φ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainCornerRestriction_hochschildCoboundary, hφ, map_zero]

/-- Corner restriction maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainCornerRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCochainCornerRestriction r n φ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainCornerRestriction r n ψ,
        (matrixCochainCornerRestriction_hochschildCoboundary r n ψ).symm⟩

end HochschildCocycles

/-! ### Loday's Hochschild cochain homotopy -/

/-- The Hochschild coboundary as an alternating sum of cofaces. -/
private theorem hochschildCoboundary_eq_sum_coface {R B M : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M] (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M) :
    hochschildCoboundary R B M n ψ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R B M i ψ := by
  ext a
  simp [hochschildCoboundary_apply, hochschildCoface_apply]

section HochschildHomotopy

variable {R A M ι : Type*} [Semiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

/-- The coordinatewise linear map applied to the `j`-th matrix entry in Loday's homotopy term
`hᵢ*`: slot `0` is multiplied on the right by `E_{q₀ r}`, slots `0 < j ≤ i` are sandwiched between
`E_{r q_{j-1}}` and `E_{q_j r}`, and slots `j > i` are left unchanged. -/
private def homotopyEntry (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (j : Fin (n + 1)) : Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if j = 0 then
    LinearMap.mulRight R (Matrix.single (q 0) r 1)
  else if hji : j ≤ i then
    LinearMap.mulRight R (Matrix.single (q ⟨j, Nat.lt_succ_of_le hji⟩) r 1) ∘ₗ
      LinearMap.mulLeft R (Matrix.single r (q ⟨(j : ℕ) - 1,
        Nat.lt_succ_of_le ((Nat.sub_le _ 1).trans hji)⟩) 1)
  else
    LinearMap.id

/-- The `(n + 2)`-tuple of matrices fed to `ψ` in the `q`-summand of `hᵢ* ψ`: insert `E_{r qᵢ}`
at position `i + 1` into the transformed `(n + 1)`-tuple. -/
private def homotopyTuple (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) : Fin (n + 2) → Matrix ι ι A :=
  i.succ.insertNth (Matrix.single r (q (Fin.last i)) 1) fun j ↦
    homotopyEntry (R := R) r i q j (a j)

private theorem homotopyTuple_zero (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) :
    homotopyTuple (R := R) r i q a 0 = a 0 * Matrix.single (q 0) r 1 := by
  have h0 : (0 : Fin (n + 2)) = i.succ.succAbove (0 : Fin (n + 1)) := by
    rw [Fin.succAbove_of_castSucc_lt i.succ (0 : Fin (n + 1)) (by simp), Fin.castSucc_zero]
  rw [h0, homotopyTuple, Fin.insertNth_apply_succAbove]
  simp [homotopyEntry]

private theorem homotopyTuple_of_pos_of_le (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) (m : Fin (n + 2)) (hm0 : 0 < (m : ℕ)) (hmi : (m : ℕ) ≤ i) :
    homotopyTuple (R := R) r i q a m =
      Matrix.single r (q ⟨(m : ℕ) - 1, by omega⟩) 1 * a ⟨m, by omega⟩ *
        Matrix.single (q ⟨m, by omega⟩) r 1 := by
  let j : Fin (n + 1) := ⟨m, by omega⟩
  have hm : m = i.succ.succAbove j := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, j]; omega)]
    exact Fin.ext rfl
  have hj0 : j ≠ 0 := by intro h; exact hm0.ne' (congrArg Fin.val h)
  have hji : j ≤ i := hmi
  conv_lhs => rw [hm]
  rw [homotopyTuple, Fin.insertNth_apply_succAbove]
  simp [homotopyEntry, hj0, hji, j]

private theorem homotopyTuple_succ_self (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) :
    homotopyTuple (R := R) r i q a i.succ = Matrix.single r (q (Fin.last i)) 1 := by
  rw [homotopyTuple, Fin.insertNth_apply_same]

private theorem homotopyTuple_of_gt (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) (m : Fin (n + 2)) (hm : (i : ℕ) + 1 < m) :
    homotopyTuple (R := R) r i q a m = a ⟨(m : ℕ) - 1, by omega⟩ := by
  let j : Fin (n + 1) := ⟨(m : ℕ) - 1, by omega⟩
  have hm' : m = i.succ.succAbove j := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, j]; omega)]
    exact Fin.ext (by simp [j]; omega)
  have hj0 : j ≠ 0 := by intro h; have := congrArg Fin.val h; simp [j] at this; omega
  have hji : ¬ j ≤ i := by simp [Fin.le_def, j]; omega
  conv_lhs => rw [hm']
  rw [homotopyTuple, Fin.insertNth_apply_succAbove]
  simp [homotopyEntry, hj0, hji, j]

private theorem homotopyTuple_update (r : ι) {n : ℕ} (i : Fin (n + 1)) (q : Fin (i + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) (j : Fin (n + 1)) (z : Matrix ι ι A) :
    homotopyTuple (R := R) r i q (Function.update a j z) =
      Function.update (homotopyTuple (R := R) r i q a) (i.succ.succAbove j)
        (homotopyEntry (R := R) r i q j z) := by
  funext k
  refine Fin.succAboveCases i.succ ?_ ?_ k
  · simp [homotopyTuple, (Fin.succAbove_ne i.succ j).symm]
  · intro m
    simp only [homotopyTuple, Fin.insertNth_apply_succAbove]
    by_cases hmj : m = j
    · subst hmj
      simp
    · have hne : i.succ.succAbove m ≠ i.succ.succAbove j :=
        fun h ↦ hmj (Fin.succAbove_right_injective h)
      simp [hmj, hne]

/-- The `q`-summand of `hᵢ* ψ` as a multilinear map. -/
private def hochschildMatrixHomotopySummand (r : ι) {n : ℕ} (i : Fin (n + 1))
    (q : Fin (i + 1) → ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun a := ψ (homotopyTuple (R := R) r i q a)
  map_update_add' := by
    intro inst a j x y
    obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    simp only [homotopyTuple_update, map_add, ψ.map_update_add]
  map_update_smul' := by
    intro inst a j c x
    obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    simp only [homotopyTuple_update, map_smul, ψ.map_update_smul]

/-- The `i`-th term `hᵢ* : Cⁿ⁺¹(M_ι(A); M) → Cⁿ(M_ι(A); M)` of Loday's Hochschild homotopy. -/
private def hochschildMatrixHomotopyTerm (r : ι) {n : ℕ} (i : Fin (n + 1)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun ψ := ∑ q : Fin (i + 1) → ι, hochschildMatrixHomotopySummand (R := R) r i q ψ
  map_add' ψ₁ ψ₂ := by
    ext a
    simp [hochschildMatrixHomotopySummand, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext a
    simp [hochschildMatrixHomotopySummand, Finset.smul_sum]

private theorem hochschildMatrixHomotopyTerm_apply (r : ι) {n : ℕ} (i : Fin (n + 1))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    hochschildMatrixHomotopyTerm (R := R) r i ψ a =
      ∑ q : Fin (i + 1) → ι, ψ (homotopyTuple (R := R) r i q a) := by
  simp [hochschildMatrixHomotopyTerm, hochschildMatrixHomotopySummand]

/-- Face identity 1: `h₀* (δ₀ ψ) = ψ`. -/
private theorem hochschildMatrixHomotopyTerm_zero_hochschildCoface_zero (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ Matrix ι ι A) M) :
    hochschildMatrixHomotopyTerm (R := R) r (0 : Fin (m + 1))
        (hochschildCoface R (Matrix ι ι A) M 0 ψ) = ψ := by
  ext a
  rw [hochschildMatrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply]
  have hterm (q : Fin ((0 : Fin (m + 1)) + 1) → ι) :
      hochschildFace 0 (homotopyTuple (R := R) r (0 : Fin (m + 1)) q a) =
        Function.update a 0 (a 0 * Matrix.single (q 0) (q 0) 1) := by
    funext t
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    rcases eq_or_ne t 0 with rfl | ht
    · have hlast0 : (Fin.last ((0 : Fin (m + 1)) : ℕ) : Fin ((0 : Fin (m + 1)) + 1)) = 0 :=
        Fin.ext (by simp)
      rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp), Function.update_self, Fin.castSucc_zero,
        homotopyTuple_zero, homotopyTuple_succ_self, hlast0,
        mul_assoc, Matrix.single_mul_single_same, mul_one]
    · have ht0 : 0 < (t : ℕ) := Nat.pos_of_ne_zero (fun h ↦ ht (Fin.ext h))
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp [ht0]), Function.update_of_ne ht,
        homotopyTuple_of_gt _ _ _ _ _ (by simp only [Fin.val_zero, Fin.val_succ]; omega)]
      simp
  simp_rw [hterm]
  have hsum :
      (∑ q : Fin ((0 : Fin (m + 1)) + 1) → ι,
          ψ (Function.update a 0 (a 0 * Matrix.single (q 0) (q 0) 1))) =
        ∑ s : ι, ψ (Function.update a 0 (a 0 * Matrix.single s s 1)) :=
    ((Equiv.funUnique (Fin 1) ι).symm.sum_comp
      (fun q : Fin 1 → ι ↦ ψ (Function.update a 0 (a 0 * Matrix.single (q 0) (q 0) 1)))).symm
  rw [hsum]
  simp only [← ψ.map_update_sum, ← Finset.mul_sum, Matrix.sum_single_one, mul_one,
    Function.update_eq_self]

/-- Face identity 2: `h_m* (δ_{m+1} ψ) = tr (res_r ψ)`. -/
private theorem hochschildMatrixHomotopyTerm_last_hochschildCoface_last (r : ι) {m : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ Matrix ι ι A) M) :
    hochschildMatrixHomotopyTerm (R := R) r (Fin.last m)
        (hochschildCoface R (Matrix ι ι A) M (Fin.last (m + 1)) ψ) =
      matrixCochainExtension ι m (matrixCochainCornerRestriction r m ψ) := by
  ext a
  rw [hochschildMatrixHomotopyTerm_apply, matrixCochainExtension_apply]
  simp only [hochschildCoface_apply, matrixCochainCornerRestriction_apply]
  trans ∑ p : Fin (m + 1) → ι,
      ψ (hochschildFace (Fin.last (m + 1))
        (homotopyTuple (R := R) r (Fin.last m)
          (Equiv.arrowCongr (finRotate (m + 1)).symm (Equiv.refl ι) p) a))
  · exact ((Equiv.arrowCongr (finRotate (m + 1)).symm (Equiv.refl ι)).sum_comp
      (fun q : Fin (m + 1) → ι ↦
        ψ (hochschildFace (Fin.last (m + 1))
          (homotopyTuple (R := R) r (Fin.last m) q a)))).symm
  refine Finset.sum_congr rfl fun p _ ↦ congrArg ψ (funext fun t ↦ ?_)
  have hp (k : Fin (m + 1)) :
      (Equiv.arrowCongr (finRotate (m + 1)).symm (Equiv.refl ι) p) k =
        p (finRotate (m + 1) k) := rfl
  rw [hochschildFace_last]
  cases t using Fin.cases with
  | zero =>
    have hlast : (Fin.last (Fin.last m : ℕ) : Fin (m + 1)) = Fin.last m := rfl
    rw [Fin.cons_zero, ← Fin.succ_last, homotopyTuple_succ_self, homotopyTuple_zero, ← mul_assoc,
      Matrix.single_mul_mul_single, one_mul, mul_one, hp, hp, hlast, finRotate_last]
  | succ t =>
    rw [Fin.cons_succ, homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp),
      Matrix.single_mul_mul_single, one_mul, mul_one, hp, hp]
    have hprev : (⟨(t.castSucc.succ : ℕ) - 1, by simp⟩ : Fin (m + 1)) = t.castSucc :=
      Fin.ext (by simp)
    have hcurr : (⟨(t.castSucc.succ : ℕ), by simp⟩ : Fin (m + 1)) = t.succ :=
      Fin.ext (by simp)
    have hrot : finRotate (m + 1) t.castSucc = t.succ := by
      ext
      simp
    rw [hprev, hcurr, hrot]

/-- Face identity 3 (diagonal cancellation): `h_{i+1}* (δ_{i+1} ψ) = h_i* (δ_{i+1} ψ)`. -/
private theorem hochschildMatrixHomotopyTerm_succ_hochschildCoface_succ (r : ι) {n : ℕ}
    (i : Fin (n + 1))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildMatrixHomotopyTerm (R := R) r i.succ
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc ψ) =
      hochschildMatrixHomotopyTerm (R := R) r i.castSucc
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc ψ) := by
  ext a
  rw [hochschildMatrixHomotopyTerm_apply, hochschildMatrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply]
  trans ∑ p : ι × (Fin ((i : ℕ) + 1) → ι),
      ψ (hochschildFace i.succ.castSucc
        (homotopyTuple (R := R) r i.succ (Fin.snoc p.2 p.1) a))
  · exact ((Fin.snocEquiv (fun _ : Fin ((i : ℕ) + 1 + 1) ↦ ι)).sum_comp
      (fun q : Fin ((i : ℕ) + 1 + 1) → ι ↦
        ψ (hochschildFace i.succ.castSucc (homotopyTuple (R := R) r i.succ q a)))).symm
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hterm (s : ι) :
      hochschildFace i.succ.castSucc
          (homotopyTuple (R := R) r i.succ (Fin.snoc q s) a) =
        Function.update
          (hochschildFace i.succ.castSucc (homotopyTuple (R := R) r i.castSucc q a))
          i.succ
          (Matrix.single r (q (Fin.last i)) 1 * a i.succ * Matrix.single s s 1) := by
    funext t
    rw [hochschildFace_castSucc, hochschildFace_castSucc]
    rcases lt_trichotomy (t : ℕ) (i.succ : ℕ) with ht | ht | ht
    · have hne : t ≠ i.succ := fun h ↦ ht.ne (congrArg Fin.val h)
      rw [Function.update_of_ne hne, Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using ht),
        Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using ht)]
      rcases eq_or_ne t 0 with rfl | ht0
      · rw [Fin.castSucc_zero, homotopyTuple_zero, homotopyTuple_zero]
        have h0 : (0 : Fin ((i : ℕ) + 1 + 1)) = (0 : Fin ((i : ℕ) + 1)).castSucc := rfl
        rw [h0, Fin.snoc_castSucc]
      · have htpos : 0 < (t : ℕ) := Nat.pos_of_ne_zero (fun h ↦ ht0 (Fin.ext h))
        rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simpa using htpos) (by simp at ht ⊢; omega),
          homotopyTuple_of_pos_of_le _ _ _ _ _ (by simpa using htpos) (by simp at ht ⊢; omega)]
        have h1 : (⟨(t.castSucc : ℕ) - 1,
              by simp only [Fin.val_castSucc, Fin.val_succ] at ht ⊢; omega⟩ :
              Fin ((i : ℕ) + 1 + 1)) =
            (⟨(t.castSucc : ℕ) - 1, by simp only [Fin.val_castSucc, Fin.val_succ] at ht ⊢; omega⟩ :
              Fin ((i : ℕ) + 1)).castSucc := Fin.ext rfl
        have h2 : (⟨(t.castSucc : ℕ),
              by simp only [Fin.val_castSucc, Fin.val_succ] at ht ⊢; omega⟩ :
              Fin ((i : ℕ) + 1 + 1)) =
            (⟨(t.castSucc : ℕ), by simp only [Fin.val_castSucc, Fin.val_succ] at ht ⊢; omega⟩ :
              Fin ((i : ℕ) + 1)).castSucc := Fin.ext rfl
        rw [h1, h2, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · obtain rfl : t = i.succ := Fin.ext ht
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self,
        homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp), homotopyTuple_succ_self,
        mul_assoc, Matrix.single_mul_single_same, mul_one]
      have h1 : (⟨(i.succ.castSucc : ℕ) - 1, by simp⟩ : Fin ((i : ℕ) + 1 + 1)) =
          (Fin.last (i : ℕ)).castSucc := Fin.ext (by simp)
      have h2 : (⟨(i.succ.castSucc : ℕ), by simp⟩ : Fin ((i : ℕ) + 1 + 1)) =
          Fin.last ((i : ℕ) + 1) := Fin.ext (by simp)
      have h3 : (Fin.last (i.succ : ℕ) : Fin ((i : ℕ) + 1 + 1)) = Fin.last ((i : ℕ) + 1) := rfl
      have hsnoc : Fin.snoc (α := fun _ ↦ ι) q s (Fin.last ((i : ℕ) + 1)) = s := by simp
      rw [h1, h2, h3, Fin.snoc_castSucc, hsnoc]
      rfl
    · have hne : t ≠ i.succ := fun h ↦ ht.ne' (congrArg Fin.val h)
      rw [Function.update_of_ne hne, Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using ht),
        Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using ht),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at ht ⊢; omega),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at ht ⊢; omega)]
  have hbase :
      hochschildFace i.succ.castSucc (homotopyTuple (R := R) r i.castSucc q a) i.succ =
        Matrix.single r (q (Fin.last i)) 1 * a i.succ := by
    rw [hochschildFace_castSucc, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    have hcast : i.succ.castSucc = i.castSucc.succ := rfl
    rw [hcast, homotopyTuple_succ_self, homotopyTuple_of_gt _ _ _ _ _ (by simp)]
    congr 1
  simp only [hterm, ← ψ.map_update_sum, ← Finset.mul_sum,
    Matrix.sum_single_one, mul_one, ← hbase, Function.update_eq_self]

/-- Face identity 4 (lower triangle): for `k ≤ i`, `h_{i+1}* (δ_k ψ) = δ_k (h_i* ψ)`. -/
private theorem hochschildMatrixHomotopyTerm_succ_hochschildCoface_of_le (r : ι) {n : ℕ}
    (i k : Fin (n + 1)) (hki : k ≤ i)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildMatrixHomotopyTerm (R := R) r i.succ
        (hochschildCoface R (Matrix ι ι A) M k.castSucc.castSucc ψ) =
      hochschildCoface R (Matrix ι ι A) M k.castSucc
        (hochschildMatrixHomotopyTerm (R := R) r i ψ) := by
  ext a
  rw [hochschildMatrixHomotopyTerm_apply, hochschildCoface_apply,
    hochschildMatrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply]
  let k' : Fin ((i : ℕ) + 1 + 1) := ⟨k, by omega⟩
  trans ∑ p : ι × (Fin ((i : ℕ) + 1) → ι),
      ψ (hochschildFace k.castSucc.castSucc
        (homotopyTuple (R := R) r i.succ (Fin.insertNth (α := fun _ ↦ ι) k' p.1 p.2) a))
  · exact ((Fin.insertNthEquiv (fun _ : Fin ((i : ℕ) + 1 + 1) ↦ ι) k').sum_comp
      (fun q : Fin ((i : ℕ) + 1 + 1) → ι ↦
        ψ (hochschildFace k.castSucc.castSucc (homotopyTuple (R := R) r i.succ q a)))).symm
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hq_lt (s : ι) (m : ℕ) (hm : m < k) :
      Fin.insertNth (α := fun _ ↦ ι) k' s q ⟨m, by omega⟩ = q ⟨m, by omega⟩ := by
    have hsucc : (⟨m, by omega⟩ : Fin ((i : ℕ) + 1 + 1)) = k'.succAbove ⟨m, by omega⟩ := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def, k', hm])]
      exact Fin.ext rfl
    rw [hsucc, Fin.insertNth_apply_succAbove]
  have hq_eq (s : ι) : Fin.insertNth (α := fun _ ↦ ι) k' s q k' = s :=
    Fin.insertNth_apply_same (α := fun _ ↦ ι) k' s q
  have hq_gt (s : ι) (m : ℕ) (hm1 : (k : ℕ) < m) (hm2 : m < (i : ℕ) + 1 + 1) :
      Fin.insertNth (α := fun _ ↦ ι) k' s q ⟨m, hm2⟩ = q ⟨m - 1, by omega⟩ := by
    have hsucc : (⟨m, hm2⟩ : Fin ((i : ℕ) + 1 + 1)) = k'.succAbove ⟨m - 1, by omega⟩ := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def, k']; omega)]
      exact Fin.ext (by simp; omega)
    rw [hsucc, Fin.insertNth_apply_succAbove]
  have hterm (s : ι) :
      hochschildFace k.castSucc.castSucc
          (homotopyTuple (R := R) r i.succ (Fin.insertNth (α := fun _ ↦ ι) k' s q) a) =
        Function.update
          (homotopyTuple (R := R) r i q (hochschildFace k.castSucc a))
          k.castSucc
          (if k = 0 then
            a 0 * Matrix.single s s 1 * a 1 * Matrix.single (q 0) r 1
          else
            Matrix.single r (q ⟨(k : ℕ) - 1, by omega⟩) 1 * a k.castSucc *
              Matrix.single s s 1 * a k.succ * Matrix.single (q ⟨k, by omega⟩) r 1) := by
    funext t
    rw [hochschildFace_castSucc]
    rcases lt_trichotomy (t : ℕ) (k : ℕ) with ht | ht | ht
    · have hne : t ≠ k.castSucc := fun h ↦ ht.ne (congrArg Fin.val h)
      rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using ht), Function.update_of_ne hne]
      rcases eq_or_ne t 0 with rfl | ht0
      · rw [Fin.castSucc_zero, homotopyTuple_zero, homotopyTuple_zero, hochschildFace_castSucc,
          Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using ht), Fin.castSucc_zero]
        have := hq_lt s 0 ht
        exact congrArg (fun x ↦ a 0 * Matrix.single x r 1) this
      · have htpos : 0 < (t : ℕ) := Nat.pos_of_ne_zero (fun h ↦ ht0 (Fin.ext h))
        rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simpa using htpos) (by simp; omega),
          homotopyTuple_of_pos_of_le _ _ _ _ _ htpos (by omega), hochschildFace_castSucc,
          Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using ht)]
        have h1 := hq_lt s ((t : ℕ) - 1) (by omega)
        have h2 := hq_lt s (t : ℕ) ht
        simp only [Fin.val_castSucc] at h1 h2 ⊢
        rw [h1, h2]
        rfl
    · obtain rfl : t = k.castSucc := Fin.ext ht
      rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp), Function.update_self]
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte]
        rw [Fin.castSucc_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one,
          homotopyTuple_zero, homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp)]
        have h0 : (0 : Fin ((i : ℕ) + 1 + 1)) = k' := Fin.ext rfl
        have h1 : (⟨(1 : Fin (n + 3)) - 1, by simp⟩ : Fin ((i : ℕ) + 1 + 1)) = k' :=
          Fin.ext (by simp [k'])
        have h2 := hq_gt s 1 (by simp) (by omega)
        have h1' : (⟨(1 : Fin (n + 3)), by simp⟩ : Fin ((i : ℕ) + 1 + 1)) = ⟨1, by omega⟩ :=
          Fin.ext rfl
        rw [h0, h1, hq_eq, h1', h2]
        simp only [Nat.sub_self, Fin.mk_zero, Fin.val_one, Fin.mk_one]
        calc
          a 0 * Matrix.single s r 1 * (Matrix.single r s 1 * a 1 * Matrix.single (q 0) r 1)
              = a 0 * (Matrix.single s r 1 * Matrix.single r s 1) * a 1 *
                Matrix.single (q 0) r 1 := by simp only [mul_assoc]
          _ = a 0 * Matrix.single s s 1 * a 1 * Matrix.single (q 0) r 1 := by
                rw [Matrix.single_mul_single_same, mul_one]
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero (fun h ↦ hk0 (Fin.ext h))
        simp only [hk0, ↓reduceIte]
        rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simpa using hkpos) (by simp; omega),
          homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp; omega)]
        have hm1 := hq_lt s ((k : ℕ) - 1) (by omega)
        have hmk : (⟨(k.castSucc.castSucc : ℕ), by simp; omega⟩ : Fin ((i : ℕ) + 1 + 1)) = k' :=
          Fin.ext rfl
        have hmk' : (⟨(k.castSucc.succ : ℕ) - 1, by simp; omega⟩ : Fin ((i : ℕ) + 1 + 1)) = k' :=
          Fin.ext (by simp [k'])
        have hmp := hq_gt s ((k : ℕ) + 1) (by omega) (by omega)
        have hmp' : (⟨(k.castSucc.succ : ℕ), by simp; omega⟩ : Fin ((i : ℕ) + 1 + 1)) =
            ⟨(k : ℕ) + 1, by omega⟩ := Fin.ext (by simp)
        have hm1' : (⟨(k.castSucc.castSucc : ℕ) - 1, by simp; omega⟩ : Fin ((i : ℕ) + 1 + 1)) =
            ⟨(k : ℕ) - 1, by omega⟩ := Fin.ext rfl
        rw [hm1', hm1, hmk, hmk', hq_eq, hmp', hmp]
        have ha1 : (⟨(k.castSucc.castSucc : ℕ), by simp; omega⟩ : Fin (n + 2)) = k.castSucc :=
          Fin.ext rfl
        have ha2 : (⟨(k.castSucc.succ : ℕ), by simp; omega⟩ : Fin (n + 2)) = k.succ :=
          Fin.ext (by simp)
        have hqsub : (⟨(k : ℕ) + 1 - 1, by omega⟩ : Fin (i + 1)) = ⟨k, by omega⟩ :=
          Fin.ext (Nat.add_sub_cancel _ 1)
        rw [ha1, ha2, hqsub]
        calc
          Matrix.single r (q ⟨(k : ℕ) - 1, by omega⟩) 1 * a k.castSucc * Matrix.single s r 1 *
              (Matrix.single r s 1 * a k.succ * Matrix.single (q ⟨k, by omega⟩) r 1)
              = Matrix.single r (q ⟨(k : ℕ) - 1, by omega⟩) 1 * a k.castSucc *
                (Matrix.single s r 1 * Matrix.single r s 1) * a k.succ *
                Matrix.single (q ⟨k, by omega⟩) r 1 := by simp only [mul_assoc]
          _ = Matrix.single r (q ⟨(k : ℕ) - 1, by omega⟩) 1 * a k.castSucc *
                Matrix.single s s 1 * a k.succ * Matrix.single (q ⟨k, by omega⟩) r 1 := by
                rw [Matrix.single_mul_single_same, mul_one]
    · have hne : t ≠ k.castSucc := fun h ↦ ht.ne' (congrArg Fin.val h)
      rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using ht), Function.update_of_ne hne]
      rcases lt_trichotomy (t : ℕ) (i.succ : ℕ) with hti | hti | hti
      · have htpos : 0 < (t : ℕ) := by omega
        rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp at hti ⊢; omega),
          homotopyTuple_of_pos_of_le _ _ _ _ _ htpos (by simp at hti ⊢; omega),
          hochschildFace_castSucc, Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using ht)]
        have h1 := hq_gt s (t : ℕ) ht (by simp only [Fin.val_succ] at hti; omega)
        have h2 := hq_gt s ((t : ℕ) + 1) (by omega) (by simp only [Fin.val_succ] at hti; omega)
        have h1' : (⟨(t.succ : ℕ) - 1, by simp only [Fin.val_succ] at hti ⊢; omega⟩ :
              Fin ((i : ℕ) + 1 + 1)) =
            ⟨(t : ℕ), by simp only [Fin.val_succ] at hti; omega⟩ := Fin.ext (by simp)
        have h2' : (⟨(t.succ : ℕ), by simp only [Fin.val_succ] at hti ⊢; omega⟩ :
              Fin ((i : ℕ) + 1 + 1)) =
            ⟨(t : ℕ) + 1, by simp only [Fin.val_succ] at hti; omega⟩ := Fin.ext (by simp)
        rw [h1', h1, h2', h2]
        have hq2 : (⟨(t : ℕ) + 1 - 1, by simp only [Fin.val_succ] at hti; omega⟩ : Fin (i + 1)) =
            ⟨t, by simp only [Fin.val_succ] at hti; omega⟩ := Fin.ext (Nat.add_sub_cancel _ 1)
        have ha : (⟨(t.succ : ℕ), by simp only [Fin.val_succ]; omega⟩ : Fin (n + 2)) =
            (⟨t, by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp)
        rw [hq2, ha]
      · obtain rfl : t = i.succ := Fin.ext hti
        rw [homotopyTuple_succ_self, homotopyTuple_succ_self]
        have hlast := hq_gt s ((i : ℕ) + 1) (by omega) (by omega)
        have hlast' : Fin.last (i.succ : ℕ) = ⟨(i : ℕ) + 1, by simp⟩ := Fin.ext (by simp)
        rw [hlast', hlast]
        congr 1
      · rw [homotopyTuple_of_gt _ _ _ _ _ (by simp at hti ⊢; omega),
          homotopyTuple_of_gt _ _ _ _ _ hti, hochschildFace_castSucc,
          Fin.contractNth_apply_of_gt _ _ _ _ (by simp at ht hti ⊢; omega)]
        congr 1
        exact Fin.ext (by simp; omega)
  simp only [hterm, ← ψ.map_update_sum]
  by_cases hk0 : k = 0
  · subst hk0
    simp only [↓reduceIte, Fin.castSucc_zero]
    have hsum : (∑ s : ι, a 0 * Matrix.single s s 1 * a 1 * Matrix.single (q 0) r 1) =
        homotopyTuple (R := R) r i q (hochschildFace 0 a) 0 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one, mul_one]
      rw [homotopyTuple_zero, ← Fin.castSucc_zero, hochschildFace_castSucc,
        Fin.contractNth_apply_of_eq _ _ _ _ (by simp), Fin.castSucc_zero, Fin.succ_zero_eq_one]
    rw [hsum, Function.update_eq_self]
  · simp only [hk0, ↓reduceIte]
    have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero (fun h ↦ hk0 (Fin.ext h))
    have hsum : (∑ s : ι, Matrix.single r (q ⟨(k : ℕ) - 1, by omega⟩) 1 * a k.castSucc *
          Matrix.single s s 1 * a k.succ * Matrix.single (q ⟨k, by omega⟩) r 1) =
        homotopyTuple (R := R) r i q (hochschildFace k.castSucc a) k.castSucc := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one, mul_one]
      rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simpa using hkpos) (by simpa using hki),
        hochschildFace_castSucc, Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]
      simp only [Fin.val_castSucc, Fin.eta]
      simp only [mul_assoc]
    rw [hsum, Function.update_eq_self]

/-- Face identity 5 (upper triangle): for `i < k`, `h_i* (δ_{k+1} ψ) = δ_k (h_i* ψ)`. -/
private theorem hochschildMatrixHomotopyTerm_castSucc_hochschildCoface_succ_of_lt (r : ι) {n : ℕ}
    (i : Fin (n + 1)) (k : Fin (n + 2)) (hik : (i : ℕ) < k)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildMatrixHomotopyTerm (R := R) r i.castSucc
        (hochschildCoface R (Matrix ι ι A) M k.succ ψ) =
      hochschildCoface R (Matrix ι ι A) M k
        (hochschildMatrixHomotopyTerm (R := R) r i ψ) := by
  ext a
  rw [hochschildMatrixHomotopyTerm_apply, hochschildCoface_apply,
    hochschildMatrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply]
  refine Finset.sum_congr rfl fun q _ ↦ congrArg ψ (funext fun t ↦ ?_)
  induction k using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildFace_last, hochschildFace_last]
    cases t using Fin.cases with
    | zero =>
      rw [Fin.cons_zero, homotopyTuple_of_gt _ _ _ _ _ (by simp; omega), homotopyTuple_zero,
        homotopyTuple_zero, Fin.cons_zero, mul_assoc]
      congr 2
    | succ t =>
      rw [Fin.cons_succ]
      rcases lt_trichotomy (t.succ : ℕ) (i.succ : ℕ) with hti | hti | hti
      · rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp at hti ⊢; omega),
          homotopyTuple_of_pos_of_le _ _ _ _ _ (by simp) (by simp at hti ⊢; omega)]
        have ha : (⟨(t.succ : ℕ), by simp only [Fin.val_succ] at hti ⊢; omega⟩ : Fin (n + 1)) =
            (⟨(t : ℕ), by simp only [Fin.val_succ] at hti ⊢; omega⟩ : Fin n).succ :=
          Fin.ext (by simp)
        rw [ha, Fin.cons_succ]
        congr 2
      · have hti' : t.succ = i.succ := Fin.ext hti
        have hti'' : t.castSucc.succ = i.castSucc.succ := Fin.ext (by simpa using hti)
        rw [hti', hti'', homotopyTuple_succ_self, homotopyTuple_succ_self]
        rfl
      · rw [homotopyTuple_of_gt _ _ _ _ _ (by simp at hti ⊢; omega),
          homotopyTuple_of_gt _ _ _ _ _ hti]
        have htpos : 0 < (t : ℕ) := by simp only [Fin.val_succ] at hti; omega
        have ha : (⟨(t.succ : ℕ) - 1, by omega⟩ : Fin (n + 1)) =
            (⟨(t : ℕ) - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
        rw [ha, Fin.cons_succ]
        congr 1
        exact Fin.ext (by simp; omega)
  | cast j =>
    rw [Fin.succ_castSucc, hochschildFace_castSucc, hochschildFace_castSucc]
    have hij : (i : ℕ) < j := by simpa using hik
    rcases lt_trichotomy (t : ℕ) (j.succ : ℕ) with htj | htj | htj
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using htj)]
      rcases lt_trichotomy (t : ℕ) (i.succ : ℕ) with hti | hti | hti
      · rcases eq_or_ne t 0 with rfl | ht0
        · rw [Fin.castSucc_zero, homotopyTuple_zero, homotopyTuple_zero,
            Fin.contractNth_apply_of_lt _ _ _ _ (by simp only [Fin.val_zero]; omega),
            Fin.castSucc_zero]
        · have htpos : 0 < (t : ℕ) := Nat.pos_of_ne_zero (fun h ↦ ht0 (Fin.ext h))
          rw [homotopyTuple_of_pos_of_le _ _ _ _ _ (by simpa using htpos) (by simp at hti ⊢; omega),
            homotopyTuple_of_pos_of_le _ _ _ _ _ htpos (by simp at hti ⊢; omega),
            Fin.contractNth_apply_of_lt _ _ _ _ (by simp at hti ⊢; omega)]
          rfl
      · obtain rfl : t = i.succ := Fin.ext hti
        have hcast : i.succ.castSucc = i.castSucc.succ := rfl
        rw [hcast, homotopyTuple_succ_self, homotopyTuple_succ_self]
        rfl
      · rw [homotopyTuple_of_gt _ _ _ _ _ (by simp at hti ⊢; omega),
          homotopyTuple_of_gt _ _ _ _ _ hti,
          Fin.contractNth_apply_of_lt _ _ _ _ (by simp at htj hti ⊢; omega)]
        rfl
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using htj),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at htj ⊢; omega),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at htj ⊢; omega),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at htj ⊢; omega),
        Fin.contractNth_apply_of_eq _ _ _ _ (by simp at htj ⊢; omega)]
      congr 1; exact congrArg a (Fin.ext (by simp at htj ⊢; omega))
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using htj),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at htj ⊢; omega),
        homotopyTuple_of_gt _ _ _ _ _ (by simp at htj ⊢; omega),
        Fin.contractNth_apply_of_gt _ _ _ _ (by simp at htj ⊢; omega)]
      exact congrArg a (Fin.ext (by simp at htj ⊢; omega))

/-- Loday's Hochschild contracting homotopy `H_n = ∑_i (-1)^i hᵢ* : Cⁿ⁺¹ → Cⁿ`. -/
private def hochschildMatrixHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • hochschildMatrixHomotopyTerm (R := R) r i

/-- Degree-zero homotopy identity: `H₀ (b₀ ψ) = ψ - tr (res_r ψ)`. -/
private theorem hochschildMatrixHomotopy_hochschildCoboundary_zero (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    hochschildMatrixHomotopy (R := R) r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) =
      ψ - matrixCochainExtension ι 0 (matrixCochainCornerRestriction r 0 ψ) := by
  rw [hochschildMatrixHomotopy, LinearMap.sum_apply, Fin.sum_univ_one,
    hochschildCoboundary_eq_sum_coface, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, map_add, map_neg]
  have h1 : (1 : Fin 2) = Fin.last 1 := rfl
  have h0 : (0 : Fin 1) = Fin.last 0 := rfl
  rw [hochschildMatrixHomotopyTerm_zero_hochschildCoface_zero, h1, h0,
    hochschildMatrixHomotopyTerm_last_hochschildCoface_last, sub_eq_add_neg]

/-- Positive-degree homotopy identity: `b_n (H_n ψ) + H_{n+1} (b_{n+1} ψ) = ψ - tr (res_r ψ)`. -/
private theorem hochschildCoboundary_hochschildMatrixHomotopy_add (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M n (hochschildMatrixHomotopy (R := R) r n ψ) +
        hochschildMatrixHomotopy (R := R) r (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) ψ) =
      ψ - matrixCochainExtension ι (n + 1) (matrixCochainCornerRestriction r (n + 1) ψ) := by
  let F : Fin (n + 2) → Fin (n + 3) →
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M :=
    fun i k ↦ (-1 : ℤ) ^ ((i : ℕ) + (k : ℕ)) •
      hochschildMatrixHomotopyTerm (R := R) r i (hochschildCoface R (Matrix ι ι A) M k ψ)
  let G : Fin (n + 1) → Fin (n + 2) →
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M :=
    fun j k ↦ (-1 : ℤ) ^ ((j : ℕ) + (k : ℕ)) •
      hochschildCoface R (Matrix ι ι A) M k (hochschildMatrixHomotopyTerm (R := R) r j ψ)
  have hHb :
      hochschildMatrixHomotopy (R := R) r (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) ψ) =
        ∑ i : Fin (n + 2), ∑ k : Fin (n + 3), F i k := by
    rw [hochschildMatrixHomotopy, LinearMap.sum_apply]
    simp only [hochschildCoboundary_eq_sum_coface, LinearMap.smul_apply, map_sum, map_zsmul,
      smul_smul, ← pow_add, F]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [add_comm (k : ℕ) (i : ℕ)]
  have hbH :
      hochschildCoboundary R (Matrix ι ι A) M n (hochschildMatrixHomotopy (R := R) r n ψ) =
        ∑ j : Fin (n + 1), ∑ k : Fin (n + 2), G j k := by
    rw [hochschildCoboundary_eq_sum_coface]
    simp only [hochschildMatrixHomotopy, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_zsmul, Finset.smul_sum, smul_smul, ← pow_add, G]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [add_comm (k : ℕ) (j : ℕ)]
  -- Split each row `i` into `k < i`, `k = i`, `k = i + 1`, and `k > i + 1`.
  have hrow (i : Fin (n + 2)) :
      ∑ k : Fin (n + 3), F i k =
        (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 3) ↦ (k : ℕ) < i), F i k) +
        (F i i.castSucc + F i i.succ) +
        (∑ k ∈ Finset.univ.filter (fun k : Fin (n + 3) ↦ (i : ℕ) + 1 < k), F i k) := by
    have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin (n + 3) ↦ (k : ℕ) < i) (F i)).symm
    have h2 := (Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun k : Fin (n + 3) ↦ ¬ (k : ℕ) < i))
      (fun k : Fin (n + 3) ↦ (i : ℕ) + 1 < k) (F i)).symm
    have hmid :
        (Finset.univ.filter (fun k : Fin (n + 3) ↦ ¬ (k : ℕ) < i)).filter
          (fun k : Fin (n + 3) ↦ ¬ (i : ℕ) + 1 < k) = {i.castSucc, i.succ} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
    have hgt :
        (Finset.univ.filter (fun k : Fin (n + 3) ↦ ¬ (k : ℕ) < i)).filter
          (fun k : Fin (n + 3) ↦ (i : ℕ) + 1 < k) =
        Finset.univ.filter (fun k : Fin (n + 3) ↦ (i : ℕ) + 1 < k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hne : i.castSucc ≠ i.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    rw [h1, h2, hgt, hmid, Finset.sum_pair hne]
    abel
  -- 1. Diagonal terms telescope to `ψ - tr (res_r ψ)`.
  have hdiag :
      ∑ i : Fin (n + 2), (F i i.castSucc + F i i.succ) =
        ψ - matrixCochainExtension ι (n + 1) (matrixCochainCornerRestriction r (n + 1) ψ) := by
    have hsimp (i : Fin (n + 2)) :
        F i i.castSucc + F i i.succ =
          hochschildMatrixHomotopyTerm (R := R) r i
              (hochschildCoface R (Matrix ι ι A) M i.castSucc ψ) -
            hochschildMatrixHomotopyTerm (R := R) r i
              (hochschildCoface R (Matrix ι ι A) M i.succ ψ) := by
      have heven : (-1 : ℤ) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
        rw [← two_mul, pow_mul, neg_one_sq, one_pow]
      have hodd : (-1 : ℤ) ^ ((i : ℕ) + ((i : ℕ) + 1)) = -1 := by
        rw [← add_assoc, pow_succ, heven, one_mul]
      simp only [F, Fin.val_castSucc, Fin.val_succ, heven, hodd, one_smul, neg_smul,
        sub_eq_add_neg]
    simp_rw [hsimp, Finset.sum_sub_distrib]
    conv_lhs =>
      arg 1
      rw [Fin.sum_univ_succ]
    conv_lhs =>
      arg 2
      rw [Fin.sum_univ_castSucc]
    have hcancel :
        (∑ j : Fin (n + 1), hochschildMatrixHomotopyTerm (R := R) r j.succ
          (hochschildCoface R (Matrix ι ι A) M j.succ.castSucc ψ)) =
        (∑ j : Fin (n + 1), hochschildMatrixHomotopyTerm (R := R) r j.castSucc
          (hochschildCoface R (Matrix ι ι A) M j.castSucc.succ ψ)) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact hochschildMatrixHomotopyTerm_succ_hochschildCoface_succ r j ψ
    rw [hcancel, Fin.castSucc_zero, hochschildMatrixHomotopyTerm_zero_hochschildCoface_zero,
      Fin.succ_last, hochschildMatrixHomotopyTerm_last_hochschildCoface_last]
    abel
  -- 2. Lower triangle terms (`k < i`) match `-G j k` for `k ≤ j`.
  have hlower :
      (∑ i : Fin (n + 2), ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 3) ↦ (k : ℕ) < i), F i k) =
        ∑ j : Fin (n + 1), ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ (k : ℕ) ≤ j),
          -G j k := by
    rw [Fin.sum_univ_succ]
    have h0 : Finset.univ.filter (fun k : Fin (n + 3) ↦ (k : ℕ) < (0 : Fin (n + 2))) = ∅ := by
      ext k; simp
    rw [h0, Finset.sum_empty, zero_add]
    refine Finset.sum_congr rfl fun j _ ↦ (Finset.sum_bij (fun k _ ↦ k.castSucc) ?_ ?_ ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_succ] at hk ⊢
      omega
    · intro k₁ _ k₂ _ h
      exact Fin.castSucc_injective _ h
    · intro k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ] at hk'
      refine ⟨⟨k', by omega⟩, ?_, Fin.ext rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      let k₀ : Fin (n + 1) := ⟨k, by omega⟩
      have hk_eq : k = k₀.castSucc := Fin.ext rfl
      rw [hk_eq]
      simp only [F, G, Fin.val_succ, Fin.val_castSucc, add_right_comm _ 1, pow_succ, mul_neg_one,
        neg_smul]
      rw [hochschildMatrixHomotopyTerm_succ_hochschildCoface_of_le r j k₀ hk ψ]
  -- 3. Upper triangle terms (`i + 1 < k`) match `-G j k` for `j < k`.
  have hupper :
      (∑ i : Fin (n + 2),
          ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 3) ↦ (i : ℕ) + 1 < k), F i k) =
        ∑ j : Fin (n + 1), ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ ¬ (k : ℕ) ≤ j),
          -G j k := by
    rw [Fin.sum_univ_castSucc]
    have hlast :
        Finset.univ.filter (fun k : Fin (n + 3) ↦ (Fin.last (n + 1) : ℕ) + 1 < k) = ∅ := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last,
        Finset.notMem_empty, iff_false]; omega
    rw [hlast, Finset.sum_empty, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ (Finset.sum_bij (fun k _ ↦ k.succ) ?_ ?_ ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_succ] at hk ⊢
      omega
    · intro k₁ _ k₂ _ h
      exact Fin.succ_injective _ h
    · intro k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc] at hk'
      refine ⟨⟨(k' : ℕ) - 1, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
      simp only [F, G, Fin.val_castSucc, Fin.val_succ, ← add_assoc, pow_succ, mul_neg_one, neg_smul]
      rw [hochschildMatrixHomotopyTerm_castSucc_hochschildCoface_succ_of_lt r j k hk ψ]
  rw [hbH, hHb]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdiag, hlower, hupper]
  have hcancel :
      (∑ j : Fin (n + 1), ∑ k : Fin (n + 2), G j k) +
      ((∑ j : Fin (n + 1), ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ (k : ℕ) ≤ j), -G j k) +
        ∑ j : Fin (n + 1), ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ ¬ (k : ℕ) ≤ j),
          -G j k) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_neg_distrib]
    exact add_neg_cancel _
  calc
    (∑ j : Fin (n + 1), ∑ k : Fin (n + 2), G j k) +
        ((∑ j : Fin (n + 1),
            ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ (k : ℕ) ≤ j), -G j k) +
          (ψ - matrixCochainExtension ι (n + 1) (matrixCochainCornerRestriction r (n + 1) ψ)) +
          ∑ j : Fin (n + 1),
            ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ ¬ (k : ℕ) ≤ j), -G j k)
        = (ψ - matrixCochainExtension ι (n + 1) (matrixCochainCornerRestriction r (n + 1) ψ)) +
          ((∑ j : Fin (n + 1), ∑ k : Fin (n + 2), G j k) +
            ((∑ j : Fin (n + 1),
                ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ (k : ℕ) ≤ j), -G j k) +
              ∑ j : Fin (n + 1),
                ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 2) ↦ ¬ (k : ℕ) ≤ j), -G j k)) := by
          abel
    _ = ψ - matrixCochainExtension ι (n + 1) (matrixCochainCornerRestriction r (n + 1) ψ) := by
          rw [hcancel, add_zero]

/-- On any Hochschild cocycle `ψ` on `Matrix ι ι A`, the difference `ψ - tr (res_r ψ)` is a
Hochschild coboundary. -/
theorem sub_matrixCochainExtension_cornerRestriction_mem_hochschildCoboundaries (r : ι) {n : ℕ}
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    ψ - matrixCochainExtension ι n (matrixCochainCornerRestriction r n ψ) ∈
      hochschildCoboundaries R (Matrix ι ι A) M n := by
  have h0 : hochschildCoboundary R (Matrix ι ι A) M n ψ = 0 := mem_hochschildCocycles_iff.1 hψ
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot,
      ← hochschildMatrixHomotopy_hochschildCoboundary_zero (R := R) r ψ, h0, map_zero]
  | succ n =>
    refine mem_hochschildCoboundaries_succ_iff.2 ⟨hochschildMatrixHomotopy (R := R) r n ψ, ?_⟩
    have h := hochschildCoboundary_hochschildMatrixHomotopy_add (R := R) r n ψ
    rw [h0, map_zero, add_zero] at h
    exact h

end HochschildHomotopy

/-! ### Matrix Morita invariance of Hochschild cohomology -/

section HochschildCohomology

namespace hochschildCohomology

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- The map `HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` induced by matrix
extension of Hochschild cocycles. -/
noncomputable def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2 (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends the class of a cocycle to the class of its
matrix extension. -/
@[simp]
theorem matrixExtension_mk {ι : Type*} [Fintype ι] {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ,
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

variable (M) in
/-- The map `HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M)) → HHⁿ(A, Hom_R(A, M))` induced by
restricting Hochschild cocycles to the `(r, r)` corner. -/
noncomputable def cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCochainCornerRestriction r n).restrict
      fun _ ↦ matrixCochainCornerRestriction_mem_hochschildCocycles r)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2
      (matrixCochainCornerRestriction_mem_hochschildCoboundaries r hφ)

/-- Corner restriction on Hochschild cohomology sends the class of a cocycle to the class of its
corner restriction. -/
@[simp]
theorem cornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (φ : hochschildCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M r n (mk R (Matrix ι ι A) M n φ) =
      mk R A M n ⟨matrixCochainCornerRestriction r n φ,
        matrixCochainCornerRestriction_mem_hochschildCocycles r φ.2⟩ :=
  desc_mk _ _ _ φ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp]
theorem cornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) (c : hochschildCohomology R A M n) :
    cornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, cornerRestriction_mk]
  congr 1
  exact Subtype.ext (matrixCochainCornerRestriction_matrixCochainExtension r n φ.1)

end hochschildCohomology

namespace hochschildCohomology

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- For a unital algebra, corner restriction is a right inverse to matrix extension on Hochschild
cohomology. -/
@[simp]
theorem matrixExtension_cornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M r n c) = c := by
  obtain ⟨ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  simp only [cornerRestriction_mk, matrixExtension_mk]
  symm
  exact (mk_eq_mk_iff R (Matrix ι ι A) M n _ _).2
    (sub_matrixCochainExtension_cornerRestriction_mem_hochschildCoboundaries r ψ.2)

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital associative algebra `A`
over any commutative ring `R` and any finite nonempty index type `ι`, the generalized matrix trace
induces a bijection on Hochschild cohomology `HHⁿ(A, Hom_R(A, M)) → HHⁿ(M_ι(A), Hom_R(M_ι(A), M))`.
-/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.bijective_iff_has_inverse.2
    ⟨cornerRestriction M r n,
      cornerRestriction_matrixExtension r n,
      matrixExtension_cornerRestriction r n⟩

variable (M) in
/-- Matrix Morita equivalence on Hochschild cohomology as an `R`-linear equivalence. -/
noncomputable def matrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The underlying linear map of `hochschildCohomology.matrixEquiv` is `matrixExtension`. -/
@[simp]
theorem coe_matrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    (matrixEquiv (R := R) (A := A) M ι n :
        hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n :=
  (rfl)

/-- Applying `hochschildCohomology.matrixEquiv` is applying `matrixExtension`. -/
@[simp]
theorem matrixEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixEquiv (R := R) (A := A) M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `hochschildCohomology.matrixEquiv` is `cornerRestriction` at any corner `r`. -/
theorem matrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (r : ι)
    (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixEquiv (R := R) (A := A) M ι n).symm c = cornerRestriction M r n c := by
  apply (matrixEquiv (R := R) (A := A) M ι n).injective
  simp

end hochschildCohomology

end HochschildCohomology

end TauCeti
