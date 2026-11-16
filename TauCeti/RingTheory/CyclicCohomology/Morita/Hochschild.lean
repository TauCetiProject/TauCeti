/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.HochschildCohomology.Complex
import TauCeti.Algebra.BigOperators.AlternatingSum
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Matrix.Basis

/-!
# Matrix Morita invariance of Hochschild cohomology

For a unital algebra `A` over a commutative ring `R`, an `R`-module `M`, and a nonempty finite
index type `ι`, the generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`)
induces an isomorphism on Hochschild cohomology `HHⁿ(A, Hom_R(A, M))` in every degree `n`.

## Strategy

Fix a base index `r : ι`. Pulling back along the diagonal corner inclusion
`a ↦ Matrix.single r r a` (`TauCeti.matrixCornerCochainRestriction`) is a cochain map that is a
left inverse to `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension_single`). On the matrix cochain
complex, Loday's explicit presimplicial homotopy `H = ∑_{j=0}^n (-1)^j h_j`,
`(h_j ψ)(a₀, …, aₙ) = ∑_{k₀, …, kⱼ} ψ(a₀ E_{k₀ r}, (a₁)_{k₀ k₁} E_{r r}, …,`
`(aⱼ)_{k_{j-1} kⱼ} E_{r r}, E_{r kⱼ}, a_{j+1}, …, aₙ)`,
satisfies `H (b ψ) + b (H ψ) = ψ - (inc_r* ψ)#Tr` (with `b (H ψ) = 0` in degree zero). Thus
matrix extension and corner restriction are mutually inverse on Hochschild cohomology over every
commutative ring `R`.

## Main definitions

* `TauCeti.matrixCornerCochainRestriction`: pulling a matrix cochain back to a diagonal corner.
* `TauCeti.hochschildCohomology.matrixExtension`: the map on Hochschild cohomology induced by
  `φ ↦ φ#Tr`.
* `TauCeti.hochschildCohomology.matrixCornerRestriction`: diagonal corner restriction on Hochschild
  cohomology.
* `TauCeti.hochschildCohomology.matrixEquiv`: the Morita linear equivalence on Hochschild
  cohomology.

## Main results

* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of Hochschild
  cohomology over any commutative ring.

## References

* J.-L. Loday, *Cyclic Homology*, §1.2.4.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Hochschild matrix extension, corner restriction, and cochain homotopy -/

section HochschildCocycles

variable {R A M : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {ι : Type*} [Fintype ι] {n : ℕ}

/-- Matrix extension maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ ⊢
  rw [← matrixCochainExtension_hochschildCoboundary, hφ, map_zero]

/-- Matrix extension maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
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
      ⟨_, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩

end HochschildCocycles

section CornerCochain

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M] {ι : Type*} [DecidableEq ι]

/-- Pulling a matrix cochain back to the `(r, r)` diagonal corner. -/
def matrixCornerCochainRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun ψ := ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' _ _ := by ext; simp [MultilinearMap.compLinearMap_apply]
  map_smul' _ _ := by ext; simp [MultilinearMap.compLinearMap_apply]

/-- Evaluation of diagonal corner restriction on a tuple of elements of `A`. -/
@[simp]
theorem matrixCornerCochainRestriction_apply (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    matrixCornerCochainRestriction r n ψ x = ψ (fun j ↦ Matrix.single r r (x j)) := by
  rfl

/-- Corner restriction is a left inverse to matrix extension on cochains. -/
theorem matrixCornerCochainRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCornerCochainRestriction r n (matrixCochainExtension ι n φ) = φ := by
  ext x
  exact matrixCochainExtension_single ι r n φ x

end CornerCochain

section CornerHom

variable {R A M : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCornerCochainRestriction_hochschildCoboundary (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCornerCochainRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n ψ) =
      hochschildCoboundary R A M n (matrixCornerCochainRestriction r n ψ) :=
  (hochschildCoboundary_compLinearMap
    ({ toFun := Matrix.single r r
       map_zero' := Matrix.single_zero r r
       map_add' := Matrix.single_add r r
       map_smul' := fun c a ↦ (Matrix.smul_single c r r a).symm
       map_mul' := fun a b ↦ (Matrix.single_mul_single_same a r r r b).symm } :
      A →ₙₐ[R] Matrix ι ι A) ψ).symm

/-- Corner restriction maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCornerCochainRestriction_mem_hochschildCocycles (r : ι) {n : ℕ}
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCornerCochainRestriction r n ψ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hψ ⊢
  rw [← matrixCornerCochainRestriction_hochschildCoboundary, hψ, map_zero]

/-- Corner restriction maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCornerCochainRestriction_mem_hochschildCoboundaries (r : ι) {n : ℕ}
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCornerCochainRestriction r n ψ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hψ ⊢
    rw [hψ, map_zero]
  | succ n =>
    obtain ⟨χ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hψ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨_, (matrixCornerCochainRestriction_hochschildCoboundary r n χ).symm⟩

end CornerHom

section HochschildHomotopy

variable {R A M : Type*} [Semiring R] [Semiring A] [Module R A] [IsScalarTower R A A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear map applied to coordinate `l` in the `j`-th term of Loday's matrix homotopy. -/
private def matrixHomotopyCoord {n : ℕ} (r : ι) (j : Fin (n + 1)) (k : Fin (j.1 + 1) → ι)
    (l : Fin (n + 1)) : Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if _ : l.1 = 0 then
    LinearMap.mulRight R (Matrix.single (k 0) r (1 : A))
  else if hl : l.1 ≤ j.1 then
    Matrix.singleLinearMap R r r ∘ₗ
      Matrix.entryLinearMap R A (k ⟨l.1 - 1, by omega⟩) (k ⟨l.1, by omega⟩)
  else
    LinearMap.id

/-- The `(n + 2)`-tuple `(a₀ E_{k₀ r}, (a₁)_{k₀ k₁} E_{r r}, …, E_{r kⱼ}, a_{j+1}, …, aₙ)` in
the `j`-th term of Loday's matrix homotopy. -/
private def matrixHomotopyTuple {n : ℕ} (r : ι) (j : Fin (n + 1)) (k : Fin (j.1 + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) : Fin (n + 2) → Matrix ι ι A :=
  Fin.insertNth j.succ (Matrix.single r (k (Fin.last j.1)) 1) fun l ↦
    if _ : l.1 = 0 then a 0 * Matrix.single (k 0) r 1
    else if hl : l.1 ≤ j.1 then
      Matrix.single r r (a l (k ⟨l.1 - 1, by omega⟩) (k ⟨l.1, by omega⟩))
    else a l

/-- Explicit coordinate description of `matrixHomotopyTuple`. -/
private theorem matrixHomotopyTuple_apply {n : ℕ} (r : ι) (j : Fin (n + 1))
    (k : Fin (j.1 + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A) (m : Fin (n + 2)) :
    matrixHomotopyTuple r j k a m =
      if _ : m.1 = 0 then a 0 * Matrix.single (k 0) r 1
      else if hm : m.1 ≤ j.1 then
        Matrix.single r r
          (a ⟨m.1, by omega⟩ (k ⟨m.1 - 1, by omega⟩) (k ⟨m.1, by omega⟩))
      else if _ : m.1 = j.1 + 1 then
        Matrix.single r (k (Fin.last j.1)) 1
      else a ⟨m.1 - 1, by omega⟩ := by
  dsimp only [matrixHomotopyTuple]
  cases m using Fin.succAboveCases j.succ with
  | x =>
    rw [Fin.insertNth_apply_same]
    have h1 : j.1 + 1 ≠ 0 := by omega
    have h2 : ¬j.1 + 1 ≤ j.1 := by omega
    simp only [Fin.val_succ, h1, h2, ↓reduceDIte]
  | p l =>
    rw [Fin.insertNth_apply_succAbove]
    by_cases h : l.castSucc < j.succ
    · have hv : (j.succ.succAbove l).1 = l.1 := by rw [Fin.succAbove_of_castSucc_lt _ _ h]; rfl
      have hlj : l.1 ≤ j.1 := by simpa [Fin.lt_def, Nat.lt_succ_iff] using h
      by_cases hl0 : l.1 = 0
      · simp only [hl0, hv.trans hl0, ↓reduceDIte]
      · have hm0 : (j.succ.succAbove l).1 ≠ 0 := by omega
        have hmj : (j.succ.succAbove l).1 ≤ j.1 := by omega
        simp only [hl0, hm0, hlj, hmj, ↓reduceDIte]
        exact congrArg (Matrix.single r r)
          (congr (congr (congrArg a (Fin.ext hv.symm)) (congrArg k (Fin.ext (by dsimp; omega))))
            (congrArg k (Fin.ext (by dsimp; omega))))
    · have hle : j.succ ≤ l.castSucc := le_of_not_gt h
      have hv : (j.succ.succAbove l).1 = l.1 + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ hle]; rfl
      have hle' : j.1 + 1 ≤ l.1 := by
        simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using hle
      have hl0 : l.1 ≠ 0 := by omega
      have hlj : ¬l.1 ≤ j.1 := by omega
      have hm0 : (j.succ.succAbove l).1 ≠ 0 := by omega
      have hmj : ¬(j.succ.succAbove l).1 ≤ j.1 := by omega
      have hmj1 : (j.succ.succAbove l).1 ≠ j.1 + 1 := by omega
      simp only [hl0, hlj, hm0, hmj, hmj1, ↓reduceDIte]
      exact congrArg a (Fin.ext (by dsimp; omega))

/-- A single index-path summand in the `j`-th term of Loday's homotopy. -/
private def matrixHomotopyTermSummand (r : ι) {n : ℕ} (j : Fin (n + 1)) (k : Fin (j.1 + 1) → ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  MultilinearMap.compLinearMap
    (.mk' (fun a ↦ ψ (j.succ.insertNth (α := fun _ ↦ Matrix ι ι A)
        (Matrix.single r (k (Fin.last j.1)) 1) a))
      (fun a l x y ↦ by simp [Fin.insertNth_update])
      (fun a l c x ↦ by simp [Fin.insertNth_update]))
    (matrixHomotopyCoord r j k)

/-- The `j`-th summand `h_j : C^{n+1}(M_ι A; M) → C^n(M_ι A; M)` of Loday's homotopy. -/
private def matrixHomotopyTerm (r : ι) {n : ℕ} (j : Fin (n + 1)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun ψ := ∑ k : Fin (j.1 + 1) → ι, matrixHomotopyTermSummand (R := R) r j k ψ
  map_add' ψ₁ ψ₂ := by
    ext a
    simp [matrixHomotopyTermSummand, MultilinearMap.compLinearMap_apply, MultilinearMap.mk',
      Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext a
    simp [matrixHomotopyTermSummand, MultilinearMap.compLinearMap_apply, MultilinearMap.mk',
      Finset.smul_sum]

private theorem matrixHomotopyTerm_apply (r : ι) {n : ℕ} (j : Fin (n + 1))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r j ψ a =
      ∑ k : Fin (j.1 + 1) → ι, ψ (matrixHomotopyTuple r j k a) := by
  simp only [matrixHomotopyTerm, matrixHomotopyTermSummand, LinearMap.coe_mk, AddHom.coe_mk,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mk', MultilinearMap.coe_mk, sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg ψ ?_
  dsimp only [matrixHomotopyTuple]
  congr 1; funext l; dsimp only [matrixHomotopyCoord]
  split_ifs with hl0 hlj
  · obtain rfl : l = 0 := Fin.ext hl0; rfl
  · rfl
  · rfl

/-- Loday's alternating cochain homotopy
`H_n = ∑_j (-1)^j h_j : C^{n+1}(M_ι A; M) → C^n(M_ι A; M)`. -/
private def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • matrixHomotopyTerm (R := R) r j

variable [SMulCommClass R A A]

/-- At `(j = 0, i = 0)`, `h_0 (δ_0 ψ) = ψ` because `∑_k E_{k r} E_{r k} = 1`. -/
private theorem matrixHomotopyTerm_zero_hochschildCoface_zero (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r 0 (hochschildCoface R (Matrix ι ι A) M 0 ψ) a = ψ a := by
  rw [matrixHomotopyTerm_apply]
  have hface (k : Fin ((0 : Fin (n + 1)).1 + 1) → ι) :
      hochschildFace 0 (matrixHomotopyTuple r (0 : Fin (n + 1)) k a) =
        Function.update a 0 (a 0 * Matrix.single (k 0) (k 0) 1) := by
    have hface0 : hochschildFace (0 : Fin (n + 2)) (matrixHomotopyTuple r (0 : Fin (n + 1)) k a) =
        Fin.contractNth (0 : Fin (n + 2)) (· * ·) (matrixHomotopyTuple r (0 : Fin (n + 1)) k a) :=
      by simpa [Fin.castSucc_zero] using hochschildFace_castSucc (0 : Fin (n + 1)) _
    rw [hface0]
    funext l
    by_cases hl : l.1 = 0
    · obtain rfl : l = 0 := Fin.ext hl
      rw [Function.update_self]
      simp only [Fin.contractNth, Fin.val_zero, lt_self_iff_false, ↓reduceIte]
      rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
      simp [mul_assoc, Fin.last]; rfl
    · have hl' : l ≠ 0 := fun h ↦ hl (congrArg Fin.val h)
      rw [Function.update_of_ne hl']
      simp only [Fin.contractNth, Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, hl]
      rw [matrixHomotopyTuple_apply]
      have h1 : l.1 + 1 ≠ 0 := by omega
      have h2 : ¬l.1 + 1 ≤ 0 := by omega
      have h3 : l.1 + 1 ≠ 0 + 1 := by omega
      simp only [Fin.val_succ, Fin.val_zero, h1, h2, h3, ↓reduceDIte]
      rfl
  simp_rw [hochschildCoface_apply, hface]
  let e : (Fin ((0 : Fin (n + 1)).1 + 1) → ι) ≃ ι := Equiv.funUnique (Fin 1) ι
  rw [Fintype.sum_equiv e (fun x ↦ ψ (Function.update a 0 (a 0 * Matrix.single (x 0) (x 0) 1)))
      (fun t ↦ ψ (Function.update a 0 (a 0 * Matrix.single t t 1))) fun _ ↦ rfl,
    ← ψ.map_update_sum, ← Finset.mul_sum, Matrix.sum_single_one, mul_one,
    Function.update_eq_self]

/-- At `(j = last, i = last)`, `h_n (δ_{n+1} ψ) = (inc_r* ψ)#Tr`. -/
private theorem matrixHomotopyTerm_last_hochschildCoface_last (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r (Fin.last n)
        (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1)) ψ) a =
      matrixCochainExtension ι n (matrixCornerCochainRestriction (R := R) r n ψ) a := by
  rw [matrixHomotopyTerm_apply, matrixCochainExtension_apply]
  simp only [hochschildCoface_apply, matrixCornerCochainRestriction_apply, Fin.val_last]
  conv_lhs => rw [← (Equiv.arrowCongr (finRotate (n + 1)).symm (Equiv.refl ι)).sum_comp]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg ψ ?_
  funext l
  rw [hochschildFace_last]
  have hrot (x : Fin (n + 1)) :
      (Equiv.arrowCongr (finRotate (n + 1)).symm (Equiv.refl ι) p) x =
        p (finRotate (n + 1) x) := rfl
  cases l using Fin.cases with
  | zero =>
    have h1 : ¬n + 1 ≤ n := by omega
    simp only [Fin.cons_zero, matrixHomotopyTuple_apply, Fin.val_last, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, h1, ↓reduceDIte, Fin.val_zero, hrot]
    rw [← mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one, finRotate_last]
  | succ l =>
    have hle : l.1 + 1 ≤ n := l.2
    simp only [Fin.cons_succ, matrixHomotopyTuple_apply, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel, hle,
      ↓reduceDIte, hrot]
    have hprev : finRotate (n + 1) ⟨l.1, by omega⟩ = l.succ := by
      have : (⟨l.1, by omega⟩ : Fin (n + 1)) = l.castSucc := rfl
      rw [this, Fin.finRotate_castSucc]
    have hcurr : (⟨l.1 + 1, by omega⟩ : Fin (n + 1)) = l.succ := rfl
    rw [hprev, hcurr]

/-- Tuple identity behind diagonal cancellation `h_{k+1} (δ_{k+1} ψ) = h_k (δ_{k+1} ψ)`. -/
private theorem hochschildFace_castSucc_matrixHomotopyTuple_snoc (r : ι) {m : ℕ}
    (k : Fin (m + 1)) (p : Fin (k.1 + 1) → ι) (t : ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace k.succ.castSucc
        (matrixHomotopyTuple r k.succ (Fin.snoc (α := fun _ ↦ ι) p t) a) =
      Function.update
        (hochschildFace k.succ.castSucc (matrixHomotopyTuple r k.castSucc p a))
        k.succ (Matrix.single r t (a k.succ (p (Fin.last k.1)) t)) := by
  rw [hochschildFace_castSucc, hochschildFace_castSucc]
  funext l
  by_cases hl : l = k.succ
  · subst hl; rw [Function.update_self]
    have h1 : ¬k.1 + 1 + 1 ≤ k.1 + 1 := by omega
    have hlast : (⟨k.1 + 1, by omega⟩ : Fin (k.1 + 2)) = Fin.last (k.1 + 1) := rfl
    have hprev : (⟨k.1, by omega⟩ : Fin (k.1 + 2)) = (Fin.last k.1).castSucc := rfl
    simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, lt_self_iff_false, ↓reduceIte,
      matrixHomotopyTuple_apply, Nat.add_eq_zero_iff, one_ne_zero, and_false, le_refl,
      Nat.add_sub_cancel, h1, ↓reduceDIte, hlast, hprev, Fin.snoc_last, Fin.snoc_castSucc,
      Matrix.single_mul_single_same, mul_one]
    rfl
  · rw [Function.update_of_ne hl]
    have hlv : l.1 ≠ k.1 + 1 := fun h ↦ hl (Fin.ext h)
    rcases lt_or_gt_of_ne hlv with hlt | hgt
    · simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, hlt, ↓reduceIte]
      rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
      by_cases hl0 : l.1 = 0
      · simp only [Fin.val_castSucc, hl0, ↓reduceDIte, Fin.snoc_apply_zero]
      · have hlk : l.1 ≤ k.1 := by omega
        have hlk1 : l.1 ≤ k.1 + 1 := by omega
        have hp1 : (⟨l.1 - 1, by omega⟩ : Fin (k.1 + 2)) =
            (⟨l.1 - 1, by omega⟩ : Fin (k.1 + 1)).castSucc := rfl
        have hp2 : (⟨l.1, by omega⟩ : Fin (k.1 + 2)) =
            (⟨l.1, by omega⟩ : Fin (k.1 + 1)).castSucc := rfl
        simp only [Fin.val_castSucc, Fin.val_succ, hl0, hlk, hlk1, ↓reduceDIte, hp1, hp2,
          Fin.snoc_castSucc]
    · have hnl : ¬l.1 < k.1 + 1 := by omega
      have hl10 : l.1 + 1 ≠ 0 := by omega
      have hlk : ¬l.1 + 1 ≤ k.1 := by omega
      have hlk1 : l.1 + 1 ≠ k.1 + 1 := by omega
      have hlk1' : ¬l.1 + 1 ≤ k.1 + 1 := by omega
      have hlk2 : l.1 + 1 ≠ k.1 + 1 + 1 := by omega
      simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, hnl, hlv, ↓reduceIte]
      rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
      simp only [Fin.val_succ, Fin.val_castSucc, hl10, hlk, hlk1, hlk1', hlk2, ↓reduceDIte]

/-- Diagonal cancellation: `h_{k+1} (δ_{k+1} ψ) = h_k (δ_{k+1} ψ)` for `k : Fin (m + 1)`. -/
private theorem matrixHomotopyTerm_diag (r : ι) {m : ℕ} (k : Fin (m + 1))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (a : Fin (m + 2) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r k.castSucc
        (hochschildCoface R (Matrix ι ι A) M k.succ.castSucc ψ) a =
      matrixHomotopyTerm (R := R) r k.succ
        (hochschildCoface R (Matrix ι ι A) M k.succ.castSucc ψ) a := by
  symm
  rw [matrixHomotopyTerm_apply, matrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply, Fin.val_succ, Fin.val_castSucc]
  rw [← (Fin.snocEquiv (fun _ : Fin (k.1 + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp_rw [Fin.snocEquiv_apply, hochschildFace_castSucc_matrixHomotopyTuple_snoc]
  rw [← ψ.map_update_sum, Matrix.sum_single_eq_single_mul]
  congr 1
  rw [Function.update_eq_self_iff, hochschildFace_castSucc]
  have h1 : ¬k.1 + 1 ≤ k.1 := by omega
  have h2 : ¬k.1 + 1 + 1 ≤ k.1 := by omega
  have h3 : k.1 + 1 + 1 ≠ k.1 + 1 := by omega
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, lt_self_iff_false, ↓reduceIte,
    matrixHomotopyTuple_apply, Nat.add_eq_zero_iff, one_ne_zero, and_false, h1, h2, h3, ↓reduceDIte]
  rfl

/-- Tuple identity behind the lower-triangle relation at `i = 0`. -/
private theorem hochschildFace_zero_matrixHomotopyTuple_cons (r : ι) {m : ℕ} (j : Fin (m + 1))
    (p : Fin (j.1 + 1) → ι) (t : ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace 0 (matrixHomotopyTuple r j.succ (Fin.cons (α := fun _ ↦ ι) t p) a) =
      Function.update (matrixHomotopyTuple r j p (hochschildFace 0 a))
        0 (a 0 * Matrix.single t r (a 1 t (p 0))) := by
  have hface0 {d : ℕ} (v : Fin (d + 2) → Matrix ι ι A) :
      hochschildFace (0 : Fin (d + 2)) v = Fin.contractNth (0 : Fin (d + 2)) (· * ·) v := by
    simpa [Fin.castSucc_zero] using hochschildFace_castSucc (0 : Fin (d + 1)) v
  rw [hface0, hface0]
  funext l
  by_cases hl : l = 0
  · obtain rfl : l = 0 := hl
    rw [Function.update_self]
    have h0 : 0 + 1 ≠ 0 := by omega
    have h1 : 0 + 1 ≤ j.1 + 1 := by omega
    have h0eq : (⟨0, by omega⟩ : Fin (j.1 + 2)) = 0 := rfl
    have h1eq : (⟨0 + 1, by omega⟩ : Fin (j.1 + 2)) = (0 : Fin (j.1 + 1)).succ := rfl
    simp only [Fin.contractNth, Fin.val_zero, lt_self_iff_false, ↓reduceIte,
      matrixHomotopyTuple_apply, Fin.val_castSucc, Fin.val_succ, h0, h1, ↓reduceDIte,
      Nat.add_sub_cancel, h0eq, h1eq, Fin.cons_zero, Fin.cons_succ]
    rw [mul_assoc, Matrix.single_mul_single_same, one_mul]; rfl
  · rw [Function.update_of_ne hl]
    have hlv : l.1 ≠ 0 := fun h ↦ hl (Fin.ext h)
    have hl1 : l.1 + 1 ≠ 0 := by omega
    simp only [Fin.contractNth, Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, hlv]
    rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
    by_cases hlj : l.1 ≤ j.1
    · have hlj1 : l.1 + 1 ≤ j.1 + 1 := by omega
      have hp1 : (⟨l.1, by omega⟩ : Fin (j.1 + 2)) =
          (⟨l.1 - 1, by omega⟩ : Fin (j.1 + 1)).succ := Fin.ext (by dsimp; omega)
      have hp2 : (⟨l.1 + 1, by omega⟩ : Fin (j.1 + 2)) =
          (⟨l.1, by omega⟩ : Fin (j.1 + 1)).succ := rfl
      simp only [Fin.val_succ, hlv, hl1, hlj, hlj1, ↓reduceDIte, Fin.contractNth, Fin.val_zero,
        Nat.not_lt_zero, ↓reduceIte, Nat.add_sub_cancel, hp1, hp2, Fin.cons_succ]
      rfl
    · by_cases hlj1 : l.1 = j.1 + 1
      · have h0 : j.1 + 1 ≠ 0 := by omega
        have h1 : ¬j.1 + 1 ≤ j.1 := by omega
        have h2 : j.1 + 1 + 1 ≠ 0 := by omega
        have h3 : ¬j.1 + 1 + 1 ≤ j.1 + 1 := by omega
        simp only [Fin.val_succ, hlj1, h0, h1, h2, h3, ↓reduceDIte, ← Fin.succ_last, Fin.cons_succ]
      · have h1 : ¬l.1 + 1 ≤ j.1 + 1 := by omega
        have h2 : l.1 + 1 ≠ j.1 + 1 + 1 := by omega
        have h3 : l.1 - 1 ≠ 0 := by omega
        simp only [Fin.val_succ, hlv, hl1, hlj, hlj1, h1, h2, ↓reduceDIte, Fin.contractNth,
          Fin.val_zero, Nat.not_lt_zero, h3, ↓reduceIte]
        exact congrArg a (Fin.ext (by dsimp; omega))

/-- Lower-triangle identity when `i = 0`: `h_{j+1} (δ_0 ψ) a = h_j ψ (d_0 a)`. -/
private theorem matrixHomotopyTerm_succ_hochschildCoface_zero (r : ι) {m : ℕ} (j : Fin (m + 1))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (a : Fin (m + 2) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r j.succ (hochschildCoface R (Matrix ι ι A) M 0 ψ) a =
      matrixHomotopyTerm (R := R) r j ψ (hochschildFace 0 a) := by
  have hface0 (v : Fin (m + 2) → Matrix ι ι A) :
      hochschildFace (0 : Fin (m + 2)) v = Fin.contractNth (0 : Fin (m + 2)) (· * ·) v := by
    simpa [Fin.castSucc_zero] using hochschildFace_castSucc (0 : Fin (m + 1)) v
  rw [matrixHomotopyTerm_apply, matrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply, Fin.val_succ]
  rw [← (Fin.consEquiv (fun _ : Fin (j.1 + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp_rw [Fin.consEquiv_apply, hochschildFace_zero_matrixHomotopyTuple_cons]
  rw [← ψ.map_update_sum, Matrix.sum_mul_single_eq_mul_mul_single]
  congr 1
  rw [Function.update_eq_self_iff, hface0]
  simp [matrixHomotopyTuple_apply, Fin.contractNth]

/-- Tuple identity behind the lower-triangle relation for `0 < i ≤ j`. -/
private theorem hochschildFace_castSucc_matrixHomotopyTuple_insertNth (r : ι) {m : ℕ}
    (j : Fin (m + 1)) (i : Fin (m + 2)) (hi0 : 0 < i.1) (hij : i.1 ≤ j.1)
    (q : Fin (j.1 + 2)) (hq : q.1 = i.1)
    (p : Fin (j.1 + 1) → ι) (t : ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace i.castSucc
        (matrixHomotopyTuple r j.succ (Fin.insertNth (α := fun _ ↦ ι) q t p) a) =
      Function.update (matrixHomotopyTuple r j p (hochschildFace i a))
        i (Matrix.single r r (a ⟨i.1, by omega⟩ (p ⟨i.1 - 1, by omega⟩) t *
          a ⟨i.1 + 1, by omega⟩ t (p ⟨i.1, by omega⟩))) := by
  have hi_face : hochschildFace i a = Fin.contractNth i (· * ·) a := by
    have hi_eq : i = (⟨i.1, by omega⟩ : Fin (m + 1)).castSucc := Fin.ext rfl
    rw [hi_eq, hochschildFace_castSucc]
  have hbelow (x : Fin (j.1 + 2)) (hx : x.1 < i.1) :
      Fin.insertNth (α := fun _ ↦ ι) q t p x = p ⟨x.1, by omega⟩ := by
    have hx' : x = q.succAbove ⟨x.1, by omega⟩ := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def, hq]; exact hx)]; rfl
    exact (congrArg (Fin.insertNth (α := fun _ ↦ ι) q t p) hx').trans
      (Fin.insertNth_apply_succAbove (α := fun _ ↦ ι) q t p _)
  have habove (x : Fin (j.1 + 2)) (hx : i.1 < x.1) :
      Fin.insertNth (α := fun _ ↦ ι) q t p x = p ⟨x.1 - 1, by omega⟩ := by
    have hx' : x = q.succAbove ⟨x.1 - 1, by omega⟩ := by
      rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, hq]; dsimp; omega)]
      exact Fin.ext (by dsimp; omega)
    exact (congrArg (Fin.insertNth (α := fun _ ↦ ι) q t p) hx').trans
      (Fin.insertNth_apply_succAbove (α := fun _ ↦ ι) q t p _)
  rw [hochschildFace_castSucc, hi_face]
  funext l
  by_cases hl : l = i
  · -- Coordinate `l = i`: multiply the two adjacent `E_{r r}` entries sharing index `t`.
    rw [hl, Function.update_self]
    have hl0 : i.1 ≠ 0 := by omega
    have hlj : i.1 ≤ j.1 + 1 := by omega
    have hl1j : i.1 + 1 ≤ j.1 + 1 := by omega
    simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ, lt_self_iff_false, ↓reduceIte,
      matrixHomotopyTuple_apply, hl0, hlj, hl1j, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      Nat.add_sub_cancel, ↓reduceDIte]
    have hqi : (⟨i.1, by omega⟩ : Fin (j.1 + 2)) = q := Fin.ext hq.symm
    rw [hbelow ⟨i.1 - 1, by omega⟩ (by dsimp; omega), hqi, Fin.insertNth_apply_same,
      habove ⟨i.1 + 1, by omega⟩ (by dsimp; omega), Matrix.single_mul_single_same]
    rfl
  · rw [Function.update_of_ne hl]
    have hlv : l.1 ≠ i.1 := fun h ↦ hl (Fin.ext h)
    rcases lt_or_gt_of_ne hlv with hlt | hgt
    · -- Coordinate `l < i`: both sides read strictly below the insertion position `q`.
      simp only [Fin.contractNth, Fin.val_castSucc, hlt, ↓reduceIte]
      rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
      by_cases hl0 : l.1 = 0
      · simp only [Fin.val_castSucc, hl0, ↓reduceDIte, Fin.contractNth, Fin.val_zero, hi0,
          ↓reduceIte]
        rw [hbelow 0 (by simpa using hi0)]
        rfl
      · have hlj : l.1 ≤ j.1 := by omega
        have hlj1 : l.1 ≤ j.1 + 1 := by omega
        simp only [Fin.val_castSucc, Fin.val_succ, hl0, hlj, hlj1, ↓reduceDIte, Fin.contractNth,
          hlt, ↓reduceIte]
        rw [hbelow ⟨l.1 - 1, by omega⟩ (by dsimp; omega), hbelow ⟨l.1, by omega⟩ hlt]
        rfl
    · -- Coordinate `l > i`: indices shift by `+1` and read strictly above `q`.
      have hnl : ¬l.1 < i.1 := by omega
      have hl0 : l.1 ≠ 0 := by omega
      have hl10 : l.1 + 1 ≠ 0 := by omega
      simp only [Fin.contractNth, Fin.val_castSucc, hnl, hlv, ↓reduceIte]
      rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
      by_cases hlj : l.1 ≤ j.1
      · have hlj1 : l.1 + 1 ≤ j.1 + 1 := by omega
        simp only [Fin.val_succ, hl0, hl10, hlj, hlj1, ↓reduceDIte, Fin.contractNth, hnl, hlv,
          ↓reduceIte, Nat.add_sub_cancel]
        rw [habove ⟨l.1, by omega⟩ hgt, habove ⟨l.1 + 1, by omega⟩ (by dsimp; omega)]
        rfl
      · by_cases hlj1 : l.1 = j.1 + 1
        · have h0 : j.1 + 1 ≠ 0 := by omega
          have h1 : ¬j.1 + 1 ≤ j.1 := by omega
          have h2 : j.1 + 1 + 1 ≠ 0 := by omega
          have h3 : ¬j.1 + 1 + 1 ≤ j.1 + 1 := by omega
          simp only [Fin.val_succ, hlj1, h0, h1, h2, h3, ↓reduceDIte]
          rw [habove (Fin.last (j.1 + 1)) (by simp only [Fin.val_last]; omega)]
          exact congrArg (fun x ↦ Matrix.single r x 1) (congrArg p (Fin.ext rfl))
        · have h1 : ¬l.1 + 1 ≤ j.1 + 1 := by omega
          have h2 : l.1 + 1 ≠ j.1 + 1 + 1 := by omega
          have h3 : ¬l.1 - 1 < i.1 := by omega
          have h4 : l.1 - 1 ≠ i.1 := by omega
          simp only [Fin.val_succ, hl0, hl10, hlj, hlj1, h1, h2, ↓reduceDIte, Fin.contractNth,
            h3, h4, ↓reduceIte]
          exact congrArg a (Fin.ext (by dsimp; omega))

/-- Lower-triangle identity for `0 < i ≤ j`: `h_{j+1} (δ_i ψ) a = h_j ψ (d_i a)`. -/
private theorem matrixHomotopyTerm_succ_hochschildCoface_castSucc_of_pos (r : ι) {m : ℕ}
    (j : Fin (m + 1)) (i : Fin (m + 2)) (hi0 : 0 < i.1) (hij : i.1 ≤ j.1)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (a : Fin (m + 2) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r j.succ (hochschildCoface R (Matrix ι ι A) M i.castSucc ψ) a =
      matrixHomotopyTerm (R := R) r j ψ (hochschildFace i a) := by
  have hi_face : hochschildFace i a = Fin.contractNth i (· * ·) a := by
    have hi_eq : i = (⟨i.1, by omega⟩ : Fin (m + 1)).castSucc := Fin.ext rfl
    rw [hi_eq, hochschildFace_castSucc]
  have hsingle (f : ι → A) : ∑ t : ι, Matrix.single r r (f t) = Matrix.single r r (∑ t : ι, f t) :=
    (map_sum (Matrix.singleAddMonoidHom (α := A) r r) f Finset.univ).symm
  let q : Fin (j.1 + 2) := ⟨i.1, by omega⟩
  rw [matrixHomotopyTerm_apply, matrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply, Fin.val_succ]
  rw [← (Fin.insertNthEquiv (fun _ : Fin (j.1 + 2) ↦ ι) q).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp_rw [Fin.insertNthEquiv_apply,
    hochschildFace_castSucc_matrixHomotopyTuple_insertNth r j i hi0 hij q rfl p _ a]
  rw [← ψ.map_update_sum, hsingle]
  congr 1
  rw [Function.update_eq_self_iff, hi_face]
  have hi0' : i.1 ≠ 0 := by omega
  simp only [matrixHomotopyTuple_apply, hi0', hij, ↓reduceDIte, Fin.contractNth, lt_self_iff_false,
    ↓reduceIte, Matrix.mul_apply]
  rfl

/-- Combined lower-triangle identity for `i ≤ j`: `h_{j+1} (δ_i ψ) a = h_j ψ (d_i a)`. -/
private theorem matrixHomotopyTerm_succ_hochschildCoface_castSucc (r : ι) {m : ℕ}
    (j : Fin (m + 1)) (i : Fin (m + 2)) (hij : i.1 ≤ j.1)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (a : Fin (m + 2) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r j.succ (hochschildCoface R (Matrix ι ι A) M i.castSucc ψ) a =
      matrixHomotopyTerm (R := R) r j ψ (hochschildFace i a) := by
  by_cases hi0 : i.1 = 0
  · obtain rfl : i = 0 := Fin.ext hi0
    exact matrixHomotopyTerm_succ_hochschildCoface_zero r j ψ a
  · exact matrixHomotopyTerm_succ_hochschildCoface_castSucc_of_pos r j i (by omega) hij ψ a

/-- Upper-triangle tuple identity for the last face (`i = last`). -/
private theorem hochschildFace_last_matrixHomotopyTuple_castSucc (r : ι) {m : ℕ}
    (j : Fin (m + 1)) (k : Fin (j.1 + 1) → ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace (Fin.last (m + 2)) (matrixHomotopyTuple r j.castSucc k a) =
      matrixHomotopyTuple r j k (hochschildFace (Fin.last (m + 1)) a) := by
  funext l
  rw [hochschildFace_last, hochschildFace_last]
  cases l using Fin.cases with
  | zero =>
    have h1 : ¬m + 2 ≤ j.1 := by omega
    have h2 : m + 2 ≠ j.1 + 1 := by omega
    simp only [Fin.cons_zero, matrixHomotopyTuple_apply, Fin.val_last, Fin.val_zero,
      Fin.val_castSucc, Nat.add_eq_zero_iff, one_ne_zero, and_false, h1, h2, ↓reduceDIte]
    rw [mul_assoc]; rfl
  | succ l =>
    rw [Fin.cons_succ, matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
    by_cases hlj : l.1 + 1 ≤ j.1
    · simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        hlj, ↓reduceDIte]
      rfl
    · by_cases hlj1 : l.1 + 1 = j.1 + 1
      · have h1 : ¬j.1 + 1 ≤ j.1 := by omega
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          hlj1, h1, ↓reduceDIte]
      · have hl0 : l.1 ≠ 0 := by omega
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          hlj, hlj1, ↓reduceDIte, Nat.add_sub_cancel]
        cases l using Fin.cases with
        | zero => simp at hl0
        | succ l => rfl

/-- Upper-triangle tuple identity for an interior face `i.castSucc` with `j < i`. -/
private theorem hochschildFace_castSucc_succ_matrixHomotopyTuple_castSucc (r : ι) {m : ℕ}
    (j : Fin (m + 1)) (i : Fin (m + 1)) (hji : j.1 < i.1)
    (k : Fin (j.1 + 1) → ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace i.succ.castSucc (matrixHomotopyTuple r j.castSucc k a) =
      matrixHomotopyTuple r j k (hochschildFace i.castSucc a) := by
  funext l
  rw [hochschildFace_castSucc, hochschildFace_castSucc]
  -- Coordinates `l ≤ j + 1` lie strictly before the contraction at `i.succ`.
  by_cases hl0 : l.1 = 0
  · have h0i : 0 < i.1 := by omega
    have h0i1 : 0 < i.1 + 1 := by omega
    simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, hl0, h0i1, ↓reduceIte]
    rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
    simp only [Fin.val_castSucc, hl0, ↓reduceDIte, Fin.contractNth, Fin.val_zero, h0i, ↓reduceIte]
    rfl
  · by_cases hlj : l.1 ≤ j.1
    · have hli : l.1 < i.1 := by omega
      have hli1 : l.1 < i.1 + 1 := by omega
      simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, hli1, ↓reduceIte]
      rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
      simp only [Fin.val_castSucc, hl0, hlj, ↓reduceDIte, Fin.contractNth, hli, ↓reduceIte]
      rfl
    · by_cases hlj1 : l.1 = j.1 + 1
      · have hli1 : j.1 + 1 < i.1 + 1 := by omega
        have h0 : j.1 + 1 ≠ 0 := by omega
        have h1 : ¬j.1 + 1 ≤ j.1 := by omega
        simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, hlj1, hli1, ↓reduceIte]
        rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
        simp only [Fin.val_castSucc, hlj1, h0, h1, ↓reduceDIte]
      · -- Coordinates `l > j + 1` pass through the unmodified tail `a_{l-1}`.
        rcases lt_trichotomy (l.1 - 1) i.1 with hlt | heq | hgt
        · have hli1 : l.1 < i.1 + 1 := by omega
          simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, hli1, ↓reduceIte]
          rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
          simp only [Fin.val_castSucc, hl0, hlj, hlj1, ↓reduceDIte, Fin.contractNth, hlt,
            ↓reduceIte]
          exact congrArg a (Fin.ext rfl)
        · have heq1 : l.1 = i.1 + 1 := by omega
          have hl10 : l.1 + 1 ≠ 0 := by omega
          have hlj' : ¬l.1 + 1 ≤ j.1 := by omega
          have hlj1' : l.1 + 1 ≠ j.1 + 1 := by omega
          simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, heq1, lt_self_iff_false,
            ↓reduceIte]
          rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
          simp only [Fin.val_castSucc, Fin.val_succ, hl0, hl10, hlj, hlj1, hlj', hlj1',
            ↓reduceDIte, Fin.contractNth, heq, lt_self_iff_false, ↓reduceIte]
          exact congrArg₂ (· * ·) (congrArg a (Fin.ext rfl))
            (congrArg a (Fin.ext (by dsimp; omega)))
        · have hnl1 : ¬l.1 < i.1 + 1 := by omega
          have hne1 : l.1 ≠ i.1 + 1 := by omega
          have hnl : ¬l.1 - 1 < i.1 := by omega
          have hne : l.1 - 1 ≠ i.1 := by omega
          have hl10 : l.1 + 1 ≠ 0 := by omega
          have hlj' : ¬l.1 + 1 ≤ j.1 := by omega
          have hlj1' : l.1 + 1 ≠ j.1 + 1 := by omega
          simp only [Fin.contractNth, Fin.val_succ, Fin.val_castSucc, hnl1, hne1, ↓reduceIte]
          rw [matrixHomotopyTuple_apply, matrixHomotopyTuple_apply]
          simp only [Fin.val_castSucc, Fin.val_succ, hl0, hl10, hlj, hlj1, hlj', hlj1',
            ↓reduceDIte, Fin.contractNth, hnl, hne, ↓reduceIte]
          exact congrArg a (Fin.ext (by dsimp; omega))

/-- Upper-triangle identity for `j < i`: `h_j (δ_{i+1} ψ) a = h_j ψ (d_i a)` (holds termwise in
the index path `k`). -/
private theorem matrixHomotopyTerm_castSucc_hochschildCoface_succ (r : ι) {m : ℕ}
    (j : Fin (m + 1)) (i : Fin (m + 2)) (hji : j.1 < i.1)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (a : Fin (m + 2) → Matrix ι ι A) :
    matrixHomotopyTerm (R := R) r j.castSucc (hochschildCoface R (Matrix ι ι A) M i.succ ψ) a =
      matrixHomotopyTerm (R := R) r j ψ (hochschildFace i a) := by
  rw [matrixHomotopyTerm_apply, matrixHomotopyTerm_apply]
  simp only [hochschildCoface_apply]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg ψ ?_
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.succ_last]
    exact hochschildFace_last_matrixHomotopyTuple_castSucc r j k a
  | cast i =>
    rw [Fin.succ_castSucc]
    exact hochschildFace_castSucc_succ_matrixHomotopyTuple_castSucc r j i hji k a

/-- Degree-zero homotopy identity: `H_0 (b ψ) = ψ - (inc_r* ψ)#Tr`. -/
private theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy (R := R) r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) =
      ψ - matrixCochainExtension ι 0 (matrixCornerCochainRestriction (R := R) r 0 ψ) := by
  ext a
  rw [matrixHochschildHomotopy, LinearMap.sum_apply, Fin.sum_univ_one, Fin.val_zero, pow_zero,
    one_smul, sub_apply]
  have hb : hochschildCoboundary R (Matrix ι ι A) M 0 ψ =
      hochschildCoface R (Matrix ι ι A) M 0 ψ - hochschildCoface R (Matrix ι ι A) M 1 ψ := by
    ext x
    simp [hochschildCoboundary_apply, Fin.sum_univ_two, sub_eq_add_neg]
  rw [hb, map_sub, sub_apply, matrixHomotopyTerm_zero_hochschildCoface_zero]
  congr 1
  exact matrixHomotopyTerm_last_hochschildCoface_last r (n := 0) ψ a

/-- Positive-degree homotopy identity: `H_{m+1} (b ψ) + b (H_m ψ) = ψ - (inc_r* ψ)#Tr`. -/
private theorem matrixHochschildHomotopy_hochschildCoboundary_add_hochschildCoboundary (r : ι)
    (m : ℕ) (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy (R := R) r (m + 1)
        (hochschildCoboundary R (Matrix ι ι A) M (m + 1) ψ) +
      hochschildCoboundary R (Matrix ι ι A) M m (matrixHochschildHomotopy (R := R) r m ψ) =
      ψ - matrixCochainExtension ι (m + 1)
        (matrixCornerCochainRestriction (R := R) r (m + 1) ψ) := by
  have hb : hochschildCoboundary R (Matrix ι ι A) M (m + 1) ψ =
      ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • hochschildCoface R (Matrix ι ι A) M i ψ := by
    ext x; simp [hochschildCoboundary_apply]
  ext a
  rw [add_apply, sub_apply]
  have h1 : matrixHochschildHomotopy (R := R) r (m + 1)
      (hochschildCoboundary R (Matrix ι ι A) M (m + 1) ψ) a =
      ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
        ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) •
          matrixHomotopyTerm (R := R) r j (hochschildCoface R (Matrix ι ι A) M i ψ) a := by
    rw [matrixHochschildHomotopy, LinearMap.sum_apply, sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [LinearMap.smul_apply, smul_apply, hb, map_sum, sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, smul_apply])
  have h2 : hochschildCoboundary R (Matrix ι ι A) M m
      (matrixHochschildHomotopy (R := R) r m ψ) a =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j : ℕ) •
          matrixHomotopyTerm (R := R) r j ψ (hochschildFace i a) := by
    rw [hochschildCoboundary_apply, matrixHochschildHomotopy]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply, smul_apply]
  rw [h1, h2, sum_neg_one_pow_smul_sum_neg_one_pow_smul_add_eq_sub
    (F := fun j i ↦
      matrixHomotopyTerm (R := R) r j (hochschildCoface R (Matrix ι ι A) M i ψ) a)
    (E := fun j i ↦ matrixHomotopyTerm (R := R) r j ψ (hochschildFace i a))
    (fun k ↦ matrixHomotopyTerm_diag r k ψ a)
    (fun j i hij ↦ matrixHomotopyTerm_succ_hochschildCoface_castSucc r j i hij ψ a)
    (fun j i hji ↦ matrixHomotopyTerm_castSucc_hochschildCoface_succ r j i hji ψ a),
    matrixHomotopyTerm_zero_hochschildCoface_zero, matrixHomotopyTerm_last_hochschildCoface_last]

end HochschildHomotopy

/-! ### Matrix Morita invariance of Hochschild cohomology -/

namespace hochschildCohomology

section Map

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

variable (M) in
/-- The map `HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` on Hochschild
cohomology induced by the generalized matrix trace `φ ↦ φ#Tr`. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2
      (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends the class of a cocycle to the class of its
matrix extension. -/
@[simp]
theorem matrixExtension_mk {ι : Type*} [Fintype ι] {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ.1,
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

variable (M) in
/-- Restriction to the `(r, r)` diagonal corner on Hochschild cohomology. -/
def matrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCornerCochainRestriction (R := R) r n).restrict
      fun _ ↦ matrixCornerCochainRestriction_mem_hochschildCocycles r)
    fun _ hψ ↦ (mk_eq_zero_iff _ _ _ n _).2
      (matrixCornerCochainRestriction_mem_hochschildCoboundaries r hψ)

/-- Corner restriction on Hochschild cohomology sends the class of a matrix cocycle to the class
of its restriction to the `(r, r)` diagonal corner. -/
@[simp]
theorem matrixCornerRestriction_mk {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}
    (ψ : hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCornerRestriction M r n (mk R (Matrix ι ι A) M n ψ) =
      mk R A M n ⟨matrixCornerCochainRestriction (R := R) r n ψ.1,
        matrixCornerCochainRestriction_mem_hochschildCocycles r ψ.2⟩ :=
  desc_mk _ _ _ ψ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp]
theorem matrixCornerRestriction_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (c : hochschildCohomology R A M n) :
    matrixCornerRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  simp only [matrixExtension_mk, matrixCornerRestriction_mk]
  congr 1
  exact Subtype.ext (matrixCornerCochainRestriction_matrixCochainExtension r n φ.1)

end Map

section Morita

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- For a unital algebra, matrix extension is a left inverse to corner restriction on Hochschild
cohomology (via Loday's cochain homotopy). -/
@[simp]
theorem matrixExtension_matrixCornerRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (matrixCornerRestriction M r n c) = c := by
  obtain ⟨ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [matrixCornerRestriction_mk, matrixExtension_mk, eq_comm, mk_eq_mk_iff]
  have hψ : hochschildCoboundary R (Matrix ι ι A) M n ψ.1 = 0 :=
    mem_hochschildCocycles_iff.1 ψ.2
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot]
    have h := matrixHochschildHomotopy_hochschildCoboundary_zero (R := R) r ψ.1
    rw [hψ, map_zero] at h
    exact h.symm
  | succ m =>
    rw [mem_hochschildCoboundaries_succ_iff]
    refine ⟨matrixHochschildHomotopy (R := R) r m ψ.1, ?_⟩
    have h := matrixHochschildHomotopy_hochschildCoboundary_add_hochschildCoboundary
      (R := R) r m ψ.1
    rwa [hψ, map_zero, zero_add] at h

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital algebra `A` over any
commutative ring `R`, any `R`-module `M`, and any nonempty finite index type `ι`, the generalized
matrix trace induces a bijection
`HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.bijective_iff_has_inverse.2
    ⟨matrixCornerRestriction M r n,
      matrixCornerRestriction_matrixExtension r n,
      matrixExtension_matrixCornerRestriction r n⟩

variable (M) in
/-- **Matrix Morita equivalence of Hochschild cohomology**, as an `R`-linear equivalence
`HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))`. -/
def matrixEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The Morita linear equivalence on Hochschild cohomology is given by `matrixExtension`. -/
@[simp]
theorem matrixEquiv_apply {ι : Type*} [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixEquiv M ι n c = matrixExtension M ι n c := by
  rfl

/-- The inverse of `matrixEquiv` is given by diagonal corner restriction at any index `r : ι`. -/
theorem matrixEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (r : ι)
    (n : ℕ) (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixEquiv M ι n).symm c = matrixCornerRestriction M r n c :=
  (bijective_matrixExtension ι n).1 <| by
    rw [← matrixEquiv_apply, LinearEquiv.apply_symm_apply, matrixExtension_matrixCornerRestriction]

end Morita

end hochschildCohomology

end TauCeti
