/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Matrix.Basic
public import TauCeti.RingTheory.HochschildCohomology.Complex
import Mathlib.Tactic.Abel
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For an `R`-algebra `A`, an `R`-module `M`, and finite `ι`, `TauCeti.matrixCochainExtension` sends
`φ` to `φ#Tr` on `Matrix ι ι A` and `TauCeti.matrixCornerRestriction` pulls back along
`TauCeti.matrixCornerNonUnitalAlgHom`, giving a cochain left inverse. When `A` is unital,
`TauCeti.matrixHochschildHomotopy` (`hₙ Φ = ∑_{m = 0}^n λₙ^m (S_{n, m} Φ)` built from
`TauCeti.matrixHochschildHomotopyStep`, summing
`Φ(E_{p₀, r}(1), E_{r, r}((b₀)_{p₀, p₁}), …, E_{r, p_m}(1) b_m, b_{m+1}, …, b_n)` over paths `p`)
satisfies `h₀ (b₀ Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr` and
`h_{k+1} (b_{k+1} Ψ) + b_k (h_k Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr`, proving matrix Morita invariance of
`HHⁿ` over every commutative ring `R` for nonempty finite `ι`.

## Main definitions and results

* `TauCeti.matrixHochschildHomotopyStep`, `TauCeti.matrixHochschildHomotopy`,
  `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero`,
  `matrixHochschildHomotopy_hochschildCoboundary_add_hochschildCoboundary_matrixHochschildHomotopy`.
* `TauCeti.hochschildCohomology.matrixExtension`, `TauCeti.hochschildCohomology.cornerRestriction`,
  `TauCeti.hochschildCohomology.bijective_matrixExtension`,
  `TauCeti.hochschildCohomology.matrixExtensionEquiv`.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS **62** (1985), Part II, §1;
  *Noncommutative Geometry* (1994), Chapter III, §1.
* R. McCarthy, *Morita equivalence and cyclic homology*, C. R. Acad. Sci. Paris Sér. I Math.
  **307** (1988), 211–215.
* J.-L. Loday, *Cyclic Homology*, 2nd ed., Springer, 1998, §§1.2.4, 1.5.6.
-/

public section

namespace TauCeti

open scoped BigOperators

section Cocycles

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι] {n : ℕ}

/-- Matrix extension sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff, ← matrixCochainExtension_hochschildCoboundary,
    mem_hochschildCocycles_iff.1 hφ, map_zero]

/-- Matrix extension sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero => simp_all [hochschildCoboundaries_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainExtension ι n ψ, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩

/-- Corner restriction sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCornerRestriction_mem_hochschildCocycles [DecidableEq ι] (r : ι)
    {Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M}
    (hΦ : Φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n Φ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff, ← matrixCornerRestriction_hochschildCoboundary,
    mem_hochschildCocycles_iff.1 hΦ, map_zero]

/-- Corner restriction sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCornerRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι)
    {Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M}
    (hΦ : Φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCornerRestriction r n Φ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero => simp_all [hochschildCoboundaries_zero]
  | succ n =>
    obtain ⟨Ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hΦ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCornerRestriction r n Ψ, (matrixCornerRestriction_hochschildCoboundary r n Ψ).symm⟩

end Cocycles

private theorem insertNth_succ_apply_of_le {α : Type*} {m' i s : ℕ} (hi : i ≤ m') (u : α)
    (q : Fin (m' + 1) → α) (hs : s ≤ i) (hs' : s < m' + 2) :
    (Fin.insertNth ⟨i + 1, by omega⟩ u q : Fin (m' + 2) → α) ⟨s, hs'⟩ = q ⟨s, by omega⟩ := by
  rw [show (⟨s, hs'⟩ : Fin (m' + 2)) = (⟨i + 1, by omega⟩ : Fin (m' + 2)).succAbove ⟨s, by omega⟩ by
    ext; simp only [Fin.val_succAbove]; split_ifs <;> omega, Fin.insertNth_apply_succAbove]

private theorem insertNth_succ_apply_succ_of_gt {α : Type*} {m' i s : ℕ} (hi : i ≤ m') (u : α)
    (q : Fin (m' + 1) → α) (hs : i < s) (hs' : s + 1 < m' + 2) :
    (Fin.insertNth ⟨i + 1, by omega⟩ u q : Fin (m' + 2) → α) ⟨s + 1, hs'⟩ = q ⟨s, by omega⟩ := by
  rw [show (⟨s + 1, hs'⟩ : Fin (m' + 2)) =
      (⟨i + 1, by omega⟩ : Fin (m' + 2)).succAbove ⟨s, by omega⟩ by
    ext; simp only [Fin.val_succAbove]; split_ifs <;> omega, Fin.insertNth_apply_succAbove]

section Coord

variable {R A ι : Type*} [Semiring R] [Semiring A] [Module R A] [SMulCommClass R A A] [Fintype ι]
  [DecidableEq ι]

private def homotopyCoordLinearMap (r : ι) {m : ℕ} (p : Fin (m + 1) → ι) (k : ℕ) :
    Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if hk : k < m then Matrix.singleLinearMap R r r ∘ₗ
    Matrix.entryLinearMap R A (p ⟨k, by omega⟩) (p ⟨k + 1, by omega⟩)
  else if _ : k = m then LinearMap.mulLeft R (Matrix.single r (p ⟨m, by omega⟩) (1 : A))
  else LinearMap.id

private theorem homotopyCoordLinearMap_of_lt (r : ι) {m k : ℕ} (hk : k < m)
    (p : Fin (m + 1) → ι) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r p k X =
      Matrix.single r r (X (p ⟨k, by omega⟩) (p ⟨k + 1, by omega⟩)) := by
  simp [homotopyCoordLinearMap, hk]

private theorem homotopyCoordLinearMap_same (r : ι) (m : ℕ) (p : Fin (m + 1) → ι)
    (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r p m X = Matrix.single r (p ⟨m, by omega⟩) (1 : A) * X := by
  simp [homotopyCoordLinearMap]

private theorem homotopyCoordLinearMap_of_gt (r : ι) {m k : ℕ} (hk : m < k)
    (p : Fin (m + 1) → ι) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r p k X = X := by
  simp [homotopyCoordLinearMap, show ¬k < m by omega, show k ≠ m by omega]

private theorem homotopyCoordLinearMap_cons_succ (r u : ι) {m : ℕ} (q : Fin (m + 1) → ι) (k : ℕ)
    (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r (Fin.cons u q) (k + 1) X =
      homotopyCoordLinearMap (R := R) r q k X := by
  by_cases hk : k < m
  · rw [homotopyCoordLinearMap_of_lt r (by omega), homotopyCoordLinearMap_of_lt r hk]
    exact congrArg (Matrix.single r r) (congrArg₂ X
      (Fin.cons_succ (α := fun _ => ι) u q ⟨k, by omega⟩)
      (Fin.cons_succ (α := fun _ => ι) u q ⟨k + 1, by omega⟩))
  · rcases Nat.eq_or_lt_of_le (Nat.not_lt.1 hk) with rfl | hgt
    · rw [homotopyCoordLinearMap_same, homotopyCoordLinearMap_same]
      exact congrArg (fun i => Matrix.single r i (1 : A) * X)
        (Fin.cons_succ (α := fun _ => ι) u q ⟨m, Nat.lt_succ_self m⟩)
    · rw [homotopyCoordLinearMap_of_gt r (by omega), homotopyCoordLinearMap_of_gt r hgt]

private theorem homotopyCoordLinearMap_insertNth_of_lt (r u : ι) {m' i j : ℕ} (hi : i ≤ m')
    (hj : j < i) (q : Fin (m' + 1) → ι) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r (Fin.insertNth ⟨i + 1, by omega⟩ u q) j X =
      homotopyCoordLinearMap (R := R) r q j X := by
  rw [homotopyCoordLinearMap_of_lt r (by omega), homotopyCoordLinearMap_of_lt r (by omega),
    insertNth_succ_apply_of_le hi u q (by omega) (by omega),
    insertNth_succ_apply_of_le hi u q (by omega) (by omega)]

private theorem homotopyCoordLinearMap_insertNth_succ_of_gt (r u : ι) {m' i j : ℕ} (hi : i ≤ m')
    (hj : i < j) (q : Fin (m' + 1) → ι) (X : Matrix ι ι A) :
    homotopyCoordLinearMap (R := R) r (Fin.insertNth ⟨i + 1, by omega⟩ u q) (j + 1) X =
      homotopyCoordLinearMap (R := R) r q j X := by
  by_cases hjm : j < m'
  · rw [homotopyCoordLinearMap_of_lt r (by omega), homotopyCoordLinearMap_of_lt r hjm,
      insertNth_succ_apply_succ_of_gt hi u q hj (by omega),
      insertNth_succ_apply_succ_of_gt hi u q (by omega) (by omega)]
  · rcases Nat.eq_or_lt_of_le (Nat.not_lt.1 hjm) with rfl | hgt
    · rw [homotopyCoordLinearMap_same, homotopyCoordLinearMap_same,
        insertNth_succ_apply_succ_of_gt hi u q hj (by omega)]
    · rw [homotopyCoordLinearMap_of_gt r (by omega), homotopyCoordLinearMap_of_gt r hgt]

private theorem sum_homotopyCoordLinearMap_insertNth_mul (r : ι) {m' i : ℕ} (hi : i ≤ m')
    (q : Fin (m' + 1) → ι) (X Y : Matrix ι ι A) :
    (∑ u : ι, homotopyCoordLinearMap (R := R) r (Fin.insertNth ⟨i + 1, by omega⟩ u q) i X *
        homotopyCoordLinearMap (R := R) r (Fin.insertNth ⟨i + 1, by omega⟩ u q) (i + 1) Y) =
      homotopyCoordLinearMap (R := R) r q i (X * Y) := by
  have hsame (u : ι) : (Fin.insertNth ⟨i + 1, by omega⟩ u q : Fin (m' + 2) → ι) ⟨i + 1, by omega⟩ =
      u := Fin.insertNth_apply_same (α := fun _ => ι) ⟨i + 1, by omega⟩ u q
  rcases lt_or_eq_of_le hi with hlt | rfl
  · trans ∑ u : ι, Matrix.single r r (X (q ⟨i, by omega⟩) u * Y u (q ⟨i + 1, by omega⟩))
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [homotopyCoordLinearMap_of_lt r (by omega), homotopyCoordLinearMap_of_lt r (by omega),
        insertNth_succ_apply_of_le hi u q le_rfl (by omega), hsame u,
        insertNth_succ_apply_succ_of_gt hi u q (Nat.lt_succ_self i) (by omega),
        Matrix.single_mul_single_same]
    · simp_rw [← Matrix.singleAddMonoidHom_apply, ← map_sum, Matrix.singleAddMonoidHom_apply,
        ← Matrix.mul_apply, homotopyCoordLinearMap_of_lt r hlt]
  · trans ∑ u : ι, (Matrix.single r (q ⟨i, by omega⟩) (1 : A) * X * Matrix.single u u (1 : A)) * Y
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [homotopyCoordLinearMap_of_lt r (Nat.lt_succ_self i), homotopyCoordLinearMap_same,
        insertNth_succ_apply_of_le le_rfl u q le_rfl (by omega), hsame u, ← mul_assoc,
        Matrix.single_mul_single_same, mul_one, Matrix.single_mul_mul_single, one_mul, mul_one]
    · simp_rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.sum_single_one, mul_one, mul_assoc,
        homotopyCoordLinearMap_same]

end Coord

section Step

variable {R A M ι : Type*} [Semiring R] [Semiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι]
  [DecidableEq ι]

/-- The unrotated `m`-th homotopy step `S_{n, m}` used to build `matrixHochschildHomotopy`. -/
noncomputable def matrixHochschildHomotopyStep {M : Type*} [AddCommMonoid M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n m : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M where
  toFun Φ := ∑ p : Fin (m + 1) → ι,
    (MultilinearMap.mk' (fun a => Φ (Fin.cons (Matrix.single (p 0) r 1) a))
      (fun a i x y => by
        rw [Fin.cons_update, Φ.map_update_add, ← Fin.cons_update, ← Fin.cons_update])
      (fun a i c x => by
        rw [Fin.cons_update, Φ.map_update_smul, RingHom.id_apply, ← Fin.cons_update])).compLinearMap
      fun k : Fin (n + 1) => homotopyCoordLinearMap r p k
  map_add' _ _ := by ext b; simp [Finset.sum_add_distrib]
  map_smul' _ _ := by ext b; simp [Finset.smul_sum]

omit [IsScalarTower R A A] in
private theorem matrixHochschildHomotopyStep_apply_coord {M : Type*} [AddCommMonoid M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n m : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M)
    (b : Fin (n + 1) → Matrix ι ι A) : matrixHochschildHomotopyStep r n m Φ b =
      ∑ p : Fin (m + 1) → ι, Φ (Fin.cons (Matrix.single (p 0) r 1)
        fun k => homotopyCoordLinearMap (R := R) r p k (b k)) := by
  simp [matrixHochschildHomotopyStep]

omit [IsScalarTower R A A] in
/-- Evaluating `matrixHochschildHomotopyStep r n m Φ` sums over paths `p : Fin (m + 1) → ι`,
placing `E_{p₀, r}(1)` in slot `0`, `E_{r, r}((bₖ)_{pₖ, pₖ₊₁})` for `k < m`, and `E_{r, pₘ}(1) bₘ`
at `k = m`. -/
@[simp]
theorem matrixHochschildHomotopyStep_apply {M : Type*} [AddCommMonoid M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n m : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M)
    (b : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r n m Φ b = ∑ p : Fin (m + 1) → ι,
      Φ (Fin.cons (Matrix.single (p 0) r 1) fun k : Fin (n + 1) =>
        if hk : (k : ℕ) < m then Matrix.single r r
          (b k (p ⟨k, Nat.lt_succ_of_lt hk⟩) (p ⟨(k : ℕ) + 1, Nat.succ_lt_succ hk⟩))
        else if (k : ℕ) = m then Matrix.single r (p (Fin.last m)) 1 * b k else b k) := by
  rw [matrixHochschildHomotopyStep_apply_coord]
  refine Finset.sum_congr rfl fun p _ => congrArg Φ (funext (Fin.cases rfl fun k => ?_))
  simp only [Fin.cons_succ]; split_ifs with hk hkm
  · exact homotopyCoordLinearMap_of_lt r hk p (b k)
  · subst hkm; exact homotopyCoordLinearMap_same r k p (b k)
  · exact homotopyCoordLinearMap_of_gt r (by omega) p (b k)

private theorem matrixHochschildHomotopyStep_zero_hochschildCoface_zero (r : ι) (n : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    matrixHochschildHomotopyStep r n 0 (hochschildCoface R (Matrix ι ι A) M 0 Ψ) = Ψ := by
  ext b; rw [matrixHochschildHomotopyStep_apply_coord]
  simp only [hochschildCoface_apply]; rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  trans ∑ u : ι, Ψ (Function.update b 0 ((Matrix.single u r 1 * Matrix.single r u 1) * b 0))
  · refine Finset.sum_congr rfl fun u _ => congrArg Ψ ?_
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]; refine funext (Fin.cases ?_ fun k => ?_)
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
        homotopyCoordLinearMap_same, mul_assoc]; rfl
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (Nat.succ_pos k),
        Function.update_of_ne (Fin.succ_ne_zero k)]
      simp [homotopyCoordLinearMap_of_gt r (Nat.succ_pos k)]
  · simp_rw [← Ψ.map_update_sum, ← Finset.sum_mul, Matrix.single_mul_single_same, one_mul,
      Matrix.sum_single_one, one_mul, Function.update_eq_self]

private theorem cyclicOperator_matrixHochschildHomotopyStep_succ_hochschildCoface_zero (r : ι)
    {n m : ℕ} (hm : m < n)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    cyclicOperator R (Matrix ι ι A) M n
        (matrixHochschildHomotopyStep r n (m + 1) (hochschildCoface R (Matrix ι ι A) M 0 Ψ)) =
      (-1 : ℤ) ^ n • matrixHochschildHomotopyStep r n m
        (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1)) Ψ) := by
  ext d; simp only [cyclicOperator_apply, smul_apply]; congr 1
  rw [matrixHochschildHomotopyStep_apply_coord, matrixHochschildHomotopyStep_apply_coord]
  simp only [hochschildCoface_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => ι)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  set c : Fin (n + 1) → Matrix ι ι A := d ∘ (finRotate (n + 1)).symm
  let base : Fin (n + 1) → Matrix ι ι A :=
    Fin.cons (c 0 * Matrix.single (q 0) r 1) fun k : Fin n =>
      homotopyCoordLinearMap (R := R) r q k (c k.succ)
  trans ∑ u : ι, Ψ (Function.update base 0 (Matrix.single u r 1 * Matrix.single r r (c 0 u (q 0))))
  · refine Finset.sum_congr rfl fun u _ => congrArg Ψ ?_
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]; refine funext (Fin.cases ?_ fun k => ?_)
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self]
      simp only [Fin.consEquiv_apply, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
        Fin.val_zero, homotopyCoordLinearMap_of_lt r (Nat.zero_lt_succ m)]; rfl
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (Nat.succ_pos k),
        Function.update_of_ne (Fin.succ_ne_zero k)]
      simp only [Fin.consEquiv_apply, Fin.cons_succ, Fin.val_succ, base]
      exact homotopyCoordLinearMap_cons_succ r u q k (c k.succ)
  · have hsum : ∑ u : ι, Matrix.single u r (1 : A) * Matrix.single r r (c 0 u (q 0)) =
        c 0 * Matrix.single (q 0) r 1 := by
      have hmul (u : ι) : Matrix.single r r (c 0 u (q 0)) =
          Matrix.single r u (1 : A) * c 0 * Matrix.single (q 0) r (1 : A) := by simp
      simp_rw [hmul, ← mul_assoc, ← Finset.sum_mul, Matrix.single_mul_single_same, one_mul,
        Matrix.sum_single_one, one_mul]
    rw [← Ψ.map_update_sum, hsum, Function.update_eq_self_iff.2 (Fin.cons_zero _ _).symm]; congr 1
    rw [hochschildFace_last]; dsimp only [c, Function.comp_apply]
    refine funext (Fin.cases ?_ fun k => ?_)
    · rw [Fin.cons_zero, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, Fin.cons_zero,
        Fin.val_last, homotopyCoordLinearMap_of_gt r hm, congrArg d Fin.finRotate_symm_zero]
    · rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.val_castSucc,
        congrArg d (Fin.finRotate_symm_succ k)]

private theorem matrixHochschildHomotopyStep_self_hochschildCoface_last (r : ι) (n : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M) :
    matrixHochschildHomotopyStep r n n (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 1)) Ψ) =
      (-1 : ℤ) ^ n • cyclicOperator R (Matrix ι ι A) M n
        (matrixCochainExtension ι n (matrixCornerRestriction r n Ψ)) := by
  ext d; simp only [smul_apply, cyclicOperator_apply, smul_smul]
  rw [← pow_add, ← two_mul n, pow_mul, neg_one_sq, one_pow, one_smul,
    matrixHochschildHomotopyStep_apply_coord, matrixCochainExtension_apply]
  simp only [hochschildCoface_apply, matrixCornerRestriction_apply]
  conv_rhs => rw [← (Equiv.arrowCongr (finRotate (n + 1)) (Equiv.refl ι)).sum_comp]
  refine Finset.sum_congr rfl fun p _ => congrArg Ψ ?_
  rw [hochschildFace_last]; refine funext (Fin.cases ?_ fun k => ?_)
  · simp only [Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, Fin.val_last,
      homotopyCoordLinearMap_same, Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply,
      Fin.finRotate_symm_zero, Equiv.symm_apply_apply]
    rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl,
      Matrix.single_mul_mul_single, one_mul, mul_one]
  · simp only [Fin.cons_succ, Fin.val_castSucc, Equiv.arrowCongr_apply, Equiv.refl_apply,
      Function.comp_apply, Fin.finRotate_symm_succ, Equiv.symm_apply_apply]
    rw [homotopyCoordLinearMap_of_lt r k.isLt]; rfl

private theorem matrixHochschildHomotopyStep_succ_hochschildCoface_succ_of_le (r : ι) {k m' : ℕ}
    (i : Fin (k + 1)) (hi : (i : ℕ) ≤ m')
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopyStep r (k + 1) (m' + 1)
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) =
      hochschildCoface R (Matrix ι ι A) M i.castSucc (matrixHochschildHomotopyStep r k m' Ψ) := by
  ext b; rw [matrixHochschildHomotopyStep_apply_coord, hochschildCoface_apply,
    matrixHochschildHomotopyStep_apply_coord]; simp only [hochschildCoface_apply]
  let idx : Fin (m' + 2) := ⟨(i : ℕ) + 1, by omega⟩
  rw [← (Fin.insertNthEquiv (fun _ : Fin (m' + 2) => ι) idx).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  let target : Fin (k + 2) → Matrix ι ι A := Fin.cons (Matrix.single (q 0) r 1)
    fun j : Fin (k + 1) => homotopyCoordLinearMap (R := R) r q j (hochschildFace i.castSucc b j)
  let term (u : ι) : Matrix ι ι A :=
    homotopyCoordLinearMap (R := R) r (Fin.insertNth idx u q) i (b i.castSucc) *
      homotopyCoordLinearMap (R := R) r (Fin.insertNth idx u q) ((i : ℕ) + 1) (b i.succ)
  trans ∑ u : ι, Ψ (Function.update target i.succ (term u))
  · refine Finset.sum_congr rfl fun u _ => congrArg Ψ ?_
    simp only [Fin.insertNthEquiv_apply]; rw [hochschildFace_succ_castSucc_cons]
    refine funext (Fin.cases ?_ fun j => ?_)
    · rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      dsimp only [target, idx]; rw [Fin.cons_zero, Fin.cons_zero]
      exact congrArg (fun x => Matrix.single x r 1)
        (insertNth_succ_apply_of_le hi u q (Nat.zero_le (i : ℕ)) (Nat.zero_lt_succ (m' + 1)))
    · simp only [Fin.cons_succ]
      rcases lt_trichotomy (j : ℕ) (i : ℕ) with hlt | heq | hgt
      · rw [Function.update_of_ne ((Fin.succ_injective _).ne (Fin.ne_of_lt hlt))]
        dsimp only [target, idx]; simp only [Fin.cons_succ, hochschildFace_castSucc]
        rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt, Fin.contractNth_apply_of_lt _ _ _ _ hlt,
          Fin.val_castSucc, homotopyCoordLinearMap_insertNth_of_lt r u hi hlt]
      · obtain rfl : j = i := Fin.ext heq
        rw [Function.update_self, hochschildFace_castSucc, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
        rfl
      · rw [Function.update_of_ne ((Fin.succ_injective _).ne (Fin.ne_of_gt hgt))]
        dsimp only [target, idx]; simp only [Fin.cons_succ, hochschildFace_castSucc]
        rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt, Fin.contractNth_apply_of_gt _ _ _ _ hgt,
          Fin.val_succ, homotopyCoordLinearMap_insertNth_succ_of_gt r u hi hgt]
  · have hsum : ∑ u : ι, term u = target i.succ := by
      dsimp only [target, term, idx]
      rw [Fin.cons_succ, hochschildFace_castSucc, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
      exact sum_homotopyCoordLinearMap_insertNth_mul r hi q (b i.castSucc) (b i.succ)
    rw [← Ψ.map_update_sum, hsum, Function.update_eq_self]

private theorem matrixHochschildHomotopyStep_hochschildCoface_succ_of_le (r : ι) {k m : ℕ}
    (i : Fin (k + 1)) (hm : m ≤ (i : ℕ))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopyStep r (k + 1) m
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) =
      hochschildCoface R (Matrix ι ι A) M i.castSucc (matrixHochschildHomotopyStep r k m Ψ) := by
  ext b; rw [matrixHochschildHomotopyStep_apply_coord, hochschildCoface_apply,
    matrixHochschildHomotopyStep_apply_coord]; simp only [hochschildCoface_apply]
  refine Finset.sum_congr rfl fun p _ => congrArg Ψ ?_
  rw [hochschildFace_succ_castSucc_cons]; congr 1; funext j; simp only [hochschildFace_castSucc]
  rcases lt_trichotomy (j : ℕ) (i : ℕ) with hlt | heq | hgt
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt, Fin.contractNth_apply_of_lt _ _ _ _ hlt,
      Fin.val_castSucc]
  · obtain rfl : j = i := Fin.ext heq
    rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.contractNth_apply_of_eq _ _ _ _ rfl,
      Fin.val_castSucc, Fin.val_succ, homotopyCoordLinearMap_of_gt r (k := (j : ℕ) + 1) (by omega)]
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [homotopyCoordLinearMap_same, homotopyCoordLinearMap_same, mul_assoc]
    · rw [homotopyCoordLinearMap_of_gt r hlt, homotopyCoordLinearMap_of_gt r hlt]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt, Fin.contractNth_apply_of_gt _ _ _ _ hgt,
      Fin.val_succ, homotopyCoordLinearMap_of_gt r (by omega),
      homotopyCoordLinearMap_of_gt r (by omega)]

/-- The explicit Hochschild cochain homotopy `hₙ = ∑_{m = 0}^n λₙ^m ∘ S_{n, m}`. -/
noncomputable def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) => Matrix ι ι A) M :=
  ∑ m ∈ Finset.range (n + 1),
    (cyclicOperator R (Matrix ι ι A) M n ^ m) ∘ₗ matrixHochschildHomotopyStep r n m

omit [IsScalarTower R A A] in
/-- `matrixHochschildHomotopy r n` expands as `∑_{m = 0}^n λₙ^m ∘ S_{n, m}`. -/
theorem matrixHochschildHomotopy_def (r : ι) (n : ℕ) :
    matrixHochschildHomotopy (R := R) (A := A) (M := M) r n = ∑ m ∈ Finset.range (n + 1),
      (cyclicOperator R (Matrix ι ι A) M n ^ m) ∘ₗ matrixHochschildHomotopyStep r n m := (rfl)

omit [IsScalarTower R A A] in
/-- Evaluating `matrixHochschildHomotopy r n Φ` sums `(λₙ^m (S_{n, m} Φ)) b` for `0 ≤ m ≤ n`. -/
theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) => Matrix ι ι A) M)
    (b : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n Φ b = ∑ m ∈ Finset.range (n + 1),
      ((cyclicOperator R (Matrix ι ι A) M n ^ m) (matrixHochschildHomotopyStep r n m Φ)) b := by
  simp [matrixHochschildHomotopy_def, LinearMap.sum_apply]

/-- In degree zero, `h₀ (b₀ Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 Ψ) =
      Ψ - matrixCochainExtension ι 0 (matrixCornerRestriction r 0 Ψ) := by
  have hcob : hochschildCoboundary R (Matrix ι ι A) M 0 Ψ =
      hochschildCoface R (Matrix ι ι A) M 0 Ψ -
        hochschildCoface R (Matrix ι ι A) M (Fin.last 1) Ψ := by
    ext a; rw [hochschildCoboundary_apply, Fin.sum_univ_two]; simp [Fin.last, sub_eq_add_neg]
  have hlam : cyclicOperator R (Matrix ι ι A) M 0 = 1 := by
    simpa only [zero_add, pow_one] using
      cyclicOperator_pow_eq_one (R := R) (A := Matrix ι ι A) (M := M) 0
  rw [matrixHochschildHomotopy_def, Finset.range_one, Finset.sum_singleton, pow_zero, hcob, map_sub,
    LinearMap.comp_apply, LinearMap.comp_apply, _root_.one_apply_eq_self, _root_.one_apply_eq_self,
    matrixHochschildHomotopyStep_zero_hochschildCoface_zero,
    matrixHochschildHomotopyStep_self_hochschildCoface_last, pow_zero, one_smul, hlam,
    _root_.one_apply_eq_self]

/-- Every Hochschild `0`-cocycle on `Matrix ι ι A` is the extension of its corner restriction. -/
theorem matrixCochainExtension_matrixCornerRestriction_of_mem_hochschildCocycles_zero (r : ι)
    {Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 => Matrix ι ι A) M}
    (hΨ : Ψ ∈ hochschildCocycles R (Matrix ι ι A) M 0) :
    matrixCochainExtension ι 0 (matrixCornerRestriction r 0 Ψ) = Ψ := by
  have h := matrixHochschildHomotopy_hochschildCoboundary_zero r Ψ
  rw [mem_hochschildCocycles_iff.1 hΨ, map_zero, eq_comm, sub_eq_zero] at h; exact h.symm

private theorem matrixHochschildHomotopy_hochschildCoface_zero (r : ι) (k : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1) (hochschildCoface R (Matrix ι ι A) M 0 Ψ) =
      Ψ + ∑ m ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + 1) •
        (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m) (matrixHochschildHomotopyStep r (k + 1) m
          (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ)) := by
  rw [matrixHochschildHomotopy_def, LinearMap.sum_apply, Finset.sum_range_succ', pow_zero,
    LinearMap.comp_apply, _root_.one_apply_eq_self,
    matrixHochschildHomotopyStep_zero_hochschildCoface_zero, add_comm _ Ψ, add_right_inj]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [LinearMap.comp_apply, pow_succ _ m, _root_.mul_apply_eq_comp,
    cyclicOperator_matrixHochschildHomotopyStep_succ_hochschildCoface_zero r
      (Finset.mem_range.1 hm), map_zsmul]

private theorem matrixHochschildHomotopy_zsmul_hochschildCoface_last (r : ι) (k : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1)
        ((-1 : ℤ) ^ (k + 2) • hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ) =
      -(∑ m ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + 1) •
          (cyclicOperator R (Matrix ι ι A) M (k + 1) ^ m) (matrixHochschildHomotopyStep r (k + 1) m
            (hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ))) -
        matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ) := by
  rw [map_zsmul, matrixHochschildHomotopy_def, LinearMap.sum_apply, Finset.sum_range_succ,
    smul_add, sub_eq_add_neg]; congr 1
  · rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by
      rw [LinearMap.comp_apply, pow_succ (-1 : ℤ), mul_neg_one, neg_smul]
  · rw [LinearMap.comp_apply, matrixHochschildHomotopyStep_self_hochschildCoface_last, map_zsmul,
      ← _root_.mul_apply_eq_comp, ← pow_succ, cyclicOperator_pow_eq_one, _root_.one_apply_eq_self,
      smul_smul, ← pow_add, show k + 2 + (k + 1) = 2 * (k + 1) + 1 by omega, pow_succ, pow_mul,
      neg_one_sq, one_pow, one_mul, neg_one_smul]

private theorem matrixHochschildHomotopy_sum_hochschildCoface_succ_add_hochschildCoboundary
    (r : ι) (k : ℕ) (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1) (∑ i : Fin (k + 1),
        (-1 : ℤ) ^ ((i : ℕ) + 1) • hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) +
      hochschildCoboundary R (Matrix ι ι A) M k (matrixHochschildHomotopy r k Ψ) = 0 := by
  let L := cyclicOperator R (Matrix ι ι A) M (k + 1)
  have hsplit (m : ℕ) :
      (((L ^ m) ∘ₗ matrixHochschildHomotopyStep r (k + 1) m) (∑ x : Fin (k + 1),
          (-1 : ℤ) ^ ((x : ℕ) + 1) • hochschildCoface R (Matrix ι ι A) M x.succ.castSucc Ψ)) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => m ≤ (i : ℕ)), (-1 : ℤ) ^ ((i : ℕ) + 1) •
            (L ^ m) (hochschildCoface R (Matrix ι ι A) M i.castSucc
              (matrixHochschildHomotopyStep r k m Ψ))) +
          ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) < m), (-1 : ℤ) ^ ((i : ℕ) + 1) •
            (L ^ m) (matrixHochschildHomotopyStep r (k + 1) m
              (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ)) := by
    rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (k + 1) => m ≤ (i : ℕ))]; congr 1
    · exact Finset.sum_congr rfl fun i hi => by
        rw [LinearMap.comp_apply, map_zsmul, map_zsmul,
          matrixHochschildHomotopyStep_hochschildCoface_succ_of_le r i (Finset.mem_filter.1 hi).2]
    · exact Finset.sum_congr (by ext i; simp [not_le]) fun _ _ => by
        rw [LinearMap.comp_apply, map_zsmul, map_zsmul]
  have hB (m : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) < m + 1), (-1 : ℤ) ^ ((i : ℕ) + 1) •
          (L ^ (m + 1)) (matrixHochschildHomotopyStep r (k + 1) (m + 1)
            (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ))) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) => (i : ℕ) ≤ m), (-1 : ℤ) ^ ((i : ℕ) + 1) •
          (L ^ (m + 1)) (hochschildCoface R (Matrix ι ι A) M i.castSucc
            (matrixHochschildHomotopyStep r k m Ψ)) :=
    Finset.sum_congr (by ext i; simp) fun i hi => by
      rw [matrixHochschildHomotopyStep_succ_hochschildCoface_succ_of_le r i
        (Finset.mem_filter.1 hi).2]
  rw [matrixHochschildHomotopy_def, LinearMap.sum_apply, matrixHochschildHomotopy_def,
    LinearMap.sum_apply, map_sum]
  dsimp only [L] at hsplit hB; simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ, show (Finset.univ.filter fun i : Fin (k + 1) => k + 1 ≤ (i : ℕ)) = ∅ by
      ext i; simp; omega, Finset.sum_empty, add_zero, Finset.sum_range_succ' _ (k + 1),
    show (Finset.univ.filter fun i : Fin (k + 1) => (i : ℕ) < 0) = ∅ by ext i; simp,
    Finset.sum_empty, add_zero, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [hB m, LinearMap.comp_apply]
  exact sum_filter_cyclicOperator_pow_hochschildCoface_add_hochschildCoboundary
    (Nat.le_of_lt_succ (Finset.mem_range.1 hm)) (matrixHochschildHomotopyStep r k m Ψ)

/-- In positive degree `k + 1`, `h_{k+1} (b_{k+1} Ψ) + b_k (h_k Ψ) = Ψ - (Ψ ∘ E_{rr})#Tr`. -/
theorem
  matrixHochschildHomotopy_hochschildCoboundary_add_hochschildCoboundary_matrixHochschildHomotopy
    (r : ι) (k : ℕ) (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) => Matrix ι ι A) M) :
    matrixHochschildHomotopy r (k + 1) (hochschildCoboundary R (Matrix ι ι A) M (k + 1) Ψ) +
        hochschildCoboundary R (Matrix ι ι A) M k (matrixHochschildHomotopy r k Ψ) =
      Ψ - matrixCochainExtension ι (k + 1) (matrixCornerRestriction r (k + 1) Ψ) := by
  have hcob : hochschildCoboundary R (Matrix ι ι A) M (k + 1) Ψ =
      (hochschildCoface R (Matrix ι ι A) M 0 Ψ + ∑ i : Fin (k + 1),
          (-1 : ℤ) ^ ((i : ℕ) + 1) • hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) +
        (-1 : ℤ) ^ (k + 2) • hochschildCoface R (Matrix ι ι A) M (Fin.last (k + 2)) Ψ := by
    ext a; rw [hochschildCoboundary_apply, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp [Fin.castSucc_zero]
  rw [hcob, map_add, map_add, matrixHochschildHomotopy_hochschildCoface_zero,
    matrixHochschildHomotopy_zsmul_hochschildCoface_last]
  conv_rhs => rw [← add_zero (_ - _),
    ← matrixHochschildHomotopy_sum_hochschildCoface_succ_add_hochschildCoboundary r k Ψ]
  abel

end Step

namespace hochschildCohomology

section NonUnital

variable {R A M ι : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [Fintype ι] {n : ℕ}

variable (M ι n) in
/-- Matrix extension on Hochschild cohomology induced by `matrixCochainExtension`. -/
noncomputable def matrixExtension :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ
      (matrixCochainExtension ι n).restrict fun _ => matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ => (mk_eq_zero_iff R (Matrix ι ι A) M n _).2
      (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends `[φ]` to `[φ#Tr]`. -/
@[simp]
theorem matrixExtension_mk (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) = mk R (Matrix ι ι A) M n
      ⟨matrixCochainExtension ι n φ, matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

variable (M n) in
/-- Diagonal corner restriction on Hochschild cohomology induced by `matrixCornerRestriction`. -/
noncomputable def cornerRestriction [DecidableEq ι] (r : ι) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCornerRestriction r n).restrict
      fun _ => matrixCornerRestriction_mem_hochschildCocycles r)
    fun _ hΦ => (mk_eq_zero_iff R A M n _).2
      (matrixCornerRestriction_mem_hochschildCoboundaries r hΦ)

/-- Corner restriction on Hochschild cohomology sends `[Φ]` to `[Φ ∘ E_{rr}]`. -/
@[simp]
theorem cornerRestriction_mk [DecidableEq ι] (r : ι) (Φ : hochschildCocycles R (Matrix ι ι A) M n) :
    cornerRestriction M n r (mk R (Matrix ι ι A) M n Φ) = mk R A M n
      ⟨matrixCornerRestriction r n Φ, matrixCornerRestriction_mem_hochschildCocycles r Φ.2⟩ :=
  desc_mk _ _ _ Φ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp]
theorem cornerRestriction_matrixExtension [DecidableEq ι] (r : ι)
    (c : hochschildCohomology R A M n) :
    cornerRestriction M n r (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c; simp

/-- Corner restriction composed with matrix extension is the identity on Hochschild cohomology. -/
@[simp]
theorem cornerRestriction_comp_matrixExtension [DecidableEq ι] (r : ι) :
    cornerRestriction (R := R) (A := A) M n r ∘ₗ matrixExtension M ι n = LinearMap.id :=
  LinearMap.ext (cornerRestriction_matrixExtension r)

/-- Matrix extension on Hochschild cohomology is injective for nonempty finite `ι`. -/
theorem matrixExtension_injective [Nonempty ι] :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  let ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (cornerRestriction_matrixExtension r)

end NonUnital

section Unital

variable {R A M ι : Type*} [CommRing R] [Semiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M] [Fintype ι] {n : ℕ}

/-- When `A` is unital, matrix extension is a left inverse to corner restriction on `HHⁿ`. -/
@[simp]
theorem matrixExtension_cornerRestriction [DecidableEq ι] (r : ι)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (cornerRestriction M n r c) = c := by
  obtain ⟨Φ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [cornerRestriction_mk, matrixExtension_mk, mk_eq_mk_iff]; dsimp only
  cases n with
  | zero =>
    have h := matrixCochainExtension_matrixCornerRestriction_of_mem_hochschildCocycles_zero r Φ.2
    rw [hochschildCoboundaries_zero, Submodule.mem_bot, h, sub_self]
  | succ k =>
    have h :=
    matrixHochschildHomotopy_hochschildCoboundary_add_hochschildCoboundary_matrixHochschildHomotopy
        r k Φ.1
    rw [mem_hochschildCocycles_iff.1 Φ.2, map_zero, zero_add] at h
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨-matrixHochschildHomotopy r k Φ.1, by rw [map_neg, h, neg_sub]⟩

/-- Matrix extension composed with corner restriction is the identity on `HHⁿ(Matrix ι ι A; M)`. -/
@[simp]
theorem matrixExtension_comp_cornerRestriction [DecidableEq ι] (r : ι) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ cornerRestriction M n r = LinearMap.id :=
  LinearMap.ext (matrixExtension_cornerRestriction r)

/-- Diagonal corner restriction on `HHⁿ` of a unital algebra is independent of `r : ι`. -/
theorem cornerRestriction_eq_cornerRestriction [DecidableEq ι] (r s : ι) :
    cornerRestriction (R := R) (A := A) M n r = cornerRestriction M n s :=
  LinearMap.ext fun c => by
    conv_lhs => rw [← matrixExtension_cornerRestriction s c, cornerRestriction_matrixExtension]

/-- **Matrix Morita invariance of Hochschild cohomology** over any commutative ring `R`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  let ⟨r⟩ := ‹Nonempty ι›
  exact ⟨Function.LeftInverse.injective (cornerRestriction_matrixExtension r),
    Function.RightInverse.surjective (matrixExtension_cornerRestriction r)⟩

/-- Diagonal corner restriction on Hochschild cohomology is bijective for a unital algebra. -/
theorem bijective_cornerRestriction [DecidableEq ι] (r : ι) (n : ℕ) :
    Function.Bijective (cornerRestriction (R := R) (A := A) M n r) :=
  ⟨Function.LeftInverse.injective (matrixExtension_cornerRestriction r),
    Function.RightInverse.surjective (cornerRestriction_matrixExtension r)⟩

variable (M ι n) in
/-- Matrix extension as a linear equivalence on Hochschild cohomology for unital `A`. -/
noncomputable def matrixExtensionEquiv [Nonempty ι] :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- Applying `matrixExtensionEquiv` agrees with `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply [Nonempty ι] (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c := (rfl)

/-- Converting `matrixExtensionEquiv` to a linear map recovers `matrixExtension`. -/
@[simp]
theorem toLinearMap_matrixExtensionEquiv [Nonempty ι] :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)

/-- The inverse of `matrixExtensionEquiv` agrees with restriction to any diagonal corner `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply [DecidableEq ι] [Nonempty ι] (r : ι)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = cornerRestriction M n r c := by
  apply (matrixExtensionEquiv M ι n).injective; simp

end Unital

end hochschildCohomology

end TauCeti
