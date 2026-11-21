/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Multilinear.Curry
public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import TauCeti.RingTheory.HochschildCohomology.Complex
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Matrix.Basis
import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For finite `ι`, `TauCeti.matrixCochainExtension` extends cochains on `A` to `Matrix ι ι A` with
left inverse `TauCeti.matrixCochainRestriction` along `x ↦ Matrix.single r r x`. For unital `A`,
McCarthy's homotopy `TauCeti.matrixHochschildHomotopy` on `TauCeti.matrixHomotopyTuple` contracts
`matrixCochainExtension ∘ matrixCochainRestriction` to the identity, yielding Morita equivalences
on `HHⁿ` for nonempty `ι`.

## Main definitions

* `TauCeti.matrixCochainRestriction`: `(r, r)` corner restriction of matrix cochains.
* `TauCeti.matrixHomotopyTuple`, `TauCeti.matrixHochschildHomotopy`: McCarthy's cochain homotopy.
* `TauCeti.hochschildCohomology.matrixExtension`, `TauCeti.hochschildCohomology.matrixRestriction`,
  `TauCeti.hochschildCohomology.matrixExtensionEquiv`: extension, restriction, and equivalence.

## Main results

* `TauCeti.matrixCochainRestriction_matrixCochainExtension`,
  `TauCeti.matrixCochainRestriction_hochschildCoboundary`: restriction is a left-inverse chain map.
* `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero`,
  `TauCeti.hochschildCoboundary_matrixHochschildHomotopy_add`: homotopy identities.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of `HHⁿ`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§1.2.4, 1.5.
* R. McCarthy, *Morita equivalence and cyclic homology*, C. R. Acad. Sci. Paris Sér. I Math. 307
  (1988), 211–215.
-/

public section

open scoped BigOperators

namespace TauCeti

/-! ### Restriction of matrix cochains to a diagonal corner -/

section Linear
variable {R A M ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- Restrict a degree-`n` cochain on `Matrix ι ι A` to `A` along `x ↦ Matrix.single r r x`. -/
def matrixCochainRestriction (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M :=
  { toFun φ := φ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
    map_add' _ _ := rfl, map_smul' _ _ := rfl }
private theorem matrixCochainRestriction_def (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r n φ = φ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r := rfl
/-- Pointwise evaluation of `matrixCochainRestriction` on the `(r, r)` diagonal corner. -/
@[simp] theorem matrixCochainRestriction_apply (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    matrixCochainRestriction r n φ x = φ fun j ↦ Matrix.single r r (x j) := (rfl)
/-- Restricting a matrix-extended cochain to any diagonal corner recovers the original cochain. -/
@[simp] theorem matrixCochainRestriction_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainRestriction r n (matrixCochainExtension ι n φ) = φ := by ext; simp
/-- Corner restriction composed with matrix cochain extension is the identity linear map. -/
@[simp] theorem matrixCochainRestriction_comp_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ) :
    (matrixCochainRestriction (R := R) (A := A) (M := M) r n).comp (matrixCochainExtension ι n) =
      LinearMap.id := LinearMap.ext (matrixCochainRestriction_matrixCochainExtension r n)
end Linear

section RestrictionCoboundary
variable {R A M ι : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Fintype ι] [DecidableEq ι]

/-- Corner restriction commutes with every Hochschild coface. -/
theorem matrixCochainRestriction_hochschildCoface [AddCommMonoid M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n : ℕ) (i : Fin (n + 2))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i φ) =
      hochschildCoface R A M i (matrixCochainRestriction r n φ) := by
  simpa only [matrixCochainRestriction_def, Matrix.singleNonUnitalAlgHom_toLinearMap] using
    (hochschildCoface_compLinearMap (Matrix.singleNonUnitalAlgHom R (A := A) r) i φ).symm
/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCochainRestriction_hochschildCoboundary [AddCommGroup M] [Module R M]
    [SMulCommClass R R M] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n φ) =
      hochschildCoboundary R A M n (matrixCochainRestriction r n φ) := by
  simpa only [matrixCochainRestriction_def, Matrix.singleNonUnitalAlgHom_toLinearMap] using
    (hochschildCoboundary_compLinearMap (Matrix.singleNonUnitalAlgHom R (A := A) r) φ).symm
end RestrictionCoboundary

/-! ### Cochain homotopy for matrix Hochschild cochains -/

section Tuple
variable {A ι : Type*} [AddCommMonoid A] [Mul A] [One A] [Fintype ι] [DecidableEq ι]
  (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin ((k : ℕ) + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A)

/-- Modified `(n + 2)`-tuple for the `k`-th summand of `matrixHochschildHomotopy` along `p`. -/
def matrixHomotopyTuple : Fin (n + 2) → Matrix ι ι A :=
  Fin.cons (a 0 * Matrix.single (p 0) r (1 : A)) fun j : Fin (n + 1) ↦
    if hj : j < k then
      Matrix.single r r (a ⟨(j : ℕ) + 1, by have := k.isLt; omega⟩ (p ⟨j, Nat.lt_succ_of_lt hj⟩)
        (p ⟨(j : ℕ) + 1, Nat.add_lt_add_right hj 1⟩))
    else if j = k then Matrix.single r (p (Fin.last k)) (1 : A) else a j
/-- Entry `0` of `matrixHomotopyTuple` right-multiplies `a 0` by `Matrix.single (p 0) r 1`. -/
@[simp] theorem matrixHomotopyTuple_zero :
    matrixHomotopyTuple r k p a 0 = a 0 * Matrix.single (p 0) r (1 : A) := (rfl)
/-- For `j < k`, entry `j + 1` places `a (j + 1) (p j) (p (j + 1))` in the `(r, r)` corner. -/
@[simp] theorem matrixHomotopyTuple_succ_of_lt {j : Fin (n + 1)} (hj : j < k) :
    matrixHomotopyTuple r k p a j.succ =
      Matrix.single r r (a ⟨(j : ℕ) + 1, by have := k.isLt; omega⟩ (p ⟨j, Nat.lt_succ_of_lt hj⟩)
        (p ⟨(j : ℕ) + 1, Nat.add_lt_add_right hj 1⟩)) := by simp [matrixHomotopyTuple, hj]
/-- Entry `k + 1` of `matrixHomotopyTuple` is the unit matrix unit `E_{r, pₖ}`. -/
@[simp] theorem matrixHomotopyTuple_succ_self :
    matrixHomotopyTuple r k p a k.succ = Matrix.single r (p (Fin.last k)) (1 : A) := by
  simp [matrixHomotopyTuple]
/-- For `k < j`, entry `j + 1` of `matrixHomotopyTuple` leaves `a j` unchanged. -/
@[simp] theorem matrixHomotopyTuple_succ_of_gt {j : Fin (n + 1)} (hj : k < j) :
    matrixHomotopyTuple r k p a j.succ = a j := by simp [matrixHomotopyTuple, hj.not_gt, hj.ne']
end Tuple

section Definition
private def matrixHomotopyArgLinearMap {R A ι : Type*} [Semiring R] [AddCommMonoid A]
    [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ} (k : Fin (n + 1))
    (p : Fin (k + 1) → ι) (s : Fin (n + 1)) : Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if (s : ℕ) = 0 then ∑ u : ι, Matrix.singleLinearMap R u r ∘ₗ Matrix.entryLinearMap R A u (p 0)
  else if hs : (s : ℕ) < (k : ℕ) + 1 then
    Matrix.singleLinearMap R r r ∘ₗ Matrix.entryLinearMap R A (p ⟨s - 1, by omega⟩) (p ⟨s, hs⟩)
  else LinearMap.id

variable (R A M : Type*) {ι : Type*} [Semiring R] [AddCommMonoid A] [One A] [Module R A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

/-- McCarthy's explicit Hochschild cochain homotopy contracting `Matrix ι ι A` onto `(r, r)`. -/
def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ∑ p : Fin (k + 1) → ι,
    { toFun φ := (MultilinearMap.compInsertNthLinearMap R
        (M := fun _ : Fin (n + 2) ↦ Matrix ι ι A) k.succ
        (Matrix.single r (p (Fin.last k)) (1 : A)) φ).compLinearMap
        (matrixHomotopyArgLinearMap r k p)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
end Definition

/-! ### Simplicial identities on `ℕ`-indexed homotopy tuples -/

private def extPath {ι : Type*} (r : ι) {m : ℕ} (p : Fin m → ι) (t : ℕ) : ι :=
  if ht : t < m then p ⟨t, ht⟩ else r
private def natInsertIdx {α : Type*} (i : ℕ) (u : α) (q : ℕ → α) (t : ℕ) : α :=
  if t < i then q t else if t = i then u else q (t - 1)
private def extTuple {B : Type*} [Zero B] {m : ℕ} (a : Fin m → B) (t : ℕ) : B :=
  if ht : t < m then a ⟨t, ht⟩ else 0
private def natContractMul {B : Type*} [Mul B] (i : ℕ) (b : ℕ → B) (t : ℕ) : B :=
  if t < i then b t else if t = i then b t * b (t + 1) else b (t + 1)
private theorem extPath_insertNth_eq_natInsertIdx {ι : Type*} (r : ι) {k : ℕ} (j : Fin (k + 2))
    (u : ι) (q : Fin (k + 1) → ι) (t : ℕ) (ht : t < k + 2) :
    extPath r (j.insertNth (α := fun _ ↦ ι) u q) t = natInsertIdx j u (extPath r q) t := by
  simp only [extPath, ht, ↓reduceDIte, natInsertIdx]
  rcases lt_trichotomy (⟨t, ht⟩ : Fin (k + 2)) j with hlt | heq | hgt
  · have hlt' : t < j := hlt
    rw [← Fin.succAbove_castPred_of_lt j ⟨t, ht⟩ hlt, Fin.insertNth_apply_succAbove]
    simp [hlt', show t < k + 1 by omega]
  · obtain rfl : t = j := congrArg Fin.val heq; simp [Fin.insertNth_apply_same]
  · have : (j : ℕ) < t := hgt
    rw [← Fin.succAbove_pred_of_lt j ⟨t, ht⟩ hgt, Fin.insertNth_apply_succAbove]
    simp only [show ¬t < j by omega, show t ≠ j by omega, show t - 1 < k + 1 by omega, ↓reduceIte,
      ↓reduceDIte]; exact congrArg q (Fin.ext rfl)
private theorem extTuple_comp_val {B : Type*} [Zero B] {m : ℕ} (a : Fin m → B) :
    (fun t : Fin m ↦ extTuple a t) = a
        := funext fun t ↦ by simp only [extTuple, t.isLt, ↓reduceDIte]
private theorem hochschildFace_castSucc_comp_val {B : Type*} [Mul B] {N : ℕ} (j : Fin (N + 1))
    (b : ℕ → B) : hochschildFace j.castSucc (fun t : Fin (N + 2) ↦ b t) =
      fun s : Fin (N + 1) ↦ natContractMul j b s :=
  funext fun _ ↦ by simp [hochschildFace_castSucc, Fin.contractNth, natContractMul]
private theorem hochschildFace_last_comp_val {B : Type*} [Mul B] {N : ℕ} (b : ℕ → B) :
    hochschildFace (Fin.last (N + 1)) (fun t : Fin (N + 2) ↦ b t) =
      fun s : Fin (N + 1) ↦ if (s : ℕ) = 0 then b (N + 1) * b 0 else b s :=
  funext fun s ↦ by rw [hochschildFace_last]; cases s using Fin.cases <;> simp

section NatIdentities
variable {A ι : Type*} [NonAssocSemiring A] [Fintype ι] [DecidableEq ι] (r : ι)

private def natHomotopyTuple (k : ℕ) (P : ℕ → ι) (b : ℕ → Matrix ι ι A) (s : ℕ) : Matrix ι ι A :=
  if s = 0 then b 0 * Matrix.single (P 0) r (1 : A)
  else if s < k + 1 then Matrix.single r r (b s (P (s - 1)) (P s))
  else if s = k + 1 then Matrix.single r (P k) (1 : A) else b (s - 1)
private theorem natHomotopyTuple_congr_path (k : ℕ) {P Q : ℕ → ι} (hPQ : ∀ t < k + 1, P t = Q t)
    (b : ℕ → Matrix ι ι A) : natHomotopyTuple r k P b = natHomotopyTuple r k Q b := by
  funext s; unfold natHomotopyTuple; split_ifs with h0 hk hk1
  · rw [hPQ 0 (Nat.zero_lt_succ _)]
  · rw [hPQ (s - 1) (by omega), hPQ s hk]
  · rw [hPQ k (Nat.lt_succ_self _)]
  · rfl
private theorem natLastFace_natHomotopyTuple_of_le {n k' : ℕ} (hk : k' ≤ n) (P : ℕ → ι)
    (b : ℕ → Matrix ι ι A) (s : ℕ) :
    (if s = 0 then natHomotopyTuple r k' P b (n + 2) * natHomotopyTuple r k' P b 0
      else natHomotopyTuple r k' P b s) =
      natHomotopyTuple r k' P (fun t ↦ if t = 0 then b (n + 1) * b 0 else b t) s := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp only [↓reduceIte, natHomotopyTuple, show ¬n + 2 = 0 by omega,
      show ¬n + 2 < k' + 1 by omega, show ¬n + 2 = k' + 1 by omega]
    exact Matrix.mul_mul_single_one (b (n + 1)) (b 0) (P 0) r
  · simp only [hs0, ↓reduceIte, natHomotopyTuple]; split_ifs <;> first | omega | rfl
private def natMatrixHomotopyTuple {n : ℕ} (k : ℕ) (p : Fin (k + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) (s : Fin (n + 2)) : Matrix ι ι A :=
  natHomotopyTuple r k (extPath r p) (extTuple a) s
private theorem matrixHomotopyTuple_eq_natMatrixHomotopyTuple {n : ℕ} (k : Fin (n + 1))
    (p : Fin ((k : ℕ) + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHomotopyTuple r k p a = natMatrixHomotopyTuple r k p a := by
  funext s; cases s using Fin.cases with
  | zero => simp [natMatrixHomotopyTuple, natHomotopyTuple, extPath, extTuple]
  | succ j =>
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · simp [(hlt : (j : ℕ) < k), natMatrixHomotopyTuple, natHomotopyTuple, extPath, extTuple,
        show (j : ℕ) < (k : ℕ) + 1 by omega, show (j : ℕ) + 1 < n + 1 by omega]
    · simp [natMatrixHomotopyTuple, natHomotopyTuple, extPath, Fin.last]
    · have : (k : ℕ) < j := hgt
      simp [hgt, show (j : ℕ) ≠ k by omega, natMatrixHomotopyTuple, natHomotopyTuple, extTuple,
        show ¬(j : ℕ) + 1 < (k : ℕ) + 1 by omega, j.isLt]
private theorem natMatrixHomotopyTuple_comp_val {N k : ℕ} (hkN : k ≤ N) (p : Fin (k + 1) → ι)
    (b : ℕ → Matrix ι ι A) : natMatrixHomotopyTuple r k p (fun t : Fin (N + 1) ↦ b t) =
      fun s : Fin (N + 2) ↦ natHomotopyTuple r k (extPath r p) b s := by
  funext s; have := s.isLt; unfold natMatrixHomotopyTuple natHomotopyTuple extTuple
  split_ifs <;> first | omega | rfl
end NatIdentities

section FaceIdentities
variable {R A M ι : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ}

private theorem sum_hochschildFace_natMatrixHomotopyTuple_of_le
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (m : Fin (n + 2)) (k' : Fin (n + 1)) (hmk : (m : ℕ) ≤ k') :
    ∑ p : Fin ((k' : ℕ) + 2) → ι,
        φ (hochschildFace m.castSucc (natMatrixHomotopyTuple r ((k' : ℕ) + 1) p a)) =
      ∑ q : Fin ((k' : ℕ) + 1) → ι, φ (natMatrixHomotopyTuple r k' q (hochschildFace m a)) := by
  have := k'.isLt; let j : Fin ((k' : ℕ) + 2) := ⟨m, by omega⟩
  let m₀ : Fin (n + 1) := ⟨m, by omega⟩
  have hm_eq : m = m₀.castSucc := Fin.ext (Fin.val_castSucc m₀).symm
  let b := extTuple a; have ha : a = fun t : Fin (n + 2) ↦ b t := (extTuple_comp_val a).symm
  rw [← (j.insertNthEquiv (fun _ : Fin ((k' : ℕ) + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hupd (u : ι) : hochschildFace m.castSucc
      (natMatrixHomotopyTuple r ((k' : ℕ) + 1) (j.insertNth (α := fun _ ↦ ι) u q) a) =
      Function.update (natMatrixHomotopyTuple r k' q (hochschildFace m a)) m
        (if (m : ℕ) = 0 then
          b 0 * Matrix.single u r (1 : A) * Matrix.single r r (b 1 u (extPath r q 0))
        else Matrix.single r r (b m (extPath r q (m - 1)) u) *
          Matrix.single r r (b (m + 1) u (extPath r q m))) := by
    rw [ha, natMatrixHomotopyTuple_comp_val r (by omega) _ b, hochschildFace_castSucc_comp_val,
      hm_eq, hochschildFace_castSucc_comp_val, natMatrixHomotopyTuple_comp_val r (by omega) q,
      natHomotopyTuple_congr_path r ((k' : ℕ) + 1) (extPath_insertNth_eq_natInsertIdx r j u q) b]
    funext s; rcases eq_or_ne s m₀.castSucc with rfl | hne
    · rw [Function.update_self, Fin.val_castSucc]
      rcases eq_or_ne (m : ℕ) 0 with hm0 | hm0 <;>
        simp only [hm0, m₀, j, natContractMul, natHomotopyTuple, natInsertIdx, Nat.add_eq_zero_iff,
          one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] <;>
        split_ifs <;> first | omega | rfl
    · rw [Function.update_of_ne hne]; rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hsm | hms
      · simp only [m₀, j, natContractMul, hsm, ↓reduceIte, natHomotopyTuple, natInsertIdx,
          show (s : ℕ) < (k' : ℕ) + 1 by omega, show (s : ℕ) < (k' : ℕ) + 1 + 1 by omega]
        split_ifs <;> first | omega | rfl
      · simp only [Fin.val_castSucc, m₀, j, natContractMul, natHomotopyTuple, natInsertIdx,
          show ¬(s : ℕ) < m by omega, show (s : ℕ) ≠ m by omega, show (s : ℕ) ≠ 0 by omega,
          show (s : ℕ) + 1 ≠ 0 by omega, show ¬(s : ℕ) + 1 < m by omega,
          show (s : ℕ) + 1 ≠ m by omega, ↓reduceIte, Nat.add_sub_cancel]
        split_ifs <;> first | omega | rfl | (congr 1; omega)
  simp_rw [Fin.insertNthEquiv_apply, hupd, ← φ.map_update_sum]
  congr 1; rw [Function.update_eq_self_iff, ha, hm_eq, hochschildFace_castSucc_comp_val,
    natMatrixHomotopyTuple_comp_val r (by omega) q]
  by_cases hm0 : (m : ℕ) = 0
  · simp [hm0, m₀, Matrix.sum_mul_single_one_mul_single, natHomotopyTuple, natContractMul]
  · simp only [Fin.val_castSucc, m₀, hm0, ↓reduceIte]; rw [Matrix.sum_single_mul_single]
    simp [hm0, natHomotopyTuple, natContractMul, show (m : ℕ) < (k' : ℕ) + 1 by omega]

omit [Semiring R] [Module R A] [AddCommMonoid M] [Module R M] in
private theorem hochschildFace_succ_natMatrixHomotopyTuple_of_lt (a : Fin (n + 2) → Matrix ι ι A)
    (m : Fin (n + 2)) (k' : Fin (n + 1)) (hkm : (k' : ℕ) < m) (p : Fin ((k' : ℕ) + 1) → ι) :
    hochschildFace m.succ (natMatrixHomotopyTuple r k' p a) =
      natMatrixHomotopyTuple r k' p (hochschildFace m a) := by
  have := k'.isLt; let b := extTuple a
  have ha : a = fun t : Fin (n + 2) ↦ b t := (extTuple_comp_val a).symm
  rw [ha, natMatrixHomotopyTuple_comp_val r (by omega) p b]
  induction m using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildFace_last_comp_val, hochschildFace_last_comp_val,
      natMatrixHomotopyTuple_comp_val r (Nat.le_of_lt_succ k'.isLt) p
        (fun t ↦ if t = 0 then b (n + 1) * b 0 else b t)]
    exact funext fun s ↦ natLastFace_natHomotopyTuple_of_le r (Nat.le_of_lt_succ k'.isLt) _ b s
  | cast m₀ =>
    have hkm' : (k' : ℕ) < m₀ := by simpa using hkm
    rw [Fin.succ_castSucc, hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
      natMatrixHomotopyTuple_comp_val r (by omega) p]
    funext s; simp only [Fin.val_succ, natContractMul, natHomotopyTuple, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    split_ifs <;> first | omega | rfl | (congr 1; omega) | (congr 2; omega)

private theorem sum_hochschildFace_diagonal_succ_eq_superdiagonal
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (j : Fin (n + 1)) :
    ∑ q : Fin ((j : ℕ) + 2) → ι,
        φ (hochschildFace j.succ.castSucc (natMatrixHomotopyTuple r ((j : ℕ) + 1) q a)) =
      ∑ p : Fin ((j : ℕ) + 1) → ι,
        φ (hochschildFace j.castSucc.succ (natMatrixHomotopyTuple r j p a)) := by
  have := j.isLt; let L : Fin ((j : ℕ) + 2) := Fin.last ((j : ℕ) + 1); let b := extTuple a
  have ha : a = fun t : Fin (n + 2) ↦ b t := (extTuple_comp_val a).symm
  rw [← (L.insertNthEquiv (fun _ : Fin ((j : ℕ) + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hupd (v : ι) : hochschildFace j.succ.castSucc
      (natMatrixHomotopyTuple r ((j : ℕ) + 1) (L.insertNth (α := fun _ ↦ ι) v p) a) =
      Function.update (hochschildFace j.castSucc.succ (natMatrixHomotopyTuple r j p a)) j.succ
        (Matrix.single r r (b ((j : ℕ) + 1) (extPath r p j) v) * Matrix.single r v (1 : A)) := by
    rw [Fin.succ_castSucc, ha, natMatrixHomotopyTuple_comp_val r (by omega) _ b,
      natMatrixHomotopyTuple_comp_val r (by omega) p b, hochschildFace_castSucc_comp_val,
      hochschildFace_castSucc_comp_val,
      natHomotopyTuple_congr_path r ((j : ℕ) + 1) (extPath_insertNth_eq_natInsertIdx r L v p) b]
    funext s; by_cases hs : s = j.succ
    · subst hs; simp [L, natContractMul, natHomotopyTuple, natInsertIdx]
    · simp only [Function.update_of_ne hs, Fin.val_succ, L, Fin.val_last, natContractMul,
        natHomotopyTuple, natInsertIdx, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      have : (s : ℕ) ≠ (j : ℕ) + 1 := fun h ↦ hs (Fin.ext h)
      split_ifs <;> first | omega | rfl
  simp_rw [Fin.insertNthEquiv_apply, hupd, ← φ.map_update_sum, Matrix.sum_single_mul_single_one]
  congr 1; rw [Function.update_eq_self_iff, Fin.succ_castSucc, ha,
    natMatrixHomotopyTuple_comp_val r (by omega) p b, hochschildFace_castSucc_comp_val]
  simp only [Fin.val_succ, natContractMul, natHomotopyTuple, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel]; split_ifs <;> first | omega | rfl

private theorem sum_hochschildFace_zero_natMatrixHomotopyTuple_zero
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin 1 → ι, φ (hochschildFace 0 (natMatrixHomotopyTuple r 0 p a)) = φ a := by
  let b := extTuple a; have ha : a = fun t : Fin (n + 1) ↦ b t := (extTuple_comp_val a).symm
  have heq := Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι)
    (fun p : Fin 1 → ι ↦ φ (hochschildFace 0 (natMatrixHomotopyTuple r 0 p a)))
    (fun u ↦ φ (Function.update a 0 (a 0 * Matrix.single u r (1 : A) * Matrix.single r u (1 : A))))
    fun p ↦ congrArg φ (by
      rw [← Fin.castSucc_zero, ha,
        natMatrixHomotopyTuple_comp_val r (Nat.zero_le _) p b, hochschildFace_castSucc_comp_val,
        Fin.val_zero, natHomotopyTuple_congr_path r 0 (Q := fun _ ↦ p 0)
          (fun t ht ↦ by obtain rfl : t = 0 := (by omega); simp [extPath]) b]
      funext s; rcases eq_or_ne s 0 with rfl | hne
      · simp [natContractMul, natHomotopyTuple]
      · simp [natContractMul, natHomotopyTuple, hne])
  rw [heq, ← φ.map_update_sum, Matrix.sum_mul_single_one_mul_single_one, Function.update_eq_self]

private theorem sum_hochschildFace_last_natMatrixHomotopyTuple_last [SMulCommClass R R M]
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin (n + 1) → ι,
        φ (hochschildFace (Fin.last (n + 1)) (natMatrixHomotopyTuple r n p a)) =
      matrixCochainExtension ι n (matrixCochainRestriction r n φ) a := by
  simp only [matrixCochainExtension_apply, matrixCochainRestriction_apply]
  refine (Fintype.sum_equiv (Equiv.arrowCongr (finRotate (n + 1)).symm (Equiv.refl ι)) _ _
    fun p ↦ congrArg φ (funext fun s ↦ ?_)).symm
  rw [hochschildFace_last]; cases s using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, natMatrixHomotopyTuple, natHomotopyTuple, extPath, extTuple,
      Fin.val_last, Fin.val_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, lt_self_iff_false,
      ↓reduceIte, Nat.lt_succ_self, Nat.zero_lt_succ, ↓reduceDIte, Equiv.arrowCongr_apply,
      Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply, Matrix.single_one_mul_mul_single_one,
      Fin.mk_zero]
    rw [Fin.eq_last_of_not_lt (i := ⟨n, Nat.lt_succ_self n⟩) (lt_irrefl n), finRotate_last]
  | succ m =>
    simp only [Fin.cons_succ, natMatrixHomotopyTuple, natHomotopyTuple, extPath, extTuple,
      Fin.val_succ, Fin.val_castSucc, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_lt_add_iff_right, m.isLt, Nat.add_sub_cancel, Nat.lt_succ_of_lt m.isLt,
      Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply]
    exact congrArg (fun x ↦ Matrix.single r r (a m.succ (p x) (p (finRotate (n + 1) m.succ))))
      (Fin.finRotate_castSucc m).symm

private def homotopyFaceSum
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (k : Fin (n + 2)) (i : Fin (n + 3)) : M :=
  ∑ p : Fin ((k : ℕ) + 1) → ι, φ (hochschildFace i (natMatrixHomotopyTuple r k p a))
private def homotopyArgFaceSum
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (m : Fin (n + 2)) (k' : Fin (n + 1)) : M :=
  ∑ p : Fin ((k' : ℕ) + 1) → ι, φ (natMatrixHomotopyTuple r k' p (hochschildFace m a))
end FaceIdentities

variable {R A M ι : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Pointwise evaluation of `matrixHochschildHomotopy` as an alternating sum over `k` and `p`. -/
theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) : matrixHochschildHomotopy R A M r n φ a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin ((k : ℕ) + 1) → ι, φ (matrixHomotopyTuple r k p a) := by
  simp only [matrixHochschildHomotopy, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, sum_apply, smul_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.compInsertNthLinearMap_apply,
    MultilinearMap.compInsertNth_apply]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg _ (Finset.sum_congr rfl fun p _ ↦
    congrArg φ (funext fun s ↦ ?_))
  cases s using Fin.cases with
  | zero =>
    rw [Fin.insertNth_apply_below (Fin.succ_pos k)]
    simp [matrixHomotopyArgLinearMap, Matrix.sum_single_eq_mul_single_one]
  | succ j =>
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · rw [matrixHomotopyTuple_succ_of_lt r k p a hlt,
        Fin.insertNth_apply_below (Fin.succ_lt_succ_iff.2 hlt)]
      simp [matrixHomotopyArgLinearMap, Nat.add_lt_add_right (hlt : (j : ℕ) < k) 1]; rfl
    · simp
    · have : (k : ℕ) < j := hgt
      rw [matrixHomotopyTuple_succ_of_gt r k p a hgt,
        Fin.insertNth_apply_above (Fin.succ_lt_succ_iff.2 hgt)]
      simp [matrixHomotopyArgLinearMap, show (j : ℕ) ≠ 0 by omega,
        show ¬(j : ℕ) < (k : ℕ) + 1 by omega]

/-- **Degree-zero homotopy identity:** `h₀ (b₀ φ) = φ - (res_r φ)#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy R A M r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 φ) =
      φ - matrixCochainExtension ι 0 (matrixCochainRestriction r 0 φ) := by
  ext a; rw [matrixHochschildHomotopy_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, sub_apply, hochschildCoboundary_apply,
    Fin.sum_univ_castSucc, Fin.sum_univ_zero, Fin.val_castSucc, Fin.val_last, pow_one,
    neg_one_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib, zero_add,
    matrixHomotopyTuple_eq_natMatrixHomotopyTuple]
  rw [Fin.last_zero, Fin.castSucc_zero,
    sum_hochschildFace_zero_natMatrixHomotopyTuple_zero r φ a, ← sub_eq_add_neg,
    sum_hochschildFace_last_natMatrixHomotopyTuple_last r φ a]

/-- Every Hochschild `0`-cocycle on `Matrix ι ι A` is the generalized trace of its restriction. -/
theorem eq_matrixCochainExtension_matrixCochainRestriction_of_hochschildCoboundary_zero_eq_zero
    (r : ι) {φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M}
    (hφ : hochschildCoboundary R (Matrix ι ι A) M 0 φ = 0) :
    φ = matrixCochainExtension ι 0 (matrixCochainRestriction r 0 φ) := by
  have h := matrixHochschildHomotopy_hochschildCoboundary_zero r φ
  rwa [hφ, map_zero, eq_comm, sub_eq_zero] at h

/-- **Positive-degree Hochschild homotopy identity:**
`bₙ (hₙ φ) + hₙ₊₁ (bₙ₊₁ φ) = φ - (res_r φ)#Tr`. -/
theorem hochschildCoboundary_matrixHochschildHomotopy_add (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy R A M r n φ) +
        matrixHochschildHomotopy R A M r (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) φ) =
      φ - matrixCochainExtension ι (n + 1) (matrixCochainRestriction r (n + 1) φ) := by
  ext a
  have hLH1 : hochschildCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy R A M r n φ) a =
      ∑ x : Fin (n + 2) × Fin (n + 1),
        ((-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) • homotopyArgFaceSum r φ a x.1 x.2 := by
    simp only [hochschildCoboundary_apply, matrixHochschildHomotopy_apply,
      matrixHomotopyTuple_eq_natMatrixHomotopyTuple, Finset.smul_sum, smul_smul, ← pow_add,
      Fintype.sum_prod_type, homotopyArgFaceSum]
  have hLH2 : matrixHochschildHomotopy R A M r (n + 1)
      (hochschildCoboundary R (Matrix ι ι A) M (n + 1) φ) a = ∑ y : Fin (n + 2) × Fin (n + 3),
        ((-1 : ℤ) ^ ((y.1 : ℕ) + (y.2 : ℕ))) • homotopyFaceSum r φ a y.1 y.2 := by
    rw [matrixHochschildHomotopy_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [hochschildCoboundary_apply, matrixHomotopyTuple_eq_natMatrixHomotopyTuple,
      Finset.smul_sum, smul_smul, ← pow_add, homotopyFaceSum]; rw [Finset.sum_comm]
  have hinl (x : Fin (n + 2) × Fin (n + 1)) :
      let y := homotopyIndexEquiv (n + 1) (.inl x)
      ((-1 : ℤ) ^ ((y.1 : ℕ) + (y.2 : ℕ))) • homotopyFaceSum r φ a y.1 y.2 =
        -((-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) • homotopyArgFaceSum r φ a x.1 x.2) := by
    rcases x with ⟨m, k'⟩
    have hsign (e : ℕ) (he : e = (m : ℕ) + k' + 1) : (-1 : ℤ) ^ e = -((-1 : ℤ) ^ ((m : ℕ) + k')) :=
      by rw [he, pow_succ, mul_neg_one]
    by_cases hmk : (m : ℕ) ≤ (k' : ℕ)
    · simp only [homotopyIndexEquiv_inl, hmk, ↓reduceIte, Fin.val_succ, Fin.val_castSucc,
        hsign ((k' : ℕ) + 1 + m) (by omega), neg_smul]
      congr 2; exact sum_hochschildFace_natMatrixHomotopyTuple_of_le r φ a m k' hmk
    · simp only [homotopyIndexEquiv_inl, hmk, ↓reduceIte, Fin.val_succ, Fin.val_castSucc,
        hsign ((k' : ℕ) + ((m : ℕ) + 1)) (by omega), neg_smul]
      congr 2; exact Finset.sum_congr rfl fun p _ ↦
        congrArg φ (hochschildFace_succ_natMatrixHomotopyTuple_of_lt r a m k' (by omega) p)
  have hdiag (k : Fin (n + 2)) : ((-1 : ℤ) ^ ((k : ℕ) + (k.castSucc : ℕ))) •
      homotopyFaceSum r φ a k k.castSucc = homotopyFaceSum r φ a k k.castSucc := by
    rw [Fin.val_castSucc, ← two_mul, Even.neg_one_pow (even_two_mul _), one_smul]
  have hsuper (k : Fin (n + 2)) : ((-1 : ℤ) ^ ((k : ℕ) + (k.succ : ℕ))) •
      homotopyFaceSum r φ a k k.succ = -homotopyFaceSum r φ a k k.succ := by
    rw [Fin.val_succ, ← add_assoc, ← two_mul, Odd.neg_one_pow ⟨k, rfl⟩, neg_one_smul]
  simp only [add_apply, sub_apply, hLH1, hLH2, ← (homotopyIndexEquiv (n + 1)).sum_comp,
    Fintype.sum_sum_type, hinl, Finset.sum_neg_distrib, homotopyIndexEquiv_inr_inl,
    homotopyIndexEquiv_inr_inr, hdiag, hsuper]
  rw [add_neg_cancel_left,
    Fin.sum_univ_succ (fun k : Fin (n + 2) ↦ homotopyFaceSum r φ a k k.castSucc),
    Fin.sum_univ_castSucc (fun k : Fin (n + 2) ↦ homotopyFaceSum r φ a k k.succ),
    Fin.castSucc_zero, Fin.succ_last,
    show ∑ j : Fin (n + 1), homotopyFaceSum r φ a j.succ j.succ.castSucc =
        ∑ j : Fin (n + 1), homotopyFaceSum r φ a j.castSucc j.castSucc.succ from
      Finset.sum_congr rfl fun j _ ↦ sum_hochschildFace_diagonal_succ_eq_superdiagonal r φ a j,
    show homotopyFaceSum r φ a 0 0 = φ a from
      sum_hochschildFace_zero_natMatrixHomotopyTuple_zero r φ a,
    show homotopyFaceSum r φ a (Fin.last (n + 1)) (Fin.last (n + 2)) =
      matrixCochainExtension ι (n + 1) (matrixCochainRestriction r (n + 1) φ) a from
      sum_hochschildFace_last_natMatrixHomotopyTuple_last r φ a]; abel

/-! ### Hochschild cocycles, coboundaries, and cohomology -/

section NonUnital
variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] {n : ℕ}

/-- Matrix extension sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainExtension_mem_hochschildCocycles
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCocycles R (Matrix ι ι A) M n := by
  simpa [mem_hochschildCocycles_iff, ← matrixCochainExtension_hochschildCoboundary] using
    congrArg (matrixCochainExtension ι (n + 1)) (mem_hochschildCocycles_iff.1 hφ)
/-- Matrix extension sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainExtension_mem_hochschildCoboundaries
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M n) :
    matrixCochainExtension ι n φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero => simp_all [hochschildCoboundaries_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainExtension ι n ψ, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩
/-- Corner restriction sends Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainRestriction_mem_hochschildCocycles [DecidableEq ι] (r : ι)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCochainRestriction r n φ ∈ hochschildCocycles R A M n := by
  simpa only [matrixCochainRestriction_def, Matrix.singleNonUnitalAlgHom_toLinearMap] using
    compLinearMap_mem_hochschildCocycles (Matrix.singleNonUnitalAlgHom R (A := A) r) hφ
/-- Corner restriction sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCochainRestriction r n φ ∈ hochschildCoboundaries R A M n := by
  simpa only [matrixCochainRestriction_def, Matrix.singleNonUnitalAlgHom_toLinearMap] using
    compLinearMap_mem_hochschildCoboundaries (Matrix.singleNonUnitalAlgHom R (A := A) r) hφ
end NonUnital

/-- Every Hochschild cocycle on `Matrix ι ι A` is cohomologous to the trace of its restriction. -/
theorem sub_matrixCochainExtension_matrixCochainRestriction_mem_hochschildCoboundaries
    {R A M ι : Type*} [Semiring R] [Semiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι]
    [DecidableEq ι] (r : ι) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    φ - matrixCochainExtension ι n (matrixCochainRestriction r n φ) ∈
      hochschildCoboundaries R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ; cases n with
  | zero => simpa [hochschildCoboundaries_zero, sub_eq_zero] using
      eq_matrixCochainExtension_matrixCochainRestriction_of_hochschildCoboundary_zero_eq_zero r hφ
  | succ n =>
    refine mem_hochschildCoboundaries_succ_iff.2 ⟨matrixHochschildHomotopy R A M r n φ, ?_⟩
    simpa [hφ] using hochschildCoboundary_matrixHochschildHomotopy_add r n φ

namespace hochschildCohomology
section NonUnital
variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

variable (M ι) in
/-- `HHⁿ(A, Hom_R(A, M)) →ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` via matrix trace. -/
noncomputable def matrixExtension (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff R (Matrix ι ι A) M n _).2
      (matrixCochainExtension_mem_hochschildCoboundaries hφ)
/-- `matrixExtension` sends the class of a cocycle to the class of its matrix extension. -/
@[simp] theorem matrixExtension_mk {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ,
        matrixCochainExtension_mem_hochschildCocycles φ.property⟩ := desc_mk _ _ _ φ

variable (M) in
/-- `HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M)) →ₗ[R] HHⁿ(A, Hom_R(A, M))` via `(r, r)` corner. -/
noncomputable def matrixRestriction [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  map M (Matrix.singleNonUnitalAlgHom R (A := A) r) n
/-- `matrixRestriction` sends `[φ]` to the class of its `(r, r)` corner restriction. -/
@[simp] theorem matrixRestriction_mk [DecidableEq ι] (r : ι) {n : ℕ}
    (φ : hochschildCocycles R (Matrix ι ι A) M n) :
    matrixRestriction M r n (mk R (Matrix ι ι A) M n φ) =
      mk R A M n ⟨matrixCochainRestriction r n φ,
        matrixCochainRestriction_mem_hochschildCocycles r φ.property⟩ := by
  simp only [matrixRestriction, map_mk, matrixCochainRestriction_def,
    Matrix.singleNonUnitalAlgHom_toLinearMap]
/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp] theorem matrixRestriction_matrixExtension [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R A M n) : matrixRestriction M r n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c; simp
end NonUnital

section Unital
variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

/-- For unital `A`, matrix extension is a left inverse to corner restriction on `HHⁿ`. -/
@[simp] theorem matrixExtension_matrixRestriction [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (matrixRestriction M r n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [matrixRestriction_mk, matrixExtension_mk, eq_comm, mk_eq_mk_iff]
  exact sub_matrixCochainExtension_matrixCochainRestriction_mem_hochschildCoboundaries r φ.property

section Nonempty
variable [Nonempty ι]

variable (ι) in
/-- **Matrix Morita invariance of Hochschild cohomology** for unital `A` and nonempty `ι`. -/
theorem bijective_matrixExtension (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.bijective_iff_has_inverse.2 ⟨matrixRestriction M r n,
    matrixRestriction_matrixExtension r n, matrixExtension_matrixRestriction r n⟩
variable (M ι) in
/-- **Matrix Morita equivalence on Hochschild cohomology** for unital `A` and nonempty `ι`. -/
noncomputable def matrixExtensionEquiv (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)
/-- The underlying linear map of `matrixExtensionEquiv` is `matrixExtension`. -/
@[simp] theorem coe_matrixExtensionEquiv (n : ℕ) :
    (matrixExtensionEquiv (R := R) (A := A) M ι n :
      hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n) =
      matrixExtension M ι n := (rfl)
/-- `matrixExtensionEquiv` acts on Hochschild cohomology classes by `matrixExtension`. -/
@[simp] theorem matrixExtensionEquiv_apply (n : ℕ) (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c := (rfl)
/-- Applying `matrixExtension` to `(matrixExtensionEquiv M ι n).symm c` recovers `c`. -/
@[simp] theorem matrixExtension_matrixExtensionEquiv_symm (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n ((matrixExtensionEquiv M ι n).symm c) = c :=
  LinearEquiv.apply_symm_apply (matrixExtensionEquiv M ι n) c
/-- Applying `(matrixExtensionEquiv M ι n).symm` after `matrixExtension` recovers `c`. -/
@[simp] theorem matrixExtensionEquiv_symm_matrixExtension (n : ℕ)
    (c : hochschildCohomology R A M n) :
    (matrixExtensionEquiv M ι n).symm (matrixExtension M ι n c) = c :=
  LinearEquiv.symm_apply_apply (matrixExtensionEquiv M ι n) c
/-- The inverse of `matrixExtensionEquiv` acts by corner restriction along any `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = matrixRestriction M r n c :=
  (matrixExtensionEquiv M ι n).injective (by simp)
end Nonempty
end Unital
end hochschildCohomology

end TauCeti
