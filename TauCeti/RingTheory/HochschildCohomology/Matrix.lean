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

/-!
# Matrix Morita invariance of Hochschild cohomology

For a finite index type `ι` and an `R`-algebra `A`, generalized matrix trace
`TauCeti.matrixCochainExtension` extends `M`-valued cochains on `A` to `Matrix ι ι A` and commutes
with the Hochschild coboundary. Pulling cochains back along `x ↦ Matrix.single r r x` defines
`TauCeti.matrixCochainRestriction`, a cochain map left inverse to `matrixCochainExtension`.

When `A` is unital, `matrixCochainExtension ∘ matrixCochainRestriction` is chain homotopic to the
identity via McCarthy's explicit cochain homotopy `TauCeti.matrixHochschildHomotopy` on
`TauCeti.matrixHomotopyTuple`
`(a₀ E_{p₀, r}, E_{r, r}(a₁(p₀, p₁)), …, E_{r, r}(aₖ(pₖ₋₁, pₖ)), E_{r, pₖ}, aₖ₊₁, …, aₙ)`
with sign `(-1)ᵏ`, yielding `R`-linear Morita isomorphisms on `HHⁿ` when `ι` is nonempty.

## Main definitions

* `TauCeti.matrixCochainRestriction`: restriction of matrix cochains to a diagonal corner `(r, r)`.
* `TauCeti.matrixHomotopyTuple`, `TauCeti.matrixHochschildHomotopy`: McCarthy's cochain homotopy on
  matrix Hochschild cochains and its modified `(n + 2)`-tuple of matrix arguments.
* `TauCeti.hochschildCohomology.matrixExtension`, `TauCeti.hochschildCohomology.matrixRestriction`,
  `TauCeti.hochschildCohomology.matrixExtensionEquiv`: extension, corner restriction, and Morita
  `R`-linear equivalence on Hochschild cohomology.

## Main results

* `TauCeti.matrixCochainRestriction_matrixCochainExtension`,
  `TauCeti.matrixCochainRestriction_hochschildCoboundary`: corner restriction is a cochain map left
  inverse to matrix extension.
* `TauCeti.matrixHochschildHomotopy_apply`,
  `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero`,
  `TauCeti.hochschildCoboundary_matrixHochschildHomotopy_add`: path-sum formula and homotopy
  identities `h₀ (b₀ φ) = φ - (res_r φ)#Tr` and `bₙ (hₙ φ) + hₙ₊₁ (bₙ₊₁ φ) = φ - (res_r φ)#Tr`.
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
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun φ := φ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

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
      LinearMap.id :=
  LinearMap.ext (matrixCochainRestriction_matrixCochainExtension r n)

end Linear

/-- Corner restriction commutes with every Hochschild coface. -/
theorem matrixCochainRestriction_hochschildCoface {R A M ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommMonoid M] [Module R M] [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (i : Fin (n + 2))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r (n + 1) (hochschildCoface R (Matrix ι ι A) M i φ) =
      hochschildCoface R A M i (matrixCochainRestriction r n φ) := by
  ext x; simpa [Function.comp_def] using
    congrArg φ (comp_hochschildFace (Matrix.singleNonUnitalAlgHom R (A := A) r) i x).symm

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCochainRestriction_hochschildCoboundary {R A M ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainRestriction r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n φ) =
      hochschildCoboundary R A M n (matrixCochainRestriction r n φ) := by
  simpa [matrixCochainRestriction] using
    (hochschildCoboundary_compLinearMap (Matrix.singleNonUnitalAlgHom R (A := A) r) φ).symm

/-! ### Cochain homotopy for matrix Hochschild cochains -/

section Tuple

variable {A ι : Type*} [AddCommMonoid A] [Mul A] [One A] [Fintype ι] [DecidableEq ι]
  (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin ((k : ℕ) + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A)

/-- Modified `(n + 2)`-tuple of `Matrix ι ι A` arguments for the `k`-th summand of
`matrixHochschildHomotopy` along path `p : Fin (k + 1) → ι`. -/
def matrixHomotopyTuple : Fin (n + 2) → Matrix ι ι A :=
  Fin.cons (a 0 * Matrix.single (p 0) r (1 : A)) fun j : Fin (n + 1) ↦
    if hj : j < k then
      Matrix.single r r (a ⟨(j : ℕ) + 1, by have := k.2; omega⟩ (p ⟨j, Nat.lt_succ_of_lt hj⟩)
        (p ⟨(j : ℕ) + 1, Nat.add_lt_add_right hj 1⟩))
    else if j = k then Matrix.single r (p (Fin.last k)) (1 : A)
    else a j

/-- Entry `0` of `matrixHomotopyTuple` right-multiplies `a 0` by `Matrix.single (p 0) r 1`. -/
@[simp] theorem matrixHomotopyTuple_zero :
    matrixHomotopyTuple r k p a 0 = a 0 * Matrix.single (p 0) r (1 : A) := (rfl)

/-- For `j < k`, entry `j + 1` places `a (j + 1) (p j) (p (j + 1))` in the `(r, r)` corner. -/
@[simp] theorem matrixHomotopyTuple_succ_of_lt {j : Fin (n + 1)} (hj : j < k) :
    matrixHomotopyTuple r k p a j.succ =
      Matrix.single r r (a ⟨(j : ℕ) + 1, by have := k.2; omega⟩ (p ⟨j, Nat.lt_succ_of_lt hj⟩)
        (p ⟨(j : ℕ) + 1, Nat.add_lt_add_right hj 1⟩)) := by
  simp [matrixHomotopyTuple, hj]

/-- Entry `k + 1` of `matrixHomotopyTuple` is the unit matrix unit `E_{r, pₖ}`. -/
@[simp] theorem matrixHomotopyTuple_succ_self :
    matrixHomotopyTuple r k p a k.succ = Matrix.single r (p (Fin.last k)) (1 : A) := by
  simp [matrixHomotopyTuple]

/-- For `k < j`, entry `j + 1` of `matrixHomotopyTuple` leaves `a j` unchanged. -/
@[simp] theorem matrixHomotopyTuple_succ_of_gt {j : Fin (n + 1)} (hj : k < j) :
    matrixHomotopyTuple r k p a j.succ = a j := by
  simp [matrixHomotopyTuple, hj.not_gt, hj.ne']

end Tuple

section Definition

private def matrixHomotopyArgLinearMap {R A ι : Type*} [Semiring R] [AddCommMonoid A]
    [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ} (k : Fin (n + 1))
    (p : Fin (k + 1) → ι) (s : Fin (n + 1)) : Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if (s : ℕ) = 0 then ∑ u : ι, Matrix.singleLinearMap R u r ∘ₗ Matrix.entryLinearMap R A u (p 0)
  else if hs : (s : ℕ) < (k : ℕ) + 1 then
    Matrix.singleLinearMap R r r ∘ₗ Matrix.entryLinearMap R A (p ⟨s - 1, by omega⟩) (p ⟨s, hs⟩)
  else LinearMap.id

variable (R A M ι : Type*) [Semiring R] [AddCommMonoid A] [One A] [Module R A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

private def matrixHochschildHomotopyStep (r : ι) {n : ℕ} (k : Fin (n + 1)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ p : Fin (k + 1) → ι,
    { toFun φ := (MultilinearMap.compInsertNthLinearMap R
        (M := fun _ : Fin (n + 2) ↦ Matrix ι ι A) k.succ
        (Matrix.single r (p (Fin.last k)) (1 : A)) φ).compLinearMap
        (matrixHomotopyArgLinearMap r k p)
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }

/-- McCarthy's explicit Hochschild cochain homotopy
`hₙ : Cⁿ⁺¹(Matrix ι ι A; M) →ₗ[R] Cⁿ(Matrix ι ι A; M)` contracting `Matrix ι ι A` onto its `(r, r)`
diagonal corner. -/
def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • matrixHochschildHomotopyStep R A M ι r k

end Definition

/-! ### Simplicial identities on `ℕ`-indexed homotopy tuples -/

private def extPath {ι : Type*} (r : ι) {m : ℕ} (p : Fin m → ι) (t : ℕ) : ι :=
  if ht : t < m then p ⟨t, ht⟩ else r

private def natInsertIdx {α : Type*} (i : ℕ) (u : α) (q : ℕ → α) (t : ℕ) : α :=
  if t < i then q t else if t = i then u else q (t - 1)

private theorem extPath_insertNth_eq_natInsertIdx {ι : Type*} (r : ι) {k : ℕ} (j : Fin (k + 2))
    (u : ι) (q : Fin (k + 1) → ι) (t : ℕ) (ht : t < k + 2) :
    extPath r (j.insertNth (α := fun _ ↦ ι) u q) t = natInsertIdx j u (extPath r q) t := by
  rw [show extPath r (j.insertNth (α := fun _ ↦ ι) u q) t =
      j.insertNth (α := fun _ ↦ ι) u q ⟨t, ht⟩ by simp [extPath, ht]]
  rcases lt_trichotomy (⟨t, ht⟩ : Fin (k + 2)) j with hlt | heq | hgt
  · have hlt' : t < (j : ℕ) := hlt
    rw [← Fin.succAbove_castPred_of_lt j ⟨t, ht⟩ hlt, Fin.insertNth_apply_succAbove]
    simp only [natInsertIdx, hlt', ↓reduceIte, extPath, show t < k + 1 by omega, ↓reduceDIte]
    exact congrArg q (Fin.ext (by simp))
  · obtain rfl : t = j := congrArg Fin.val heq
    simp [natInsertIdx, Fin.insertNth_apply_same]
  · have hgt' : (j : ℕ) < t := hgt
    rw [← Fin.succAbove_pred_of_lt j ⟨t, ht⟩ hgt, Fin.insertNth_apply_succAbove]
    simp only [natInsertIdx, show ¬t < (j : ℕ) by omega, show t ≠ (j : ℕ) by omega, ↓reduceIte,
      extPath, show t - 1 < k + 1 by omega, ↓reduceDIte]
    exact congrArg q (Fin.ext (by simp))

private def homotopyIndexEquiv (n : ℕ) :
    (Fin (n + 2) × Fin (n + 1)) ⊕ (Fin (n + 2) ⊕ Fin (n + 2)) ≃ Fin (n + 2) × Fin (n + 3) where
  toFun
    | .inl (m, k') => if (m : ℕ) ≤ (k' : ℕ) then (k'.succ, m.castSucc) else (k'.castSucc, m.succ)
    | .inr (.inl k) => (k, k.castSucc)
    | .inr (.inr k) => (k, k.succ)
  invFun x :=
    if h₁ : (x.2 : ℕ) < (x.1 : ℕ) then
      .inl (⟨x.2, by have := x.1.2; omega⟩, ⟨x.1 - 1, by have := x.1.2; omega⟩)
    else if h₂ : (x.2 : ℕ) = (x.1 : ℕ) then .inr (.inl x.1)
    else if h₃ : (x.2 : ℕ) = (x.1 : ℕ) + 1 then .inr (.inr x.1)
    else .inl (⟨x.2 - 1, by have := x.2.2; omega⟩, ⟨x.1, by have := x.1.2; have := x.2.2; omega⟩)
  left_inv := by
    rintro (⟨m, k'⟩ | k | k)
    · by_cases hmk : (m : ℕ) ≤ (k' : ℕ)
      · simp [hmk, show (m : ℕ) < (k' : ℕ) + 1 by omega]
      · simp [hmk, show ¬(m : ℕ) + 1 < (k' : ℕ) by omega, show ¬(m : ℕ) + 1 = (k' : ℕ) by omega,
          show ¬(m : ℕ) = (k' : ℕ) by omega]
    · simp
    · simp [show ¬(k : ℕ) + 1 < (k : ℕ) by omega]
  right_inv := by
    rintro ⟨k, i⟩; have := k.2; have := i.2; simp only; split_ifs with h1 h2 h3
    · have hle : ((⟨(i : ℕ), by omega⟩ : Fin (n + 2)) : ℕ) ≤
          ((⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) := by simp; omega
      simp [hle, Fin.ext_iff]; omega
    · ext <;> simp [h2]
    · ext <;> simp [h3]
    · have hnle : ¬((⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 2)) : ℕ) ≤ (k : ℕ) := by simp; omega
      simp [hnle, Fin.ext_iff]; omega

@[simp] private theorem homotopyIndexEquiv_inl (n : ℕ) (m : Fin (n + 2)) (k' : Fin (n + 1)) :
    homotopyIndexEquiv n (.inl (m, k')) =
      if (m : ℕ) ≤ (k' : ℕ) then (k'.succ, m.castSucc) else (k'.castSucc, m.succ) := rfl

@[simp] private theorem homotopyIndexEquiv_inr_inl (n : ℕ) (k : Fin (n + 2)) :
    homotopyIndexEquiv n (.inr (.inl k)) = (k, k.castSucc) := rfl

@[simp] private theorem homotopyIndexEquiv_inr_inr (n : ℕ) (k : Fin (n + 2)) :
    homotopyIndexEquiv n (.inr (.inr k)) = (k, k.succ) := rfl

private def extTuple {B : Type*} [Zero B] {m : ℕ} (a : Fin m → B) (t : ℕ) : B :=
  if ht : t < m then a ⟨t, ht⟩ else 0

private theorem fun_extTuple_eq {B : Type*} [Zero B] {m : ℕ} (a : Fin m → B) :
    (fun t : Fin m ↦ extTuple a t) = a := funext fun t ↦ by simp [extTuple]

private def natContractMul {B : Type*} [Mul B] (i : ℕ) (b : ℕ → B) (t : ℕ) : B :=
  if t < i then b t else if t = i then b t * b (t + 1) else b (t + 1)

private theorem hochschildFace_castSucc_comp_val {B : Type*} [Mul B] {N : ℕ} (j : Fin (N + 1))
    (b : ℕ → B) : hochschildFace j.castSucc (fun t : Fin (N + 2) ↦ b t) =
      fun s : Fin (N + 1) ↦ natContractMul j b s := by
  funext s; simp [hochschildFace_castSucc, Fin.contractNth, natContractMul]

private theorem hochschildFace_last_comp_val {B : Type*} [Mul B] {N : ℕ} (b : ℕ → B) :
    hochschildFace (Fin.last (N + 1)) (fun t : Fin (N + 2) ↦ b t) =
      fun s : Fin (N + 1) ↦ if (s : ℕ) = 0 then b (N + 1) * b 0 else b s := by
  funext s; rw [hochschildFace_last]; cases s using Fin.cases <;> simp

section NatIdentities

variable {A ι : Type*} [NonAssocSemiring A] [Fintype ι] [DecidableEq ι]

private def natHomotopyTuple (r : ι) (k : ℕ) (P : ℕ → ι) (b : ℕ → Matrix ι ι A) (s : ℕ) :
    Matrix ι ι A :=
  if s = 0 then b 0 * Matrix.single (P 0) r (1 : A)
  else if s < k + 1 then Matrix.single r r (b s (P (s - 1)) (P s))
  else if s = k + 1 then Matrix.single r (P k) (1 : A)
  else b (s - 1)

private theorem natHomotopyTuple_congr_path (r : ι) (k : ℕ) {P Q : ℕ → ι}
    (hPQ : ∀ t < k + 1, P t = Q t) (b : ℕ → Matrix ι ι A) :
    natHomotopyTuple r k P b = natHomotopyTuple r k Q b := by
  funext s; unfold natHomotopyTuple; split_ifs with h0 hk hk1
  · rw [hPQ 0 (Nat.zero_lt_succ _)]
  · rw [hPQ (s - 1) (by omega), hPQ s hk]
  · rw [hPQ k (Nat.lt_succ_self _)]
  · rfl

private theorem natContractMul_natHomotopyTuple_of_ne (r : ι) {m k' s : ℕ} (hmk : m ≤ k')
    (hne : s ≠ m) (u : ι) (P : ℕ → ι) (b : ℕ → Matrix ι ι A) :
    natContractMul m (natHomotopyTuple r (k' + 1) (natInsertIdx m u P) b) s =
      natHomotopyTuple r k' P (natContractMul m b) s := by
  simp only [natContractMul, natHomotopyTuple, natInsertIdx, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel]
  split_ifs <;> first | omega | rfl | (congr 1; omega)

private theorem natContractMul_natHomotopyTuple_self (r : ι) {m k' : ℕ} (hmk : m ≤ k')
    (u : ι) (P : ℕ → ι) (b : ℕ → Matrix ι ι A) :
    natContractMul m (natHomotopyTuple r (k' + 1) (natInsertIdx m u P) b) m =
      if m = 0 then b 0 * Matrix.single u r (1 : A) * Matrix.single r r (b 1 u (P 0))
      else Matrix.single r r (b m (P (m - 1)) u) * Matrix.single r r (b (m + 1) u (P m)) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [natContractMul, natHomotopyTuple, natInsertIdx]
  · simp only [hm0, natContractMul, natHomotopyTuple, natInsertIdx, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    split_ifs <;> first | omega | rfl

private theorem natContractMul_succ_natHomotopyTuple_of_lt (r : ι) {m k' : ℕ} (hkm : k' < m)
    (P : ℕ → ι) (b : ℕ → Matrix ι ι A) (s : ℕ) :
    natContractMul (m + 1) (natHomotopyTuple r k' P b) s =
      natHomotopyTuple r k' P (natContractMul m b) s := by
  simp only [natContractMul, natHomotopyTuple, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel]
  split_ifs <;> first | omega | rfl | (congr 1; omega) | (congr 2; omega)

private theorem natLastFace_natHomotopyTuple_of_le (r : ι) {n k' s : ℕ} (hk : k' ≤ n)
    (hs : s ≤ n + 1) (P : ℕ → ι) (b : ℕ → Matrix ι ι A) :
    (if s = 0 then natHomotopyTuple r k' P b (n + 2) * natHomotopyTuple r k' P b 0
      else natHomotopyTuple r k' P b s) =
      natHomotopyTuple r k' P (fun t ↦ if t = 0 then b (n + 1) * b 0 else b t) s := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp only [↓reduceIte, natHomotopyTuple, show ¬n + 2 = 0 by omega,
      show ¬n + 2 < k' + 1 by omega, show ¬n + 2 = k' + 1 by omega]
    exact Matrix.mul_mul_single_one (b (n + 1)) (b 0) (P 0) r
  · simp only [hs0, ↓reduceIte, natHomotopyTuple]; split_ifs <;> first | omega | rfl

private theorem natContractMul_diag_succ_of_ne (r : ι) {j s : ℕ} (hne : s ≠ j + 1) (v : ι)
    (P : ℕ → ι) (b : ℕ → Matrix ι ι A) :
    natContractMul (j + 1) (natHomotopyTuple r (j + 1) (natInsertIdx (j + 1) v P) b) s =
      natContractMul (j + 1) (natHomotopyTuple r j P b) s := by
  simp only [natContractMul, natHomotopyTuple, natInsertIdx, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel]
  split_ifs <;> first | omega | rfl

private theorem natContractMul_diag_succ_self (r : ι) (j : ℕ) (v : ι) (P : ℕ → ι)
    (b : ℕ → Matrix ι ι A) :
    natContractMul (j + 1) (natHomotopyTuple r (j + 1) (natInsertIdx (j + 1) v P) b) (j + 1) =
      Matrix.single r r (b (j + 1) (P j) v) * Matrix.single r v (1 : A) := by
  simp only [natContractMul, natHomotopyTuple, natInsertIdx, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel]
  split_ifs <;> first | omega | rfl

private theorem natContractMul_superdiag_self (r : ι) (j : ℕ) (P : ℕ → ι) (b : ℕ → Matrix ι ι A) :
    natContractMul (j + 1) (natHomotopyTuple r j P b) (j + 1) =
      Matrix.single r (P j) (1 : A) * b (j + 1) := by
  simp only [natContractMul, natHomotopyTuple, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel]
  split_ifs <;> first | omega | rfl

private theorem natContractMul_zero_natHomotopyTuple_zero (r u : ι) (b : ℕ → Matrix ι ι A) (s : ℕ) :
    natContractMul 0 (natHomotopyTuple r 0 (fun _ ↦ u) b) s =
      if s = 0 then b 0 * Matrix.single u r (1 : A) * Matrix.single r u (1 : A) else b s := by
  simp only [natContractMul, natHomotopyTuple, Nat.not_lt_zero, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  split_ifs <;> first | omega | rfl

private def natMatrixHomotopyTuple (r : ι) {n : ℕ} (k : ℕ) (p : Fin (k + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) (s : Fin (n + 2)) : Matrix ι ι A :=
  natHomotopyTuple r k (extPath r p) (extTuple a) s

private theorem matrixHomotopyTuple_eq_natMatrixHomotopyTuple (r : ι) {n : ℕ} (k : Fin (n + 1))
    (p : Fin ((k : ℕ) + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHomotopyTuple r k p a = natMatrixHomotopyTuple r k p a := by
  funext s; cases s using Fin.cases with
  | zero => simp [natMatrixHomotopyTuple, natHomotopyTuple, extPath, extTuple]
  | succ j =>
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · have hlt' : (j : ℕ) < k := hlt
      simp [hlt, hlt', natMatrixHomotopyTuple, natHomotopyTuple, extPath, extTuple,
        show (j : ℕ) < (k : ℕ) + 1 by omega, show (j : ℕ) + 1 < n + 1 by omega]
    · simp [natMatrixHomotopyTuple, natHomotopyTuple, extPath, Fin.last]
    · have hgt' : (k : ℕ) < j := hgt
      simp [hgt, hgt'.ne', natMatrixHomotopyTuple, natHomotopyTuple, extTuple,
        show ¬(j : ℕ) + 1 < (k : ℕ) + 1 by omega, j.2]

private theorem natMatrixHomotopyTuple_comp_val (r : ι) {N k : ℕ} (hkN : k ≤ N)
    (p : Fin (k + 1) → ι) (b : ℕ → Matrix ι ι A) :
    natMatrixHomotopyTuple r k p (fun t : Fin (N + 1) ↦ b t) =
      fun s : Fin (N + 2) ↦ natHomotopyTuple r k (extPath r p) b s := by
  funext s; have := s.2; unfold natMatrixHomotopyTuple natHomotopyTuple extTuple
  split_ifs <;> first | omega | rfl

end NatIdentities

section FaceIdentities

variable {R A M ι : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

private theorem sum_hochschildFace_natMatrixHomotopyTuple_of_le (r : ι) {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (m : Fin (n + 2)) (k' : Fin (n + 1)) (hmk : (m : ℕ) ≤ k') :
    ∑ p : Fin ((k' : ℕ) + 2) → ι,
        φ (hochschildFace m.castSucc (natMatrixHomotopyTuple r ((k' : ℕ) + 1) p a)) =
      ∑ q : Fin ((k' : ℕ) + 1) → ι, φ (natMatrixHomotopyTuple r k' q (hochschildFace m a)) := by
  have := k'.2; let j : Fin ((k' : ℕ) + 2) := ⟨m, by omega⟩
  let m₀ : Fin (n + 1) := ⟨m, by omega⟩; have hm_eq : m = m₀.castSucc := rfl
  let b := extTuple a; have ha : a = fun t : Fin (n + 2) ↦ b t := (fun_extTuple_eq a).symm
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
      exact natContractMul_natHomotopyTuple_self r hmk u (extPath r q) b
    · rw [Function.update_of_ne hne]
      exact natContractMul_natHomotopyTuple_of_ne r hmk (Fin.val_ne_of_ne hne) u (extPath r q) b
  simp_rw [Fin.insertNthEquiv_apply, hupd, ← φ.map_update_sum]
  congr 1; rw [Function.update_eq_self_iff]
  by_cases hm0 : (m : ℕ) = 0
  · simp only [hm0, ↓reduceIte, Matrix.sum_mul_single_one_mul_single]
    rw [ha, hm_eq, hochschildFace_castSucc_comp_val,
      natMatrixHomotopyTuple_comp_val r (by omega) q]
    simp [m₀, hm0, natHomotopyTuple, natContractMul]
  · simp only [hm0, ↓reduceIte, Matrix.sum_single_mul_single]
    rw [ha, hm_eq, hochschildFace_castSucc_comp_val,
      natMatrixHomotopyTuple_comp_val r (by omega) q]
    simp [m₀, hm0, natHomotopyTuple, natContractMul, show (m : ℕ) < (k' : ℕ) + 1 by omega]

omit [Semiring R] [Module R A] [AddCommMonoid M] [Module R M] in
private theorem hochschildFace_succ_natMatrixHomotopyTuple_of_lt (r : ι) {n : ℕ}
    (a : Fin (n + 2) → Matrix ι ι A) (m : Fin (n + 2)) (k' : Fin (n + 1)) (hkm : (k' : ℕ) < m)
    (p : Fin ((k' : ℕ) + 1) → ι) :
    hochschildFace m.succ (natMatrixHomotopyTuple r k' p a) =
      natMatrixHomotopyTuple r k' p (hochschildFace m a) := by
  have := k'.2; let b := extTuple a
  have ha : a = fun t : Fin (n + 2) ↦ b t := (fun_extTuple_eq a).symm
  rw [ha, natMatrixHomotopyTuple_comp_val r (by omega) p b]
  induction m using Fin.lastCases with
  | last =>
    let c : ℕ → Matrix ι ι A := fun t ↦ if t = 0 then b (n + 1) * b 0 else b t
    have hc : (fun s : Fin (n + 1) ↦ if (s : ℕ) = 0 then b (n + 1) * b 0 else b s) =
        fun s : Fin (n + 1) ↦ c s := rfl
    rw [Fin.succ_last, hochschildFace_last_comp_val, hochschildFace_last_comp_val, hc,
      natMatrixHomotopyTuple_comp_val r (Nat.le_of_lt_succ k'.2) p c]
    exact funext fun s ↦ natLastFace_natHomotopyTuple_of_le r (Nat.le_of_lt_succ k'.2)
      (Nat.le_of_lt_succ s.2) (extPath r p) b
  | cast m₀ =>
    rw [Fin.succ_castSucc, hochschildFace_castSucc_comp_val, hochschildFace_castSucc_comp_val,
      natMatrixHomotopyTuple_comp_val r (by omega) p]
    exact funext fun s ↦
      natContractMul_succ_natHomotopyTuple_of_lt r (by simpa using hkm) (extPath r p) b s

private theorem sum_hochschildFace_diagonal_succ_eq_superdiagonal (r : ι) {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (j : Fin (n + 1)) :
    ∑ q : Fin ((j : ℕ) + 2) → ι,
        φ (hochschildFace j.succ.castSucc (natMatrixHomotopyTuple r ((j : ℕ) + 1) q a)) =
      ∑ p : Fin ((j : ℕ) + 1) → ι,
        φ (hochschildFace j.castSucc.succ (natMatrixHomotopyTuple r j p a)) := by
  have := j.2; let L : Fin ((j : ℕ) + 2) := Fin.last ((j : ℕ) + 1); let b := extTuple a
  have ha : a = fun t : Fin (n + 2) ↦ b t := (fun_extTuple_eq a).symm
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
    funext s; rcases eq_or_ne s j.succ with rfl | hne
    · rw [Function.update_self, Fin.val_succ]; exact natContractMul_diag_succ_self r j v _ b
    · rw [Function.update_of_ne hne, Fin.val_succ]
      exact natContractMul_diag_succ_of_ne r (Fin.val_ne_of_ne hne) v _ b
  simp_rw [Fin.insertNthEquiv_apply, hupd, ← φ.map_update_sum, Matrix.sum_single_mul_single_one]
  congr 1; rw [Function.update_eq_self_iff, Fin.succ_castSucc, ha,
    natMatrixHomotopyTuple_comp_val r (by omega) p b, hochschildFace_castSucc_comp_val,
    Fin.val_succ]
  exact (natContractMul_superdiag_self r j (extPath r p) b).symm

private theorem sum_hochschildFace_zero_natMatrixHomotopyTuple_zero (r : ι) {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin 1 → ι, φ (hochschildFace 0 (natMatrixHomotopyTuple r 0 p a)) = φ a := by
  let b := extTuple a; have ha : a = fun t : Fin (n + 1) ↦ b t := (fun_extTuple_eq a).symm
  have heq := Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι)
    (fun p : Fin 1 → ι ↦ φ (hochschildFace 0 (natMatrixHomotopyTuple r 0 p a)))
    (fun u : ι ↦
      φ (Function.update a 0 (a 0 * Matrix.single u r (1 : A) * Matrix.single r u (1 : A))))
    fun p ↦ congrArg φ (by
      have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
      rw [h0, ha, natMatrixHomotopyTuple_comp_val r (Nat.zero_le _) p b,
        hochschildFace_castSucc_comp_val, Fin.val_zero,
        natHomotopyTuple_congr_path r 0 (P := extPath r p) (Q := fun _ ↦ p 0)
          (fun t ht ↦ by obtain rfl : t = 0 := (by omega); simp [extPath]) b]
      funext s; rw [natContractMul_zero_natHomotopyTuple_zero]
      rcases eq_or_ne s 0 with rfl | hne <;> simp [*])
  rw [heq, ← φ.map_update_sum, Matrix.sum_mul_single_one_mul_single_one, Function.update_eq_self]

private theorem sum_hochschildFace_last_natMatrixHomotopyTuple_last [SMulCommClass R R M]
    (r : ι) {n : ℕ} (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin (n + 1) → ι,
        φ (hochschildFace (Fin.last (n + 1)) (natMatrixHomotopyTuple r n p a)) =
      matrixCochainExtension ι n (matrixCochainRestriction r n φ) a := by
  simp only [matrixCochainExtension_apply, matrixCochainRestriction_apply]
  refine (Fintype.sum_equiv (Equiv.arrowCongr (finRotate (n + 1)).symm (Equiv.refl ι)) _ _
    fun p ↦ congrArg φ (funext fun s ↦ ?_)).symm
  have hlast (q) : natMatrixHomotopyTuple r n q a = matrixHomotopyTuple r (Fin.last n) q a :=
    (matrixHomotopyTuple_eq_natMatrixHomotopyTuple r (Fin.last n) q a).symm
  rw [hlast, hochschildFace_last]
  cases s using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, ← Fin.succ_last, matrixHomotopyTuple_succ_self, matrixHomotopyTuple_zero,
      Matrix.single_one_mul_mul_single_one]
    simp
  | succ m =>
    rw [Fin.cons_succ, matrixHomotopyTuple_succ_of_lt r (Fin.last n) _ a (Fin.castSucc_lt_last m)]
    simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.symm_symm, Equiv.refl_apply]
    change Matrix.single r r (a m.succ (p m.succ) (p (finRotate (n + 1) m.succ))) =
      Matrix.single r r (a m.succ (p (finRotate (n + 1) m.castSucc)) (p (finRotate (n + 1) m.succ)))
    rw [Fin.finRotate_castSucc]

private def homotopyFaceSum (r : ι) {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (k : Fin (n + 2)) (i : Fin (n + 3)) : M :=
  ∑ p : Fin ((k : ℕ) + 1) → ι, φ (hochschildFace i (natMatrixHomotopyTuple r k p a))

private def homotopyArgFaceSum (r : ι) {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (m : Fin (n + 2)) (k' : Fin (n + 1)) : M :=
  ∑ p : Fin ((k' : ℕ) + 1) → ι, φ (natMatrixHomotopyTuple r k' p (hochschildFace m a))

end FaceIdentities

variable {R A M ι : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] [DecidableEq ι]

omit [IsScalarTower R A A] [SMulCommClass R A A] in
private theorem matrixHochschildHomotopyStep_apply (r : ι) {n : ℕ} (k : Fin (n + 1))
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopyStep R A M ι r k φ a =
      ∑ p : Fin ((k : ℕ) + 1) → ι, φ (matrixHomotopyTuple r k p a) := by
  simp only [matrixHochschildHomotopyStep, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    sum_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.compInsertNthLinearMap_apply,
    MultilinearMap.compInsertNth_apply]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg φ (funext fun s ↦ ?_)
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

omit [IsScalarTower R A A] [SMulCommClass R A A] in
/-- Pointwise evaluation of `matrixHochschildHomotopy` as an alternating sum over `k ≤ n` and
index paths `p : Fin (k + 1) → ι` applied to `matrixHomotopyTuple`. -/
theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy R A M ι r n φ a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin ((k : ℕ) + 1) → ι, φ (matrixHomotopyTuple r k p a) := by
  simp [matrixHochschildHomotopy, LinearMap.sum_apply, matrixHochschildHomotopyStep_apply]

/-- **Degree-zero homotopy identity:** `h₀ (b₀ φ) = φ - (res_r φ)#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy R A M ι r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 φ) =
      φ - matrixCochainExtension ι 0 (matrixCochainRestriction r 0 φ) := by
  ext a; rw [matrixHochschildHomotopy_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, sub_apply, hochschildCoboundary_apply,
    Fin.sum_univ_castSucc, Fin.sum_univ_zero, Fin.val_castSucc, Fin.val_last, pow_one,
    neg_one_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib, zero_add,
    matrixHomotopyTuple_eq_natMatrixHomotopyTuple]
  rw [show (Fin.last 0).castSucc = (0 : Fin 2) from rfl,
    sum_hochschildFace_zero_natMatrixHomotopyTuple_zero r φ a, ← sub_eq_add_neg,
    sum_hochschildFace_last_natMatrixHomotopyTuple_last r φ a]

/-- Every Hochschild `0`-cocycle on `Matrix ι ι A` is the generalized trace of its restriction. -/
theorem eq_matrixCochainExtension_matrixCochainRestriction_of_hochschildCoboundary_zero_eq_zero
    (r : ι) {φ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M}
    (hφ : hochschildCoboundary R (Matrix ι ι A) M 0 φ = 0) :
    φ = matrixCochainExtension ι 0 (matrixCochainRestriction r 0 φ) := by
  have h := matrixHochschildHomotopy_hochschildCoboundary_zero r φ
  rwa [hφ, map_zero, eq_comm, sub_eq_zero] at h

omit [IsScalarTower R A A] [SMulCommClass R A A] [SMulCommClass R R M] in
private theorem homotopyFaceSum_homotopyIndexEquiv_inl (r : ι) {n : ℕ}
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) (x : Fin (n + 2) × Fin (n + 1)) :
    ((-1 : ℤ) ^ (((homotopyIndexEquiv n (.inl x)).1 : ℕ) +
      ((homotopyIndexEquiv n (.inl x)).2 : ℕ))) •
      homotopyFaceSum r φ a (homotopyIndexEquiv n (.inl x)).1 (homotopyIndexEquiv n (.inl x)).2 =
    -((-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) • homotopyArgFaceSum r φ a x.1 x.2) := by
  rcases x with ⟨m, k'⟩
  have hsign (e : ℕ) (he : e = (m : ℕ) + k' + 1) : (-1 : ℤ) ^ e = -((-1 : ℤ) ^ ((m : ℕ) + k')) := by
    rw [he, pow_succ, mul_neg_one]
  by_cases hmk : (m : ℕ) ≤ (k' : ℕ)
  · simp only [homotopyIndexEquiv_inl, hmk, ↓reduceIte, Fin.val_succ, Fin.val_castSucc,
      hsign ((k' : ℕ) + 1 + m) (by omega), neg_smul]
    exact congrArg (fun z : M ↦ -((-1 : ℤ) ^ ((m : ℕ) + k') • z))
      (sum_hochschildFace_natMatrixHomotopyTuple_of_le r φ a m k' hmk)
  · simp only [homotopyIndexEquiv_inl, hmk, ↓reduceIte, Fin.val_succ, Fin.val_castSucc,
      hsign ((k' : ℕ) + ((m : ℕ) + 1)) (by omega), neg_smul]
    refine congrArg (fun z : M ↦ -((-1 : ℤ) ^ ((m : ℕ) + k') • z)) ?_
    simp only [homotopyFaceSum, homotopyArgFaceSum, Fin.val_castSucc]
    exact Finset.sum_congr rfl fun p _ ↦
      congrArg φ (hochschildFace_succ_natMatrixHomotopyTuple_of_lt r a m k' (by omega) p)

/-- **Positive-degree Hochschild homotopy identity:**
`bₙ (hₙ φ) + hₙ₊₁ (bₙ₊₁ φ) = φ - (res_r φ)#Tr`. -/
theorem hochschildCoboundary_matrixHochschildHomotopy_add (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy R A M ι r n φ) +
        matrixHochschildHomotopy R A M ι r (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) φ) =
      φ - matrixCochainExtension ι (n + 1) (matrixCochainRestriction r (n + 1) φ) := by
  ext a
  have hLH1 : hochschildCoboundary R (Matrix ι ι A) M n
      (matrixHochschildHomotopy R A M ι r n φ) a = ∑ x : Fin (n + 2) × Fin (n + 1),
        ((-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ))) • homotopyArgFaceSum r φ a x.1 x.2 := by
    simp only [hochschildCoboundary_apply, matrixHochschildHomotopy_apply,
      matrixHomotopyTuple_eq_natMatrixHomotopyTuple, Finset.smul_sum, smul_smul, ← pow_add,
      Fintype.sum_prod_type, homotopyArgFaceSum]
  have hLH2 : matrixHochschildHomotopy R A M ι r (n + 1)
      (hochschildCoboundary R (Matrix ι ι A) M (n + 1) φ) a = ∑ y : Fin (n + 2) × Fin (n + 3),
        ((-1 : ℤ) ^ ((y.1 : ℕ) + (y.2 : ℕ))) • homotopyFaceSum r φ a y.1 y.2 := by
    rw [matrixHochschildHomotopy_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [hochschildCoboundary_apply, matrixHomotopyTuple_eq_natMatrixHomotopyTuple,
      Finset.smul_sum, smul_smul, ← pow_add, homotopyFaceSum]
    rw [Finset.sum_comm]
  have hdiag (k : Fin (n + 2)) :
      ((-1 : ℤ) ^ ((k : ℕ) + (k.castSucc : ℕ))) • homotopyFaceSum r φ a k k.castSucc =
        homotopyFaceSum r φ a k k.castSucc := by
    rw [Fin.val_castSucc, ← two_mul, Even.neg_one_pow (even_two_mul _), one_smul]
  have hsuper (k : Fin (n + 2)) :
      ((-1 : ℤ) ^ ((k : ℕ) + (k.succ : ℕ))) • homotopyFaceSum r φ a k k.succ =
        -homotopyFaceSum r φ a k k.succ := by
    rw [Fin.val_succ, ← add_assoc, ← two_mul, Odd.neg_one_pow ⟨k, rfl⟩, neg_one_smul]
  simp only [add_apply, sub_apply, hLH1, hLH2, ← (homotopyIndexEquiv n).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [homotopyFaceSum_homotopyIndexEquiv_inl, Finset.sum_neg_distrib,
    homotopyIndexEquiv_inr_inl, homotopyIndexEquiv_inr_inr, hdiag, hsuper]
  have htel : ∑ j : Fin (n + 1), homotopyFaceSum r φ a j.succ j.succ.castSucc =
      ∑ j : Fin (n + 1), homotopyFaceSum r φ a j.castSucc j.castSucc.succ :=
    Finset.sum_congr rfl fun j _ ↦ sum_hochschildFace_diagonal_succ_eq_superdiagonal r φ a j
  rw [add_neg_cancel_left,
    Fin.sum_univ_succ (fun k : Fin (n + 2) ↦ homotopyFaceSum r φ a k k.castSucc),
    Fin.sum_univ_castSucc (fun k : Fin (n + 2) ↦ homotopyFaceSum r φ a k k.succ), htel,
    show homotopyFaceSum r φ a 0 (0 : Fin (n + 2)).castSucc = φ a from
      sum_hochschildFace_zero_natMatrixHomotopyTuple_zero r φ a,
    show homotopyFaceSum r φ a (Fin.last (n + 1)) (Fin.last (n + 1)).succ =
      matrixCochainExtension ι (n + 1) (matrixCochainRestriction r (n + 1) φ) a from
      sum_hochschildFace_last_natMatrixHomotopyTuple_last r φ a]
  abel

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
  simpa [mem_hochschildCocycles_iff, ← matrixCochainRestriction_hochschildCoboundary] using
    congrArg (matrixCochainRestriction r (n + 1)) (mem_hochschildCocycles_iff.1 hφ)

/-- Corner restriction sends Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainRestriction_mem_hochschildCoboundaries [DecidableEq ι] (r : ι)
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCochainRestriction r n φ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero => simp_all [hochschildCoboundaries_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixCochainRestriction r n ψ, (matrixCochainRestriction_hochschildCoboundary r n ψ).symm⟩

end NonUnital

/-- Every Hochschild cocycle on `Matrix ι ι A` for unital `A` is cohomologous to the generalized
matrix trace of its corner restriction. -/
theorem sub_matrixCochainExtension_matrixCochainRestriction_mem_hochschildCoboundaries
    {R A M ι : Type*} [Semiring R] [Semiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [AddCommGroup M] [Module R M] [SMulCommClass R R M] [Fintype ι]
    [DecidableEq ι] (r : ι) {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hφ : φ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    φ - matrixCochainExtension ι n (matrixCochainRestriction r n φ) ∈
      hochschildCoboundaries R (Matrix ι ι A) M n := by
  rw [mem_hochschildCocycles_iff] at hφ
  cases n with
  | zero =>
    simpa [hochschildCoboundaries_zero, sub_eq_zero] using
      eq_matrixCochainExtension_matrixCochainRestriction_of_hochschildCoboundary_zero_eq_zero r hφ
  | succ n =>
    refine mem_hochschildCoboundaries_succ_iff.2 ⟨matrixHochschildHomotopy R A M ι r n φ, ?_⟩
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
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ := desc_mk _ _ _ φ

variable (M) in
/-- `HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M)) →ₗ[R] HHⁿ(A, Hom_R(A, M))` via `(r, r)` corner. -/
noncomputable def matrixRestriction [DecidableEq ι] (r : ι) (n : ℕ) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCochainRestriction r n).restrict
      fun _ ↦ matrixCochainRestriction_mem_hochschildCocycles r)
    fun _ hφ ↦ (mk_eq_zero_iff R A M n _).2
      (matrixCochainRestriction_mem_hochschildCoboundaries r hφ)

/-- `matrixRestriction` sends `[φ]` to the class of its `(r, r)` corner restriction. -/
@[simp] theorem matrixRestriction_mk [DecidableEq ι] (r : ι) {n : ℕ}
    (φ : hochschildCocycles R (Matrix ι ι A) M n) :
    matrixRestriction M r n (mk R (Matrix ι ι A) M n φ) =
      mk R A M n ⟨matrixCochainRestriction r n φ,
        matrixCochainRestriction_mem_hochschildCocycles r φ.2⟩ := desc_mk _ _ _ φ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp] theorem matrixRestriction_matrixExtension [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixRestriction M r n (matrixExtension M ι n c) = c := by
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
  exact sub_matrixCochainExtension_matrixCochainRestriction_mem_hochschildCoboundaries r φ.2

section Nonempty

variable [Nonempty ι]

variable (ι) in
/-- **Matrix Morita invariance of Hochschild cohomology** for unital `A` and nonempty `ι`. -/
theorem bijective_matrixExtension (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.bijective_iff_has_inverse.2
    ⟨matrixRestriction M r n, matrixRestriction_matrixExtension r n,
      matrixExtension_matrixRestriction r n⟩

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

/-- The inverse of `matrixExtensionEquiv` acts by corner restriction along any `r : ι`. -/
theorem matrixExtensionEquiv_symm_apply [DecidableEq ι] (r : ι) (n : ℕ)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c = matrixRestriction M r n c :=
  (matrixExtensionEquiv M ι n).injective (by simp)

end Nonempty

end Unital

end hochschildCohomology

end TauCeti
