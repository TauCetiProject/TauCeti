/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Hochschild
public import TauCeti.RingTheory.CyclicCohomology.Matrix
import Mathlib.Tactic.Abel
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

For a unital associative `R`-algebra `A`, an `R`-module `M`, and a nonempty finite index type `ι`,
the generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) induces a bijection on
Hochschild cohomology `HHⁿ(A, Hom_R(A, M)) → HHⁿ(M_ι(A), Hom_R(M_ι(A), M))` in every degree `n`,
over every commutative ring `R` and associative unital `R`-semiring `A`.

Restricting cochains to a diagonal corner `a ↦ Matrix.single r r a`
(`TauCeti.matrixCochainSingleRestrict`) is a left inverse to matrix extension already on cochains
(`TauCeti.matrixCochainSingleRestrict_matrixCochainExtension`). Using the matrix units
`E_{ij} = Matrix.single i j 1`, Loday's explicit chain homotopy
`h : Cⁿ⁺¹(M_ι(A); M) → Cⁿ(M_ι(A); M)` (`TauCeti.matrixHochschildHomotopy`) satisfies
`h ∘ b + b ∘ h = id - ext ∘ res_r` (and `h₀ ∘ b₀ = id - ext ∘ res_r` in degree zero), making
matrix extension and corner restriction mutually inverse on Hochschild cohomology. We also record
that matrix extension on Hochschild cohomology commutes with Connes' operator `B`.

## Main definitions

* `TauCeti.matrixCochainSingleRestrict`: restriction of cochains on `Matrix ι ι A` to the
  `(r, r)` diagonal corner.
* `TauCeti.matrixHochschildHomotopy`: the explicit Hochschild chain homotopy between the identity
  and `matrixCochainExtension ∘ matrixCochainSingleRestrict`.
* `TauCeti.hochschildCohomology.matrixExtension`, `TauCeti.hochschildCohomology.singleRestrict`:
  matrix extension and corner restriction on Hochschild cohomology.

## Main results

* `TauCeti.matrixHochschildHomotopy_zero_hochschildCoboundary`,
  `TauCeti.matrixHochschildHomotopy_succ_hochschildCoboundary_add`: the chain homotopy identities.
* `TauCeti.hochschildCohomology.singleRestrict_comp_matrixExtension`,
  `TauCeti.hochschildCohomology.matrixExtension_comp_singleRestrict`,
  `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of Hochschild
  cohomology.
* `TauCeti.hochschildCohomology.connesB_comp_matrixExtension`: compatibility of matrix extension
  with Connes' operator `B` on Hochschild cohomology.

## References

* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II,
  Corollary 24, p. 113.
* J.-L. Loday, *Cyclic Homology*, §1.2.4.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Corner restriction of cochains -/

section CornerRestrict

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M] {ι : Type*} [DecidableEq ι]

/-- Restrict a degree-`n` cochain on square matrices to the `(r, r)` diagonal corner via
`x ↦ Matrix.single r r x`. -/
def matrixCochainSingleRestrict (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M where
  toFun ψ := ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Corner restriction evaluates a matrix cochain on matrices concentrated in the `(r, r)` entry. -/
@[simp]
theorem matrixCochainSingleRestrict_apply (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (x : Fin (n + 1) → A) :
    matrixCochainSingleRestrict r n ψ x = ψ fun j ↦ Matrix.single r r (x j) :=
  (rfl)

/-- Corner restriction is a left inverse to matrix extension on cochains. -/
@[simp]
theorem matrixCochainSingleRestrict_matrixCochainExtension [Fintype ι] (r : ι) (n : ℕ)
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) :
    matrixCochainSingleRestrict r n (matrixCochainExtension ι n φ) = φ := by
  ext x
  exact matrixCochainExtension_single ι r n φ x

end CornerRestrict

section CornerRestrictCoboundary

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inclusion of `A` as the `(r, r)` diagonal corner of `Matrix ι ι A`, as a nonunital algebra
homomorphism. -/
private def singleNonUnitalAlgHom (R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι) : A →ₙₐ[R] Matrix ι ι A where
  __ := Matrix.singleLinearMap R r r
  map_zero' := Matrix.single_zero r r
  map_mul' x y := (Matrix.single_mul_single_same x r r r y).symm

/-- Corner restriction commutes with the Hochschild coboundary. -/
theorem matrixCochainSingleRestrict_hochschildCoboundary (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M) :
    matrixCochainSingleRestrict r (n + 1) (hochschildCoboundary R (Matrix ι ι A) M n ψ) =
      hochschildCoboundary R A M n (matrixCochainSingleRestrict r n ψ) :=
  (hochschildCoboundary_compLinearMap (singleNonUnitalAlgHom R A r) ψ).symm

end CornerRestrictCoboundary

/-! ### Explicit Hochschild chain homotopy -/

section SimplicialCombinatorics

/-- A telescoping sum of consecutive differences over `Fin (n + 1)`. -/
private theorem sum_sub_telescope {G : Type*} [AddCommGroup G] :
    ∀ {n : ℕ} (f g : Fin (n + 1) → G), (∀ l : Fin n, f l.succ = g l.castSucc) →
      ∑ k : Fin (n + 1), (f k - g k) = f 0 - g (Fin.last n)
  | 0, f, g, _ => by simp
  | n + 1, f, g, h => by
    rw [Fin.sum_univ_succ,
      sum_sub_telescope (fun l ↦ f l.succ) (fun l ↦ g l.succ) (fun l ↦ h l.succ),
      h 0, Fin.castSucc_zero, Fin.succ_last]
    abel

/-- Partition of `Fin (m + 2) × Fin (m + 3)` into the off-diagonal pairs `(k, i)` with `i < k` or
`k + 1 < i` (bijecting with `Fin (m + 1) × Fin (m + 2)`) and the diagonal pairs `(k, k)` and
`(k, k + 1)` (bijecting with `Fin (m + 2) × Bool`). -/
private def homotopyIndexEquiv (m : ℕ) :
    (Fin (m + 1) × Fin (m + 2)) ⊕ (Fin (m + 2) × Bool) ≃ Fin (m + 2) × Fin (m + 3) where
  toFun
    | .inl (l, j) => if (j : ℕ) ≤ l then (l.succ, j.castSucc) else (l.castSucc, j.succ)
    | .inr (k, false) => (k, k.castSucc)
    | .inr (k, true) => (k, k.succ)
  invFun p :=
    if h₁ : (p.2 : ℕ) < p.1 then
      .inl (⟨p.1.1 - 1, by omega⟩, ⟨p.2.1, by omega⟩)
    else if h₂ : (p.1 : ℕ) + 1 < p.2 then
      .inl (⟨p.1.1, by omega⟩, ⟨p.2.1 - 1, by omega⟩)
    else if (p.2 : ℕ) = p.1 then
      .inr (p.1, false)
    else
      .inr (p.1, true)
  left_inv := by
    rintro (⟨l, j⟩ | ⟨k, _ | _⟩)
    · dsimp only
      by_cases h : (j : ℕ) ≤ l
      · simp [h]
      · simp only [h, ↓reduceIte, show ¬ (j.succ : ℕ) < l.castSucc by simp; omega,
          show (l.castSucc : ℕ) + 1 < j.succ by simp; omega, ↓reduceDIte]
        simp
    · simp
    · simp
  right_inv := by
    rintro ⟨k, i⟩
    dsimp only
    split_ifs <;> dsimp only <;> (try split_ifs) <;> simp_all [Fin.ext_iff] <;> omega

/-- Abstract simplicial homotopy cancellation: when the off-diagonal entries of `S` match `T` and
the consecutive diagonal entries match each other, the two alternating double sums add up to the
difference of the two corner terms. -/
private theorem sum_simplicial_homotopy {G : Type*} [AddCommGroup G] {m : ℕ}
    (S : Fin (m + 2) → Fin (m + 3) → G) (T : Fin (m + 1) → Fin (m + 2) → G)
    (hdiag : ∀ l : Fin (m + 1), S l.succ l.succ.castSucc = S l.castSucc l.castSucc.succ)
    (hlo : ∀ (l : Fin (m + 1)) (j : Fin (m + 2)), (j : ℕ) ≤ l → S l.succ j.castSucc = T l j)
    (hhi : ∀ (l : Fin (m + 1)) (j : Fin (m + 2)), (l : ℕ) < j → S l.castSucc j.succ = T l j) :
    (∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • S k i) +
      (∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) • ∑ l : Fin (m + 1), (-1 : ℤ) ^ (l : ℕ) • T l j) =
      S 0 0 - S (Fin.last (m + 1)) (Fin.last (m + 2)) := by
  let e := homotopyIndexEquiv m
  let F : Fin (m + 2) × Fin (m + 3) → G := fun p ↦ (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • S p.1 p.2
  have hS : (∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) •
      ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • S k i) = ∑ p, F p := by
    simp only [F, Finset.smul_sum, smul_smul, ← pow_add, Fintype.sum_prod_type]
  rw [hS, ← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hinl : (∑ l, ∑ j, F (e (.inl (l, j)))) =
      -(∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
          ∑ l : Fin (m + 1), (-1 : ℤ) ^ (l : ℕ) • T l j) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [F, e, homotopyIndexEquiv, Equiv.coe_fn_mk, smul_smul, ← pow_add]
    split_ifs with hjl
    · rw [Fin.val_succ, Fin.val_castSucc, hlo l j hjl, add_right_comm, pow_succ, mul_neg_one,
        neg_smul, add_comm (l : ℕ)]
    · rw [Fin.val_castSucc, Fin.val_succ, hhi l j (by omega), ← add_assoc, pow_succ, mul_neg_one,
        neg_smul, add_comm (l : ℕ)]
  have hinr : (∑ k, ∑ b, F (e (.inr (k, b)))) =
      S 0 0 - S (Fin.last (m + 1)) (Fin.last (m + 2)) := by
    have hstep (k : Fin (m + 2)) : ∑ b, F (e (.inr (k, b))) = S k k.castSucc - S k k.succ := by
      rw [Fintype.sum_bool]
      simp only [F, e, homotopyIndexEquiv, Equiv.coe_fn_mk, Fin.val_castSucc, Fin.val_succ,
        ← add_assoc, ← two_mul, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, one_smul,
        neg_one_smul]
      abel
    simp_rw [hstep]
    simpa [Fin.castSucc_zero, Fin.succ_last] using
      sum_sub_telescope (fun k ↦ S k k.castSucc) (fun k ↦ S k k.succ) hdiag
  rw [hinl, hinr]
  abel

end SimplicialCombinatorics

section HochschildHomotopyTuple

variable {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise formula for a non-last Hochschild face map. -/
private theorem hochschildFace_apply_of_lt_last {B : Type*} [Mul B] {m : ℕ}
    (j : Fin (m + 2)) (hj : j.val < m + 1) (a : Fin (m + 2) → B) (t : Fin (m + 1)) :
    hochschildFace j a t =
      if t.val < j.val then a t.castSucc
      else if t.val = j.val then a t.castSucc * a t.succ
      else a t.succ := by
  have hjcast : j = (⟨j.val, hj⟩ : Fin (m + 1)).castSucc := Fin.ext rfl
  rw [hjcast, hochschildFace_castSucc, Fin.contractNth]

/-- Entrywise formula for `hochschildFace j.castSucc`. -/
private theorem hochschildFace_castSucc_apply {B : Type*} [Mul B] {m : ℕ}
    (j : Fin (m + 1)) (a : Fin (m + 2) → B) (t : Fin (m + 1)) :
    hochschildFace j.castSucc a t =
      if t.val < j.val then a t.castSucc
      else if t.val = j.val then a t.castSucc * a t.succ
      else a t.succ :=
  hochschildFace_apply_of_lt_last j.castSucc j.isLt a t

/-- The `(n + 2)`-tuple `(a₀ E_{p₀, r}, E_{r, p₀} a₁ E_{p₁, r}, …, E_{r, p_{k-1}} a_k E_{p_k, r},
E_{r, p_k}, a_{k+1}, …, aₙ)` appearing in the `k`-th summand of the Hochschild chain homotopy. -/
private def homotopyTuple (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k.val + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) : Fin (n + 2) → Matrix ι ι A :=
  Fin.insertNth k.succ (Matrix.single r (p (Fin.last k.val)) 1) fun j ↦
    if hj0 : j.val = 0 then
      a j * Matrix.single (p ⟨0, Nat.zero_lt_succ k.val⟩) r 1
    else if hjk : j.val ≤ k.val then
      Matrix.single r (p ⟨j.val - 1, by omega⟩) 1 * a j *
        Matrix.single (p ⟨j.val, by omega⟩) r 1
    else
      a j

/-- Entrywise characterization of `homotopyTuple`. -/
private theorem homotopyTuple_apply (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k.val + 1) → ι)
    (a : Fin (n + 1) → Matrix ι ι A) (m : Fin (n + 2)) :
    homotopyTuple r k p a m =
      if hm0 : m.val = 0 then
        a 0 * Matrix.single (p ⟨0, Nat.zero_lt_succ k.val⟩) r 1
      else if hmk : m.val ≤ k.val then
        Matrix.single r (p ⟨m.val - 1, by omega⟩) 1 * a ⟨m.val, by omega⟩ *
          Matrix.single (p ⟨m.val, by omega⟩) r 1
      else if hmeq : m.val = k.val + 1 then
        Matrix.single r (p ⟨k.val, Nat.lt_succ_self k.val⟩) 1
      else
        a ⟨m.val - 1, by omega⟩ := by
  unfold homotopyTuple
  by_cases hmeq : m = k.succ
  · subst hmeq
    simp [Fin.insertNth_apply_same, Fin.last]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hmeq
    rw [Fin.insertNth_apply_succAbove]
    by_cases hlt : j.castSucc < k.succ
    · rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      have hlt' : j.val ≤ k.val := by simpa [Fin.lt_def] using hlt
      simp only [Fin.val_castSucc]
      by_cases h0 : j.val = 0
      · simp only [h0, ↓reduceDIte]
        congr 2
        exact Fin.ext h0
      · simp only [h0, ↓reduceDIte, hlt']
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hlt)]
      have hge : k.val + 1 ≤ j.val := by simpa [Fin.le_def] using le_of_not_gt hlt
      simp only [Fin.val_succ, show j.val ≠ 0 by omega, show ¬ j.val ≤ k.val by omega,
        show j.val + 1 ≠ 0 by omega, show ¬ j.val + 1 ≤ k.val by omega,
        show j.val + 1 ≠ k.val + 1 by omega, ↓reduceDIte, Nat.add_sub_cancel]

/-- Diagonal-band tuple identity: appending `x` to `q` yields a single-coordinate update of the
adjacent diagonal face. -/
private theorem hochschildFace_diag_homotopyTuple_snoc (r : ι) {n : ℕ} (l : Fin n)
    (q : Fin (l.castSucc.val + 1) → ι) (a : Fin (n + 1) → Matrix ι ι A) (x : ι) :
    hochschildFace l.succ.castSucc (homotopyTuple r l.succ (Fin.snoc q x) a) =
      Function.update (hochschildFace l.castSucc.succ (homotopyTuple r l.castSucc q a)) l.succ
        (Matrix.single r (q (Fin.last l.val)) 1 * a l.succ *
          (Matrix.single x r 1 * Matrix.single r x 1)) := by
  funext m
  rcases eq_or_ne m l.succ with rfl | hm
  · rw [Function.update_self, hochschildFace_castSucc_apply]
    simp only [lt_self_iff_false, ↓reduceIte, homotopyTuple_apply, Fin.val_castSucc, Fin.val_succ,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, le_refl, Nat.add_sub_cancel,
      add_le_iff_nonpos_right, nonpos_iff_eq_zero, Fin.last]
    have h1 : Fin.snoc (α := fun _ ↦ ι) q x ⟨l.val, by simp⟩ = q ⟨l.val, Nat.lt_succ_self _⟩ :=
      Fin.snoc_castSucc (α := fun _ ↦ ι) x q ⟨l.val, Nat.lt_succ_self _⟩
    have h2 : Fin.snoc (α := fun _ ↦ ι) q x ⟨l.val + 1, by simp⟩ = x :=
      Fin.snoc_last (α := fun _ ↦ ι) x q
    rw [h1, h2, Matrix.mul_assoc]
    rfl
  · rw [Function.update_of_ne hm, Fin.succ_castSucc, hochschildFace_castSucc_apply,
      hochschildFace_castSucc_apply]
    have hne : m.val ≠ l.val + 1 := fun h ↦ hm (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hml | hlm
    · have hsnoc (u : ℕ) (hu : u < l.val + 1) :
          Fin.snoc (α := fun _ ↦ ι) q x ⟨u, by simp; omega⟩ = q ⟨u, hu⟩ :=
        Fin.snoc_castSucc (α := fun _ ↦ ι) x q ⟨u, hu⟩
      simp only [Fin.val_succ, hml, ↓reduceIte, homotopyTuple_apply, Fin.val_castSucc]
      by_cases hm0 : m.val = 0
      · simp only [hm0, ↓reduceDIte, hsnoc 0 (Nat.zero_lt_succ l.val)]
      · simp only [hm0, ↓reduceDIte, show m.val ≤ l.val + 1 by omega, show m.val ≤ l.val by omega,
          hsnoc (m.val - 1) (by omega), hsnoc m.val (by omega)]
    · simp only [Fin.val_succ, show ¬ m.val < l.val + 1 by omega, hne, ↓reduceIte,
        homotopyTuple_apply, Fin.val_castSucc, show m.val + 1 ≠ 0 by omega,
        show ¬ m.val + 1 ≤ l.val + 1 by omega, show m.val + 1 ≠ l.val + 1 + 1 by omega,
        show ¬ m.val + 1 ≤ l.val by omega, show m.val + 1 ≠ l.val + 1 by omega, ↓reduceDIte,
        Nat.add_sub_cancel]

/-- Lower-triangle tuple identity at the contracted coordinate `t = j`. -/
private theorem hochschildFace_lt_homotopyTuple_insertNth_eq (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (j : Fin (m + 2)) (hj : (j : ℕ) ≤ l)
    (q : Fin l.succ.val → ι) (a : Fin (m + 2) → Matrix ι ι A) (x : ι) :
    hochschildFace j.castSucc
        (homotopyTuple r l.succ
          (Fin.insertNth (α := fun _ ↦ ι) ⟨j.val, by simp only [Fin.val_succ]; omega⟩ x q) a) j =
      if j.val = 0 then
        a 0 * (Matrix.single x r 1 * Matrix.single r x 1) * a 1 *
          Matrix.single (q ⟨0, Nat.zero_lt_succ l.val⟩) r 1
      else
        Matrix.single r (q ⟨j.val - 1, by simp only [Fin.val_succ]; omega⟩) 1 * a j *
          (Matrix.single x r 1 * Matrix.single r x 1) * a ⟨j.val + 1, by omega⟩ *
          Matrix.single (q ⟨j.val, by simp only [Fin.val_succ]; omega⟩) r 1 := by
  rw [hochschildFace_castSucc_apply]
  simp only [lt_self_iff_false, ↓reduceIte, homotopyTuple_apply, Fin.val_castSucc, Fin.val_succ]
  by_cases hj0 : j.val = 0
  · simp only [hj0, ↓reduceDIte, ↓reduceIte, one_ne_zero, Nat.succ_le_succ (Nat.zero_le l.val),
      Nat.zero_add, Fin.mk_one, Matrix.mul_assoc]
    have h0 : Fin.insertNth (α := fun _ ↦ ι)
        (⟨0, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q
        ⟨0, Nat.zero_lt_succ _⟩ = x :=
      Fin.insertNth_apply_same (α := fun _ ↦ ι) ⟨0, by simp only [Fin.val_succ]; omega⟩ x q
    have h1 : Fin.insertNth (α := fun _ ↦ ι)
        (⟨0, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q 1 =
          q ⟨0, Nat.zero_lt_succ l.val⟩ :=
      Fin.insertNth_apply_above (α := fun _ ↦ ι) (i := ⟨0, by simp only [Fin.val_succ]; omega⟩)
        (j := 1) (by simp) x q
    rw [h0, h1]
  · have hjm : Fin.insertNth (α := fun _ ↦ ι)
        (⟨j.val, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q
        ⟨j.val - 1, by simp only [Fin.val_succ]; omega⟩ =
          q ⟨j.val - 1, by simp only [Fin.val_succ]; omega⟩ := by
      rw [Fin.insertNth_apply_below (α := fun _ ↦ ι)]; · simp; rfl
      exact Fin.mk_lt_mk.2 (by omega)
    have hj' : Fin.insertNth (α := fun _ ↦ ι)
        (⟨j.val, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q
        ⟨j.val, by simp only [Fin.val_succ]; omega⟩ = x :=
      Fin.insertNth_apply_same (α := fun _ ↦ ι) ⟨j.val, by simp only [Fin.val_succ]; omega⟩ x q
    have hjp : Fin.insertNth (α := fun _ ↦ ι)
        (⟨j.val, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q
        ⟨j.val + 1, by simp only [Fin.val_succ]; omega⟩ =
          q ⟨j.val + 1 - 1, by simp only [Fin.val_succ]; omega⟩ := by
      rw [Fin.insertNth_apply_above (α := fun _ ↦ ι)]; · simp
      exact Fin.mk_lt_mk.2 (by omega)
    simp only [hj0, ↓reduceDIte, ↓reduceIte, show j.val ≤ l.val + 1 by omega,
      show j.val + 1 ≠ 0 by omega, show j.val + 1 ≤ l.val + 1 by omega, hjm, hj', hjp,
      Nat.add_sub_cancel, Matrix.mul_assoc]

/-- Lower-triangle tuple identity at any coordinate `t ≠ j`. -/
private theorem hochschildFace_lt_homotopyTuple_insertNth_ne (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (j : Fin (m + 2)) (hj : (j : ℕ) ≤ l)
    (q : Fin l.succ.val → ι) (a : Fin (m + 2) → Matrix ι ι A) (x : ι)
    {t : Fin (m + 2)} (ht : t ≠ j) :
    hochschildFace j.castSucc
        (homotopyTuple r l.succ
          (Fin.insertNth (α := fun _ ↦ ι) ⟨j.val, by simp only [Fin.val_succ]; omega⟩ x q) a) t =
      homotopyTuple r l q (hochschildFace j a) t := by
  have hins_lt (u : ℕ) (hu : u < j.val) :
      Fin.insertNth (α := fun _ ↦ ι)
          (⟨j.val, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q
          ⟨u, by simp only [Fin.val_succ]; omega⟩ = q ⟨u, by simp only [Fin.val_succ]; omega⟩ := by
    rw [Fin.insertNth_apply_below (α := fun _ ↦ ι)]; · simp; rfl
    exact Fin.mk_lt_mk.2 hu
  have hins_gt (u : ℕ) (hu₁ : j.val < u) (hu₂ : u < l.succ.val + 1) :
      Fin.insertNth (α := fun _ ↦ ι)
          (⟨j.val, by simp only [Fin.val_succ]; omega⟩ : Fin (l.succ.val + 1)) x q ⟨u, hu₂⟩ =
        q ⟨u - 1, by simp only [Fin.val_succ] at hu₂ ⊢; omega⟩ := by
    rw [Fin.insertNth_apply_above (α := fun _ ↦ ι)]; · simp [Fin.pred]
    exact Fin.mk_lt_mk.2 hu₁
  rw [hochschildFace_castSucc_apply]
  have hne : t.val ≠ j.val := fun h ↦ ht (Fin.ext h)
  rcases lt_or_gt_of_ne hne with htj | hjt
  · simp only [htj, ↓reduceIte, homotopyTuple_apply, Fin.val_castSucc, Fin.val_succ,
      hochschildFace_apply_of_lt_last j (by omega)]
    by_cases ht0 : t.val = 0
    · simp only [ht0, ↓reduceDIte, Fin.val_zero, show 0 < j.val by omega, ↓reduceIte,
        hins_lt 0 (by omega)]
      rfl
    · simp only [ht0, ↓reduceDIte, show t.val ≤ l.val + 1 by omega, show t.val ≤ l.val by omega,
        hins_lt (t.val - 1) (by omega), hins_lt t.val htj]
      rfl
  · simp only [show ¬ t.val < j.val by omega, hne, ↓reduceIte, homotopyTuple_apply, Fin.val_succ,
      show t.val + 1 ≠ 0 by omega, show t.val ≠ 0 by omega, ↓reduceDIte,
      hochschildFace_apply_of_lt_last j (by omega)]
    by_cases htl : t.val ≤ l.val
    · simp only [show t.val + 1 ≤ l.val + 1 by omega, htl, ↓reduceDIte, Nat.add_sub_cancel,
        hins_gt t.val hjt (by simp only [Fin.val_succ]; omega),
        hins_gt (t.val + 1) (by omega) (by simp only [Fin.val_succ]; omega)]
      rfl
    · by_cases hteq : t.val = l.val + 1
      · simp only [hteq, Nat.not_succ_le_self, ↓reduceDIte,
          hins_gt (l.val + 1) (by omega) (by simp only [Fin.val_succ]; omega), Nat.add_sub_cancel]
      · simp only [show ¬ t.val + 1 ≤ l.val + 1 by omega, show t.val + 1 ≠ l.val + 1 + 1 by omega,
          htl, hteq, ↓reduceDIte, Nat.add_sub_cancel, show ¬ t.val - 1 < j.val by omega,
          show t.val - 1 ≠ j.val by omega, ↓reduceIte]
        congr 1; exact Fin.ext (by simp; omega)

/-- Inserting index `x` at position `j ≤ l` turns the `j`-th face of `homotopyTuple r l.succ` into
a single-coordinate update of `homotopyTuple r l q (hochschildFace j a)`. -/
private theorem hochschildFace_lt_homotopyTuple_insertNth (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (j : Fin (m + 2)) (hj : (j : ℕ) ≤ l)
    (q : Fin l.succ.val → ι) (a : Fin (m + 2) → Matrix ι ι A) (x : ι) :
    hochschildFace j.castSucc
        (homotopyTuple r l.succ
          (Fin.insertNth (α := fun _ ↦ ι) ⟨j.val, by simp only [Fin.val_succ]; omega⟩ x q) a) =
      Function.update (homotopyTuple r l q (hochschildFace j a)) j
        (if j.val = 0 then
          a 0 * (Matrix.single x r 1 * Matrix.single r x 1) * a 1 *
            Matrix.single (q ⟨0, Nat.zero_lt_succ l.val⟩) r 1
        else
          Matrix.single r (q ⟨j.val - 1, by simp only [Fin.val_succ]; omega⟩) 1 * a j *
            (Matrix.single x r 1 * Matrix.single r x 1) * a ⟨j.val + 1, by omega⟩ *
            Matrix.single (q ⟨j.val, by simp only [Fin.val_succ]; omega⟩) r 1) := by
  funext t
  rcases eq_or_ne t j with rfl | ht
  · rw [Function.update_self]
    exact hochschildFace_lt_homotopyTuple_insertNth_eq r l t hj q a x
  · rw [Function.update_of_ne ht]
    exact hochschildFace_lt_homotopyTuple_insertNth_ne r l j hj q a x ht

/-- Upper-triangle tuple identity for the last face `j = Fin.last (m + 1)`. -/
private theorem hochschildFace_gt_homotopyTuple_last (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (p : Fin (l.val + 1) → ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace (Fin.last (m + 1)).succ (homotopyTuple r l.castSucc p a) =
      homotopyTuple r l p (hochschildFace (Fin.last (m + 1)) a) := by
  funext t
  rw [Fin.succ_last, hochschildFace_last, hochschildFace_last]
  cases t using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, homotopyTuple_apply, Fin.val_last, Fin.val_castSucc, Fin.val_zero,
      ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel,
      show ¬ m + 2 ≤ l.val by omega, show m + 2 ≠ l.val + 1 by omega, Matrix.mul_assoc]
    rfl
  | succ t =>
    simp only [Fin.cons_succ, homotopyTuple_apply, Fin.val_castSucc, Fin.val_succ,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte]
    by_cases h1 : t.val + 1 ≤ l.val
    · simp only [h1, ↓reduceDIte]
      have hidx : (⟨t.val + 1, by omega⟩ : Fin (m + 1)) = (⟨t.val, by omega⟩ : Fin m).succ :=
        Fin.ext rfl
      rw [hidx, Fin.cons_succ]
      rfl
    · by_cases h2 : t.val + 1 = l.val + 1
      · simp only [h2, Nat.not_succ_le_self, ↓reduceDIte]
      · simp only [h1, h2, ↓reduceDIte, Nat.add_sub_cancel]
        have hidx : (⟨t.val, by omega⟩ : Fin (m + 1)) = (⟨t.val - 1, by omega⟩ : Fin m).succ :=
          Fin.ext (by simp; omega)
        rw [hidx, Fin.cons_succ]
        congr 1; exact Fin.ext (by simp; omega)

/-- Upper-triangle tuple identity for a non-last face `j.castSucc` with `l < j`. -/
private theorem hochschildFace_gt_homotopyTuple_castSucc (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (j : Fin (m + 1)) (hj : (l : ℕ) < j)
    (p : Fin (l.val + 1) → ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace j.castSucc.succ (homotopyTuple r l.castSucc p a) =
      homotopyTuple r l p (hochschildFace j.castSucc a) := by
  funext t
  rw [Fin.succ_castSucc, hochschildFace_castSucc_apply]
  by_cases htl : t.val ≤ l.val
  · simp only [Fin.val_succ, show t.val < j.val + 1 by omega, ↓reduceIte, homotopyTuple_apply,
      Fin.val_castSucc, hochschildFace_castSucc_apply]
    by_cases ht0 : t.val = 0
    · simp only [ht0, ↓reduceDIte, Fin.val_zero, show 0 < j.val by omega, ↓reduceIte]
      rfl
    · simp only [ht0, htl, ↓reduceDIte, show t.val < j.val by omega, ↓reduceIte]
      rfl
  · by_cases hteq : t.val = l.val + 1
    · simp only [Fin.val_succ, homotopyTuple_apply, Fin.val_castSucc, hteq,
        show l.val + 1 < j.val + 1 by omega, show l.val + 1 ≠ 0 by omega,
        Nat.not_succ_le_self, ↓reduceIte, ↓reduceDIte]
    · rcases lt_trichotomy (t.val - 1) j.val with hlt | heq | hgt
      · simp only [Fin.val_succ, show t.val < j.val + 1 by omega, ↓reduceIte, homotopyTuple_apply,
          Fin.val_castSucc, show t.val ≠ 0 by omega, htl, hteq, ↓reduceDIte,
          hochschildFace_castSucc_apply, hlt]
        rfl
      · simp only [Fin.val_succ, homotopyTuple_apply, Fin.val_castSucc,
          show t.val = j.val + 1 by omega, lt_self_iff_false, ↓reduceIte,
          show j.val + 1 ≠ 0 by omega, show ¬ j.val + 1 ≤ l.val by omega,
          show j.val + 1 ≠ l.val + 1 by omega, show j.val + 1 + 1 ≠ 0 by omega,
          show ¬ j.val + 1 + 1 ≤ l.val by omega, show j.val + 1 + 1 ≠ l.val + 1 by omega,
          ↓reduceDIte, Nat.add_sub_cancel, hochschildFace_castSucc_apply]
        rfl
      · simp only [Fin.val_succ, show ¬ t.val < j.val + 1 by omega,
          show t.val ≠ j.val + 1 by omega, ↓reduceIte, homotopyTuple_apply, Fin.val_castSucc,
          show t.val ≠ 0 by omega, htl, hteq, ↓reduceDIte, hochschildFace_castSucc_apply,
          show ¬ t.val - 1 < j.val by omega, show t.val - 1 ≠ j.val by omega,
          show t.val + 1 ≠ 0 by omega, show ¬ t.val + 1 ≤ l.val by omega,
          show t.val + 1 ≠ l.val + 1 by omega, Nat.add_sub_cancel]
        congr 1; exact Fin.ext (by simp; omega)

/-- Upper-triangle cancellation: for `l < j`, the `(j + 1)`-st face of `T_l(a, p)` equals
`T_l(d_j a, p)` term by term. -/
private theorem hochschildFace_gt_homotopyTuple (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (j : Fin (m + 2)) (hj : (l : ℕ) < j)
    (p : Fin (l.val + 1) → ι) (a : Fin (m + 2) → Matrix ι ι A) :
    hochschildFace j.succ (homotopyTuple r l.castSucc p a) =
      homotopyTuple r l p (hochschildFace j a) := by
  induction j using Fin.lastCases with
  | last => exact hochschildFace_gt_homotopyTuple_last r l p a
  | cast j => exact hochschildFace_gt_homotopyTuple_castSucc r l j hj p a

end HochschildHomotopyTuple

section HochschildHomotopyFaces

variable {R A M : Type*} [Semiring R] [Semiring A] [Module R A]
  [AddCommMonoid M] [Module R M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `(0, 0)` corner term of `h (b ψ)` recovers `ψ`. -/
private theorem sum_hochschildFace_zero_homotopyTuple_zero (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin ((0 : Fin (n + 1)).val + 1) → ι,
        ψ (hochschildFace 0 (homotopyTuple r 0 p a)) = ψ a := by
  let e : ι ≃ (Fin ((0 : Fin (n + 1)).val + 1) → ι) :=
    { toFun x _ := x
      invFun p := p ⟨0, Nat.zero_lt_succ _⟩
      left_inv _ := rfl
      right_inv p := funext fun i ↦ congrArg p (Fin.ext (by
        have hi := i.isLt; simp only [Fin.val_zero, Nat.zero_add] at hi; dsimp; omega)) }
  rw [← e.sum_comp]
  dsimp only [e, Equiv.coe_fn_mk]
  have hupd (x : ι) :
      hochschildFace 0 (homotopyTuple r 0 (fun _ ↦ x) a) =
        Function.update a 0 (a 0 * (Matrix.single x r 1 * Matrix.single r x 1)) := by
    funext m
    rw [← Fin.castSucc_zero, hochschildFace_castSucc_apply]
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [Function.update_self, lt_self_iff_false, ↓reduceIte, Fin.castSucc_zero,
        Fin.succ_zero_eq_one, homotopyTuple_apply]
      simp only [Fin.val_zero, Fin.val_one, one_ne_zero, show ¬ (1 : ℕ) ≤ 0 by omega, ↓reduceDIte,
        Matrix.mul_assoc]
    · have hm' : m.val ≠ 0 := fun h ↦ hm (Fin.ext h)
      simp only [Function.update_of_ne hm, show ¬ m.val < (0 : Fin (n + 1)).val by simp,
        show m.val ≠ (0 : Fin (n + 1)).val by simpa using hm', ↓reduceIte, homotopyTuple_apply]
      simp only [Fin.val_zero, Fin.val_succ, show m.val + 1 ≠ 0 by omega,
        show ¬ m.val + 1 ≤ 0 by omega, show m.val + 1 ≠ 1 by omega, ↓reduceDIte,
        Nat.add_sub_cancel]
  simp_rw [hupd, ← ψ.map_update_sum, ← Finset.mul_sum, Matrix.single_mul_single_same, mul_one,
    Matrix.sum_single_one, mul_one, Function.update_eq_self]

/-- The `(n, n + 1)` corner term of `h (b ψ)` equals `(matrixCochainExtension (res_r ψ)) a`. -/
private theorem sum_hochschildFace_last_homotopyTuple_last [SMulCommClass R R M] (r : ι) {n : ℕ}
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin ((Fin.last n).val + 1) → ι,
        ψ (hochschildFace (Fin.last (n + 1)) (homotopyTuple r (Fin.last n) p a)) =
      matrixCochainExtension ι n (matrixCochainSingleRestrict r n ψ) a := by
  rw [matrixCochainExtension_apply]
  let e : (Fin (n + 1) → ι) ≃ (Fin ((Fin.last n).val + 1) → ι) :=
    Equiv.arrowCongr (finRotate (n + 1)).symm (Equiv.refl ι)
  refine (e.sum_comp _).symm.trans (Finset.sum_congr rfl fun q _ ↦ ?_)
  simp only [matrixCochainSingleRestrict_apply]
  congr 1
  funext j
  rw [hochschildFace_last]
  cases j using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, homotopyTuple_apply, Fin.val_last, Fin.val_zero, ↓reduceDIte,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, add_le_iff_nonpos_right, nonpos_iff_eq_zero]
    rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]
    have h1 : e q ⟨n, Nat.lt_succ_self n⟩ = q 0 := congrArg q (finRotate_last (n := n))
    have h2 : e q ⟨0, Nat.zero_lt_succ n⟩ = q (finRotate (n + 1) 0) := rfl
    rw [h1, h2]
  | succ j =>
    have hlt : j.val + 1 ≤ n := j.isLt
    simp only [Fin.cons_succ, homotopyTuple_apply, Fin.val_castSucc, Fin.val_succ, Fin.val_last,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, hlt, Nat.add_sub_cancel]
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    have h1 : e q ⟨j.val, by simp only [Fin.val_last]; omega⟩ = q j.succ :=
      congrArg q (Fin.finRotate_castSucc j)
    have h2 : e q ⟨j.val + 1, by simp only [Fin.val_last]; omega⟩ = q (finRotate (n + 1) j.succ) :=
      rfl
    rw [h1, h2]
    rfl

/-- Adjacent diagonal terms in `h (b ψ)` match pairwise, causing the diagonal band to telescope. -/
private theorem sum_hochschildFace_diag_homotopyTuple (r : ι) {n : ℕ} (l : Fin n)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    ∑ p : Fin (l.succ.val + 1) → ι,
        ψ (hochschildFace l.succ.castSucc (homotopyTuple r l.succ p a)) =
      ∑ q : Fin (l.castSucc.val + 1) → ι,
        ψ (hochschildFace l.castSucc.succ (homotopyTuple r l.castSucc q a)) := by
  refine ((Fin.snocEquiv (fun _ : Fin (l.succ.val + 1) ↦ ι)).sum_comp _).symm.trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp_rw [Fin.snocEquiv_apply, hochschildFace_diag_homotopyTuple_snoc r l q a,
    ← ψ.map_update_sum, ← Finset.mul_sum, Matrix.single_mul_single_same, mul_one,
    Matrix.sum_single_one, mul_one]
  congr 1
  rw [Function.update_eq_self_iff, Fin.succ_castSucc, hochschildFace_castSucc_apply]
  simp only [lt_self_iff_false, ↓reduceIte, homotopyTuple_apply, Fin.val_castSucc, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, add_le_iff_nonpos_right,
    nonpos_iff_eq_zero, show ¬ l.val + 1 + 1 ≤ l.val by omega,
    show l.val + 1 + 1 ≠ l.val + 1 by omega, Fin.last, Nat.add_sub_cancel]
  rfl

/-- Lower-triangle cancellation: for `j ≤ l`, summing out the index `p_j` turns
`d_j (T_{l+1}(a, p))` into `T_l(d_j a, q)`. -/
private theorem sum_hochschildFace_lt_homotopyTuple (r : ι) {m : ℕ}
    (l : Fin (m + 1)) (j : Fin (m + 2)) (hj : (j : ℕ) ≤ l)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M)
    (a : Fin (m + 2) → Matrix ι ι A) :
    ∑ p : Fin (l.succ.val + 1) → ι,
        ψ (hochschildFace j.castSucc (homotopyTuple r l.succ p a)) =
      ∑ q : Fin (l.val + 1) → ι, ψ (homotopyTuple r l q (hochschildFace j a)) := by
  refine ((Fin.insertNthEquiv (fun _ : Fin (l.succ.val + 1) ↦ ι)
      ⟨j.val, by simp only [Fin.val_succ]; omega⟩).sum_comp _).symm.trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp_rw [Fin.insertNthEquiv_apply, hochschildFace_lt_homotopyTuple_insertNth r l j hj q a,
    ← ψ.map_update_sum]
  congr 1
  rw [Function.update_eq_self_iff, homotopyTuple_apply]
  by_cases hj0 : j.val = 0
  · simp only [hj0, ↓reduceIte, ↓reduceDIte, ← Finset.sum_mul, ← Finset.mul_sum,
      Matrix.single_mul_single_same, Matrix.sum_single_one, mul_one]
    rw [hochschildFace_apply_of_lt_last j (by omega)]
    simp [hj0]
  · simp only [hj0, hj, ↓reduceIte, ↓reduceDIte, ← Finset.sum_mul, ← Finset.mul_sum,
      Matrix.single_mul_single_same, Matrix.sum_single_one, mul_one]
    rw [hochschildFace_apply_of_lt_last j (by omega)]
    simp [Matrix.mul_assoc]

end HochschildHomotopyFaces

section HochschildHomotopy

variable {R A M : Type*} [Semiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fix the `i`-th argument of an `(n + 1)`-cochain to a constant `c`. -/
private def insertNthConst {B : Type*} [AddCommMonoid B] [Module R B] {n : ℕ}
    (i : Fin (n + 2)) (c : B) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ B) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ B) M where
  toFun φ :=
    { toFun a := φ (Fin.insertNth i c a)
      map_update_add' := by
        intro _ a k x y
        obtain rfl : ‹DecidableEq (Fin (n + 1))› = instDecidableEqFin _ := Subsingleton.elim _ _
        simp only [Fin.insertNth_update, MultilinearMap.map_update_add]
      map_update_smul' := by
        intro _ a k s x
        obtain rfl : ‹DecidableEq (Fin (n + 1))› = instDecidableEqFin _ := Subsingleton.elim _ _
        simp only [Fin.insertNth_update, MultilinearMap.map_update_smul] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinatewise linear maps in the `k`-th summand of Loday's Hochschild chain homotopy. -/
private def homotopyCoordMap (R : Type*) {A : Type*} [Semiring R] [Semiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) {n : ℕ} (k : Fin (n + 1)) (p : Fin (k.val + 1) → ι) (j : Fin (n + 1)) :
    Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if hj0 : j.val = 0 then
    LinearMap.mulRight R (Matrix.single (p ⟨0, Nat.zero_lt_succ k.val⟩) r 1)
  else if hjk : j.val ≤ k.val then
    LinearMap.mulLeftRight R
      (Matrix.single r (p ⟨j.val - 1, by omega⟩) 1, Matrix.single (p ⟨j.val, by omega⟩) r 1)
  else
    LinearMap.id

/-- The `k`-th summand of the Hochschild chain homotopy on `Matrix ι ι A`. -/
private def matrixHochschildHomotopyPiece (r : ι) (n : ℕ) (k : Fin (n + 1)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun ψ := ∑ p : Fin (k.val + 1) → ι,
    (insertNthConst k.succ (Matrix.single r (p (Fin.last k.val)) 1) ψ).compLinearMap
      (homotopyCoordMap R r k p)
  map_add' φ ψ := by
    ext a
    simp [insertNthConst, Finset.sum_add_distrib]
  map_smul' c φ := by
    ext a
    simp [insertNthConst, Finset.smul_sum]

private theorem matrixHochschildHomotopyPiece_apply (r : ι) (n : ℕ) (k : Fin (n + 1))
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopyPiece r n k ψ a =
      ∑ p : Fin (k.val + 1) → ι, ψ (homotopyTuple r k p a) := by
  simp only [matrixHochschildHomotopyPiece, LinearMap.coe_mk, AddHom.coe_mk, _root_.sum_apply,
    MultilinearMap.compLinearMap_apply, insertNthConst, homotopyTuple]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg ψ (congrArg _ (funext fun j ↦ ?_))
  unfold homotopyCoordMap
  split_ifs <;> simp [LinearMap.mulRight_apply, LinearMap.mulLeftRight_apply]

/-- Loday's explicit Hochschild chain homotopy `h : Cⁿ⁺¹(M_ι(A); M) → Cⁿ(M_ι(A); M)` between the
identity and `matrixCochainExtension ∘ matrixCochainSingleRestrict`, built from matrix units at
the chosen diagonal index `r : ι`. -/
def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • matrixHochschildHomotopyPiece r n k

private theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n ψ a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin (k.val + 1) → ι, ψ (homotopyTuple r k p a) := by
  simp [matrixHochschildHomotopy, matrixHochschildHomotopyPiece_apply]

/-- In degree zero, the chain homotopy satisfies `h₀ (b₀ ψ) = ψ - ext (res_r ψ)`. -/
theorem matrixHochschildHomotopy_zero_hochschildCoboundary (r : ι)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 ψ) =
      ψ - matrixCochainExtension ι 0 (matrixCochainSingleRestrict r 0 ψ) := by
  ext a
  rw [matrixHochschildHomotopy_apply, Fin.sum_univ_one]
  have hsign0 : (-1 : ℤ) ^ ((0 : Fin 1) : ℕ) = 1 := by simp
  rw [hsign0, one_smul]
  have hinner (p : Fin ((0 : Fin 1).val + 1) → ι) :
      hochschildCoboundary R (Matrix ι ι A) M 0 ψ (homotopyTuple r 0 p a) =
        ψ (hochschildFace 0 (homotopyTuple r 0 p a)) -
          ψ (hochschildFace (Fin.last 1) (homotopyTuple r 0 p a)) := by
    rw [hochschildCoboundary_apply, Fin.sum_univ_two]
    simp [show (1 : Fin 2) = Fin.last 1 from rfl, sub_eq_add_neg]
  simp_rw [hinner, Finset.sum_sub_distrib, _root_.sub_apply]
  rw [sum_hochschildFace_zero_homotopyTuple_zero, ← Fin.last_zero,
    sum_hochschildFace_last_homotopyTuple_last]

/-- In positive degree, the chain homotopy satisfies
`h_{m+1} (b_{m+1} ψ) + b_m (h_m ψ) = ψ - ext (res_r ψ)`. -/
theorem matrixHochschildHomotopy_succ_hochschildCoboundary_add (r : ι) (m : ℕ)
    (ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy r (m + 1) (hochschildCoboundary R (Matrix ι ι A) M (m + 1) ψ) +
        hochschildCoboundary R (Matrix ι ι A) M m (matrixHochschildHomotopy r m ψ) =
      ψ - matrixCochainExtension ι (m + 1) (matrixCochainSingleRestrict r (m + 1) ψ) := by
  ext a
  simp only [_root_.add_apply, _root_.sub_apply, matrixHochschildHomotopy_apply,
    hochschildCoboundary_apply]
  have hlhs :
      (∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin (k.val + 1) → ι,
          ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • ψ (hochschildFace i (homotopyTuple r k p a))) =
        ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) •
          ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) •
            ∑ p : Fin (k.val + 1) → ι, ψ (hochschildFace i (homotopyTuple r k p a)) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ (Finset.smul_sum).symm
  rw [hlhs]
  have hcomb := sum_simplicial_homotopy
    (fun (k : Fin (m + 2)) (i : Fin (m + 3)) ↦
      ∑ p : Fin (k.val + 1) → ι, ψ (hochschildFace i (homotopyTuple r k p a)))
    (fun (l : Fin (m + 1)) (j : Fin (m + 2)) ↦
      ∑ q : Fin (l.val + 1) → ι, ψ (homotopyTuple r l q (hochschildFace j a)))
    (fun l ↦ sum_hochschildFace_diag_homotopyTuple r l ψ a)
    (fun l j hj ↦ sum_hochschildFace_lt_homotopyTuple r l j hj ψ a)
    (fun l j hj ↦ Finset.sum_congr rfl fun p _ ↦ by
      rw [hochschildFace_gt_homotopyTuple r l j hj p a])
  rw [hcomb, sum_hochschildFace_zero_homotopyTuple_zero,
    sum_hochschildFace_last_homotopyTuple_last]

end HochschildHomotopy

/-! ### Matrix Morita invariance of Hochschild cohomology -/

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

/-- Corner restriction maps Hochschild cocycles to Hochschild cocycles. -/
theorem matrixCochainSingleRestrict_mem_hochschildCocycles [DecidableEq ι] {r : ι}
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCocycles R (Matrix ι ι A) M n) :
    matrixCochainSingleRestrict r n ψ ∈ hochschildCocycles R A M n := by
  rw [mem_hochschildCocycles_iff] at hψ ⊢
  rw [← matrixCochainSingleRestrict_hochschildCoboundary, hψ, map_zero]

/-- Corner restriction maps Hochschild coboundaries to Hochschild coboundaries. -/
theorem matrixCochainSingleRestrict_mem_hochschildCoboundaries [DecidableEq ι] {r : ι}
    {ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M}
    (hψ : ψ ∈ hochschildCoboundaries R (Matrix ι ι A) M n) :
    matrixCochainSingleRestrict r n ψ ∈ hochschildCoboundaries R A M n := by
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot] at hψ ⊢
    rw [hψ, map_zero]
  | succ n =>
    obtain ⟨χ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hψ
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨_, (matrixCochainSingleRestrict_hochschildCoboundary r n χ).symm⟩

end HochschildCocycles

namespace hochschildCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] {n : ℕ}

variable (M ι n) in
/-- The map `HHⁿ(A, Hom_R(A, M)) → HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))` on Hochschild
cohomology induced by matrix extension of Hochschild cocycles. -/
def matrixExtension :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCochainExtension ι n).restrict
      fun _ ↦ matrixCochainExtension_mem_hochschildCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2 (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends the class of a cocycle to the class of its
matrix extension. -/
@[simp]
theorem matrixExtension_mk (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCochainExtension ι n φ,
        matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

variable (M n) in
/-- The map `HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M)) → HHⁿ(A, Hom_R(A, M))` on Hochschild
cohomology induced by restricting cocycles to the `(r, r)` diagonal corner. -/
def singleRestrict [DecidableEq ι] (r : ι) :
    hochschildCohomology R (Matrix ι ι A) M n →ₗ[R] hochschildCohomology R A M n :=
  desc n (mk R A M n ∘ₗ (matrixCochainSingleRestrict r n).restrict
      fun _ ↦ matrixCochainSingleRestrict_mem_hochschildCocycles)
    fun _ hψ ↦ (mk_eq_zero_iff _ _ _ n _).2
      (matrixCochainSingleRestrict_mem_hochschildCoboundaries hψ)

/-- Corner restriction on Hochschild cohomology sends the class of a cocycle to the class of its
restriction to the `(r, r)` corner. -/
@[simp]
theorem singleRestrict_mk [DecidableEq ι] (r : ι)
    (ψ : hochschildCocycles R (Matrix ι ι A) M n) :
    singleRestrict M n r (mk R (Matrix ι ι A) M n ψ) =
      mk R A M n ⟨matrixCochainSingleRestrict r n ψ,
        matrixCochainSingleRestrict_mem_hochschildCocycles ψ.2⟩ :=
  desc_mk _ _ _ ψ

/-- Corner restriction is a left inverse to matrix extension on Hochschild cohomology. -/
@[simp]
theorem singleRestrict_comp_matrixExtension [DecidableEq ι] (r : ι) (n : ℕ) :
    singleRestrict (R := R) (A := A) M n r ∘ₗ matrixExtension M ι n = LinearMap.id := by
  ext φ
  simp

/-- Corner restriction followed after matrix extension is the identity on Hochschild classes. -/
@[simp]
theorem singleRestrict_matrixExtension [DecidableEq ι] (r : ι)
    (c : hochschildCohomology R A M n) :
    singleRestrict M n r (matrixExtension M ι n c) = c :=
  LinearMap.congr_fun (singleRestrict_comp_matrixExtension (R := R) (A := A) (M := M) r n) c

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] {n : ℕ}

/-- Matrix extension is a left inverse to corner restriction on Hochschild cohomology of a unital
algebra. -/
@[simp]
theorem matrixExtension_comp_singleRestrict [DecidableEq ι] (r : ι) (n : ℕ) :
    matrixExtension (R := R) (A := A) M ι n ∘ₗ singleRestrict M n r = LinearMap.id := by
  ext ψ
  simp only [LinearMap.comp_apply, singleRestrict_mk, matrixExtension_mk, LinearMap.id_apply]
  rw [mk_eq_mk_iff]
  have hψ : hochschildCoboundary R (Matrix ι ι A) M n ψ.1 = 0 := mem_hochschildCocycles_iff.1 ψ.2
  cases n with
  | zero =>
    rw [hochschildCoboundaries_zero, Submodule.mem_bot]
    have h := matrixHochschildHomotopy_zero_hochschildCoboundary r ψ.1
    rw [hψ, map_zero] at h
    exact sub_eq_zero.2 (sub_eq_zero.1 h.symm).symm
  | succ m =>
    refine mem_hochschildCoboundaries_succ_iff.2 ⟨-matrixHochschildHomotopy r m ψ.1, ?_⟩
    have h := matrixHochschildHomotopy_succ_hochschildCoboundary_add r m ψ.1
    rw [hψ, map_zero, zero_add] at h
    rw [map_neg, h, neg_sub]

/-- Matrix extension followed after corner restriction is the identity on Hochschild classes of a
unital algebra. -/
@[simp]
theorem matrixExtension_singleRestrict [DecidableEq ι] (r : ι)
    (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (singleRestrict M n r c) = c :=
  LinearMap.congr_fun (matrixExtension_comp_singleRestrict (R := R) (A := A) (M := M) r n) c

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital associative algebra `A`
over a commutative ring `R`, an `R`-module `M`, and a nonempty finite index type `ι`, matrix
extension induces a bijection
`HHⁿ(A, Hom_R(A, M)) → HHⁿ(M_ι(A), Hom_R(M_ι(A), M))` in every degree `n`. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.bijective_iff_has_inverse.2
    ⟨singleRestrict M n r, singleRestrict_matrixExtension r, matrixExtension_singleRestrict r⟩

/-- Corner restriction induces a bijection on Hochschild cohomology of a unital algebra. -/
theorem bijective_singleRestrict [DecidableEq ι] (r : ι) (n : ℕ) :
    Function.Bijective (singleRestrict (R := R) (A := A) M n r) :=
  Function.bijective_iff_has_inverse.2
    ⟨matrixExtension M ι n, matrixExtension_singleRestrict r, singleRestrict_matrixExtension r⟩

end Unital

section ConnesB

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix extension commutes with Connes' operator `B` on Hochschild cohomology. -/
theorem connesB_comp_matrixExtension (m : ℕ) :
    (connesB R (Matrix ι ι A) M m).hom ∘ₗ matrixExtension M ι (m + 1) =
      cyclicCohomology.matrixExtension M ι m ∘ₗ (connesB R A M m).hom := by
  ext φ
  simp only [LinearMap.comp_apply, matrixExtension_mk, connesB_mk,
    cyclicCohomology.matrixExtension_mk]
  congr 1
  exact Subtype.ext (Subtype.ext (by simp [matrixCochainExtension_connesB]))

end ConnesB

end hochschildCohomology

end TauCeti
