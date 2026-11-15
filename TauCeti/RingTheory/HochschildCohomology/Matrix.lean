/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Basis
public import TauCeti.RingTheory.CyclicCohomology.Matrix.Basic
public import TauCeti.RingTheory.HochschildCohomology.Complex
import TauCeti.Data.Fin.Basic

/-!
# Matrix Morita invariance of Hochschild cohomology

Extending an `M`-valued multilinear cochain `φ` on an `R`-algebra `A` to `Matrix ι ι A` by the
generalized matrix trace `φ ↦ φ#Tr` (`TauCeti.matrixCochainExtension`) commutes with the Hochschild
coboundary, so it maps Hochschild cocycles and coboundaries to Hochschild cocycles and coboundaries
and induces `TauCeti.hochschildCohomology.matrixExtension` on Hochschild cohomology. Pulling back
along the diagonal corner inclusion `Matrix.singleNonUnitalAlgHom R A r` is a left inverse in every
degree, without unitality of `A`.

When `A` is unital and `ι` is nonempty, matrix extension and corner pullback are mutually inverse on
Hochschild cohomology. Fix a reference index `r : ι`. Following the explicit chain homotopy of
Dennis, Igusa, and Loday (transposed to multilinear cochains), the degree-`n` cochain homotopy
`TauCeti.matrixHochschildHomotopy` sends an `(n + 1)`-cochain `Ψ` on `Matrix ι ι A` to the
alternating sum over `0 ≤ k ≤ n` and index paths `(p₀, …, pₖ₊₁)` of `Ψ` evaluated on
`(E_{p₀,r}(a₀(p₀,p₁)), E_{r,r}(a₁(p₁,p₂)), …, E_{r,r}(aₖ(pₖ,pₖ₊₁)), E_{r,pₖ₊₁}(1), aₖ₊₁, …, aₙ)`.
Its coboundary identity `b (h Ψ) + h (b Ψ) = Ψ - (Ψ ∘ E_{r,r})#Tr` exhibits `Ψ` as cohomologous to
the matrix extension of its `r`-corner restriction whenever `Ψ` is a Hochschild cocycle.

## Main definitions

* `TauCeti.matrixHochschildHomotopy`: the explicit cochain homotopy between the identity on
  Hochschild cochains of `Matrix ι ι A` and matrix extension of corner restriction.
* `TauCeti.hochschildCohomology.matrixExtension`: the linear map on Hochschild cohomology induced by
  `TauCeti.matrixCochainExtension`.
* `TauCeti.hochschildCohomology.matrixExtensionEquiv`: the resulting linear equivalence for a unital
  algebra `A` and nonempty finite index type `ι`.

## Main results

* `TauCeti.matrixHochschildHomotopy_hochschildCoboundary_zero` and
  `TauCeti.hochschildCoboundary_matrixHochschildHomotopy_add`: the cochain homotopy equations in
  degree zero and positive degree.
* `TauCeti.hochschildCohomology.bijective_matrixExtension`: matrix Morita invariance of Hochschild
  cohomology over any commutative ring.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* R. K. Dennis and K. Igusa, *Hochschild homology and the second obstruction for pseudoisotopy*,
  Lecture Notes in Math. **966**, Springer (1982).
* J.-L. Loday, *Cyclic Homology*, §1.2, Theorem 1.2.4.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti

/-! ### Hochschild cocycles and coboundaries under matrix extension -/

section Cocycles

variable {R A M ι : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] [Fintype ι] {n : ℕ}

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
      ⟨matrixCochainExtension ι n ψ, (matrixCochainExtension_hochschildCoboundary ι n ψ).symm⟩

end Cocycles

/-! ### Double-sum decomposition on `Fin (n + 2)` -/

/-- Partitioning a double sum on `Fin (n + 2) × Fin (n + 2)` into `(0, 0)`, the adjacent pairs
`(k + 1, k + 1)` and `(k, k + 1)`, and the strict off-diagonal pairs `i ≤ k` (at `(k + 1, i)`)
together with `k < i` (at `(k, i + 1)`). -/
private theorem sum_fin_succ_succ_eq {M : Type*} [AddCommMonoid M] :
    ∀ (n : ℕ) (F : Fin (n + 2) → Fin (n + 2) → M),
      ∑ k : Fin (n + 2), ∑ i : Fin (n + 2), F k i =
        F 0 0 +
          ∑ k : Fin (n + 1), (F k.succ k.succ + F k.castSucc k.succ) +
          ∑ k : Fin (n + 1), ∑ i : Fin (n + 1),
            if i ≤ k then F k.succ i.castSucc else F k.castSucc i.succ
  | 0, F => by
    simp [Fin.sum_univ_two]
    abel
  | n + 1, F => by
    -- Peel the last row `k = Fin.last (n + 2)` and last column `i = Fin.last (n + 2)`.
    rw [Fin.sum_univ_castSucc]
    simp_rw [Fin.sum_univ_castSucc (n := n + 2)]
    rw [Finset.sum_add_distrib, sum_fin_succ_succ_eq n (fun k i ↦ F k.castSucc i.castSucc)]
    rw [Fin.sum_univ_castSucc (f := fun k : Fin (n + 2) ↦ F k.castSucc (Fin.last (n + 2)))]
    rw [Fin.sum_univ_castSucc (f := fun i : Fin (n + 2) ↦ F (Fin.last (n + 2)) i.castSucc)]
    rw [Fin.sum_univ_castSucc (n := n + 1)
      (f := fun k ↦ F k.succ k.succ + F k.castSucc k.succ)]
    rw [Fin.sum_univ_castSucc (n := n + 1)
      (f := fun k ↦ ∑ i : Fin (n + 2), if i ≤ k then F k.succ i.castSucc else F k.castSucc i.succ)]
    simp_rw [Fin.sum_univ_castSucc (n := n + 1)
      (f := fun i ↦ if i ≤ _ then _ else _)]
    simp only [Finset.sum_add_distrib, Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last,
      Fin.le_last, Fin.castSucc_le_castSucc_iff, ↓reduceIte]
    have hlt (k : Fin (n + 1)) : ¬ Fin.last (n + 1) ≤ k.castSucc :=
      not_le.2 (Fin.castSucc_lt_last k)
    simp only [hlt, ↓reduceIte]
    abel

/-! ### The cochain homotopy on matrix Hochschild cochains -/

section Homotopy

variable {R A M ι : Type*} [Semiring R] [NonAssocSemiring A] [Module R A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M] [DecidableEq ι]

/-- The `(n + 2)`-tuple `(E_{p₀,r}(a₀(p₀,p₁)), E_{r,r}(a₁(p₁,p₂)), …, E_{r,r}(aₖ(pₖ,pₖ₊₁)),
E_{r,pₖ₊₁}(1), aₖ₊₁, …, aₙ)` appearing in the `k`-th step of the matrix Hochschild homotopy. -/
private def homotopyTuple {A ι : Type*} [Zero A] [One A] [DecidableEq ι] (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (a : Fin (n + 1) → Matrix ι ι A) (p : Fin ((k : ℕ) + 2) → ι)
    (m : Fin (n + 2)) : Matrix ι ι A :=
  if hm : (m : ℕ) ≤ k then
    Matrix.single (if (m : ℕ) = 0 then p 0 else r) r
      (a ⟨m, by omega⟩ (p ⟨m, by omega⟩) (p ⟨(m : ℕ) + 1, by omega⟩))
  else if (m : ℕ) = (k : ℕ) + 1 then
    Matrix.single r (p (Fin.last ((k : ℕ) + 1))) 1
  else
    a ⟨(m : ℕ) - 1, by omega⟩

private theorem homotopyTuple_of_le {A ι : Type*} [Zero A] [One A] [DecidableEq ι] (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (a : Fin (n + 1) → Matrix ι ι A) (p : Fin ((k : ℕ) + 2) → ι)
    {m : Fin (n + 2)} (hm : (m : ℕ) ≤ k) :
    homotopyTuple r k a p m =
      Matrix.single (if (m : ℕ) = 0 then p 0 else r) r
        (a ⟨m, by omega⟩ (p ⟨m, by omega⟩) (p ⟨(m : ℕ) + 1, by omega⟩)) := by
  simp only [homotopyTuple, hm, ↓reduceDIte]

private theorem homotopyTuple_succ_self {A ι : Type*} [Zero A] [One A] [DecidableEq ι] (r : ι)
    {n : ℕ} (k : Fin (n + 1)) (a : Fin (n + 1) → Matrix ι ι A) (p : Fin ((k : ℕ) + 2) → ι) :
    homotopyTuple r k a p k.succ = Matrix.single r (p (Fin.last ((k : ℕ) + 1))) 1 := by
  simp [homotopyTuple]

private theorem homotopyTuple_of_gt {A ι : Type*} [Zero A] [One A] [DecidableEq ι] (r : ι) {n : ℕ}
    (k : Fin (n + 1)) (a : Fin (n + 1) → Matrix ι ι A) (p : Fin ((k : ℕ) + 2) → ι)
    {m : Fin (n + 2)} (hm : (k : ℕ) + 1 < m) :
    homotopyTuple r k a p m = a ⟨(m : ℕ) - 1, by omega⟩ := by
  have h1 : ¬ (m : ℕ) ≤ k := by omega
  have h2 : (m : ℕ) ≠ (k : ℕ) + 1 := by omega
  simp only [homotopyTuple, h1, h2, ↓reduceDIte, ↓reduceIte]

/-- The slotwise linear maps in `a₀, …, aₙ` before inserting `E_{r,pₖ₊₁}(1)` at position `k + 1`. -/
private def homotopySlotLinearMap (r : ι) {n : ℕ} (k : Fin (n + 1))
    (p : Fin ((k : ℕ) + 2) → ι) (j : Fin (n + 1)) :
    Matrix ι ι A →ₗ[R] Matrix ι ι A :=
  if hj : (j : ℕ) ≤ k then
    Matrix.singleLinearMap R (if (j : ℕ) = 0 then p 0 else r) r ∘ₗ
      Matrix.entryLinearMap R A (p ⟨j, by omega⟩) (p ⟨(j : ℕ) + 1, by omega⟩)
  else
    LinearMap.id

private theorem insertNth_homotopySlotLinearMap (r : ι) {n : ℕ} (k : Fin (n + 1))
    (a : Fin (n + 1) → Matrix ι ι A) (p : Fin ((k : ℕ) + 2) → ι) :
    k.succ.insertNth (Matrix.single r (p (Fin.last ((k : ℕ) + 1))) 1)
        (fun j ↦ homotopySlotLinearMap (R := R) r k p j (a j)) =
      homotopyTuple r k a p := by
  funext m
  refine Fin.succAboveCases k.succ (by simp [homotopyTuple_succ_self]) (fun j ↦ ?_) m
  rw [Fin.insertNth_apply_succAbove]
  by_cases hj : (j : ℕ) ≤ k
  · have hsucc : k.succ.succAbove j = j.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.2 hj)
    rw [hsucc, homotopyTuple_of_le r k a p hj]
    simp [homotopySlotLinearMap, hj]
  · have hsucc : k.succ.succAbove j = j.succ :=
      Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.2 (lt_of_not_ge hj))
    rw [hsucc, homotopyTuple_of_gt r k a p (by simp; omega)]
    simp [homotopySlotLinearMap, hj]

variable [Fintype ι]

/-- Single-path summand of `matrixHochschildHomotopyStep`. -/
private def matrixHochschildHomotopyStepSummand (r : ι) {n : ℕ} (k : Fin (n + 1))
    (p : Fin ((k : ℕ) + 2) → ι)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  (MultilinearMap.mk'
    (fun m ↦ Ψ (k.succ.insertNth (Matrix.single r (p (Fin.last ((k : ℕ) + 1))) (1 : A)) m))
    (fun m i x y ↦ by simp [Fin.insertNth_update])
    (fun m i c x ↦ by simp [Fin.insertNth_update])).compLinearMap
    (homotopySlotLinearMap (R := R) r k p)

/-- The `k`-th unsigned step of the matrix Hochschild cochain homotopy. -/
private def matrixHochschildHomotopyStep (r : ι) (n : ℕ) (k : Fin (n + 1)) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M where
  toFun Ψ := ∑ p : Fin ((k : ℕ) + 2) → ι, matrixHochschildHomotopyStepSummand r k p Ψ
  map_add' Ψ Φ := by
    ext a
    simp [matrixHochschildHomotopyStepSummand, Finset.sum_add_distrib]
  map_smul' c Ψ := by
    ext a
    simp [matrixHochschildHomotopyStepSummand, Finset.smul_sum]

private theorem matrixHochschildHomotopyStep_apply (r : ι) (n : ℕ) (k : Fin (n + 1))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r n k Ψ a =
      ∑ p : Fin ((k : ℕ) + 2) → ι, Ψ (homotopyTuple r k a p) := by
  simp only [matrixHochschildHomotopyStep, LinearMap.coe_mk, AddHom.coe_mk, sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg Ψ (insertNth_homotopySlotLinearMap r k a p)

/-- The explicit cochain homotopy `Cⁿ⁺¹(Matrix ι ι A; M) → Cⁿ(Matrix ι ι A; M)` contracting the
Hochschild cochain complex of `Matrix ι ι A` onto the matrix-extended cochains from corner `r`. -/
def matrixHochschildHomotopy (r : ι) (n : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • matrixHochschildHomotopyStep r n k

private theorem matrixHochschildHomotopy_apply (r : ι) (n : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixHochschildHomotopy r n Ψ a =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        ∑ p : Fin ((k : ℕ) + 2) → ι, Ψ (homotopyTuple r k a p) := by
  simp [matrixHochschildHomotopy, matrixHochschildHomotopyStep_apply]

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Evaluate `(b Ψ)(E_{p₀,r}(a₀(p₀,p₁)), E_{r,p₁}(1))` for a `0`-cochain `Ψ`. -/
private theorem hochschildCoboundary_zero_homotopyTuple (r : ι)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M)
    (a : Fin 1 → Matrix ι ι A) (p : Fin 2 → ι) :
    hochschildCoboundary R (Matrix ι ι A) M 0 Ψ (homotopyTuple r 0 a p) =
      Ψ (fun _ ↦ Matrix.single (p 0) (p 1) (a 0 (p 0) (p 1))) -
        if p 1 = p 0 then Ψ (fun _ ↦ Matrix.single r r (a 0 (p 0) (p 0))) else 0 := by
  rw [hochschildCoboundary_apply, Fin.sum_univ_two]
  have h0 : homotopyTuple r 0 a p 0 = Matrix.single (p 0) r (a 0 (p 0) (p 1)) := by
    simp [homotopyTuple]
  have h1 : homotopyTuple r 0 a p 1 = Matrix.single r (p 1) (1 : A) :=
    homotopyTuple_succ_self r 0 a p
  have hf0 : hochschildFace 0 (homotopyTuple r 0 a p) =
      fun _ ↦ Matrix.single (p 0) (p 1) (a 0 (p 0) (p 1)) := by
    ext m; rw [Fin.eq_zero m, ← Fin.castSucc_zero, hochschildFace_castSucc]
    simp [Fin.contractNth, h0, h1, Matrix.single_mul_single_same]
  have hf1 : hochschildFace 1 (homotopyTuple r 0 a p) =
      fun _ ↦ if p 1 = p 0 then Matrix.single r r (a 0 (p 0) (p 0)) else 0 := by
    funext m
    have hlast : (1 : Fin 2) = Fin.last 1 := Fin.ext (by simp)
    rw [Fin.eq_zero m, hlast, hochschildFace_last, Fin.cons_zero, ← hlast, h1, h0]
    split_ifs with hp
    · rw [hp, Matrix.single_mul_single_same, one_mul]
    · simp [Matrix.single_mul_single_of_ne, hp]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_one_smul, hf0, hf1, sub_eq_add_neg]
  congr 1; split_ifs with hp
  · simp
  · rw [Ψ.map_coord_zero 0 (by simp), neg_zero]

/-- Degree-zero cochain homotopy identity: `h₀ (b Ψ) = Ψ - (Ψ ∘ E_{r,r})#Tr`. -/
theorem matrixHochschildHomotopy_hochschildCoboundary_zero (r : ι)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin 1 ↦ Matrix ι ι A) M) :
    matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 Ψ) =
      Ψ - matrixCochainExtension ι 0 (Ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r) := by
  ext a
  have hupd (x : Matrix ι ι A) : Function.update a 0 x = fun _ ↦ x :=
    funext fun m ↦ by rw [Fin.eq_zero m, Function.update_self]
  have h0 : matrixHochschildHomotopy r 0 (hochschildCoboundary R (Matrix ι ι A) M 0 Ψ) a =
      ∑ p : Fin 2 → ι, hochschildCoboundary R (Matrix ι ι A) M 0 Ψ (homotopyTuple r 0 a p) := by
    rw [matrixHochschildHomotopy_apply, Fin.sum_univ_one]
    -- For `0 : Fin 1`, the sign `(-1) ^ ↑0` is `1` and `Fin (↑0 + 2)` is definitionally `Fin 2`.
    exact one_smul ℤ _
  rw [h0, sub_apply, matrixCochainExtension_apply]
  simp only [hochschildCoboundary_zero_homotopyTuple, Finset.sum_sub_distrib,
    MultilinearMap.compLinearMap_apply, Matrix.singleLinearMap_apply]
  rw [← (Fin.consEquiv (fun _ : Fin 2 ↦ ι)).sum_comp, Fintype.sum_prod_type]
  rw [← (Fin.consEquiv (fun _ : Fin 2 ↦ ι)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_one]
  congr 1
  · conv_rhs => rw [← Function.update_eq_self 0 a, Matrix.matrix_eq_sum_single (a 0),
      Ψ.map_update_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Ψ.map_update_sum, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [hupd]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact congrArg Ψ (funext fun i ↦ by rw [Fin.eq_zero i, Fin.eq_zero (finRotate 1 0)])

/-! #### The six coface regimes in positive degree -/

private theorem insertNth_succ_apply_of_le {ι : Type*} {n : ℕ} {i k : Fin (n + 1)} (hik : i ≤ k)
    (q : Fin ((k : ℕ) + 2) → ι) (s : ι) {u : ℕ} (hu : u ≤ i) :
    Fin.insertNth (α := fun _ ↦ ι)
        ⟨(i : ℕ) + 1, by have := Fin.le_def.mp hik; have := Fin.val_succ k; omega⟩ s q
        ⟨u, by have := Fin.le_def.mp hik; have := Fin.val_succ k; omega⟩ =
      q ⟨u, by have := Fin.le_def.mp hik; omega⟩ := by
  have : (i : ℕ) ≤ (k : ℕ) := Fin.le_def.mp hik
  have : (k.succ : ℕ) = (k : ℕ) + 1 := Fin.val_succ k
  let pi1 : Fin ((k.succ : ℕ) + 2) := ⟨(i : ℕ) + 1, by omega⟩
  have hsucc : pi1.succAbove ⟨u, by omega⟩ = ⟨u, by omega⟩ :=
    Fin.succAbove_of_castSucc_lt pi1 ⟨u, by omega⟩ (by rw [Fin.lt_def]; simp [pi1]; omega)
  simpa [pi1, hsucc] using Fin.insertNth_apply_succAbove (α := fun _ ↦ ι) pi1 s q ⟨u, by omega⟩

private theorem insertNth_succ_apply_of_gt {ι : Type*} {n : ℕ} {i k : Fin (n + 1)} (hik : i ≤ k)
    (q : Fin ((k : ℕ) + 2) → ι) (s : ι) {u : ℕ} (hu : i < u) (huk : u ≤ (k : ℕ) + 1) :
    Fin.insertNth (α := fun _ ↦ ι)
        ⟨(i : ℕ) + 1, by have := Fin.le_def.mp hik; have := Fin.val_succ k; omega⟩ s q
        ⟨u + 1, by have := Fin.val_succ k; omega⟩ =
      q ⟨u, by omega⟩ := by
  have : (i : ℕ) ≤ (k : ℕ) := Fin.le_def.mp hik
  have : (k.succ : ℕ) = (k : ℕ) + 1 := Fin.val_succ k
  let pi1 : Fin ((k.succ : ℕ) + 2) := ⟨(i : ℕ) + 1, by omega⟩
  have hsucc : pi1.succAbove ⟨u, by omega⟩ = ⟨u + 1, by omega⟩ :=
    Fin.succAbove_of_le_castSucc pi1 ⟨u, by omega⟩ (by rw [Fin.le_def]; simp [pi1]; omega)
  simpa [pi1, hsucc] using Fin.insertNth_apply_succAbove (α := fun _ ↦ ι) pi1 s q ⟨u, by omega⟩

/-- Regime A (`i ≤ k`): inserting an intermediate index `s` at position `i + 1` of `q` contracts
the adjacent matrix units in slots `i` and `i + 1`. -/
private theorem update_homotopyTuple_hochschildFace_of_le {A ι : Type*} [NonAssocSemiring A]
    [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ} {i k : Fin (n + 1)} (hik : i ≤ k)
    (a : Fin (n + 2) → Matrix ι ι A) (q : Fin ((k : ℕ) + 2) → ι) (s : ι) :
    let qi : Fin ((k : ℕ) + 2) := ⟨i, by omega⟩
    let qi1 : Fin ((k : ℕ) + 2) := ⟨(i : ℕ) + 1, by omega⟩
    let pi1 : Fin ((k.succ : ℕ) + 2) := ⟨(i : ℕ) + 1, by simp; omega⟩
    Function.update (homotopyTuple r k (hochschildFace i.castSucc a) q) i.castSucc
        (Matrix.single (if (i : ℕ) = 0 then q 0 else r) r
          (a i.castSucc (q qi) s * a i.succ s (q qi1))) =
      hochschildFace i.castSucc.castSucc
        (homotopyTuple r k.succ a (Fin.insertNth (α := fun _ ↦ ι) pi1 s q)) := by
  intro qi qi1 pi1
  let p := Fin.insertNth (α := fun _ ↦ ι) pi1 s q
  have hksucc : (k.succ : ℕ) = (k : ℕ) + 1 := Fin.val_succ k
  have hp0 : p 0 = q 0 := insertNth_succ_apply_of_le hik q s (u := 0) (Nat.zero_le _)
  funext m
  conv_rhs => rw [hochschildFace_castSucc]
  rcases lt_trichotomy (m : ℕ) i with hm | hm | hm
  · rw [Function.update_of_ne (Fin.ne_of_lt hm),
      Fin.contractNth_apply_of_lt _ _ _ _ (by simp [hm]),
      homotopyTuple_of_le r k _ q (by omega), homotopyTuple_of_le r k.succ a p (by simp; omega)]
    simp [hochschildFace_castSucc,
      Fin.contractNth_apply_of_lt i.castSucc _ a ⟨m, by omega⟩ (by simp [hm]), hp0,
      p, pi1, insertNth_succ_apply_of_le hik q s (u := m) (by omega),
      insertNth_succ_apply_of_le hik q s (u := (m : ℕ) + 1) (Nat.succ_le_of_lt hm)]
  · obtain rfl : m = i.castSucc := Fin.ext hm
    rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
      homotopyTuple_of_le r k.succ a p (by simp; omega),
      homotopyTuple_of_le r k.succ a p (by simp; omega)]
    have hp_eq : p ⟨(i : ℕ) + 1, by omega⟩ = s := Fin.insertNth_apply_same (α := fun _ ↦ ι) pi1 s q
    simp only [qi, qi1, Fin.val_castSucc, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, hp0,
      hp_eq, Matrix.single_mul_single_same, p, pi1, insertNth_succ_apply_of_le hik q s le_rfl,
      insertNth_succ_apply_of_gt hik q s (Nat.lt_succ_self i) (by omega)]
    rw [show (⟨i, _⟩ : Fin (n + 2)) = i.castSucc from Fin.ext (by simp),
      show (⟨(i : ℕ) + 1, _⟩ : Fin (n + 2)) = i.succ from Fin.ext (by simp)]
  · rw [Function.update_of_ne (Fin.ne_of_gt hm),
      Fin.contractNth_apply_of_gt _ _ _ _ (by simp [hm])]
    rcases lt_trichotomy (m : ℕ) ((k : ℕ) + 1) with hmk | hmk | hmk
    · rw [homotopyTuple_of_le r k _ q (by omega),
        homotopyTuple_of_le r k.succ a p (by simp; omega)]
      have hm0 : (m : ℕ) ≠ 0 := by omega
      simp [hm0, hochschildFace_castSucc,
        Fin.contractNth_apply_of_gt i.castSucc _ a ⟨m, by omega⟩ (by simp [hm]),
        p, pi1, insertNth_succ_apply_of_gt hik q s hm (by omega),
        insertNth_succ_apply_of_gt hik q s (u := (m : ℕ) + 1) (by omega) (by omega)]
    · rw [show m.succ = k.succ.succ from Fin.ext (by simp [hmk]), homotopyTuple_succ_self,
        show m = k.succ from Fin.ext hmk, homotopyTuple_succ_self]
      congr 1
      simpa [Fin.last, hksucc] using (insertNth_succ_apply_of_gt hik q s (by omega) le_rfl).symm
    · rw [homotopyTuple_of_gt r k _ q hmk, homotopyTuple_of_gt r k.succ a p (by simp; omega),
        hochschildFace_castSucc, Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
      exact congrArg a (Fin.ext (by simp; omega))

/-- Regime A sum identity (`i ≤ k`). -/
private theorem step_hochschildCoface_of_le (r : ι) {n : ℕ} {i k : Fin (n + 1)} (hik : i ≤ k)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r (n + 1) k.succ
        (hochschildCoface R (Matrix ι ι A) M i.castSucc.castSucc Ψ) a =
      matrixHochschildHomotopyStep r n k Ψ (hochschildFace i.castSucc a) := by
  let qi : Fin ((k : ℕ) + 2) := ⟨i, by omega⟩
  let qi1 : Fin ((k : ℕ) + 2) := ⟨(i : ℕ) + 1, by omega⟩
  let pi1 : Fin ((k.succ : ℕ) + 2) := ⟨(i : ℕ) + 1, by simp; omega⟩
  rw [matrixHochschildHomotopyStep_apply, matrixHochschildHomotopyStep_apply]
  simp only [hochschildCoface_apply]
  rw [← (Fin.insertNthEquiv (fun _ : Fin ((k.succ : ℕ) + 2) ↦ ι) pi1).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hupd : homotopyTuple r k (hochschildFace i.castSucc a) q =
      Function.update (homotopyTuple r k (hochschildFace i.castSucc a) q) i.castSucc
        (∑ s : ι, Matrix.single (if (i : ℕ) = 0 then q 0 else r) r
          (a i.castSucc (q qi) s * a i.succ s (q qi1))) := by
    rw [eq_comm, Function.update_eq_self_iff, homotopyTuple_of_le r k _ q hik]
    simp only [Fin.val_castSucc, hochschildFace_castSucc,
      Fin.contractNth_apply_of_eq i.castSucc _ a i rfl, Matrix.mul_apply]
    exact (map_sum (Matrix.singleLinearMap R (if (i : ℕ) = 0 then q 0 else r) r) _ _).symm
  conv_rhs => rw [hupd, Ψ.map_update_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Fin.insertNthEquiv_apply, ← update_homotopyTuple_hochschildFace_of_le r hik a q s]

/-- Regime B at `k = 0`: the zeroth coface of the `k = 0` step recovers `Ψ a`. -/
private theorem step_zero_hochschildCoface_zero (r : ι) {n : ℕ}
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r (n + 1) 0
        (hochschildCoface R (Matrix ι ι A) M 0 Ψ) a = Ψ a := by
  rw [matrixHochschildHomotopyStep_apply]
  simp only [hochschildCoface_apply]
  let e : (Fin (((0 : Fin (n + 2)) : ℕ) + 2) → ι) ≃ (Fin 2 → ι) :=
    Equiv.arrowCongr (finCongr (by simp)) (Equiv.refl ι)
  have he (p : Fin 2 → ι) :
      homotopyTuple r (0 : Fin (n + 2)) a (e.symm p) =
        homotopyTuple r (0 : Fin (n + 2)) a p := by
    refine congrArg (homotopyTuple r (0 : Fin (n + 2)) a) (funext fun u ↦ ?_)
    simp only [e, Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, finCongr_symm]
    exact congrArg p (Fin.ext (by rw [finCongr_apply, Fin.val_cast]))
  rw [← e.symm.sum_comp]
  simp_rw [he]
  have hface (p : Fin 2 → ι) :
      hochschildFace 0 (homotopyTuple r 0 a p) =
        Function.update a 0 (Matrix.single (p 0) (p 1) (a 0 (p 0) (p 1))) := by
    funext m
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    refine Fin.cases ?_ (fun m' ↦ ?_) m
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Function.update_self,
        homotopyTuple_of_le r 0 a p (by simp), homotopyTuple_succ_self r 0 a p]
      simp only [Fin.val_castSucc, Fin.val_zero, ↓reduceIte, zero_add, Fin.mk_zero, Fin.mk_one,
        Fin.last, Matrix.single_mul_single_same, mul_one]
      congr 1
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (Fin.succ_pos m'),
        Function.update_of_ne (Fin.succ_ne_zero m'),
        homotopyTuple_of_gt r 0 a p (by simp)]
      exact congrArg a (Fin.ext (by simp))
  simp_rw [hface]
  rw [← (Fin.consEquiv (fun _ : Fin 2 ↦ ι)).sum_comp, Fintype.sum_prod_type]
  conv_rhs => rw [← Function.update_eq_self 0 a, Matrix.matrix_eq_sum_single (a 0),
    Ψ.map_update_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Ψ.map_update_sum, ← (Equiv.funUnique (Fin 1) ι).sum_comp]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  simp [Equiv.funUnique_apply]

/-- Tuple-level identity for Regimes B & C: appending `s` to `q` updates slot `k + 1` of the
contracted `k`-th homotopy tuple. -/
private theorem hochschildFace_succ_homotopyTuple_snoc {A ι : Type*} [NonAssocSemiring A]
    [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ} (k : Fin (n + 1)) (a : Fin (n + 2) → Matrix ι ι A)
    (q : Fin ((k.castSucc : ℕ) + 2) → ι) (s : ι) :
    hochschildFace k.succ.castSucc
        (homotopyTuple r k.succ a ((Fin.snocEquiv fun _ : Fin ((k.succ : ℕ) + 2) ↦ ι) (s, q))) =
      Function.update (hochschildFace k.succ.castSucc (homotopyTuple r k.castSucc a q)) k.succ
        (Matrix.single r s (a k.succ (q (Fin.last ((k : ℕ) + 1))) s)) := by
  let pq := Fin.snoc (α := fun _ ↦ ι) q s
  have hksucc : (k.succ : ℕ) = (k : ℕ) + 1 := Fin.val_succ k
  have hkcast : (k.castSucc : ℕ) = (k : ℕ) := Fin.val_castSucc k
  funext m
  simp only [Fin.snocEquiv_apply, hochschildFace_castSucc]
  rcases lt_trichotomy (m : ℕ) ((k : ℕ) + 1) with hm | hm | hm
  · rw [Function.update_of_ne (Fin.ne_of_lt hm),
      Fin.contractNth_apply_of_lt _ _ _ _ (by simp [hm]),
      Fin.contractNth_apply_of_lt _ _ _ _ (by simp [hm]),
      homotopyTuple_of_le r k.succ a pq (by simp; omega),
      homotopyTuple_of_le r k.castSucc a q (by simp; omega)]
    have hsnoc1 : Fin.snoc (α := fun _ ↦ ι) q s ⟨m, by omega⟩ = q ⟨m, by simp; omega⟩ :=
      Fin.snoc_castSucc (α := fun _ ↦ ι) s q ⟨m, by simp; omega⟩
    have hsnoc2 : Fin.snoc (α := fun _ ↦ ι) q s ⟨(m : ℕ) + 1, by omega⟩ =
        q ⟨(m : ℕ) + 1, by simp; omega⟩ :=
      Fin.snoc_castSucc (α := fun _ ↦ ι) s q ⟨(m : ℕ) + 1, by simp; omega⟩
    simp only [pq, Fin.val_castSucc, Fin.snoc_apply_zero]
    rw [hsnoc1, hsnoc2]
  · obtain rfl : m = k.succ := Fin.ext hm
    rw [Function.update_self, Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
      homotopyTuple_of_le r k.succ a pq (by simp), homotopyTuple_succ_self r k.succ a pq]
    have h1 : Fin.snoc (α := fun _ ↦ ι) q s ⟨(k : ℕ) + 1, by omega⟩ =
        q ⟨(k : ℕ) + 1, by omega⟩ :=
      Fin.snoc_castSucc (α := fun _ ↦ ι) s q ⟨(k : ℕ) + 1, by omega⟩
    have h2 : Fin.snoc (α := fun _ ↦ ι) q s ⟨(k : ℕ) + 1 + 1, by omega⟩ = s := by
      simpa [Fin.last, hksucc] using Fin.snoc_last (α := fun _ ↦ ι) s q
    simp only [pq, Fin.val_castSucc, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte,
      Fin.snoc_last, Matrix.single_mul_single_same, mul_one]
    rw [h1, h2]
    congr 2
  · rw [Function.update_of_ne (Fin.ne_of_gt hm),
      Fin.contractNth_apply_of_gt _ _ _ _ (by simp [hm]),
      Fin.contractNth_apply_of_gt _ _ _ _ (by simp [hm]),
      homotopyTuple_of_gt r k.succ a pq (by simp; omega),
      homotopyTuple_of_gt r k.castSucc a q (by simp; omega)]

/-- Regimes B & C (`1 ≤ k + 1 ≤ n + 1`): the `(k + 1)`-st coface agrees on steps `k + 1` and `k`. -/
private theorem step_succ_hochschildCoface_succ_eq_step_castSucc (r : ι) {n : ℕ} (k : Fin (n + 1))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r (n + 1) k.succ
        (hochschildCoface R (Matrix ι ι A) M k.succ.castSucc Ψ) a =
      matrixHochschildHomotopyStep r (n + 1) k.castSucc
        (hochschildCoface R (Matrix ι ι A) M k.succ.castSucc Ψ) a := by
  rw [matrixHochschildHomotopyStep_apply, matrixHochschildHomotopyStep_apply]
  simp only [hochschildCoface_apply]
  rw [← (Fin.snocEquiv (fun _ : Fin ((k.succ : ℕ) + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hsum : hochschildFace k.succ.castSucc (homotopyTuple r k.castSucc a q) =
      Function.update (hochschildFace k.succ.castSucc (homotopyTuple r k.castSucc a q)) k.succ
        (∑ s : ι, Matrix.single r s (a k.succ (q (Fin.last ((k : ℕ) + 1))) s)) := by
    rw [eq_comm, Function.update_eq_self_iff, hochschildFace_castSucc,
      Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    have hleft : homotopyTuple r k.castSucc a q k.succ.castSucc =
        Matrix.single r (q (Fin.last ((k : ℕ) + 1))) 1 :=
      homotopyTuple_succ_self r k.castSucc a q
    have hright : homotopyTuple r k.castSucc a q k.succ.succ = a k.succ :=
      homotopyTuple_of_gt r k.castSucc a q (by simp)
    rw [hleft, hright, Matrix.single_mul_eq_sum_single]
    simp
  conv_rhs => rw [hsum, Ψ.map_update_sum]
  exact Finset.sum_congr rfl fun s _ ↦ congrArg Ψ (hochschildFace_succ_homotopyTuple_snoc r k a q s)

/-- Tuple-level identity for Regime D on closed cyclic index paths (`s = q 0`). -/
private theorem hochschildFace_last_homotopyTuple_snoc_self {A ι : Type*} [NonAssocSemiring A]
    [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ} (a : Fin (n + 2) → Matrix ι ι A)
    (q : Fin (n + 2) → ι) :
    hochschildFace (Fin.last (n + 2))
        (homotopyTuple r (Fin.last (n + 1)) a (Fin.snoc (α := fun _ ↦ ι) q (q 0))) =
      fun m ↦ Matrix.single r r (a m (q m) (q (finRotate (n + 2) m))) := by
  let pq := Fin.snoc (α := fun _ ↦ ι) q (q 0)
  funext m
  rw [hochschildFace_last]
  refine Fin.cases ?_ (fun m' ↦ ?_) m
  · simp only [Fin.cons_zero]
    rw [← Fin.succ_last (n + 1), homotopyTuple_succ_self r (Fin.last (n + 1)) a pq,
      homotopyTuple_of_le r (Fin.last (n + 1)) a pq (by simp)]
    simp only [pq, Fin.val_zero, ↓reduceIte, zero_add, Fin.val_last, Fin.snoc_last,
      Fin.mk_zero, Fin.snoc_apply_zero, Fin.mk_one,
      Matrix.single_mul_single_same, one_mul]
    rw [show (1 : Fin (n + 3)) = (0 : Fin (n + 1)).succ.castSucc from Fin.ext (by simp),
      Fin.snoc_castSucc, ← Fin.castSucc_zero (n := n + 1), Fin.finRotate_castSucc,
      Fin.succ_zero_eq_one]
  · simp only [Fin.cons_succ]
    refine Fin.lastCases ?_ (fun j ↦ ?_) m'
    · rw [homotopyTuple_of_le r (Fin.last (n + 1)) a pq (by simp)]
      have hp1 : pq ⟨n + 1, by omega⟩ = q (Fin.last (n + 1)) :=
        Fin.snoc_castSucc (α := fun _ ↦ ι) (q 0) q (Fin.last (n + 1))
      have hp2 : pq ⟨n + 1 + 1, by omega⟩ = q 0 :=
        Fin.snoc_last (α := fun _ ↦ ι) (q 0) q
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, Nat.add_one_ne_zero, ↓reduceIte,
        hp1, hp2, Fin.succ_last, finRotate_last]
      congr 2
    · rw [homotopyTuple_of_le r (Fin.last (n + 1)) a pq (by simp)]
      have hp1 : pq ⟨(j : ℕ) + 1, by omega⟩ = q j.succ.castSucc :=
        Fin.snoc_castSucc (α := fun _ ↦ ι) (q 0) q j.succ.castSucc
      have hp2 : pq ⟨(j : ℕ) + 1 + 1, by omega⟩ = q j.succ.succ :=
        Fin.snoc_castSucc (α := fun _ ↦ ι) (q 0) q j.succ.succ
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_one_ne_zero, ↓reduceIte, hp1, hp2,
        Fin.succ_castSucc, Fin.finRotate_castSucc]
      congr 2

/-- Regime D (`k = n + 1, j = n + 2`): the last coface of the last step recovers the matrix
extension of the `r`-corner restriction of `Ψ`. -/
private theorem step_last_hochschildCoface_last (r : ι) {n : ℕ}
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r (n + 1) (Fin.last (n + 1))
        (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 2)) Ψ) a =
      matrixCochainExtension ι (n + 1)
        (Ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r) a := by
  rw [matrixHochschildHomotopyStep_apply, matrixCochainExtension_apply]
  simp only [hochschildCoface_apply, MultilinearMap.compLinearMap_apply,
    Matrix.singleLinearMap_apply]
  let e : (Fin (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) + 2) → ι) ≃ (Fin (n + 3) → ι) :=
    Equiv.arrowCongr (finCongr (by simp)) (Equiv.refl ι)
  have he (p : Fin (n + 3) → ι) :
      homotopyTuple r (Fin.last (n + 1)) a (e.symm p) = homotopyTuple r (Fin.last (n + 1)) a p := by
    refine congrArg (homotopyTuple r (Fin.last (n + 1)) a) (funext fun u ↦ ?_)
    simp only [e, Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, finCongr_symm]
    exact congrArg p (Fin.ext (by simp))
  rw [← e.symm.sum_comp]
  simp_rw [he]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 3) ↦ ι)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_eq_single (q 0)]
  · simp [Fin.snocEquiv_apply, hochschildFace_last_homotopyTuple_snoc_self r a q]
  · intro s _ hs
    refine Ψ.map_coord_zero 0 ?_
    rw [Fin.snocEquiv_apply, hochschildFace_last, Fin.cons_zero, ← Fin.succ_last (n + 1),
      homotopyTuple_succ_self r (Fin.last (n + 1)) a _,
      homotopyTuple_of_le r (Fin.last (n + 1)) a _ (by simp)]
    simp [Fin.snoc_last, hs]
  · intro hq0
    exact (hq0 (Finset.mem_univ _)).elim

/-- Regime E (`k < i`): an inner coface past slot `k + 1` commutes with `homotopyTuple`
pointwise. -/
private theorem step_hochschildCoface_of_lt (r : ι) {n : ℕ} {k i : Fin (n + 1)} (hki : k < i)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r (n + 1) k.castSucc
        (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) a =
      matrixHochschildHomotopyStep r n k Ψ (hochschildFace i.castSucc a) := by
  rw [matrixHochschildHomotopyStep_apply, matrixHochschildHomotopyStep_apply]
  simp only [hochschildCoface_apply, Fin.val_castSucc]
  refine Finset.sum_congr rfl fun p _ ↦ congrArg Ψ ?_
  funext m
  rw [hochschildFace_castSucc]
  rcases lt_trichotomy (m : ℕ) ((k : ℕ) + 1) with hmk | hmk | hmk
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega),
      homotopyTuple_of_le r k.castSucc a p (by simp; omega),
      homotopyTuple_of_le r k _ p (by omega)]
    have hcontr : hochschildFace i.castSucc a ⟨m, by omega⟩ = a ⟨m, by omega⟩ := by
      rw [hochschildFace_castSucc]
      exact Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)
    simp [hcontr]
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega),
      show m.castSucc = k.castSucc.succ from Fin.ext (by simp [hmk]), homotopyTuple_succ_self,
      show m = k.succ from Fin.ext hmk, homotopyTuple_succ_self]
    exact congrArg (fun u ↦ Matrix.single r (p u) 1) (Fin.ext (by simp))
  · rw [homotopyTuple_of_gt r k _ p hmk, hochschildFace_castSucc]
    rcases lt_trichotomy (m : ℕ) ((i : ℕ) + 1) with hmi | hmi | hmi
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp [hmi]),
        homotopyTuple_of_gt r k.castSucc a p (by simp; omega),
        Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
      exact congrArg a (Fin.ext (by simp))
    · obtain rfl : m = i.succ := Fin.ext hmi
      rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
        homotopyTuple_of_gt r k.castSucc a p (by simp; omega),
        homotopyTuple_of_gt r k.castSucc a p (by simp; omega),
        show (⟨(i.succ : ℕ) - 1, _⟩ : Fin (n + 1)) = i from Fin.ext (by simp),
        Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]
      exact congrArg₂ (· * ·) (congrArg a (Fin.ext (by simp))) (congrArg a (Fin.ext (by simp)))
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp [hmi]),
        homotopyTuple_of_gt r k.castSucc a p (by simp; omega),
        Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
      congr 1; ext; simp; omega

/-- Helper for Regime F: updating slot `0` with `E_{s,r}(a_{n+1}(s,u) a₀(u,w₀))` matches on both
sides. -/
private theorem update_zero_hochschildFace_last_homotopyTuple {A ι : Type*} [NonAssocSemiring A]
    [Fintype ι] [DecidableEq ι] (r : ι) {n : ℕ} (k : Fin (n + 1))
    (a : Fin (n + 2) → Matrix ι ι A) (u s : ι) (w : Fin ((k : ℕ) + 1) → ι) :
    Function.update
        (hochschildFace (Fin.last (n + 2)) (homotopyTuple r k.castSucc a (Fin.cons u w))) 0
        (Matrix.single s r (a (Fin.last (n + 1)) s u * a 0 u (w 0))) =
      Function.update
        (homotopyTuple r k (hochschildFace (Fin.last (n + 1)) a) (Fin.cons s w)) 0
        (Matrix.single s r (a (Fin.last (n + 1)) s u * a 0 u (w 0))) := by
  funext m
  refine Fin.cases (by simp) (fun m' ↦ ?_) m
  have hm' := m'.2
  have hm'succ : (m'.succ : ℕ) = (m' : ℕ) + 1 := Fin.val_succ m'
  rw [Function.update_of_ne (Fin.succ_ne_zero m'), Function.update_of_ne (Fin.succ_ne_zero m'),
    hochschildFace_last, Fin.cons_succ]
  rcases lt_trichotomy (m'.succ : ℕ) ((k : ℕ) + 1) with hmk | hmk | hmk
  · rw [homotopyTuple_of_le r k.castSucc a _ (by simp; omega),
      homotopyTuple_of_le r k _ _ (by omega)]
    have hlast : hochschildFace (Fin.last (n + 1)) a ⟨(m' : ℕ) + 1, by omega⟩ =
        a ⟨(m' : ℕ) + 1, by omega⟩ := by
      let j : Fin n := ⟨m', by omega⟩
      rw [hochschildFace_last,
        show (⟨(m' : ℕ) + 1, _⟩ : Fin (n + 1)) = j.succ from Fin.ext (by simp [j]), Fin.cons_succ]
      exact congrArg a (Fin.ext (by simp [j]))
    have hc1 : Fin.cons (α := fun _ ↦ ι) u w ⟨(m' : ℕ) + 1, by simp; omega⟩ = w ⟨m', by omega⟩ :=
      Fin.cons_succ (α := fun _ ↦ ι) u w ⟨m', by omega⟩
    have hc2 : Fin.cons (α := fun _ ↦ ι) u w ⟨(m' : ℕ) + 1 + 1, by simp; omega⟩ =
        w ⟨(m' : ℕ) + 1, by omega⟩ :=
      Fin.cons_succ (α := fun _ ↦ ι) u w ⟨(m' : ℕ) + 1, by omega⟩
    have hd1 : Fin.cons (α := fun _ ↦ ι) s w ⟨(m' : ℕ) + 1, by omega⟩ = w ⟨m', by omega⟩ :=
      Fin.cons_succ (α := fun _ ↦ ι) s w ⟨m', by omega⟩
    have hd2 : Fin.cons (α := fun _ ↦ ι) s w ⟨(m' : ℕ) + 1 + 1, by omega⟩ =
        w ⟨(m' : ℕ) + 1, by omega⟩ :=
      Fin.cons_succ (α := fun _ ↦ ι) s w ⟨(m' : ℕ) + 1, by omega⟩
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_one_ne_zero, ↓reduceIte,
      hc1, hc2, hd1, hd2, hlast]
  · rw [show m'.castSucc.succ = k.castSucc.succ from Fin.ext (by simp [← hmk]),
      homotopyTuple_succ_self, show m'.succ = k.succ from Fin.ext hmk, homotopyTuple_succ_self,
      show Fin.last ((k.castSucc : ℕ) + 1) = (Fin.last (k : ℕ)).succ from Fin.ext (by simp),
      show Fin.last ((k : ℕ) + 1) = (Fin.last (k : ℕ)).succ from Fin.ext (by simp),
      Fin.cons_succ, Fin.cons_succ]
  · rw [homotopyTuple_of_gt r k.castSucc a _ (by simp; omega), homotopyTuple_of_gt r k _ _ hmk,
      hochschildFace_last]
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (i := m') (by rintro rfl; simp at hmk)
    rw [show (⟨(j.succ.succ : ℕ) - 1, _⟩ : Fin (n + 1)) = j.succ from Fin.ext (by simp),
      Fin.cons_succ]
    exact congrArg a (Fin.ext (by simp))

private theorem hochschildFace_last_homotopyTuple_cons_eq_update (r : ι) {n : ℕ} (k : Fin (n + 1))
    (a : Fin (n + 2) → Matrix ι ι A) (u : ι) (w : Fin ((k : ℕ) + 1) → ι) :
    hochschildFace (Fin.last (n + 2)) (homotopyTuple r k.castSucc a (Fin.cons u w)) =
      Function.update
        (hochschildFace (Fin.last (n + 2)) (homotopyTuple r k.castSucc a (Fin.cons u w))) 0
        (∑ s : ι, Matrix.single s r (a (Fin.last (n + 1)) s u * a 0 u (w 0))) := by
  rw [eq_comm, Function.update_eq_self_iff, hochschildFace_last, Fin.cons_zero,
    homotopyTuple_of_gt r k.castSucc a _ (by simp; omega),
    homotopyTuple_of_le r k.castSucc a _ (by simp)]
  simp [Matrix.mul_single_eq_sum_single, Fin.last]

private theorem homotopyTuple_hochschildFace_last_cons_eq_update (r : ι) {n : ℕ} (k : Fin (n + 1))
    (a : Fin (n + 2) → Matrix ι ι A) (s : ι) (w : Fin ((k : ℕ) + 1) → ι) :
    homotopyTuple r k (hochschildFace (Fin.last (n + 1)) a) (Fin.cons s w) =
      Function.update (homotopyTuple r k (hochschildFace (Fin.last (n + 1)) a) (Fin.cons s w)) 0
        (∑ u : ι, Matrix.single s r (a (Fin.last (n + 1)) s u * a 0 u (w 0))) := by
  rw [eq_comm, Function.update_eq_self_iff, homotopyTuple_of_le r k _ _ (Nat.zero_le _)]
  simp only [Fin.val_zero, ↓reduceIte, Fin.cons_zero, hochschildFace_last]
  exact (map_sum (Matrix.singleLinearMap ℕ s r) _ _).symm

/-- Regime F (`k ≤ n, j = n + 2`): the last coface on step `k` matches step `k` on the last face. -/
private theorem step_castSucc_hochschildCoface_last (r : ι) {n : ℕ} (k : Fin (n + 1))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    matrixHochschildHomotopyStep r (n + 1) k.castSucc
        (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 2)) Ψ) a =
      matrixHochschildHomotopyStep r n k Ψ (hochschildFace (Fin.last (n + 1)) a) := by
  rw [matrixHochschildHomotopyStep_apply, matrixHochschildHomotopyStep_apply]
  simp only [hochschildCoface_apply, Fin.val_castSucc]
  rw [← (Fin.consEquiv (fun _ : Fin ((k : ℕ) + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type]
  rw [← (Fin.consEquiv (fun _ : Fin ((k : ℕ) + 2) ↦ ι)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply]
  calc
    ∑ u : ι, ∑ w : Fin ((k : ℕ) + 1) → ι,
        Ψ (hochschildFace (Fin.last (n + 2)) (homotopyTuple r k.castSucc a (Fin.cons u w)))
      = ∑ u : ι, ∑ w : Fin ((k : ℕ) + 1) → ι, ∑ s : ι,
          Ψ (Function.update
            (homotopyTuple r k (hochschildFace (Fin.last (n + 1)) a) (Fin.cons s w)) 0
            (Matrix.single s r (a (Fin.last (n + 1)) s u * a 0 u (w 0)))) :=
        Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun w _ ↦ by
          conv_lhs => rw [hochschildFace_last_homotopyTuple_cons_eq_update r k a u w,
            Ψ.map_update_sum]
          exact Finset.sum_congr rfl fun s _ ↦
            congrArg Ψ (update_zero_hochschildFace_last_homotopyTuple r k a u s w)
    _ = ∑ s : ι, ∑ w : Fin ((k : ℕ) + 1) → ι, ∑ u : ι,
          Ψ (Function.update
            (homotopyTuple r k (hochschildFace (Fin.last (n + 1)) a) (Fin.cons s w)) 0
            (Matrix.single s r (a (Fin.last (n + 1)) s u * a 0 u (w 0)))) := by
        rw [Finset.sum_comm]
        refine (Finset.sum_congr rfl fun w _ ↦ Finset.sum_comm).trans ?_
        rw [Finset.sum_comm]
    _ = ∑ s : ι, ∑ w : Fin ((k : ℕ) + 1) → ι,
          Ψ (homotopyTuple r k (hochschildFace (Fin.last (n + 1)) a) (Fin.cons s w)) :=
        Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun w _ ↦ by
          conv_rhs => rw [homotopyTuple_hochschildFace_last_cons_eq_update r k a s w,
            Ψ.map_update_sum]

private theorem neg_one_pow_eq_neg {a b : ℕ} (h : a = b + 1) :
    (-1 : ℤ) ^ a = -((-1 : ℤ) ^ b) := by
  rw [h, pow_succ, mul_neg_one]

private theorem step_inner_coface_diag (r : ι) {n : ℕ} (k : Fin (n + 1))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    (-1 : ℤ) ^ ((k.succ : ℕ) + (k.succ.castSucc : ℕ)) •
        matrixHochschildHomotopyStep r (n + 1) k.succ
          (hochschildCoface R (Matrix ι ι A) M k.succ.castSucc Ψ) a +
      (-1 : ℤ) ^ ((k.castSucc : ℕ) + (k.succ.castSucc : ℕ)) •
        matrixHochschildHomotopyStep r (n + 1) k.castSucc
          (hochschildCoface R (Matrix ι ι A) M k.succ.castSucc Ψ) a = 0 := by
  rw [step_succ_hochschildCoface_succ_eq_step_castSucc,
    neg_one_pow_eq_neg (b := (k.castSucc : ℕ) + (k.succ.castSucc : ℕ)) (by simp; omega),
    neg_smul, neg_add_cancel]

private theorem step_inner_coface_offDiag (r : ι) {n : ℕ} (k i : Fin (n + 1))
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M)
    (a : Fin (n + 2) → Matrix ι ι A) :
    (if i ≤ k then
        (-1 : ℤ) ^ ((k.succ : ℕ) + (i.castSucc.castSucc : ℕ)) •
          matrixHochschildHomotopyStep r (n + 1) k.succ
            (hochschildCoface R (Matrix ι ι A) M i.castSucc.castSucc Ψ) a
      else
        (-1 : ℤ) ^ ((k.castSucc : ℕ) + (i.succ.castSucc : ℕ)) •
          matrixHochschildHomotopyStep r (n + 1) k.castSucc
            (hochschildCoface R (Matrix ι ι A) M i.succ.castSucc Ψ) a) =
      -((-1 : ℤ) ^ ((i : ℕ) + (k : ℕ)) •
        matrixHochschildHomotopyStep r n k Ψ (hochschildFace i.castSucc a)) := by
  split_ifs with hik
  · rw [step_hochschildCoface_of_le r hik,
      neg_one_pow_eq_neg (b := (i : ℕ) + (k : ℕ)) (by simp; omega), neg_smul]
  · rw [step_hochschildCoface_of_lt r (lt_of_not_ge hik),
      neg_one_pow_eq_neg (b := (i : ℕ) + (k : ℕ)) (by simp; omega), neg_smul]

/-- Positive-degree cochain homotopy identity:
`b (hₙ Ψ) + hₙ₊₁ (b Ψ) = Ψ - (Ψ ∘ E_{r,r})#Tr`. -/
theorem hochschildCoboundary_matrixHochschildHomotopy_add (r : ι) (n : ℕ)
    (Ψ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ Matrix ι ι A) M) :
    hochschildCoboundary R (Matrix ι ι A) M n (matrixHochschildHomotopy r n Ψ) +
        matrixHochschildHomotopy r (n + 1)
          (hochschildCoboundary R (Matrix ι ι A) M (n + 1) Ψ) =
      Ψ - matrixCochainExtension ι (n + 1)
        (Ψ.compLinearMap fun _ ↦ Matrix.singleLinearMap R r r) := by
  ext a
  -- Express `hₙ₊₁ (b Ψ) a` through the step maps and split off the last coface `j = n + 2`.
  have hbΨ : hochschildCoboundary R (Matrix ι ι A) M (n + 1) Ψ =
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ (j : ℕ) • hochschildCoface R (Matrix ι ι A) M j Ψ := by
    ext x; simp [hochschildCoboundary_apply]
  have hh (x : Fin (n + 1) → Matrix ι ι A) : matrixHochschildHomotopy r n Ψ x =
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • matrixHochschildHomotopyStep r n k Ψ x := by
    simp [matrixHochschildHomotopy]
  have hh1 (Φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 3) ↦ Matrix ι ι A) M) :
      matrixHochschildHomotopy r (n + 1) Φ a =
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • matrixHochschildHomotopyStep r (n + 1) k Φ a := by
    simp [matrixHochschildHomotopy]
  rw [add_apply, sub_apply, hbΨ, hh1]
  simp only [map_sum, map_zsmul, sum_apply, smul_apply, Finset.smul_sum, smul_smul, ← pow_add]
  simp_rw [Fin.sum_univ_castSucc (n := n + 2), Finset.sum_add_distrib]
  -- Evaluate the inner coface double sum via `sum_fin_succ_succ_eq` and Regimes A, B, C, E.
  rw [sum_fin_succ_succ_eq n (fun k i ↦
    (-1 : ℤ) ^ ((k : ℕ) + (i.castSucc : ℕ)) •
      matrixHochschildHomotopyStep r (n + 1) k
        (hochschildCoface R (Matrix ι ι A) M i.castSucc Ψ) a)]
  -- Evaluate the last coface sum via Regimes D and F.
  rw [Fin.sum_univ_castSucc (n := n + 1) (f := fun k ↦
    (-1 : ℤ) ^ ((k : ℕ) + (Fin.last (n + 2) : ℕ)) •
      matrixHochschildHomotopyStep r (n + 1) k
        (hochschildCoface R (Matrix ι ι A) M (Fin.last (n + 2)) Ψ) a)]
  simp_rw [Fin.castSucc_zero, step_zero_hochschildCoface_zero, step_inner_coface_diag,
    step_inner_coface_offDiag, step_castSucc_hochschildCoface_last, step_last_hochschildCoface_last]
  simp only [Fin.val_zero, add_zero, pow_zero, one_smul, Finset.sum_const_zero,
    Finset.sum_neg_distrib, Fin.val_last, Fin.val_castSucc]
  have hlast_sign (k : Fin (n + 1)) :
      (-1 : ℤ) ^ ((k : ℕ) + (n + 2)) = -((-1 : ℤ) ^ ((n + 1) + (k : ℕ))) :=
    neg_one_pow_eq_neg (by omega)
  have hcorner_sign : (-1 : ℤ) ^ ((n + 1) + (n + 2)) = -1 :=
    (show Odd ((n + 1) + (n + 2)) from ⟨n + 1, by omega⟩).neg_one_pow
  simp only [hlast_sign, neg_smul, Finset.sum_neg_distrib, hcorner_sign]
  -- Expand `b (hₙ Ψ) a` and cancel term by term.
  rw [hochschildCoboundary_apply, Fin.sum_univ_castSucc]
  simp only [hh, Finset.smul_sum, smul_smul, ← pow_add, Fin.val_castSucc, Fin.val_last]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin (n + 1)))]
  abel

end Homotopy

/-! ### Matrix Morita invariance on Hochschild cohomology -/

namespace hochschildCohomology

section NonUnital

variable {R A M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Matrix extension of Hochschild cocycles as a linear map. -/
private def cocyclesMatrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCocycles R A M n →ₗ[R] hochschildCocycles R (Matrix ι ι A) M n :=
  LinearMap.codRestrict _
    (matrixCochainExtension ι n ∘ₗ (hochschildCocycles R A M n).subtype)
    fun φ ↦ matrixCochainExtension_mem_hochschildCocycles φ.2

variable (M) in
/-- The linear map on Hochschild cohomology induced by the generalized matrix trace
`TauCeti.matrixCochainExtension`. -/
def matrixExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    hochschildCohomology R A M n →ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ cocyclesMatrixExtension ι n) fun _ hφ ↦
    (mk_eq_zero_iff R (Matrix ι ι A) M n _).2 (matrixCochainExtension_mem_hochschildCoboundaries hφ)

/-- Matrix extension on Hochschild cohomology sends the class of a cocycle to the class of its
matrix extension. -/
@[simp]
theorem matrixExtension_mk (ι : Type*) [Fintype ι] {n : ℕ} (φ : hochschildCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n
        ⟨matrixCochainExtension ι n φ, matrixCochainExtension_mem_hochschildCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

/-- Pulling back along a diagonal corner inclusion is a left inverse to matrix extension on
Hochschild cohomology, without unitality of `A`. -/
@[simp]
theorem map_singleNonUnitalAlgHom_matrixExtension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) {n : ℕ} (c : hochschildCohomology R A M n) :
    map M (Matrix.singleNonUnitalAlgHom R A r) n (matrixExtension M ι n c) = c := by
  obtain ⟨φ, rfl⟩ := mk_surjective R A M n c
  rw [matrixExtension_mk, map_mk]
  congr 1
  ext x
  simp [MultilinearMap.compLinearMap_apply]

/-- For a nonempty finite matrix index type, matrix extension on Hochschild cohomology is
injective, without unitality of `A`. -/
theorem injective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact Function.LeftInverse.injective (map_singleNonUnitalAlgHom_matrixExtension r)

end NonUnital

section Unital

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- For a unital algebra `A`, matrix extension is a right inverse to diagonal corner pullback on
Hochschild cohomology. -/
@[simp]
theorem matrixExtension_map_singleNonUnitalAlgHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) {n : ℕ} (c : hochschildCohomology R (Matrix ι ι A) M n) :
    matrixExtension M ι n (map M (Matrix.singleNonUnitalAlgHom R A r) n c) = c := by
  obtain ⟨Ψ, rfl⟩ := mk_surjective R (Matrix ι ι A) M n c
  rw [map_mk, matrixExtension_mk, eq_comm, mk_eq_mk_iff]
  have hΨ : hochschildCoboundary R (Matrix ι ι A) M n Ψ.1 = 0 :=
    mem_hochschildCocycles_iff.1 Ψ.2
  cases n with
  | zero =>
    have h0 := matrixHochschildHomotopy_hochschildCoboundary_zero r Ψ.1
    rw [hΨ, map_zero] at h0
    simpa [hochschildCoboundaries_zero] using h0.symm
  | succ n =>
    have hn := hochschildCoboundary_matrixHochschildHomotopy_add r n Ψ.1
    rw [hΨ, map_zero, add_zero] at hn
    exact mem_hochschildCoboundaries_succ_iff.2
      ⟨matrixHochschildHomotopy r n Ψ.1, by simpa using hn⟩

/-- **Matrix Morita invariance of Hochschild cohomology.** For a unital algebra `A` and a nonempty
finite index type `ι`, the generalized matrix trace induces a bijection on Hochschild cohomology in
every degree. -/
theorem bijective_matrixExtension (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Bijective (matrixExtension (R := R) (A := A) M ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  exact ⟨Function.LeftInverse.injective (map_singleNonUnitalAlgHom_matrixExtension r),
    Function.RightInverse.surjective (matrixExtension_map_singleNonUnitalAlgHom r)⟩

variable (M) in
/-- **Matrix Morita equivalence for Hochschild cohomology.** Matrix extension as a linear
equivalence `HHⁿ(A, Hom_R(A, M)) ≃ₗ[R] HHⁿ(Matrix ι ι A, Hom_R(Matrix ι ι A, M))`. -/
def matrixExtensionEquiv (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    hochschildCohomology R A M n ≃ₗ[R] hochschildCohomology R (Matrix ι ι A) M n :=
  LinearEquiv.ofBijective (matrixExtension M ι n) (bijective_matrixExtension ι n)

/-- The forward map of `matrixExtensionEquiv` is `matrixExtension`. -/
@[simp]
theorem matrixExtensionEquiv_apply (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ)
    (c : hochschildCohomology R A M n) :
    matrixExtensionEquiv M ι n c = matrixExtension M ι n c :=
  (rfl)

/-- The inverse of `matrixExtensionEquiv` is pullback along any diagonal corner inclusion. -/
theorem matrixExtensionEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r : ι) {n : ℕ} (c : hochschildCohomology R (Matrix ι ι A) M n) :
    (matrixExtensionEquiv M ι n).symm c =
      map M (Matrix.singleNonUnitalAlgHom R A r) n c := by
  apply (matrixExtensionEquiv M ι n).injective
  rw [LinearEquiv.apply_symm_apply, matrixExtensionEquiv_apply,
    matrixExtension_map_singleNonUnitalAlgHom]

end Unital

end hochschildCohomology

end TauCeti
