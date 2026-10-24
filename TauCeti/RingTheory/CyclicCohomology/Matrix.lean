/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.ConnesOperator
import TauCeti.Data.Fin.Basic

/-!
# Matrix extensions of multilinear cochains

The generalized matrix trace extends a scalar cochain to matrices by summing over closed
paths of matrix indices. This construction is multilinear, preserves signed cyclicity,
and recovers the original cochain on a single diagonal corner. Matrix extension commutes
with cyclic rotation, the cyclic norm, insertion of the unit, and Connes' operator `B`.
It is the cochain-level input to matrix Morita invariance and pairings with idempotents and
invertibles.

No multiplication on the coefficient module is needed. The cochain constructions work over
any semiring whose action on the coefficient module commutes with itself. In degree zero the
construction is ordinary matrix trace followed by the original linear functional.

Matrix extension commutes with every Hochschild coface, hence with the Hochschild
coboundary: `(bφ)#Tr = b(φ#Tr)`. For the faces multiplying adjacent entries this is the
expansion of a matrix product over the intermediate index, which lengthens a closed index
path by one; the last face is reduced to the zeroth by cyclic rotation. Consequently matrix
extension maps cyclic cocycles and coboundaries to cyclic cocycles and coboundaries, and
induces a map `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)` on cyclic cohomology.

The convention follows Connes, *Noncommutative Geometry*, Chapter III, §1.
The construction uses `MultilinearMap.compLinearMap` and `Matrix.entryLinearMap`.

## Main definitions

* `TauCeti.matrixCochainExtension`: the matrix extension `φ ↦ φ#Tr`.
* `TauCeti.matrixCyclicCochainExtension`: its restriction to cyclic cochains.
* `TauCeti.cyclicCohomology.matrixExtension`: the induced map on cyclic cohomology.

## Main results

* `TauCeti.matrixCochainExtension_cyclic`: matrix extension preserves signed cyclicity.
* `TauCeti.matrixCochainExtension_fromBlocks_zero₁₂_zero₂₁`: matrix extension is additive on
  block-diagonal matrices, the cochain-level input to additivity of the pairings on direct sums.
* `TauCeti.matrixCochainExtension_hochschildCoface`,
  `TauCeti.matrixCochainExtension_hochschildCoboundary`: compatibility with the cofaces and the
  Hochschild coboundary.
-/

public section

namespace TauCeti

open scoped BigOperators

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [SMulCommClass R R M]

/-- Extend a degree-`n` cochain to square matrices by the generalized matrix trace:
sum `φ(a₀(i₀,i₁), …, aₙ(iₙ,i₀))` over all closed index paths. -/
noncomputable def matrixCochainExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) => A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 1) => Matrix ι ι A) M where
  toFun φ := ∑ p : Fin (n + 1) → ι,
    φ.compLinearMap (fun j => Matrix.entryLinearMap R A (p j) (p (finRotate (n + 1) j)))
  map_add' φ ψ := by
    classical
    ext a
    simp [MultilinearMap.compLinearMap_apply, Finset.sum_add_distrib]
  map_smul' c φ := by
    classical
    ext a
    simp [MultilinearMap.compLinearMap_apply, Finset.smul_sum]

/-- The closed-path formula for the matrix extension. -/
-- Prefer the corner and stabilization normal forms to expanding the closed-path sum.
@[simp low] theorem matrixCochainExtension_apply (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ a =
      ∑ p : Fin (n + 1) → ι, φ (fun j => a j (p j) (p (finRotate (n + 1) j))) := by
  classical
  simp [matrixCochainExtension, MultilinearMap.compLinearMap_apply]

/-- The entries `(a₀(p₀, p₁), …, aₙ(pₙ, p₀))` of matrices along a closed index path `p`. -/
private def pathEntries {A ι : Type*} {n : ℕ} (a : Fin (n + 1) → Matrix ι ι A)
    (p : Fin (n + 1) → ι) : Fin (n + 1) → A :=
  fun j => a j (p j) (p (finRotate (n + 1) j))

private theorem pathEntries_apply {A ι : Type*} {n : ℕ} (a : Fin (n + 1) → Matrix ι ι A)
    (p : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    pathEntries a p j = a j (p j) (p (finRotate (n + 1) j)) :=
  rfl

private theorem matrixCochainExtension_apply_eq_sum_pathEntries (ι : Type*) [Fintype ι]
    (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ a = ∑ p, φ (pathEntries a p) :=
  matrixCochainExtension_apply ι n φ a

/-- Rotating both the matrices and the index path rotates the path entries. -/
private theorem pathEntries_comp_finRotate_symm {A ι : Type*} {n : ℕ}
    (a : Fin (n + 1) → Matrix ι ι A) (p : Fin (n + 1) → ι) :
    pathEntries (a ∘ (finRotate (n + 1)).symm) (p ∘ (finRotate (n + 1)).symm) =
      pathEntries a p ∘ (finRotate (n + 1)).symm := by
  funext j
  simp [pathEntries_apply]

/-- A sum over closed index paths is invariant under rotating the paths. -/
private theorem sum_comp_finRotate_symm {ι : Type*} [Fintype ι] {n : ℕ}
    (f : (Fin (n + 1) → ι) → M) :
    ∑ p, f (p ∘ (finRotate (n + 1)).symm) = ∑ p, f p :=
  (Equiv.arrowCongr (finRotate (n + 1)) (Equiv.refl ι)).sum_comp f

/-- Matrix extension intertwines rotation of the cochain arguments and matrix arguments. -/
private theorem matrixCochainExtension_rotate (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ (a ∘ (finRotate (n + 1)).symm) =
      ∑ p : Fin (n + 1) → ι, φ (pathEntries a p ∘ (finRotate (n + 1)).symm) := by
  rw [matrixCochainExtension_apply_eq_sum_pathEntries, ← sum_comp_finRotate_symm]
  simp only [pathEntries_comp_finRotate_symm]

/-- Any signed cyclicity relation of a cochain is inherited by its matrix extension.
Over a ring, degree-`n` cyclic cochains have `c = (-1 : R) ^ n`. -/
theorem matrixCochainExtension_cyclic (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) (c : R)
    (hφ : ∀ x, φ (x ∘ (finRotate (n + 1)).symm) = c • φ x)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ (a ∘ (finRotate (n + 1)).symm) =
      c • matrixCochainExtension ι n φ a := by
  rw [matrixCochainExtension_rotate, matrixCochainExtension_apply_eq_sum_pathEntries]
  simp only [hφ, Finset.smul_sum]

/-- Matrix extension sends cyclic cochains to cyclic cochains. -/
theorem matrixCochainExtension_mem_cyclicCochains
    {R : Type*} [Semiring R] {A M : Type*} [AddCommMonoid A] [Module R A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M]
    (ι : Type*) [Fintype ι] (n : ℕ) (φ : cyclicCochains R A M n) :
    matrixCochainExtension ι n φ.1 ∈ cyclicCochains R (Matrix ι ι A) M n := by
  rw [mem_cyclicCochains_iff]
  intro a
  rw [matrixCochainExtension_rotate]
  rw [matrixCochainExtension_apply_eq_sum_pathEntries, ← Finset.sum_zsmul]
  simp only [cyclicCochains_apply_finRotate_symm]

/-- Extension of cyclic cochains to square matrix algebras. -/
noncomputable def matrixCyclicCochainExtension
    {R : Type*} [Semiring R] {A M : Type*} [AddCommMonoid A] [Module R A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M]
    (ι : Type*) [Fintype ι] (n : ℕ) :
    cyclicCochains R A M n →ₗ[R] cyclicCochains R (Matrix ι ι A) M n :=
  ((matrixCochainExtension ι n).domRestrict (cyclicCochains R A M n)).codRestrict
    (cyclicCochains R (Matrix ι ι A) M n)
    (matrixCochainExtension_mem_cyclicCochains ι n)

/-- The underlying cochain of a matrix-extended cyclic cochain is its generalized matrix trace. -/
@[simp]
theorem coe_matrixCyclicCochainExtension_apply
    {R : Type*} [Semiring R] {A M : Type*} [AddCommMonoid A] [Module R A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M]
    (ι : Type*) [Fintype ι] (n : ℕ) (φ : cyclicCochains R A M n) :
    (matrixCyclicCochainExtension ι n φ :
      MultilinearMap R (fun _ : Fin (n + 1) => Matrix ι ι A) M) =
      matrixCochainExtension ι n φ.1 := (rfl)

/-- On a one-by-one matrix algebra, matrix extension is the original cochain. -/
@[simp] theorem matrixCochainExtension_unique (ι : Type*) [Fintype ι] [Unique ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ a = φ (fun j => a j default default) := by
  simp

/-- Extension is unchanged by restricting matrices to an embedded index set, provided
all rows outside that set vanish. In particular, it is unchanged by zero stabilization. -/
theorem matrixCochainExtension_submatrix (ι κ : Type*) [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix κ κ A)
    (ha : ∀ j r, r ∉ Set.range e → ∀ s, a j r s = 0) :
    matrixCochainExtension ι n φ (fun j => (a j).submatrix e e) =
      matrixCochainExtension κ n φ a := by
  classical
  simp only [matrixCochainExtension_apply, Matrix.submatrix_apply]
  apply Fintype.sum_of_injective (fun p j => e (p j))
    (fun p q h => funext fun j => e.injective (congrFun h j))
  · intro p hp
    by_cases h : ∀ j, p j ∈ Set.range e
    · obtain ⟨q, hq⟩ := Classical.axiomOfChoice h
      exact (hp ⟨q, funext hq⟩).elim
    · obtain ⟨j, hj⟩ := not_forall.mp h
      exact φ.map_coord_zero j (ha j (p j) hj _)
  · intro p
    rfl

/-- Relabeling the matrix indices does not change the generalized trace. -/
theorem matrixCochainExtension_submatrix_equiv (ι κ : Type*) [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix κ κ A) :
    matrixCochainExtension ι n φ (fun j => (a j).submatrix e e) =
      matrixCochainExtension κ n φ a := by
  apply matrixCochainExtension_submatrix ι κ e.toEmbedding
  intro j r hr
  exact (hr (e.surjective r)).elim

/-- The matrix extension of a tuple of block-diagonal matrices is the sum of the matrix extensions
of the two tuples of diagonal blocks. -/
theorem matrixCochainExtension_fromBlocks_zero₁₂_zero₂₁ (ι κ : Type*) [Fintype ι] [Fintype κ]
    (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) (b : Fin (n + 1) → Matrix κ κ A) :
    matrixCochainExtension (ι ⊕ κ) n φ (fun j => Matrix.fromBlocks (a j) 0 0 (b j)) =
      matrixCochainExtension ι n φ a + matrixCochainExtension κ n φ b := by
  classical
  simp only [matrixCochainExtension_apply]
  -- The closed paths inside `ι` or inside `κ` contribute the two extensions.
  have h := Fintype.sum_of_injective
    (Sum.elim (fun q j ↦ Sum.inl (q j)) (fun q j ↦ Sum.inr (q j)) :
      (Fin (n + 1) → ι) ⊕ (Fin (n + 1) → κ) → Fin (n + 1) → ι ⊕ κ)
    (by rintro (q | q) (q' | q') h <;> simp_all [funext_iff])
    (Sum.elim (fun q ↦ φ fun j ↦ a j (q j) (q (finRotate (n + 1) j)))
      (fun q ↦ φ fun j ↦ b j (q j) (q (finRotate (n + 1) j))))
    (fun p ↦ φ fun j ↦ Matrix.fromBlocks (a j) 0 0 (b j) (p j) (p (finRotate (n + 1) j)))
    (by
      intro p hp
      -- Every other closed path steps between the summands somewhere, since a path which
      -- never does stays in the summand of its starting point.
      obtain ⟨j, hj⟩ : ∃ j, (p (finRotate (n + 1) j)).isLeft ≠ (p j).isLeft := by
        by_contra! h
        have hc (j) : (p j).isLeft = (p 0).isLeft :=
          apply_eq_apply_zero_of_add_one (f := fun j ↦ (p j).isLeft)
            (fun j ↦ by simpa only [finRotate_apply] using h j) j
        cases h₀ : (p 0).isLeft
        · exact hp ⟨.inr fun j ↦ (p j).getRight (Sum.isLeft_eq_false.1 (by rw [hc, h₀])),
            funext fun j ↦ by simp⟩
        · exact hp ⟨.inl fun j ↦ (p j).getLeft (by rw [hc, h₀]), funext fun j ↦ by simp⟩
      -- There the path meets a vanishing off-diagonal block.
      apply φ.map_coord_zero j
      revert hj
      rcases p (finRotate (n + 1) j) with s | s <;> rcases p j with r | r <;> simp)
    (by rintro (q | q) <;> rfl)
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using h.symm

/-- Adding a zero diagonal block leaves the matrix extension unchanged. -/
@[simp] theorem matrixCochainExtension_fromBlocks_zero (ι κ : Type*)
    [Fintype ι] [Fintype κ] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension (ι ⊕ κ) n φ (fun j => Matrix.fromBlocks (a j) 0 0 0) =
      matrixCochainExtension ι n φ a := by
  simpa using matrixCochainExtension_fromBlocks_zero₁₂_zero₂₁ ι κ n φ a 0

/-- Restricting to a diagonal matrix corner recovers the original cochain in every degree. -/
@[simp] theorem matrixCochainExtension_single (ι : Type*) [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (x : Fin (n + 1) → A) :
    matrixCochainExtension ι n φ (fun j => Matrix.single r r (x j)) = φ x := by
  let e : Unit ↪ ι := ⟨fun _ => r, fun _ _ _ => Subsingleton.elim _ _⟩
  have he (u : Unit) : e u = r := rfl
  have h := matrixCochainExtension_submatrix Unit ι e n φ
    (fun j => Matrix.single r r (x j)) (by
      intro j s hs t
      have hsr : r ≠ s := by
        intro h
        exact hs ⟨(), h⟩
      exact Matrix.single_apply_of_row_ne hsr r t (x j))
  simpa only [matrixCochainExtension_unique, Matrix.submatrix_apply, he,
    Matrix.single_apply_same] using h.symm

/-- Matrix extension is injective for every nonempty matrix index type. -/
theorem matrixCochainExtension_injective (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixCochainExtension (R := R) (A := A) (M := M) ι n) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  intro φ ψ h
  ext x
  have hx := congrArg (fun f => f (fun j => Matrix.single r r (x j))) h
  simpa only [matrixCochainExtension_single] using hx

/-- Matrix extension is injective on cyclic cochains for a nonempty matrix index type. -/
theorem matrixCyclicCochainExtension_injective
    {R : Type*} [Semiring R] {A M : Type*} [AddCommMonoid A] [Module R A]
    [AddCommGroup M] [Module R M] [SMulCommClass R R M]
    (ι : Type*) [Fintype ι] [Nonempty ι] (n : ℕ) :
    Function.Injective (matrixCyclicCochainExtension (R := R) (A := A) (M := M) ι n) := by
  intro φ ψ h
  apply Subtype.ext
  apply matrixCochainExtension_injective ι n
  simpa only [coe_matrixCyclicCochainExtension_apply] using congrArg Subtype.val h

/-- In degree zero, matrix extension is ordinary trace followed by the unary cochain. -/
@[simp] theorem matrixCochainExtension_zero_eq_trace (ι : Type*) [Fintype ι]
    (φ : MultilinearMap R (fun _ : Fin 1 => A) M) (a : Matrix ι ι A) :
    matrixCochainExtension ι 0 φ (fun _ => a) = φ (fun _ => Matrix.trace a) := by
  classical
  simpa [Matrix.trace, finRotate_one] using
    (φ.map_sum (fun (_ : Fin 1) (r : ι) => a r r)).symm

/-- Applying a linear map to the cochain values commutes with matrix extension. -/
theorem matrixCochainExtension_compMultilinearMap
    {N : Type*} [AddCommMonoid N] [Module R N] [SMulCommClass R R N]
    (ι : Type*) [Fintype ι] (n : ℕ) (f : M →ₗ[R] N)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension ι n (f.compMultilinearMap φ) =
      f.compMultilinearMap (matrixCochainExtension ι n φ) := by
  ext a
  simp [LinearMap.compMultilinearMap_apply, map_sum]

/-- Pulling a cochain back along a linear map commutes with entrywise application of that
map to its matrix arguments. Algebra homomorphisms are a special case. -/
theorem matrixCochainExtension_compLinearMap
    {B : Type*} [AddCommMonoid B] [Module R B]
    (ι : Type*) [Fintype ι] (n : ℕ) (f : B →ₗ[R] A)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension ι n (φ.compLinearMap (fun _ => f)) =
      (matrixCochainExtension ι n φ).compLinearMap (fun _ => f.mapMatrix) := by
  ext a
  simp [MultilinearMap.compLinearMap_apply]

/-! ### Compatibility with the Hochschild coboundary -/

section Hochschild

variable {R A M : Type*} [NonUnitalNonAssocSemiring A] [AddCommMonoid M]

/-- Inserting an intermediate index `k` at position `i + 1` of a closed path `p`: the entries of
the contracted matrices along `p`, with the product entry at `i` replaced by its `k`-th summand,
are the contracted entries along the lengthened path. -/
private theorem update_pathEntries_hochschildFace_castSucc {ι : Type*} [Fintype ι] {n : ℕ}
    (a : Fin (n + 2) → Matrix ι ι A) (i : Fin (n + 1)) (p : Fin (n + 1) → ι) (k : ι) :
    Function.update (pathEntries (hochschildFace i.castSucc a) p) i
        (a i.castSucc (p i) k * a i.succ k (p (finRotate (n + 1) i))) =
      hochschildFace i.castSucc (pathEntries a (Fin.insertNth i.succ k p)) := by
  have hsA (m : Fin (n + 1)) (hm : m ≠ i) : i.castSucc.succAbove m = i.succ.succAbove m := by
    rw [Ne, Fin.ext_iff] at hm
    ext
    simp only [Fin.val_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  have hself : Fin.insertNth (α := fun _ => ι) i.succ k p i.castSucc = p i := by
    rw [← Fin.succAbove_succ_self, Fin.insertNth_apply_succAbove]
  funext m
  simp only [hochschildFace_castSucc]
  rcases eq_or_ne m i with rfl | hm
  · simp only [Function.update_self, Fin.contractNth_apply_of_eq m.castSucc _ _ m rfl,
      pathEntries_apply, Fin.finRotate_castSucc, hself, Fin.insertNth_apply_same,
      Fin.finRotate_succ_eq_succ_succAbove, Fin.insertNth_apply_succAbove]
  · have hm' : (i.castSucc : ℕ) ≠ m := by simpa [Fin.ext_iff, eq_comm] using hm
    simp only [Function.update_of_ne hm, Fin.contractNth_apply_of_ne _ _ _ _ hm',
      pathEntries_apply, hsA m hm, Fin.finRotate_succ_succAbove_of_ne hm,
      Fin.insertNth_apply_succAbove]

section Semiring

variable [Semiring R] [Module R A] [Module R M]

/-- Matrix extension commutes with a face multiplying adjacent entries. Expanding the matrix
product `(aᵢaᵢ₊₁)(pᵢ, pᵢ₊₁)` over the intermediate index `k` turns a closed path `p` of length
`n + 1` into the closed path of length `n + 2` obtained by inserting `k` at position `i + 1`. -/
private theorem sum_pathEntries_hochschildFace_castSucc {ι : Type*} [Fintype ι] {n : ℕ}
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) (i : Fin (n + 1))
    (a : Fin (n + 2) → Matrix ι ι A) :
    ∑ p, φ (pathEntries (hochschildFace i.castSucc a) p) =
      ∑ q, φ (hochschildFace i.castSucc (pathEntries a q)) := by
  classical
  rw [← (Fin.insertNthEquiv (fun _ => ι) i.succ).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hx : pathEntries (hochschildFace i.castSucc a) p = Function.update
      (pathEntries (hochschildFace i.castSucc a) p) i
      (∑ k, a i.castSucc (p i) k * a i.succ k (p (finRotate (n + 1) i))) := by
    rw [eq_comm, Function.update_eq_self_iff, pathEntries_apply, hochschildFace_castSucc,
      Fin.contractNth_apply_of_eq _ _ _ _ rfl, Matrix.mul_apply]
  rw [hx, φ.map_update_sum]
  simp only [update_pathEntries_hochschildFace_castSucc, Fin.insertNthEquiv_apply]

/-- Matrix extension commutes with the last face, which is the zeroth face of the rotated
tuple. -/
private theorem sum_pathEntries_hochschildFace_last {ι : Type*} [Fintype ι] {n : ℕ}
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) (a : Fin (n + 2) → Matrix ι ι A) :
    ∑ p, φ (pathEntries (hochschildFace (Fin.last (n + 1)) a) p) =
      ∑ q, φ (hochschildFace (Fin.last (n + 1)) (pathEntries a q)) := by
  have h := sum_pathEntries_hochschildFace_castSucc φ 0 (a ∘ (finRotate (n + 2)).symm)
  rw [Fin.castSucc_zero, hochschildFace_zero_comp_finRotate_symm] at h
  rw [h, ← sum_comp_finRotate_symm]
  simp only [pathEntries_comp_finRotate_symm, hochschildFace_zero_comp_finRotate_symm]

end Semiring

variable [Semiring R] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [Module R M]
  [SMulCommClass R R M]

/-- Matrix extension commutes with each Hochschild coface. -/
theorem matrixCochainExtension_hochschildCoface (ι : Type*) [Fintype ι] (n : ℕ)
    (i : Fin (n + 2)) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension ι (n + 1) (hochschildCoface R A M i φ) =
      hochschildCoface R (Matrix ι ι A) M i (matrixCochainExtension ι n φ) := by
  ext a
  rw [matrixCochainExtension_apply_eq_sum_pathEntries, hochschildCoface_apply,
    matrixCochainExtension_apply_eq_sum_pathEntries]
  simp only [hochschildCoface_apply]
  induction i using Fin.lastCases with
  | last => exact (sum_pathEntries_hochschildFace_last φ a).symm
  | cast i => exact (sum_pathEntries_hochschildFace_castSucc φ i a).symm

end Hochschild

section Coboundary

variable {R A M : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Matrix extension commutes with the Hochschild coboundary: `(bφ)#Tr = b(φ#Tr)`. -/
theorem matrixCochainExtension_hochschildCoboundary (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension ι (n + 1) (hochschildCoboundary R A M n φ) =
      hochschildCoboundary R (Matrix ι ι A) M n (matrixCochainExtension ι n φ) := by
  ext a
  have hface (i : Fin (n + 2)) :
      matrixCochainExtension ι n φ (hochschildFace i a) =
        ∑ p, φ (hochschildFace i (pathEntries a p)) := by
    rw [← hochschildCoface_apply, ← matrixCochainExtension_hochschildCoface,
      matrixCochainExtension_apply_eq_sum_pathEntries]
    simp only [hochschildCoface_apply]
  rw [hochschildCoboundary_apply, matrixCochainExtension_apply_eq_sum_pathEntries]
  simp only [hochschildCoboundary_apply, hface, Finset.smul_sum]
  exact Finset.sum_comm

end Coboundary

section CyclicCohomology

variable {R A M : Type*} [AddCommGroup M] {ι : Type*} [Fintype ι] {n : ℕ}

section NonUnital

variable [Semiring R] [Module R M] [SMulCommClass R R M] [NonUnitalNonAssocSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- Matrix extension of cyclic cochains commutes with the Hochschild coboundary. -/
theorem cyclicHochschildCoboundary_matrixCyclicCochainExtension (φ : cyclicCochains R A M n) :
    cyclicHochschildCoboundary R (Matrix ι ι A) M n (matrixCyclicCochainExtension ι n φ) =
      matrixCyclicCochainExtension ι (n + 1) (cyclicHochschildCoboundary R A M n φ) := by
  ext : 1
  simp [matrixCochainExtension_hochschildCoboundary]

/-- Matrix extension maps cyclic cocycles to cyclic cocycles. -/
theorem matrixCyclicCochainExtension_mem_cyclicCocycles {φ : cyclicCochains R A M n}
    (hφ : φ ∈ cyclicCocycles R A M n) :
    matrixCyclicCochainExtension ι n φ ∈ cyclicCocycles R (Matrix ι ι A) M n := by
  rw [mem_cyclicCocycles_iff] at hφ ⊢
  rw [coe_matrixCyclicCochainExtension_apply, ← matrixCochainExtension_hochschildCoboundary, hφ,
    map_zero]

/-- Matrix extension maps cyclic coboundaries to cyclic coboundaries. -/
theorem matrixCyclicCochainExtension_mem_cyclicCoboundaries {φ : cyclicCochains R A M n}
    (hφ : φ ∈ cyclicCoboundaries R A M n) :
    matrixCyclicCochainExtension ι n φ ∈ cyclicCoboundaries R (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ ⊢
    rw [hφ, map_zero]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_cyclicCoboundaries_succ_iff _ _ _).1 hφ
    exact (mem_cyclicCoboundaries_succ_iff _ _ _).2
      ⟨_, cyclicHochschildCoboundary_matrixCyclicCochainExtension ψ⟩

end NonUnital

namespace cyclicCohomology

variable [CommRing R] [Module R M] [Ring A] [Algebra R A] [DecidableEq ι]

variable (M ι n) in
/-- The map `HCⁿ(A; M) → HCⁿ(Matrix ι ι A; M)` on cyclic cohomology induced by matrix extension of
cyclic cocycles. -/
noncomputable def matrixExtension :
    cyclicCohomology R A M n →ₗ[R] cyclicCohomology R (Matrix ι ι A) M n :=
  desc n (mk R (Matrix ι ι A) M n ∘ₗ (matrixCyclicCochainExtension ι n).restrict
      fun _ ↦ matrixCyclicCochainExtension_mem_cyclicCocycles)
    fun _ hφ ↦ (mk_eq_zero_iff _ _ _ n _).2 (matrixCyclicCochainExtension_mem_cyclicCoboundaries hφ)

/-- The induced map sends the class of a cyclic cocycle to the class of its matrix extension. -/
@[simp]
theorem matrixExtension_mk (φ : cyclicCocycles R A M n) :
    matrixExtension M ι n (mk R A M n φ) =
      mk R (Matrix ι ι A) M n ⟨matrixCyclicCochainExtension ι n φ,
        matrixCyclicCochainExtension_mem_cyclicCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

end cyclicCohomology

end CyclicCohomology

section Differential

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [One A] [Module R A]
  [AddCommGroup M] [Module R M] [SMulCommClass R R M]

omit [One A] in
/-- Matrix extension commutes with the cyclic operator. -/
theorem matrixCochainExtension_cyclicOperator (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension (R := R) ι n (cyclicOperator R A M n φ) =
      cyclicOperator R (Matrix ι ι A) M n
        (matrixCochainExtension (R := R) ι n φ) := by
  ext a
  rw [cyclicOperator_apply, matrixCochainExtension_apply_eq_sum_pathEntries,
    matrixCochainExtension_rotate]
  simp only [cyclicOperator_apply, Finset.smul_sum]

omit [One A] in
private theorem matrixCochainExtension_cyclicOperator_pow (ι : Type*) [Fintype ι]
    (n k : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension (R := R) ι n ((cyclicOperator R A M n ^ k) φ) =
      (cyclicOperator R (Matrix ι ι A) M n ^ k)
        (matrixCochainExtension (R := R) ι n φ) := by
  exact (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute
    (LinearMap.ext fun ψ => (matrixCochainExtension_cyclicOperator ι n ψ).symm) k) φ).symm

omit [One A] in
/-- Matrix extension commutes with the cyclic norm. -/
theorem matrixCochainExtension_cyclicNorm (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) :
    matrixCochainExtension (R := R) ι n (cyclicNorm R A M n φ) =
      cyclicNorm R (Matrix ι ι A) M n (matrixCochainExtension (R := R) ι n φ) := by
  rw [cyclicNorm_def, cyclicNorm_def, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => matrixCochainExtension_cyclicOperator_pow ι n k φ

/-- Matrix extension commutes with insertion of the unit in the first cochain argument. -/
theorem matrixCochainExtension_barContraction (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 2) => A) M) :
    matrixCochainExtension (R := R) ι n (barContraction R A M n φ) =
      barContraction R (Matrix ι ι A) M n
        (matrixCochainExtension (R := R) ι (n + 1) φ) := by
  classical
  ext a
  rw [matrixCochainExtension_apply]
  simp_rw [barContraction_apply]
  rw [matrixCochainExtension_apply]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => ι)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (p 0)]
  · have hindex (j : Fin (n + 1)) :
        @Fin.cons _ (fun _ => ι) (p 0) p (finRotate (n + 2) j.succ) =
          p (finRotate (n + 1) j) := by
      rw [← congrFun (Fin.snoc_eq_cons_rotate p (p 0)) j.succ]
      by_cases hj : j = Fin.last n
      · subst j
        simp
      · have heq : j.succ = (finRotate (n + 1) j).castSucc := by
          ext
          exact (coe_finRotate_of_ne_last hj).symm
        rw [heq, Fin.snoc_castSucc]
    congr 1
    funext j
    refine Fin.cases (by simp) (fun j => ?_) j
    simp only [Fin.cons_succ, Fin.consEquiv_apply]
    rw [hindex]
  · intro r _ hr
    exact φ.map_coord_zero 0 (by simp [hr])
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Matrix extension commutes with Connes' operator `B`. -/
theorem matrixCochainExtension_connesB (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n : ℕ) (φ : MultilinearMap R (fun _ : Fin (n + 2) => A) M) :
    matrixCochainExtension (R := R) ι n (connesB R A M n φ) =
      connesB R (Matrix ι ι A) M n
        (matrixCochainExtension (R := R) ι (n + 1) φ) := by
  rw [connesB_apply, connesB_apply, matrixCochainExtension_cyclicNorm,
    matrixCochainExtension_barContraction, map_sub,
    matrixCochainExtension_cyclicOperator]

end Differential

end TauCeti
