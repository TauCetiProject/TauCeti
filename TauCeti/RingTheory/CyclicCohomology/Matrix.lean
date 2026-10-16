/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Matrix extensions of multilinear cochains

The generalized matrix trace extends a scalar cochain to matrices by summing over closed
paths of matrix indices. This construction is multilinear, preserves signed cyclicity,
and recovers the original cochain on a single diagonal corner. It is the cochain-level
input to matrix Morita invariance and pairings with idempotents and invertibles.

No multiplication on the coefficient module is needed. In degree zero the construction
is ordinary matrix trace followed by the original linear functional.

The convention follows Connes, *Noncommutative Geometry*, Chapter III, §1.
The construction uses `MultilinearMap.compLinearMapₗ` and `Matrix.entryLinearMap`.
-/

public section

namespace TauCeti

open scoped BigOperators

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M]

/-- Extend a degree-`n` cochain to square matrices by the generalized matrix trace:
sum `φ(a₀(i₀,i₁), …, aₙ(iₙ,i₀))` over all closed index paths. -/
noncomputable def matrixCochainExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) => A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 1) => Matrix ι ι A) M :=
  ∑ p : Fin (n + 1) → ι,
    MultilinearMap.compLinearMapₗ
      (fun j => Matrix.entryLinearMap R A (p j) (p (finRotate (n + 1) j)))

/-- The closed-path formula for the matrix extension. -/
-- Prefer the corner and stabilization normal forms to expanding the closed-path sum.
@[simp low] theorem matrixCochainExtension_apply (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ a =
      ∑ p : Fin (n + 1) → ι, φ (fun j => a j (p j) (p (finRotate (n + 1) j))) := by
  classical
  simp [matrixCochainExtension, MultilinearMap.compLinearMap_apply]

/-- Matrix extension intertwines rotation of the cochain arguments and matrix arguments. -/
private theorem matrixCochainExtension_rotate (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ (a ∘ (finRotate (n + 1)).symm) =
      ∑ p : Fin (n + 1) → ι,
        φ ((fun j => a j (p j) (p (finRotate (n + 1) j))) ∘
          (finRotate (n + 1)).symm) := by
  classical
  rw [matrixCochainExtension_apply]
  let e := Equiv.arrowCongr (finRotate (n + 1)).symm (Equiv.refl ι)
  exact Fintype.sum_equiv e _ _ (fun p => by
    congr 1
    funext j
    simp only [e, Equiv.arrowCongr, Equiv.coe_fn_mk, Equiv.symm_symm,
      Equiv.refl_apply, Function.comp_apply, Equiv.apply_symm_apply])

/-- Any signed cyclicity relation of a cochain is inherited by its matrix extension.
Over a ring, degree-`n` cyclic cochains have `c = (-1 : R) ^ n`. -/
theorem matrixCochainExtension_cyclic (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M) (c : R)
    (hφ : ∀ x, φ (x ∘ (finRotate (n + 1)).symm) = c • φ x)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension ι n φ (a ∘ (finRotate (n + 1)).symm) =
      c • matrixCochainExtension ι n φ a := by
  rw [matrixCochainExtension_rotate, matrixCochainExtension_apply]
  simp only [hφ, Finset.smul_sum]

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

/-- Adding a zero diagonal block leaves the matrix extension unchanged. -/
@[simp] theorem matrixCochainExtension_fromBlocks_zero (ι κ : Type*)
    [Fintype ι] [Fintype κ] (n : ℕ)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) => A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    matrixCochainExtension (ι ⊕ κ) n φ (fun j => Matrix.fromBlocks (a j) 0 0 0) =
      matrixCochainExtension ι n φ a := by
  let e : ι ↪ ι ⊕ κ := ⟨Sum.inl, Sum.inl_injective⟩
  have h := matrixCochainExtension_submatrix ι (ι ⊕ κ) e n φ
    (fun j => Matrix.fromBlocks (a j) 0 0 0) (by
      intro j r hr s
      cases r with
      | inl r => exact (hr ⟨r, rfl⟩).elim
      | inr r => cases s <;> simp)
  have he (r : ι) : e r = Sum.inl r := rfl
  have hsub (j) : (Matrix.fromBlocks (a j) 0 0 0).submatrix e e = a j := by
    ext r s
    simp [he]
  simpa only [hsub] using h.symm

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

/-- In degree zero, matrix extension is ordinary trace followed by the unary cochain. -/
@[simp] theorem matrixCochainExtension_zero_eq_trace (ι : Type*) [Fintype ι]
    (φ : MultilinearMap R (fun _ : Fin 1 => A) M) (a : Matrix ι ι A) :
    matrixCochainExtension ι 0 φ (fun _ => a) = φ (fun _ => Matrix.trace a) := by
  classical
  simpa [Matrix.trace, finRotate_one] using
    (φ.map_sum (fun (_ : Fin 1) (r : ι) => a r r)).symm

/-- Applying a linear map to the cochain values commutes with matrix extension. -/
theorem matrixCochainExtension_compMultilinearMap
    {N : Type*} [AddCommMonoid N] [Module R N]
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

end TauCeti
