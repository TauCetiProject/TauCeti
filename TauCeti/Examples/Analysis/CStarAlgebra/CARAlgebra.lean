/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit
public import TauCeti.LinearAlgebra.Matrix.TensorProduct

/-!
# The CAR algebra as a C⋆-inductive limit

The CAR algebra is the C⋆-inductive limit of the matrix algebras `M_{2^n}` along the unital
embeddings `a ↦ a ⊗ 1₂`. This file builds the connecting ⋆-homomorphisms
`M_{2^n} → M_{2^(n+1)}`, composes them into a directed system over `ℕ`, and checks with the
C⋆-inductive limit API of `TauCeti.Analysis.CStarAlgebra.InductiveLimit` that the limit is a
nonzero unital C⋆-algebra, that it is separable, and that the canonical maps of the stages are
unital isometric ⋆-homomorphisms. The CAR algebra is the UHF algebra of type `2^∞`.

## References

* K. R. Davidson, *C*-Algebras by Example*, §III.5.
-/

public section

noncomputable section

open scoped ComplexOrder Kronecker

namespace TauCeti.CARAlgebra

/-- The matrix algebra `M_{2^n}`, as a C⋆-algebra. -/
abbrev Stage (n : ℕ) : Type := CStarMatrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- The identification `Fin (2^n) × Fin 2 ≃ Fin (2^(n+1))`. -/
def finProdFinTwoEquiv (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ 2 n).symm)

@[simp]
theorem finProdFinTwoEquiv_apply_val (n : ℕ) (p : Fin (2 ^ n) × Fin 2) :
    (finProdFinTwoEquiv n p : ℕ) = p.2 + 2 * p.1 := by
  simp [finProdFinTwoEquiv]

/-- The connecting map `M_{2^n} → M_{2^(n+1)}`, `a ↦ a ⊗ 1₂`. -/
def step (n : ℕ) : Stage n →⋆ₐ[ℂ] Stage (n + 1) :=
  (CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
      ((Matrix.reindexStarAlgEquiv ℂ ℂ (finProdFinTwoEquiv n)).toStarAlgHom.comp
        (Matrix.kroneckerOneStarAlgHom ℂ (Fin 2) (m := Fin (2 ^ n))))).comp
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom

@[simp]
theorem step_apply (n : ℕ) (a : Stage n) :
    step n a = CStarMatrix.ofMatrix (Matrix.reindex (finProdFinTwoEquiv n)
      (finProdFinTwoEquiv n) (CStarMatrix.ofMatrix.symm a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  simp only [step, StarAlgHom.comp_apply, Matrix.kroneckerOneStarAlgHom_apply]
  -- `CStarMatrix.ofMatrixStarAlgEquiv` and its inverse are `CStarMatrix.ofMatrix` and its inverse
  rfl

/-- The connecting map `a ↦ a ⊗ 1₂` is injective. -/
theorem step_injective (n : ℕ) : Function.Injective (step n) :=
  CStarMatrix.ofMatrixStarAlgEquiv.injective.comp
    ((Matrix.reindexStarAlgEquiv ℂ ℂ (finProdFinTwoEquiv n)).injective.comp
      (Matrix.kroneckerOneStarAlgHom_injective.comp
        CStarMatrix.ofMatrixStarAlgEquiv.symm.injective))

/-- The connecting map `M_{2^i} → M_{2^j}` for `i ≤ j`, the composite of the maps `a ↦ a ⊗ 1₂`. -/
def connecting (i j : ℕ) (h : i ≤ j) : Stage i →⋆ₐ[ℂ] Stage j :=
  Nat.leRecOn h (fun {k} g ↦ (step k).comp g) (StarAlgHom.id ℂ _)

/-- The connecting map from a stage to itself is the identity. -/
@[simp]
theorem connecting_self (i : ℕ) : connecting i i le_rfl = StarAlgHom.id ℂ _ :=
  Nat.leRecOn_self _

/-- The connecting map to the next stage after `k` is `a ↦ a ⊗ 1₂` after the map to `k`. -/
theorem connecting_succ {i k : ℕ} (h : i ≤ k) :
    connecting i (k + 1) (h.trans k.le_succ) = (step k).comp (connecting i k h) :=
  Nat.leRecOn_succ h _

/-- The connecting maps compose. -/
theorem connecting_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (connecting j k hjk).comp (connecting i j hij) = connecting i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [connecting_self, StarAlgHom.id_comp]
  | succ k hjk ih => rw [connecting_succ hjk, connecting_succ (hij.trans hjk),
      StarAlgHom.comp_assoc, ih]

/-- The connecting maps form a directed system. -/
instance directedSystem : DirectedSystem Stage fun i j h ↦ connecting i j h where
  map_self i a := by rw [connecting_self, StarAlgHom.coe_id, id_eq]
  map_map k j i hij hjk a := by rw [← connecting_comp hij hjk, StarAlgHom.comp_apply]

end TauCeti.CARAlgebra

namespace TauCeti

open CARAlgebra

/-- The **CAR algebra**, the C⋆-inductive limit of the matrix algebras `M_{2^n}` along the unital
embeddings `a ↦ a ⊗ 1₂`. -/
abbrev CARAlgebra : Type := CStarInductiveLimit Stage fun i j h ↦ connecting i j h

namespace CARAlgebra

/-- The CAR algebra is a unital C⋆-algebra. -/
example : CStarAlgebra CARAlgebra := inferInstance

/-- The CAR algebra is nonzero. -/
example : Nontrivial CARAlgebra := inferInstance

/-- The CAR algebra is separable, as a limit of a countable system of finite-dimensional
algebras. -/
example : TopologicalSpace.SeparableSpace CARAlgebra := inferInstance

/-- The connecting maps are injective. -/
theorem connecting_injective (i j : ℕ) (h : i ≤ j) : Function.Injective (connecting i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [connecting_self]; exact Function.injective_id
  | succ k hik ih => rw [connecting_succ hik]; exact (step_injective k).comp ih

/-- The canonical maps `M_{2^n} → CARAlgebra` are isometric. -/
theorem isometry_of (n : ℕ) :
    Isometry (CStarInductiveLimit.of Stage (fun i j h ↦ connecting i j h) n) :=
  CStarInductiveLimit.isometry_of fun j h ↦ connecting_injective n j h

/-- The canonical maps `M_{2^n} → CARAlgebra` are unital. -/
example (n : ℕ) : CStarInductiveLimit.of Stage (fun i j h ↦ connecting i j h) n 1 = 1 :=
  CStarInductiveLimit.of_one n

end CARAlgebra

end TauCeti
