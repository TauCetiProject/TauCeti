/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import TauCeti.Algebra.Star.StarAlgHom
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic
public import TauCeti.LinearAlgebra.Matrix.TensorProduct
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Ideal

/-!
# The CAR algebra as a C⋆-inductive limit

The CAR algebra is the C⋆-inductive limit of the matrix algebras `M_{2^n}` along the unital
embeddings `a ↦ a ⊗ 1₂`. It is the UHF algebra of type `2^∞`.

## Main definitions

* `TauCeti.CARAlgebra.Stage n`: the matrix algebra `M_{2^n}`, as a C⋆-algebra.
* `TauCeti.CARAlgebra.step n`: the injective unital ⋆-homomorphism `M_{2^n} → M_{2^(n+1)}`,
  `a ↦ a ⊗ 1₂`.
* `TauCeti.CARAlgebra`: the C⋆-inductive limit of the stages along the composites
  `StarAlgHom.natLERec step` of these maps.

## Main statements

* `TauCeti.CARAlgebra.isometry_of`: the canonical maps `M_{2^n} → CARAlgebra` are isometric.
* `TauCeti.CARAlgebra.forall_isClosed_eq_bot_or_eq_top`: the CAR algebra is simple, since every
  stage `M_{2^n}` is.

## References

* K. R. Davidson, *C*-Algebras by Example*, §III.5.
* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.8.2.5.
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

@[simp]
theorem finProdFinTwoEquiv_symm_apply_fst_val (n : ℕ) (i : Fin (2 ^ (n + 1))) :
    (((finProdFinTwoEquiv n).symm i).1 : ℕ) = i / 2 := by
  simp [finProdFinTwoEquiv, Fin.divNat]

@[simp]
theorem finProdFinTwoEquiv_symm_apply_snd_val (n : ℕ) (i : Fin (2 ^ (n + 1))) :
    (((finProdFinTwoEquiv n).symm i).2 : ℕ) = i % 2 := by
  simp [finProdFinTwoEquiv, Fin.modNat]

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

end TauCeti.CARAlgebra

namespace TauCeti

open CARAlgebra

/-- The **CAR algebra**, the C⋆-inductive limit of the matrix algebras `M_{2^n}` along the unital
embeddings `a ↦ a ⊗ 1₂`. -/
abbrev CARAlgebra : Type := CStarInductiveLimit Stage (StarAlgHom.natLERec step)

/-- The canonical maps `M_{2^n} → CARAlgebra` are isometric. -/
theorem CARAlgebra.isometry_of (n : ℕ) :
    Isometry (CStarInductiveLimit.of Stage (StarAlgHom.natLERec step) n) :=
  CStarInductiveLimit.isometry_of (StarAlgHom.natLERec_injective step_injective n)

/-- **The CAR algebra is simple**: its only closed two-sided ideals are `⊥` and `⊤`, because every
stage `M_{2^n}` is a simple ring (Blackadar, II.8.2.5). -/
theorem CARAlgebra.forall_isClosed_eq_bot_or_eq_top (J : TwoSidedIdeal CARAlgebra)
    (hJ : IsClosed (J : Set CARAlgebra)) : J = ⊥ ∨ J = ⊤ :=
  CStarInductiveLimit.forall_isClosed_eq_bot_or_eq_top
    (fun _ I _ ↦ IsSimpleOrder.eq_bot_or_eq_top I) J hJ

end TauCeti
