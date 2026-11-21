/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Hochschild.Complex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Acyclicity of cofree Hochschild coefficients

For a bialgebra `H` over a commutative ring `R` and any `R`-module `N`, the Hochschild
complex with coefficients in the cofree comodule `N ⊗ H` is exact in positive degrees.
The contraction applies the counit to the first `H` factor, retaining all subsequent
factors in their original order. In degree zero its homotopy identity is the identity
minus the projection `n ⊗ h ↦ ε(h) • (n ⊗ 1)`.

This gives explicit primitives for all positive-degree cocycles. Neither `H` nor `N`
needs to be flat, finite or injective; the result concerns the Hochschild complex itself.
It is the cofree acyclicity calculation used to compare that complex with derived
invariants for flat Hopf algebras.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§4.14–4.16.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) [CommRing R] (H : Type v)
  (N : Type w) [AddCommGroup N] [Module R N]

attribute [local instance] cofree

section Coalgebra

variable [AddCommMonoid H] [Module R H] [Coalgebra R H]

/-- The contraction of the Hochschild complex of the cofree comodule `N ⊗ H`.
It applies the counit to its first `H` factor, leaving the remaining factors in order. -/
noncomputable def hochschildCofreeContraction : (n : ℕ) →
    (hochschildCochains R H (N ⊗[R] H) (n + 1) →ₗ[R]
      hochschildCochains R H (N ⊗[R] H) n)
  | 0 => ((TensorProduct.rid R N).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := H)).lTensor N).rTensor H
  | n + 1 => (hochschildCofreeContraction n).rTensor H

/-- In degree one, the contraction evaluates the first coalgebra factor by the counit. -/
@[simp]
theorem hochschildCofreeContraction_zero_tmul (n : N) (a b : H) :
    hochschildCofreeContraction R H N 0 ((n ⊗ₜ[R] a) ⊗ₜ[R] b) =
      Coalgebra.counit (R := R) a • (n ⊗ₜ[R] b) := by
  simp [hochschildCofreeContraction, TensorProduct.smul_tmul']

/-- In higher degrees, the contraction leaves the last tensor factor untouched. -/
theorem hochschildCofreeContraction_succ (n : ℕ) :
    hochschildCofreeContraction R H N (n + 1) =
      (hochschildCofreeContraction R H N n).rTensor H :=
  (rfl)

end Coalgebra

variable [Semiring H] [Bialgebra R H]

/-- The contraction cancels the first coface. -/
@[simp]
theorem hochschildCofreeContraction_comp_coface_zero (n : ℕ) :
    hochschildCofreeContraction R H N n ∘ₗ
        hochschildCoface R H (N ⊗[R] H) n 0 = LinearMap.id := by
  induction n with
  | zero =>
    -- Present the first index as a cast so the recursive coface formula applies.
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
      hochschildCoface_zero_castSucc]
    exact rTensor_rid_comp_lTensor_counit_comp_cofreeCoact
  | succ n ih =>
    -- Two casts select precisely the recursively tensored cofaces.
    rw [show (0 : Fin (n + 3)) = (0 : Fin (n + 1)).castSucc.castSucc from rfl,
      hochschildCoface_succ_castSucc_castSucc, hochschildCofreeContraction_succ,
      ← LinearMap.rTensor_comp, Fin.castSucc_zero, ih, LinearMap.rTensor_id]

/-- The contraction commutes with every later coface, shifting its index down by one. -/
@[simp]
theorem hochschildCofreeContraction_comp_coface_succ (n : ℕ) (i : Fin (n + 2)) :
    hochschildCofreeContraction R H N (n + 1) ∘ₗ
        hochschildCoface R H (N ⊗[R] H) (n + 1) i.succ =
      hochschildCoface R H (N ⊗[R] H) n i ∘ₗ
        hochschildCofreeContraction R H N n := by
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildCoface_last, hochschildCoface_last,
      hochschildCofreeContraction_succ]
    ext x
    simp
  | cast i =>
    rw [Fin.succ_castSucc, hochschildCofreeContraction_succ]
    induction n with
    | zero =>
      have hi : i = Fin.last 0 := Fin.ext (by omega)
      subst i
      rw [Fin.succ_last, hochschildCoface_succ_castSucc_last,
        hochschildCoface_zero_castSucc]
      exact (cofreeCoact_comp_rTensor _).symm
    | succ n ih =>
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, hochschildCoface_succ_castSucc_last,
          hochschildCoface_succ_castSucc_last, hochschildCofreeContraction_succ]
        exact (cofreeCoact_comp_rTensor _).symm
      | cast i =>
        rw [Fin.succ_castSucc, hochschildCoface_succ_castSucc_castSucc,
          hochschildCoface_succ_castSucc_castSucc, hochschildCofreeContraction_succ,
          ← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
        exact congrArg (LinearMap.rTensor H) (ih i)

/-- The contracting homotopy identity in positive degrees, with no sign change in the
contraction: `s d + d s = id`. -/
theorem hochschildCofreeContraction_comp_differential (n : ℕ) :
    hochschildCofreeContraction R H N (n + 1) ∘ₗ
        hochschildDifferential R H (N ⊗[R] H) (n + 1) +
      hochschildDifferential R H (N ⊗[R] H) n ∘ₗ
        hochschildCofreeContraction R H N n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [hochschildDifferential_apply R H (N ⊗[R] H),
    hochschildDifferential_apply R H (N ⊗[R] H)]
  simp only [map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  have hzero := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_coface_zero R H N (n + 1)) x
  have hsucc (i : Fin (n + 2)) := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_coface_succ R H N n i) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hzero hsucc
  rw [hzero]
  simp_rw [hsucc]
  simp only [Fin.val_zero, pow_zero, one_zsmul, LinearMap.id_apply, Fin.val_succ,
    pow_succ, mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  abel

/-- In degree zero, the homotopy retracts onto the counit evaluation followed by
`n ↦ n ⊗ 1`. -/
theorem hochschildCofreeContraction_zero_comp_differential (x : N ⊗[R] H) :
    hochschildCofreeContraction R H N 0
        (hochschildDifferential R H (N ⊗[R] H) 0 x) =
      x - TensorProduct.rid R N
        ((Coalgebra.counit (R := R) (A := H)).lTensor N x) ⊗ₜ[R] (1 : H) := by
  rw [hochschildDifferential_zero_apply, map_sub]
  have h := LinearMap.congr_fun
    (hochschildCofreeContraction_comp_coface_zero R H N 0) x
  -- The first index must be a cast for the degree-zero coface formula to match.
  rw [LinearMap.comp_apply,
    show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl,
    hochschildCoface_zero_castSucc, LinearMap.id_apply] at h
  rw [h]
  rfl

/-- Every positive-degree Hochschild cocycle with cofree coefficients has the explicit
primitive given by the contraction. -/
theorem hochschildDifferential_contraction_of_cocycle (n : ℕ)
    (x : hochschildCochains R H (N ⊗[R] H) (n + 1))
    (hx : hochschildDifferential R H (N ⊗[R] H) (n + 1) x = 0) :
    hochschildDifferential R H (N ⊗[R] H) n
      (hochschildCofreeContraction R H N n x) = x := by
  have h := LinearMap.congr_fun (hochschildCofreeContraction_comp_differential R H N n) x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero, zero_add,
    LinearMap.id_apply] using h

/-- The Hochschild complex of a cofree comodule is exact in every positive degree. -/
theorem exactAt_hochschildComplex_cofree (n : ℕ) :
    (hochschildComplex R H (N ⊗[R] H)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [hochschildComplex_d]
  intro x hx
  refine ⟨hochschildCofreeContraction R H N n x, ?_⟩
  exact hochschildDifferential_contraction_of_cocycle R H N n x hx

/-- All positive-degree Hochschild cohomology objects of a cofree comodule vanish. -/
theorem isZero_homology_hochschildComplex_cofree (n : ℕ) :
    Limits.IsZero ((hochschildComplex R H (N ⊗[R] H)).homology (n + 1)) :=
  (exactAt_hochschildComplex_cofree R H N n).isZero_homology

end TauCeti.Comodule
