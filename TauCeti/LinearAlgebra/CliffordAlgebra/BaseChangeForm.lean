/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Matrix
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Clifford algebras under base change of coefficients

Let `q` be a quadratic form on `R^n` and `A` a commutative `R`-algebra, and let
`q_A = QuadraticForm.baseChangeForm q A` be the form on `A^n` with the same coefficients; nothing
assumes `2` invertible. The inclusion `R^n → A^n` sends `q` to `q_A`
(`QuadraticForm.baseChangeForm_algebraMap_comp`), so it induces a morphism of `R`-algebras
`CliffordAlgebra.baseChangeHom q A : C(q) → C(q_A)` with `ι(x) ↦ ι(x_A)`. This is the
characteristic-free analogue of Mathlib's `CliffordAlgebra.ofBaseChangeAux`, which is stated for
Mathlib's `QuadraticForm.baseChange` and so needs `2` invertible. It preserves the even part and
commutes with `reverse`, and `ι(A^n)` is the `A`-span of the images of the coordinate vectors.

## Main results

* `CliffordAlgebra.baseChangeHom`: the algebra morphism `C(q) → C(q_A)`, with
  `CliffordAlgebra.baseChangeHom_ι`.
* `CliffordAlgebra.ι_eq_sum_smul_baseChangeHom`: every vector of `ι(A^n)` is an `A`-linear
  combination of images of the coordinate vectors.
* `CliffordAlgebra.baseChangeHom_mem_even`, `CliffordAlgebra.baseChangeHom_reverse`: it preserves
  the even part and commutes with `reverse`.
-/

public section

namespace CliffordAlgebra

open QuadraticForm (baseChangeForm baseChangeForm_algebraMap_comp)

variable {R n : Type*} [CommRing R] [Fintype n] [LinearOrder n] (q : QuadraticForm R (n → R))
  (A : Type*) [CommRing A] [Algebra R A]

omit [Fintype n] [LinearOrder n] in
/-- The inclusion `R^n → A^n` used to define `baseChangeHom` applies `algebraMap R A` to each
coordinate. -/
private theorem compLeft_linearMap_apply (x : n → R) :
    (Algebra.linearMap R A).compLeft n x = algebraMap R A ∘ x := by
  ext i
  rw [LinearMap.compLeft_apply, Algebra.coe_linearMap]

/-- The morphism of `R`-algebras `C(q) → C(q_A)` induced by the inclusion `R^n → A^n`. This is the
analogue of Mathlib's `CliffordAlgebra.ofBaseChangeAux` for `QuadraticForm.baseChangeForm`, which
needs no hypothesis on `2`. -/
noncomputable def baseChangeHom : CliffordAlgebra q →ₐ[R] CliffordAlgebra (baseChangeForm q A) :=
  lift q ⟨(CliffordAlgebra.ι (baseChangeForm q A)).restrictScalars R ∘ₗ
      (Algebra.linearMap R A).compLeft n,
    fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, compLeft_linearMap_apply,
        ι_sq_scalar, baseChangeForm_algebraMap_comp,
        ← IsScalarTower.algebraMap_apply]⟩

variable {q A}

/-- `baseChangeHom` sends `ι(x)` to `ι(x_A)`. -/
@[simp]
theorem baseChangeHom_ι (x : n → R) :
    baseChangeHom q A (CliffordAlgebra.ι q x) =
      CliffordAlgebra.ι (baseChangeForm q A) (algebraMap R A ∘ x) := by
  rw [baseChangeHom, lift_ι_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    compLeft_linearMap_apply]

/-- Every vector of `ι(A^n)` is an `A`-linear combination of images of vectors of `ι(R^n)`: of the
coordinate vectors. -/
theorem ι_eq_sum_smul_baseChangeHom (m : n → A) :
    CliffordAlgebra.ι (baseChangeForm q A) m =
      ∑ i, m i • baseChangeHom q A (CliffordAlgebra.ι q (Pi.single i 1)) := by
  conv_lhs => rw [pi_eq_sum_univ m]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, baseChangeHom_ι]
  congr 2
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj, Ne.symm hj]

/-- `baseChangeHom` preserves the even part. -/
theorem baseChangeHom_mem_even {x : CliffordAlgebra q} (hx : x ∈ even q) :
    baseChangeHom q A x ∈ even (baseChangeForm q A) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hx ⊢
  induction x, hx using even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R A]
    exact SetLike.algebraMap_mem_graded _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    rw [map_mul, map_mul, baseChangeHom_ι, baseChangeHom_ι]
    simpa only [add_zero] using SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) hx

/-- `baseChangeHom` commutes with `reverse`. -/
theorem baseChangeHom_reverse (x : CliffordAlgebra q) :
    baseChangeHom q A (reverse x) = reverse (baseChangeHom q A x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply R A, reverse.commutes]
  | ι x => rw [reverse_ι, baseChangeHom_ι, reverse_ι]
  | mul x y hx hy => rw [reverse.map_mul, map_mul, map_mul, hx, hy, reverse.map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

end CliffordAlgebra
