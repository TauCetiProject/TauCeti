/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Polynomial.Laurent.Specialization

/-!
# Specializing q-sesquilinear forms at a unit

Let `R` be a commutative ring.  For a unit `ε` of `R` and a module `N` over `R[q,q⁻¹]`, the
specialization `N_ε = TauCeti.LaurentSpecialization ε N` is the base change of `N` along
evaluation at `q = ε`; on it `q` acts as `ε`.

A sesquilinear form `b : N₁ × N₂ → R[q,q⁻¹]`, antilinear in its first argument for the involution
`q ↦ q⁻¹` (`LaurentPolynomial.invert`) and linear in its second, specializes to an `R`-bilinear
form on `N₁_ε₁ × N₂_ε₂` with values `laurentEval ε₂ (b x y)` whenever `ε₁⁻¹ = ε₂`: evaluating
`invert p` at `ε₂` is evaluating `p` at `ε₂⁻¹`.  Taking `ε₁ = ε₂ = ε` needs `ε⁻¹ = ε`; over
`R = ℤ` this is automatic, the two units being `q = 1` and `q = -1`.  This is how the q-Euler form
of a graded category specializes.

Specialization does not preserve nondegeneracy: the Laurent matrix with rows `(1, q)` and `(q, 1)`
has determinant `1 - q²`, which is nonzero, while its value at any `ε` with `ε⁻¹ = ε` has
determinant zero.

## Main definitions

* `LinearMap.laurentSpecialize`: the specialization of a q-sesquilinear form.

## Main results

* `LinearMap.laurentSpecialize_mk_mk`: the specialized form is evaluation of the original one.
* `TauCeti.exists_nondegenerate_and_not_nondegenerate_map_laurentEval`: nondegeneracy of a
  Laurent-polynomial matrix need not survive evaluation at `q = ±1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Sections 1.2 and 3.1, on the specialization of
  the q-Euler form and the warning that it may become degenerate.
-/

public section

open LaurentPolynomial

namespace LinearMap

open TauCeti TauCeti.LaurentSpecialization

variable {R : Type*} [CommRing R] {ε₁ ε₂ : Rˣ}
variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R[T;T⁻¹] N₁] [Module R N₁]
  [IsScalarTower R R[T;T⁻¹] N₁] [AddCommGroup N₂] [Module R[T;T⁻¹] N₂] [Module R N₂]
  [IsScalarTower R R[T;T⁻¹] N₂]

/-- Evaluation at `ε₂` after the involution `q ↦ q⁻¹` is evaluation at `ε₁`, for `ε₁⁻¹ = ε₂`. -/
private theorem laurentEval_invert (hε : ε₁⁻¹ = ε₂) (p : R[T;T⁻¹]) :
    laurentEval ε₂ (invert p) = laurentEval ε₁ p := by
  rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply,
    laurentEval_unique ε₁ ((laurentEval ε₂).comp invert.toAlgHom) (by simp [← hε])]

/-- A q-sesquilinear form evaluated at `q = ε₂`, as an `R`-bilinear form on the unspecialized
modules. -/
private noncomputable def laurentEvalForm
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹]) :
    N₁ →ₗ[R] N₂ →ₗ[R] R :=
  LinearMap.mk₂ R (fun x y => laurentEval ε₂ (b x y))
    (fun x₁ x₂ y => by rw [LinearMap.map_add₂, map_add])
    (fun r x y => by
      rw [← algebraMap_smul (A := R[T;T⁻¹]) r x, LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul]
      simp)
    (fun x y₁ y₂ => by rw [map_add, map_add])
    (fun r x y => by
      rw [← algebraMap_smul (A := R[T;T⁻¹]) r y, map_smul, smul_eq_mul, map_mul,
        AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul])

/-- **The specialization of a q-sesquilinear form**, at `q = ε₁` in the first argument and at
`q = ε₂` in the second, for units with `ε₁⁻¹ = ε₂`.  The form `b` is antilinear in its first
argument for `q ↦ q⁻¹` and linear in its second; its specialization is the `R`-bilinear form on
the specialized modules whose values are the values of `b` evaluated at `ε₂`.  Taking
`ε₁ = ε₂ = ε` specializes both arguments at a unit with `ε⁻¹ = ε`; over `ℤ` this holds for both
units, `q = 1` and `q = -1`. -/
noncomputable def laurentSpecialize
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε₁⁻¹ = ε₂) :
    LaurentSpecialization ε₁ N₁ →ₗ[R] LaurentSpecialization ε₂ N₂ →ₗ[R] R :=
  ((laurentEvalForm (ε₂ := ε₂) b).liftQ₂ _ _
    (fun z hz => by
      rw [Submodule.restrictScalars_mem] at hz
      refine Submodule.smul_induction_on hz (fun p hp x _ => ?_) fun x y hx hy => add_mem hx hy
      refine LinearMap.mem_ker.mpr (LinearMap.ext fun y => ?_)
      change laurentEval ε₂ (b (p • x) y) = 0
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul]
      change laurentEval ε₂ (invert p) * _ = 0
      rw [laurentEval_invert hε, RingHom.mem_ker.mp hp, zero_mul])
    (fun z hz => by
      rw [Submodule.restrictScalars_mem] at hz
      refine Submodule.smul_induction_on hz (fun p hp y _ => ?_) fun x y hx hy => add_mem hx hy
      refine LinearMap.mem_ker.mpr (LinearMap.ext fun x => ?_)
      change laurentEval ε₂ (b x (p • y)) = 0
      rw [map_smul, smul_eq_mul, map_mul, RingHom.mem_ker.mp hp, zero_mul])).compl₁₂
    (Submodule.Quotient.restrictScalarsEquiv R
      (RingHom.ker (laurentEval (R := R) ε₁) • ⊤ : Submodule R[T;T⁻¹] N₁)).symm.toLinearMap
    (Submodule.Quotient.restrictScalarsEquiv R
      (RingHom.ker (laurentEval (R := R) ε₂) • ⊤ : Submodule R[T;T⁻¹] N₂)).symm.toLinearMap

/-- **The specialized form is the evaluated form**: on specialized elements its value is the value
of the Laurent form evaluated at `ε₂`. -/
@[simp]
theorem laurentSpecialize_mk_mk
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε₁⁻¹ = ε₂) (x : N₁) (y : N₂) :
    b.laurentSpecialize hε (LaurentSpecialization.mk ε₁ x) (LaurentSpecialization.mk ε₂ y) =
      laurentEval ε₂ (b x y) := by
  rw [laurentSpecialize, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    mk_apply, mk_apply, Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, LinearMap.liftQ₂_mk]
  rfl

end LinearMap

namespace TauCeti

open scoped Polynomial

/-- **Specialization need not preserve nondegeneracy.**  Over a nontrivial commutative ring `R`,
some two-by-two Laurent-polynomial matrix is nondegenerate while its value at every unit `ε` with
`ε⁻¹ = ε` is degenerate; over `ℤ` these are both specializations `q = 1` and `q = -1`.  The
witness has rows `(1, q)` and `(q, 1)`, with determinant `1 - q²`, a non-zero-divisor. -/
theorem exists_nondegenerate_and_not_nondegenerate_map_laurentEval (R : Type*) [CommRing R]
    [Nontrivial R] :
    ∃ M : Matrix (Fin 2) (Fin 2) R[T;T⁻¹], M.Nondegenerate ∧
      ∀ ε : Rˣ, ε⁻¹ = ε → ¬ (M.map (laurentEval ε)).Nondegenerate := by
  refine ⟨!![1, T 1; T 1, 1], .of_det_mem_nonZeroDivisors ?_, fun ε hε hM => ?_⟩
  · have hmonic : (Polynomial.X ^ 2 - Polynomial.C 1 : R[X]).Monic :=
      Polynomial.monic_X_pow_sub_C 1 two_ne_zero
    have hmem := IsLocalization.map_nonZeroDivisors_le (Submonoid.powers (Polynomial.X : R[X]))
      R[T;T⁻¹] (Submonoid.mem_map_of_mem _ hmonic.mem_nonZeroDivisors)
    rw [algebraMap_eq_toLaurent] at hmem
    have hdet : Matrix.det !![(1 : R[T;T⁻¹]), T 1; T 1, 1] =
        Polynomial.toLaurent (Polynomial.X ^ 2 - Polynomial.C 1 : R[X]) * -1 := by
      rw [Matrix.det_fin_two_of, map_sub, map_pow, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
        map_one, one_mul, ← T_add, sq, ← T_add]
      ring
    rw [hdet]
    exact mul_mem hmem isUnit_one.neg.mem_nonZeroDivisors
  · have hεε : (ε : R) * ε = 1 := by
      nth_rewrite 1 [← hε]
      exact Units.inv_mul ε
    have h := hM.separatingRight.eq_zero_of_mulVec_eq_zero (v := ![(ε : R), -1]) (by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hεε])
    simpa using congrFun h 1

end TauCeti
