/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Algebra.Polynomial.LaurentSpecialization

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

/-- The second argument of a specialized form, before specializing the first argument. -/
private noncomputable def laurentSpecializeRight
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹]) (x : N₁) :
    LaurentSpecialization ε₂ N₂ →ₗ[R] R :=
  lift ε₂ ((laurentEval ε₂).toLinearMap ∘ₗ (b x).restrictScalars R) fun y => by
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, smul_eq_mul,
      AlgHom.toLinearMap_apply, map_mul, laurentEval_T_one, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, smul_eq_mul]

omit [Module R N₁] [IsScalarTower R R[T;T⁻¹] N₁] in
@[simp]
private theorem laurentSpecializeRight_mk
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹]) (x : N₁)
    (y : N₂) :
    laurentSpecializeRight (ε₂ := ε₂) b x (LaurentSpecialization.mk ε₂ y) =
      laurentEval ε₂ (b x y) := by
  rw [laurentSpecializeRight, lift_mk, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgHom.toLinearMap_apply]

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
  lift ε₁
    { toFun := laurentSpecializeRight b
      map_add' := fun x₁ x₂ => hom_ext ε₂ fun y => by
        rw [LinearMap.add_apply, laurentSpecializeRight_mk, laurentSpecializeRight_mk,
          laurentSpecializeRight_mk, LinearMap.map_add₂, map_add]
      map_smul' := fun r x => hom_ext ε₂ fun y => by
        rw [← algebraMap_smul (A := R[T;T⁻¹]) r x, LinearMap.smul_apply,
          laurentSpecializeRight_mk, laurentSpecializeRight_mk, LinearMap.map_smulₛₗ₂]
        simp [smul_eq_mul] }
    fun x => hom_ext ε₂ fun y => by
      have hq : laurentEval ε₂ ((invert (R := R)).toRingEquiv.toRingHom (T 1)) = ε₁ := by
        simp [← hε]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, laurentSpecializeRight_mk]
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, hq, smul_eq_mul]

/-- **The specialized form is the evaluated form**: on specialized elements its value is the value
of the Laurent form evaluated at `ε₂`. -/
@[simp]
theorem laurentSpecialize_mk_mk
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε₁⁻¹ = ε₂) (x : N₁) (y : N₂) :
    b.laurentSpecialize hε (LaurentSpecialization.mk ε₁ x) (LaurentSpecialization.mk ε₂ y) =
      laurentEval ε₂ (b x y) := by
  rw [laurentSpecialize, lift_mk]
  exact laurentSpecializeRight_mk b x y

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
