/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.Polynomial.Laurent

/-!
# Specializing Laurent modules and q-sesquilinear forms at a unit

Let `R` be a commutative ring and `ε` a unit of `R`.  Evaluation at `q = ε` is the `R`-algebra map
`TauCeti.laurentEval ε : R[q,q⁻¹] → R`.  For a module `N` over `R[q,q⁻¹]`, the **specialization**
of `N` at `ε` is the quotient

`N_ε = N ⧸ I_ε N`,  where `I_ε = ker (laurentEval ε)`.

This is the base change `R ⊗_{R[q,q⁻¹]} N` along evaluation: evaluation is surjective, so
`R[q,q⁻¹] ⧸ I_ε ≃ R` (`Ideal.quotientKerAlgEquivOfSurjective`), and
`(R[q,q⁻¹] ⧸ I_ε) ⊗ N ≃ N ⧸ I_ε N` is `TensorProduct.quotTensorEquivQuotSMul`.  The quotient
presentation is used because it needs no auxiliary algebra structure of `R` over `R[q,q⁻¹]`.
On `N_ε` every Laurent scalar acts through its value at `ε`; in particular `q` acts as `ε`.  The
universal property says that `R`-linear maps out of `N_ε` are the `R`-linear maps out of `N`
turning multiplication by `q` into multiplication by `ε`.

A sesquilinear form `b : N₁ × N₂ → R[q,q⁻¹]`, antilinear in its first argument for the involution
`q ↦ q⁻¹` (`LaurentPolynomial.invert`) and linear in its second, specializes to an `R`-bilinear
form on `N₁_ε × N₂_ε` with values `laurentEval ε (b x y)` exactly when evaluation at `ε` does not
see the involution, that is when `ε⁻¹ = ε`.  Over `R = ℤ` this is automatic, the two units being
`q = 1` and `q = -1`.  This is how the q-Euler form of a graded category specializes.

Specialization does not preserve nondegeneracy: the Laurent matrix with rows `(1, q)` and `(q, 1)`
has determinant `1 - q²`, which is nonzero, while its value at any `ε` with `ε⁻¹ = ε` has
determinant zero.

## Main definitions

* `TauCeti.LaurentSpecialization ε N`: the specialization of an `R[q,q⁻¹]`-module at `q = ε`.
* `TauCeti.LaurentSpecialization.mk`: the specialization map `N → N_ε`.
* `TauCeti.LaurentSpecialization.lift`: the universal property for `R`-linear maps.
* `LinearMap.laurentSpecialize`: the specialization of a q-sesquilinear form.

## Main results

* `TauCeti.LaurentSpecialization.mk_smul`: a Laurent scalar acts on `N_ε` by its value at `ε`.
* `TauCeti.LaurentSpecialization.lift_mk` and `TauCeti.LaurentSpecialization.hom_ext`: the
  universal property.
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

namespace TauCeti

variable {R : Type*} [CommRing R] (ε : Rˣ)

/-- **The specialization of an `R[q,q⁻¹]`-module at `q = ε`**: the quotient of `N` by the kernel of
evaluation at `ε` acting on `N`.  It is the base change of `N` along
`TauCeti.laurentEval ε : R[q,q⁻¹] → R`, and `q` acts on it as `ε`. -/
abbrev LaurentSpecialization (N : Type*) [AddCommGroup N] [Module R[T;T⁻¹] N] :=
  N ⧸ (RingHom.ker (laurentEval (R := R) ε) • ⊤ : Submodule R[T;T⁻¹] N)

namespace LaurentSpecialization

variable {N : Type*} [AddCommGroup N] [Module R[T;T⁻¹] N]

/-- The specialization map `N → N_ε`. -/
noncomputable def mk : N →ₗ[R[T;T⁻¹]] LaurentSpecialization ε N :=
  Submodule.mkQ _

/-- The specialization of an element is its quotient class. -/
theorem mk_apply (x : N) : mk ε x = Submodule.Quotient.mk x :=
  (rfl)

/-- Every element of the specialization is specialized from `N`. -/
theorem mk_surjective : Function.Surjective (mk ε : N → LaurentSpecialization ε N) :=
  Submodule.mkQ_surjective _

variable [Module R N] [IsScalarTower R R[T;T⁻¹] N]

/-- **A Laurent scalar acts on the specialization at `ε` by its value at `ε`.**  In particular
`q` acts as `ε`. -/
@[simp]
theorem mk_smul (p : R[T;T⁻¹]) (x : N) : mk ε (p • x) = laurentEval ε p • mk ε x := by
  have hp :
      p - algebraMap R R[T;T⁻¹] (laurentEval ε p) ∈ RingHom.ker (laurentEval (R := R) ε) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have hmem :=
    Submodule.smul_mem_smul (N := (⊤ : Submodule R[T;T⁻¹] N)) hp (Submodule.mem_top (x := x))
  rw [sub_smul, algebraMap_smul] at hmem
  rw [mk_apply, mk_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact hmem

variable {A : Type*} [AddCommGroup A] [Module R A]

/-- An `R`-linear map turning multiplication by `q` into multiplication by `ε` turns every Laurent
scalar into its value at `ε`. -/
private theorem map_smul_eq_laurentEval_smul (f : N →ₗ[R] A)
    (hf : ∀ x, f ((T 1 : R[T;T⁻¹]) • x) = (ε : R) • f x) (p : R[T;T⁻¹]) (x : N) :
    f (p • x) = laurentEval ε p • f x := by
  have hinv : ∀ x, f ((T (-1) : R[T;T⁻¹]) • x) = ((ε⁻¹ : Rˣ) : R) • f x := fun x => by
    have hx := hf ((T (-1) : R[T;T⁻¹]) • x)
    rw [smul_smul, ← T_add, add_neg_cancel, T_zero, one_smul] at hx
    rw [hx, smul_smul, Units.inv_mul, one_smul]
  have hT : ∀ (n : ℤ) (x : N), f ((T n : R[T;T⁻¹]) • x) = ((ε ^ n : Rˣ) : R) • f x := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        intro x
        rw [T_add, mul_smul, ih, hf, smul_smul, zpow_add_one, Units.val_mul]
    | pred k ih =>
        intro x
        rw [sub_eq_add_neg, T_add, mul_smul, ih, hinv, smul_smul, zpow_add,
          zpow_neg_one, Units.val_mul]
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add, add_smul]
  | C_mul_T n a =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul, map_smul, hT, map_mul, laurentEval_T,
        AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_smul]

/-- **The universal property of the specialization at `ε`**: an `R`-linear map out of `N` which
turns multiplication by `q` into multiplication by `ε` factors through `N_ε`. -/
noncomputable def lift (f : N →ₗ[R] A) (hf : ∀ x, f ((T 1 : R[T;T⁻¹]) • x) = (ε : R) • f x) :
    LaurentSpecialization ε N →ₗ[R] A :=
  (((RingHom.ker (laurentEval (R := R) ε) • ⊤ : Submodule R[T;T⁻¹] N).restrictScalars R).liftQ f
    fun z hz => by
      rw [Submodule.restrictScalars_mem] at hz
      refine Submodule.smul_induction_on hz (fun p hp x _ => ?_) fun x y hx hy => add_mem hx hy
      rw [LinearMap.mem_ker, map_smul_eq_laurentEval_smul ε f hf, RingHom.mem_ker.mp hp,
        zero_smul]) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R _).symm.toLinearMap

/-- The map induced on the specialization agrees with the original map on specialized elements. -/
@[simp]
theorem lift_mk (f : N →ₗ[R] A) (hf : ∀ x, f ((T 1 : R[T;T⁻¹]) • x) = (ε : R) • f x) (x : N) :
    lift ε f hf (mk ε x) = f x :=
  (rfl)

/-- An `R`-linear map out of the specialization is determined by its values on specialized
elements. -/
@[ext]
theorem hom_ext {f g : LaurentSpecialization ε N →ₗ[R] A} (h : ∀ x, f (mk ε x) = g (mk ε x)) :
    f = g :=
  LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := mk_surjective ε y
    exact h x

end LaurentSpecialization

end TauCeti

namespace LinearMap

open TauCeti TauCeti.LaurentSpecialization

variable {R : Type*} [CommRing R] {ε : Rˣ}
variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R[T;T⁻¹] N₁] [Module R N₁]
  [IsScalarTower R R[T;T⁻¹] N₁] [AddCommGroup N₂] [Module R[T;T⁻¹] N₂] [Module R N₂]
  [IsScalarTower R R[T;T⁻¹] N₂]

/-- The second argument of a specialized form, before specializing the first argument. -/
private noncomputable def laurentSpecializeRight
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹]) (x : N₁) :
    LaurentSpecialization ε N₂ →ₗ[R] R :=
  lift ε ((laurentEval ε).toLinearMap ∘ₗ (b x).restrictScalars R) fun y => by
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, smul_eq_mul,
      AlgHom.toLinearMap_apply, map_mul, laurentEval_T_one, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, smul_eq_mul]

omit [Module R N₁] [IsScalarTower R R[T;T⁻¹] N₁] in
@[simp]
private theorem laurentSpecializeRight_mk
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹]) (x : N₁)
    (y : N₂) :
    laurentSpecializeRight (ε := ε) b x (LaurentSpecialization.mk ε y) = laurentEval ε (b x y) :=
  (rfl)

/-- **The specialization of a q-sesquilinear form at `q = ε`**, for a unit with `ε⁻¹ = ε`.  The form
`b` is antilinear in its first argument for `q ↦ q⁻¹` and linear in its second; its specialization
is the `R`-bilinear form on the specialized modules whose values are the values of `b` evaluated
at `ε`.  Over `ℤ` the hypothesis holds for both units, `q = 1` and `q = -1`. -/
noncomputable def laurentSpecialize
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε⁻¹ = ε) :
    LaurentSpecialization ε N₁ →ₗ[R] LaurentSpecialization ε N₂ →ₗ[R] R :=
  lift ε
    { toFun := laurentSpecializeRight b
      map_add' := fun x₁ x₂ => hom_ext ε fun y => by
        rw [LinearMap.add_apply, laurentSpecializeRight_mk, laurentSpecializeRight_mk,
          laurentSpecializeRight_mk, LinearMap.map_add₂, map_add]
      map_smul' := fun r x => hom_ext ε fun y => by
        rw [← algebraMap_smul (A := R[T;T⁻¹]) r x, LinearMap.smul_apply,
          laurentSpecializeRight_mk, laurentSpecializeRight_mk, LinearMap.map_smulₛₗ₂]
        simp [smul_eq_mul] }
    fun x => hom_ext ε fun y => by
      have hq : laurentEval ε ((invert (R := R)).toRingEquiv.toRingHom (T 1)) = ε := by
        simpa using congrArg Units.val hε
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, laurentSpecializeRight_mk]
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, hq, smul_eq_mul]

/-- **The specialized form is the evaluated form**: on specialized elements its value is the value
of the Laurent form evaluated at `ε`. -/
@[simp]
theorem laurentSpecialize_mk_mk
    (b : N₁ →ₛₗ[(invert (R := R)).toRingEquiv.toRingHom] N₂ →ₗ[R[T;T⁻¹]] R[T;T⁻¹])
    (hε : ε⁻¹ = ε) (x : N₁) (y : N₂) :
    b.laurentSpecialize hε (LaurentSpecialization.mk ε x) (LaurentSpecialization.mk ε y) =
      laurentEval ε (b x y) :=
  (rfl)

end LinearMap

namespace TauCeti

/-- **Specialization need not preserve nondegeneracy.**  Over a domain `R`, some two-by-two
Laurent-polynomial matrix is nondegenerate while its value at every unit `ε` with `ε⁻¹ = ε` is
degenerate; over `ℤ` these are both specializations `q = 1` and `q = -1`.  The witness has rows
`(1, q)` and `(q, 1)`, with determinant `1 - q²`. -/
theorem exists_nondegenerate_and_not_nondegenerate_map_laurentEval (R : Type*) [CommRing R]
    [IsDomain R] :
    ∃ M : Matrix (Fin 2) (Fin 2) R[T;T⁻¹], M.Nondegenerate ∧
      ∀ ε : Rˣ, ε⁻¹ = ε → ¬ (M.map (laurentEval ε)).Nondegenerate := by
  refine ⟨!![1, T 1; T 1, 1], ?_, fun ε hε => ?_⟩
  · rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_fin_two_of, one_mul, ← T_add,
      sub_ne_zero]
    intro h
    have h2 := congrArg (fun p : R[T;T⁻¹] => p.coeff 0) h
    simp at h2
  · have hεε : (ε : R) * ε = 1 := by
      nth_rewrite 1 [← hε]
      exact Units.inv_mul ε
    rw [Matrix.nondegenerate_iff_det_ne_zero, not_not, Matrix.det_fin_two]
    simp [hεε]

end TauCeti
