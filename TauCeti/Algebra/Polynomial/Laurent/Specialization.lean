/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# Specializing Laurent modules at a unit

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

## Main definitions

* `TauCeti.LaurentSpecialization ε N`: the specialization of an `R[q,q⁻¹]`-module at `q = ε`.
* `TauCeti.LaurentSpecialization.mk`: the specialization map `N → N_ε`.
* `TauCeti.LaurentSpecialization.lift`: the universal property for `R`-linear maps.
* `TauCeti.LaurentSpecialization.map`: specialize a Laurent-linear map.
* `TauCeti.LaurentSpecialization.basis`: specialize a Laurent-module basis coefficientwise, as the
  base-change basis `IsBaseChange.basis`.

## Main results

* `TauCeti.LaurentSpecialization.mk_smul`: a Laurent scalar acts on `N_ε` by its value at `ε`.
* `TauCeti.LaurentSpecialization.lift_mk` and `TauCeti.LaurentSpecialization.hom_ext`: the
  universal property.
* `TauCeti.LaurentSpecialization.isBaseChange`: the specialization is the base change along
  evaluation at `ε`, for any algebra structure on `R` given by that evaluation.
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
theorem mk_smul (p : R[T;T⁻¹]) (x : N) : p • mk ε x = laurentEval ε p • mk ε x := by
  rw [← map_smul]
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
    lift ε f hf (mk ε x) = f x := by
  rw [lift, LinearMap.comp_apply, LinearEquiv.coe_coe, mk_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]

variable {M : Type*} [AddCommGroup M] [Module R[T;T⁻¹] M] [Module R M]
  [IsScalarTower R R[T;T⁻¹] M]

/-- A Laurent-linear map induces an `R`-linear map between specializations at the same unit. -/
noncomputable def map (f : N →ₗ[R[T;T⁻¹]] M) :
    LaurentSpecialization ε N →ₗ[R] LaurentSpecialization ε M :=
  ((RingHom.ker (laurentEval (R := R) ε) • ⊤ : Submodule R[T;T⁻¹] N).mapQ
    (RingHom.ker (laurentEval (R := R) ε) • ⊤) f
    (Submodule.smul_top_le_comap_smul_top _ f)).restrictScalars R

/-- Specializing a Laurent-linear map commutes with taking quotient classes. -/
@[simp]
theorem map_mk (f : N →ₗ[R[T;T⁻¹]] M) (x : N) :
    map ε f (mk ε x) = mk ε (f x) :=
  (Submodule.mapQ_apply _ _ f (h := Submodule.smul_top_le_comap_smul_top _ f) x)

/-- An `R`-linear map out of the specialization is determined by its values on specialized
elements. -/
@[ext]
theorem hom_ext {f g : LaurentSpecialization ε N →ₗ[R] A} (h : ∀ x, f (mk ε x) = g (mk ε x)) :
    f = g :=
  LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := mk_surjective ε y
    exact h x

/-- Specializing the identity map gives the identity on the specialization. -/
@[simp]
theorem map_id : map ε (LinearMap.id : N →ₗ[R[T;T⁻¹]] N) = LinearMap.id := by
  apply hom_ext
  intro x
  simp

variable {P : Type*} [AddCommGroup P] [Module R[T;T⁻¹] P] [Module R P]
  [IsScalarTower R R[T;T⁻¹] P]

/-- Specialization preserves composition of Laurent-linear maps. -/
@[simp]
theorem map_comp (g : M →ₗ[R[T;T⁻¹]] P) (f : N →ₗ[R[T;T⁻¹]] M) :
    map ε (g.comp f) = (map ε g).comp (map ε f) := by
  apply hom_ext
  intro x
  simp

section Basis

open scoped TensorProduct

/-- Under an `R[q,q⁻¹]`-algebra structure on `R` given by evaluation at `ε`, Laurent scalars and
coefficients act compatibly on the specialization at `ε`. -/
theorem isScalarTower [Algebra R[T;T⁻¹] R] (h : ∀ p, algebraMap R[T;T⁻¹] R p = laurentEval ε p) :
    IsScalarTower R[T;T⁻¹] R (LaurentSpecialization ε N) :=
  ⟨fun p r y => by
    obtain ⟨x, rfl⟩ := mk_surjective ε y
    rw [Algebra.smul_def, mul_smul, h, mk_apply, ← Submodule.Quotient.mk_smul, ← mk_apply,
      mk_smul]⟩

/-- **The specialization at `ε` is the base change along evaluation at `ε`.**  This is stated for
any `R[q,q⁻¹]`-algebra structure on `R` whose algebra map is `TauCeti.laurentEval ε`, since that
structure depends on `ε` and so is not an instance. -/
theorem isBaseChange [Algebra R[T;T⁻¹] R] (h : ∀ p, algebraMap R[T;T⁻¹] R p = laurentEval ε p)
    [IsScalarTower R[T;T⁻¹] R (LaurentSpecialization ε N)] :
    IsBaseChange R (mk ε : N →ₗ[R[T;T⁻¹]] LaurentSpecialization ε N) := by
  have hC (r : R) : algebraMap R R[T;T⁻¹] r • (1 : R) = r := by
    rw [Algebra.smul_def, h, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_one]
  let g : N →ₗ[R] R ⊗[R[T;T⁻¹]] N :=
    { toFun x := 1 ⊗ₜ x
      map_add' := TensorProduct.tmul_add 1
      map_smul' r x := by
        rw [RingHom.id_apply, ← algebraMap_smul R[T;T⁻¹] r x, ← TensorProduct.smul_tmul, hC,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one] }
  have hg (x : N) : g ((T 1 : R[T;T⁻¹]) • x) = (ε : R) • g x := by
    dsimp only [g, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, h, laurentEval_T_one, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨Function.LeftInverse.injective (g := lift ε g hg) fun z => ?_, fun y => ?_⟩
  · induction z with
    | tmul s x => simp [g, TensorProduct.smul_tmul']
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  · obtain ⟨x, rfl⟩ := mk_surjective ε y
    exact ⟨1 ⊗ₜ x, by simp⟩

variable {ι : Type*}

/-- A Laurent-module basis specializes to a basis over the coefficient ring. It is the base-change
basis `IsBaseChange.basis` along evaluation at `ε`: its vectors are the classes of the original
basis vectors, and its coordinates are obtained by evaluating Laurent coordinates at `ε`. -/
noncomputable def basis (b : Module.Basis ι R[T;T⁻¹] N) :
    Module.Basis ι R (LaurentSpecialization ε N) :=
  letI : Algebra R[T;T⁻¹] R := (laurentEval ε).toAlgebra
  haveI := isScalarTower ε (N := N) fun _ ↦ rfl
  (isBaseChange ε fun _ ↦ rfl).basis b

/-- Specializing a basis specializes each basis vector. -/
@[simp]
theorem basis_apply (b : Module.Basis ι R[T;T⁻¹] N) (i : ι) :
    basis ε b i = mk ε (b i) := by
  let _ : Algebra R[T;T⁻¹] R := (laurentEval ε).toAlgebra
  have := isScalarTower ε (N := N) fun _ ↦ rfl
  exact IsBaseChange.basis_apply ..

/-- Coordinates in the specialized basis are evaluated Laurent coordinates. -/
@[simp]
theorem basis_repr_mk_apply (b : Module.Basis ι R[T;T⁻¹] N) (x : N) (i : ι) :
    (basis ε b).repr (mk ε x) i = laurentEval ε (b.repr x i) := by
  let _ : Algebra R[T;T⁻¹] R := (laurentEval ε).toAlgebra
  have := isScalarTower ε (N := N) fun _ ↦ rfl
  exact IsBaseChange.basis_repr_comp_apply ..

end Basis

end LaurentSpecialization

end TauCeti
