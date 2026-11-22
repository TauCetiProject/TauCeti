/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Semilinear functoriality of exterior algebras

A `σ`-semilinear map `g : M →ₛₗ[σ] N` along `σ : A →+* B` induces a ring homomorphism
`ExteriorAlgebra.mapSemilinear g : ExteriorAlgebra A M →+* ExteriorAlgebra B N`, compatible with
`algebraMap`, `ι`, scalar multiplication, `ιMulti`, `ExteriorAlgebra.map`, identity, composition,
and the grade involution.
-/

public section

namespace ExteriorAlgebra

variable {A B C M N P : Type*} [CommRing A] [CommRing B] [CommRing C]
  {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]

private noncomputable abbrev algebraOfRingHom (σ : A →+* B) (N : Type*) [AddCommGroup N]
    [Module B N] : Algebra A (ExteriorAlgebra B N) :=
  ((algebraMap B _).comp σ).toAlgebra' fun a x ↦ Algebra.commutes (σ a) x

/-- **Semilinear functoriality of the exterior algebra.** A `σ`-semilinear map `g : M →ₛₗ[σ] N`
induces `ExteriorAlgebra A M →+* ExteriorAlgebra B N` sending `algebraMap a` to `algebraMap (σ a)`
and `ι A m` to `ι B (g m)`. -/
noncomputable def mapSemilinear (g : M →ₛₗ[σ] N) :
    ExteriorAlgebra A M →+* ExteriorAlgebra B N :=
  letI := algebraOfRingHom σ N
  (lift A ⟨{ toFun := fun m ↦ ι B (g m), map_add' := fun _ _ ↦ by simp,
             map_smul' := fun a m ↦ by simp [Algebra.smul_def]; rfl },
    fun m ↦ ι_sq_zero (g m)⟩).toRingHom

@[simp] theorem mapSemilinear_algebraMap (g : M →ₛₗ[σ] N) (a : A) :
    mapSemilinear g (algebraMap A (ExteriorAlgebra A M) a) =
      algebraMap B (ExteriorAlgebra B N) (σ a) :=
  letI := algebraOfRingHom σ N; (lift A ⟨_, fun m ↦ ι_sq_zero (g m)⟩).commutes a
@[simp] theorem mapSemilinear_ι (g : M →ₛₗ[σ] N) (m : M) : mapSemilinear g (ι A m) = ι B (g m) :=
  letI := algebraOfRingHom σ N; lift_ι_apply A _ (fun m ↦ ι_sq_zero (g m)) m
@[simp] theorem mapSemilinear_smul (g : M →ₛₗ[σ] N) (a : A) (x : ExteriorAlgebra A M) :
    mapSemilinear g (a • x) = σ a • mapSemilinear g x := by
  rw [Algebra.smul_def, map_mul, mapSemilinear_algebraMap, Algebra.smul_def]
@[simp] theorem mapSemilinear_ιMulti (g : M →ₛₗ[σ] N) {n : ℕ} (v : Fin n → M) :
    mapSemilinear g (ιMulti A n v) = ιMulti B n (g ∘ v) := by
  induction n with
  | zero => simp [ιMulti_zero_apply]
  | succ n ih => simp [ιMulti_succ_apply, ih, Matrix.vecTail, Function.comp_def]

/-- For an `A`-linear map, `mapSemilinear` agrees with `ExteriorAlgebra.map`. -/
theorem mapSemilinear_eq_map {N' : Type*} [AddCommGroup N'] [Module A N'] (g : M →ₗ[A] N') :
    mapSemilinear g = (map g).toRingHom := ringHom_ext (fun _ ↦ by simp) (fun _ ↦ by simp)
@[simp] theorem mapSemilinear_id :
    mapSemilinear (LinearMap.id : M →ₗ[A] M) = RingHom.id (ExteriorAlgebra A M) :=
  ringHom_ext (fun _ ↦ by simp) (fun _ ↦ by simp)
theorem mapSemilinear_id_apply (x : ExteriorAlgebra A M) :
    mapSemilinear (LinearMap.id : M →ₗ[A] M) x = x := RingHom.congr_fun mapSemilinear_id x
theorem mapSemilinear_comp [RingHomCompTriple σ τ ρ] (h : N →ₛₗ[τ] P) (g : M →ₛₗ[σ] N) :
    mapSemilinear (h.comp g) = (mapSemilinear h).comp (mapSemilinear g) :=
  ringHom_ext (fun _ ↦ by simp [RingHomCompTriple.comp_apply]) (fun _ ↦ by simp)
@[simp] theorem mapSemilinear_comp_apply [RingHomCompTriple σ τ ρ] (h : N →ₛₗ[τ] P)
    (g : M →ₛₗ[σ] N) (x : ExteriorAlgebra A M) :
    mapSemilinear (h.comp g) x = mapSemilinear h (mapSemilinear g x) :=
  RingHom.congr_fun (mapSemilinear_comp h g) x

/-- `mapSemilinear` commutes with the grade involution on the exterior algebra. -/
@[simp] theorem mapSemilinear_involute (g : M →ₛₗ[σ] N) (x : ExteriorAlgebra A M) :
    mapSemilinear g (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm B N)) (mapSemilinear g x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap _ | ι _ => simp
  | mul _ _ hx hy | add _ _ hx hy => simp [hx, hy]

end ExteriorAlgebra
