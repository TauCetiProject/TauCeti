/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Localization
import Mathlib.RingTheory.Flat.Localization

/-!
# Submonoid torsion under base change

Let `R` be a commutative ring, `S` a submonoid of `R`, and `A` a localization of `R` at `S`.
Base change `A ⊗[R] -` is exact and kills a module exactly when it is `S`-torsion
(`Submonoid.isTorsion'_iff_subsingleton_tensorProduct`). Applied to the kernel and cokernel exact
sequences of an `R`-linear map `f : M →ₗ[R] N`, this characterizes when `f.baseChange A` is
injective, surjective, or bijective:

* `LinearMap.injective_baseChange_iff_isTorsion'_ker`: `f.baseChange A` is injective if and only
  if `LinearMap.ker f` is `S`-torsion.
* `LinearMap.surjective_baseChange_iff_isTorsion'_quotient`: `f.baseChange A` is surjective if and
  only if `N ⧸ LinearMap.range f` is `S`-torsion.
* `LinearMap.bijective_baseChange_iff`: `f.baseChange A` is bijective if and only if both the
  kernel and cokernel of `f` are `S`-torsion.
-/

public section

open scoped TensorProduct

namespace LinearMap

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Base change of `f : M →ₗ[R] N` to a localization `A` of `R` at `S` is injective if and only
if `LinearMap.ker f` is `S`-torsion. -/
theorem injective_baseChange_iff_isTorsion'_ker (f : M →ₗ[R] N) (S : Submonoid R) (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Function.Injective (f.baseChange A) ↔ Module.IsTorsion' (LinearMap.ker f) S := by
  have : Module.Flat R A := IsLocalization.flat A S
  have hex : Function.Exact ((LinearMap.ker f).subtype.lTensor A) (f.lTensor A) :=
    Module.Flat.lTensor_exact A f.exact_subtype_ker_map
  have hinj : Function.Injective ((LinearMap.ker f).subtype.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [S.isTorsion'_iff_subsingleton_tensorProduct A, LinearMap.baseChange_eq_lTensor,
    ← LinearMap.ker_eq_bot, hex.linearMap_ker_eq, LinearMap.range_eq_bot]
  refine ⟨fun h ↦ subsingleton_of_forall_eq 0 fun x ↦ hinj ?_,
    fun _ ↦ LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  rw [map_zero]
  exact LinearMap.congr_fun h x

/-- Base change of `f : M →ₗ[R] N` to a localization `A` of `R` at `S` is surjective if and only
if the cokernel `N ⧸ LinearMap.range f` is `S`-torsion. -/
theorem surjective_baseChange_iff_isTorsion'_quotient (f : M →ₗ[R] N) (S : Submonoid R)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A] :
    Function.Surjective (f.baseChange A) ↔ Module.IsTorsion' (N ⧸ LinearMap.range f) S := by
  have hex : Function.Exact (f.lTensor A) ((LinearMap.range f).mkQ.lTensor A) :=
    lTensor_exact A f.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((LinearMap.range f).mkQ.lTensor A) :=
    LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  rw [S.isTorsion'_iff_subsingleton_tensorProduct A, LinearMap.baseChange_eq_lTensor,
    ← LinearMap.range_eq_top, ← hex.linearMap_ker_eq, LinearMap.ker_eq_top]
  refine ⟨fun h ↦ subsingleton_of_forall_eq 0 fun y ↦ ?_,
    fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩
  obtain ⟨x, rfl⟩ := hsurj y
  exact LinearMap.congr_fun h x

/-- Base change of `f : M →ₗ[R] N` to a localization `A` of `R` at `S` is bijective if and only
if both its kernel and its cokernel are `S`-torsion. -/
theorem bijective_baseChange_iff (f : M →ₗ[R] N) (S : Submonoid R) (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    Function.Bijective (f.baseChange A) ↔
      Module.IsTorsion' (LinearMap.ker f) S ∧ Module.IsTorsion' (N ⧸ LinearMap.range f) S :=
  and_congr (f.injective_baseChange_iff_isTorsion'_ker S A)
    (f.surjective_baseChange_iff_isTorsion'_quotient S A)

end LinearMap
