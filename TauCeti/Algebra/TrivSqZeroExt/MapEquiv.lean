/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Linear equivalences induce algebra equivalences of trivial square-zero extensions

Let `R` be a commutative semiring and let `M`, `N` be symmetric `R`-bimodules: modules over `R`
and over `Rᵐᵒᵖ` whose two actions agree (`IsCentralScalar R M`), which is what makes `R ⊕ M` an
`R`-algebra. Mathlib's `TrivSqZeroExt.map` sends a linear map `f : M →ₗ[R] N` to the algebra
homomorphism `R ⊕ M →ₐ[R] R ⊕ N` that fixes `R` and applies `f` to the square-zero part. This file
packages the case of a linear equivalence: `LinearEquiv.trivSqZeroExtCongr e` is an algebra
equivalence with inverse `e.symm.trivSqZeroExtCongr`, and `e ↦ e.trivSqZeroExtCongr` is a group
homomorphism from the linear automorphisms of `M` to the algebra automorphisms of `R ⊕ M`.

For the dual numbers `R[ε] = R ⊕ R` this homomorphism sends the multiplication by a unit `u`
to the automorphism `ε ↦ u • ε`; when `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`
(for instance when `R` is reduced or `2` is invertible) these are all the automorphisms of `R[ε]`
(`TauCeti.DualNumber.linearEquivEquivAlgEquiv`).

## Main definitions

* `LinearEquiv.trivSqZeroExtCongr`: the algebra equivalence `R ⊕ M ≃ₐ[R] R ⊕ N` induced by a
  linear equivalence `M ≃ₗ[R] N` of symmetric bimodules.
* `TauCeti.TrivSqZeroExt.congrHom`: the group homomorphism
  `(M ≃ₗ[R] M) →* (R ⊕ M ≃ₐ[R] R ⊕ M)` for a symmetric bimodule `M`.
-/

public section

@[inherit_doc] local notation "tsze" => TrivSqZeroExt

open TrivSqZeroExt

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [AddCommMonoid N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
  [AddCommMonoid P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

namespace LinearEquiv

/-- The algebra equivalence `R ⊕ M ≃ₐ[R] R ⊕ N` induced by a linear equivalence `e : M ≃ₗ[R] N`
of symmetric `R`-bimodules (`[Module Rᵐᵒᵖ M] [IsCentralScalar R M]`, and likewise for `N`): it
fixes `R` and applies `e` to the square-zero part. As a map it is `TrivSqZeroExt.map e`
(`LinearEquiv.coe_trivSqZeroExtCongr`), and its inverse is `e.symm.trivSqZeroExtCongr`
(`LinearEquiv.trivSqZeroExtCongr_symm`). -/
def trivSqZeroExtCongr (e : M ≃ₗ[R] N) : tsze R M ≃ₐ[R] tsze R N :=
  AlgEquiv.ofAlgHom (map e.toLinearMap) (map e.symm.toLinearMap)
    (by rw [← map_comp_map, LinearEquiv.comp_symm, map_id])
    (by rw [← map_comp_map, LinearEquiv.symm_comp, map_id])

@[simp]
theorem toAlgHom_trivSqZeroExtCongr (e : M ≃ₗ[R] N) :
    (e.trivSqZeroExtCongr : tsze R M →ₐ[R] tsze R N) = map e.toLinearMap := by
  rw [trivSqZeroExtCongr, AlgEquiv.toAlgHom_ofAlgHom]

@[simp]
theorem coe_trivSqZeroExtCongr (e : M ≃ₗ[R] N) : ⇑e.trivSqZeroExtCongr = map e.toLinearMap := by
  rw [← AlgEquiv.coe_toAlgHom, toAlgHom_trivSqZeroExtCongr]

@[simp]
theorem trivSqZeroExtCongr_symm (e : M ≃ₗ[R] N) :
    e.trivSqZeroExtCongr.symm = e.symm.trivSqZeroExtCongr := by
  rw [trivSqZeroExtCongr, trivSqZeroExtCongr, AlgEquiv.ofAlgHom_symm]
  simp_rw [LinearEquiv.symm_symm]

@[simp]
theorem trivSqZeroExtCongr_refl : (LinearEquiv.refl R M).trivSqZeroExtCongr = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective <| by
    rw [toAlgHom_trivSqZeroExtCongr, LinearEquiv.refl_toLinearMap, map_id, AlgEquiv.refl_toAlgHom]

@[simp]
theorem trivSqZeroExtCongr_trans (e : M ≃ₗ[R] N) (e' : N ≃ₗ[R] P) :
    (e.trans e').trivSqZeroExtCongr = e.trivSqZeroExtCongr.trans e'.trivSqZeroExtCongr :=
  AlgEquiv.ext fun x ↦ TrivSqZeroExt.ext (by simp) (by simp)

theorem trivSqZeroExtCongr_injective :
    Function.Injective (trivSqZeroExtCongr : (M ≃ₗ[R] N) → _) := fun e e' h ↦
  LinearEquiv.ext fun m ↦ inr_injective (R := R) <| by
    simpa using congrArg (fun g ↦ g (inr m)) h

end LinearEquiv

namespace TauCeti.TrivSqZeroExt

variable (R M) in
/-- The group homomorphism from the linear automorphisms of a symmetric `R`-bimodule `M` to the
algebra automorphisms of `R ⊕ M`, sending `e` to `LinearEquiv.trivSqZeroExtCongr e`. It is
injective (`LinearEquiv.trivSqZeroExtCongr_injective`). -/
def congrHom : (M ≃ₗ[R] M) →* (tsze R M ≃ₐ[R] tsze R M) where
  toFun := LinearEquiv.trivSqZeroExtCongr
  map_one' := LinearEquiv.trivSqZeroExtCongr_refl
  map_mul' e e' := LinearEquiv.trivSqZeroExtCongr_trans e' e

@[simp]
theorem coe_congrHom : ⇑(congrHom R M) = LinearEquiv.trivSqZeroExtCongr := (rfl)

end TauCeti.TrivSqZeroExt
