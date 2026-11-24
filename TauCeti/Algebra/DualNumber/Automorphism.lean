/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.Algebra.DualNumber.Map
public import TauCeti.Algebra.TrivSqZeroExt.MapEquiv

/-!
# Automorphisms of the dual numbers

Let `R` be a commutative semiring. An `R`-algebra endomorphism `f` of the dual numbers `R[ε]`
sends `ε` to an element `a + b • ε` squaring to zero, that is, with `a ^ 2 = 0` and `2 * a * b = 0`.
For an automorphism `φ` the coefficient `b` is a unit over every `R`, because applying `φ` to
`φ.symm ε` supplies an inverse coefficient; so `a ^ 2 = 0` and `2 * a = 0`. Since an algebra map
out of `R[ε]` is determined by its value on `ε`, the automorphism `φ` is `ε ↦ u • ε` for a unit `u`,
that is, `e.trivSqZeroExtCongr` for a linear automorphism `e` of `R`, exactly when `a = 0`
(`AlgEquiv.exists_trivSqZeroExtCongr_eq_iff`). When `R` has no nonzero `a` with `a ^ 2 = 0` and
`2 * a = 0` — for instance when `R` is reduced, or when `2` is invertible in `R` — this always
holds, and `TauCeti.DualNumber.linearEquivEquivAlgEquiv` is a group isomorphism
`(R ≃ₗ[R] R) ≃* (R[ε] ≃ₐ[R] R[ε])`.

The hypothesis is also necessary: if `a ≠ 0` satisfies `a ^ 2 = 0` and `2 * a = 0`, then
`ε ↦ a + ε` defines an automorphism of `R[ε]` (with inverse `ε ↦ -a + ε` when `R` is a ring, since
`(a + ε) ^ 2 = a ^ 2 + 2 * a • ε = 0`) that does not preserve the line `R • ε`. For instance,
`a = δ` over `R = 𝔽₂[δ]/(δ²)`.

## Main results

* `AlgEquiv.isUnit_snd_apply_eps`: for an automorphism, the coefficient of `ε` in the
  image of `ε` is a unit.
* `AlgEquiv.exists_trivSqZeroExtCongr_eq_iff`: an automorphism is `ε ↦ u • ε` for a unit `u`
  exactly when the image of `ε` has zero `R`-component.
* `TauCeti.DualNumber.linearEquivEquivAlgEquiv`: the automorphism group of `R[ε]` is the group of
  linear automorphisms of `R`, acting on the coefficient of `ε`.
-/

public section

open DualNumber TrivSqZeroExt

variable {R : Type*} [CommSemiring R]

namespace AlgEquiv

/-- An automorphism of the dual numbers multiplies `ε`, up to an `R`-component, by a unit. -/
theorem isUnit_snd_apply_eps (φ : R[ε] ≃ₐ[R] R[ε]) : IsUnit (φ ε).snd :=
  -- Applying `φ` to `φ.symm ε` gives back `ε`, whose `ε`-coefficient is `1`.
  IsUnit.of_mul_eq_one (φ.symm ε).snd <| (mul_comm _ _).trans <|
    (DualNumber.snd_apply_eq_snd_mul_snd_apply_eps φ (φ.symm ε)).symm.trans <| by
      rw [φ.apply_symm_apply, snd_eps]

/-- An automorphism `φ` of the dual numbers is `e.trivSqZeroExtCongr` for a linear automorphism `e`
of `R`, that is, `ε ↦ u • ε` for a unit `u`, exactly when `φ ε` has zero `R`-component. -/
theorem exists_trivSqZeroExtCongr_eq_iff (φ : R[ε] ≃ₐ[R] R[ε]) :
    (∃ e : R ≃ₗ[R] R, e.trivSqZeroExtCongr = φ) ↔ (φ ε).fst = 0 := by
  refine ⟨fun ⟨e, he⟩ ↦ he ▸ by simp, fun h ↦ ?_⟩
  -- The multiplication by the unit `(φ ε).snd` sends `ε` to `(φ ε).snd • ε = φ ε`.
  obtain ⟨u, hu⟩ := φ.isUnit_snd_apply_eps
  refine ⟨DistribMulAction.toLinearEquiv R R u,
    coe_toAlgHom_injective <| DualNumber.algHom_ext <| TrivSqZeroExt.ext ?_ ?_⟩
  · simp [h, Units.smul_def]
  · simp [← hu, Units.smul_def]

end AlgEquiv

namespace TauCeti.DualNumber

/-- If `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or
`2` is invertible in `R`, then an automorphism of the dual numbers sends `ε` to an element with
zero `R`-component. -/
theorem fst_algEquiv_apply_eps_eq_zero (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0)
    (φ : R[ε] ≃ₐ[R] R[ε]) : (φ ε).fst = 0 := by
  -- Write `φ ε = a + b • ε`; then `(φ ε) ^ 2 = 0` gives `a ^ 2 = 0` and `2 * a * b = 0`.
  have h : φ ε * φ ε = 0 := by rw [← map_mul, eps_mul_eps, map_zero]
  refine hR _ ?_ (φ.isUnit_snd_apply_eps.mul_left_eq_zero.mp ?_)
  · rw [pow_two, ← fst_mul, h, fst_zero]
  · calc 2 * (φ ε).fst * (φ ε).snd = (φ ε).fst * (φ ε).snd + (φ ε).snd * (φ ε).fst := by ring
      _ = 0 := by simpa [DualNumber.snd_mul] using congrArg snd h

/-- **The automorphisms of the dual numbers.** If `R` has no nonzero `a` with `a ^ 2 = 0` and
`2 * a = 0`, for instance if `R` is reduced or `2` is invertible in `R`, then every `R`-algebra
automorphism `φ` of `R[ε]` is `e.trivSqZeroExtCongr` for a unique linear automorphism `e` of `R`,
namely the multiplication by the unit `(φ ε).snd`; composition corresponds to composition. -/
noncomputable def linearEquivEquivAlgEquiv (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0) :
    (R ≃ₗ[R] R) ≃* (R[ε] ≃ₐ[R] R[ε]) :=
  MulEquiv.ofBijective (TrivSqZeroExt.congrHom R R) <| by
    rw [TrivSqZeroExt.coe_congrHom]
    exact ⟨LinearEquiv.trivSqZeroExtCongr_injective, fun φ ↦
      φ.exists_trivSqZeroExtCongr_eq_iff.mpr (fst_algEquiv_apply_eps_eq_zero hR φ)⟩

@[simp]
theorem linearEquivEquivAlgEquiv_apply (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0)
    (e : R ≃ₗ[R] R) : linearEquivEquivAlgEquiv hR e = e.trivSqZeroExtCongr := by
  rw [linearEquivEquivAlgEquiv, MulEquiv.ofBijective_apply, TrivSqZeroExt.coe_congrHom]

/-- The linear automorphism of `R` attached to an automorphism `φ` of `R[ε]` is the multiplication
by the `ε`-coefficient of `φ ε`. -/
@[simp]
theorem linearEquivEquivAlgEquiv_symm_apply_apply (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0)
    (φ : R[ε] ≃ₐ[R] R[ε]) (r : R) : (linearEquivEquivAlgEquiv hR).symm φ r = r * (φ ε).snd := by
  obtain ⟨e, rfl⟩ := (linearEquivEquivAlgEquiv hR).surjective φ
  -- A linear endomorphism of `R` is the multiplication by its value at `1`.
  rw [MulEquiv.symm_apply_apply]
  simpa using e.map_smul r 1

end TauCeti.DualNumber
