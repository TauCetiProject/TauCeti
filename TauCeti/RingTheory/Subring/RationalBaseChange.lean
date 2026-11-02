/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.Localization.TensorProduct

/-!
# Extending the scalars of a subring of a rational algebra

Let `A` be a `ℚ`-algebra and `R` a subring of `A`. Because `R` is a ring and not a `ℚ`-subalgebra,
it can be a genuine lattice: an integral structure whose rational span is all of `A`. This file
builds the comparison map

```text
ratBaseChange R : ℚ ⊗[ℤ] R →ₐ[ℚ] A,     q ⊗ₜ r ↦ q • r
```

records that its range is exactly the `ℚ`-span of `R`, and proves that it is always injective.
Consequently it is an isomorphism exactly when that span is everything, which is what it means for
`R` to be a `ℤ`-form of `A`.

Injectivity holds with no hypothesis on `R` and is the reason the file exists: every element of
`ℚ ⊗[ℤ] M`, for any additive group `M`, has a common denominator, so it is a single elementary
tensor `(n : ℚ)⁻¹ ⊗ₜ m` rather than a sum of them. That normal form,
`TensorProduct.exists_eq_inv_natCast_tmul`, is purely module-theoretic and lives in
`TauCeti.RingTheory.Localization.TensorProduct`. It also turns the spanning hypothesis into the
concrete statement `Subring.exists_natCast_smul_mem`, that every element of `A` is carried into `R`
by some nonzero natural number.

## Main definitions

* `Subring.ratBaseChange`: the canonical `ℚ`-algebra map `ℚ ⊗[ℤ] R → A`.
* `Subring.ratBaseChangeEquiv`: that map as an isomorphism, given a spanning subring.

## Main results

* `Subring.ratBaseChange_injective`: the comparison map is injective.
* `Subring.range_ratBaseChange`: its range is the `ℚ`-span of `R`.
* `Subring.span_eq_top_iff_exists_natCast_smul_mem`: a subring spans exactly when denominators can
  be cleared.
-/

public section

open scoped TensorProduct

namespace Subring

/-! ## The comparison map -/

section BaseChange

variable {A : Type*} [Ring A] [Algebra ℚ A] (R : Subring A)

/-- The canonical `ℚ`-algebra map `ℚ ⊗[ℤ] R → A` extending the inclusion of a subring of a
`ℚ`-algebra. It sends `q ⊗ₜ r` to `q • r`. -/
noncomputable def ratBaseChange : ℚ ⊗[ℤ] R →ₐ[ℚ] A :=
  AlgHom.liftEquiv ℤ ℚ R A R.subtype.toIntAlgHom

@[simp]
theorem ratBaseChange_tmul (q : ℚ) (r : R) : ratBaseChange R (q ⊗ₜ[ℤ] r) = q • (r : A) := by
  simp [ratBaseChange]

/-- The comparison map is injective for every subring. -/
theorem ratBaseChange_injective : Function.Injective (ratBaseChange R) := by
  -- Write the input as `(n : ℚ)⁻¹ ⊗ₜ r`; its image `(n : ℚ)⁻¹ • r` vanishes only if `r = 0`.
  refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
  obtain ⟨n, r, hn, rfl⟩ := TensorProduct.exists_eq_inv_natCast_tmul z
  simp_all

/-- The range of the comparison map is the `ℚ`-span of the subring. -/
theorem range_ratBaseChange :
    LinearMap.range (ratBaseChange R).toLinearMap = Submodule.span ℚ (R : Set A) := by
  -- The comparison map is the base change of the inclusion of `R`, whose range is `R` itself.
  have hlift : (ratBaseChange R).toLinearMap =
      LinearMap.liftBaseChange ℚ R.subtype.toIntAlgHom.toLinearMap := by
    ext
    simp
  rw [hlift, LinearMap.range_liftBaseChange]
  congr 1
  ext
  simp

/-- The comparison map is surjective exactly when the subring spans the ambient algebra over `ℚ`. -/
theorem ratBaseChange_surjective_iff :
    Function.Surjective (ratBaseChange R) ↔ Submodule.span ℚ (R : Set A) = ⊤ := by
  rw [← range_ratBaseChange, LinearMap.range_eq_top, AlgHom.coe_toLinearMap]

/-- The comparison map is bijective for a spanning subring. -/
theorem ratBaseChange_bijective (h : Submodule.span ℚ (R : Set A) = ⊤) :
    Function.Bijective (ratBaseChange R) :=
  ⟨ratBaseChange_injective R, (ratBaseChange_surjective_iff R).2 h⟩

/-- A spanning subring is a `ℤ`-form of the ambient `ℚ`-algebra: extending its scalars to `ℚ`
recovers that algebra. -/
noncomputable def ratBaseChangeEquiv (h : Submodule.span ℚ (R : Set A) = ⊤) :
    ℚ ⊗[ℤ] R ≃ₐ[ℚ] A :=
  AlgEquiv.ofBijective (ratBaseChange R) (ratBaseChange_bijective R h)

@[simp]
theorem ratBaseChangeEquiv_tmul (h : Submodule.span ℚ (R : Set A) = ⊤) (q : ℚ) (r : R) :
    ratBaseChangeEquiv R h (q ⊗ₜ[ℤ] r) = q • (r : A) := by
  simp [ratBaseChangeEquiv]

/-- Denominators can be cleared in a spanning subring: every element of the ambient algebra is
carried into it by some nonzero natural number. -/
theorem exists_natCast_smul_mem (h : Submodule.span ℚ (R : Set A) = ⊤) (a : A) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • a ∈ R := by
  obtain ⟨z, rfl⟩ := (ratBaseChange_surjective_iff R).2 h a
  obtain ⟨n, r, hn, rfl⟩ := TensorProduct.exists_eq_inv_natCast_tmul z
  exact ⟨n, hn, by simp [hn]⟩

/-- A subring spans its ambient `ℚ`-algebra exactly when denominators can be cleared: every
element is carried into the subring by some nonzero natural number. This is the form of the
spanning hypothesis that a consumer checks in practice. -/
theorem span_eq_top_iff_exists_natCast_smul_mem :
    Submodule.span ℚ (R : Set A) = ⊤ ↔ ∀ a : A, ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • a ∈ R := by
  refine ⟨exists_natCast_smul_mem R, fun h ↦ Submodule.eq_top_iff'.2 fun a ↦ ?_⟩
  obtain ⟨n, hn, hmem⟩ := h a
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hn)).1 (Submodule.subset_span hmem)

end BaseChange

end Subring
