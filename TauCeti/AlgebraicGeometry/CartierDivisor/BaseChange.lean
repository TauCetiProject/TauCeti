/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial

/-!
# `K`-Cartier divisors and `ℚ`-Cartier Weil divisors

Let `X` be an integral scheme and `Div(X)` its group of Cartier divisors. For a commutative ring
`K`, write `Div(X)_K = K ⊗[ℤ] Div(X)`; the cases of interest are `Div(X)_ℚ` and `Div(X)_ℝ`, the
`ℚ`-Cartier and `ℝ`-Cartier divisors. Two `K`-Cartier divisors are *`K`-linearly equivalent* when
their difference is a `K`-combination of principal divisors.

When `X` is moreover Noetherian and normal, the Cartier-to-Weil map is injective
(`Scheme.CartierDivisor.toWeilDivisorHom_injective`), and so is its extension
`Div(X)_ℚ ⟶ ℚ ⊗[ℤ] Weil(X)`, since `ℚ` is flat over `ℤ`. A Weil divisor `D` with rational
coefficients is *`ℚ`-Cartier* when `r D` is the Weil divisor of a Cartier divisor `A` for some
integer `r ≥ 1`; these form the range of that extension, a `ℚ`-subspace isomorphic to `Div(X)_ℚ`.

## Main declarations

* `Scheme.CartierDivisor.principalSubmodule K X`: the `K`-combinations of principal divisors;
* `Scheme.CartierDivisor.baseChangeToWeilDivisor K X`: the Cartier-to-Weil map after extending
  scalars to `K`, injective for flat `K`
  (`Scheme.CartierDivisor.baseChangeToWeilDivisor_injective`);
* `Scheme.CartierDivisor.qCartierSubmodule X`: the `ℚ`-Cartier Weil divisors, characterized by
  `Scheme.CartierDivisor.mem_qCartierSubmodule_iff`;
* `Scheme.CartierDivisor.qCartierEquiv X`: the isomorphism `Div(X)_ℚ ≃ₗ[ℚ] qCartierSubmodule X`,
  which carries `ℚ`-combinations of principal Weil divisors back into `principalSubmodule ℚ X`
  (`Scheme.CartierDivisor.qCartierEquiv_symm_mem_principalSubmodule`).

## References

* R. Lazarsfeld, *Positivity in Algebraic Geometry I*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 48, Springer, 2004, §1.1.C and §1.3.B: `ℚ`-Cartier and `ℝ`-Cartier divisors and
  `ℝ`-linear equivalence.
* [The Stacks Project, Lemma 10.157.6](https://stacks.math.columbia.edu/tag/031T): a Noetherian
  normal domain is the intersection of its localizations at height-one primes, the input to the
  injectivity of the Cartier-to-Weil map.
-/

public section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

noncomputable section

variable (K : Type*) [CommRing K] {X : Scheme.{u}} [IsIntegral X]

variable (X) in
/-- The `K`-submodule of `Div(X)_K` spanned by the principal Cartier divisors. Two `K`-Cartier
divisors are **`K`-linearly equivalent** when their difference lies in it. -/
def principalSubmodule : Submodule K (K ⊗[ℤ] CartierDivisor X) :=
  (principalSubgroup X).toIntSubmodule.baseChange K

/-- `a ⊗ D` is a `K`-combination of principal divisors when `D` is principal. -/
theorem tmul_mem_principalSubmodule (a : K) {D : CartierDivisor X}
    (hD : D ∈ principalSubgroup X) : a ⊗ₜ D ∈ principalSubmodule K X :=
  Submodule.tmul_mem_baseChange_of_mem (p := (principalSubgroup X).toIntSubmodule) a hD

/-- A `K`-submodule of `Div(X)_K` contains every `K`-combination of principal divisors exactly
when it contains `1 ⊗ D` for every principal Cartier divisor `D`. -/
theorem principalSubmodule_le_iff {p : Submodule K (K ⊗[ℤ] CartierDivisor X)} :
    principalSubmodule K X ≤ p ↔ ∀ D ∈ principalSubgroup X, (1 : K) ⊗ₜ D ∈ p :=
  Submodule.baseChange_le_iff_le_comap

section Weil

variable [IsNoetherian X]

variable (X) in
/-- The Cartier-to-Weil map `Div(X) ⟶ Weil(X)` after extending scalars to `K`. -/
def baseChangeToWeilDivisor : K ⊗[ℤ] CartierDivisor X →ₗ[K] K ⊗[ℤ] SchemeWeilDivisor X :=
  (toWeilDivisorHom (X := X)).toIntLinearMap.baseChange K

/-- The extended Cartier-to-Weil map sends `a ⊗ D` to `a ⊗ D_Weil`. -/
@[simp]
lemma baseChangeToWeilDivisor_tmul (a : K) (D : CartierDivisor X) :
    baseChangeToWeilDivisor K X (a ⊗ₜ D) = a ⊗ₜ D.toWeilDivisor := by
  rw [baseChangeToWeilDivisor, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    toWeilDivisorHom_apply]

/-- If `r D` is the Weil divisor of a Cartier divisor `A` with `r ≠ 0`, then `D` is the image of
`r⁻¹ ⊗ A` under the extended Cartier-to-Weil map. -/
theorem baseChangeToWeilDivisor_inv_tmul {K : Type*} [Field K] {D : K ⊗[ℤ] SchemeWeilDivisor X}
    {r : K} (hr : r ≠ 0) {A : CartierDivisor X} (h : r • D = 1 ⊗ₜ A.toWeilDivisor) :
    baseChangeToWeilDivisor K X (r⁻¹ ⊗ₜ A) = D := by
  rw [baseChangeToWeilDivisor_tmul, ← mul_one r⁻¹, ← smul_eq_mul, ← smul_tmul', ← h,
    inv_smul_smul₀ hr]

variable (X) in
/-- The `ℚ`-subspace of **`ℚ`-Cartier Weil divisors**: the Weil divisors with rational coefficients
some positive multiple of which is the Weil divisor of a Cartier divisor
(`Scheme.CartierDivisor.mem_qCartierSubmodule_iff`). -/
def qCartierSubmodule : Submodule ℚ (ℚ ⊗[ℤ] SchemeWeilDivisor X) :=
  LinearMap.range (baseChangeToWeilDivisor ℚ X)

/-- **`ℚ`-Cartier Weil divisors.** A Weil divisor `D` with rational coefficients is `ℚ`-Cartier
exactly when `r D` is the Weil divisor of a Cartier divisor `A` for some integer `r ≥ 1`. -/
theorem mem_qCartierSubmodule_iff {D : ℚ ⊗[ℤ] SchemeWeilDivisor X} :
    D ∈ qCartierSubmodule X ↔
      ∃ r : ℕ, 0 < r ∧ ∃ A : CartierDivisor X, (r : ℚ) • D = 1 ⊗ₜ A.toWeilDivisor := by
  rw [qCartierSubmodule, LinearMap.mem_range]
  refine ⟨?_, fun ⟨r, hr, A, h⟩ ↦
    ⟨_, baseChangeToWeilDivisor_inv_tmul (Nat.cast_ne_zero.mpr hr.ne') h⟩⟩
  -- `ℚ ⊗[ℤ] Div(X)` is the localization of `Div(X)` at the nonzero integers.
  rintro ⟨E, rfl⟩
  obtain ⟨⟨A, s, hs⟩, h⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (CartierDivisor X) 1) E
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have h' : (s : ℚ) • baseChangeToWeilDivisor ℚ X E = 1 ⊗ₜ A.toWeilDivisor := by
    rw [← map_smul, Int.cast_smul_eq_zsmul, ← baseChangeToWeilDivisor_tmul]
    simpa only [Submonoid.smul_def, mk_apply] using congrArg (baseChangeToWeilDivisor ℚ X) h
  obtain ⟨n, rfl | rfl⟩ := s.eq_nat_or_neg
  · exact ⟨n, by omega, A, by simpa only [Int.cast_natCast] using h'⟩
  · refine ⟨n, by omega, -A, ?_⟩
    rw [Int.cast_neg, neg_smul, neg_eq_iff_eq_neg, Int.cast_natCast] at h'
    simp [h', ← toWeilDivisorHom_apply, tmul_neg]

variable (X) in
/-- Every `K`-combination of principal Weil divisors is the image of a `K`-combination of principal
Cartier divisors under the extended Cartier-to-Weil map. -/
theorem baseChange_principalSubgroup_le_map_principalSubmodule :
    (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup.toIntSubmodule.baseChange K ≤
      (principalSubmodule K X).map (baseChangeToWeilDivisor K X) := by
  refine Submodule.baseChange_le_iff_le_comap.mpr fun w hw ↦ ?_
  obtain ⟨g, rfl⟩ := (WeilDivisor.OrderSystem.mem_principalSubgroup _).mp hw
  refine ⟨1 ⊗ₜ principalCartierDivisor X g.toMul,
    tmul_mem_principalSubmodule K 1 (mem_principalSubgroup.mpr ⟨_, rfl⟩), ?_⟩
  rw [baseChangeToWeilDivisor_tmul, toWeilDivisor_principalCartierDivisor, mk_apply]

variable [IsNormalScheme X]

/-- On a Noetherian normal integral scheme, the Cartier-to-Weil map stays injective after
extending scalars to a flat `ℤ`-algebra `K`, such as `ℚ` or `ℝ`. -/
theorem baseChangeToWeilDivisor_injective [Module.Flat ℤ K] :
    Function.Injective (baseChangeToWeilDivisor K X) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ toWeilDivisorHom_injective

variable (X) in
/-- On a Noetherian normal integral scheme, `Div(X)_ℚ` is isomorphic to the `ℚ`-Cartier Weil
divisors through the Cartier-to-Weil map. -/
def qCartierEquiv : (ℚ ⊗[ℤ] CartierDivisor X) ≃ₗ[ℚ] qCartierSubmodule X :=
  LinearEquiv.ofInjective _ (baseChangeToWeilDivisor_injective ℚ)

/-- The isomorphism `Div(X)_ℚ ≃ₗ[ℚ] qCartierSubmodule X` is the extended Cartier-to-Weil map. -/
@[simp]
lemma coe_qCartierEquiv_apply (E : ℚ ⊗[ℤ] CartierDivisor X) :
    (qCartierEquiv X E : ℚ ⊗[ℤ] SchemeWeilDivisor X) = baseChangeToWeilDivisor ℚ X E :=
  LinearEquiv.ofInjective_apply _ E

/-- A `ℚ`-Cartier Weil divisor that is a `ℚ`-combination of principal Weil divisors comes from a
`ℚ`-combination of principal Cartier divisors. -/
theorem qCartierEquiv_symm_mem_principalSubmodule {D : qCartierSubmodule X}
    (h : (D : ℚ ⊗[ℤ] SchemeWeilDivisor X) ∈
      (WeilDivisor.OrderSystem.ofScheme X).principalSubgroup.toIntSubmodule.baseChange ℚ) :
    (qCartierEquiv X).symm D ∈ principalSubmodule ℚ X := by
  obtain ⟨E, hE, hED⟩ := baseChange_principalSubgroup_le_map_principalSubmodule ℚ X h
  rwa [(qCartierEquiv X).symm_apply_eq.mpr
    (Subtype.ext ((coe_qCartierEquiv_apply E).trans hED)).symm]

end Weil

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
