/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Separation
public import TauCeti.NumberTheory.ModularForms.Fricke.CharacterSpace

/-!
# The normalized Fricke operator `𝒲_N`

The raw Fricke slash `f ↦ f ∣[k] W`, `W = !![0, -1; N, 0]`, is not an involution: it squares to
the scalar `frickeScalar N k = (-1) ^ k * N ^ (k - 2)`
(`TauCeti.frickeOperator_frickeOperator`). Dividing it by `(√N) ^ (k - 2)` removes the `N`-power
and leaves only the sign. This file introduces that arithmetic normalization,

`𝒲_N f = (√N) ^ (2 - k) • (f ∣[k] W)`,

proves `𝒲_N ∘ 𝒲_N = (-1) ^ k • id`, and reads off the two consequences the theory rests on: in
**even** weight `𝒲_N` is an involution, and its `±1` eigenspaces are complementary in
`M_k(Γ₁(N))` and in `S_k(Γ₁(N))`.

## Why the normalization is fixed once

Every later Atkin–Lehner statement — `𝒲_Q 𝒲_R = 𝒲_{QR / gcd(Q, R) ²}` for exact divisors, the
signs `𝒲_Q f = ε_Q f` on a newform, and the sign `i ^ k · ε_N` of the functional equation of
`L(s, f)` — is a statement about the *normalized* operator; with the raw slash they all acquire
a stray power of `N`. So the constant is named here, and the operator built from it is what the
rest of the theory quantifies over.

## The two Fricke constants

Two scalars attached to `W` now have names, and they are not the same one:

* `TauCeti.frickeScalar N k = (-1) ^ k * N ^ (k - 2)` is what the **raw** operator squares to;
* `TauCeti.frickeNormalizer N k = (√N) ^ (2 - k)` is the factor the raw operator is **multiplied
  by**.

They are related by `TauCeti.frickeNormalizer_sq_mul_frickeScalar`: the square of the normalizer
cancels the `N`-power of the scalar, leaving `(-1) ^ k`. That single identity is the whole
arithmetic content of the file; everything else is bookkeeping around it.

## Main definitions

* `TauCeti.frickeNormalizer`: the constant `(√N) ^ (2 - k)`.
* `TauCeti.normalizedFrickeOperator`, `TauCeti.normalizedFrickeOperatorCusp`: `𝒲_N` on
  `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.
* `TauCeti.normalizedFrickeOperatorEquiv`, `TauCeti.normalizedFrickeOperatorCuspEquiv`: `𝒲_N`
  bundled as a linear automorphism, with inverse `(-1) ^ k • 𝒲_N`.
* `TauCeti.normalizedFrickeCharRestrict`, `TauCeti.normalizedFrickeCharCuspRestrict`: `𝒲_N`
  restricted from the `χ`- to the `χ⁻¹`-nebentypus space.
* `TauCeti.normalizedFrickeCharEquiv`, `TauCeti.normalizedFrickeCharCuspEquiv`: those restrictions
  bundled as linear equivalences.

## Main results

* `TauCeti.normalizedFrickeOperator_normalizedFrickeOperator_apply` and its cusp-form
  counterpart: `𝒲_N (𝒲_N f) = (-1) ^ k • f`.
* `TauCeti.normalizedFrickeOperator_involutive`,
  `TauCeti.normalizedFrickeOperatorCusp_involutive`: **in even weight `𝒲_N` is an involution**.
* `TauCeti.isCompl_eigenspace_normalizedFrickeOperator`,
  `TauCeti.isCompl_eigenspace_normalizedFrickeOperatorCusp`: in even weight the `+1` and `-1`
  eigenspaces of `𝒲_N` are complementary — the splitting the sign of the functional equation is
  read off.
* `TauCeti.normalizedFrickeOperator_mem_modFormCharSpace` and its cusp-form counterpart: like the
  raw operator, `𝒲_N` carries the nebentypus `χ` to `χ⁻¹`.

## Why `Even k` is a hypothesis, and not a defect

`𝒲_N ∘ 𝒲_N = (-1) ^ k • id` is sharp: at odd `k` the normalized operator squares to `-1`.
A further factor of `i` would repair that, but it is not what the arithmetic normalization
means — `(√N) ^ (2 - k)` is the constant the functional equation and the Petersson pairing are
stated with, and a weight-dependent extra root of unity would desynchronise those statements
from this one. Nothing is lost where the sign theory is stated: for **trivial nebentypus** and
odd `k` the space is already zero, since `χ(-1) = 1 ≠ -1 = (-1) ^ k` and
`TauCeti.modFormCharSpace_eq_bot_of_char_neg_one_ne` applies. So the square law is kept at every
weight — it is what the bundled automorphism below needs — and only the involution and the
eigenspace splitting ask for `Even k`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.10.
* Miyake, *Modular forms*, Section 4.6.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970).
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### The normalizing constant -/

/-- The constant `(√N) ^ (2 - k)` the raw Fricke slash is multiplied by, so that the normalized
operator squares to `(-1) ^ k` rather than to `(-1) ^ k * N ^ (k - 2)`.

Read through `frickeNormalizer_sq` this is a square root of `N ^ (2 - k)`; the square root is
taken in `ℝ` and cast, rather than as a complex power, so that no branch of `(·) ^ (2 - k)` has
to be chosen. -/
public noncomputable def frickeNormalizer (N : ℕ) (k : ℤ) : ℂ :=
  ((Real.sqrt N : ℝ) : ℂ) ^ (2 - k)

/-- Defining equation for `frickeNormalizer`. The definition is `public` but is not marked
`@[expose]`, so a downstream module rewrites with this rather than unfolding the body. -/
public theorem frickeNormalizer_def (N : ℕ) (k : ℤ) :
    frickeNormalizer N k = ((Real.sqrt N : ℝ) : ℂ) ^ (2 - k) := (rfl)

/-- `√N` is nonzero in `ℂ`, the base of `frickeNormalizer`. Both facts the file needs about the
constant — that it is invertible, and that it squares to `N ^ (2 - k)` — rest on this. -/
private theorem ofReal_sqrt_natCast_ne_zero : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- `frickeNormalizer N k` is nonzero, which is what makes the normalized operator a bijection
and lets the normalization be undone. -/
public theorem frickeNormalizer_ne_zero (k : ℤ) : frickeNormalizer N k ≠ 0 :=
  zpow_ne_zero _ ofReal_sqrt_natCast_ne_zero

/-- **The normalizer squares to `N ^ (2 - k)`.** -/
public theorem frickeNormalizer_sq (k : ℤ) :
    frickeNormalizer N k ^ 2 = (N : ℂ) ^ (2 - k) := by
  have hs : (N : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ (2 : ℤ) := by
    rw [zpow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N),
      Complex.ofReal_natCast]
  rw [frickeNormalizer_def, hs, ← zpow_mul, pow_two, ← zpow_add₀ ofReal_sqrt_natCast_ne_zero,
    two_mul]

/-- **The normalization cancels the `N`-power of `frickeScalar`**, leaving the sign `(-1) ^ k`. -/
public theorem frickeNormalizer_sq_mul_frickeScalar (k : ℤ) :
    frickeNormalizer N k ^ 2 * frickeScalar N k = (-1) ^ k := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [frickeNormalizer_sq, frickeScalar_eq, ← mul_assoc, mul_comm ((N : ℂ) ^ (2 - k)) ((-1) ^ k),
    mul_assoc, ← zpow_add₀ hN]
  simp

/-! ### The operator -/

/-- **The normalized Fricke operator `𝒲_N` on `M_k(Γ₁(N))`**: the raw slash by `W` scaled by
`frickeNormalizer N k`. Unlike `frickeOperator` it squares to a sign, and in even weight it is an
involution. -/
public noncomputable def normalizedFrickeOperator (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  frickeNormalizer N k • frickeOperator k

/-- Defining equation for `normalizedFrickeOperator`, for clients that cannot unfold it. -/
public theorem normalizedFrickeOperator_def (k : ℤ) :
    normalizedFrickeOperator (N := N) k = frickeNormalizer N k • frickeOperator k := (rfl)

/-- On underlying functions the normalized Fricke operator is `(√N) ^ (2 - k) • (⇑f ∣[k] W)`. -/
@[simp]
public theorem coe_normalizedFrickeOperator (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(normalizedFrickeOperator (N := N) k f) : ℍ → ℂ) =
      frickeNormalizer N k • (⇑f ∣[k] frickeGL ℝ N) := by
  rw [normalizedFrickeOperator_def]
  ext z
  simp

/-- **The normalized Fricke operator on cusp forms** `S_k(Γ₁(N))`. -/
public noncomputable def normalizedFrickeOperatorCusp (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  frickeNormalizer N k • frickeOperatorCusp k

/-- Defining equation for `normalizedFrickeOperatorCusp`. -/
public theorem normalizedFrickeOperatorCusp_def (k : ℤ) :
    normalizedFrickeOperatorCusp (N := N) k = frickeNormalizer N k • frickeOperatorCusp k := (rfl)

/-- On underlying functions the normalized Fricke operator on cusp forms is
`(√N) ^ (2 - k) • (⇑f ∣[k] W)`. -/
@[simp]
public theorem coe_normalizedFrickeOperatorCusp (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(normalizedFrickeOperatorCusp (N := N) k f) : ℍ → ℂ) =
      frickeNormalizer N k • (⇑f ∣[k] frickeGL ℝ N) := by
  rw [normalizedFrickeOperatorCusp_def]
  ext z
  simp

/-- **The two normalized Fricke operators agree under the coercion** `S_k(Γ₁(N)) → M_k(Γ₁(N))`,
since the raw ones do and the scalar is the same. -/
@[simp]
public theorem normalizedFrickeOperator_coe_cuspForm (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (normalizedFrickeOperatorCusp k f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [normalizedFrickeOperator_def, normalizedFrickeOperatorCusp_def, LinearMap.smul_apply,
    LinearMap.smul_apply, frickeOperator_coe_cuspForm]
  ext z
  simp

/-! ### The square law -/

/-- **`𝒲_N ∘ 𝒲_N = (-1) ^ k • id` on `M_k(Γ₁(N))`.** -/
public theorem normalizedFrickeOperator_normalizedFrickeOperator (k : ℤ) :
    (normalizedFrickeOperator (N := N) k).comp (normalizedFrickeOperator (N := N) k) =
      ((-1 : ℂ) ^ k) • LinearMap.id := by
  rw [normalizedFrickeOperator_def, LinearMap.smul_comp, LinearMap.comp_smul,
    frickeOperator_frickeOperator, smul_smul, smul_smul, ← pow_two,
    frickeNormalizer_sq_mul_frickeScalar]

/-- **`𝒲_N (𝒲_N f) = (-1) ^ k • f`** for a modular form `f`, the pointwise form of
`normalizedFrickeOperator_normalizedFrickeOperator`. As for the raw operator this, not the
composition equality, is the `simp`-normal form. -/
@[simp]
public theorem normalizedFrickeOperator_normalizedFrickeOperator_apply (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperator k (normalizedFrickeOperator k f) = ((-1 : ℂ) ^ k) • f :=
  LinearMap.congr_fun (normalizedFrickeOperator_normalizedFrickeOperator (N := N) k) f

/-- **`𝒲_N ∘ 𝒲_N = (-1) ^ k • id` on `S_k(Γ₁(N))`.** -/
public theorem normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp (k : ℤ) :
    (normalizedFrickeOperatorCusp (N := N) k).comp (normalizedFrickeOperatorCusp (N := N) k) =
      ((-1 : ℂ) ^ k) • LinearMap.id := by
  rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_comp, LinearMap.comp_smul,
    frickeOperatorCusp_frickeOperatorCusp, smul_smul, smul_smul, ← pow_two,
    frickeNormalizer_sq_mul_frickeScalar]

/-- **`𝒲_N (𝒲_N f) = (-1) ^ k • f`** for a cusp form `f`. -/
@[simp]
public theorem normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp_apply (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperatorCusp k (normalizedFrickeOperatorCusp k f) = ((-1 : ℂ) ^ k) • f :=
  LinearMap.congr_fun (normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp (N := N) k) f

/-! ### Even weight: an involution -/

/-- **In even weight `𝒲_N` is an involution of `M_k(Γ₁(N))`** — the property the raw Fricke
slash lacks and the whole normalization exists to supply. -/
public theorem normalizedFrickeOperator_involutive {k : ℤ} (hk : Even k) :
    Function.Involutive (normalizedFrickeOperator (N := N) k) := fun f ↦ by
  rw [normalizedFrickeOperator_normalizedFrickeOperator_apply, hk.neg_one_zpow, one_smul]

/-- **In even weight `𝒲_N` is an involution of `S_k(Γ₁(N))`.** -/
public theorem normalizedFrickeOperatorCusp_involutive {k : ℤ} (hk : Even k) :
    Function.Involutive (normalizedFrickeOperatorCusp (N := N) k) := fun f ↦ by
  rw [normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp_apply, hk.neg_one_zpow, one_smul]

/-! ### The bundled automorphism -/

/-- **`𝒲_N` as a linear automorphism of `M_k(Γ₁(N))`**, with inverse `(-1) ^ k • 𝒲_N`. In even
weight the inverse is the operator itself. -/
public noncomputable def normalizedFrickeOperatorEquiv (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k ≃ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (frickeOperatorEquiv (N := N) k).trans <|
    LinearEquiv.smulOfUnit (Units.mk0 (frickeNormalizer N k) (frickeNormalizer_ne_zero k))

/-- The bundled normalized Fricke automorphism acts as `normalizedFrickeOperator`. -/
@[simp]
public theorem normalizedFrickeOperatorEquiv_apply (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperatorEquiv (N := N) k f = normalizedFrickeOperator k f := by
  simp only [normalizedFrickeOperatorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.smulOfUnit_apply, Units.val_mk0, frickeOperatorEquiv_apply,
    normalizedFrickeOperator_def, LinearMap.smul_apply]

/-- The inverse of the bundled normalized Fricke automorphism is `(-1) ^ k • 𝒲_N`. -/
@[simp]
public theorem normalizedFrickeOperatorEquiv_symm_apply (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (normalizedFrickeOperatorEquiv (N := N) k).symm f =
      ((-1 : ℂ) ^ k) • normalizedFrickeOperator k f := by
  apply (normalizedFrickeOperatorEquiv (N := N) k).injective
  rw [LinearEquiv.apply_symm_apply, normalizedFrickeOperatorEquiv_apply, map_smul,
    normalizedFrickeOperator_normalizedFrickeOperator_apply, smul_smul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

/-- **`𝒲_N` as a linear automorphism of `S_k(Γ₁(N))`**, with inverse `(-1) ^ k • 𝒲_N`. -/
public noncomputable def normalizedFrickeOperatorCuspEquiv (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k ≃ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (frickeOperatorCuspEquiv (N := N) k).trans <|
    LinearEquiv.smulOfUnit (Units.mk0 (frickeNormalizer N k) (frickeNormalizer_ne_zero k))

/-- The bundled normalized Fricke automorphism on cusp forms acts as
`normalizedFrickeOperatorCusp`. -/
@[simp]
public theorem normalizedFrickeOperatorCuspEquiv_apply (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    normalizedFrickeOperatorCuspEquiv (N := N) k f = normalizedFrickeOperatorCusp k f := by
  simp only [normalizedFrickeOperatorCuspEquiv, LinearEquiv.trans_apply,
    LinearEquiv.smulOfUnit_apply, Units.val_mk0, frickeOperatorCuspEquiv_apply,
    normalizedFrickeOperatorCusp_def, LinearMap.smul_apply]

/-- The inverse of the bundled normalized Fricke automorphism on cusp forms. -/
@[simp]
public theorem normalizedFrickeOperatorCuspEquiv_symm_apply (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (normalizedFrickeOperatorCuspEquiv (N := N) k).symm f =
      ((-1 : ℂ) ^ k) • normalizedFrickeOperatorCusp k f := by
  apply (normalizedFrickeOperatorCuspEquiv (N := N) k).injective
  rw [LinearEquiv.apply_symm_apply, normalizedFrickeOperatorCuspEquiv_apply, map_smul,
    normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp_apply, smul_smul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

/-! ### The nebentypus -/

/-- **The normalized Fricke operator shifts the nebentypus to its inverse**: it carries
`M_k(Γ₁(N), χ)` into `M_k(Γ₁(N), χ⁻¹)`. Scaling by a constant does not move a subspace, so this
is the raw statement `frickeOperator_mem_modFormCharSpace` read through the normalization. -/
public theorem normalizedFrickeOperator_mem_modFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    normalizedFrickeOperator k f ∈ modFormCharSpace k χ⁻¹ := by
  rw [normalizedFrickeOperator_def, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (frickeOperator_mem_modFormCharSpace k χ hf)

/-- **The normalized Fricke operator shifts the nebentypus to its inverse, on cusp forms.** -/
public theorem normalizedFrickeOperatorCusp_mem_cuspFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    normalizedFrickeOperatorCusp k f ∈ cuspFormCharSpace k χ⁻¹ := by
  rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (frickeOperatorCusp_mem_cuspFormCharSpace k χ hf)

/-- **The normalized Fricke operator restricted to a nebentypus space**, as a linear map from
`M_k(Γ₁(N), χ)` to `M_k(Γ₁(N), χ⁻¹)`. -/
public noncomputable def normalizedFrickeCharRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ⁻¹ :=
  frickeNormalizer N k • frickeCharRestrict k χ

/-- On underlying modular forms, `normalizedFrickeCharRestrict` is
`normalizedFrickeOperator`. -/
@[simp]
public theorem coe_normalizedFrickeCharRestrict_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : modFormCharSpace k χ) :
    ((normalizedFrickeCharRestrict k χ f : modFormCharSpace k χ⁻¹) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      normalizedFrickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [normalizedFrickeCharRestrict, normalizedFrickeOperator_def]

/-- **The normalized Fricke operator restricted to a cusp-form nebentypus space**, as a linear
map from `S_k(Γ₁(N), χ)` to `S_k(Γ₁(N), χ⁻¹)`. -/
public noncomputable def normalizedFrickeCharCuspRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ →ₗ[ℂ] cuspFormCharSpace k χ⁻¹ :=
  frickeNormalizer N k • frickeCharCuspRestrict k χ

/-- On underlying cusp forms, `normalizedFrickeCharCuspRestrict` is
`normalizedFrickeOperatorCusp`. -/
@[simp]
public theorem coe_normalizedFrickeCharCuspRestrict_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : cuspFormCharSpace k χ) :
    ((normalizedFrickeCharCuspRestrict k χ f : cuspFormCharSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      normalizedFrickeOperatorCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [normalizedFrickeCharCuspRestrict, normalizedFrickeOperatorCusp_def]

/-- **The normalized Fricke automorphism carries the `χ`-space onto the `χ⁻¹`-space.** -/
@[simp]
public theorem map_normalizedFrickeOperatorEquiv_modFormCharSpace (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    (modFormCharSpace k χ).map (normalizedFrickeOperatorEquiv (N := N) k : _ →ₗ[ℂ] _) =
      modFormCharSpace k χ⁻¹ := by
  have heq : (normalizedFrickeOperatorEquiv (N := N) k).toLinearMap =
      frickeNormalizer N k • (frickeOperatorEquiv (N := N) k).toLinearMap := by
    ext f
    simp [normalizedFrickeOperatorEquiv_apply, normalizedFrickeOperator_def]
  rw [heq, Submodule.map_smul _ _ _ (frickeNormalizer_ne_zero k),
    map_frickeOperatorEquiv_modFormCharSpace]

/-- **The normalized Fricke isomorphism between nebentypus spaces**
`M_k(Γ₁(N), χ) ≃ₗ[ℂ] M_k(Γ₁(N), χ⁻¹)`. -/
public noncomputable def normalizedFrickeCharEquiv (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ ≃ₗ[ℂ] modFormCharSpace k χ⁻¹ :=
  (frickeCharEquiv k χ).trans <|
    LinearEquiv.smulOfUnit (Units.mk0 (frickeNormalizer N k) (frickeNormalizer_ne_zero k))

/-- On underlying modular forms, `normalizedFrickeCharEquiv` is
`normalizedFrickeOperator`. -/
@[simp]
public theorem coe_normalizedFrickeCharEquiv_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : modFormCharSpace k χ) :
    ((normalizedFrickeCharEquiv k χ f : modFormCharSpace k χ⁻¹) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      normalizedFrickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp only [normalizedFrickeCharEquiv, LinearEquiv.trans_apply,
    LinearEquiv.smulOfUnit_apply, Units.val_mk0, Submodule.coe_smul,
    coe_frickeCharEquiv_apply, normalizedFrickeOperator_def, LinearMap.smul_apply]

/-- On underlying modular forms, the inverse of `normalizedFrickeCharEquiv` is
`(-1) ^ k • normalizedFrickeOperator`. -/
@[simp]
public theorem coe_normalizedFrickeCharEquiv_symm_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : modFormCharSpace k χ⁻¹) :
    (((normalizedFrickeCharEquiv k χ).symm g : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ((-1 : ℂ) ^ k) •
        normalizedFrickeOperator k (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hg : (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      normalizedFrickeOperator k
        (((normalizedFrickeCharEquiv k χ).symm g : modFormCharSpace k χ) :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [← coe_normalizedFrickeCharEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [hg, normalizedFrickeOperator_normalizedFrickeOperator_apply, smul_smul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

/-- **The normalized Fricke automorphism carries the `χ`-space of cusp forms onto the
`χ⁻¹`-space.** -/
@[simp]
public theorem map_normalizedFrickeOperatorCuspEquiv_cuspFormCharSpace (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    (cuspFormCharSpace k χ).map (normalizedFrickeOperatorCuspEquiv (N := N) k : _ →ₗ[ℂ] _) =
      cuspFormCharSpace k χ⁻¹ := by
  have heq : (normalizedFrickeOperatorCuspEquiv (N := N) k).toLinearMap =
      frickeNormalizer N k • (frickeOperatorCuspEquiv (N := N) k).toLinearMap := by
    ext f
    simp [normalizedFrickeOperatorCuspEquiv_apply, normalizedFrickeOperatorCusp_def]
  rw [heq, Submodule.map_smul _ _ _ (frickeNormalizer_ne_zero k),
    map_frickeOperatorCuspEquiv_cuspFormCharSpace]

/-- **The normalized Fricke isomorphism between cusp-form nebentypus spaces**
`S_k(Γ₁(N), χ) ≃ₗ[ℂ] S_k(Γ₁(N), χ⁻¹)`. -/
public noncomputable def normalizedFrickeCharCuspEquiv (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ ≃ₗ[ℂ] cuspFormCharSpace k χ⁻¹ :=
  (frickeCharCuspEquiv k χ).trans <|
    LinearEquiv.smulOfUnit (Units.mk0 (frickeNormalizer N k) (frickeNormalizer_ne_zero k))

/-- On underlying cusp forms, `normalizedFrickeCharCuspEquiv` is
`normalizedFrickeOperatorCusp`. -/
@[simp]
public theorem coe_normalizedFrickeCharCuspEquiv_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : cuspFormCharSpace k χ) :
    ((normalizedFrickeCharCuspEquiv k χ f : cuspFormCharSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      normalizedFrickeOperatorCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp only [normalizedFrickeCharCuspEquiv, LinearEquiv.trans_apply,
    LinearEquiv.smulOfUnit_apply, Units.val_mk0, Submodule.coe_smul,
    coe_frickeCharCuspEquiv_apply, normalizedFrickeOperatorCusp_def, LinearMap.smul_apply]

/-- On underlying cusp forms, the inverse of `normalizedFrickeCharCuspEquiv` is
`(-1) ^ k • normalizedFrickeOperatorCusp`. -/
@[simp]
public theorem coe_normalizedFrickeCharCuspEquiv_symm_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : cuspFormCharSpace k χ⁻¹) :
    (((normalizedFrickeCharCuspEquiv k χ).symm g : cuspFormCharSpace k χ) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ((-1 : ℂ) ^ k) •
        normalizedFrickeOperatorCusp k (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hg : (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      normalizedFrickeOperatorCusp k
        (((normalizedFrickeCharCuspEquiv k χ).symm g : cuspFormCharSpace k χ) :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [← coe_normalizedFrickeCharCuspEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [hg, normalizedFrickeOperatorCusp_normalizedFrickeOperatorCusp_apply, smul_smul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

/-! ### The eigenspace splitting in even weight -/

/-- **In even weight the `±1` eigenspaces of `𝒲_N` are complementary in `M_k(Γ₁(N))`.**

This is the splitting from which the sign of the functional equation of `L(s, f)` is read off:
on the `+1` eigenspace `𝒲_N f = f`, on the `-1` eigenspace `𝒲_N f = -f`, and every modular form
is uniquely a sum of one of each. -/
public theorem isCompl_eigenspace_normalizedFrickeOperator {k : ℤ} (hk : Even k) :
    IsCompl (Module.End.eigenspace (normalizedFrickeOperator (N := N) k) 1)
      (Module.End.eigenspace (normalizedFrickeOperator (N := N) k) (-1)) :=
  isCompl_eigenspace_one_neg_one (isUnit_iff_ne_zero.mpr two_ne_zero)
    (normalizedFrickeOperator_involutive hk)

/-- **In even weight the `±1` eigenspaces of `𝒲_N` are complementary in `S_k(Γ₁(N))`.** -/
public theorem isCompl_eigenspace_normalizedFrickeOperatorCusp {k : ℤ} (hk : Even k) :
    IsCompl (Module.End.eigenspace (normalizedFrickeOperatorCusp (N := N) k) 1)
      (Module.End.eigenspace (normalizedFrickeOperatorCusp (N := N) k) (-1)) :=
  isCompl_eigenspace_one_neg_one (isUnit_iff_ne_zero.mpr two_ne_zero)
    (normalizedFrickeOperatorCusp_involutive hk)

end TauCeti
