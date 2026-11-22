/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.LinearCharacter.Eigenspace
import TauCeti.FieldTheory.Galois.Trace

/-!
# Character sums of relative norms

Let `L/F` be a finite Galois extension with group `Δ = Gal(L/F)`, let `O` be a commutative ring
and `χ : Δ →* Oˣ` a linear character. The group `Δ` acts on `Lˣ`, hence `O`-linearly on
`O ⊗ Lˣ`, the multiplicative group written additively with coefficients extended to `O`. For an
element `z` of an extension `M` of `L`, put

`ξ_χ(z) = S_χ(1 ⊗ N_{M/L}(z)) = ∑_{δ ∈ Δ} χ(δ)⁻¹ ⊗ δ(N_{M/L} z) ∈ O ⊗ Lˣ`,

here `TauCeti.charSumNorm χ z`, where `S_χ` is the character sum
`Representation.charSum`. Multiplicatively it is the twisted product `∏_δ δ(N_{M/L} z)^{χ(δ)⁻¹}`.

With `F = ℚ`, `M = ℚ(μ_f)`, `L` the field cut out by an even Dirichlet character `χ` of conductor
`f` and `z = 1 - ζ_f`, this is Rubin's generator `ξ_{L,χ}` of the `χ`-part of the cyclotomic
units; over the layers `F = ℚ_n` of the cyclotomic `ℤ_p`-extension, with `L = L_n` and
`M = ℚ_n(μ_{f p^{n+1}})`, it is `ξ_{n,χ}`. Taking the relative norm to `L` first keeps the element
in `O ⊗ Lˣ`, with no descent from `O ⊗ Mˣ`.

The basic properties are:

* `ξ_χ(z)` lies in the `χ`-eigensubmodule of `O ⊗ Lˣ`, so `δ ξ_χ(z) = χ(δ) ξ_χ(z)`;
* `ξ_χ` turns products into sums;
* if `O` is a domain and `χ` is nontrivial, then `ξ_χ(c z) = ξ_χ(z)` for every `c ∈ Fˣ`, because
  the norm of `c` is fixed by `Δ` and `∑_δ χ(δ)⁻¹ = 0`. In particular `ξ_χ(-z) = ξ_χ(z)`, so the
  normalizations `1 - ζ` and `ζ - 1` give the same element;
* if `M/F` is also finite Galois, the image of `ξ_χ(z)` in `O ⊗ Mˣ` is the character sum
  `S_{χ ∘ res}(1 ⊗ z) = ∑_{δ ∈ Gal(M/F)} χ(δ|_L)⁻¹ ⊗ δ z` over the larger group, where
  `res : Gal(M/F) → Δ` is restriction. This is Rubin's product
  `∏_{δ ∈ Gal(M/F)} (δ z)^{χ⁻¹(δ)}`: grouping the automorphisms by their restriction to `L`, each
  fibre is a coset of `Gal(M/L)` and its product of conjugates is a conjugate of `N_{M/L} z`.

## Main definitions

* `TauCeti.charSumNorm χ z`: the character sum `S_χ(1 ⊗ N_{M/L} z)` in `O ⊗ Lˣ`.

## Main results

* `TauCeti.charSumNorm_eq_sum`: `ξ_χ(z) = ∑_δ χ(δ)⁻¹ ⊗ δ(N_{M/L} z)`.
* `TauCeti.charSumNorm_mem_charEigenspace`,
  `TauCeti.baseChange_ofMulDistribMulAction_apply_charSumNorm`: `ξ_χ(z)` is a `χ`-eigenvector of
  the Galois action.
* `TauCeti.charSumNorm_mul`, `TauCeti.charSumNorm_one`: `ξ_χ(z w) = ξ_χ(z) + ξ_χ(w)` and
  `ξ_χ(1) = 0`.
* `TauCeti.charSumNorm_eq_zero`, `TauCeti.charSumNorm_neg`,
  `TauCeti.charSumNorm_units_map_algebraMap_mul`: for a nontrivial character with values in a
  domain, `ξ_χ` vanishes when the norm is Galois invariant, and so is unchanged by the sign and by
  scalars from `F`.
* `TauCeti.baseChange_units_map_charSumNorm` and `TauCeti.baseChange_units_map_charSumNorm_eq_sum`:
  for `M/F` finite Galois, the image of `ξ_χ(z)` in `O ⊗ Mˣ` is the character sum of `1 ⊗ z` for
  the character `χ ∘ res` of `Gal(M/F)`.

## References

* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147 (2000), Chapter III, §2.2,
  display (4), and §2.4, Definition 2.2.
-/

public section

open TensorProduct Representation

namespace TauCeti

variable {O F L M : Type*} [CommRing O] [Field F] [Field L] [Field M] [Algebra F L]
  [FiniteDimensional F L] [Algebra L M]

/-- **The character sum of a relative norm** `ξ_χ(z) = S_χ(1 ⊗ N_{M/L} z)` in `O ⊗ Lˣ`, for a
linear character `χ : Gal(L/F) →* Oˣ` and a unit `z` of an extension `M` of `L`: the sum
`∑_δ χ(δ)⁻¹ ⊗ δ(N_{M/L} z)` (`TauCeti.charSumNorm_eq_sum`), multiplicatively the twisted product
`∏_δ δ(N_{M/L} z)^{χ(δ)⁻¹}`. For `F = ℚ`, `M = ℚ(μ_f)` and `z = 1 - ζ_f` it is Rubin's
cyclotomic generator `ξ_{L,χ}`. -/
noncomputable def charSumNorm (χ : (L ≃ₐ[F] L) →* Oˣ) (z : Mˣ) : O ⊗[ℤ] Additive Lˣ :=
  ((ofMulDistribMulAction (L ≃ₐ[F] L) Lˣ).baseChange O).charSum χ
    ((1 : O) ⊗ₜ Additive.ofMul (Units.map (Algebra.norm L) z))

variable (χ : (L ≃ₐ[F] L) →* Oˣ)

theorem charSumNorm_def (z : Mˣ) :
    charSumNorm χ z = ((ofMulDistribMulAction (L ≃ₐ[F] L) Lˣ).baseChange O).charSum χ
      ((1 : O) ⊗ₜ Additive.ofMul (Units.map (Algebra.norm L) z)) :=
  (rfl)

/-- `ξ_χ(z)` is the `χ⁻¹`-weighted sum of the Galois conjugates of `1 ⊗ N_{M/L} z`. -/
theorem charSumNorm_eq_sum (z : Mˣ) :
    charSumNorm χ z = ∑ σ : L ≃ₐ[F] L, (((χ σ)⁻¹ : Oˣ) : O) •
      ((1 : O) ⊗ₜ Additive.ofMul (σ • Units.map (Algebra.norm L) z)) := by
  simp [charSumNorm_def, charSum_apply]

/-- **`ξ_χ(z)` lies in the `χ`-eigensubmodule** of `O ⊗ Lˣ`. -/
theorem charSumNorm_mem_charEigenspace (z : Mˣ) :
    charSumNorm χ z ∈ ((ofMulDistribMulAction (L ≃ₐ[F] L) Lˣ).baseChange O).charEigenspace χ :=
  charSum_apply_mem _ χ _

/-- **The Galois action on `ξ_χ(z)`**: `δ ξ_χ(z) = χ(δ) ξ_χ(z)` for every `δ ∈ Gal(L/F)`. -/
@[simp]
theorem baseChange_ofMulDistribMulAction_apply_charSumNorm (σ : L ≃ₐ[F] L) (z : Mˣ) :
    (ofMulDistribMulAction (L ≃ₐ[F] L) Lˣ σ).baseChange O (charSumNorm χ z) =
      (χ σ : O) • charSumNorm χ z := by
  rw [← baseChange_apply]
  exact (mem_charEigenspace_iff _ χ).1 (charSumNorm_mem_charEigenspace χ z) σ

/-- `ξ_χ` turns products into sums: `ξ_χ(z w) = ξ_χ(z) + ξ_χ(w)`. -/
@[simp]
theorem charSumNorm_mul (z w : Mˣ) :
    charSumNorm χ (z * w) = charSumNorm χ z + charSumNorm χ w := by
  simp [charSumNorm_def, ofMul_mul, tmul_add]

/-- `ξ_χ(1) = 0`. -/
@[simp]
theorem charSumNorm_one : charSumNorm χ (1 : Mˣ) = 0 := by
  simp [charSumNorm_def]

/-- **`ξ_χ` vanishes on elements whose norm is fixed by the Galois group**, when `χ` is
nontrivial with values in a domain: the nontrivial character sum kills `Gal(L/F)`-invariant
vectors. -/
theorem charSumNorm_eq_zero [IsDomain O] (hχ : χ ≠ 1) {w : Mˣ}
    (hw : ∀ σ : L ≃ₐ[F] L, σ • Units.map (Algebra.norm L) w = Units.map (Algebra.norm L) w) :
    charSumNorm χ w = 0 :=
  charSum_apply_eq_zero_of_mem_invariants _ χ hχ fun σ ↦ by
    rw [baseChange_apply, LinearMap.baseChange_tmul, ofMulDistribMulAction_apply_apply,
      toMul_ofMul, hw]

/-- **The sign does not change `ξ_χ`** when `χ` is nontrivial with values in a domain:
`ξ_χ(-z) = ξ_χ(z)`. So the normalizations `1 - ζ` and `ζ - 1` of the cyclotomic numbers give the
same `ξ_χ`. -/
theorem charSumNorm_neg [IsDomain O] (hχ : χ ≠ 1) (z : Mˣ) :
    charSumNorm χ (-z) = charSumNorm χ z := by
  rw [← neg_one_mul, charSumNorm_mul, add_eq_right]
  refine charSumNorm_eq_zero χ hχ fun σ ↦ Units.ext ?_
  have h : Algebra.norm L (-1 : M) = (-1) ^ Module.finrank L M := by
    rw [← map_one (algebraMap L M), ← map_neg, Algebra.norm_algebraMap]
  simp [h]

/-- **Scalars from the base field do not change `ξ_χ`** when `χ` is nontrivial with values in a
domain: `ξ_χ(c z) = ξ_χ(z)` for `c ∈ Fˣ`, because the norm of `c` lies in `F` and so is fixed by
`Gal(L/F)`. For the trivial character this fails, already for `F = L = M = ℚ`, `O = ℤ` and
`c = 2`: then `ξ_1(2 z) = (1 ⊗ 2) + ξ_1(z)`. -/
theorem charSumNorm_units_map_algebraMap_mul [Algebra F M] [IsScalarTower F L M] [IsDomain O]
    (hχ : χ ≠ 1) (c : Fˣ) (z : Mˣ) :
    charSumNorm χ (Units.map (algebraMap F M : F →* M) c * z) = charSumNorm χ z := by
  rw [charSumNorm_mul, add_eq_right]
  refine charSumNorm_eq_zero χ hχ fun σ ↦ Units.ext ?_
  have h : Algebra.norm L (algebraMap F M c) = algebraMap F L c ^ Module.finrank L M := by
    rw [IsScalarTower.algebraMap_apply F L M, Algebra.norm_algebraMap]
  simp [h]

section Galois

variable [Algebra F M] [IsScalarTower F L M] [FiniteDimensional F M] [IsGalois F M] [Normal F L]

/-- **The image of `ξ_χ(z)` in `O ⊗ Mˣ`** is the character sum `S_{χ ∘ res}(1 ⊗ z)` over
`Gal(M/F)`, for the character `χ ∘ res` of `Gal(M/F)` obtained by restricting automorphisms to
`L`. -/
theorem baseChange_units_map_charSumNorm (z : Mˣ) :
    (Units.map (algebraMap L M : L →* M)).toAdditive.toIntLinearMap.baseChange O
        (charSumNorm χ z) =
      ((ofMulDistribMulAction (M ≃ₐ[F] M) Mˣ).baseChange O).charSum
        (χ.comp (AlgEquiv.restrictNormalHom L)) ((1 : O) ⊗ₜ Additive.ofMul z) := by
  classical
  rw [charSumNorm_eq_sum, map_sum, charSum_apply,
    ← Finset.sum_fiberwise Finset.univ (AlgEquiv.restrictNormalHom (K₁ := M) L)]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  -- the conjugates `δ z` over the fibre above `σ` multiply to `σ (N_{M/L} z)`
  have h : Units.map (algebraMap L M : L →* M) (σ • Units.map (Algebra.norm L) z) =
      ∏ δ ∈ Finset.univ.filter (fun δ : M ≃ₐ[F] M ↦ AlgEquiv.restrictNormalHom L δ = σ),
        δ • z := by
    ext
    simp only [Units.coe_map, AlgEquiv.smul_units_def, Units.coe_prod]
    exact (MonoidHom.prod_fiber_apply_eq_algebraMap_norm _
      (fun δ x ↦ AlgEquiv.restrictNormal_commutes δ L x) σ (z : M)).symm
  rw [map_smul, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul, h, ofMul_prod, tmul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ hδ ↦ ?_
  rw [MonoidHom.comp_apply, (Finset.mem_filter.1 hδ).2]
  simp

/-- **Rubin's product description of `ξ_χ(z)`**: its image in `O ⊗ Mˣ` is
`∑_{δ ∈ Gal(M/F)} χ(δ|_L)⁻¹ ⊗ δ z`, multiplicatively `∏_δ (δ z)^{χ⁻¹(δ|_L)}`. -/
theorem baseChange_units_map_charSumNorm_eq_sum (z : Mˣ) :
    (Units.map (algebraMap L M : L →* M)).toAdditive.toIntLinearMap.baseChange O
        (charSumNorm χ z) =
      ∑ δ : M ≃ₐ[F] M, (((χ (AlgEquiv.restrictNormalHom L δ))⁻¹ : Oˣ) : O) •
        ((1 : O) ⊗ₜ Additive.ofMul (δ • z)) := by
  simp [baseChange_units_map_charSumNorm, charSum_apply]

end Galois

end TauCeti
