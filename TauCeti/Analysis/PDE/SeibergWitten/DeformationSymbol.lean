/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# The principal symbol of the anti-self-dual deformation operator

On an oriented Riemannian four-manifold the gauge-fixed linearization of the anti-self-dual
equations is the first-order operator `δ₀ = (-d*, √2 d⁺) : Ω¹ → Ω⁰ ⊕ Ω⁺`. Its principal symbol at
a covector `ξ` is the linear map
`σ_ξ(a) = (⟪ξ, a⟫, √2 (ξ ∧ a)⁺)`, `(ξ ∧ a)⁺ = (ξ ∧ a + ⋆(ξ ∧ a)) / 2`,
from covectors to `ℝ ⊕ Λ⁺` (`TauCeti.SeibergWitten.deformationSymbol`); here a covector is
identified with a vector, and a two-form with a two-vector, through the metric. This file
proves the pointwise algebra of `σ_ξ` used to orient the determinant line of `δ₀`.

**Ellipticity.** `|⟪ξ, a⟫|² + ‖√2 (ξ ∧ a)⁺‖² = ‖ξ‖² ‖a‖²`, so for `ξ ≠ 0` the symbol is `‖ξ‖`
times an isometry, and in particular injective. This uses only that `(ξ ∧ a) ∧ (ξ ∧ a) = 0`.

**Complex linearity.** Let `J` be an orthogonal almost complex structure inducing the
orientation, with Kähler two-vector `ω` (`TauCeti.AlmostComplexStructure.kahlerForm`) and
`ω_u = ω / √2`, a unit self-dual form. On `ℝ ⊕ Λ⁺ = ℝ ⊕ ℝ ω_u ⊕ (ℝ ω_u)ᗮ` put
`J′(f, g ω_u + ρ) = (-g, f ω_u + ω_u × ρ)`, where `ω_u × ρ = D_J ρ / 2` is the rotation by a right
angle of the anti-`J`-invariant self-dual forms, `D_J` being the derivation action of `J` on
two-forms. As a formula on `ℝ ⊕ ⋀²`, `J′(f, η) = (-⟪ω_u, η⟫, f ω_u + D_J η / 2)`
(`TauCeti.SeibergWitten.deformationComplexStructure`). Then `J′` preserves `ℝ ⊕ Λ⁺`, squares to
`-1` there, and `σ_ξ (J a) = J′ (σ_ξ a)` for every `ξ`. Consequently the complex-linear part
`δ_ω = (δ₀ - J′ δ₀ J) / 2` of `δ₀` has the same principal symbol as `δ₀`: their difference is of
order zero. At a unit `ξ` the symbol sends `ξ ↦ (1, 0)` and `J ξ ↦ (0, ω_u)`.

The statements involving `J` take a positively oriented orthonormal basis `e` with `J e₀ = e₁`
and `J e₂ = e₃` as a witness that the orientation is the complex orientation of `J`.

## Main definitions

* `TauCeti.SeibergWitten.deformationSymbol o hkl ξ`: the principal symbol `σ_ξ` of
  `δ₀ = (-d*, √2 d⁺)`, a linear map `V → ℝ × ⋀² V`.
* `TauCeti.SeibergWitten.deformationComplexStructure J`: the complex structure `J′` of
  `ℝ ⊕ Λ⁺`, as a linear endomorphism of `ℝ × ⋀² V`.

## Main results

* `TauCeti.SeibergWitten.hodgeStar_deformationSymbol_snd`: `σ_ξ` takes values in `ℝ ⊕ Λ⁺`.
* `TauCeti.SeibergWitten.deformationSymbol_fst_sq_add_norm_snd_sq`: the ellipticity identity
  `⟪ξ, a⟫² + ‖√2 (ξ ∧ a)⁺‖² = ‖ξ‖² ‖a‖²`, and `TauCeti.SeibergWitten.deformationSymbol_injective`.
* `TauCeti.SeibergWitten.hodgeStar_deformationComplexStructure_snd` and
  `TauCeti.SeibergWitten.deformationComplexStructure_deformationComplexStructure`: `J′`
  preserves `ℝ ⊕ Λ⁺` and squares to `-1` there.
* `TauCeti.SeibergWitten.deformationSymbol_comp_toLinearMap`: `σ_ξ ∘ J = J′ ∘ σ_ξ`.
* `TauCeti.SeibergWitten.two_inv_smul_sub_deformationComplexStructure_deformationSymbol`: the
  complex-linear part of the symbol is the symbol, `(σ_ξ a - J′ (σ_ξ (J a))) / 2 = σ_ξ a`.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  (o : Orientation ℝ V (Fin 4)) (hkl : 2 + 2 = finrank ℝ V)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance finiteDimensional_of_finrank_eq_four : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-- **The principal symbol of `δ₀ = (-d*, √2 d⁺)`** at `ξ`:
`σ_ξ(a) = (⟪ξ, a⟫, √2 (ξ ∧ a)⁺)`, where `(ξ ∧ a)⁺ = (ξ ∧ a + ⋆(ξ ∧ a)) / 2` is the self-dual part,
so that the second component is `(√2 / 2) (ξ ∧ a + ⋆(ξ ∧ a))`. -/
def deformationSymbol (ξ : V) : V →ₗ[ℝ] ℝ × ⋀[ℝ]^2 V where
  toFun a := (⟪ξ, a⟫, (√2 / 2) • (ιMulti ℝ 2 ![ξ, a] + o.hodgeStar hkl (ιMulti ℝ 2 ![ξ, a])))
  map_add' a b := by
    simp only [inner_add_right, ιMulti_two_add_right, map_add, Prod.mk_add_mk, smul_add]
    abel_nf
  map_smul' c a := by
    simp only [real_inner_smul_right, ιMulti_two_smul_right, map_smul, ← smul_add, smul_comm c,
      RingHom.id_apply, Prod.smul_mk, smul_eq_mul]

@[simp]
theorem deformationSymbol_apply_fst (ξ a : V) : (deformationSymbol o hkl ξ a).1 = ⟪ξ, a⟫ :=
  (rfl)

@[simp]
theorem deformationSymbol_apply_snd (ξ a : V) :
    (deformationSymbol o hkl ξ a).2 =
      (√2 / 2) • (ιMulti ℝ 2 ![ξ, a] + o.hodgeStar hkl (ιMulti ℝ 2 ![ξ, a])) :=
  (rfl)

/-- The symbol takes values in `ℝ ⊕ Λ⁺`: its two-form component is self-dual. -/
theorem hodgeStar_deformationSymbol_snd (ξ a : V) :
    o.hodgeStar hkl (deformationSymbol o hkl ξ a).2 = (deformationSymbol o hkl ξ a).2 := by
  rw [deformationSymbol_apply_snd, map_smul, map_add,
    o.hodgeStar_hodgeStar_of_even even_two hkl, add_comm]

/-- **Ellipticity of `δ₀`**: `⟪ξ, a⟫² + ‖√2 (ξ ∧ a)⁺‖² = ‖ξ‖² ‖a‖²`. Thus `σ_ξ` is `‖ξ‖` times an
isometry into `ℝ ⊕ Λ⁺` with its Euclidean norm. -/
theorem deformationSymbol_fst_sq_add_norm_snd_sq (ξ a : V) :
    (deformationSymbol o hkl ξ a).1 ^ 2 + ‖(deformationSymbol o hkl ξ a).2‖ ^ 2 =
      ‖ξ‖ ^ 2 * ‖a‖ ^ 2 := by
  -- `⟪x, ⋆x⟫ = vol(ξ, a, ξ, a) = 0` for `x = ξ ∧ a`, since `x ∧ x = 0`.
  have hx : ⟪ιMulti ℝ 2 ![ξ, a], o.hodgeStar hkl (ιMulti ℝ 2 ![ξ, a])⟫ = 0 := by
    rw [real_inner_comm, o.inner_hodgeStar_ιMulti_two hkl]
    exact o.volumeForm.map_eq_zero_of_eq ![ξ, a, ξ, a] (i := 0) (j := 2) rfl (by decide)
  have h2 : (√2 / 2) ^ 2 = 2⁻¹ := by
    rw [div_pow, Real.sq_sqrt zero_le_two]
    norm_num
  rw [deformationSymbol_apply_fst, deformationSymbol_apply_snd, norm_smul, mul_pow,
    Real.norm_of_nonneg (by positivity), h2, norm_add_sq_real, o.norm_hodgeStar, hx,
    ← real_inner_self_eq_norm_sq (ιMulti ℝ 2 ![ξ, a]), inner_ιMulti_two,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm a ξ]
  ring

/-- **The symbol of `δ₀` is injective at every nonzero covector**: `δ₀` is elliptic. -/
theorem deformationSymbol_injective {ξ : V} (hξ : ξ ≠ 0) :
    Function.Injective (deformationSymbol o hkl ξ) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  have h := deformationSymbol_fst_sq_add_norm_snd_sq o hkl ξ a
  rw [ha, Prod.fst_zero, Prod.snd_zero, norm_zero] at h
  have : ‖a‖ ^ 2 = 0 := by
    have hξ' : ‖ξ‖ ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.1 (by linarith)).resolve_left hξ'
  simpa using this

/-- At `ξ` itself the symbol is `σ_ξ(ξ) = (‖ξ‖², 0)`. -/
@[simp]
theorem deformationSymbol_self (ξ : V) : deformationSymbol o hkl ξ ξ = (‖ξ‖ ^ 2, 0) := by
  have h : ιMulti ℝ 2 ![ξ, ξ] = 0 :=
    (ιMulti ℝ 2).map_eq_zero_of_eq ![ξ, ξ] (i := 0) (j := 1) rfl zero_ne_one
  refine Prod.ext ?_ ?_
  · simp
  · simp [h]

/-- The linear map `J′(f, η) = (-⟪ω_u, η⟫, f ω_u + D_J η / 2)` on `ℝ × ⋀² V` determined by an
almost complex structure `J`, where `ω` is the Kähler two-vector of `J`, `ω_u = ω / √2 = (√2 / 2) ω`
and `D_J` is the derivation action of `J` on two-forms. The formula makes sense for every `J`.

When `J` is orthogonal and induces the orientation, witnessed by a positively oriented orthonormal
basis `e` with `J e₀ = e₁` and `J e₂ = e₃`, the form `ω_u` is a self-dual unit vector and
`D_J ω = 0`, so writing `η = g ω_u + ρ` with `ρ ⊥ ω_u` self-dual gives
`J′(f, g ω_u + ρ) = (-g, f ω_u + ω_u × ρ)`. Under these hypotheses `J′` preserves `ℝ ⊕ Λ⁺`
(`hodgeStar_deformationComplexStructure_snd`) and is a complex structure there
(`deformationComplexStructure_deformationComplexStructure`). -/
def deformationComplexStructure (J : AlmostComplexStructure V) :
    ℝ × ⋀[ℝ]^2 V →ₗ[ℝ] ℝ × ⋀[ℝ]^2 V where
  toFun p := (-(√2 / 2 * ⟪J.kahlerForm, p.2⟫),
    (√2 / 2 * p.1) • J.kahlerForm + (2⁻¹ : ℝ) • exteriorPower.lieMap 2 J.toLinearMap p.2)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, map_add, Prod.mk_add_mk, mul_add,
      add_smul, smul_add, neg_add]
    abel_nf
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul,
        RingHom.id_apply]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]
      module

@[simp]
theorem deformationComplexStructure_apply_fst (J : AlmostComplexStructure V)
    (p : ℝ × ⋀[ℝ]^2 V) :
    (deformationComplexStructure J p).1 = -(√2 / 2 * ⟪J.kahlerForm, p.2⟫) :=
  (rfl)

@[simp]
theorem deformationComplexStructure_apply_snd (J : AlmostComplexStructure V)
    (p : ℝ × ⋀[ℝ]^2 V) :
    (deformationComplexStructure J p).2 =
      (√2 / 2 * p.1) • J.kahlerForm + (2⁻¹ : ℝ) • exteriorPower.lieMap 2 J.toLinearMap p.2 :=
  (rfl)

/-! ### Complex linearity for the complex orientation -/

section Frame

variable {o} {e : OrthonormalBasis (Fin 4) ℝ V} (he : e.toBasis.orientation = o)
  {J : AlmostComplexStructure V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

include he h₀ h₂

/-- `J′` preserves `ℝ ⊕ Λ⁺`: its two-form component is self-dual on self-dual input. -/
theorem hodgeStar_deformationComplexStructure_snd {p : ℝ × ⋀[ℝ]^2 V}
    (hp : o.hodgeStar hkl p.2 = p.2) :
    o.hodgeStar hkl (deformationComplexStructure J p).2 = (deformationComplexStructure J p).2 := by
  rw [deformationComplexStructure_apply_snd, map_add, map_smul, map_smul,
    AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he,
    o.hodgeStar_lieMap_two hkl (AlmostComplexStructure.inner_apply_left
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂)), hp]

/-- **`J′` is a complex structure on `ℝ ⊕ Λ⁺`**: `J′ (J′ (f, η)) = -(f, η)` for self-dual `η`. -/
theorem deformationComplexStructure_deformationComplexStructure {p : ℝ × ⋀[ℝ]^2 V}
    (hp : o.hodgeStar hkl p.2 = p.2) :
    deformationComplexStructure J (deformationComplexStructure J p) = -p := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hω : ⟪J.kahlerForm, J.kahlerForm⟫ = 2 := by
    rw [AlmostComplexStructure.inner_kahlerForm_self hJ, Fact.out (p := finrank ℝ V = 4)]
    norm_num
  have hDω : exteriorPower.lieMap 2 J.toLinearMap J.kahlerForm = 0 :=
    AlmostComplexStructure.lieMap_kahlerForm hJ
  -- `⟪ω, D_J η⟫ = -⟪D_J ω, η⟫ = 0`.
  have hωD : ⟪J.kahlerForm, exteriorPower.lieMap 2 J.toLinearMap p.2⟫ = 0 := by
    rw [real_inner_comm, inner_lieMap_two_left
      (AlmostComplexStructure.inner_apply_left hJ), hDω, inner_zero_right, neg_zero]
  have hDD :=
    AlmostComplexStructure.lieMap_lieMap_of_hodgeStar_eq_self
      h₀ h₂ hkl he hp
  refine Prod.ext ?_ ?_
  · simp only [deformationComplexStructure_apply_fst, deformationComplexStructure_apply_snd,
      inner_add_right, real_inner_smul_right, hω, hωD, Prod.fst_neg]
    linear_combination (-p.1 / 2) * Real.mul_self_sqrt zero_le_two
  · simp only [deformationComplexStructure_apply_fst, deformationComplexStructure_apply_snd,
      map_add, map_smul, hDω, hDD, smul_zero, zero_add, Prod.snd_neg]
    linear_combination (norm := module)
      -(Real.mul_self_sqrt zero_le_two • (((4⁻¹ : ℝ) * ⟪J.kahlerForm, p.2⟫) • J.kahlerForm))

/-- **The principal symbol of `δ₀` is complex linear**: `σ_ξ (J a) = J′ (σ_ξ a)` for every `ξ`,
that is, `σ_ξ ∘ J = J′ ∘ σ_ξ`. -/
theorem deformationSymbol_comp_toLinearMap (ξ : V) :
    deformationSymbol o hkl ξ ∘ₗ J.toLinearMap =
      deformationComplexStructure J ∘ₗ deformationSymbol o hkl ξ := by
  refine LinearMap.ext fun a ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he
  have hz := AlmostComplexStructure.ιMulti_sub_ιMulti_add_hodgeStar h₀ h₂ hkl he ξ a
  refine Prod.ext ?_ ?_
  · -- `⟪ω, (ξ ∧ a)⁺⟫ = ⟪ω, ξ ∧ a⟫ = ⟪J ξ, a⟫ = -⟪ξ, J a⟫`.
    simp only [deformationSymbol_apply_fst, deformationComplexStructure_apply_fst,
      deformationSymbol_apply_snd, real_inner_smul_right, inner_add_right]
    have hs := o.isSymmetric_hodgeStar_of_even even_two hkl J.kahlerForm (ιMulti ℝ 2 ![ξ, a])
    simp only [LinearEquiv.coe_coe] at hs
    rw [← hs, hω, AlmostComplexStructure.inner_kahlerForm_ιMulti hJ,
      AlmostComplexStructure.inner_apply_left hJ]
    linear_combination (-⟪ξ, J a⟫ / 2) * Real.mul_self_sqrt zero_le_two
  · simp only [deformationSymbol_apply_snd, deformationComplexStructure_apply_snd,
      deformationSymbol_apply_fst, map_smul, map_add,
      ← o.hodgeStar_lieMap_two hkl (AlmostComplexStructure.inner_apply_left hJ),
      exteriorPower.lieMap_two_apply_ιMulti]
    rw [map_sub] at hz
    linear_combination (norm := module) (√2 / 4 : ℝ) • hz

/-- At `ξ` the symbol sends `J ξ` to `(0, ‖ξ‖² ω_u)`, `ω_u = (√2 / 2) ω`: for a unit `ξ = e₀` this
is the frame computation `e₀ ↦ (1, 0)`, `e₁ = J e₀ ↦ (0, ω_u)`. -/
theorem deformationSymbol_toLinearMap_self (ξ : V) :
    deformationSymbol o hkl ξ (J ξ) = (0, (√2 / 2 * ‖ξ‖ ^ 2) • J.kahlerForm) := by
  rw [← LinearMap.comp_apply, deformationSymbol_comp_toLinearMap hkl he h₀ h₂,
    LinearMap.comp_apply, deformationSymbol_self]
  refine Prod.ext ?_ ?_ <;> simp

/-- **The complex-linear part of `δ₀` has the same principal symbol as `δ₀`**: the symbol of
`δ_ω = (δ₀ - J′ δ₀ J) / 2` at `ξ`, namely `(σ_ξ - J′ σ_ξ J) / 2`, equals `σ_ξ`. Hence `δ₀` and
`δ_ω` differ by an operator of order zero. -/
theorem two_inv_smul_sub_deformationComplexStructure_deformationSymbol (ξ a : V) :
    (2⁻¹ : ℝ) • (deformationSymbol o hkl ξ a -
        deformationComplexStructure J (deformationSymbol o hkl ξ (J a))) =
      deformationSymbol o hkl ξ a := by
  rw [← LinearMap.comp_apply (deformationSymbol o hkl ξ),
    deformationSymbol_comp_toLinearMap hkl he h₀ h₂, LinearMap.comp_apply,
    deformationComplexStructure_deformationComplexStructure
    hkl he h₀ h₂ (hodgeStar_deformationSymbol_snd o hkl ξ a)]
  module

end Frame

end TauCeti.SeibergWitten
