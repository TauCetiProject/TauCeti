/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Basic
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Cohomologous cocycles give isomorphic crossed products

Two `2`-cocycles `z` and `w` of `Aut_K(L)` with values in `Lˣ` are **cohomologous** when they
differ by the coboundary of a function `b : Aut_K(L) → Lˣ`:
`w(σ, τ) = z(σ, τ) · σ(b(τ)) · b(στ)⁻¹ · b(σ)`.
In Mathlib's language this says that the pointwise quotient `w / z` satisfies
`groupCohomology.IsMulCoboundary₂`, and that is how `TauCeti.TwoCocycle.Cohomologous` is defined;
`TauCeti.TwoCocycle.cohomologous_iff` is the explicit formula.

The crossed products of cohomologous cocycles are isomorphic as `K`-algebras: the `L`-linear
map `u'_σ ↦ b(σ) · u_σ` from the crossed product of `w` to that of `z` is multiplicative, because
`(b(σ) · u_σ) · (b(τ) · u_τ) = (b(σ) · σ(b(τ)) · z(σ, τ)) · u_{στ} = (w(σ, τ) · b(στ)) · u_{στ}`
is its value on `u'_σ · u'_τ = w(σ, τ) · u'_{στ}`.

## Main definitions

* `TauCeti.TwoCocycle.Cohomologous z w`: the cocycles `z` and `w` differ by a coboundary.
* `TauCeti.CrossedProduct.algEquivOfCoboundary b h`: for `w / z` the coboundary of `b`, the
  `L`-linear `K`-algebra isomorphism `CrossedProduct w ≃ₐ[K] CrossedProduct z` sending `u'_σ` to
  `b(σ) · u_σ`.

## Main results

* `TauCeti.TwoCocycle.cohomologous_iff`: being cohomologous, as the explicit formula in `L`.
* `TauCeti.TwoCocycle.Cohomologous.refl`, `.symm`, `.trans`: it is an equivalence relation.
* `TauCeti.CrossedProduct.nonempty_algEquiv_of_cohomologous`: the crossed products of
  cohomologous cocycles are isomorphic `K`-algebras.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open groupCohomology

universe u v

namespace TauCeti

variable {K : Type u} [CommSemiring K] {L : Type v} [CommRing L] [Algebra K L]

namespace TwoCocycle

/-- Two `2`-cocycles `z` and `w` are **cohomologous** when their pointwise quotient `w / z` is a
multiplicative `2`-coboundary, that is `w(σ, τ) = z(σ, τ) · σ(b(τ)) · b(στ)⁻¹ · b(σ)` for some
`b : Aut_K(L) → Lˣ`; see `TwoCocycle.cohomologous_iff`. -/
def Cohomologous (z w : TwoCocycle K L) : Prop :=
  IsMulCoboundary₂ fun p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) => w.toFun p.1 p.2 / z.toFun p.1 p.2

/-- The cocycles `z` and `w` are cohomologous if and only if
`w(σ, τ) = z(σ, τ) · σ(b(τ)) · b(στ)⁻¹ · b(σ)` for some `b : Aut_K(L) → Lˣ`. -/
theorem cohomologous_iff {z w : TwoCocycle K L} :
    z.Cohomologous w ↔ ∃ b : (L ≃ₐ[K] L) → Lˣ, ∀ σ τ : L ≃ₐ[K] L,
      (w.toFun σ τ : L) = z.toFun σ τ * σ (b τ : L) * (↑(b (σ * τ))⁻¹ : L) * b σ := by
  refine exists_congr fun b ↦ forall₂_congr fun σ τ ↦ ?_
  dsimp only
  rw [eq_comm, div_eq_iff_eq_mul, ← Units.val_inj]
  simp only [Units.val_mul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
    div_eq_mul_inv]
  constructor <;> intro h <;> rw [h] <;> ring

/-- Every cocycle is cohomologous to itself. -/
@[refl]
theorem Cohomologous.refl (z : TwoCocycle K L) : z.Cohomologous z :=
  ⟨1, fun _ _ ↦ by simp⟩

/-- Being cohomologous is symmetric. -/
@[symm]
theorem Cohomologous.symm {z w : TwoCocycle K L} (h : z.Cohomologous w) : w.Cohomologous z := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b⁻¹, fun σ τ ↦ ?_⟩
  dsimp only at hb ⊢
  rw [Pi.inv_apply, Pi.inv_apply, Pi.inv_apply, smul_inv', ← inv_div (w.toFun σ τ), ← hb σ τ]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]

/-- Being cohomologous is transitive. -/
@[trans]
theorem Cohomologous.trans {z w v : TwoCocycle K L} (h₁ : z.Cohomologous w)
    (h₂ : w.Cohomologous v) : z.Cohomologous v := by
  obtain ⟨b, hb⟩ := h₁
  obtain ⟨b', hb'⟩ := h₂
  refine ⟨b' * b, fun σ τ ↦ ?_⟩
  dsimp only at hb hb' ⊢
  rw [← div_mul_div_cancel (v.toFun σ τ) (w.toFun σ τ), ← hb σ τ, ← hb' σ τ]
  simp only [Pi.mul_apply, smul_mul', div_eq_mul_inv, mul_inv]
  ac_rfl

end TwoCocycle

namespace CrossedProduct

variable {z w : TwoCocycle K L} (b : (L ≃ₐ[K] L) → Lˣ)
  (h : ∀ σ τ : L ≃ₐ[K] L, σ • b τ / b (σ * τ) * b σ = w.toFun σ τ / z.toFun σ τ)

variable (z w) in
/-- The `L`-linear isomorphism `x · u'_σ ↦ (x · b(σ)) · u_σ` underlying
`CrossedProduct.algEquivOfCoboundary`. -/
private noncomputable def linearEquivOfCoboundary : CrossedProduct w ≃ₗ[L] CrossedProduct z :=
  (basis w).equiv ((basis z).unitsSMul b) (Equiv.refl _)

private theorem linearEquivOfCoboundary_smul_basis (σ : L ≃ₐ[K] L) (x : L) :
    linearEquivOfCoboundary z w b (x • basis w σ) = (x * b σ) • basis z σ := by
  rw [linearEquivOfCoboundary, map_smul, Module.Basis.equiv_apply, Equiv.refl_apply,
    Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul]

include h in
/-- The multiplication identity behind `CrossedProduct.algEquivOfCoboundary`. -/
private theorem linearEquivOfCoboundary_mul (a a' : CrossedProduct w) :
    linearEquivOfCoboundary z w b (a * a') =
      linearEquivOfCoboundary z w b a * linearEquivOfCoboundary z w b a' := by
  induction a using induction_on with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
  | smul_basis σ x =>
  induction a' using induction_on with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
  | smul_basis τ y =>
    simp only [smul_basis_mul_smul_basis, linearEquivOfCoboundary_smul_basis]
    congr 1
    -- read `h σ τ` as `w(σ, τ) = σ(b(τ)) · b(στ)⁻¹ · b(σ) · z(σ, τ)` in `L`
    have hw := congrArg ((↑) : Lˣ → L) (eq_div_iff_mul_eq'.1 (h σ τ)).symm
    simp only [Units.val_mul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
      div_eq_mul_inv] at hw
    rw [hw, map_mul]
    linear_combination (x * σ y * σ (b τ : L) * b σ * z.toFun σ τ) * Units.inv_mul (b (σ * τ))

include h in
/-- The unit identity behind `CrossedProduct.algEquivOfCoboundary`: at `σ = τ = 1` the
coboundary condition reads `b(1) = w(1, 1) / z(1, 1)`. -/
private theorem linearEquivOfCoboundary_one :
    linearEquivOfCoboundary z w b (1 : CrossedProduct w) = 1 := by
  have h1 : (w.toFun 1 1)⁻¹ * b 1 = (z.toFun 1 1)⁻¹ := by
    have := h 1 1
    rw [one_smul, mul_one, div_self', one_mul] at this
    rw [this, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [one_def, one_def, linearEquivOfCoboundary_smul_basis, ← Units.val_mul, h1]

/-- **Cohomologous cocycles have isomorphic crossed products.** If `w / z` is the coboundary of
`b : Aut_K(L) → Lˣ`, that is `w(σ, τ) = z(σ, τ) · σ(b(τ)) · b(στ)⁻¹ · b(σ)`, then
`x · u'_σ ↦ (x · b(σ)) · u_σ` is an isomorphism of `K`-algebras from the crossed product of `w` to
that of `z`. -/
noncomputable def algEquivOfCoboundary : CrossedProduct w ≃ₐ[K] CrossedProduct z :=
  .ofLinearEquiv ((linearEquivOfCoboundary z w b).restrictScalars K)
    (linearEquivOfCoboundary_one b h) (linearEquivOfCoboundary_mul b h)

/-- As a function, `CrossedProduct.algEquivOfCoboundary b h` is
`linearEquivOfCoboundary z w b`: `AlgEquiv.ofLinearEquiv` and `LinearEquiv.restrictScalars` do not
change the underlying function, so this holds by `rfl`. -/
private theorem coe_algEquivOfCoboundary :
    ⇑(algEquivOfCoboundary b h) = linearEquivOfCoboundary z w b :=
  rfl

/-- `CrossedProduct.algEquivOfCoboundary` sends `u'_σ` to `b(σ) · u_σ`. -/
@[simp]
theorem algEquivOfCoboundary_basis (σ : L ≃ₐ[K] L) :
    algEquivOfCoboundary b h (basis w σ) = (b σ : L) • basis z σ := by
  rw [coe_algEquivOfCoboundary, ← one_smul L (basis w σ), linearEquivOfCoboundary_smul_basis,
    one_mul]

/-- `CrossedProduct.algEquivOfCoboundary` is `L`-linear. -/
@[simp]
theorem algEquivOfCoboundary_smul (x : L) (a : CrossedProduct w) :
    algEquivOfCoboundary b h (x • a) = x • algEquivOfCoboundary b h a := by
  rw [coe_algEquivOfCoboundary, map_smul]

/-- `CrossedProduct.algEquivOfCoboundary` restricts to the identity on the embedded copies of
`L`. -/
@[simp]
theorem algEquivOfCoboundary_inc (x : L) : algEquivOfCoboundary b h (inc w x) = inc z x := by
  rw [← mul_one (inc w x), ← smul_def, algEquivOfCoboundary_smul, map_one, smul_def, mul_one]

/-- The coordinates of `CrossedProduct.algEquivOfCoboundary b h a` are those of `a`, the
`σ`-th one multiplied by `b(σ)`. -/
@[simp]
theorem repr_algEquivOfCoboundary (a : CrossedProduct w) (σ : L ≃ₐ[K] L) :
    (basis z).repr (algEquivOfCoboundary b h a) σ = (basis w).repr a σ * b σ := by
  -- `Basis.equiv` carries coordinates in `basis w` to coordinates in `(basis z).unitsSMul b`
  have hrepr : ((basis z).unitsSMul b).repr (algEquivOfCoboundary b h a) = (basis w).repr a := by
    rw [coe_algEquivOfCoboundary, linearEquivOfCoboundary, Module.Basis.equiv, Equiv.refl_symm,
      Module.Basis.reindex_refl, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hσ := DFunLike.congr_fun hrepr σ
  rw [Module.Basis.repr_unitsSMul, inv_smul_eq_iff, Units.smul_def, smul_eq_mul] at hσ
  rw [hσ, mul_comm]

/-- **The crossed products of cohomologous cocycles are isomorphic `K`-algebras.** -/
theorem nonempty_algEquiv_of_cohomologous (hzw : z.Cohomologous w) :
    Nonempty (CrossedProduct z ≃ₐ[K] CrossedProduct w) :=
  let ⟨b, hb⟩ := hzw
  ⟨(algEquivOfCoboundary b hb).symm⟩

end CrossedProduct

end TauCeti
