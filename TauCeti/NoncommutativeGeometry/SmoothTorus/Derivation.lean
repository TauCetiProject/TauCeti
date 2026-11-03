/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.SmoothTorus.Basic
public import TauCeti.RingTheory.CyclicCohomology.Derivation

/-!
# The derivations of the smooth noncommutative torus and its cyclic cocycles

The gauge action of the two-torus on `𝒜_θ` multiplies the monomial `U₁ ^ m U₂ ^ n` by
`z₁ ^ m z₂ ^ n`. Its infinitesimal generators are the two basic derivations

`δ₁ (U₁ ^ m U₂ ^ n) = 2πi m U₁ ^ m U₂ ^ n` and `δ₂ (U₁ ^ m U₂ ^ n) = 2πi n U₁ ^ m U₂ ^ n`,

which play the role of the partial derivatives `∂/∂x` and `∂/∂y` on the ordinary torus, the case
`θ = 0`. More generally, every additive map `ℓ : ℤ × ℤ →+ ℂ` gives a derivation `δ_ℓ` of `𝒜_θ`
multiplying the coefficient at `x` by `ℓ x`: it preserves rapid decay because `ℓ` grows linearly,
and it obeys the Leibniz rule because the twisted product of `𝒜_θ` is graded by `ℤ × ℤ`. All these
derivations commute, they kill the canonical trace `τ`, and `δ_ℓ` is a star derivation when `ℓ`
takes purely imaginary values. The basic derivations are `δ₁ = δ_ℓ` for `ℓ (m, n) = 2πi m` and
`δ₂ = δ_ℓ` for `ℓ (m, n) = 2πi n`.

With the trace these give the cyclic cocycles of `𝒜_θ`

`ψ_j (a₀, a₁) = τ (a₀ δ_j(a₁))` and
`φ (a₀, a₁, a₂) = (2πi)⁻¹ τ (a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`

of degrees one and two, through the general construction `TauCeti.traceDerivationCocycle` and
`TauCeti.traceDerivationPairCocycle`. These are the odd and even classes in Connes' computation of
the periodic cyclic cohomology of `𝒜_θ`; Connes obtains `φ` as the character of the
two-dimensional differential calculus of `𝒜_θ`, while here it is built directly from the trace and
the derivations. The factor `(2πi)⁻¹` makes `φ` the noncommutative analogue of
`(2πi)⁻¹ ∫ f₀ df₁ ∧ df₂`; on the generators, `φ (star (U₁ U₂), U₁, U₂) = 2πi`.

## Main definitions

* `TauCeti.SmoothNoncommutativeTorus.gaugeDerivation θ ℓ`: the derivation `δ_ℓ` of `𝒜_θ`
  multiplying the coefficient at `x` by `ℓ x`.
* `TauCeti.SmoothNoncommutativeTorus.derivation₁`, `TauCeti.SmoothNoncommutativeTorus.derivation₂`:
  the basic derivations `δ₁` and `δ₂`.
* `TauCeti.SmoothNoncommutativeTorus.oddCocycle₁`, `TauCeti.SmoothNoncommutativeTorus.oddCocycle₂`:
  the cyclic `1`-cocycles `ψ_j (a₀, a₁) = τ (a₀ δ_j(a₁))`.
* `TauCeti.SmoothNoncommutativeTorus.fundamentalCocycle`: the cyclic `2`-cocycle `φ`.

## Main statements

* `TauCeti.SmoothNoncommutativeTorus.trace_gaugeDerivation`: `τ ∘ δ_ℓ = 0`.
* `TauCeti.SmoothNoncommutativeTorus.gaugeDerivation_star`: `δ_ℓ` commutes with the involution when
  `ℓ` is purely imaginary.
* `TauCeti.SmoothNoncommutativeTorus.commute_gaugeDerivation`,
  `TauCeti.SmoothNoncommutativeTorus.lie_gaugeDerivation`: the derivations `δ_ℓ` commute.
* `TauCeti.SmoothNoncommutativeTorus.derivation₁_U₁_zpow_mul_U₂_zpow` and
  `TauCeti.SmoothNoncommutativeTorus.derivation₂_U₁_zpow_mul_U₂_zpow`: the values of `δ₁` and `δ₂`
  on the ordered monomials.
* `TauCeti.SmoothNoncommutativeTorus.fundamentalCocycle_apply_single`: on monomials, `φ` is `2πi`
  times the determinant of the last two exponents times the trace of the product.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §2.β, and Chapter IV,
  §6.
-/

public section

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace TauCeti

namespace SmoothNoncommutativeTorus

variable {θ : ℝ}

/-! ### Derivations along additive maps of the lattice -/

/-- The coefficients `ℓ x * a x` stay rapidly decreasing, because `ℓ` grows linearly. -/
private theorem isRapidDecay_addMonoidHom_mul (ℓ : ℤ × ℤ →+ ℂ) (a : SmoothNoncommutativeTorus θ) :
    IsRapidDecay fun x ↦ ℓ x * a.coeff x :=
  a.isRapidDecay_coeff.mul_left_of_norm_le (f := fun x ↦ ℓ x) (n := 1) fun x ↦ by
    simpa using norm_addMonoidHom_apply_le_mul_weight ℓ x

/-- The linear map multiplying the coefficient at `x` by `ℓ x`. -/
private def gaugeDerivationLinearMap (ℓ : ℤ × ℤ →+ ℂ) :
    Module.End ℂ (SmoothNoncommutativeTorus θ) where
  toFun a := ⟨fun x ↦ ℓ x * a.coeff x, isRapidDecay_addMonoidHom_mul ℓ a⟩
  map_add' a b := by ext x; simp [mul_add]
  map_smul' c a := by ext x; simp [mul_left_comm]

private theorem coeff_gaugeDerivationLinearMap (ℓ : ℤ × ℤ →+ ℂ)
    (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    (gaugeDerivationLinearMap ℓ a).coeff x = ℓ x * a.coeff x :=
  (rfl)

/-- Multiplication by `ℓ` obeys the Leibniz rule: the twisted convolution only combines
coefficients at `y` and `x - y` into the coefficient at `x`, and `ℓ x = ℓ y + ℓ (x - y)`. -/
private theorem gaugeDerivationLinearMap_mul (ℓ : ℤ × ℤ →+ ℂ)
    (a b : SmoothNoncommutativeTorus θ) :
    gaugeDerivationLinearMap ℓ (a * b) =
      gaugeDerivationLinearMap ℓ a * b + a * gaugeDerivationLinearMap ℓ b := by
  ext x
  rw [coeff_add, Pi.add_apply, coeff_gaugeDerivationLinearMap, coeff_mul, coeff_mul, coeff_mul,
    ← (summable_mul_coeff _ _ x).tsum_add (summable_mul_coeff _ _ x), ← tsum_mul_left]
  refine tsum_congr fun y ↦ ?_
  simp only [coeff_gaugeDerivationLinearMap]
  rw [show ℓ x = ℓ y + ℓ (x - y) by rw [← map_add, add_sub_cancel]]
  ring

variable (θ) in
/-- The derivation `δ_ℓ` of `𝒜_θ` along an additive map `ℓ : ℤ × ℤ →+ ℂ`: it multiplies the
coefficient at `x` by `ℓ x`, so `δ_ℓ (U₁ ^ m U₂ ^ n) = ℓ (m, n) U₁ ^ m U₂ ^ n`. For purely
imaginary `ℓ` it is the derivative at `t = 0` of the gauge automorphisms multiplying the
coefficient at `x` by `exp(t ℓ x)`. -/
def gaugeDerivation (ℓ : ℤ × ℤ →+ ℂ) : derivationLieAlgebra ℂ (SmoothNoncommutativeTorus θ) :=
  ⟨gaugeDerivationLinearMap ℓ, mem_derivationLieAlgebra.2 (gaugeDerivationLinearMap_mul ℓ)⟩

@[simp]
theorem coeff_gaugeDerivation (ℓ : ℤ × ℤ →+ ℂ) (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    ((gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a).coeff x =
      ℓ x * a.coeff x :=
  (rfl)

@[simp]
theorem gaugeDerivation_single (ℓ : ℤ × ℤ →+ ℂ) (x : ℤ × ℤ) (c : ℂ) :
    (gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (single x c) =
      single x (ℓ x * c) := by
  ext y
  rcases eq_or_ne y x with rfl | hy
  · simp
  · simp [hy]

/-- The canonical trace is invariant under `δ_ℓ`: `τ (δ_ℓ a) = 0`. -/
theorem trace_gaugeDerivation (ℓ : ℤ × ℤ →+ ℂ) (a : SmoothNoncommutativeTorus θ) :
    trace θ ((gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a) = 0 := by
  simp

/-- For purely imaginary `ℓ`, the derivation `δ_ℓ` is a star derivation. -/
@[simp]
theorem gaugeDerivation_star {ℓ : ℤ × ℤ →+ ℂ} (hℓ : ∀ x, conj (ℓ x) = -ℓ x)
    (a : SmoothNoncommutativeTorus θ) :
    (gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (star a) =
      star ((gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a) := by
  ext x
  simp only [coeff_gaugeDerivation, coeff_star, map_mul, map_neg, hℓ, neg_neg]
  ring

/-- Any two derivations `δ_ℓ` and `δ_ℓ'` commute. -/
theorem commute_gaugeDerivation (ℓ ℓ' : ℤ × ℤ →+ ℂ) :
    Commute (gaugeDerivation θ ℓ : Module.End ℂ (SmoothNoncommutativeTorus θ))
      (gaugeDerivation θ ℓ' : Module.End ℂ (SmoothNoncommutativeTorus θ)) := by
  refine LinearMap.ext fun a ↦ ?_
  ext x
  simp only [mul_apply_eq_comp, coeff_gaugeDerivation]
  ring

/-- The Lie bracket of any two derivations `δ_ℓ` and `δ_ℓ'` vanishes: `⁅δ_ℓ, δ_ℓ'⁆ = 0`. -/
@[simp]
theorem lie_gaugeDerivation (ℓ ℓ' : ℤ × ℤ →+ ℂ) :
    ⁅gaugeDerivation θ ℓ, gaugeDerivation θ ℓ'⁆ = 0 :=
  Subtype.ext <| by
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, (commute_gaugeDerivation ℓ ℓ').eq,
      sub_self, ZeroMemClass.coe_zero]

/-- `δ_0 = 0`. -/
@[simp]
theorem gaugeDerivation_zero : gaugeDerivation θ 0 = 0 := by
  ext a x
  simp

/-- `δ_ℓ` is additive in `ℓ`: `δ_(ℓ + ℓ') = δ_ℓ + δ_ℓ'`. -/
theorem gaugeDerivation_add (ℓ ℓ' : ℤ × ℤ →+ ℂ) :
    gaugeDerivation θ (ℓ + ℓ') = gaugeDerivation θ ℓ + gaugeDerivation θ ℓ' := by
  ext a x
  simp [add_mul]

/-- `δ_ℓ` is homogeneous in `ℓ`: `δ_(c • ℓ) = c • δ_ℓ`. -/
theorem gaugeDerivation_smul (c : ℂ) (ℓ : ℤ × ℤ →+ ℂ) :
    gaugeDerivation θ (c • ℓ) = c • gaugeDerivation θ ℓ := by
  ext a x
  simp [mul_assoc]

/-! ### The two basic derivations -/

variable (θ) in
/-- The basic derivation `δ₁ (U₁ ^ m U₂ ^ n) = 2πi m U₁ ^ m U₂ ^ n` of `𝒜_θ`, the analogue of
`∂/∂x` on the ordinary torus. -/
def derivation₁ : derivationLieAlgebra ℂ (SmoothNoncommutativeTorus θ) :=
  gaugeDerivation θ ((2 * π * I) • (Int.castAddHom ℂ).comp (AddMonoidHom.fst ℤ ℤ))

variable (θ) in
/-- The basic derivation `δ₂ (U₁ ^ m U₂ ^ n) = 2πi n U₁ ^ m U₂ ^ n` of `𝒜_θ`, the analogue of
`∂/∂y` on the ordinary torus. -/
def derivation₂ : derivationLieAlgebra ℂ (SmoothNoncommutativeTorus θ) :=
  gaugeDerivation θ ((2 * π * I) • (Int.castAddHom ℂ).comp (AddMonoidHom.snd ℤ ℤ))

@[simp]
theorem coeff_derivation₁ (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    ((derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a).coeff x =
      2 * π * I * x.1 * a.coeff x := by
  simp [derivation₁]

@[simp]
theorem coeff_derivation₂ (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    ((derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a).coeff x =
      2 * π * I * x.2 * a.coeff x := by
  simp [derivation₂]

@[simp]
theorem derivation₁_single (x : ℤ × ℤ) (c : ℂ) :
    (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (single x c) =
      single x (2 * π * I * x.1 * c) := by
  simp [derivation₁]

@[simp]
theorem derivation₂_single (x : ℤ × ℤ) (c : ℂ) :
    (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (single x c) =
      single x (2 * π * I * x.2 * c) := by
  simp [derivation₂]

/-- `δ₁ (U₁ ^ m U₂ ^ n) = 2πi m U₁ ^ m U₂ ^ n`. -/
theorem derivation₁_U₁_zpow_mul_U₂_zpow (m n : ℤ) :
    (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ))
        ((U₁ θ ^ m : unitary _) * (U₂ θ ^ n : unitary _)) =
      (2 * π * I * m) • ((U₁ θ ^ m : unitary _) * (U₂ θ ^ n : unitary _) :
        SmoothNoncommutativeTorus θ) := by
  rw [U₁_zpow_mul_U₂_zpow]
  simp

/-- `δ₂ (U₁ ^ m U₂ ^ n) = 2πi n U₁ ^ m U₂ ^ n`. -/
theorem derivation₂_U₁_zpow_mul_U₂_zpow (m n : ℤ) :
    (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ))
        ((U₁ θ ^ m : unitary _) * (U₂ θ ^ n : unitary _)) =
      (2 * π * I * n) • ((U₁ θ ^ m : unitary _) * (U₂ θ ^ n : unitary _) :
        SmoothNoncommutativeTorus θ) := by
  rw [U₁_zpow_mul_U₂_zpow]
  simp

/-- `δ₁ U₁ = 2πi U₁`. -/
theorem derivation₁_U₁ :
    (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (U₁ θ) =
      (2 * π * I) • (U₁ θ : SmoothNoncommutativeTorus θ) := by
  simp

/-- `δ₁ U₂ = 0`. -/
theorem derivation₁_U₂ :
    (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (U₂ θ) = 0 := by
  simp

/-- `δ₂ U₁ = 0`. -/
theorem derivation₂_U₁ :
    (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (U₁ θ) = 0 := by
  simp

/-- `δ₂ U₂ = 2πi U₂`. -/
theorem derivation₂_U₂ :
    (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (U₂ θ) =
      (2 * π * I) • (U₂ θ : SmoothNoncommutativeTorus θ) := by
  simp

/-- The canonical trace is invariant under `δ₁`: `τ (δ₁ a) = 0`. -/
theorem trace_derivation₁ (a : SmoothNoncommutativeTorus θ) :
    trace θ ((derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a) = 0 :=
  trace_gaugeDerivation _ a

/-- The canonical trace is invariant under `δ₂`: `τ (δ₂ a) = 0`. -/
theorem trace_derivation₂ (a : SmoothNoncommutativeTorus θ) :
    trace θ ((derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a) = 0 :=
  trace_gaugeDerivation _ a

/-- `δ₁` is a star derivation: `δ₁ (star a) = star (δ₁ a)`. -/
@[simp]
theorem derivation₁_star (a : SmoothNoncommutativeTorus θ) :
    (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (star a) =
      star ((derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a) :=
  gaugeDerivation_star (fun x ↦ by simp [map_ofNat]) a

/-- `δ₂` is a star derivation: `δ₂ (star a) = star (δ₂ a)`. -/
@[simp]
theorem derivation₂_star (a : SmoothNoncommutativeTorus θ) :
    (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (star a) =
      star ((derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) a) :=
  gaugeDerivation_star (fun x ↦ by simp [map_ofNat]) a

/-- The two basic derivations commute: `δ₁ δ₂ = δ₂ δ₁`. -/
theorem commute_derivation₁_derivation₂ :
    Commute (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ))
      (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) :=
  commute_gaugeDerivation _ _

/-- The Lie bracket of the two basic derivations vanishes: `⁅δ₁, δ₂⁆ = 0`. -/
@[simp]
theorem lie_derivation₁_derivation₂ : ⁅derivation₁ θ, derivation₂ θ⁆ = 0 :=
  lie_gaugeDerivation _ _

/-! ### The odd cocycles `τ (a₀ δ_j(a₁))` -/

variable (θ) in
/-- The cyclic `1`-cocycle `ψ₁ (a₀, a₁) = τ (a₀ δ₁(a₁))` of `𝒜_θ`. -/
def oddCocycle₁ : cyclicCocycles ℂ (SmoothNoncommutativeTorus θ) ℂ 1 :=
  traceDerivationCocycle trace_mul_comm trace_derivation₁

variable (θ) in
/-- The cyclic `1`-cocycle `ψ₂ (a₀, a₁) = τ (a₀ δ₂(a₁))` of `𝒜_θ`. -/
def oddCocycle₂ : cyclicCocycles ℂ (SmoothNoncommutativeTorus θ) ℂ 1 :=
  traceDerivationCocycle trace_mul_comm trace_derivation₂

@[simp]
theorem coe_oddCocycle₁ :
    ((oddCocycle₁ θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 1) :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) =
      traceDerivationCochain (trace θ) (derivation₁ θ) :=
  coe_traceDerivationCocycle _ _

@[simp]
theorem coe_oddCocycle₂ :
    ((oddCocycle₂ θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 1) :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) =
      traceDerivationCochain (trace θ) (derivation₂ θ) :=
  coe_traceDerivationCocycle _ _

/-- `ψ₁ (a₀, U₁) = 2πi τ (a₀ U₁)`. -/
theorem oddCocycle₁_apply_U₁ (a₀ : SmoothNoncommutativeTorus θ) :
    ((oddCocycle₁ θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 1) :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) ![a₀, U₁ θ] =
      2 * π * I * trace θ (a₀ * U₁ θ) := by
  rw [coe_oddCocycle₁, traceDerivationCochain_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, derivation₁_U₁, mul_smul_comm, map_smul,
    smul_eq_mul]

/-- `ψ₁ (a₀, U₂) = 0`. -/
theorem oddCocycle₁_apply_U₂ (a₀ : SmoothNoncommutativeTorus θ) :
    ((oddCocycle₁ θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 1) :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) ![a₀, U₂ θ] = 0 := by
  simp

/-- `ψ₂ (a₀, U₁) = 0`. -/
theorem oddCocycle₂_apply_U₁ (a₀ : SmoothNoncommutativeTorus θ) :
    ((oddCocycle₂ θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 1) :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) ![a₀, U₁ θ] = 0 := by
  simp

/-- `ψ₂ (a₀, U₂) = 2πi τ (a₀ U₂)`. -/
theorem oddCocycle₂_apply_U₂ (a₀ : SmoothNoncommutativeTorus θ) :
    ((oddCocycle₂ θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 1) :
      MultilinearMap ℂ (fun _ : Fin 2 ↦ SmoothNoncommutativeTorus θ) ℂ) ![a₀, U₂ θ] =
      2 * π * I * trace θ (a₀ * U₂ θ) := by
  rw [coe_oddCocycle₂, traceDerivationCochain_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, derivation₂_U₂, mul_smul_comm, map_smul,
    smul_eq_mul]

/-! ### The fundamental cocycle -/

variable (θ) in
/-- The **fundamental cyclic `2`-cocycle** of `𝒜_θ`,
`φ (a₀, a₁, a₂) = (2πi)⁻¹ τ (a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`, built from the canonical
trace and the two basic derivations. -/
def fundamentalCocycle : cyclicCocycles ℂ (SmoothNoncommutativeTorus θ) ℂ 2 :=
  (2 * π * I)⁻¹ • traceDerivationPairCocycle trace_mul_comm trace_derivation₁ trace_derivation₂
    commute_derivation₁_derivation₂

/-- The defining formula
`φ (a₀, a₁, a₂) = (2πi)⁻¹ τ (a₀ (δ₁(a₁) δ₂(a₂) - δ₂(a₁) δ₁(a₂)))`. -/
@[simp]
theorem fundamentalCocycle_apply (a : Fin 3 → SmoothNoncommutativeTorus θ) :
    ((fundamentalCocycle θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 2) :
      MultilinearMap ℂ (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ) a =
      (2 * π * I)⁻¹ * trace θ (a 0 *
        ((derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (a 1) *
            (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (a 2) -
          (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (a 1) *
            (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (a 2))) := by
  simp [fundamentalCocycle]

/-- On monomials, `φ (c₀ U^x, c₁ U^y, c₂ U^z) = 2πi (y₁ z₂ - y₂ z₁) τ (c₀ U^x c₁ U^y c₂ U^z)`. -/
theorem fundamentalCocycle_apply_single (x y z : ℤ × ℤ) (c₀ c₁ c₂ : ℂ) :
    ((fundamentalCocycle θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 2) :
      MultilinearMap ℂ (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ)
        ![single x c₀, single y c₁, single z c₂] =
      2 * π * I * (y.1 * z.2 - y.2 * z.1) *
        trace θ (single x c₀ * single y c₁ * single z c₂) := by
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero, I_ne_zero]
  -- write the derivatives of the monomials as scalar multiples of the monomials
  have h₁ (w : ℤ × ℤ) (c : ℂ) :
      (derivation₁ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (single w c) =
        (2 * π * I * w.1) • single w c := by
    rw [derivation₁_single, smul_single]
  have h₂ (w : ℤ × ℤ) (c : ℂ) :
      (derivation₂ θ : Module.End ℂ (SmoothNoncommutativeTorus θ)) (single w c) =
        (2 * π * I * w.2) • single w c := by
    rw [derivation₂_single, smul_single]
  simp only [fundamentalCocycle_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, h₁, h₂, smul_mul_assoc,
    mul_smul_comm, smul_smul, ← sub_smul, map_smul, smul_eq_mul, mul_assoc]
  field_simp

/-- The normalization of the fundamental cocycle: `φ (star (U₁ U₂), U₁, U₂) = 2πi`. -/
theorem fundamentalCocycle_apply_star_U₁_mul_U₂ :
    ((fundamentalCocycle θ : cyclicCochains ℂ (SmoothNoncommutativeTorus θ) ℂ 2) :
      MultilinearMap ℂ (fun _ : Fin 3 ↦ SmoothNoncommutativeTorus θ) ℂ)
        ![star ((U₁ θ : SmoothNoncommutativeTorus θ) * U₂ θ), U₁ θ, U₂ θ] = 2 * π * I := by
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero, I_ne_zero]
  have hu : star ((U₁ θ : SmoothNoncommutativeTorus θ) * U₂ θ) * (U₁ θ * U₂ θ) = 1 :=
    Unitary.star_mul_self_of_mem (U₁ θ * U₂ θ).2
  simp only [fundamentalCocycle_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, derivation₁_U₁, derivation₁_U₂,
    derivation₂_U₁, derivation₂_U₂, mul_zero, sub_zero, smul_mul_assoc,
    mul_smul_comm, smul_smul, map_smul, smul_eq_mul, hu, trace_one]
  field_simp

end SmoothNoncommutativeTorus

end TauCeti
