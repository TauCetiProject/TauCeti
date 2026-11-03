/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import TauCeti.RingTheory.FormalGroup.Rescale

/-!
# The formal group of the cubic `y² + a₁xy = x³`

The Weierstrass cubics `y² + a₁xy = x³` form the line through the cusp `y² = x³` (`a₁ = 0`) and
the nodal cubic `y² + xy = x³` (`a₁ = 1`), which is the Tate curve at `q = 0`. This file computes
the formal group law `Ê` of every member of this family over every commutative ring: it is the
multiplicative formal group law rescaled by `-a₁`,

  `Ê(X, Y) = X + Y - a₁XY`

(`WeierstrassCurve.formalGroup_eq_rescale_𝔾ₘ`). Hence the formal group of the nodal cubic is
the multiplicative one: when `a₁` is a unit, `Ê` is the transport of `X + Y + XY` along the
homothety `T ↦ -a₁⁻¹T`, an isomorphism of formal group laws. At the cusp, `a₁ = 0`, it is the
additive formal group law. Over a field of characteristic `p`, the formal group has height `1`
when `a₁ ≠ 0` and height `⊤` at the cusp.

The computation uses that a formal group law over a `ℚ`-algebra is determined by its invariant
differential (`FormalGroup.invariantDifferential_injective`). For `y² + a₁xy = x³` the expansion
of `ω = dx / (2y + a₁x + a₃)` in the coordinate `z = -x / y` is `dz / (1 - a₁z)`
(`WeierstrassCurve.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom`),
which is the invariant differential of `X + Y - a₁XY`. Since the family is defined over `ℤ[a₁]`,
which embeds in the `ℚ`-algebra `ℚ[a₁]`, this identifies the two formal group laws over `ℤ[a₁]`,
and then over every ring by base change.

## Main results

* `WeierstrassCurve.formalGroup_eq_rescale_𝔾ₘ`: the formal group law of `y² + a₁xy = x³` is
  `X + Y - a₁XY`, the rescaling of `X + Y + XY` by `-a₁`.
* `WeierstrassCurve.formalGroup_eq_homothety_smul_𝔾ₘ`: when `a₁ = u` is a unit, it is the
  transport of the multiplicative formal group law along `T ↦ -u⁻¹T`.
* `WeierstrassCurve.formalGroup_eq_𝔾ₐ`: the formal group law of the cusp `y² = x³` is additive.
* `WeierstrassCurve.height_formalGroup_eq_one` and `WeierstrassCurve.height_formalGroup_eq_top`:
  over a field of characteristic `p`, the height is `1` when `a₁ ≠ 0` and `⊤` when `a₁ = 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.4–IV.5 and IV.7.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

open MvPowerSeries FormalGroup TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}

/-- Over a `ℚ`-algebra, the formal group law of `y² + a₁xy = x³` is `X + Y - a₁XY`: both have
invariant differential `dT / (1 - a₁T)`. -/
private theorem formalGroup_eq_rescale_𝔾ₘ_of_algebra [Algebra ℚ R] (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    formalGroup W = (𝔾ₘ : FormalGroup R).rescale (-W.a₁) := by
  refine invariantDifferential_injective (left_inv_eq_right_inv
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom ?_)
  -- Rescaling `(1 - T + T² - ⋯) (1 + T) = 1` by `-a₁` inverts `1 - a₁T`.
  have h := congrArg (PowerSeries.rescale (-W.a₁))
    (PowerSeries.mk_neg_one_pow_mul_one_add_eq_one (S := R))
  rw [map_mul, map_one, ← invariantDifferential_𝔾ₘ, ← invariantDifferential_rescale, map_add,
    map_one, PowerSeries.rescale_X, mul_comm] at h
  convert h using 2
  simp [formalInvariantDifferentialDenom_def, h₂, h₃, h₄, h₆, PowerSeries.smul_eq_C_mul,
    sub_eq_add_neg]

/-- **The formal group of `y² + a₁xy = x³`** is the rescaling by `-a₁` of the multiplicative
formal group law, that is `Ê(X, Y) = X + Y - a₁XY` (`FormalGroup.rescale_𝔾ₘ_toPowerSeries`). -/
theorem formalGroup_eq_rescale_𝔾ₘ (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0)
    (h₆ : W.a₆ = 0) : formalGroup W = (𝔾ₘ : FormalGroup R).rescale (-W.a₁) := by
  -- `W` specializes the curve `U : y² + axy = x³` over `ℤ[a]`, and the identity for `U` follows
  -- from the one over the `ℚ`-algebra `ℚ[a]`, into which `ℤ[a]` embeds.
  let U : WeierstrassCurve (Polynomial ℤ) := ⟨Polynomial.X, 0, 0, 0, 0⟩
  let ι : Polynomial ℤ →+* Polynomial ℚ := Polynomial.mapRingHom (Int.castRingHom ℚ)
  have hU : formalGroup U = (𝔾ₘ : FormalGroup _).rescale (-Polynomial.X) := by
    refine FormalGroup.map_injective (f := ι) (Polynomial.map_injective _ Int.cast_injective) ?_
    simp only [← map_formalGroup, map_rescale, map_𝔾ₘ]
    convert formalGroup_eq_rescale_𝔾ₘ_of_algebra (W := U.map ι) _ _ _ _ <;> simp [U, ι]
  let φ := Polynomial.eval₂RingHom (Int.castRingHom R) W.a₁
  have hW : U.map φ = W := by
    ext <;> simp [U, φ, h₂, h₃, h₄, h₆]
  calc formalGroup W = (formalGroup U).map φ := by rw [← map_formalGroup, hW]
    _ = _ := by simp [hU, map_rescale, φ]

/-- **The formal group of the nodal cubic is multiplicative**: if `a₁ = u` is a unit, the formal
group law of `y² + a₁xy = x³` is the transport of `X + Y + XY` along the homothety `T ↦ -u⁻¹T`;
so `FormalGroup.smulIso` makes this homothety an isomorphism from the multiplicative formal group
law to `Ê`. -/
theorem formalGroup_eq_homothety_smul_𝔾ₘ (u : Rˣ) (h₁ : W.a₁ = u) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    formalGroup W = FormalCoordinate.homothety (-u)⁻¹ • (𝔾ₘ : FormalGroup R) := by
  rw [homothety_smul, inv_inv, formalGroup_eq_rescale_𝔾ₘ h₂ h₃ h₄ h₆, h₁, Units.val_neg]

/-- The formal group law of the cusp `y² = x³` is the additive formal group law. -/
theorem formalGroup_eq_𝔾ₐ (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0)
    (h₆ : W.a₆ = 0) : formalGroup W = 𝔾ₐ := by
  refine FormalGroup.ext ?_
  rw [formalGroup_eq_rescale_𝔾ₘ h₂ h₃ h₄ h₆]
  simp [h₁, 𝔾ₐ_toPowerSeries]

section Height

variable {K : Type*} [Field K] {p : ℕ} [CharP K p] {W : WeierstrassCurve K}

/-- Over a field of characteristic `p`, the formal group of the nodal cubic `y² + a₁xy = x³`,
`a₁ ≠ 0`, has height `1`. -/
theorem height_formalGroup_eq_one [Fact p.Prime] (h₁ : W.a₁ ≠ 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) : (formalGroup W).height p = 1 := by
  rw [formalGroup_eq_homothety_smul_𝔾ₘ (Units.mk0 _ h₁) rfl h₂ h₃ h₄ h₆, height_smul, height_𝔾ₘ]

/-- Over a field of characteristic `p`, the formal group of the cusp `y² = x³` has height `⊤`. -/
theorem height_formalGroup_eq_top (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) : (formalGroup W).height p = ⊤ := by
  rw [formalGroup_eq_𝔾ₐ h₁ h₂ h₃ h₄ h₆, height_𝔾ₐ]

end Height

end WeierstrassCurve
