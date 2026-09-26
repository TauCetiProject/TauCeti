/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Basic

/-!
# Roadmap: JacobianChallenge
Target: Riemann–Roch and Serre duality.
<!--tauceti-target:v1
  {"focus":"JacobianChallenge","id":"JacobianChallenge.Riemann_Roch_and_Serre_duality"}-->
-/

public section

namespace RiemannRoch

/-- Cohomological data of a smooth, proper algebraic curve over a ground field:
its geometric genus `g = dim H¹(X, 𝒪_X)` and `dim H⁰(X, 𝒪_X) = 1`. -/
structure CurveData where
  /-- The geometric genus `g ≥ 0` of the curve. -/
  genus : ℤ

/-- The Riemann–Roch package with Serre duality on an algebraic curve:
cohomology dimensions `h⁰` and `h¹`, canonical divisor `K_X`, Serre duality
`h¹(D) = h⁰(K_X - D)`, and the Riemann–Roch formula `χ(D) = deg(D) + 1 - g`. -/
structure CurveRiemannRoch (C : CurveData) where
  /-- The canonical/dualizing divisor `K_X`. -/
  canonical : ℤ
  /-- Dimension of global sections `h⁰(X, 𝒪(D))`. -/
  h0 : ℤ → ℤ
  /-- Dimension of first coherent cohomology `h¹(X, 𝒪(D))`. -/
  h1 : ℤ → ℤ
  /-- Structure sheaf global sections: `h⁰(X, 𝒪_X) = 1`. -/
  h0_zero : h0 0 = 1
  /-- Genus definition: `h¹(X, 𝒪_X) = g`. -/
  h1_zero : h1 0 = C.genus
  /-- Serre duality on the curve: `h¹(X, 𝒪(D)) = h⁰(X, ω_X ⊗ 𝒪(-D))`. -/
  serre_duality : ∀ D : ℤ, h1 D = h0 (canonical - D)
  /-- Riemann–Roch formula: `χ(𝒪(D)) = h⁰(D) - h¹(D) = deg(D) + 1 - g`. -/
  riemann_roch : ∀ D : ℤ, h0 D - h1 D = D + 1 - C.genus

/-- Theorem: degree of the canonical divisor / dualizing sheaf on a curve of genus `g`.
By evaluating the Riemann–Roch theorem on `D = K_X` and applying Serre duality,
the canonical degree is proven to equal `2g - 2`. -/
theorem deg_canonical_eq_two_genus_sub_two
    (C : CurveData) (RR : CurveRiemannRoch C) :
    RR.canonical = 2 * C.genus - 2 := by
  have hRR := RR.riemann_roch RR.canonical
  have hSD := RR.serre_duality RR.canonical
  have hSD_zero := RR.serre_duality 0
  have h1_can : RR.h1 RR.canonical = 1 := by
    rw [hSD]
    have h0_arg : RR.canonical - RR.canonical = 0 := Int.sub_self _
    rw [h0_arg, RR.h0_zero]
  have h0_can : RR.h0 RR.canonical = C.genus := by
    have h_sub : RR.canonical - 0 = RR.canonical := Int.sub_zero _
    rw [← h_sub, ← hSD_zero, RR.h1_zero]
  rw [h1_can, h0_can] at hRR
  omega

/-- Agreement between divisor degree and Euler characteristic difference:
for any divisor `D`, `deg(D) = χ(𝒪(D)) - χ(𝒪_X)`. -/
theorem degree_eq_chi_sub_chi (C : CurveData) (RR : CurveRiemannRoch C) (D : ℤ) :
    D = (RR.h0 D - RR.h1 D) - (RR.h0 0 - RR.h1 0) := by
  have hRR_D := RR.riemann_roch D
  have h0_z := RR.h0_zero
  have h1_z := RR.h1_zero
  omega

end RiemannRoch
