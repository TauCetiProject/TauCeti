/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# Algebra maps out of `A⟦X⟧` killing a distinguished polynomial

Let `A` be complete for an ideal `I` and let `g` be a polynomial distinguished at `I`. Mathlib's
Weierstrass division writes every power series `F ∈ A⟦X⟧` as `F = g * q + r` with `r` a
polynomial. An `A`-algebra map out of `A⟦X⟧` that kills `g` therefore sends `F` to the value of
`r` at the image of `X`, so it is determined by the image of `X`. No continuity is assumed. This
is how the level coordinates of the Iwasawa algebra are characterised by the image of `T`.

## Main results

* `Polynomial.IsDistinguishedAt.algHom_ext`: two `A`-algebra maps `A⟦X⟧ → B` that agree on `X`
  and kill a polynomial distinguished at `I` are equal.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Proposition 7.2.
-/

public section

open PowerSeries

namespace Polynomial.IsDistinguishedAt

variable {A B : Type*} [CommRing A] [Semiring B] [Algebra A B] {g : A[X]} {I : Ideal A}

/-- **`A`-algebra maps out of `A⟦X⟧` killing a distinguished polynomial are determined by the
image of `X`.** Let `A` be `I`-adically complete and `g` distinguished at `I`. If two `A`-algebra
maps `A⟦X⟧ → B` agree on `X` and one of them kills `g`, they are equal. No continuity is
assumed: Weierstrass division writes every series as a multiple of `g` plus a polynomial. -/
theorem algHom_ext (H : g.IsDistinguishedAt I) [IsAdicComplete I A] {φ ψ : A⟦X⟧ →ₐ[A] B}
    (hg : φ (g : A⟦X⟧) = 0) (hX : φ PowerSeries.X = ψ PowerSeries.X) : φ = ψ := by
  have hg' : ψ (g : A⟦X⟧) = 0 := by
    rwa [PowerSeries.algHom_coe_eq_aeval, ← hX, ← PowerSeries.algHom_coe_eq_aeval]
  refine AlgHom.ext fun F ↦ ?_
  -- Weierstrass division: `F = g * q + r` with `r` a polynomial.
  obtain ⟨-, hF⟩ := H.isWeierstrassDivisorAt'.isWeierstrassDivisionAt_div_mod F
  rw [hF]
  simp only [map_add, map_mul, hg, hg', zero_mul, zero_add, PowerSeries.algHom_coe_eq_aeval, hX]

end Polynomial.IsDistinguishedAt
