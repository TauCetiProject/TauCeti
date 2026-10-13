/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Laurent

/-!
# Cusp orders from Laurent q-expansions

For a cusp-invariant holomorphic function with controlled exponential growth, the meromorphic
order of its q-extension is exactly the order of its convergent Laurent q-expansion. Both orders
are infinite for the zero germ. Thus vanishing of the coefficients below an integer characterizes
an order bound, and the first nonzero coefficient gives the exact order, for poles and zeros alike.

The comparison uses Mathlib's derivative characterization of analytic order and the existing
Taylor coefficients of the twisted q-extension. It connects the formal Laurent series to local
orders of descended meromorphic functions, rather than defining another notion of cusp order.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Asymptotics Filter MulAction UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- The meromorphic order of the cusp extension is the least exponent with a nonzero Laurent
coefficient, with value `⊤` when all coefficients vanish. It is independent of the growth bound
used to construct the Laurent series. -/
theorem meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion
    (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    meromorphicOrderAt (cuspExtension D f) 0 = (laurentQExpansion D k f).orderTop := by
  have han := analyticAt_twistedExtension_zero D k f hf hhol hbound
  rw [meromorphicOrderAt_cuspExtension_eq_neg_add D k f hf hhol hbound]
  cases ho : analyticOrderAt (twistedExtension D k f) 0 with
  | top =>
    have hzero : laurentQExpansion D k f = 0 := by
      apply HahnSeries.ext
      funext j
      by_cases hj : j < -k
      · simp [laurentQExpansion_coeff_eq_zero_of_lt_neg D k f hj]
      · have hderiv : iteratedDeriv (j + k).toNat (twistedExtension D k f) 0 = 0 :=
          (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp
            (ho ▸ le_top (a := (((j + k).toNat + 1 : ℕ) : ℕ∞))) _ (Nat.lt_succ_self _)
        simp [laurentQExpansion_coeff, show 0 ≤ j + k by omega,
          twistedQExpansion_coeff, hderiv]
    simp [hzero]
  | coe n =>
    obtain ⟨hvanish, hnonzero⟩ := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp ho
    have hcoeff : (laurentQExpansion D k f).coeff ((n : ℤ) - k) ≠ 0 := by
      rw [laurentQExpansion_coeff_natCast_sub]
      simpa [twistedQExpansion_coeff, Nat.factorial_ne_zero] using hnonzero
    have hlower : ∀ j : ℤ, j < (n : ℤ) - k → (laurentQExpansion D k f).coeff j = 0 := by
      intro j hj
      by_cases hjk : j < -k
      · exact laurentQExpansion_coeff_eq_zero_of_lt_neg D k f hjk
      · rw [laurentQExpansion_coeff, ite_eq_left (by omega)]
        simpa [twistedQExpansion_coeff, Nat.factorial_ne_zero] using
          hvanish (j + k).toNat (by omega)
    have hord : (laurentQExpansion D k f).orderTop = ((n : ℤ) - k : ℤ) :=
      le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hcoeff)
        (HahnSeries.le_orderTop_iff_forall.mpr fun j hj ↦
          hlower j (WithTop.coe_lt_coe.mp hj))
    rw [hord]
    simp [sub_eq_add_neg, add_comm]

/-- A meromorphic cusp order is at least `m` exactly when every Laurent coefficient of exponent
less than `m` vanishes. The bound may be positive, zero, or negative. -/
theorem le_meromorphicOrderAt_cuspExtension_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) (m : ℤ) :
    (m : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 ↔
      ∀ j < m, (laurentQExpansion D k f).coeff j = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf hhol hbound,
    HahnSeries.le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- The first nonzero Laurent coefficient gives the exact meromorphic cusp order. -/
theorem meromorphicOrderAt_cuspExtension_eq_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) (m : ℤ) :
    meromorphicOrderAt (cuspExtension D f) 0 = (m : WithTop ℤ) ↔
      (laurentQExpansion D k f).coeff m ≠ 0 ∧
        ∀ j < m, (laurentQExpansion D k f).coeff j = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf hhol hbound]
  refine ⟨fun h ↦ ⟨HahnSeries.coeff_orderTop_ne h, ?_⟩, fun ⟨hm, hbelow⟩ ↦ ?_⟩
  · intro j hj
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop (h ▸ WithTop.coe_lt_coe.mpr hj)
  · exact le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hm)
      (HahnSeries.le_orderTop_iff_forall.mpr fun j hj ↦ hbelow j (WithTop.coe_lt_coe.mp hj))

/-- The Laurent q-expansion vanishes exactly when its meromorphic cusp germ has infinite order. -/
theorem meromorphicOrderAt_cuspExtension_eq_top_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    meromorphicOrderAt (cuspExtension D f) 0 = ⊤ ↔ laurentQExpansion D k f = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf hhol hbound,
    HahnSeries.orderTop_eq_top]

end TauCeti.Subgroup.CuspDatum
