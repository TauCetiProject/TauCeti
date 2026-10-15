/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Laurent
public import TauCeti.Analysis.Complex.UpperHalfPlane.QExpansion.Order

/-!
# Cusp orders from Laurent q-expansions

For a cusp-invariant function whose twisted q-extension is analytic at zero, the meromorphic
order of its q-extension is exactly the order of its Laurent q-expansion. Controlled exponential
growth of a function holomorphic sufficiently high ensures this analyticity. Both orders
are infinite for the zero germ. Thus vanishing of the coefficients below an integer characterizes
an order bound, and the first nonzero coefficient gives the exact order, for poles and zeros alike.

The comparison uses the q-expansion order comparison for the twisted q-extension and
Mathlib's Hahn-series order API. It connects the formal Laurent series to local
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
coefficient, with value `⊤` when all coefficients vanish, provided the twisted extension is
analytic at zero. It is independent of the valid integer twist used to construct the series. -/
theorem meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion
    (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) :
    meromorphicOrderAt (cuspExtension D f) 0 = (laurentQExpansion D k f).orderTop := by
  have hord : (twistedQExpansion D k f).order =
      analyticOrderAt (twistedExtension D k f) 0 := by
    rw [twistedQExpansion_def, twistedExtension_def, cuspExtension_def]
    rw [twistedExtension_def, cuspExtension_def] at han
    exact TauCeti.qExpansion_order_eq_analyticOrderAt_cuspFunction han
  rw [meromorphicOrderAt_cuspExtension_eq_neg_add_analyticOrderAt_twistedExtension D k f hf han,
    laurentQExpansion_def, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
    ← hord]
  congr 1
  cases ho : (twistedQExpansion D k f).order with
  | top =>
    have hzero := PowerSeries.order_eq_top.mp ho
    simp [hzero]
  | coe n =>
    obtain ⟨hnonzero, hvanish⟩ := PowerSeries.order_eq_nat.mp ho
    simp only [ENat.map_natCast]
    symm
    apply le_antisymm
    · exact HahnSeries.orderTop_le_of_coeff_ne_zero
        (by simpa only [LaurentSeries.coeff_coe_powerSeries] using hnonzero)
    · apply HahnSeries.le_orderTop_iff_forall.mpr
      intro j hj
      rw [PowerSeries.coeff_coe]
      split_ifs with hjneg
      · rfl
      · exact hvanish j.natAbs (by
          have := WithTop.coe_lt_coe.mp hj
          omega)

/-- A meromorphic cusp order is at least `m` exactly when every Laurent coefficient of exponent
less than `m` vanishes. The bound may be positive, zero, or negative. -/
theorem le_meromorphicOrderAt_cuspExtension_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) (m : ℤ) :
    (m : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 ↔
      ∀ j < m, (laurentQExpansion D k f).coeff j = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf han,
    HahnSeries.le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- The first nonzero Laurent coefficient gives the exact meromorphic cusp order. -/
theorem meromorphicOrderAt_cuspExtension_eq_int_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) (m : ℤ) :
    meromorphicOrderAt (cuspExtension D f) 0 = (m : WithTop ℤ) ↔
      (laurentQExpansion D k f).coeff m ≠ 0 ∧
        ∀ j < m, (laurentQExpansion D k f).coeff j = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf han]
  refine ⟨fun h ↦ ⟨HahnSeries.coeff_orderTop_ne h, ?_⟩, fun ⟨hm, hbelow⟩ ↦ ?_⟩
  · intro j hj
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop (h ▸ WithTop.coe_lt_coe.mpr hj)
  · exact le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hm)
      (HahnSeries.le_orderTop_iff_forall.mpr fun j hj ↦ hbelow j (WithTop.coe_lt_coe.mp hj))

/-- The Laurent q-expansion vanishes exactly when its meromorphic cusp germ has infinite order. -/
theorem meromorphicOrderAt_cuspExtension_eq_top_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) :
    meromorphicOrderAt (cuspExtension D f) 0 = ⊤ ↔ laurentQExpansion D k f = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf han,
    HahnSeries.orderTop_eq_top]

end TauCeti.Subgroup.CuspDatum
