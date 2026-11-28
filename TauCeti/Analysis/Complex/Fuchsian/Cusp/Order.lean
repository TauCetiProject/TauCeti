/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Laurent
public import TauCeti.Analysis.Complex.UpperHalfPlane.QExpansion.Order
import TauCeti.Analysis.Meromorphic.LaurentSeries

/-!
# Cusp orders from Laurent q-expansions

For a function whose twisted q-extension is analytic at zero, the meromorphic
order of its q-extension is exactly the order of its Laurent q-expansion. Controlled exponential
growth of a function holomorphic sufficiently high ensures this analyticity. Both orders
are infinite for the zero germ. Thus vanishing of the coefficients below an integer characterizes
an order bound, and the first nonzero coefficient gives the exact order, for poles and zeros alike.

The comparison identifies the Laurent q-expansion with the formal expansion of the
meromorphic cusp germ and uses the order comparison for meromorphic germs.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Asymptotics Filter MulAction UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

open meromorphicGerms

/-- The meromorphic order of the cusp extension is the least exponent with a nonzero Laurent
coefficient, with value `⊤` when all coefficients vanish, provided the twisted extension is
analytic at zero. It is independent of the valid integer twist used to construct the series. -/
theorem meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion
    (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) :
    meromorphicOrderAt (cuspExtension D f) 0 = (laurentQExpansion D k f).orderTop := by
  have hshift := cuspExtension_eventuallyEq_zpow_mul_twistedExtension D k f
  have hf : MeromorphicAt (cuspExtension D f) 0 :=
    (((MeromorphicAt.id 0).zpow (-k)).mul han.meromorphicAt).congr hshift.symm
  have hrep : mk (cuspExtension D f) hf =
      meromorphicGerms.coordinate 0 ^ (-k) * mk (twistedExtension D k f) han.meromorphicAt := by
    rw [coordinate_zpow_eq_mk, ← mk_mul, mk_eq_mk_iff]
    exact hshift.mono fun q hq ↦ by simpa only [Pi.mul_apply, sub_zero] using hq
  have hTaylor : twistedQExpansion D k f = taylorSeries (twistedExtension D k f) 0 := by
    ext n
    rw [twistedQExpansion_coeff, ← han.factorial_smul_coeff_taylorSeries, nsmul_eq_mul,
      inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]
  have hexp : laurentSeries 0 (mk (cuspExtension D f) hf) = laurentQExpansion D k f := by
    rw [hrep, map_mul, map_zpow₀, laurentSeries_coordinate, ← RatFunc.single_zpow,
      laurentSeries_mk_of_analyticAt han, laurentQExpansion_def, hTaylor]
  rw [← hexp, orderTop_laurentSeries, order_mk]

/-- A meromorphic cusp order is at least `m` exactly when every Laurent coefficient of exponent
less than `m` vanishes. The bound may be positive, zero, or negative. -/
theorem le_meromorphicOrderAt_cuspExtension_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) (m : ℤ) :
    (m : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 ↔
      ∀ j < m, (laurentQExpansion D k f).coeff j = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f han,
    HahnSeries.le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- The first nonzero Laurent coefficient gives the exact meromorphic cusp order. -/
theorem meromorphicOrderAt_cuspExtension_eq_int_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) (m : ℤ) :
    meromorphicOrderAt (cuspExtension D f) 0 = (m : WithTop ℤ) ↔
      (laurentQExpansion D k f).coeff m ≠ 0 ∧
        ∀ j < m, (laurentQExpansion D k f).coeff j = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f han]
  refine ⟨fun h ↦ ⟨HahnSeries.coeff_orderTop_ne h, ?_⟩, fun ⟨hm, hbelow⟩ ↦ ?_⟩
  · intro j hj
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop (h ▸ WithTop.coe_lt_coe.mpr hj)
  · exact le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hm)
      (HahnSeries.le_orderTop_iff_forall.mpr fun j hj ↦ hbelow j (WithTop.coe_lt_coe.mp hj))

/-- The Laurent q-expansion vanishes exactly when its meromorphic cusp germ has infinite order. -/
theorem meromorphicOrderAt_cuspExtension_eq_top_iff (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (han : AnalyticAt ℂ (twistedExtension D k f) 0) :
    meromorphicOrderAt (cuspExtension D f) 0 = ⊤ ↔ laurentQExpansion D k f = 0 := by
  rw [meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f han,
    HahnSeries.orderTop_eq_top]

end TauCeti.Subgroup.CuspDatum
