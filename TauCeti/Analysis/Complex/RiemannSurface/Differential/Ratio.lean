/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic

/-!
# The ratio of two `1`-forms on a Riemann surface

Two `1`-forms `η` and `ω` on a Riemann surface have, at every point, coefficients in a chart whose
ratio does not depend on the chart: changing chart multiplies both coefficients by the same
nonzero derivative of the transition map. This ratio is the function `η / ω`
(`TauCeti.RiemannSurface.OneForm.ratio`). Where `ω` does not vanish it is the unique scalar `c`
with `η = c ω` (`TauCeti.RiemannSurface.OneForm.ratio_eq_iff`). It is meromorphic where `η` and
`ω` are, and at a point where `ω` has finite order its order is `ord_x η - ord_x ω`
(`TauCeti.RiemannSurface.OneForm.meromorphicOrderAt_ratio_add_order`). The finite-order hypothesis
is needed: if `ω` vanishes near `x`, the ratio is `0` near `x`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (local expressions of differential forms) and §17 (quotients of meromorphic `1`-forms).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {ω η : OneForm X} {x : X}
  {e : OpenPartialHomeomorph X ℂ}

/-- The **ratio** `η / ω` of two `1`-forms: at each point, the quotient of their coefficients in
the preferred chart there. It does not depend on the chart
(`TauCeti.RiemannSurface.OneForm.ratio_eq_of_mem_maximalAtlas`), and `η = (η / ω) ω` wherever `ω`
does not vanish. -/
def ratio (η ω : OneForm X) (x : X) : ℂ :=
  η.coeff (chartAt ℂ x) (chartAt ℂ x x) / ω.coeff (chartAt ℂ x) (chartAt ℂ x x)

theorem ratio_def (η ω : OneForm X) (x : X) :
    ratio η ω x = η.coeff (chartAt ℂ x) (chartAt ℂ x x) / ω.coeff (chartAt ℂ x) (chartAt ℂ x x) :=
  (rfl)

variable [IsManifold 𝓘(ℂ) 1 X]

/-- **Chart independence of the ratio.** The ratio of two `1`-forms at `y` is the quotient of their
coefficients in any chart of the maximal atlas at `y`. -/
theorem ratio_eq_of_mem_maximalAtlas (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) {y : X}
    (hy : y ∈ e.source) : ratio η ω y = η.coeff e (e y) / ω.coeff e (e y) := by
  have hcy := mem_chart_source ℂ y
  rw [ratio_def, coeff_eq_coeff_mul_deriv η he (chart_mem_maximalAtlas y) hy hcy,
    coeff_eq_coeff_mul_deriv ω he (chart_mem_maximalAtlas y) hy hcy,
    mul_div_mul_right _ _ (TauCeti.deriv_symm_trans_ne_zero (chart_mem_maximalAtlas y) he hcy hy)]

/-- Read in the chart at `x`, the ratio is the quotient of the coefficients near `x`. -/
theorem ratio_comp_chartAt_symm_eventuallyEq :
    ratio η ω ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)]
      η.coeff (chartAt ℂ x) / ω.coeff (chartAt ℂ x) := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with z hz
  rw [comp_apply, ratio_eq_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    ((chartAt ℂ x).map_target hz), (chartAt ℂ x).right_inv hz, Pi.div_apply]

/-- The ratio of two meromorphic `1`-forms is a meromorphic function. -/
theorem meromorphicAt_ratio (hη : η.MeromorphicAt x) (hω : ω.MeromorphicAt x) :
    RiemannSurface.MeromorphicAt (ratio η ω) x := by
  rw [RiemannSurface.meromorphicAt_def]
  exact (((meromorphicAt_def η x).1 hη).div ((meromorphicAt_def ω x).1 hω)).congr
    (ratio_comp_chartAt_symm_eventuallyEq.symm.filter_mono nhdsWithin_le_nhds)

/-- **`ord_x (η / ω) + ord_x ω = ord_x η`** for meromorphic `1`-forms, with `ω` of finite order at
`x`. -/
theorem meromorphicOrderAt_ratio_add_order (hη : η.MeromorphicAt x) (hω : ω.MeromorphicAt x)
    (hω₀ : ω.order x ≠ ⊤) :
    RiemannSurface.meromorphicOrderAt (ratio η ω) x + ω.order x = η.order x := by
  rw [RiemannSurface.meromorphicOrderAt_def, _root_.meromorphicOrderAt_congr
    (ratio_comp_chartAt_symm_eventuallyEq.filter_mono nhdsWithin_le_nhds),
    _root_.meromorphicOrderAt_div ((meromorphicAt_def η x).1 hη) ((meromorphicAt_def ω x).1 hω),
    ← order_def, ← order_def]
  generalize η.order x = a at *
  lift ω.order x to ℤ using hω₀ with b
  cases a with
  | top => simp
  | coe a => norm_cast; simp

/-- Where `ω` does not vanish, its coefficient in the chart at `x` does not vanish. -/
private theorem coeff_chartAt_ne_zero (hω : ω x ≠ 0) :
    ω.coeff (chartAt ℂ x) (chartAt ℂ x x) ≠ 0 := by
  intro h0
  apply hω
  rw [← (coeff_eq_iff ω (chart_mem_maximalAtlas x) (mem_chart_source ℂ x)).1 rfl, h0, zero_smul]

/-- **The ratio is the unique scalar with `η = c ω`.** Where `ω` does not vanish, `η / ω` is the
unique `c` with `c ω = η` at `x`. -/
theorem ratio_eq_iff (hω : ω x ≠ 0) {c : ℂ} : ratio η ω x = c ↔ c • ω x = η x := by
  have hcx := mem_chart_source ℂ x
  have hη := (coeff_eq_iff η (chart_mem_maximalAtlas x) hcx).1 rfl
  have hω' := (coeff_eq_iff ω (chart_mem_maximalAtlas x) hcx).1 rfl
  rw [ratio_def, div_eq_iff (coeff_chartAt_ne_zero hω), ← hη, ← hω', smul_smul]
  exact ⟨fun h ↦ by rw [h], fun h ↦ smul_left_injective ℂ
    (mvfderiv_ne_zero (chart_mem_maximalAtlas x) hcx) h.symm⟩

/-- **`η = (η / ω) ω`** at a point where `ω` does not vanish. -/
theorem ratio_smul (hω : ω x ≠ 0) : ratio η ω x • ω x = η x :=
  (ratio_eq_iff hω).1 rfl

/-- The ratio of `f ω` to `ω` is `f`, at a point where `ω` does not vanish. -/
@[simp]
theorem ratio_smul_left (f : X → ℂ) (hω : ω x ≠ 0) : ratio (f • ω) ω x = f x :=
  (ratio_eq_iff hω).2 rfl

/-- The ratio of `c ω` to `ω` is `c`, at a point where `ω` does not vanish. -/
@[simp]
theorem ratio_const_smul_left (c : ℂ) (hω : ω x ≠ 0) : ratio (c • ω) ω x = c :=
  (ratio_eq_iff hω).2 rfl

/-- The ratio of `ω` to itself is `1` where `ω` does not vanish. -/
@[simp]
theorem ratio_self (hω : ω x ≠ 0) : ratio ω ω x = 1 :=
  (ratio_eq_iff hω).2 (one_smul ℂ (ω x))

end TauCeti.RiemannSurface.OneForm
