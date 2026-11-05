/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Divisor

/-!
# Canonical divisors of a compact Riemann surface

Two `1`-forms `η` and `ω` on a Riemann surface have, at every point, coefficients in a chart whose
ratio does not depend on the chart: changing chart multiplies both coefficients by the same
nonzero derivative of the transition map. This ratio is the function `η / ω`
(`TauCeti.RiemannSurface.OneForm.ratio`), meromorphic where `η` and `ω` are, and of order
`ord_x η - ord_x ω` (`TauCeti.RiemannSurface.OneForm.meromorphicOrderAt_ratio_add_order`).

On a compact connected Riemann surface it follows that any two `1`-forms which are meromorphic and
of finite order everywhere differ by a nonzero meromorphic function, so their divisors differ by
the principal divisor of that function and are linearly equivalent
(`TauCeti.RiemannSurface.OneForm.linearlyEquivalent_divisor`). A **canonical divisor**
(`TauCeti.RiemannSurface.IsCanonicalDivisor`) is the divisor of such a `1`-form. The canonical
divisors form exactly one linear equivalence class: any two are linearly equivalent, and a divisor
linearly equivalent to a canonical divisor `div ω` is canonical, being the divisor of `f ω` for a
meromorphic function `f` (`TauCeti.RiemannSurface.IsCanonicalDivisor.isCanonicalDivisor_iff`).
That a canonical divisor exists, i.e. that a nonzero meromorphic `1`-form exists, is not proved
here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the divisor of a meromorphic `1`-form and the canonical divisor class).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter V §1 (canonical divisors).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry WeilDivisor

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace OneForm

variable {ω η : OneForm X} {x : X} {e : OpenPartialHomeomorph X ℂ}

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

section Connected

variable [ConnectedSpace X]

/-- The ratio `η / ω` of two `1`-forms meromorphic everywhere, as a meromorphic function. -/
def ratioFunction (η ω : OneForm X) (hη : ∀ x, η.MeromorphicAt x) (hω : ∀ x, ω.MeromorphicAt x) :
    MeromorphicFunction X :=
  MeromorphicFunction.ofMeromorphic fun x ↦ meromorphicAt_ratio (hη x) (hω x)

variable (hη : ∀ x, η.MeromorphicAt x) (hω : ∀ x, ω.MeromorphicAt x)
  (hω₀ : ∀ x, ω.order x ≠ ⊤)
include hη hω hω₀

/-- **`ord_x (η / ω) + ord_x ω = ord_x η`** for the ratio as a meromorphic function. -/
theorem order_ratioFunction_add_order (x : X) :
    MeromorphicFunction.order x (ratioFunction η ω hη hω) + ω.order x = η.order x := by
  rw [ratioFunction, MeromorphicFunction.order_apply, RiemannSurface.meromorphicOrderAt_congr
    (MeromorphicFunction.finitePart_ofMeromorphic_eventuallyEq _ x)]
  exact meromorphicOrderAt_ratio_add_order (hη x) (hω x) (hω₀ x)

omit hω₀ in
/-- If `η` has finite order somewhere, its ratio to `ω` is a nonzero meromorphic function. -/
theorem ratioFunction_ne_zero (hω₀ : ∀ x, ω.order x ≠ ⊤) (hη₀ : ∀ x, η.order x ≠ ⊤) :
    ratioFunction η ω hη hω ≠ 0 := by
  intro h
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have := order_ratioFunction_add_order hη hω hω₀ x
  rw [h, AddValuation.map_zero, WithTop.top_add] at this
  exact hη₀ x this.symm

variable [CompactSpace X]

/-- **Divisors of `1`-forms differ by a principal divisor.** On a compact connected Riemann
surface, if `η` and `ω` are meromorphic and of finite order everywhere then
`div η = div (η / ω) + div ω`. -/
theorem divisor_eq_principalDivisor_add (hη₀ : ∀ x, η.order x ≠ ⊤) :
    η.divisor = (MeromorphicFunction.orderSystem X).principalDivisor
      (Additive.ofMul (Units.mk0 _ (ratioFunction_ne_zero hη hω hω₀ hη₀))) + ω.divisor := by
  refine WeilDivisor.ext fun x ↦ ?_
  have hp := MeromorphicFunction.coe_coeff_principalDivisor_orderSystem
    (Additive.ofMul (Units.mk0 _ (ratioFunction_ne_zero hη hω hω₀ hη₀))) x
  simp only [toMul_ofMul, Units.val_mk0] at hp
  have hf₀ : MeromorphicFunction.order x (ratioFunction η ω hη hω) ≠ ⊤ :=
    (MeromorphicFunction.order x).ne_top_iff.2 (ratioFunction_ne_zero hη hω hω₀ hη₀)
  rw [WeilDivisor.coeff_add, coeff_divisor hη, coeff_divisor hω,
    ← order_ratioFunction_add_order hη hω hω₀ x, WithTop.untop₀_add hf₀ (hω₀ x), ← hp,
    WithTop.untop₀_coe]

/-- **Divisors of `1`-forms are linearly equivalent.** On a compact connected Riemann surface, the
divisors of two `1`-forms meromorphic and of finite order everywhere are linearly equivalent. -/
theorem linearlyEquivalent_divisor (hη₀ : ∀ x, η.order x ≠ ⊤) :
    (MeromorphicFunction.orderSystem X).LinearlyEquivalent η.divisor ω.divisor :=
  (MeromorphicFunction.orderSystem X).linearlyEquivalent_iff_exists_principalDivisor.2
    ⟨_, by rw [divisor_eq_principalDivisor_add hη hω hω₀ hη₀, add_sub_cancel_right]⟩

end Connected

end OneForm

section Canonical

variable [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]

/-- A divisor `K` on a compact Riemann surface is **canonical** if it is the divisor of
a `1`-form which is meromorphic and of finite order at every point. -/
def IsCanonicalDivisor (K : WeilDivisor X) : Prop :=
  ∃ ω : OneForm X, (∀ x, ω.MeromorphicAt x) ∧ (∀ x, ω.order x ≠ ⊤) ∧ ω.divisor = K

/-- The divisor of a `1`-form meromorphic and of finite order everywhere is canonical. -/
theorem isCanonicalDivisor_divisor {ω : OneForm X} (hω : ∀ x, ω.MeromorphicAt x)
    (hω₀ : ∀ x, ω.order x ≠ ⊤) : IsCanonicalDivisor ω.divisor :=
  ⟨ω, hω, hω₀, rfl⟩

namespace IsCanonicalDivisor

variable [ConnectedSpace X] {K K' D : WeilDivisor X}

/-- **Any two canonical divisors are linearly equivalent.** -/
theorem linearlyEquivalent (hK : IsCanonicalDivisor K) (hK' : IsCanonicalDivisor K') :
    (MeromorphicFunction.orderSystem X).LinearlyEquivalent K K' := by
  obtain ⟨η, hη, hη₀, rfl⟩ := hK
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK'
  exact OneForm.linearlyEquivalent_divisor hη hω hω₀ hη₀

/-- A divisor linearly equivalent to a canonical divisor is canonical. -/
theorem of_linearlyEquivalent (hK : IsCanonicalDivisor K)
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D K) :
    IsCanonicalDivisor D := by
  obtain ⟨ω, hω, hω₀, rfl⟩ := hK
  obtain ⟨u, hu⟩ :=
    (MeromorphicFunction.orderSystem X).linearlyEquivalent_iff_exists_principalDivisor.1 h
  set f : MeromorphicFunction X := (Additive.toMul u).1
  have hf : f ≠ 0 := (Additive.toMul u).ne_zero
  have hfω (x : X) : (f.finitePart • ω).MeromorphicAt x :=
    (hω x).smul (f.meromorphicAt_finitePart x)
  refine ⟨f.finitePart • ω, hfω, fun x ↦ ?_, ?_⟩
  · rw [OneForm.order_smul (f.meromorphicAt_finitePart x) (hω x),
      ← MeromorphicFunction.order_apply]
    exact WithTop.add_ne_top.2 ⟨(MeromorphicFunction.order x).ne_top_iff.2 hf, hω₀ x⟩
  · rw [OneForm.divisor_smul f hf hω hω₀]
    have hu' : Additive.ofMul (Units.mk0 f hf) = u := by
      ext
      rfl
    rw [hu', hu, sub_add_cancel]

/-- **The canonical divisors form one linear equivalence class.** Given a canonical divisor `K`,
a divisor is canonical exactly when it is linearly equivalent to `K`. -/
theorem isCanonicalDivisor_iff (hK : IsCanonicalDivisor K) :
    IsCanonicalDivisor D ↔ (MeromorphicFunction.orderSystem X).LinearlyEquivalent D K :=
  ⟨fun hD ↦ hD.linearlyEquivalent hK, hK.of_linearlyEquivalent⟩

end IsCanonicalDivisor

end Canonical

end TauCeti.RiemannSurface
