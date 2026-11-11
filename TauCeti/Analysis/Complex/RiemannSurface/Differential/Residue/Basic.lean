/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Basic
public import TauCeti.Analysis.Contour.Residue.ChangeOfVariables

/-!
# The residue of a meromorphic `1`-form

Let `ω` be a `1`-form on a Riemann surface `X`, written `ω = f(z) dz` in a chart `z` at a point
`x`. Its **residue** at `x` (`TauCeti.RiemannSurface.OneForm.residue`) is the residue of `f` at the
coordinate of `x`, the order-`(-1)` Laurent coefficient. The coefficient depends on the chart, but
the residue does not: changing to a chart `w` replaces `f(z)` by `f(z(w)) · dz/dw`, and the residue
of this pull-back is the residue of `f` by the change of variables formula for residues
(`TauCeti.Contour.residue_comp_mul_deriv`). So the residue may be computed in any chart of the
maximal atlas (`TauCeti.RiemannSurface.OneForm.residue_eq_of_mem_maximalAtlas`). Unlike the value
of a function, the residue is attached to the `1`-form `f(z) dz` and not to the function `f`.

The residue is additive on meromorphic `1`-forms, homogeneous, and vanishes where `ω` is
holomorphic. The differential of a meromorphic function has residue `0`
(`TauCeti.RiemannSurface.OneForm.residue_mvfderiv`), and the logarithmic differential `df / f` has
residue the order of `f` (`TauCeti.RiemannSurface.OneForm.residue_inv_smul_mvfderiv`). These are
the local facts behind the residue pairing of Serre duality and the vanishing of the degree of a
principal divisor.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (the residue of a meromorphic differential form and its independence of the chart).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §1 (residues of meromorphic `1`-forms).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {ω η : OneForm X} {x : X}
  {e : OpenPartialHomeomorph X ℂ}

/-- The **residue** of a `1`-form `ω` at `x`: the residue of its coefficient in the preferred chart
at `x`, at the coordinate of `x`. Any chart of the maximal atlas at `x` gives the same value
(`TauCeti.RiemannSurface.OneForm.residue_eq_of_mem_maximalAtlas`). It is the junk value `0` if `ω`
is not meromorphic at `x`. -/
def residue (ω : OneForm X) (x : X) : ℂ :=
  Contour.residue (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x)

theorem residue_def (ω : OneForm X) (x : X) :
    ω.residue x = Contour.residue (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x) :=
  (rfl)

/-- The residue at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem residue_congr (h : ∀ᶠ y in 𝓝[≠] x, ω y = η y) : ω.residue x = η.residue x :=
  Contour.residue_congr_nhdsNE (coeff_chartAt_eventuallyEq h)

/-- A `1`-form which is not meromorphic at `x` has residue the junk value `0`. -/
@[simp]
theorem residue_of_not_meromorphicAt (h : ¬ ω.MeromorphicAt x) : ω.residue x = 0 :=
  Contour.residue_of_not_meromorphicAt ((meromorphicAt_def ω x).not.1 h)

/-- A `1`-form of nonnegative order at `x` has residue `0`. -/
@[simp]
theorem residue_eq_zero_of_order_nonneg (h : 0 ≤ ω.order x) : ω.residue x = 0 :=
  Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg ((order_def ω x) ▸ h)

/-- A `1`-form holomorphic at `x` has residue `0`. -/
@[simp]
theorem HolomorphicAt.residue_eq_zero (h : ω.HolomorphicAt x) : ω.residue x = 0 :=
  residue_eq_zero_of_order_nonneg h.order_nonneg

theorem residue_zero (x : X) : (0 : OneForm X).residue x = 0 :=
  (holomorphicAt_zero x).residue_eq_zero

/-- The residue is additive on `1`-forms meromorphic at `x`. -/
@[simp]
theorem residue_add (hω : ω.MeromorphicAt x) (hη : η.MeromorphicAt x) :
    (ω + η).residue x = ω.residue x + η.residue x := by
  rw [residue_def, coeff_add]
  exact Contour.residue_add ((meromorphicAt_def ω x).1 hω) ((meromorphicAt_def η x).1 hη)

/-- The residue is homogeneous. -/
@[simp]
theorem residue_const_smul (c : ℂ) (ω : OneForm X) (x : X) :
    (c • ω).residue x = c * ω.residue x := by
  rw [residue_def, coeff_const_smul]
  exact Contour.residue_const_smul c

@[simp]
theorem residue_neg (ω : OneForm X) (x : X) : (-ω).residue x = -ω.residue x := by
  rw [← neg_one_smul ℂ ω, residue_const_smul, neg_one_mul]

/-- The residue is subtractive on `1`-forms meromorphic at `x`. -/
@[simp]
theorem residue_sub (hω : ω.MeromorphicAt x) (hη : η.MeromorphicAt x) :
    (ω - η).residue x = ω.residue x - η.residue x := by
  rw [residue_def, coeff_sub]
  exact Contour.residue_sub ((meromorphicAt_def ω x).1 hω) ((meromorphicAt_def η x).1 hη)

variable [IsManifold 𝓘(ℂ) 1 X]

/-- **Chart independence of the residue.** The residue of a `1`-form at `x` is the residue of its
coefficient in any chart of the maximal atlas at `x`. -/
theorem residue_eq_of_mem_maximalAtlas (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) :
    ω.residue x = Contour.residue (ω.coeff e) (e x) := by
  have hcx := mem_chart_source ℂ x
  have hψ := TauCeti.analyticAt_symm_trans (chart_mem_maximalAtlas x) he hcx hx
  have hψ' := TauCeti.deriv_symm_trans_ne_zero (chart_mem_maximalAtlas x) he hcx hx
  have hψx : (e ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = e x := by
    simp [(chartAt ℂ x).left_inv hcx]
  rw [residue_def, Contour.residue_congr_nhdsNE ((coeff_eventuallyEq ω he
    (chart_mem_maximalAtlas x) hx hcx).filter_mono nhdsWithin_le_nhds), ← hψx]
  exact Contour.residue_comp_mul_deriv hψ hψ'

variable {f : X → ℂ}

/-- **The differential of a meromorphic function has residue `0`.** -/
@[simp]
theorem residue_mvfderiv (hf : RiemannSurface.MeromorphicAt f x) :
    residue (mvfderiv 𝓘(ℂ) f) x = 0 := by
  rw [residue_def, Contour.residue_congr_nhdsNE (coeff_mvfderiv_eventuallyEq hf)]
  exact Contour.residue_deriv_eq_zero ((RiemannSurface.meromorphicAt_def f x).1 hf)

/-- **The residue of `df / f` is the order of `f`.** For a function `f` meromorphic at `x` of
finite order `n`, the logarithmic differential `f⁻¹ df` has residue `n` at `x`. -/
theorem residue_inv_smul_mvfderiv {n : ℤ} (hf : RiemannSurface.MeromorphicAt f x)
    (hn : RiemannSurface.meromorphicOrderAt f x = n) :
    residue (f⁻¹ • mvfderiv 𝓘(ℂ) f) x = n := by
  have hev : coeff (f⁻¹ • mvfderiv 𝓘(ℂ) f) (chartAt ℂ x) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      logDeriv (f ∘ (chartAt ℂ x).symm) := by
    filter_upwards [coeff_mvfderiv_eventuallyEq hf] with z hz
    rw [coeff_smul, Pi.mul_apply, hz, logDeriv_apply, div_eq_inv_mul]
    rfl
  rw [residue_def, Contour.residue_congr_nhdsNE hev]
  exact Contour.residue_logDeriv_eq_meromorphicOrderAt
    ((RiemannSurface.meromorphicAt_def f x).1 hf)
    ((RiemannSurface.meromorphicOrderAt_def f x).symm.trans hn)

end TauCeti.RiemannSurface.OneForm
