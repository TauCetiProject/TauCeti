/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Basic

/-!
# Residues of pulled-back `1`-forms

Let `f : X → Y` be a holomorphic map of Riemann surfaces and `ω` a `1`-form meromorphic at `f x`.
Pullback multiplies the residue by the local multiplicity:

`Res_x (f^* ω) = m_x(f) · Res_{f x} ω`
(`TauCeti.RiemannSurface.OneForm.residue_pullback`).

In charts at `x` and `f x` write `ω = a(w) dw` and let `g` be the coordinate representative of
`f`. Then `f^* ω = a(g(z)) g'(z) dz`, and near `x` the map `g` is an `m_x(f)`-fold branched cover in
the local normal form `g(x) + z ^ m`, each of whose sheets contributes `Res_{f x} ω`. The
computation is the branched change of variables for residues
(`TauCeti.Contour.residue_comp_mul_deriv_eq_analyticOrderNatAt_mul`), with the local multiplicity
as the order of vanishing of `g − g(x)`. No nonconstancy hypothesis is needed: if `f` is constant
near `x`, both sides vanish.

Summing over a finite fibre gives the fibre formula
`∑_{x ∈ f⁻¹ y} Res_x (f^* ω) = (∑_{x ∈ f⁻¹ y} m_x(f)) · Res_y ω`
(`TauCeti.RiemannSurface.OneForm.sum_residue_pullback_eq_fiberMultiplicitySum_mul`), which for a
finite holomorphic map from a compact Riemann surface to a connected one is
`∑_{x ∈ f⁻¹ y} Res_x (f^* ω) = deg f · Res_y ω`
(`TauCeti.RiemannSurface.OneForm.sum_residue_pullback_eq_degree_mul`).

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §1 (pullback of meromorphic `1`-forms and its
  effect on orders and residues).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (the residue of a meromorphic differential form).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] {ω : OneForm Y}

/-- **Residue of a pulled-back `1`-form.** If `f` is holomorphic near `x` and `ω` is meromorphic at
`f x`, then the residue of `f^* ω` at `x` is the local multiplicity of `f` at `x` times the residue
of `ω` at `f x`. If `f` is constant near `x`, both sides vanish. -/
theorem residue_pullback {f : X → Y} {x : X} (hω : ω.MeromorphicAt (f x))
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    (ω.pullback f).residue x = localMultiplicity f x * ω.residue (f x) := by
  have hcx := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h := Contour.residue_comp_mul_deriv_eq_analyticOrderNatAt_mul
    (f := ω.coeff (chartAt ℂ (f x))) (φ := (chartAt ℂ (f x) ∘ f) ∘ (chartAt ℂ x).symm)
    (p := chartAt ℂ x x) (by simpa only [comp_apply, hcx] using (meromorphicAt_def ω (f x)).1 hω)
    (analyticAt_chartAt_comp_comp_chartAt_symm hf)
  simp only [comp_apply, hcx] at h
  rw [residue_def, Contour.residue_congr_nhdsNE
    ((coeff_pullback_eventuallyEq ω hf).filter_mono nhdsWithin_le_nhds), localMultiplicity_def,
    residue_def]
  exact h

/-- **Fibre sum of residues of a pulled-back `1`-form.** If the fibre of `f` over `y` is finite,
`f` is holomorphic near each of its points, and `ω` is meromorphic at `y`, then the residues of
`f^* ω` over the fibre add up to the fibre multiplicity sum of `f` at `y` times the residue of
`ω` at `y`. -/
theorem sum_residue_pullback_eq_fiberMultiplicitySum_mul {f : X → Y} {y : Y}
    (hy : (f ⁻¹' {y}).Finite) (hω : ω.MeromorphicAt y)
    (hf : ∀ x ∈ f ⁻¹' {y}, ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z) :
    ∑ x ∈ hy.toFinset, (ω.pullback f).residue x = fiberMultiplicitySum f y * ω.residue y := by
  rw [fiberMultiplicitySum_eq_sum hy, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' : f x ∈ ({y} : Set Y) := hy.mem_toFinset.1 hx
  rw [mem_singleton_iff] at hx'
  rw [residue_pullback (hx' ▸ hω) (hf x (hy.mem_toFinset.1 hx)), hx']

/-- **Fibre sum of residues for a finite holomorphic map.** For a finite holomorphic map `f` from
a compact Riemann surface to a connected Riemann surface and a `1`-form `ω` meromorphic at `y`,
`∑_{x ∈ f⁻¹ y} Res_x (f^* ω) = deg f · Res_y ω`. -/
theorem sum_residue_pullback_eq_degree_mul [CompactSpace X] [T2Space X] [T2Space Y]
    [PreconnectedSpace Y] (f : FiniteHolomorphicMap X Y) {y : Y} (hω : ω.MeromorphicAt y) :
    ∑ x ∈ (f.finite_fiber y).toFinset, (ω.pullback f).residue x = degree f * ω.residue y := by
  rw [sum_residue_pullback_eq_fiberMultiplicitySum_mul (f.finite_fiber y) hω
      fun _ _ ↦ .of_forall fun z ↦ f.holomorphic z,
    fiberMultiplicitySum_eq_degree f.holomorphic f.not_eventuallyConst]

end TauCeti.RiemannSurface.OneForm
