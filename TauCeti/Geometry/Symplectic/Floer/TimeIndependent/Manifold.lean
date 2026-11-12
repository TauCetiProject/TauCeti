/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Symplectic.Floer.CylinderAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.Gradient
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Time-independent Floer cylinders in a manifold are gradient lines

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and `H : M → ℝ` an autonomous Hamiltonian. For the cylindrical perturbation
`K = H dt`, the Floer equation for a map `u` of the cylinder reads
`∂_s u + J (∂_t u - X_H(u)) = 0`, with the convention `ι_{X_H} ω = dH`. A map that does not depend
on `t`, `u(s, t) = γ(s)`, therefore solves it exactly when `γ' = J X_H(γ)`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_fst_iff`). If the Riemannian
metric of `M` is `g = ω(·, J ·)` at `γ(s)`, then `J X_H` is the gradient `∇H` for `g`
(`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_eq_mgradient`), so the
time-independent Floer cylinders are exactly the upward gradient lines `γ' = ∇H(γ)` of `H`
(`IsNondegenerate.isComplexLinearMap_perturbedMFDeriv_comp_fst_iff_curveVelocity_eq_mgradient`).
For a family of almost complex structures `J` whose metric is `g` along `γ`, the curve `γ` is an
integral curve of `∇H` exactly when `(s, t) ↦ γ(s)` is a Floer cylinder for `(H, J)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_mgradient_iff`).

The Floer energy density of `(s, t) ↦ γ(s)` is `dH(γ(s)) γ'(s)`, the derivative of `H ∘ γ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp_fst`), which is `|∇H(γ(s))|²`
along a gradient line. Its energy over `[a, b] × [0, 1]` is `H(γ(b)) - H(γ(a))`
(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_comp_fst`), and if `γ` runs
from `x` at `s = -∞` to `y` at `s = ∞` with `H ∘ γ` nondecreasing, as along a gradient line, its
energy over the whole cylinder is `H(y) - H(x)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_comp_fst`,
`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_comp_fst_of_isMIntegralCurve`).
This is the action difference of the constant orbits at `y` and `x` with constant caps. Neither
closedness of `ω` nor the Floer equation is needed for the energy identities.

These are the time-independent solutions in Floer's comparison of the Floer complex of a small
autonomous Hamiltonian with the Morse complex of `H`: read backwards in `s`, an upward gradient line
from `x` to `y` is a Morse trajectory of `H` from `y` down to `x`. That every finite-energy Floer
cylinder of a `C²`-small Hamiltonian is time-independent is not proved here. The vector-space
counterpart of this file is `TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Basic`.

## Main results

* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_fst_iff`: a time-independent
  map solves the Floer equation for `K = H dt` exactly when `γ' = J X_H(γ)`.
* `IsNondegenerate.isComplexLinearMap_perturbedMFDeriv_comp_fst_iff_curveVelocity_eq_mgradient`:
  for `g = ω(·, J ·)`, exactly when `γ' = ∇H(γ)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_mgradient_iff`: the integral curves of
  `∇H` are the time-independent Floer cylinders.
* `TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp_fst`: the energy density of a
  time-independent map is `dH(γ')`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_comp_fst`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_comp_fst`: the energy over a
  rectangle and over the whole cylinder is the difference of the values of `H` at the ends.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221 (time-independent solutions of the Floer equation and the comparison
  with the Morse complex).
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360 (the Floer cylinders of a small
  autonomous Hamiltonian and its gradient lines).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 10 (solutions of the Floer equation independent of `t` are gradient trajectories).
-/

public section

open Bundle Filter MeasureTheory Set Topology
open scoped Manifold RealInnerProductSpace

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {H : M → ℝ} {γ : ℝ → M} {z : ℝ × ℝ}

/-! ### The Floer equation for time-independent maps -/

/-- The `∂_s` component of the perturbed derivative of `(s, t) ↦ γ(s)` for `K = H dt` is the
velocity of `γ`. -/
private theorem perturbedMFDeriv_comp_fst_apply_stdComplexLineReal
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z stdComplexLineReal =
      Manifold.curveVelocity I γ z.1 := by
  rw [perturbedMFDeriv_apply_stdComplexLineReal, stdComplexLineReal_eq,
    Manifold.mfderiv_comp_fst_apply_one_zero hγ, hamiltonianVectorField_const, Pi.zero_apply,
    sub_zero]

/-- The `∂_t` component of the perturbed derivative of `(s, t) ↦ γ(s)` for `K = H dt` is
`-X_H(γ(s))`. -/
private theorem perturbedMFDeriv_comp_fst_apply_stdComplexLineImag
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z stdComplexLineImag =
      -ω.hamiltonianVectorField H (γ z.1) := by
  rw [perturbedMFDeriv_apply_stdComplexLineImag, stdComplexLineImag_eq,
    Manifold.mfderiv_comp_fst_apply_zero_one hγ, zero_sub]

/-- **Time-independent Floer cylinders.** For the cylindrical perturbation `K = H dt` of an
autonomous Hamiltonian and any almost complex structure `J` on the tangent space, the map
`(s, t) ↦ γ(s)` solves the Floer equation at `z` exactly when `γ'(s) = J X_H(γ(s))`, where
`s = z.1`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_fst_iff
    {J : AlmostComplexStructure (TangentSpace I (γ z.1))} (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z).toLinearMap ↔
      Manifold.curveVelocity I γ z.1 = J (ω.hamiltonianVectorField H (γ z.1)) := by
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe,
    perturbedMFDeriv_comp_fst_apply_stdComplexLineReal hγ,
    perturbedMFDeriv_comp_fst_apply_stdComplexLineImag hγ]
  -- `-X_H = J γ'` and `γ' = J X_H` are equivalent since `J² = -1`.
  constructor
  · intro h
    have hJ := congrArg J h
    rw [map_neg, AlmostComplexStructure.apply_apply] at hJ
    exact (neg_inj.mp hJ).symm
  · intro h
    rw [h, AlmostComplexStructure.apply_apply]

section Nondegenerate

variable [FiniteDimensional ℝ E]

/-- **The energy density of a time-independent map.** For the perturbation `K = H dt`, the Floer
energy density of `(s, t) ↦ γ(s)` at `z` is `dH(γ(s)) γ'(s)`, where `s = z.1`. When `H` is
differentiable at `γ(s)`, this is the derivative of `H ∘ γ` at `s`. -/
theorem IsNondegenerate.floerEnergyDensity_comp_fst (hω : ω.IsNondegenerate)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z =
      mvfderiv I H (γ z.1) (Manifold.curveVelocity I γ z.1) := by
  rw [floerEnergyDensity_def, perturbedMFDeriv_comp_fst_apply_stdComplexLineReal hγ,
    perturbedMFDeriv_comp_fst_apply_stdComplexLineImag hγ, SmoothBundleForm.eval₂_neg_right,
    SmoothBundleForm.eval₂_swap, neg_neg, hω.eval₂_hamiltonianVectorField]

/-- **The energy of a time-independent map over a rectangle.** Let `H` and `γ` be `C¹`. For the
perturbation `K = H dt`, the Floer energy of `(s, t) ↦ γ(s)` over `[a, b] × [0, 1]` is
`H(γ(b)) - H(γ(a))`. No Floer equation is assumed. -/
theorem IsNondegenerate.integral_floerEnergyDensity_comp_fst (hω : ω.IsNondegenerate)
    (hH : ContMDiff I 𝓘(ℝ) 1 H) (hγ : ContMDiff 𝓘(ℝ) I 1 γ) {a b : ℝ} (hab : a ≤ b) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z =
      H (γ b) - H (γ a) := by
  -- This is the cylindrical energy identity; the symplectic area of a map which only depends on
  -- `s` vanishes.
  refine (hω.integral_floerEnergyDensity_cylindrical (H := fun _ ↦ H) (hH.comp contMDiff_snd)
    (hγ.comp contDiff_fst.contMDiff) hab).trans ?_
  simp [rectangleIntegral_comp_fst]

/-- **The energy of a time-independent map over the cylinder.** Let `H` and `γ` be `C¹`, with
`H ∘ γ` nondecreasing, that is `dH(γ(s)) γ'(s) ≥ 0` for all `s`, and let `γ(s)` tend to `x` as
`s → -∞` and to `y` as `s → ∞`. For the perturbation `K = H dt`, the Floer energy of
`(s, t) ↦ γ(s)` over the strip `ℝ × [0, 1]` is `H(y) - H(x)`. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_comp_fst (hω : ω.IsNondegenerate)
    (hH : ContMDiff I 𝓘(ℝ) 1 H) (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hmono : ∀ s, 0 ≤ mvfderiv I H (γ s) (Manifold.curveVelocity I γ s)) {x y : M}
    (hbot : Tendsto γ atBot (𝓝 x)) (htop : Tendsto γ atTop (𝓝 y)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z) =
      ENNReal.ofReal (H y - H x) := by
  have hcont : Continuous (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1)) :=
    hω.continuous_floerEnergyDensity_zero_left (hH.comp contMDiff_snd)
      (hγ.comp contDiff_fst.contMDiff)
  have hnonneg (z : ℝ × ℝ) :
      0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z := by
    rw [hω.floerEnergyDensity_comp_fst ((hγ z.1).mdifferentiableAt one_ne_zero)]
    exact hmono z.1
  -- On each rectangle `[-n, n] × [0, 1]` the energy is `H(γ(n)) - H(γ(-n))`.
  refine setLIntegral_univ_prod_eq_ofReal_of_tendsto (F := H ∘ γ) (fun n ↦ ?_)
    ((hH.continuous.tendsto x).comp hbot) ((hH.continuous.tendsto y).comp htop)
  rw [← ofReal_integral_eq_lintegral_ofReal
      (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
      (Eventually.of_forall hnonneg),
    hω.integral_floerEnergyDensity_comp_fst hH hγ (neg_le_self n.cast_nonneg)]
  rfl

end Nondegenerate

/-! ### Gradient lines -/

section Gradient

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- **Time-independent Floer cylinders are gradient lines.** Let the Riemannian metric at `γ(s)`
be `g(u, v) = ω(u, J v)`. For the perturbation `K = H dt`, the map `(s, t) ↦ γ(s)` solves the Floer
equation for `J` at `z` exactly when `γ'(s)` is the gradient of `H` at `γ(s)`, where `s = z.1`. -/
theorem IsNondegenerate.isComplexLinearMap_perturbedMFDeriv_comp_fst_iff_curveVelocity_eq_mgradient
    (hω : ω.IsNondegenerate) {J : AlmostComplexStructure (TangentSpace I (γ z.1))}
    (hJ : ∀ u v : TangentSpace I (γ z.1), ⟪u, v⟫ = ω.eval₂ (γ z.1) u (J v))
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z).toLinearMap ↔
      Manifold.curveVelocity I γ z.1 = Manifold.mgradient I H (γ z.1) := by
  rw [isComplexLinearMap_perturbedMFDeriv_comp_fst_iff hγ,
    hω.apply_hamiltonianVectorField_eq_mgradient hJ]

/-- **The gradient lines of `H` are the time-independent Floer cylinders.** Let `J` be a family of
almost complex structures on the tangent spaces with `g(u, v) = ω(u, J v)` along `γ` for the
Riemannian metric `g`; no regularity of `J` is needed. The curve `γ` is an integral curve of the
gradient of `H` exactly when it is differentiable and `(s, t) ↦ γ(s)` solves the Floer equation for
`K = H dt` and `J` at every point. -/
theorem IsNondegenerate.isMIntegralCurve_mgradient_iff (hω : ω.IsNondegenerate)
    {J : (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s (u v : TangentSpace I (γ s)), ⟪u, v⟫ = ω.eval₂ (γ s) u (J (γ s) v)) :
    IsMIntegralCurve γ (Manifold.mgradient I H) ↔
      (∀ s, MDifferentiableAt 𝓘(ℝ) I γ s) ∧
        ∀ z : ℝ × ℝ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (γ z.1))
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z).toLinearMap := by
  have hiff (z : ℝ × ℝ) (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1) :=
    hω.isComplexLinearMap_perturbedMFDeriv_comp_fst_iff_curveVelocity_eq_mgradient (H := H)
      (hJ z.1) hγ
  rw [Manifold.isMIntegralCurve_iff_curveVelocity_eq]
  exact ⟨fun h ↦ ⟨fun s ↦ (h s).1, fun z ↦ (hiff z (h z.1).1).2 (h z.1).2⟩,
    fun h s ↦ ⟨h.1 s, (hiff (s, 0) (h.1 s)).1 (h.2 (s, 0))⟩⟩

/-- **The energy density of a gradient line.** If `γ'(s)` is the gradient of `H` at `γ(s)`, then
the Floer energy density of `(s, t) ↦ γ(s)` for `K = H dt` at `z` is `|∇H(γ(s))|²`, where
`s = z.1`. -/
theorem IsNondegenerate.floerEnergyDensity_comp_fst_of_curveVelocity_eq_mgradient
    (hω : ω.IsNondegenerate) (hγ : MDifferentiableAt 𝓘(ℝ) I γ z.1)
    (hgrad : Manifold.curveVelocity I γ z.1 = Manifold.mgradient I H (γ z.1)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z =
      ⟪Manifold.mgradient I H (γ z.1), Manifold.mgradient I H (γ z.1)⟫ := by
  rw [hω.floerEnergyDensity_comp_fst hγ, hgrad, Manifold.mvfderiv_apply_mgradient]

/-- **The energy of a gradient line.** Let `H` and `γ` be `C¹`, let `γ` be an integral curve of the
gradient of `H`, and let `γ(s)` tend to `x` as `s → -∞` and to `y` as `s → ∞`. For the
perturbation `K = H dt`, the Floer energy of the time-independent cylinder `(s, t) ↦ γ(s)` is
`H(y) - H(x)`. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_comp_fst_of_isMIntegralCurve
    (hω : ω.IsNondegenerate) (hH : ContMDiff I 𝓘(ℝ) 1 H) (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hgrad : IsMIntegralCurve γ (Manifold.mgradient I H)) {x y : M}
    (hbot : Tendsto γ atBot (𝓝 x)) (htop : Tendsto γ atTop (𝓝 y)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z) =
      ENNReal.ofReal (H y - H x) := by
  refine hω.lintegral_floerEnergyDensity_comp_fst hH hγ (fun s ↦ ?_) hbot htop
  rw [(Manifold.isMIntegralCurve_iff_curveVelocity_eq.1 hgrad s).2,
    Manifold.mvfderiv_apply_mgradient]
  exact real_inner_self_nonneg

end Gradient

end TauCeti.SmoothTwoForm
