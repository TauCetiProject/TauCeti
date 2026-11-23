/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CylinderAction
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The action shift of continuation cylinders for arbitrary homotopies

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M` and `G_z`, `z = (s, t)`,
a `C¹` family of Hamiltonians. A continuation cylinder for `G` solves the Floer equation
`∂_s u + J_z (∂_t u - X_{G_z}(u)) = 0`, the inhomogeneous equation of the perturbation
`K = G_z dt`, whose curvature is `∂_s G`. By the energy identity
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub_sub_integral`),
the capped action of the loop at `s = b`, for the Hamiltonian `G(b, ·)`, is the capped action of
the loop at `s = a`, for `G(a, ·)` and with the cap carried along the cylinder, minus the energy
and minus the integral of `∂_s G` along `u`. Since the energy of a solution is nonnegative, every
upper bound for `-∂_s G` along `u` bounds the increase of the action from `s = a` to `s = b`.
This file records the three forms of this bound used for the action filtration of continuation
maps, which hold for any homotopy, not only for the linear one of
`TauCeti.Geometry.Symplectic.Floer.Continuation.Manifold`.

* **Arbitrary homotopies.** If `-∂_s G(s, t, x) ≤ c(s)` along `u`, the action increases by at most
  `∫_a^b c`. On a compact manifold the best choice is `c(s) = max_{t, x} (-∂_s G)(s, t, x)`, and
  `c = 0` for a homotopy that is monotone in `s`, which therefore preserves the action filtration.
* **Reparametrized paths.** If `G(s, t) = K(β(s), t)` for a `C¹` path `K_ϑ` of Hamiltonians and a
  monotone `C¹` reparametrization `β`, and `-∂_ϑ K(ϑ, t, x) ≤ k(t)` along `u`, the action
  increases by at most `(β(b) - β(a)) ∫₀¹ k`. For `β` running from `0` to `1` the bound is
  `∫₀¹ k`, independent of the profile `β` and of the length of the cylinder; the best choice is
  `k(t) = max_{ϑ, x} (-∂_ϑ K)(ϑ, t, x)`.
* **Paths close to the linear one.** If moreover `∂_ϑ K ≥ K₁ - K₀ - ε` along `u` and
  `K₀ - K₁ ≤ h`, the action increases by at most `∫₀¹ h + ε`. For the linear path
  `K_ϑ = K₀ + ϑ (K₁ - K₀)` this holds with `ε = 0`, which is the linear-homotopy estimate.

Each of the three bounds is stated for the capped action `TauCeti.cylinderAction` of an arbitrary
nondegenerate form, with the cap carried along the cylinder, and for the action
`TauCeti.contractibleLoopAction` of contractible loops of a weakly exact form. The capped forms of
the exact estimate and of the monotone case are also here; their contractible forms are
`SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_sub_integral` and
`SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_of_monotone`, in
`TauCeti.Geometry.Symplectic.Floer.CylinderAction`. The underlying estimates of the integrated
curvature along a map are `TauCeti.Floer.neg_setIntegral_fderiv_le_setIntegral`, also in
`TauCeti.Geometry.Symplectic.Floer.CylinderAction`, and
`TauCeti.Floer.neg_setIntegral_fderiv_reparam_le` and
`TauCeti.Floer.neg_setIntegral_fderiv_reparam_le_integral_add`, here.

The end `s = a` is the input of the continuation map and `s = b` its output. Barraud, Damian,
Humilière and Oancea state the same estimates with the two ends exchanged, for continuation maps
running from the positive to the negative end.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_sub_integral`: the
  capped action at `s = b` is at most the capped action at `s = a` minus the integrated curvature.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_of_monotone`: monotone
  homotopies do not increase the capped action.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_integral`,
  `IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_integral`: arbitrary
  homotopies increase the action by at most `∫_a^b c`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_reparam`,
  `IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_reparam`: reparametrized
  paths increase the action by at most `(β(b) - β(a)) ∫₀¹ k`.
* `IsNondegenerate.cylinderAction_le_cylinderAction_add_integral_add_of_reparam`,
  `IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_integral_add_of_reparam`:
  paths `ε`-close to the linear one increase the action by at most `∫₀¹ h + ε`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 3.22 and Corollaries 3.24
  and 3.25.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
-/

public section

open Function MeasureTheory Set Real
open scoped Manifold

namespace TauCeti

namespace Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M] {u : ℝ × ℝ → M}
  {a b : ℝ}

/-- **The integrated curvature of a reparametrized path along a map.** Let `K_w`, `w = (ϑ, t)`, be
a `C¹` family of Hamiltonians on a manifold, `β` a monotone `C¹` reparametrization and `u` a `C¹`
map. If `-∂_ϑ K(β(s), t, u(s, t)) ≤ k(t)` on `[a, b] × [0, 1]` for a function `k` integrable on
`[0, 1]`, then minus the integral of the curvature `∂_s G = β'(s) ∂_ϑ K(β(s), t)` of the homotopy
`G(s, t) = K(β(s), t)` along `u` over the rectangle is at most `(β(b) - β(a)) ∫₀¹ k`. -/
theorem neg_setIntegral_fderiv_reparam_le {K : ℝ × ℝ → M → ℝ}
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hab : a ≤ b) {k : ℝ → ℝ}
    (hk : IntegrableOn k (Icc 0 1))
    (hKk : ∀ z ∈ Icc a b ×ˢ Icc 0 1, -deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1) ≤ k z.2) :
    -∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ K (β w.1, w.2) (u z)) z stdComplexLineReal ≤
      (β b - β a) * ∫ t in Icc 0 1, k t := by
  have hKu : ContDiff ℝ 1 (uncurry fun (z w : ℝ × ℝ) ↦ K w (u z)) :=
    contMDiff_iff_contDiff.mp (hK.comp (contDiff_snd.contMDiff.prodMk
      (hu.comp contDiff_fst.contMDiff)))
  have hd (z : ℝ × ℝ) : ContDiff ℝ 1 fun w ↦ K w (u z) :=
    hKu.comp (contDiff_const.prodMk contDiff_id)
  have hp : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ (β w.1, w.2) := (hβ.comp contDiff_fst).prodMk contDiff_snd
  -- The `ϑ`-derivative of `K` at `(β(s), t)`, as a partial derivative of a `C¹` function.
  have hθ (z : ℝ × ℝ) : deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1) =
      fderiv ℝ (fun w ↦ K w (u z)) (β z.1, z.2) (1, 0) :=
    (fderiv_apply_mk_one_zero (z := (β z.1, z.2)) ((hd z).differentiable one_ne_zero _)).symm
  -- The chain rule: `∂_s G = β'(s) ∂_ϑ K(β(s), t)`.
  have hcurv (z : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ K (β w.1, w.2) (u z)) z stdComplexLineReal =
        deriv β z.1 * deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1) := by
    rw [stdComplexLineReal_eq,
      fderiv_apply_mk_one_zero (u := fun w ↦ K (β w.1, w.2) (u z))
        ((((hd z).comp hp).differentiable one_ne_zero) z), mul_comm]
    exact deriv_comp (h₂ := fun θ ↦ K (θ, z.2) (u z)) z.1
      ((((hd z).comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero) _)
      ((hβ.differentiable one_ne_zero) z.1)
  have hf : Continuous fun z : ℝ × ℝ ↦ deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1) := by
    simp only [hθ]
    exact (Continuous.fderiv_one hKu ((hβ.continuous.comp continuous_fst).prodMk
      continuous_snd)).clm_apply continuous_const
  simp only [hcurv]
  have hle := neg_mul_setIntegral_le_setIntegral_deriv_mul hβ hβm hab hf.continuousOn hk
    fun z hz ↦ neg_le.mp (hKk z hz)
  linarith

/-- **The integrated curvature of a path close to the linear one.** Under the hypotheses of
`TauCeti.Floer.neg_setIntegral_fderiv_reparam_le`, with `β(a) = 0` and `β(b) = 1`, suppose that
`∂_ϑ K ≥ K(1, ·) - K(0, ·) - ε` at `(β(s), t, u(s, t))` and that
`K(0, t, u(s, t)) - K(1, t, u(s, t)) ≤ h(t)`, on `[a, b] × [0, 1]`, for a function `h` integrable on
`[0, 1]`. Then minus the integral of the curvature of `G(s, t) = K(β(s), t)` along `u` over the
rectangle is at most `∫₀¹ h + ε`. -/
theorem neg_setIntegral_fderiv_reparam_le_integral_add {K : ℝ × ℝ → M → ℝ}
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hβa : β a = 0) (hβb : β b = 1) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hab : a ≤ b) {ε : ℝ} (hε : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      K (1, z.2) (u z) - K (0, z.2) (u z) - ε ≤ deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1))
    {h : ℝ → ℝ} (hhi : IntegrableOn h (Icc 0 1))
    (hh : ∀ z ∈ Icc a b ×ˢ Icc 0 1, K (0, z.2) (u z) - K (1, z.2) (u z) ≤ h z.2) :
    -∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ K (β w.1, w.2) (u z)) z stdComplexLineReal ≤
      (∫ t in Icc 0 1, h t) + ε := by
  have hε' : IntegrableOn (fun _ ↦ ε) (Icc (0 : ℝ) 1) := integrableOn_const measure_Icc_lt_top.ne
  simpa [hβa, hβb, integral_add hhi hε'] using
    neg_setIntegral_fderiv_reparam_le (k := fun t ↦ h t + ε) hK hβ hβm hu hab (hhi.add hε')
      fun z hz ↦ by linarith [hε z hz, hh z hz]

end Floer

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}
  {G K : ℝ × ℝ → M → ℝ} {u v : ℝ × ℝ → M} {a b : ℝ}

/-! ### The capped action -/

/-- **The capped action estimate along a continuation cylinder.** Let `ω` be a nondegenerate
two-form on a finite-dimensional manifold, `G_z` a `C¹` family of Hamiltonians, `u` a `C¹` map
and `v` a `C¹` map with `v (0, ·) = u (b, ·)`. If `u` solves the Floer equation
`∂_s u + J_z (∂_t u - X_{G_z}(u)) = 0` on `[a, b] × [0, 1]`, with almost complex structures
`J z` on `T_{u z} M` tamed by `ω`, then the action of `γ_b = u(b, ·)` for `G(b, ·)` measured
against `v` is at most the action of `γ_a = u(a, ·)` for `G(a, ·)` measured against the glued map
`w # v`, minus the integral of the curvature `∂_s G` along `u`. Here `w # v`
(`TauCeti.rectangleTrans`) glues `u` on `[a, b] × [0, 1]`, rescaled to `[0, 1] × [0, 1]`, to `v`.
When `v` is a cap of `γ_b`, both actions are capped actions. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_sub_integral (hω : ω.IsNondegenerate)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hab : a ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (G z) (u z)) = 0) :
    cylinderAction ω.val (fun t ↦ G (b, t)) v ≤
      cylinderAction ω.val (fun t ↦ G (a, t))
          (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal := by
  have h := hω.integral_floerEnergyDensity_eq_cylinderAction_sub_sub_integral hG hu hab hv hv₀
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (hJ z hz) (hfloer z hz)
  linarith

/-- **Monotone homotopies do not increase the capped action.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_sub_integral`, if every
`s ↦ G_{(s, t)}(x)` is monotone, then the action of `γ_b` for `G(b, ·)` measured against `v` is at
most the action of `γ_a` for `G(a, ·)` measured against `w # v`. So continuation maps along
monotone homotopies preserve the action filtration. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_of_monotone (hω : ω.IsNondegenerate)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G))
    (hmono : ∀ t x, Monotone fun s ↦ G (s, t) x) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hab : a ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (G z) (u z)) = 0) :
    cylinderAction ω.val (fun t ↦ G (b, t)) v ≤
      cylinderAction ω.val (fun t ↦ G (a, t))
        (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) := by
  have h := hω.cylinderAction_le_cylinderAction_sub_integral hG hu hab hv hv₀ J hJ hfloer
  have hc := neg_setIntegral_fderiv_le_setIntegral (a := a) (b := b) hG hu integrableOn_zero
    fun z _ ↦ neg_nonpos.mpr (hmono z.2 (u z)).deriv_nonneg
  simp only [integral_zero] at hc
  linarith

/-- **The capped action shift of an arbitrary homotopy.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_sub_integral`, if
`-∂_s G(s, t, u(s, t)) ≤ c(s)` on `[a, b] × [0, 1]` for a function `c` integrable on `[a, b]`, then
the action of `γ_b` for `G(b, ·)` measured against `v` is at most the action of `γ_a` for
`G(a, ·)` measured against `w # v` plus `∫_a^b c`. On a compact manifold one may take
`c(s) = max_{t, x} (-∂_s G)(s, t, x)`. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_integral (hω : ω.IsNondegenerate)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hab : a ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (G z) (u z)) = 0)
    {c : ℝ → ℝ} (hc : IntegrableOn c (Icc a b))
    (hGc : ∀ z ∈ Icc a b ×ˢ Icc 0 1, -deriv (fun s ↦ G (s, z.2) (u z)) z.1 ≤ c z.1) :
    cylinderAction ω.val (fun t ↦ G (b, t)) v ≤
      cylinderAction ω.val (fun t ↦ G (a, t))
          (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        ∫ s in Icc a b, c s := by
  have h := hω.cylinderAction_le_cylinderAction_sub_integral hG hu hab hv hv₀ J hJ hfloer
  linarith [neg_setIntegral_fderiv_le_setIntegral hG hu hc hGc]

/-- **The capped action shift of a reparametrized path.** Let `K_w`, `w = (ϑ, t)`, be a `C¹`
family of Hamiltonians, `β` a monotone `C¹` reparametrization and `G(s, t) = K(β(s), t)`. Under
the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_sub_integral` for `G`, if
`-∂_ϑ K(β(s), t, u(s, t)) ≤ k(t)` on `[a, b] × [0, 1]` for a function `k` integrable on `[0, 1]`,
then the action of `γ_b` for `K(β(b), ·)` measured against `v` is at most the action of `γ_a` for
`K(β(a), ·)` measured against `w # v` plus `(β(b) - β(a)) ∫₀¹ k`. For `β(a) = 0` and `β(b) = 1`
the shift is at most `∫₀¹ k`, whatever the profile `β`; on a compact manifold one may take
`k(t) = max_{ϑ, x} (-∂_ϑ K)(ϑ, t, x)`. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_of_reparam (hω : ω.IsNondegenerate)
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hab : a ≤ b)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (K (β z.1, z.2)) (u z)) = 0)
    {k : ℝ → ℝ} (hk : IntegrableOn k (Icc 0 1))
    (hKk : ∀ z ∈ Icc a b ×ˢ Icc 0 1, -deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1) ≤ k z.2) :
    cylinderAction ω.val (fun t ↦ K (β b, t)) v ≤
      cylinderAction ω.val (fun t ↦ K (β a, t))
          (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        (β b - β a) * ∫ t in Icc 0 1, k t := by
  have h := hω.cylinderAction_le_cylinderAction_sub_integral (contMDiff_uncurry_reparam hβ hK) hu
    hab hv hv₀ J hJ hfloer
  linarith [neg_setIntegral_fderiv_reparam_le hK hβ hβm hu hab hk hKk]

/-- **The capped action shift of a path close to the linear one.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_reparam`, with
`β(a) = 0` and `β(b) = 1`, suppose that `∂_ϑ K ≥ K(1, ·) - K(0, ·) - ε` at `(β(s), t, u(s, t))`
and that `K(0, t, u(s, t)) - K(1, t, u(s, t)) ≤ h(t)`, on `[a, b] × [0, 1]`, for a function `h`
integrable on `[0, 1]`. Then the action of `γ_b` for `K(1, ·)` measured against `v` is at most the
action of `γ_a` for `K(0, ·)` measured against `w # v` plus `∫₀¹ h + ε`. A path `ε`-close in `C¹`
to the linear path from `K(0, ·)` to `K(1, ·)` satisfies the first hypothesis. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_integral_add_of_reparam
    (hω : ω.IsNondegenerate) (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β) (hβm : Monotone β) (hβa : β a = 0) (hβb : β b = 1)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (hab : a ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (K (β z.1, z.2)) (u z)) = 0)
    {ε : ℝ} (hε : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      K (1, z.2) (u z) - K (0, z.2) (u z) - ε ≤ deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1))
    {h : ℝ → ℝ} (hhi : IntegrableOn h (Icc 0 1))
    (hh : ∀ z ∈ Icc a b ×ˢ Icc 0 1, K (0, z.2) (u z) - K (1, z.2) (u z) ≤ h z.2) :
    cylinderAction ω.val (fun t ↦ K (1, t)) v ≤
      cylinderAction ω.val (fun t ↦ K (0, t))
          (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        (∫ t in Icc 0 1, h t) + ε := by
  have h' := hω.cylinderAction_le_cylinderAction_sub_integral (contMDiff_uncurry_reparam hβ hK) hu
    hab hv hv₀ J hJ hfloer
  simp only [hβa, hβb] at h'
  linarith [neg_setIntegral_fderiv_reparam_le_integral_add hK hβ hβm hβa hβb hu hab hε hhi hh]

/-! ### The action of contractible loops -/

/-- **The action shift of an arbitrary homotopy for contractible loops.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_sub_integral`, if
`-∂_s G(s, t, u(s, t)) ≤ c(s)` on `[a, b] × [0, 1]` for a function `c` integrable on `[a, b]`, then
the action of the loop at `s = b` for `G(b, ·)` is at most that of the loop at `s = a` for
`G(a, ·)` plus `∫_a^b c`. -/
theorem IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_integral
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.val)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) (hab : a ≤ b)
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (G z) (u z)) = 0)
    {c : ℝ → ℝ} (hc : IntegrableOn c (Icc a b))
    (hGc : ∀ z ∈ Icc a b ×ˢ Icc 0 1, -deriv (fun s ↦ G (s, z.2) (u z)) z.1 ≤ c z.1) :
    contractibleLoopAction ω.val (fun t ↦ G (b, t)) (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.val (fun t ↦ G (a, t)) (fun t ↦ u (a, t)) +
        ∫ s in Icc a b, c s := by
  have h := hω.contractibleLoopAction_le_contractibleLoopAction_sub_integral hωe hG hu hper hab hv
    J hJ hfloer
  linarith [neg_setIntegral_fderiv_le_setIntegral hG (hu.of_le one_le_two) hc hGc]

/-- **The action shift of a reparametrized path for contractible loops.** Let `K_w`, `w = (ϑ, t)`,
be a `C¹` family of Hamiltonians, `β` a monotone `C¹` reparametrization and
`G(s, t) = K(β(s), t)`. Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_sub_integral` for
`G`, if `-∂_ϑ K(β(s), t, u(s, t)) ≤ k(t)` on `[a, b] × [0, 1]` for a function `k` integrable on
`[0, 1]`, then the action of the loop at `s = b` for `K(β(b), ·)` is at most that of the loop at
`s = a` for `K(β(a), ·)` plus `(β(b) - β(a)) ∫₀¹ k`. -/
theorem IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_reparam
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.val)
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) (hab : a ≤ b)
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (K (β z.1, z.2)) (u z)) = 0)
    {k : ℝ → ℝ} (hk : IntegrableOn k (Icc 0 1))
    (hKk : ∀ z ∈ Icc a b ×ˢ Icc 0 1, -deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1) ≤ k z.2) :
    contractibleLoopAction ω.val (fun t ↦ K (β b, t)) (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.val (fun t ↦ K (β a, t)) (fun t ↦ u (a, t)) +
        (β b - β a) * ∫ t in Icc 0 1, k t := by
  have h := hω.contractibleLoopAction_le_contractibleLoopAction_sub_integral hωe
    (contMDiff_uncurry_reparam hβ hK) hu hper hab hv J hJ hfloer
  linarith [neg_setIntegral_fderiv_reparam_le hK hβ hβm (hu.of_le one_le_two) hab hk hKk]

/-- **The action shift of a path close to the linear one, for contractible loops.** Under the
hypotheses of
`IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_reparam`, with
`β(a) = 0` and `β(b) = 1`, suppose that `∂_ϑ K ≥ K(1, ·) - K(0, ·) - ε` at `(β(s), t, u(s, t))`
and that `K(0, t, u(s, t)) - K(1, t, u(s, t)) ≤ h(t)`, on `[a, b] × [0, 1]`, for a function `h`
integrable on `[0, 1]`. Then the action of the loop at `s = b` for `K(1, ·)` is at most that of
the loop at `s = a` for `K(0, ·)` plus `∫₀¹ h + ε`. -/
theorem
    IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_integral_add_of_reparam
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.val)
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hβa : β a = 0) (hβb : β b = 1) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) (hab : a ≤ b)
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (K (β z.1, z.2)) (u z)) = 0)
    {ε : ℝ} (hε : ∀ z ∈ Icc a b ×ˢ Icc 0 1,
      K (1, z.2) (u z) - K (0, z.2) (u z) - ε ≤ deriv (fun θ ↦ K (θ, z.2) (u z)) (β z.1))
    {h : ℝ → ℝ} (hhi : IntegrableOn h (Icc 0 1))
    (hh : ∀ z ∈ Icc a b ×ˢ Icc 0 1, K (0, z.2) (u z) - K (1, z.2) (u z) ≤ h z.2) :
    contractibleLoopAction ω.val (fun t ↦ K (1, t)) (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.val (fun t ↦ K (0, t)) (fun t ↦ u (a, t)) +
        (∫ t in Icc 0 1, h t) + ε := by
  have h' := hω.contractibleLoopAction_le_contractibleLoopAction_sub_integral hωe
    (contMDiff_uncurry_reparam hβ hK) hu hper hab hv J hJ hfloer
  simp only [hβa, hβb] at h'
  linarith [neg_setIntegral_fderiv_reparam_le_integral_add hK hβ hβm hβa hβb (hu.of_le one_le_two)
    hab hε hhi hh]

end SmoothTwoForm

end TauCeti
