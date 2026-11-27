/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.HoferNorm
public import TauCeti.Geometry.Symplectic.Floer.Continuation.Normalization
public import TauCeti.Geometry.Symplectic.Floer.Stationary

/-!
# Stationary continuation cylinders and the sharpness of the action estimates

Let `ω` be a two-form on a manifold `M`, `H` a time-dependent Hamiltonian and `f : ℝ × ℝ → ℝ` a
function of the domain coordinates `z = (s, t)` alone. The homotopy `G_z = H_t + f(z)` changes `H`
only by a function of `(s, t)`, so it has the same Hamiltonian vector fields as `H`. If `x` is a
periodic orbit of `H`, the stationary cylinder `u(s, t) = x(t)` therefore solves the continuation
Floer equation `∂_s u + J_z (∂_t u - X_{G_z}(u)) = 0` for every almost complex structure
(`TauCeti.SmoothTwoForm.mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions`); this includes the
continuation homotopy from `H` to `H + c(t)`
(`SmoothTwoForm.mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions_continuationHomotopy`). The
stationary cylinder has zero area and starts and ends at the same loop, so gluing it to a cap does
not change the action (`TauCeti.cylinderAction_rectangleTrans_comp_snd`), and the action changes
only through the normalization `f`: for any cap `v` of `x`,

`A_{G(b, ·)}(x, v) = A_{G(a, ·)}(x, w # v) - ∫₀¹ (f(b, t) - f(a, t)) dt`

(`TauCeti.cylinderAction_add_eq_cylinderAction_add_sub_integral`), where `w # v` glues the
cylinder, rescaled from `[a, b]` to `[0, 1]`, to `v`, as in the action estimates of
`TauCeti.Geometry.Symplectic.Floer.Continuation.Homotopy`. So the action shift of a continuation
cylinder is not the integral of the homotopy: a bump `f(s, t) = ε(s)` with `ε(a) = ε(b)` does not
change the action, whatever the integral of `ε`.

These solutions show that the action estimates for continuation cylinders are sharp and
one-sided.

* **The curvature bound is attained.** For `f(s, t) = ε(s)` the curvature `∂_s G = ε'(s)` does
  not depend on `(t, x)`, so `c(s) = -ε'(s)` is the least admissible bound in
  `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_integral`, and the
  stationary cylinders attain it
  (`TauCeti.cylinderAction_add_eq_cylinderAction_add_setIntegral_neg_deriv`).
* **The bound by `E⁺(H₀ - H₁)` is attained.** For `H₀ = H` and `H₁ = H + c(t)` the action changes
  by exactly `-∫₀¹ c = ∫₀¹ max_x (H₀ - H₁)(t, x) dt = E⁺(H₀ - H₁)`
  (`TauCeti.cylinderAction_add_const_eq_cylinderAction_add_hoferPlus`), the bound of
  `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferPlus`. For
  `c = δ > 0` the continuation homotopy is monotone and lowers every action by exactly `δ`; for
  `c = -δ < 0` it raises every action by exactly `δ`.
* **It is not a bound by the Hofer norm.** The difference `H₀ - H₁ = -c(t)` is constant in space,
  so its Hofer norm vanishes (`TauCeti.hoferNorm_const`). When `∫₀¹ c < 0` the action rises
  nonetheless, so the hypothesis of
  `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferNorm` that
  `H₀ ≤ H₁` somewhere at each time cannot be dropped
  (`TauCeti.not_cylinderAction_add_const_le_cylinderAction_add_hoferNorm`).

No existence, rigidity or count of continuation cylinders is asserted: these are statements about
the explicit stationary solutions.

## Main results

* `TauCeti.SmoothTwoForm.mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions`: the stationary
  cylinder over a periodic orbit of `H` solves the Floer equation of `H_t + f(s, t)`.
* `TauCeti.cylinderAction_add_eq_cylinderAction_add_sub_integral`: its exact action shift.
* `TauCeti.cylinderAction_add_eq_cylinderAction_add_setIntegral_neg_deriv`: equality in the
  curvature bound for `f(s, t) = ε(s)`.
* `TauCeti.cylinderAction_add_const_eq_cylinderAction_add_hoferPlus`: equality in the `E⁺` bound
  for `H₀ = H` and `H₁ = H + c(t)`.
* `TauCeti.not_cylinderAction_add_const_le_cylinderAction_add_hoferNorm`: the Hofer norm does not
  bound the action shift without its sign hypothesis.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 3.22 and Corollaries 3.24
  and 3.25.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
-/

public section

open Function MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {H : ℝ → M → ℝ} {x : ℝ → M} {v : ℝ × ℝ → M} {a b : ℝ}

namespace SmoothTwoForm

open Floer

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}

/-! ### The Floer equation -/

/-- **Stationary cylinders solve the Floer equation of a normalized homotopy.** Let `x` be a
periodic orbit of the Hamiltonian vector field of `H` and `f : ℝ × ℝ → ℝ` a function of the domain
coordinates alone. Then the stationary cylinder `(s, t) ↦ x t` solves the Floer equation
`∂_s u + J (∂_t u - X_{G_z}(u)) = 0` for the homotopy `G_z = H_t + f(z)` at every point `z`, for
every almost complex structure `J`: adding `f(z)` does not change the Hamiltonian vector field. -/
theorem mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions {T : ℝ}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) T) (f : ℝ × ℝ → ℝ)
    (z : ℝ × ℝ) (J : AlmostComplexStructure (TangentSpace I (x z.2))) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ x w.2) z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ x w.2) z stdComplexLineImag -
        ω.hamiltonianVectorField (fun y ↦ H z.2 y + f z) (x z.2)) = 0 := by
  have h := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ _ z J).1
    (isComplexLinearMap_perturbedMFDeriv_comp_snd_of_mem_periodicSolutions hx z J)
  simpa [hamiltonianVectorField_add_const, hamiltonianVectorField_const] using h

/-- **Stationary cylinders solve the continuation equation from `H` to `H + c(t)`.** If `x` is a
periodic orbit of the Hamiltonian vector field of `H`, the stationary cylinder `(s, t) ↦ x t`
solves the Floer equation for the continuation homotopy from `H` to `H + c(t)` at every point, for
every almost complex structure. -/
theorem mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions_continuationHomotopy {T : ℝ}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) T) (c : ℝ → ℝ)
    (z : ℝ × ℝ) (J : AlmostComplexStructure (TangentSpace I (x z.2))) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ x w.2) z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ x w.2) z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H (fun t y ↦ H t y + c t) z) (x z.2)) =
      0 := by
  rw [continuationHomotopy_add_const]
  exact mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions hx
    (fun w ↦ Real.smoothTransition w.1 * c w.2) z J

end SmoothTwoForm

/-! ### The exact action shift -/

omit [TopologicalSpace M] in
/-- Rescaling the domain of the stationary cylinder in `s` does not change it. -/
private theorem comp_snd_comp_prodMap (x : ℝ → M) (g : ℝ → ℝ) :
    (fun w : ℝ × ℝ ↦ x w.2) ∘ Prod.map g id = fun w ↦ x w.2 := by
  funext w
  simp

omit [TopologicalSpace M] in
/-- The difference of a Hamiltonian and its normalization by `c(t)` is `-c(t)`, a function of time
alone. -/
private theorem sub_add_const_eq (H : ℝ → M → ℝ) (c : ℝ → ℝ) :
    (H - fun t y ↦ H t y + c t) = fun t _ ↦ -c t := by
  funext t y
  simp

omit [TopologicalSpace M] in
/-- `E⁺(H - (H + c)) = -∫₀¹ c` on a nonempty space. -/
private theorem hoferPlus_sub_add_const [Nonempty M] (H : ℝ → M → ℝ) (c : ℝ → ℝ) :
    hoferPlus (H - fun t y ↦ H t y + c t) = -∫ t in 0..1, c t := by
  rw [sub_add_const_eq, hoferPlus_const, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc, integral_neg]

variable [IsManifold I 1 M] {σ : RoughForm I M ℝ 2}

/-- **The action shift of a stationary cylinder.** Let `σ` be a continuous two-form, `v` a `C¹`
map with initial loop `x = v (0, ·)`, and `G(s, t) = H_t + f(s, t)` for a function `f` of the
domain coordinates. Along the stationary cylinder `u(s, t) = x t` the action changes only through
`f`: the action of `x` for `G(b, ·)` measured against `v` is its action for `G(a, ·)` measured
against `w # v`, minus `∫₀¹ (f(b, t) - f(a, t)) dt`. Here `w # v` (`TauCeti.rectangleTrans`) glues
`u`, rescaled from `[a, b]` to `[0, 1]`, to `v`, as in the action estimates for continuation
cylinders. In particular the action does not change when `f(a, ·) = f(b, ·)`, however large `f`
is in between: the shift is not the integral of the homotopy. -/
theorem cylinderAction_add_eq_cylinderAction_add_sub_integral (hσ : IsSmoothForm I 0 σ)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = x t)
    (f : ℝ × ℝ → ℝ) (hH : IntervalIntegrable (fun t ↦ H t (x t)) volume 0 1)
    (ha : IntervalIntegrable (fun t ↦ f (a, t)) volume 0 1)
    (hb : IntervalIntegrable (fun t ↦ f (b, t)) volume 0 1) :
    cylinderAction σ (fun t y ↦ H t y + f (b, t)) v =
      cylinderAction σ (fun t y ↦ H t y + f (a, t))
          (rectangleTrans ((fun w ↦ x w.2) ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) -
        ∫ t in 0..1, (f (b, t) - f (a, t)) := by
  have hHv : IntervalIntegrable (fun t ↦ H t (v (0, t))) volume 0 1 := by
    simpa only [hv₀] using hH
  have hHw : IntervalIntegrable
      (fun t ↦ H t (rectangleTrans (fun w ↦ x w.2) v (0, t))) volume 0 1 := by
    simpa only [rectangleTrans_apply_zero] using hH
  rw [comp_snd_comp_prodMap, cylinderAction_add_const _ _ hHv hb,
    cylinderAction_add_const _ _ hHw ha, cylinderAction_rectangleTrans_comp_snd hσ H hv hv₀,
    intervalIntegral.integral_sub hb ha]
  ring

/-- **The curvature bound is attained.** Let `ε` be a `C¹` function of `s` and
`G(s, t) = H_t + ε(s)`, whose curvature `∂_s G = ε'(s)` does not depend on `(t, x)`. Along the
stationary cylinder `u(s, t) = x t` over `[a, b]`, the action of `x` for `G(b, ·)` measured against
`v` is exactly its action for `G(a, ·)` measured against `w # v` plus `∫_a^b (-ε')`. So the bound
`c(s) = -ε'(s)` of
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_integral`, the least
one admissible for this homotopy, is attained by the stationary cylinders over the periodic orbits
of `H`, which solve the Floer equation of `G`
(`TauCeti.SmoothTwoForm.mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions`). For
nondecreasing `ε` the homotopy is monotone and lowers the action by `ε(b) - ε(a) ≥ 0`; replacing
`ε` by `-ε` raises it by the same amount. -/
theorem cylinderAction_add_eq_cylinderAction_add_setIntegral_neg_deriv (hσ : IsSmoothForm I 0 σ)
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = x t)
    (hH : IntervalIntegrable (fun t ↦ H t (x t)) volume 0 1) {ε : ℝ → ℝ} (hε : ContDiff ℝ 1 ε)
    (hab : a ≤ b) :
    cylinderAction σ (fun t y ↦ H t y + ε b) v =
      cylinderAction σ (fun t y ↦ H t y + ε a)
          (rectangleTrans ((fun w ↦ x w.2) ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        ∫ s in Icc a b, -deriv ε s := by
  have h := cylinderAction_add_eq_cylinderAction_add_sub_integral (a := a) (b := b) hσ hv hv₀
    (fun z ↦ ε z.1) hH (by simp) (by simp)
  have hint : ∫ s in Icc a b, -deriv ε s = ε a - ε b := by
    rw [integral_neg, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ hε.differentiable one_ne_zero s)
        ((hε.continuous_deriv le_rfl).intervalIntegrable a b)]
    ring
  rw [hint]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h
  linarith

/-- **The bound by `E⁺(H₀ - H₁)` is attained.** Let `σ` be a continuous two-form and `v` a `C¹`
map with initial loop `x = v (0, ·)`, and glue the stationary cylinder `u(s, t) = x t` over
`[a, b]` to `v` as `w # v`. For `H₀ = H` and `H₁ = H + c(t)`, the action of `x` for `H₁` measured
against `v` is exactly its action for `H₀` measured against `w # v` plus
`E⁺(H₀ - H₁) = ∫₀¹ max_y (H₀ - H₁)(t, y) dt = -∫₀¹ c` (`TauCeti.hoferPlus`). When `x` is a
`1`-periodic orbit of `H` and `a ≤ 0 ≤ 1 ≤ b`, the stationary cylinder solves the equation of the
continuation homotopy from `H₀` to `H₁`
(`SmoothTwoForm.mfderiv_comp_snd_add_eq_zero_of_mem_periodicSolutions_continuationHomotopy`), so
the bound of
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferPlus` is attained.
For `c = δ > 0` the homotopy is monotone and the action drops by exactly `δ`; for `c = -δ < 0` it
rises by exactly `δ`. -/
theorem cylinderAction_add_const_eq_cylinderAction_add_hoferPlus [Nonempty M]
    (hσ : IsSmoothForm I 0 σ) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = x t) (hH : IntervalIntegrable (fun t ↦ H t (x t)) volume 0 1)
    {c : ℝ → ℝ} (hc : IntervalIntegrable c volume 0 1) :
    cylinderAction σ (fun t y ↦ H t y + c t) v =
      cylinderAction σ H
          (rectangleTrans ((fun w ↦ x w.2) ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        hoferPlus (H - fun t y ↦ H t y + c t) := by
  have hHv : IntervalIntegrable (fun t ↦ H t (v (0, t))) volume 0 1 := by
    simpa only [hv₀] using hH
  rw [comp_snd_comp_prodMap, cylinderAction_rectangleTrans_comp_snd hσ H hv hv₀,
    cylinderAction_add_const _ _ hHv hc, hoferPlus_sub_add_const]
  ring

/-- **The Hofer norm does not bound the action shift.** For `H₀ = H` and `H₁ = H + c(t)` with
`∫₀¹ c < 0`, the stationary cylinder over the initial loop `x = v (0, ·)` of a
`C¹` map `v`, a solution of the continuation equation
from `H₀` to `H₁` when `x` is a `1`-periodic orbit of `H`, raises the action of `x` by
`-∫₀¹ c > 0`, although `H₀ - H₁` is constant in space and has Hofer norm `0`
(`TauCeti.hoferNorm_const`). So the estimate
`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferNorm` fails
without its hypothesis that `H₀ ≤ H₁` somewhere at each time; the action estimate is one-sided. -/
theorem not_cylinderAction_add_const_le_cylinderAction_add_hoferNorm [Nonempty M]
    (hσ : IsSmoothForm I 0 σ) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = x t) (hH : IntervalIntegrable (fun t ↦ H t (x t)) volume 0 1)
    {c : ℝ → ℝ} (hc : IntervalIntegrable c volume 0 1) (hneg : ∫ t in 0..1, c t < 0) :
    ¬ cylinderAction σ (fun t y ↦ H t y + c t) v ≤
      cylinderAction σ H
          (rectangleTrans ((fun w ↦ x w.2) ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        hoferNorm (H - fun t y ↦ H t y + c t) := by
  rw [cylinderAction_add_const_eq_cylinderAction_add_hoferPlus hσ hv hv₀ hH hc,
    hoferPlus_sub_add_const, sub_add_const_eq, hoferNorm_const]
  linarith

end TauCeti
