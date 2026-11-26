/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.FlatBoundary
public import TauCeti.Analysis.PDE.Regularity.HalfSpace
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.InnerProductSpace.OrthogonalSpanSingleton
import TauCeti.Analysis.PDE.Ellipticity.Extension
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.FlatBoundary
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.PDE.Regularity.Hessian.DivergenceForm
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.Analysis.Sobolev.WeakDeriv.NormalTangential
import TauCeti.MeasureTheory.Function.PreciseRepresentative.HalfSpace

/-!
# Hölder continuity of the second derivatives up to the boundary of a half-space

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, let `0 < α < 1`, and let
`u ∈ H¹₀(H)` be the weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `H`, `u = 0` on `∂H`,

that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H f v` for every `v ∈ H¹₀(H)`, where `a` is uniformly elliptic and
Lipschitz, as a bilinear form, on all of `H`, `a` is uniformly elliptic on a ball `B(y₀, r)` about
a point `y₀` of the boundary hyperplane and its entries are `C¹` with first derivatives `α`-Hölder
there, and `f ∈ L²(H)` is `α`-Hölder up to the boundary there. This file proves that the weak second
derivatives of `u` have `α`-Hölder precise representatives up to the boundary near `y₀`.

* **Tangential directions.** For every `e` with `⟪e, ν⟫ = 0`, the weak derivative `∂ₑu` lies in
  `H¹₀(H)`, and the precise representative of its gradient for the Lebesgue measure on `H` is
  `α`-Hölder on the closed half-ball `closedBall y₀ (r / 4) ∩ {c₀ ≤ ⟪y, ν⟫}`
  (`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient`; this and
  the other declarations named below are in the `TauCeti.PDE` namespace). Since `∇(∂ₑu)` holds
  the derivatives `∂_w ∂ₑu` in every direction `w`, this covers every second derivative with a
  tangential direction, that is all of them but `∂_ν ∂_ν u`.
* **Every direction.** For every `w`, normal ones included, the weak derivative `∂_w u` lies in
  `H¹(H)` and the precise representative of its gradient is `α`-Hölder on the closed half-ball
  `closedBall y₀ (r / 8) ∩ {c₀ ≤ ⟪y, ν⟫}`
  (`exists_hasWeakLineDerivOn_w1p_and_holderOnWith_preciseRepresentative_restrict_gradient`).
* **Near a flat portion of the boundary.** The same holds locally for an open set `Ω` with
  `Ω ∩ B(y₀, r) = H ∩ B(y₀, r)` and a weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω` that
  vanishes on `∂Ω ∩ B(y₀, r)`, with regularity and ellipticity hypotheses on `a` and `f` only on
  `B(y₀, r)` and `f ∈ L²(Ω)`: every `∂_w u` lies in `H¹(Ω ∩ B(y₀, r / 16))`, with gradient equal
  almost everywhere there to a field that is `α`-Hölder on `closedBall y₀ (r / 16) ∩ {c₀ ≤ ⟪y, ν⟫}`
  (`exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq`).

This is the boundary counterpart of interior `C^{2,α}` regularity for divergence-form equations
with `C^{1,α}` coefficients
(`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn`), and
the flat model of Schauder regularity up to a curved boundary: flattening a `C^{2,α}` boundary by
a shear with Jacobian determinant one turns `Δ` into a divergence-form operator with `C^{1,α}`
coefficients on a half-space.

## The argument

* **Tangential derivatives.** Since `a` is Lipschitz on `H`, `u ∈ H²(H)`. Translations along a
  tangential `e` map `H` onto itself, so the difference quotients of `u` along `e` lie in
  `H¹₀(H)` and converge in `H¹(H)` to `∂ₑu`, which therefore lies in `H¹₀(H)`
  (`UniformlyEllipticOn.exists_hasWeakLineDerivOn_of_halfSpace`).
* **`∇u` is Hölder up to the boundary.** Extended by zero to the ball `B = B(y₀, 3r / 4)`, `u`
  vanishes on `B ∖ H` and solves the equation on `B ∩ H` with the bounded datum `f`, so the Schauder
  estimate up to a flat boundary
  (`exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp`) makes
  the precise representative `P` of `∇u` for the Lebesgue measure on `H` `α`-Hölder on
  `closedBall y₀ (r / 2) ∩ {c₀ ≤ ⟪y, ν⟫}`.
* **The equation for `∂ₑu`.** Moving `∂ₑ` across the energy form
  (`energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_sub_setIntegral`) shows that
  `d = ∂ₑu` solves `-∂ᵢ(aⁱʲ ∂ⱼd) = -div G` on `B ∩ H`, with `G = -f e - (∂ₑa) P`
  (`energyFormH1_eq_setIntegral_inner_of_eq_neg_sub`). Products of bounded Hölder
  functions are Hölder, so `G` is `α`-Hölder on the closed half-ball
  (`exists_holderOnWith_smul_neg_sub_toDual_symm_matrixBilinearForm`, applied to `f` composed with
  the fold across the hyperplane, which is `1`-Lipschitz and fixes the closed half-space,
  `TauCeti.lipschitzWith_one_ite_hyperplaneReflection`). Composed with the fold, `G` becomes
  `α`-Hölder on the whole ball `B(y₀, r / 2)` without changing the equation, which only sees
  `B ∩ H`.
* **Schauder for `∂ₑu`.** Since `d ∈ H¹₀(H)`, its zero extension vanishes on `B ∖ H`, and the
  Schauder estimate up to a flat boundary for a divergence datum,
  `exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_matrixBilinearForm`,
  applies to it.
* **The normal direction.** Let `e = ν / ‖ν‖`. Since `u ∈ H²(H)`, the weak derivatives of `u`
  lie in `H¹(H)`, and the equation holds almost everywhere on `B(y₀, r / 4) ∩ H`, where the
  coefficients are `C¹` (`TauCeti.PDE.ae_sum_sum_eq_neg_of_hasWeakLineDerivOn`):
  `∑ᵢⱼ (∂ᵢaⁱʲ ∂ⱼu + aⁱʲ ∂ᵢ∂ⱼu) = -f`. In it every second derivative but `∂ₑ∂ₑu` has a tangential
  direction, by the symmetry of second derivatives
  (`TauCeti.W1p.inner_gradient_ae_eq_of_hasWeakLineDerivOn`), and the coefficient of `∂ₑ∂ₑu` is
  `⟪e, a e⟫ ≥ λ`. Solving for it expresses `∇(∂ₑu)` almost everywhere through `f`, `a`, `∂a`, `∇u`
  and the tangential second derivatives, a field that is `α`-Hölder on the closed half-ball.
* **The precise representative.** A function equal almost everywhere on `B(y₀, ρ) ∩ H` to a field
  continuous on the closed half-ball has that field as its precise representative there
  (`TauCeti.MeasureTheory.preciseRepresentative_restrict_setOf_lt_inner_eq_of_continuousOn`).
  A general direction `w` is `⟪e, w⟫ e` plus a tangential direction.
* **Localization.** Near `closedBall y₀ (3r/4)` the field `a` agrees with a Lipschitz field `a'`
  uniformly elliptic on the whole space (`UniformlyEllipticOn.exists_lipschitzWith_eqOn`). For a
  cutoff `ψ` equal to one near `closedBall y₀ (r / 2)`, the product `ψ u`, extended by zero, lies
  in `H¹₀(H)` and solves `-∂ᵢ(a'ⁱʲ ∂ⱼw) = g` in `H`, where `g = f` and `ψ u = u` on
  `B(y₀, r / 2) ∩ H` since `ψ = 1` near there
  (`exists_isWeakSolutionDirichlet_ae_eq_on_of_inter_eq`). The half-space theorem applies to it on
  `B(y₀, r / 2)`.

## Main declarations

* `exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient`: the
  tangential second derivatives of the solution are `α`-Hölder up to the flat boundary.
* `exists_hasWeakLineDerivOn_w1p_and_holderOnWith_preciseRepresentative_restrict_gradient`: all
  second derivatives of the solution are `α`-Hölder up to the flat boundary.
* `exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq`: all second derivatives
  of a solution vanishing on a flat portion of the boundary of a general domain are `α`-Hölder up
  to that portion.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the `C^{1,α}` estimate up to the boundary) and Lemma 6.18 (`C^{2,α}` regularity
  at the boundary).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.4.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, proof of Theorem 4 (the normal
  second derivative recovered from the equation).
-/

public section

open InnerProductSpace LineDeriv MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ContDiff Distributions Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The zero extension of `w ∈ H¹₀(H)` to the whole space, restricted to an open set `U`. -/
private noncomputable def extendRestrict {H : Opens E} (w : W1p0 volume H 2) (U : Opens E) :
    W1p volume U 2 :=
  W1p.restrictL (le_top : U ≤ ⊤) ((W1p0.extendByZeroL (le_top : H ≤ ⊤) w :
    W1p0 volume (⊤ : Opens E) 2) : W1p volume (⊤ : Opens E) 2)

/-- Restricting `extendRestrict w U` to `U ∩ H` gives the restriction of `w` to `U ∩ H`. -/
private theorem restrictL_extendRestrict {U H : Opens E} (w : W1p0 volume H 2) :
    W1p.restrictL (inf_le_left : U ⊓ H ≤ U) (extendRestrict w U) =
      W1p.restrictL (inf_le_right : U ⊓ H ≤ H) (w : W1p volume H 2) := by
  rw [extendRestrict, W1p.restrictL_restrictL, W1p0.restrictL_extendByZeroL_of_le]

/-- The zero extension of `w ∈ H¹₀(H)`, restricted to an open set `U`, vanishes on `U ∖ H`. -/
private theorem ae_value_extendRestrict_eq_zero {U H : Opens E} (w : W1p0 volume H 2) :
    ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value (extendRestrict w U) x = 0 := by
  filter_upwards [W1p0.value_restrictL_extendByZeroL_ae (le_top : H ≤ ⊤) (le_top : U ≤ ⊤) w]
    with x hx hxH
  rw [extendRestrict, hx, indicator_of_notMem hxH]

/-- On `U ∩ H`, the gradient of `extendRestrict w U` is the gradient of `w`. -/
private theorem gradient_extendRestrict_ae_eq {U H : Opens E} (w : W1p0 volume H 2) :
    (W1p.gradient (extendRestrict w U) : E → E) =ᵐ[volume.restrict ((U : Set E) ∩ H)]
      W1p.gradient (w : W1p volume H 2) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (W1p0.gradient_restrictL_extendByZeroL_ae (le_top : H ≤ ⊤) (le_top : U ≤ ⊤) w),
    ae_restrict_mem (U.isOpen.measurableSet.inter H.isOpen.measurableSet)] with y hy hyUH
  rw [extendRestrict, hy, indicator_of_mem hyUH.2]

/-- At the points of `U`, the precise representative for the Lebesgue measure on `H` of the
gradient of `extendRestrict w U` is that of the gradient of `w`. -/
private theorem preciseRepresentative_gradient_extendRestrict {U H : Opens E}
    (w : W1p0 volume H 2) {x : E} (hx : x ∈ U) :
    preciseRepresentative (volume.restrict (H : Set E))
        (W1p.gradient (extendRestrict w U) : E → E) x =
      preciseRepresentative (volume.restrict (H : Set E))
        (W1p.gradient (w : W1p volume H 2) : E → E) x := by
  refine preciseRepresentative_congr_ae_nhds (U.isOpen.mem_nhds hx) ?_
  rw [Measure.restrict_restrict U.isOpen.measurableSet]
  exact gradient_extendRestrict_ae_eq w

/-- **Step 1: `∇u` is Hölder up to the boundary.** For the solution `u ∈ H¹₀(H)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f`, with `a` uniformly elliptic on `B(y₀, r)` and `α`-Hölder on
`closedBall y₀ (3r / 4)`, and `f` bounded on the points of `H` in that ball, the precise
representative for the Lebesgue measure on `H` of the gradient of the zero extension of `u` to
`B = B(y₀, 3r / 4)` is `α`-Hölder on `closedBall y₀ (r / 2) ∩ {c₀ ≤ ⟪y, ν⟫}`. -/
private theorem exists_holderOnWith_preciseRepresentative_gradient_extendRestrict {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {H B : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} {y₀ : E} {r : ℝ} (hr : 0 < r) (hB : (B : Set E) = ball y₀ (3 * r / 4))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam) {Ka : ℝ≥0}
    (hKa : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closedBall y₀ (3 * r / 4)))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict H)) {Mf : ℝ}
    (hMf : ∀ x ∈ closedBall y₀ (3 * r / 4), x ∈ H → ‖f x‖ ≤ Mf) {u : W1p0 volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 (u : W1p volume H 2) (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x) :
    ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative (volume.restrict (H : Set E))
      (W1p.gradient (extendRestrict u B) : E → E))
      (closedBall y₀ (r / 2) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := by
  set S := closedBall y₀ (r / 2) ∩ {y : E | c₀ ≤ ⟪y, ν⟫_ℝ}
  have hth : thickening (r / 4) S ⊆ ball y₀ (3 * r / 4) :=
    (thickening_subset_of_subset _ inter_subset_left).trans (by
      rw [thickening_closedBall (by positivity) (by positivity)]
      exact ball_subset_ball (by linarith))
  -- The datum `f` is bounded near `S`.
  have hfinf : MemLp f ⊤ (volume.restrict (thickening (r / 4) S ∩ H)) :=
    memLp_top_of_bound (hf.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)) Mf
      (ae_restrict_of_forall_mem (isOpen_thickening.measurableSet.inter H.isOpen.measurableSet)
        fun x hx => hMf x (ball_subset_closedBall (hth hx.1)) hx.2)
  obtain ⟨C, -, h⟩ :=
    exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp
      (n := n) hα hα1 le_rfl le_top (by simpa using hα1.le) (lam := lam) (Lam := Lam)
      (M := Ka * (r / 4) ^ (α : ℝ))
  -- Extended by zero, `u` solves the equation on `B ∩ H` with datum `f` and no divergence part.
  exact ⟨_, h (U := B) (G := 0) (KG := 0) (S := S) (R := r / 4) hν hH (fun x hx => hx.2)
    (hellB.mono_set (hth.trans (ball_subset_ball (by linarith))))
    (hKa.mono (hth.trans ball_subset_closedBall)) (fun x _ y _ => by simp) le_rfl hfinf
    (ae_value_extendRestrict_eq_zero u) (fun φ => by
      rw [restrictL_extendRestrict]
      refine (energyFormH1_restrictL_eq_setIntegral inf_le_right hu
        ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans ?_
      simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_add]
      refine integral_congr_ae ?_
      filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with x hx
      rw [hx]) (by positivity) (hB ▸ hth)⟩

/-- If `f` is `α`-Hölder up to the boundary near each point of the closed half-ball
`B(y₀, r) ∩ {c₀ ≤ ⟪y, ν⟫}`, then `f` composed with the fold across the boundary hyperplane is
`α`-Hölder near each point of the whole ball `B(y₀, r)`. -/
private theorem holderOnWith_comp_fold_ball {α : ℝ≥0} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0) {y₀ : E}
    (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} {f : E → ℝ}
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ})) :
    ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, HolderOnWith L α
      (f ∘ fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y) (ball x ρ) := by
  intro x hx
  obtain ⟨ρ, hρ, L, hL⟩ := hfH _ ⟨mapsTo_ite_hyperplaneReflection_ball hy₀ r hx,
    le_inner_ite_hyperplaneReflection hν c₀ x⟩
  have hF := lipschitzWith_one_ite_hyperplaneReflection ν c₀
  -- The fold is `1`-Lipschitz, so it maps `B(x, ρ)` into the closed half-ball about its image.
  refine ⟨ρ, hρ, L, ?_⟩
  simpa only [NNReal.one_rpow, mul_one] using hL.comp hF.lipschitzOnWith.holderOnWith fun y hy =>
    ⟨(hF.dist_le_mul y x).trans_lt (by rwa [NNReal.coe_one, one_mul]),
      le_inner_ite_hyperplaneReflection hν c₀ y⟩

/-- **Step 1, assembled: `∇u` has a Hölder representative up to the boundary.** Under the
hypotheses of the main theorem on `a` and `f` near `y₀`, the gradient of the solution `u` agrees
almost everywhere on `B(y₀, 3r / 4) ∩ H` with a function that is `α`-Hölder on the closed half-ball
`closedBall y₀ (r / 2) ∩ {c₀ ≤ ⟪y, ν⟫}`, the precise representative of the gradient of the zero
extension of `u` to `B(y₀, 3r / 4)`. -/
private theorem exists_holderOnWith_and_ae_eq_gradient {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {H : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} {y₀ : E}
    (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict H))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p0 volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 (u : W1p volume H 2) (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x) :
    ∃ P : E → E, (∃ C : ℝ≥0, HolderOnWith C α P (closedBall y₀ (r / 2) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ})) ∧
      P =ᵐ[volume.restrict (ball y₀ (3 * r / 4) ∩ H)] W1p.gradient (u : W1p volume H 2) := by
  set B : Opens E := ⟨ball y₀ (3 * r / 4), isOpen_ball⟩
  have hBr : closedBall y₀ (3 * r / 4) ⊆ ball y₀ r := closedBall_subset_ball (by linarith)
  obtain ⟨Ka, hKa⟩ := exists_holderOnWith_matrixBilinearForm_of_contDiffOn isOpen_ball ha
    (isCompact_closedBall y₀ (3 * r / 4)) hBr hα1.le
  -- `f` composed with the fold is Hölder near `closedBall y₀ (3r / 4)`, so `f` is bounded on `H`
  -- there.
  obtain ⟨δf, hδf, -, Mf, -, hMf⟩ :=
    (isCompact_closedBall y₀ (3 * r / 4)).exists_holderOnWith_thickening_and_norm_le
      fun x hx => holderOnWith_comp_fold_ball hν hy₀ hfH x (hBr hx)
  obtain ⟨CP, hP⟩ := exists_holderOnWith_preciseRepresentative_gradient_extendRestrict hα hα1 hν hH
    hr (B := B) rfl hellB hKa hf (fun x hx hxH => by
      simpa only [Function.comp_apply, ((hH x).1 hxH).le, ↓reduceIte] using
        hMf x (self_subset_thickening hδf _ hx)) hu
  -- The precise representative agrees with `∇u` almost everywhere on `B ∩ H`.
  exact ⟨_, ⟨CP, hP⟩, (W1p.gradient_ae_eq_preciseRepresentative_restrict (extendRestrict u B)
    B.isOpen inter_subset_left).symm.trans
    (gradient_extendRestrict_ae_eq u)⟩

/-- **Step 2: the folded datum is Hölder.** If the derivatives of the entries of `a` are
`α`-Hölder near each point of `B(y₀, r)`, `f` is `α`-Hölder up to the boundary near each point of
`B(y₀, r) ∩ {c₀ ≤ ⟪y, ν⟫}` and `P` is `α`-Hölder on the closed half-ball
`S = closedBall y₀ (r / 2) ∩ {c₀ ≤ ⟪y, ν⟫}`, then the datum `G = -f e - (∂ₑa) P`, composed with the
fold across the boundary hyperplane, is `α`-Hölder on the whole ball `B(y₀, r / 2)`. -/
private theorem exists_holderOnWith_datum_comp_fold {α : ℝ≥0} (hα : 0 < α) {ν : E} {c₀ : ℝ}
    (hν : ν ≠ 0) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {y₀ : E} (hy₀ : ⟪y₀, ν⟫_ℝ = c₀)
    {r : ℝ} (hr : 0 < r)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {P : E → E} {CP : ℝ≥0} (hP : HolderOnWith CP α P (closedBall y₀ (r / 2) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    (e : E) :
    ∃ K : ℝ≥0, HolderOnWith K α ((fun x => f x • (-e) - (toDual ℝ E).symm
      (matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e) (P x))) ∘
        fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y) (ball y₀ (r / 2)) := by
  set S := closedBall y₀ (r / 2) ∩ {y : E | c₀ ≤ ⟪y, ν⟫_ℝ}
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_id.inner continuous_const))
  -- The datum built from `f` composed with the fold is Hölder on `S`.
  obtain ⟨K, hG⟩ := exists_holderOnWith_smul_neg_sub_toDual_symm_matrixBilinearForm hα hda
    (holderOnWith_comp_fold_ball hν hy₀ hfH) hSc
    (inter_subset_left.trans (closedBall_subset_ball (by linarith))) hP e
  -- The fold is `1`-Lipschitz and maps `B(y₀, r / 2)` into `S`.
  have hFs : MapsTo (fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y)
      (ball y₀ (r / 2)) S := fun y hy =>
    ⟨ball_subset_closedBall (mapsTo_ite_hyperplaneReflection_ball hy₀ (r / 2) hy),
      le_inner_ite_hyperplaneReflection hν c₀ y⟩
  have h := hG.comp (lipschitzWith_one_ite_hyperplaneReflection ν c₀).lipschitzOnWith.holderOnWith
    hFs
  simp only [NNReal.one_rpow, mul_one] at h
  -- The fold fixes its own values, so folding `f` twice is folding it once.
  refine ⟨K, h.congr fun y _ => ?_⟩
  simp only [Function.comp_apply, le_inner_ite_hyperplaneReflection hν c₀ y, ↓reduceIte]

/-- **Step 3: the equation for `∂ₑu`.** Let `u ∈ H¹(H)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `H`, with the
entries of `a` `C¹` on an open set `W` containing the closure of `B ∩ H` and `B ∩ H` relatively
compact, and let `d ∈ H¹₀(H)` be the weak derivative of `u` along `e`. If `P = ∇u` almost
everywhere on `B ∩ H`, then the zero extension of `d` to `B` solves `-∂ᵢ(aⁱʲ ∂ⱼd) = -div G` on
`B ∩ H`, for `G` the datum `-f e - (∂ₑa) P` composed with the fold, which is the identity on
`H`. -/
private theorem energyFormH1_extendRestrict_eq_setIntegral_inner {H B : Opens E} {W : Set E}
    {ν : E} {c₀ : ℝ} (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hBc : IsCompact (closure (((B ⊓ H : Opens E)) : Set E))) (hW : IsOpen W)
    (hBW : closure (((B ⊓ H : Opens E)) : Set E) ⊆ W)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) W) {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict H)) {u : W1p volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 u (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x)
    {e : E} {d : W1p0 volume H 2}
    (hd : HasWeakLineDerivOn volume H (W1p.value u) (W1p.value (d : W1p volume H 2)) e)
    {P : E → E} (hP : P =ᵐ[volume.restrict (((B ⊓ H : Opens E)) : Set E)] W1p.gradient u)
    (φ : 𝓓(B ⊓ H, ℝ)) :
    energyFormH1 a 0 0 (W1p.restrictL inf_le_left (extendRestrict d B))
        (W1p.ofTestFunctionₗ volume (B ⊓ H) 2 φ) =
      ∫ x in B ⊓ H, ⟪((fun x => f x • (-e) - (toDual ℝ E).symm
        (matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e) (P x))) ∘
          fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y) x,
            ∇ (φ : E → ℝ) x⟫_ℝ := by
  have hdV : HasWeakLineDerivOn volume (B ⊓ H)
      (W1p.value (W1p.restrictL (le_refl (B ⊓ H))
        (W1p.restrictL (inf_le_right : B ⊓ H ≤ H) u)))
      (W1p.value (W1p.restrictL (inf_le_right : B ⊓ H ≤ H) (d : W1p volume H 2))) e := by
    rw [W1p.restrictL_self]
    exact ((hd.mono inf_le_right).congr_ae
      (W1p.value_restrictL_ae inf_le_right _).symm).congr_ae_deriv
        (W1p.value_restrictL_ae inf_le_right _).symm
  rw [restrictL_extendRestrict]
  -- The coefficients only need to be `C¹` near `B ∩ H`: `u` restricts to a solution on `B ∩ H`.
  refine (energyFormH1_eq_setIntegral_inner_of_eq_neg_sub hBc le_rfl hW hBW ha
    (hf.mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
    (hP.trans (W1p.gradient_restrictL_ae inf_le_right u).symm)
    (energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_sub_setIntegral le_rfl
      (fun i j => (ha i j).mono (subset_closure.trans hBW))
      (energyFormH1_restrictL_eq_setIntegral inf_le_right hu) hdV φ)).trans (integral_congr_ae ?_)
  -- On `H` the fold is the identity.
  filter_upwards [ae_restrict_mem (B ⊓ H).isOpen.measurableSet] with x hx
  have hxν : c₀ ≤ ⟪x, ν⟫_ℝ := ((hH x).1 hx.2).le
  simp only [Function.comp_apply, hxν, ↓reduceIte]

/-- **Tangential second derivatives are Hölder up to a flat boundary.** Let `0 < α < 1`, let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `u ∈ H¹₀(H)` be a weak solution of the Dirichlet
problem `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `H`, that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H f v` for every `v ∈ H¹₀(H)`.
Suppose that `a` is uniformly elliptic with constants `λ, Λ` on `H` and Lipschitz there, and that
`f ∈ L²(H)`. Let `y₀` lie on the boundary hyperplane and `r > 0`, and suppose that the entries of
`a` are `C¹` on `B(y₀, r)`, that `a` is uniformly elliptic on `B(y₀, r)`, that the derivatives
of its entries are `α`-Hölder near each point of `B(y₀, r)`, and that `f` is `α`-Hölder up to the
boundary near each point of `B(y₀, r) ∩ {c₀ ≤ ⟪y, ν⟫}`: on `B(x, ρ) ∩ {c₀ ≤ ⟪y, ν⟫}` for some
`ρ > 0`. The values of `f` outside the closed half-space play no role.

Then for every tangential direction `e`, `⟪e, ν⟫ = 0`, the weak derivative `∂ₑu` lies in `H¹₀(H)`,
and the precise representative of its gradient for the Lebesgue measure on `H` is `α`-Hölder on
the closed half-ball `closedBall y₀ (r / 4) ∩ {c₀ ≤ ⟪y, ν⟫}`. At the points of `H` the precise
representative is `∇∂ₑu` almost everywhere, so the second derivatives `∂_w ∂ₑu` extend
`α`-Hölder continuously up to the flat boundary near `y₀`. -/
theorem exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {H : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} {K : ℝ≥0} (hell : UniformlyEllipticOn (H : Set E) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) H) {y₀ : E}
    (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict H))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p0 volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 (u : W1p volume H 2) (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x)
    {e : E} (he : ⟪e, ν⟫_ℝ = 0) :
    ∃ d : W1p0 volume H 2, HasWeakLineDerivOn volume H (W1p.value (u : W1p volume H 2))
        (W1p.value (d : W1p volume H 2)) e ∧
      ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative (volume.restrict (H : Set E))
        (W1p.gradient (d : W1p volume H 2) : E → E))
        (closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := by
  -- `∂ₑu` exists and lies in `H¹₀(H)`, since `u ∈ H²(H)`.
  obtain ⟨d, hd⟩ := hell.exists_hasWeakLineDerivOn_of_halfSpace hν hH hK
    ((isWeakSolutionDirichlet_iff (hf.toLp f) u).2 fun v => (hu v).trans
      (integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx]))) he
  refine ⟨d, hd, ?_⟩
  -- The ball `B = B(y₀, 3r / 4)` and the coefficients on it.
  set B : Opens E := ⟨ball y₀ (3 * r / 4), isOpen_ball⟩
  have hBr : closedBall y₀ (3 * r / 4) ⊆ ball y₀ r := closedBall_subset_ball (by linarith)
  have hcl : closure (((B ⊓ H : Opens E)) : Set E) ⊆ closedBall y₀ (3 * r / 4) :=
    (closure_mono inter_subset_left).trans closure_ball_subset_closedBall
  obtain ⟨Ka, hKa⟩ := exists_holderOnWith_matrixBilinearForm_of_contDiffOn isOpen_ball ha
    (isCompact_closedBall y₀ (3 * r / 4)) hBr hα1.le
  -- Step 1: `∇u` agrees almost everywhere on `B ∩ H` with a function `P` that is Hölder up to the
  -- boundary.
  obtain ⟨P, ⟨CP, hP⟩, hPV⟩ :=
    exists_holderOnWith_and_ae_eq_gradient hα hα1 hν hH hy₀ hr ha hellB hf hfH hu
  -- Step 2: the folded datum of the equation for `∂ₑu` is Hölder on `B(y₀, r / 2)`.
  obtain ⟨KG, hG⟩ := exists_holderOnWith_datum_comp_fold hα hν hy₀ hr hda hfH hP e
  -- Step 3: the Schauder estimate up to the flat boundary for the zero extension of `∂ₑu`.
  set S := closedBall y₀ (r / 4) ∩ {y : E | c₀ ≤ ⟪y, ν⟫_ℝ}
  have hth : thickening (r / 8) S ⊆ ball y₀ (r / 2) :=
    (thickening_subset_of_subset _ inter_subset_left).trans (by
      rw [thickening_closedBall (by positivity) (by positivity)]
      exact ball_subset_ball (by linarith))
  have hhalf : ball y₀ (r / 2) ⊆ ball y₀ (3 * r / 4) := ball_subset_ball (by linarith)
  obtain ⟨C, -, h⟩ :=
    exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_matrixBilinearForm
      (n := n) hα hα1 (lam := lam) (Lam := Lam) (M := Ka * (r / 8) ^ (α : ℝ))
  have hPB := h (U := B) (u := extendRestrict d B) (S := S) (R := r / 8) hν hH (fun x hx => hx.2)
    (hellB.mono_set ((hth.trans hhalf).trans (ball_subset_ball (by linarith))))
    (hKa.mono ((hth.trans hhalf).trans ball_subset_closedBall)) (hG.mono hth) le_rfl
    (ae_value_extendRestrict_eq_zero d)
    (energyFormH1_extendRestrict_eq_setIntegral_inner hH
      ((isCompact_closedBall y₀ (3 * r / 4)).of_isClosed_subset isClosed_closure hcl) isOpen_ball
      (hcl.trans hBr) ha hf hu hd hPV)
    (by positivity) (hth.trans hhalf)
  -- On the closed half-ball, the precise representatives of the gradients of `∂ₑu` and of its
  -- extension agree. Membership in the `Opens` `B` unfolds to membership in its ball, which the
  -- `show` makes explicit.
  exact ⟨_, hPB.congr fun x hx => preciseRepresentative_gradient_extendRestrict d
    (show x ∈ ball y₀ (3 * r / 4) from closedBall_subset_ball (by linarith) hx.1)⟩

/-! ### Every second derivative -/

/-- **Solving the equation for the normal second derivative, pointwise.** Let `e` be a unit vector,
`P` the orthogonal projection onto `(ℝ ∙ e)ᗮ` and `(bᵢ)` the standard basis. Suppose that the
vector `v`, the gradient of `∂ₑu`, and the vectors `t i`, the gradients of `∂_{P bᵢ} u`, satisfy the
symmetry `⟪v, P bᵢ⟫ = ⟪t i, e⟫` of second derivatives, and that the equation
`∑ᵢⱼ (Xᵢⱼ + Aᵢⱼ ∂ᵢ∂ⱼu) = -s` holds with `∂ᵢ∂ⱼu = ⟪⟪e, bⱼ⟫ v + t j, bᵢ⟫`. If `⟪e, A e⟫ ≠ 0`, then
`v` is determined by `s`, `X`, `A` and the `t i`: its component along `e` is
`⟪e, A e⟫⁻¹ (-s - ∑ᵢⱼ (Xᵢⱼ + Aᵢⱼ (⟪e, bⱼ⟫ ⟪t i, e⟫ + ⟪t j, bᵢ⟫)))`, and its components along `bₖ`
orthogonal to `e` are `⟪t k, e⟫`. -/
private theorem eq_smul_add_sum_of_sum_sum_eq_neg {e : E} (he : ‖e‖ = 1)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : matrixBilinearForm A e e ≠ 0)
    {X : Fin (n + 1) → Fin (n + 1) → ℝ} {s : ℝ} {v : E} {t : Fin (n + 1) → E}
    (hvt : ∀ i, ⟪v, (ℝ ∙ e)ᗮ.starProjection (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)⟫_ℝ =
      ⟪t i, e⟫_ℝ)
    (h : ∑ i, ∑ j, (X i j + A i j * ⟪⟪e, EuclideanSpace.basisFun (Fin (n + 1)) ℝ j⟫_ℝ • v + t j,
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ i⟫_ℝ) = -s) :
    v = ((matrixBilinearForm A e e)⁻¹ * (-s - ∑ i, ∑ j,
        (X i j + A i j * (⟪e, EuclideanSpace.basisFun (Fin (n + 1)) ℝ j⟫_ℝ * ⟪t i, e⟫_ℝ +
          ⟪t j, EuclideanSpace.basisFun (Fin (n + 1)) ℝ i⟫_ℝ)))) • e +
      ∑ k, ⟪t k, e⟫_ℝ • EuclideanSpace.basisFun (Fin (n + 1)) ℝ k := by
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  set P := (ℝ ∙ e)ᗮ.starProjection
  have hdec := inner_smul_add_starProjection_eq ℝ he
  -- `⟪v, bᵢ⟫ = ⟪e, bᵢ⟫ ⟪v, e⟫ + ⟪t i, e⟫`.
  have hvb (i : Fin (n + 1)) : ⟪v, b i⟫_ℝ = ⟪e, b i⟫_ℝ * ⟪v, e⟫_ℝ + ⟪t i, e⟫_ℝ := by
    conv_lhs => rw [← hdec (b i)]
    rw [inner_add_right, real_inner_smul_right, hvt, mul_comm]
  -- The coefficient of `⟪v, e⟫` is `⟪e, A e⟫ = ∑ᵢⱼ ⟪e, bᵢ⟫ Aᵢⱼ ⟪e, bⱼ⟫`.
  have hAe : matrixBilinearForm A e e = ∑ i, ∑ j, A i j * (⟪e, b j⟫_ℝ * ⟪e, b i⟫_ℝ) := by
    simp only [matrixBilinearForm_apply, dotProduct, Matrix.mulVec, b,
      EuclideanSpace.inner_basisFun_real, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : matrixBilinearForm A e e * ⟪v, e⟫_ℝ = -s - ∑ i, ∑ j,
      (X i j + A i j * (⟪e, b j⟫_ℝ * ⟪t i, e⟫_ℝ + ⟪t j, b i⟫_ℝ)) := by
    rw [← h, hAe, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, inner_add_left, real_inner_smul_left, hvb]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- The components of `P v` are `⟪P v, bₖ⟫ = ⟪v, P bₖ⟫ = ⟪t k, e⟫`.
  have hPv : P v = ∑ k, ⟪t k, e⟫_ℝ • b k := by
    conv_lhs => rw [← b.sum_repr' (P v)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm, Submodule.inner_starProjection_left_eq_right, hvt]
  calc v = ⟪e, v⟫_ℝ • e + P v := (hdec v).symm
    _ = _ := by rw [hPv, real_inner_comm, (eq_inv_mul_iff_mul_eq₀ hA).2 key]

/-- The candidate for the gradient of the normal derivative `∂ₑu`, for a unit normal `e`: its
component along `e` is `∂ₑ∂ₑu` solved for from the equation
`∑ᵢⱼ (∂ᵢaⁱʲ ∂ⱼu + aⁱʲ ∂ᵢ∂ⱼu) = -f`, with `P` in place of `∇u` and `g i` in place of the gradient of
the tangential derivative `∂_{P bᵢ}u`, and its components along the `bₖ` orthogonal to `e` are the
tangential derivatives `⟪g k, e⟫` of `∂ₑu`. -/
private noncomputable def normalField (a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (f : E → ℝ)
    (P : E → E) (g : Fin (n + 1) → E → E) (e x : E) : E :=
  ((matrixBilinearForm (a x) e e)⁻¹ * (-f x - ∑ i, ∑ j,
    (fderiv ℝ (fun y => a y i j) x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i) *
        ⟪P x, EuclideanSpace.basisFun (Fin (n + 1)) ℝ j⟫_ℝ +
      a x i j * (⟪e, EuclideanSpace.basisFun (Fin (n + 1)) ℝ j⟫_ℝ * ⟪g i x, e⟫_ℝ +
        ⟪g j x, EuclideanSpace.basisFun (Fin (n + 1)) ℝ i⟫_ℝ)))) • e +
    ∑ k, ⟪g k x, e⟫_ℝ • EuclideanSpace.basisFun (Fin (n + 1)) ℝ k

/-- **The candidate field is Hölder** on a compact set `S` on which `f`, the entries of `a` and
their derivatives, `⟪e, a e⟫⁻¹`, `P` and the `g k` are `α`-Hölder: it is built from them by sums and
products. -/
private theorem exists_holderOnWith_normalField {α : ℝ≥0} (hα : 0 < α) {S : Set E}
    (hSc : IsCompact S) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {f : E → ℝ} {P : E → E}
    {g : Fin (n + 1) → E → E} {e : E} (hf : ∃ C, HolderOnWith C α (fun x => -f x) S)
    (ha : ∀ i j, ∃ C, HolderOnWith C α (fun x => a x i j) S)
    (hda : ∀ i j, ∃ C, HolderOnWith C α
      (fun x => fderiv ℝ (fun y => a y i j) x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)) S)
    (hinv : ∃ C, HolderOnWith C α (fun x => (matrixBilinearForm (a x) e e)⁻¹) S)
    (hP : ∃ C, HolderOnWith C α P S) (hg : ∀ k, ∃ C, HolderOnWith C α (g k) S) :
    ∃ C, HolderOnWith C α (normalField a f P g e) S := by
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hadd : ∀ {φ ψ : E → ℝ}, (∃ C, HolderOnWith C α φ S) → (∃ C, HolderOnWith C α ψ S) →
      ∃ C, HolderOnWith C α (fun x => φ x + ψ x) S := fun ⟨_, hφ⟩ ⟨_, hψ⟩ => ⟨_, hφ.add hψ⟩
  have hmul : ∀ {φ ψ : E → ℝ}, (∃ C, HolderOnWith C α φ S) → (∃ C, HolderOnWith C α ψ S) →
      ∃ C, HolderOnWith C α (fun x => φ x * ψ x) S := fun ⟨_, hφ⟩ ⟨_, hψ⟩ =>
    ContinuousLinearMap.exists_holderOnWith_comp₂_of_isCompact (ContinuousLinearMap.mul ℝ ℝ)
      hSc hα hφ hψ
  have hsum : ∀ {φ : Fin (n + 1) → E → ℝ}, (∀ i, ∃ C, HolderOnWith C α (φ i) S) →
      ∃ C, HolderOnWith C α (fun x => ∑ i, φ i x) S := fun h => by
    choose C hC using h
    exact ⟨_, HolderOnWith.sum (s := Finset.univ) fun i _ => hC i⟩
  have hinner : ∀ {F : E → E}, (∃ C, HolderOnWith C α F S) → ∀ w : E,
      ∃ C, HolderOnWith C α (fun x => ⟪F x, w⟫_ℝ) S := fun ⟨_, hF⟩ w =>
    ⟨_, ((innerSL ℝ w).lipschitzWith.comp_holderOnWith hF).congr fun x _ => by
      simp [real_inner_comm]⟩
  have hsmul : ∀ {φ : E → ℝ}, (∃ C, HolderOnWith C α φ S) → ∀ w : E,
      ∃ C, HolderOnWith C α (fun x => φ x • w) S := fun ⟨_, hφ⟩ w =>
    ⟨_, ((ContinuousLinearMap.toSpanSingleton ℝ w).lipschitzWith.comp_holderOnWith hφ).congr
      fun x _ => by simp⟩
  have hconst (c : ℝ) : ∃ C, HolderOnWith C α (fun _ : E => c) S := ⟨0, fun x _ y _ => by simp⟩
  -- The component along `e`, then the tangential components.
  obtain ⟨CN, hN⟩ := hmul hinv (hadd hf (by
    obtain ⟨C, h⟩ := hsum fun i => hsum fun j => hadd (hmul (hda i j) (hinner hP (b j)))
      (hmul (ha i j) (hadd (hmul (hconst ⟪e, b j⟫_ℝ) (hinner (hg i) e)) (hinner (hg j) (b i))))
    exact ⟨C, h.neg⟩))
  obtain ⟨C₁, h₁⟩ := hsmul ⟨CN, hN⟩ e
  choose C₂ h₂ using fun k => hsmul (hinner (hg k) e) (b k)
  exact ⟨_, (h₁.add (HolderOnWith.sum (s := Finset.univ) fun k _ => h₂ k)).congr fun x _ => by
    simp only [normalField, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, b]⟩

/-- **The ingredients of the candidate field are Hölder.** Under the hypotheses of the main
theorem on `a` and `f` near `y₀`, on the compact closed half-ball
`S = closedBall y₀ (r / 4) ∩ {c₀ ≤ ⟪y, ν⟫}` the functions `-f`, the entries of `a` and their
derivatives and `⟪e, a e⟫⁻¹`, for a unit vector `e`, are `α`-Hölder; so, if `P` and the `g k` are
`α`-Hölder on `S`, then so is the candidate field `normalField a f P g e`. -/
private theorem exists_holderOnWith_normalField_closedBall {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {ν : E} {c₀ : ℝ} (hν : ν ≠ 0) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {y₀ : E} (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {e : E} (he : ‖e‖ = 1) {P : E → E} {g : Fin (n + 1) → E → E}
    (hP : ∃ C, HolderOnWith C α P (closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    (hg : ∀ k, ∃ C, HolderOnWith C α (g k) (closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ})) :
    ∃ C, HolderOnWith C α (normalField a f P g e)
      (closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := by
  set S : Set E := closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_id.inner continuous_const))
  have hSr : S ⊆ ball y₀ r := inter_subset_left.trans (closedBall_subset_ball (by linarith))
  refine exists_holderOnWith_normalField hα hSc ?_ (fun i j =>
    ((ha i j).locallyLipschitzOn (convex_ball y₀ r)).exists_holderOnWith_of_isCompact hα1.le hSc
      hSr) (fun i j => ?_) ?_ hP hg
  · -- `f` composed with the fold is Hölder near `S`, and the fold fixes `S`.
    obtain ⟨δ, hδ, L, -, hL, -⟩ := hSc.exists_holderOnWith_thickening_and_norm_le
      fun x hx => holderOnWith_comp_fold_ball hν hy₀ hfH x (hSr hx)
    exact ⟨L, ((hL.mono (self_subset_thickening hδ S)).neg).congr fun x hx => by
      simp only [Pi.neg_apply, Function.comp_apply, hx.2.out, ↓reduceIte]⟩
  · obtain ⟨δ, hδ, L, -, hL, -⟩ := hSc.exists_holderOnWith_thickening_and_norm_le
      (f := fderiv ℝ fun y => a y i j) fun x hx => by
        obtain ⟨ρ, hρ, L, hL⟩ := hda x (hSr hx)
        exact ⟨ρ, hρ, L, hL i j⟩
    exact ⟨_, (ContinuousLinearMap.apply ℝ ℝ _).lipschitzWith.comp_holderOnWith
      (hL.mono (self_subset_thickening hδ S))⟩
  · -- `⟪e, a e⟫ ≥ λ`, so its reciprocal is Lipschitz and bounded on `S`.
    obtain ⟨K', hK'⟩ := ((locallyLipschitzOn_matrixBilinearForm_of_contDiffOn isOpen_ball
      ha).mono hSr).exists_lipschitzOnWith_of_compact hSc
    have he0 : e ≠ 0 := fun h => by simp [h] at he
    exact ⟨_, (lipschitzOnWith_inv_matrixBilinearForm_self (hellB.mono_set hSr) hK'
      he0).holderOnWith_of_norm_le (M := (lam * ‖e‖ ^ 2)⁻¹.toNNReal) (fun x hx =>
        (norm_inv_matrixBilinearForm_self_le (hellB.mono_set hSr) hx e).trans
          (Real.le_coe_toNNReal _)) hα1.le⟩

/-- **The gradient of the normal derivative agrees with the candidate field.** Let `e` be a unit
normal of `H`, let `u` solve the equation on `H` with `a` `C¹` and elliptic on `B(y₀, r)`, let `d`
be the weak derivative of `u` along `e` and `dt k ∈ H¹₀(H)` that along the tangential direction
`P bₖ`, with `P` the orthogonal projection onto `(ℝ ∙ e)ᗮ`. If `∇u = P'` and `∇(dt k) = g k`
almost everywhere on `B(y₀, r / 4) ∩ H`, then `∇d = normalField a f P' g e` there: the equation
holds almost everywhere on `B(y₀, r / 4) ∩ H`, and is solved for `∂ₑ∂ₑu` by
`eq_smul_add_sum_of_sum_sum_eq_neg`. -/
private theorem gradient_ae_eq_normalField {H : Opens E} {e : E} (he : ‖e‖ = 1)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} {y₀ : E} {r : ℝ} (hr : 0 < r)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict H)) {u : W1p0 volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 (u : W1p volume H 2) (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x)
    {d : W1p volume H 2} (hd : HasWeakLineDerivOn volume H (W1p.value (u : W1p volume H 2))
      (W1p.value d) e)
    {dt : Fin (n + 1) → W1p0 volume H 2}
    (hdt : ∀ k, HasWeakLineDerivOn volume H (W1p.value (u : W1p volume H 2))
      (W1p.value (dt k : W1p volume H 2))
        ((ℝ ∙ e)ᗮ.starProjection (EuclideanSpace.basisFun (Fin (n + 1)) ℝ k)))
    {P' : E → E} (hP' : P' =ᵐ[volume.restrict (ball y₀ (r / 4) ∩ H)]
      W1p.gradient (u : W1p volume H 2))
    {g : Fin (n + 1) → E → E} (hg : ∀ k, (W1p.gradient (dt k : W1p volume H 2) : E → E)
      =ᵐ[volume.restrict (ball y₀ (r / 4) ∩ H)] g k) :
    W1p.gradient d =ᵐ[volume.restrict (ball y₀ (r / 4) ∩ H)] normalField a f P' g e := by
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  set V : Opens E := ⟨ball y₀ (r / 4), isOpen_ball⟩ ⊓ H
  have hVH : V ≤ H := inf_le_right
  have hVr : (V : Set E) ⊆ ball y₀ r := inter_subset_left.trans (ball_subset_ball (by linarith))
  have hVsub : (V : Set E) ⊆ H := inter_subset_right
  -- The coordinate derivatives `∂ⱼu = ⟪e, bⱼ⟫ ∂ₑu + ∂_{P bⱼ}u`.
  have hDf (j : Fin (n + 1)) : HasWeakLineDerivOn volume H (W1p.value (u : W1p volume H 2))
      (W1p.value (⟪e, b j⟫_ℝ • d + (dt j : W1p volume H 2))) (b j) :=
    by rw [W1p.value_add, W1p.value_smul]; exact hd.smul_add_of_normal_tangential he (hdt j)
  -- The equation holds almost everywhere on `V`, where the coefficients are `C¹`.
  have hstrong := ae_sum_sum_eq_neg_of_hasWeakLineDerivOn (fun i j => (ha i j).mono hVr)
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((hf.mono_measure
      (Measure.restrict_mono hVsub le_rfl)).locallyIntegrable one_le_two))
    (u := W1p.restrictL hVH (u : W1p volume H 2))
    (fun φ => (energyFormH1_restrictL_eq_setIntegral hVH hu
      ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans (integral_congr_ae (by
        filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with x hx
        rw [hx])))
    (D := fun j => W1p.restrictL hVH (⟪e, b j⟫_ℝ • d + (dt j : W1p volume H 2)))
    (fun j => (((hDf j).mono hVH).congr_ae (W1p.value_restrictL_ae hVH _).symm).congr_ae_deriv
      (W1p.value_restrictL_ae hVH _).symm)
  -- At almost every point of `V`, solve the equation for `∂ₑ∂ₑu`.
  filter_upwards [hstrong, W1p.gradient_restrictL_ae hVH (u : W1p volume H 2),
    ae_all_iff.2 fun j => W1p.gradient_restrictL_ae hVH (⟪e, b j⟫_ℝ • d + (dt j : W1p volume H 2)),
    ae_restrict_of_ae_restrict_of_subset hVsub (ae_all_iff.2 fun j =>
      W1p.gradient_add_ae (⟪e, b j⟫_ℝ • d) (dt j : W1p volume H 2)),
    ae_restrict_of_ae_restrict_of_subset hVsub (ae_all_iff.2 fun j =>
      W1p.gradient_smul_ae ⟪e, b j⟫_ℝ d),
    ae_restrict_of_ae_restrict_of_subset hVsub (ae_all_iff.2 fun i =>
      W1p.inner_gradient_ae_eq_of_hasWeakLineDerivOn hd (hdt i)),
    ae_all_iff.2 hg, hP', ae_restrict_mem V.isOpen.measurableSet]
    with x hS hU hD hadd hsmul hsym hgx hPx hxV
  have hA : matrixBilinearForm (a x) e e ≠ 0 := by
    have h := hellB.lower_bound (hVr hxV) e
    rw [← matrixBilinearForm_self, he, one_pow, mul_one] at h
    exact (hellB.pos.trans_le h).ne'
  simp only [hU, hD, hadd, hsmul, Pi.add_apply, Pi.smul_apply, hgx, ← hPx] at hS
  simp only [hgx] at hsym
  exact eq_smul_add_sum_of_sum_sum_eq_neg he hA hsym hS

/-- **The normal derivative and a Hölder field its gradient agrees with.** Under the hypotheses of
`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient`, the weak
derivative `d` of `u` along the unit normal `e = ν / ‖ν‖` exists in `H¹(H)`, and its gradient
agrees almost everywhere on `B(y₀, r / 4) ∩ H` with a field `G` that is `α`-Hölder on the closed
half-ball `closedBall y₀ (r / 4) ∩ {c₀ ≤ ⟪y, ν⟫}`. The tangential components of `∇d` are tangential
derivatives of `∂ₑu`, Hölder by the tangential theorem, and the normal component `∂ₑ∂ₑu` is solved
for from the equation `∑ᵢⱼ (∂ᵢaⁱʲ ∂ⱼu + aⁱʲ ∂ᵢ∂ⱼu) = -f`, in which its coefficient `⟪e, a e⟫` is at
least `λ`. -/
private theorem exists_hasWeakLineDerivOn_normal_and_ae_eq_holderOnWith {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {H : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} {K : ℝ≥0} (hell : UniformlyEllipticOn (H : Set E) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) H) {y₀ : E}
    (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict H))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p0 volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 (u : W1p volume H 2) (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x) :
    ∃ d : W1p volume H 2, HasWeakLineDerivOn volume H (W1p.value (u : W1p volume H 2))
        (W1p.value d) (‖ν‖⁻¹ • ν) ∧
      ∃ G : E → E, (∃ C : ℝ≥0, HolderOnWith C α G
          (closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ})) ∧
        W1p.gradient d =ᵐ[volume.restrict (ball y₀ (r / 4) ∩ H)] G := by
  set b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  set e : E := ‖ν‖⁻¹ • ν
  have he : ‖e‖ = 1 := norm_smul_inv_norm hν
  -- The normal derivative `d = ∂ₑu ∈ H¹(H)`, from `H²` regularity.
  obtain ⟨d, hd⟩ := hell.exists_hasWeakLineDerivOn_w1p_of_halfSpace hν hH hK
    ((isWeakSolutionDirichlet_iff (hf.toLp f) u).2 fun v => (hu v).trans
      (integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx]))) e
  -- The tangential derivatives `dₖ = ∂_{P bₖ} u ∈ H¹₀(H)`, whose gradients have the Hölder
  -- representatives `gₖ` on the closed half-ball, and the Hölder representative `Pu` of `∇u`.
  choose dt hdt Ct hCt using fun k =>
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient hα hα1 hν hH
      hell hK hy₀ hr ha hellB hda hf hfH hu
        (inner_starProjection_orthogonal_singleton_smul_eq_zero ℝ
          (inv_ne_zero (norm_ne_zero_iff.2 hν)) ν (b k))
  obtain ⟨Pu, ⟨CPu, hPu⟩, hPuae⟩ :=
    exists_holderOnWith_and_ae_eq_gradient hα hα1 hν hH hy₀ hr ha hellB hf hfH hu
  refine ⟨d, hd, _, exists_holderOnWith_normalField_closedBall hα hα1 hν hy₀ hr ha hellB hda hfH
    he ⟨CPu, hPu.mono (inter_subset_inter_left _ (closedBall_subset_closedBall (by linarith)))⟩
    fun k => ⟨Ct k, hCt k⟩, gradient_ae_eq_normalField he hr ha hellB hf hu hd hdt
    (ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_left _ (ball_subset_ball (by linarith))) hPuae)
    fun k => W1p.gradient_ae_eq_preciseRepresentative_restrict (dt k : W1p volume H 2)
      isOpen_ball inter_subset_right⟩

/-- **Every second derivative is Hölder up to a flat boundary.** Let `0 < α < 1`, let
`H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `u ∈ H¹₀(H)` be a weak solution of the Dirichlet
problem `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `H`, that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H f v` for every `v ∈ H¹₀(H)`.
Suppose that `a` is uniformly elliptic with constants `λ, Λ` on `H` and Lipschitz there, and that
`f ∈ L²(H)`. Let `y₀` lie on the boundary hyperplane and `r > 0`, and suppose that the entries of
`a` are `C¹` on `B(y₀, r)`, that `a` is uniformly elliptic on `B(y₀, r)`, that the derivatives
of its entries are `α`-Hölder near each point of `B(y₀, r)`, and that `f` is `α`-Hölder up to the
boundary near each point of `B(y₀, r) ∩ {c₀ ≤ ⟪y, ν⟫}`.

Then for every direction `w`, normal ones included, the weak derivative `∂_w u` exists in `H¹(H)`,
and the precise representative of its gradient for the Lebesgue measure on `H` is `α`-Hölder on
the closed half-ball `closedBall y₀ (r / 8) ∩ {c₀ ≤ ⟪y, ν⟫}`. So the weak second derivatives of `u`
have `α`-Hölder representatives up to the flat boundary near `y₀`. For a
tangential `w` the derivative `∂_w u` even lies in `H¹₀(H)`, with the Hölder bound on the larger
half-ball `closedBall y₀ (r / 4) ∩ {c₀ ≤ ⟪y, ν⟫}`
(`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient`). -/
theorem exists_hasWeakLineDerivOn_w1p_and_holderOnWith_preciseRepresentative_restrict_gradient
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {H : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} {K : ℝ≥0} (hell : UniformlyEllipticOn (H : Set E) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) H) {y₀ : E}
    (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hellB : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict H))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p0 volume H 2}
    (hu : ∀ v : W1p0 volume H 2, energyFormH1 a 0 0 (u : W1p volume H 2) (v : W1p volume H 2) =
      ∫ x in H, f x * W1p.value (v : W1p volume H 2) x)
    (w : E) :
    ∃ d : W1p volume H 2, HasWeakLineDerivOn volume H (W1p.value (u : W1p volume H 2))
        (W1p.value d) w ∧
      ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative (volume.restrict (H : Set E))
        (W1p.gradient d : E → E)) (closedBall y₀ (r / 8) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := by
  set e : E := ‖ν‖⁻¹ • ν
  have he : ‖e‖ = 1 := norm_smul_inv_norm hν
  obtain ⟨d, hd, G, ⟨C, hG⟩, hdG⟩ := exists_hasWeakLineDerivOn_normal_and_ae_eq_holderOnWith hα
    hα1 hν hH hell hK hy₀ hr ha hellB hda hf hfH hu
  obtain ⟨dτ, hdτ, Cτ, hτ⟩ :=
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient hα hα1 hν hH
      hell hK hy₀ hr ha hellB hda hf hfH hu
        (inner_starProjection_orthogonal_singleton_smul_eq_zero ℝ
          (inv_ne_zero (norm_ne_zero_iff.2 hν)) ν w)
  -- Split `w` into its normal part `⟪e, w⟫ e` and its tangential part.
  refine ⟨⟪e, w⟫_ℝ • d + (dτ : W1p volume H 2),
    by rw [W1p.value_add, W1p.value_smul]; exact hd.smul_add_of_normal_tangential he hdτ, ?_⟩
  · -- The gradient agrees on `B(y₀, r / 4) ∩ H` with `⟪e, w⟫ G + ∇(∂_{P w} u)`, whose precise
    -- representative is Hölder on the closed half-ball of radius `r / 4`.
    set gτ := preciseRepresentative (volume.restrict (H : Set E))
      (W1p.gradient (dτ : W1p volume H 2) : E → E)
    have hGw := (hG.smul ⟪e, w⟫_ℝ).add hτ
    have hae : (W1p.gradient (⟪e, w⟫_ℝ • d + (dτ : W1p volume H 2)) : E → E)
        =ᵐ[volume.restrict (ball y₀ (r / 4) ∩ H)] ⟪e, w⟫_ℝ • G + gτ := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right
          (W1p.gradient_add_ae (⟪e, w⟫_ℝ • d) (dτ : W1p volume H 2)),
        ae_restrict_of_ae_restrict_of_subset inter_subset_right
          (W1p.gradient_smul_ae ⟪e, w⟫_ℝ d), hdG,
        W1p.gradient_ae_eq_preciseRepresentative_restrict (dτ : W1p volume H 2) isOpen_ball
          inter_subset_right]
        with x h1 h2 h3 h4
      simp only [h1, h2, h3, h4, Pi.add_apply, Pi.smul_apply, gτ]
    have hHs : (H : Set E) = {y | c₀ < ⟪y, ν⟫_ℝ} := Set.ext hH
    refine ⟨_, (hGw.mono (inter_subset_inter_left _
      (closedBall_subset_closedBall (by linarith)))).congr fun x hx => ?_⟩
    have h := preciseRepresentative_restrict_setOf_lt_inner_eq_of_continuousOn volume hν hy₀
      (f := (W1p.gradient (⟪e, w⟫_ℝ • d + (dτ : W1p volume H 2)) : E → E))
      (by rw [← hHs]; exact (Lp.memLp _).locallyIntegrable one_le_two) (by rwa [← hHs])
      ((hGw.continuousOn hα).mono (inter_subset_inter_left _ ball_subset_closedBall))
      ⟨closedBall_subset_ball (by linarith) hx.1, hx.2⟩
    rw [← hHs] at h
    exact h.symm

/-! ### Near a flat portion of the boundary -/

/-- **Localizing a solution near a flat portion of the boundary.** Let `Ω` and `H` be open with
`Ω ∩ B(y₀, r) = H ∩ B(y₀, r)`, let `a` be uniformly elliptic with `C¹` entries on `B(y₀, r)`, and
let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω` with `f ∈ L²(Ω)` and vanish on `∂Ω ∩ B(y₀, r)`.
Then there are a Lipschitz field `a'`, uniformly elliptic on the whole space with the constants of
`a` and equal to `a` on `B(y₀, r / 2)`, a forcing `g ∈ L²(H)` equal to `f` on `B(y₀, r / 2)`, and
a weak solution `w ∈ H¹₀(H)` of `-∂ᵢ(a'ⁱʲ ∂ⱼw) = g` in `H` that agrees with `u` on
`Ω ∩ B(y₀, r / 2)`. -/
private theorem exists_localized_problem {H Ω : Opens E} {y₀ : E} {r : ℝ} (hr : 0 < r)
    (hΩ : (Ω : Set E) ∩ ball y₀ r = (H : Set E) ∩ ball y₀ r)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hell : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x) :
    ∃ a' : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, ∃ K : ℝ≥0,
      UniformlyEllipticOn univ a' lam Lam ∧ LipschitzWith K (fun x => matrixBilinearForm (a' x)) ∧
      EqOn a' a (ball y₀ (r / 2)) ∧ ∃ g : E → ℝ, MemLp g 2 (volume.restrict H) ∧
      EqOn g f (ball y₀ (r / 2)) ∧ ∃ w : W1p0 volume H 2,
        (∀ v : W1p0 volume H 2, energyFormH1 a' 0 0 (w : W1p volume H 2) (v : W1p volume H 2) =
          ∫ x in H, g x * W1p.value (v : W1p volume H 2) x) ∧
        W1p.value (w : W1p volume H 2) =ᵐ[volume.restrict ((Ω : Set E) ∩ ball y₀ (r / 2))]
          W1p.value u := by
  classical
  -- Near `closedBall y₀ (3r/4)`, `a` agrees with a Lipschitz field `a'` elliptic everywhere.
  obtain ⟨a', K, U, hSU, hUB, hell', hK', haa'⟩ :=
    hell.exists_lipschitzWith_eqOn (Omega := ⟨ball y₀ r, isOpen_ball⟩)
      (locallyLipschitzOn_matrixBilinearForm_of_contDiffOn isOpen_ball ha)
      (isCompact_closedBall y₀ (3 * r / 4)) (closedBall_subset_ball (by linarith))
  have hUr : (U : Set E) ⊆ ball y₀ r := hUB
  have hhalf : closedBall y₀ (r / 2) ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hSU
  -- On `Ω ∩ U` the restriction of `u` solves the equation with `a'`.
  have hfU : MemLp f 2 (volume.restrict (Ω ⊓ U : Opens E)) :=
    hf.mono_measure (Measure.restrict_mono (SetLike.coe_subset_coe.mpr inf_le_left) le_rfl)
  have hu₁ : ∀ v : W1p0 volume (Ω ⊓ U) 2,
      energyFormH1 a' 0 0 (W1p.restrictL inf_le_left u) (v : W1p volume (Ω ⊓ U) 2) =
        ∫ x in Ω ⊓ U, hfU.toLp f x * W1p.value (v : W1p volume (Ω ⊓ U) 2) x := fun v => by
    rw [energyFormH1_restrictL_eq_setIntegral_of_eqOn inf_le_left (fun x hx => haa' hx.2) hu v]
    exact integral_congr_ae (hfU.coeFn_toLp.mono fun x hx => by simp only [hx])
  -- Near `closedBall y₀ (r / 2)`, `u` agrees with a solution on `H` with forcing `f`.
  obtain ⟨w, g, hw, hwu, -, hgf⟩ := exists_isWeakSolutionDirichlet_ae_eq_on_of_inter_eq
    (U := ⟨ball y₀ r, isOpen_ball⟩) (fun x => hell'.opNorm_matrixBilinearForm_le (mem_univ x))
    hK' hΩ hUr (isCompact_closedBall y₀ (r / 2)) hhalf hu₁ hu0
  -- Inside `B(y₀, r)` the open sets `Ω` and `H` agree.
  have hHΩ : (H : Set E) ∩ ball y₀ r ⊆ Ω := fun x hx => by
    rw [← hΩ] at hx
    exact hx.1
  have hΩH : (Ω : Set E) ∩ ball y₀ r ⊆ H := fun x hx => by
    rw [hΩ] at hx
    exact hx.1
  -- The forcing `g` is `f` on `B(y₀, r / 2)` almost everywhere; take `f` there exactly.
  have hg₀ : (ball y₀ (r / 2)).piecewise f g =ᵐ[volume.restrict H] g := by
    filter_upwards [hgf, ae_restrict_of_ae (ae_imp_of_ae_restrict hfU.coeFn_toLp),
      ae_restrict_mem H.isOpen.measurableSet] with x hgx hfx hxH
    by_cases hx : x ∈ ball y₀ (r / 2)
    · have hxU := hhalf (ball_subset_closedBall hx)
      rw [piecewise_eq_of_mem _ _ _ hx, hgx (ball_subset_closedBall hx),
        hfx ⟨hHΩ ⟨hxH, hUr hxU⟩, hxU⟩]
    · rw [piecewise_eq_of_notMem _ _ _ hx]
  have hwu' : W1p.value (w : W1p volume H 2) =ᵐ[volume.restrict ((Ω : Set E) ∩ ball y₀ (r / 2))]
      W1p.value u := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (fun x hx => hΩH ⟨hx.1, hUr (hhalf (ball_subset_closedBall hx.2))⟩) hwu,
      ae_restrict_mem (Ω.isOpen.inter isOpen_ball).measurableSet] with x h hx
    exact h (ball_subset_closedBall hx.2)
  refine ⟨a', K, hell', hK', fun x hx => haa' (hhalf (ball_subset_closedBall hx)),
    (ball y₀ (r / 2)).piecewise f g, (Lp.memLp g).ae_eq hg₀.symm,
    fun x hx => piecewise_eq_of_mem _ _ _ hx, w, fun v' => ?_, hwu'⟩
  rw [(isWeakSolutionDirichlet_iff g w).1 hw v']
  exact integral_congr_ae (hg₀.mono fun x hx => by simp only [hx])

/-- **Every second derivative is Hölder up to a flat portion of the boundary.** Let `0 < α < 1`,
let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `y₀` lie on the boundary hyperplane, and let `Ω` be
open with `Ω ∩ B(y₀, r) = H ∩ B(y₀, r)`, so that `∂Ω ∩ B(y₀, r)` is a piece of the hyperplane.
Suppose that `a` is uniformly elliptic on `B(y₀, r)`, that its entries are `C¹` there with first
derivatives `α`-Hölder near each point of the ball, and that `f ∈ L²(Ω)` is `α`-Hölder up to the
boundary near each point of `B(y₀, r) ∩ {c₀ ≤ ⟪y, ν⟫}`. Let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, such that
`ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `B(y₀, r)`: `u` vanishes on
`∂Ω ∩ B(y₀, r)`.

Then for every direction `w`, normal ones included, the weak derivative `∂_w u` exists in `H¹` of
the half-ball `Ω ∩ B(y₀, r / 16)`, and its gradient agrees almost everywhere there with a field
that is `α`-Hölder on the closed half-ball `closedBall y₀ (r / 16) ∩ {c₀ ≤ ⟪y, ν⟫}`. So the weak
second derivatives of `u` have `α`-Hölder representatives up to the flat boundary portion near
`y₀`.

No regularity of `a` or `f` and no shape of `∂Ω` is assumed away from `B(y₀, r)`: this is the
local form, near a flat piece of the boundary of an arbitrary open set, of
`exists_hasWeakLineDerivOn_w1p_and_holderOnWith_preciseRepresentative_restrict_gradient`, which
treats the Dirichlet problem on the whole half-space with coefficients Lipschitz on all of `H`. -/
theorem exists_hasWeakLineDerivOn_and_holderOnWith_gradient_of_inter_ball_eq
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {H Ω : Opens E} {ν : E} {c₀ : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {y₀ : E} (hy₀ : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (hΩ : (Ω : Set E) ∩ ball y₀ r = (H : Set E) ∩ ball y₀ r)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) (ball y₀ r))
    (hell : UniformlyEllipticOn (ball y₀ r) a lam Lam)
    (hda : ∀ x ∈ ball y₀ r, ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x ρ))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hfH : ∀ x ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α f (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}))
    {u : W1p volume Ω 2}
    (hu : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x)
    (hu0 : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball y₀ r →
      ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => ψ x * W1p.value u x)
    (w : E) :
    ∃ d : W1p volume (Ω ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ : Opens E) 2,
      HasWeakLineDerivOn volume (Ω ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩ : Opens E) (W1p.value u)
        (W1p.value d) w ∧
      ∃ G : E → E, (∃ C : ℝ≥0, HolderOnWith C α G
          (closedBall y₀ (r / 16) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ})) ∧
        (W1p.gradient d : E → E) =ᵐ[volume.restrict ((Ω : Set E) ∩ ball y₀ (r / 16))] G := by
  obtain ⟨a', K, hell', hK', haa', g, hg, hgf, w', hw', hwu⟩ :=
    exists_localized_problem hr hΩ ha hell hf hu hu0
  have hball : ball y₀ (r / 2) ⊆ ball y₀ r := ball_subset_ball (by linarith)
  -- The hypotheses of the half-space theorem hold for `a'` and `g` on `B(y₀, r / 2)`, on balls
  -- about each point shrunk to fit inside `B(y₀, r / 2)`, where `a' = a` and `g = f`.
  have hda' : ∀ x ∈ ball y₀ (r / 2), ∃ ρ > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a' y i j)) (ball x ρ) := fun x hx => by
    obtain ⟨ρ, hρ, L, hL⟩ := hda x (hball hx)
    obtain ⟨ρ', hρ', hsub⟩ := Metric.mem_nhds_iff.1
      ((isOpen_ball.inter isOpen_ball).mem_nhds ⟨mem_ball_self hρ, hx⟩)
    refine ⟨ρ', hρ', L, fun i j => ((hL i j).mono (hsub.trans inter_subset_left)).congr
      fun y hy => ?_⟩
    exact (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (hsub hy).2)
      fun z hz => by simp only [haa' hz]).fderiv_eq
  have hgH : ∀ x ∈ ball y₀ (r / 2) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}, ∃ ρ > 0, ∃ L : ℝ≥0,
      HolderOnWith L α g (ball x ρ ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := fun x hx => by
    obtain ⟨ρ, hρ, L, hL⟩ := hfH x ⟨hball hx.1, hx.2⟩
    obtain ⟨ρ', hρ', hsub⟩ := Metric.mem_nhds_iff.1
      ((isOpen_ball.inter isOpen_ball).mem_nhds ⟨mem_ball_self hρ, hx.1⟩)
    exact ⟨ρ', hρ', L, (hL.mono (inter_subset_inter_left _ (hsub.trans inter_subset_left))).congr
      fun y hy => (hgf (hsub hy.1).2).symm⟩
  obtain ⟨d, hd, C, hC⟩ :=
    exists_hasWeakLineDerivOn_w1p_and_holderOnWith_preciseRepresentative_restrict_gradient hα hα1
      hν hH (hell'.mono_set (subset_univ _)) hK'.lipschitzOnWith hy₀ (half_pos hr)
      (fun i j => ((ha i j).mono hball).congr fun x hx => by simp only [haa' hx])
      (hell'.mono_set (subset_univ _)) hda' hg hgH hw' w
  rw [show r / 2 / 8 = r / 16 by ring] at hC
  -- On `Ω ∩ B(y₀, r / 16) ⊆ H ∩ B(y₀, r / 16)`, the localized solution `w'` is `u`.
  set Ω' : Opens E := Ω ⊓ ⟨ball y₀ (r / 16), isOpen_ball⟩
  have hΩ' : (Ω' : Set E) ⊆ ball y₀ (r / 16) ∩ H := fun x hx => by
    have hx' : x ∈ (Ω : Set E) ∩ ball y₀ r := ⟨hx.1, ball_subset_ball (by linarith) hx.2⟩
    rw [hΩ] at hx'
    exact ⟨hx.2, hx'.1⟩
  have hΩ'H : Ω' ≤ H := fun x hx => (hΩ' hx).2
  have hΩ'half : (Ω' : Set E) ⊆ (Ω : Set E) ∩ ball y₀ (r / 2) := fun x hx =>
    ⟨hx.1, ball_subset_ball (by linarith) hx.2⟩
  refine ⟨W1p.restrictL hΩ'H d, ((hd.mono hΩ'H).congr_ae
      (ae_restrict_of_ae_restrict_of_subset hΩ'half hwu)).congr_ae_deriv
      (W1p.value_restrictL_ae hΩ'H d).symm, _, ⟨C, hC⟩, ?_⟩
  filter_upwards [W1p.gradient_restrictL_ae hΩ'H d, ae_restrict_of_ae_restrict_of_subset hΩ'
    (W1p.gradient_ae_eq_preciseRepresentative_restrict d isOpen_ball inter_subset_right)]
    with x h1 h2
  rw [h1, h2]

end PDE

end TauCeti
