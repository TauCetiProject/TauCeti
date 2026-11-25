/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.FlatBoundary
public import TauCeti.Analysis.PDE.Regularity.HalfSpace
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.PDE.Regularity.Hessian.DivergenceForm
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.MeasureTheory.Function.PreciseRepresentative

/-!
# Hölder continuity of the second derivatives up to the boundary of a half-space

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, let `0 < α < 1`, and let
`u ∈ H¹₀(H)` be the weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `H`, `u = 0` on `∂H`,

that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H f v` for every `v ∈ H¹₀(H)`, where `a` is uniformly elliptic and
Lipschitz, as a bilinear form, on all of `H`, `a` is uniformly elliptic on a ball `B(y₀, r)` about
a point `y₀` of the boundary hyperplane and its entries are `C¹` with first derivatives `α`-Hölder
there, and `f ∈ L²(H)` is `α`-Hölder up to the boundary there. This file proves that the second
derivatives of `u` with a tangential direction are `α`-Hölder up to the boundary near `y₀`: for
every `e` with `⟪e, ν⟫ = 0`, the weak derivative `∂ₑu` lies in `H¹₀(H)`, and the precise
representative of its gradient for the Lebesgue measure on `H` is `α`-Hölder on the closed
half-ball `closedBall y₀ (r / 4) ∩ {c₀ ≤ ⟪y, ν⟫}`
(`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient`; this and
the other declarations named below are in the `TauCeti.PDE` namespace). Since `∇(∂ₑu)` holds the
derivatives `∂_w ∂ₑu` in every direction `w`, this covers every second derivative `∂_w ∂_z u` with
`z` or `w` tangential, that is all of them but `∂_ν ∂_ν u`.

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

## Main declarations

* `exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_restrict_gradient`: the
  tangential second derivatives of the solution are `α`-Hölder up to the flat boundary.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the `C^{1,α}` estimate up to the boundary) and Lemma 6.18 (`C^{2,α}` regularity
  at the boundary).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.4.
-/

public section

open InnerProductSpace LineDeriv MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

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
  -- The ball `B = B(y₀, 3r / 4)`, the coefficients on it and the bound on `f`.
  set B : Opens E := ⟨ball y₀ (3 * r / 4), isOpen_ball⟩
  have hBr : closedBall y₀ (3 * r / 4) ⊆ ball y₀ r := closedBall_subset_ball (by linarith)
  have hcl : closure (((B ⊓ H : Opens E)) : Set E) ⊆ closedBall y₀ (3 * r / 4) :=
    (closure_mono inter_subset_left).trans closure_ball_subset_closedBall
  obtain ⟨Ka, hKa⟩ := exists_holderOnWith_matrixBilinearForm_of_contDiffOn isOpen_ball ha
    (isCompact_closedBall y₀ (3 * r / 4)) hBr hα1.le
  -- `f` composed with the fold is Hölder near `closedBall y₀ (3r / 4)`, so `f` is bounded on `H`
  -- there.
  obtain ⟨δf, hδf, -, Mf, -, hMf⟩ :=
    (isCompact_closedBall y₀ (3 * r / 4)).exists_holderOnWith_thickening_and_norm_le
      fun x hx => holderOnWith_comp_fold_ball hν hy₀ hfH x (hBr hx)
  -- Step 1: the precise representative `P` of `∇u` is Hölder up to the boundary, and `P = ∇u`
  -- almost everywhere on `B ∩ H`.
  obtain ⟨CP, hP⟩ := exists_holderOnWith_preciseRepresentative_gradient_extendRestrict hα hα1 hν hH
    hr (B := B) rfl hellB hKa hf (fun x hx hxH => by
      simpa only [Function.comp_apply, ((hH x).1 hxH).le, ↓reduceIte] using
        hMf x (self_subset_thickening hδf _ hx)) hu
  have hPV : preciseRepresentative (volume.restrict (H : Set E))
      (W1p.gradient (extendRestrict u B) : E → E)
        =ᵐ[volume.restrict (((B ⊓ H : Opens E)) : Set E)] W1p.gradient (u : W1p volume H 2) :=
    (ae_eq_restrict_inter_preciseRepresentative_restrict B.isOpen
      (((Lp.memLp (W1p.gradient (extendRestrict u B))).mono_measure
        (Measure.restrict_mono inter_subset_left le_rfl)).locallyIntegrable one_le_two)).symm.trans
      (gradient_extendRestrict_ae_eq u)
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

end PDE

end TauCeti
