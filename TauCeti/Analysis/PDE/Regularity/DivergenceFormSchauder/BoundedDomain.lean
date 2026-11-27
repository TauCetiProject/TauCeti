/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Scaled
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.MeasureTheory.Function.Gluing

/-!
# The global Schauder estimate for divergence-form equations on a bounded domain

Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary: near every frontier point, in
rigid coordinates, `Ω` is the region above the graph of a `C¹` function with `α`-Hölder
derivative. Let `u ∈ H¹₀(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`,

where on `closure Ω` the coefficient `a` is uniformly elliptic with constants `λ, Λ` and
`α`-Hölder with constant `K_a ≤ M`, the field `G` is `α`-Hölder with constant `K_G`, and
`f ∈ L^q(Ω)`. This file proves the global `C^{1,β}` estimate: for `0 < β < 1` with `β ≤ α` and
`β ≤ 1 - (n + 1) / q`, the gradient `∇u` agrees almost everywhere on `Ω` with a function `g` that
is `β`-Hölder on `closure Ω`, with Hölder constant and supremum at most

`C (K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)})`,

where `C` depends only on `Ω`, its boundary charts, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`). This is the global `C^{1,α}`
estimate of Gilbarg–Trudinger, Theorem 8.33, for zero boundary values, with an `L^q` datum `f` and
the `H¹` norm of `u` in place of its supremum; `u` is only assumed to lie in `H¹₀(Ω)`, and the
regularity of `∇u` up to the boundary is part of the conclusion. The uniformity of `C` over the
coefficients is what compactness and continuity arguments over a class of operators need.

## The argument

The estimate is assembled from local estimates by a covering argument.

* **Interior pieces.** Around a point `x ∈ Ω` with `B(x, 2r) ⊆ Ω`, the scaled interior estimate
  `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le` bounds the
  Hölder constant and the supremum of the precise representative of `∇u` on `B(x, r)` by a
  multiple of `‖u‖_{L²(B(x, 2r))} + ‖f‖_{L^q(B(x, 2r))} + K_G`, the multiple depending on `r`.
* **Boundary pieces.** Around a frontier point `x`, the zero extension of `u` to the whole space
  vanishes off `Ω` and solves the equation on `Ω`
  (`energyFormH1_restrictL_extendByZeroL_ofTestFunctionₗ_eq_setIntegral_inner_add_setIntegral`),
  so the curved-boundary estimate `TauCeti.PDE.exists_holderOnWith_gradient_of_graph` gives a
  function, `β`-Hölder on `closure Ω` near `x`, which agrees with `∇u` almost everywhere there.
* **Gluing.** The pieces agree with `∇u` almost everywhere, so any two agree where both are
  defined, by continuity; compactness of `closure Ω` and a Lebesgue number of the cover by the
  balls of the pieces turn the local bounds into global ones
  (`IsOpen.exists_holderOnWith_closure_of_forall_ae_eq`).

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`: the global `C^{1,β}` estimate
  on a bounded domain with `C^{1,α}` boundary.
* `TauCeti.PDE.exists_holderOnWith_gradient_ball_inter_closure_of_graph`: the estimate near a
  single boundary point, which needs a boundary chart there only.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the global `C^{1,α}` estimate) and Section 6.2 (the covering argument for the
  global Schauder estimate).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Gradient InnerProductSpace Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Interior pieces.** Around each point `x ∈ Ω` there is a ball `B(x, ρ)` and a constant
`κ`, depending on `x`, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, on which the precise representative
of the gradient of every weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω` is `β`-Hölder with
constant `κ Q` and bounded by `κ Q`, where `Q = K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)}`. -/
private theorem exists_interior_piece {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α)
    {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) (lam Lam M : ℝ) :
    ∃ ρ > 0, ∃ κ : ℝ≥0, ∀ {u : W1p volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (Ω : Set _) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) Ω → (Ka : ℝ) ≤ M →
      HolderOnWith KG α G Ω → MemLp f q (volume.restrict (Ω : Set _)) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      HolderOnWith (κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal +
          ‖u‖).toNNReal) β
        (preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
        (ball x ρ) ∧
      ∀ y ∈ ball x ρ, ‖preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y‖ ≤
        κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  set r := ε / 2 with hr_def
  have hr : 0 < r := half_pos hε
  have hball : ball x (2 * r) ⊆ Ω := by rwa [hr_def, mul_div_cancel₀ _ two_ne_zero]
  obtain ⟨C, hC, H⟩ := exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le
    (n := n) hβ hβ1 hβα hq hβq (lam := lam) (Lam := Lam) (M := M * r ^ (α : ℝ))
  set S := r ^ (-(((n : ℝ) + 1) / 2)) + r ^ (2 - ((n : ℝ) + 1) / q.toReal) + r ^ (1 + (α : ℝ))
  set m := max (r ^ (-(1 + (β : ℝ)))) r⁻¹
  have hm : 0 ≤ m := le_max_of_le_right (inv_nonneg.2 hr.le)
  refine ⟨r, hr, (C * S * m).toNNReal, fun {u a G f Ka KG} hell hKa hKaM hKG hf hu => ?_⟩
  obtain ⟨hhol, hbd⟩ := H (Omega := Ω) (u := u) (a := a) (G := G) (f := f) (Ka := Ka) (KG := KG)
    (x₀ := x) (r := r) (hell.mono_set hball) (hKa.mono hball) (hKG.mono hball)
    (mul_le_mul_of_nonneg_right hKaM (by positivity))
    (hf.mono_measure (Measure.restrict_mono hball le_rfl)) hu hr hball
  set Q := (KG : ℝ) + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖
  -- Each term of the local data is at most `Q`.
  have hu2 : √(∫ y in ball x (2 * r), W1p.value u y ^ 2) ≤ Q := by
    rw [← ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      ← W1p.eLpNorm_two_eq_ofReal_sqrt_setIntegral Filter.EventuallyEq.rfl hball]
    linarith [W1p.toReal_eLpNorm_value_le_norm u hball, W1p.norm_value_le u, KG.coe_nonneg,
      ENNReal.toReal_nonneg (a := eLpNorm f q (volume.restrict (Ω : Set _)))]
  have hf2 : (eLpNorm f q (volume.restrict (ball x (2 * r)))).toReal ≤ Q := by
    have := ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono hball le_rfl))
    linarith [KG.coe_nonneg, norm_nonneg u]
  have hKG : (KG : ℝ) ≤ Q := by
    linarith [norm_nonneg u, ENNReal.toReal_nonneg (a := eLpNorm f q (volume.restrict (Ω : Set _)))]
  have hQi : r ^ (-(((n : ℝ) + 1) / 2)) * √(∫ y in ball x (2 * r), W1p.value u y ^ 2) +
      r ^ (2 - ((n : ℝ) + 1) / q.toReal) *
        (eLpNorm f q (volume.restrict (ball x (2 * r)))).toReal +
      r ^ (1 + (α : ℝ)) * KG ≤ S * Q := by
    simp only [S, add_mul]
    gcongr
  refine ⟨hhol.mono_const ?_, fun y hy => ?_⟩
  · rw [← Real.toNNReal_mul (by positivity)]
    refine Real.toNNReal_le_toNNReal ?_
    calc _ ≤ C * m * (S * Q) := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  · rw [Real.coe_toNNReal _ (by positivity)]
    have h := hbd y hy
    calc _ = r⁻¹ * (r * ‖preciseRepresentative volume
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y‖) :=
          by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
      _ ≤ m * (C * (S * Q)) := mul_le_mul (le_max_right _ _)
          (h.trans (mul_le_mul_of_nonneg_left hQi hC)) (by positivity) hm
      _ = _ := by ring

/-- **The `C^{1,β}` estimate near a boundary point for zero boundary values.** Let `x` be a
frontier point of a bounded open set `Ω`, near which `Ω` is, in rigid coordinates centred at `x`,
the region above the graph of a `C¹` function with `α`-Hölder derivative. Then there is a ball
`B(x, ρ)` and a constant `κ`, depending on the chart, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, with
the following property. Let the coefficients `a` be uniformly elliptic on `closure Ω` with
constants `λ, Λ` and `α`-Hölder there with constant `Ka ≤ M`, and let `G` be `α`-Hölder on
`closure Ω` with constant `K_G`. Then for every weak solution `u ∈ H¹₀(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω` the gradient `∇u` agrees almost everywhere on `Ω ∩ B(x, ρ)`
with a function that is `β`-Hölder with constant `κ Q` and bounded by `κ Q` on
`B(x, ρ) ∩ closure Ω`, where `Q = K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)}`. -/
theorem exists_holderOnWith_gradient_ball_inter_closure_of_graph {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
    {γ : E → ℝ} {h₀ r₀ : ℝ} {Kγ : ℝ≥0} (hex : e x = 0) (hh₀ : 0 < h₀) (hr₀ : 0 < r₀)
    (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ 1 γ) (hγK : HolderWith Kγ α (fderiv ℝ γ))
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst)) (lam Lam M : ℝ) :
    ∃ ρ > 0, ∃ κ : ℝ≥0, ∀ {u : W1p0 volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
          (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict ((Ω : Set _) ∩ ball x ρ)] g ∧
        HolderOnWith (κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal +
          ‖u‖).toNNReal) β g (ball x ρ ∩ closure (Ω : Set _)) ∧
        ∀ y ∈ ball x ρ ∩ closure (Ω : Set _),
          ‖g y‖ ≤ κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖) := by
  obtain ⟨ρ, ρ', C, -, hρ', hC, H⟩ :=
    exists_holderOnWith_gradient_of_graph hβ hβ1 hβα hq hβq hh₀ hr₀ hγ0 hγ hγK hgraph lam Lam M
  have hx : e.symm 0 = x := by rw [← hex, AffineIsometryEquiv.symm_apply_apply]
  rw [hx] at H
  refine ⟨ρ', hρ', C.toNNReal, fun {u a G f Ka KG} hell hKa hKaM hKG hf hu => ?_⟩
  have hα : 0 < α := hβ.trans_le hβα
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  -- The data are integrable on `Ω`, as the equation for the zero extension needs.
  obtain ⟨CG, hCG⟩ := hΩ.isCompact_closure.exists_bound_of_continuousOn (hKG.continuousOn hα)
  obtain ⟨ha, hG⟩ :=
    memLp_energyIntegrand_and_memLp_of_holderOnWith (mu := volume) hα subset_closure hell hKa hKG
      hCG
  have hsub : volume.restrict ((⊤ ⊓ Ω : Opens _) : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      volume.restrict (Ω : Set _) :=
    Measure.restrict_mono (SetLike.coe_subset_coe.mpr inf_le_right) le_rfl
  set U₀ : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2 :=
    (W1p0.extendByZeroL (Omega' := ⊤) le_top u).val
  obtain ⟨g, hg, hghol, hgb⟩ := H (W := ⊤) (u := U₀)
    (a := a) (G := G) (f := f) (Ka := Ka) (KG := KG) (fun _ _ => trivial)
    (hell.mono_set inter_subset_left) (hKa.mono inter_subset_left) hKaM
    (hKG.mono inter_subset_left) (hf.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    (ae_restrict_of_ae (W1p0.value_extendByZeroL_ae_eq_zero_compl u))
    (energyFormH1_restrictL_extendByZeroL_ofTestFunctionₗ_eq_setIntegral_inner_add_setIntegral
      le_top (ha.mono_measure hsub) (c := 0)
      (by simp only [sub_zero]; exact hG.mono_measure hsub)
      ((hf.mono_exponent hq).mono_measure hsub) hu)
  -- The data of the local estimate are bounded by those of `Ω`.
  have hQ : C * ((KG : ℝ) + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩ ball x ρ))).toReal +
      ‖U₀‖) ≤
      C * ((KG : ℝ) + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖) := by
    have h1 := ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono (inter_subset_left (t := ball x ρ)) le_rfl))
    have h2 : ‖U₀‖ = ‖u‖ :=
      W1p0.norm_extendByZeroL le_top u
    gcongr
    exact h2.le
  refine ⟨g, ?_, (hghol.mono_const ?_).mono (by rw [inter_comm]), fun y hy => ?_⟩
  · filter_upwards [ae_restrict_of_ae (W1p0.gradient_extendByZeroL_top_ae u), hg,
      ae_restrict_mem (Ω.isOpen.inter isOpen_ball).measurableSet] with y h1 h2 h3
    rw [← h2, h1, indicator_of_mem h3.1]
  · rw [← Real.toNNReal_coe (r := C.toNNReal), ← Real.toNNReal_mul (by positivity),
      Real.coe_toNNReal _ hC]
    exact Real.toNNReal_le_toNNReal hQ
  · rw [Real.coe_toNNReal _ hC]
    exact (hgb y (by rwa [inter_comm])).trans hQ

/-- **Local pieces.** Under the hypotheses of
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`, every point `x ∈ closure Ω` has
a ball `B(x, ρ)` and a constant `κ` such that for every weak solution `u ∈ H¹₀(Ω)` the gradient
`∇u` agrees almost everywhere on `Ω ∩ B(x, ρ)` with a function that is `β`-Hölder with constant
`κ Q` and bounded by `κ Q` on `B(x, ρ) ∩ closure Ω`, where `Q = K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)}`.
At interior points this function is the precise representative of `∇u`, at frontier points the
function of the curved-boundary estimate. -/
private theorem exists_piece {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∃ ρ > 0, ∃ κ : ℝ≥0, ∀ {u : W1p0 volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
          (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict ((Ω : Set _) ∩ ball x ρ)] g ∧
        HolderOnWith (κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal +
          ‖u‖).toNNReal) β g (ball x ρ ∩ closure (Ω : Set _)) ∧
        ∀ y ∈ ball x ρ ∩ closure (Ω : Set _),
          ‖g y‖ ≤ κ * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖) := by
  by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  · obtain ⟨ρ, hρ, κ, H⟩ := exists_interior_piece hβ hβ1 hβα hq hβq hxΩ lam Lam M
    refine ⟨ρ, hρ, κ, fun {u a G f Ka KG} hell hKa hKaM hKG hf hu => ?_⟩
    obtain ⟨hhol, hbd⟩ := H (u := (u : W1p volume Ω 2)) (hell.mono_set subset_closure)
      (hKa.mono subset_closure) hKaM (hKG.mono subset_closure) hf hu
    exact ⟨_, (ae_eq_restrict_preciseRepresentative Ω.isOpen
      (W1p.locallyIntegrableOn_gradient (u : W1p volume Ω 2))).filter_mono
        (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)),
      hhol.mono inter_subset_left, fun y hy => hbd y hy.1⟩
  · have hfr : x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
      ⟨hx, by rwa [Ω.isOpen.interior_eq]⟩
    obtain ⟨e, γ, h₀, r₀, Kγ, hex, hh₀, hr₀, hγ0, hγ, hγK, hgraph⟩ := hchart x hfr
    exact exists_holderOnWith_gradient_ball_inter_closure_of_graph hβ hβ1 hβα hq hβq hΩ hex hh₀
      hr₀ hγ0 hγ hγK hgraph lam Lam M

/-- **The global Schauder estimate for divergence-form equations.** Let `Ω ⊆ ℝ^{n+1}` be a bounded
open set with `C^{1,α}` boundary: for every frontier point `x` there are rigid coordinates `e`
with `e x = 0` in which, inside the normal cylinder of half-height `h₀` and radius `r₀`, `Ω` is the
region above the graph of a `C¹` function `γ` with `γ 0 = 0` and `α`-Hölder derivative. Let
`0 < β < 1` with `β ≤ α`, let `2 ≤ q ≤ ∞` and `β ≤ 1 - (n + 1) / q`, and fix `λ`, `Λ` and `M`.
There is a constant `C` such that for every `u ∈ H¹₀(Ω)` solving `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G`
weakly in `Ω`, where on `closure Ω` the coefficient `a` is uniformly elliptic with constants
`λ, Λ` and `α`-Hölder with constant `K_a ≤ M`, the field `G` is `α`-Hölder with constant `K_G`,
and `f ∈ L^q(Ω)`, the gradient `∇u` agrees almost everywhere on `Ω` with a function that is
`β`-Hölder on `closure Ω` with constant `C Q` and bounded there by `C Q`, where
`Q = K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)}`. The constant depends only on `Ω`, its charts, `n`, `α`,
`β`, `q`, `λ`, `Λ` and `M`. -/
theorem exists_holderOnWith_gradient_closure_of_isBounded {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞}
    (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : W1p0 volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
          (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict (Ω : Set _)] g ∧
        HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal +
          ‖u‖)).toNNReal β g (closure (Ω : Set _)) ∧
        ∀ y ∈ closure (Ω : Set _),
          ‖g y‖ ≤ C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖) := by
  choose! ρ hρ κ H using fun x (hx : x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) =>
    exists_piece hβ hβ1 hβα hq hβq hΩ hchart lam Lam M hx
  obtain ⟨A, hA⟩ := Ω.isOpen.exists_holderOnWith_closure_of_forall_ae_eq (μ := volume)
    (Y := EuclideanSpace ℝ (Fin (n + 1))) hΩ.isCompact_closure hβ hρ κ
  refine ⟨A, A.coe_nonneg, fun {u a G f Ka KG} hell hKa hKaM hKG hf hu => ?_⟩
  have hQ : 0 ≤ (KG : ℝ) + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u‖ := by
    positivity
  choose! g hg hghol hgbd using fun x hx => H x hx hell hKa hKaM hKG hf hu
  obtain ⟨h, hhhol, hhbd, -, hh⟩ := hA (g := g) (fun x hx => hghol x hx)
    (fun x hx y hy => by
      simpa only [NNReal.coe_mul, Real.coe_toNNReal _ hQ] using hgbd x hx y hy)
    fun x hx => (hg x hx).symm
  refine ⟨h, hh, ?_, fun y hy => ?_⟩
  · rwa [Real.toNNReal_mul A.coe_nonneg, Real.toNNReal_coe]
  · simpa only [NNReal.coe_mul, Real.coe_toNNReal _ hQ] using hhbd y hy

end PDE

end TauCeti
