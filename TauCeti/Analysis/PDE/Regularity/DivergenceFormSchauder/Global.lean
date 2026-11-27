/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.CurvedBoundary
public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Scaled
import TauCeti.Analysis.Holder.Localization
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate for divergence-form equations

Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary: near each of its boundary points,
in rigid coordinates, `Ω` is the region above the graph of a `C¹` function whose derivative is
`α`-Hölder. Let `u ∈ H¹₀(Ω)` be a weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, `u = 0` on `∂Ω`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, where `a` is
uniformly elliptic with constants `λ`, `Λ` and `α`-Hölder on `closure Ω` with constant `K_a ≤ M`,
`G` is `α`-Hölder on `closure Ω` with constant `K_G`, and `f ∈ L^q(Ω)` with `q ≥ 2`. Let
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`. This file proves that `∇u` agrees almost
everywhere on `Ω` with a function `g` that is `β`-Hölder on `closure Ω`, with

`[g]_{β; closure Ω} + sup_{closure Ω} ‖g‖ ≤ C (K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)})`,

where `C` depends on `Ω`, its boundary charts, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, but not on `u`,
`a`, `G` or `f` otherwise
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`). This is the global
`C^{1,β}` estimate up to the boundary for divergence-form equations with Hölder coefficients and
zero boundary values. The `H¹` norm of `u` on the right-hand side can be bounded by the data
through the energy estimate of the Dirichlet problem.

## The argument

The estimate is local, and is assembled from two local estimates by compactness of `closure Ω`.

* **Interior points.** Around a point of `Ω` the scaled interior estimate
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le`) bounds
  the Hölder seminorm and the supremum of the precise representative of `∇u` on a ball.
* **Boundary points.** Around a point of `frontier Ω`, the extension of `u` by zero to the whole
  space vanishes off `Ω` and solves the equation in `Ω`, so the estimate near a `C^{1,α}`
  boundary (`TauCeti.PDE.exists_holderOnWith_gradient_of_graph`) gives a representative of `∇u`
  that is `β`-Hölder and bounded on `closure Ω` near the point.
* **Gluing.** Two of these local representatives are continuous on `closure Ω` where their balls
  overlap and agree almost everywhere on `Ω` there, so they agree on `closure Ω` there
  (`IsOpen.eqOn_diag_of_forall_ae_eq`). They glue to one function on `closure Ω`, bounded by the
  local bounds on a finite subcover, and Hölder on `closure Ω` by a Lebesgue number argument
  (`IsCompact.exists_holderOnWith_of_forall_holderOnWith_ball_inter`).

The radii and constants of the local estimates depend only on the point, the boundary chart
there and the structural constants, so the global constant does not depend on `u`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`: the global `C^{1,β}`
  estimate for the Dirichlet problem with zero boundary values on a bounded `C^{1,α}` domain.
* `TauCeti.PDE.forall_frontier_chart_of_le`: the boundary charts of a `C^{1,α}` domain are also
  charts of a `C^{1,β}` domain for every `β ≤ min α 1`, so the estimate also applies with a
  coefficient exponent below the exponent of the boundary graphs.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the global `C^{1,α}` estimate for divergence-form equations).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.4.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology Gradient InnerProductSpace Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- The local form of the global estimate at a point `x`, with radius `ρ` and constant `C`: for
every weak solution `u ∈ H¹₀(Ω)` with data as in
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`, the gradient `∇u` agrees almost
everywhere on `Ω ∩ B(x, ρ)` with a function that is `β`-Hölder on `closure Ω ∩ B(x, ρ)` and bounded
there, both with constant `C (K_G + ‖f‖_{L^q(Ω)} + ‖u‖)`. -/
private def HasLocalGradientEstimate (Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))) (α β : ℝ≥0)
    (q : ℝ≥0∞) (lam Lam M : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) (ρ C : ℝ) : Prop :=
  ∀ {u : W1p0 volume Ω 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
    UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) a lam Lam →
    HolderOnWith Ka α (fun x => matrixBilinearForm (a x))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) → (Ka : ℝ) ≤ M →
    HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
    MemLp f q (volume.restrict Ω) →
    (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
        (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x) →
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict ((Ω : Set _) ∩ ball x ρ)] g ∧
      HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖)).toNNReal β g
        (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball x ρ) ∧
      ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball x ρ,
        ‖g y‖ ≤ C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖)

/-- **The local estimate at an interior point**, from the scaled interior Schauder estimate on a
ball `B(x, 2r) ⊆ Ω`. -/
private theorem exists_hasLocalGradientEstimate_of_mem {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1)
    (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (lam Lam M : ℝ) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Ω) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ HasLocalGradientEstimate Ω α β q lam Lam M x ρ C := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  obtain ⟨r, hr, hball⟩ : ∃ r : ℝ, 0 < r ∧ ball x (2 * r) ⊆ Ω :=
    ⟨ε / 2, half_pos hε, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
  obtain ⟨C₀, hC₀, h⟩ := exists_holderOnWith_preciseRepresentative_gradient_ball_and_mul_norm_le
    (n := n) hβ hβ1 hβα hq hβq (lam := lam) (Lam := Lam) (M := M * r ^ (α : ℝ))
  set c : ℝ := r ^ (-(((n : ℝ) + 1) / 2)) + r ^ (2 - ((n : ℝ) + 1) / q.toReal) +
    r ^ (1 + (α : ℝ)) with hc
  refine ⟨r, C₀ * c * (r ^ (-(1 + (β : ℝ))) + r⁻¹), hr, by positivity, ?_⟩
  intro u a G f Ka KG hell haK hKa hGK hf hu
  have hclΩ : ball x (2 * r) ⊆ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    hball.trans subset_closure
  obtain ⟨hhol, hsup⟩ := h (hell.mono_set hclΩ) (haK.mono hclΩ) (hGK.mono hclΩ)
    (mul_le_mul_of_nonneg_right hKa (by positivity))
    (hf.mono_measure (Measure.restrict_mono hball le_rfl)) hu hr hball
  set Q := KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖
  set D := r ^ (-(((n : ℝ) + 1) / 2)) *
      √(∫ y in ball x (2 * r), W1p.value (u : W1p volume Ω 2) y ^ 2) +
    r ^ (2 - ((n : ℝ) + 1) / q.toReal) * (eLpNorm f q (volume.restrict (ball x (2 * r)))).toReal +
    r ^ (1 + (α : ℝ)) * KG
  -- The data on the ball are bounded by the data on `Ω`.
  have hD : D ≤ c * Q := by
    have hQ0 := ENNReal.toReal_nonneg (a := eLpNorm f q (volume.restrict Ω))
    simp only [D, hc, add_mul]
    gcongr
    · exact ((W1p.sqrt_setIntegral_value_sq_le_norm (u : W1p volume Ω 2) hball).trans_eq
        (Submodule.norm_coe u)).trans (by simp only [Q]; linarith [KG.coe_nonneg])
    · exact (ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _
        (Measure.restrict_mono hball le_rfl))).trans
        (by simp only [Q]; linarith [norm_nonneg u, KG.coe_nonneg])
    · simp only [Q]; linarith [norm_nonneg u]
  -- Both bounds of the scaled estimate carry a factor `t ≤ r^{-(1+β)} + r⁻¹` in front of `C₀ D`.
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ r ^ (-(1 + (β : ℝ))) + r⁻¹ →
      C₀ * t * D ≤ C₀ * c * (r ^ (-(1 + (β : ℝ))) + r⁻¹) * Q := fun t ht htr =>
    calc C₀ * t * D ≤ C₀ * t * (c * Q) := by gcongr
      _ = C₀ * (c * Q) * t := by ring
      _ ≤ C₀ * (c * Q) * (r ^ (-(1 + (β : ℝ))) + r⁻¹) := by gcongr
      _ = _ := by ring
  -- On `B(x, r) ⊆ Ω` the closure of `Ω` adds nothing.
  have hinter : closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball x r = ball x r :=
    inter_eq_right.2 ((ball_subset_ball (by linarith)).trans hclΩ)
  refine ⟨_, ae_restrict_of_ae_restrict_of_subset inter_subset_left
    (ae_eq_restrict_preciseRepresentative Ω.isOpen (W1p.locallyIntegrableOn_gradient _)), ?_,
    fun y hy => ?_⟩
  · rw [hinter]
    exact hhol.mono_const (Real.toNNReal_le_toNNReal
      (hkey _ (by positivity) (le_add_of_nonneg_right (by positivity))))
  · rw [hinter] at hy
    have hle := (le_inv_mul_iff₀ hr).2 (hsup y hy)
    exact hle.trans ((le_of_eq (by ring)).trans
      (hkey r⁻¹ (by positivity) (le_add_of_nonneg_left (by positivity))))

/-- The restriction to `Ω` of the extension by zero to the whole space of a weak solution
`u ∈ H¹₀(Ω)` solves the same equation as `u`. It is stated for an open set `W` equal to `Ω`, such as
`⊤ ⊓ Ω`, which is the domain on which the estimate near the boundary tests the equation. -/
private theorem forall_energyFormH1_restrictL_extendByZeroL_eq {W : Opens _} (hW : W = Ω)
    (hle : W ≤ ⊤) {u : W1p0 volume Ω 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
        (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x) :
    ∀ φ : 𝓓(W, ℝ), energyFormH1 a 0 0
        (W1p.restrictL hle (W1p0.extendByZeroL le_top u : W1p volume ⊤ 2))
        (W1p.ofTestFunctionₗ volume W 2 φ) =
      (∫ x in W, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in W, f x * φ x := by
  subst hW
  rw [W1p0.restrictL_extendByZeroL]
  exact hu

/-- **The local estimate at a boundary point**, from the estimate near a `C^{1,α}` boundary
applied to the extension of `u` by zero. -/
private theorem exists_hasLocalGradientEstimate_of_graph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞}
    (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) (lam Lam M : ℝ)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {h₀ r₀ : ℝ}
    {Kγ : ℝ≥0} (hex : e x = 0) (hh₀ : 0 < h₀) (hr₀ : 0 < r₀) (hγ0 : γ 0 = 0)
    (hγ : ContDiff ℝ 1 γ) (hγK : HolderWith Kγ α (fderiv ℝ γ))
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ HasLocalGradientEstimate Ω α β q lam Lam M x ρ C := by
  obtain ⟨ρ, ρ', C, -, hρ', hC, h⟩ :=
    exists_holderOnWith_gradient_of_graph hβ hβ1 hβα hq hβq hh₀ hr₀ hγ0 hγ hγK hgraph lam Lam M
  rw [e.symm_apply_eq.2 hex.symm] at h
  refine ⟨ρ', C, hρ', hC, ?_⟩
  intro u a G f Ka KG hell haK hKa hGK hf hu
  set v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2 :=
    ((W1p0.extendByZeroL le_top u : W1p0 volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2) :
      W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
  obtain ⟨g, hg, hgh, hgb⟩ := h (W := ⊤) (u := v) (by simp) (hell.mono_set inter_subset_left)
    (haK.mono inter_subset_left) hKa (hGK.mono inter_subset_left)
    (hf.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    (ae_restrict_of_ae (W1p0.value_extendByZeroL_ae_eq_zero_compl u))
    (forall_energyFormH1_restrictL_extendByZeroL_eq (top_inf_eq Ω) inf_le_left hu)
  -- On `Ω` the gradient of the extension is the gradient of `u`.
  have hvu : (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict ((Ω : Set _) ∩ ball x ρ')]
        W1p.gradient v := by
    filter_upwards [ae_restrict_mem (Ω.isOpen.inter isOpen_ball).measurableSet,
      ae_restrict_of_ae (W1p0.gradient_extendByZeroL_top_ae u)] with y hy hy'
    rw [hy', indicator_of_mem hy.1]
  -- The data of the local estimate are bounded by those on `Ω`.
  have hnorm : ‖v‖ = ‖u‖ := W1p0.norm_extendByZeroL le_top u
  have hf2 : (eLpNorm f q (volume.restrict ((Ω : Set _) ∩ ball x ρ))).toReal ≤
      (eLpNorm f q (volume.restrict Ω)).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_left le_rfl))
  have hQ : C * (KG + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩ ball x ρ))).toReal + ‖v‖) ≤
      C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖) := by
    rw [hnorm]
    gcongr
  exact ⟨g, hvu.trans hg, hgh.mono_const (Real.toNNReal_le_toNNReal hQ),
    fun y hy => (hgb y hy).trans hQ⟩

/-- **The local estimate at every point of the closure**: at interior points by
`exists_hasLocalGradientEstimate_of_mem`, and at boundary points, through their `C^{1,α}` charts,
by `exists_hasLocalGradientEstimate_of_graph`. -/
private theorem exists_hasLocalGradientEstimate_of_mem_closure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞}
    (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hbdry : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      HasLocalGradientEstimate Ω α β q lam Lam M x ρ C := by
  intro x hx
  by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  · exact exists_hasLocalGradientEstimate_of_mem hβ hβ1 hβα hq hβq lam Lam M hxΩ
  · obtain ⟨e, γ, h₀, r₀, Kγ, hex, hh₀, hr₀, hγ0, hγ, hγK, hgraph⟩ :=
      hbdry x ⟨hx, by rwa [Ω.isOpen.interior_eq]⟩
    exact exists_hasLocalGradientEstimate_of_graph hβ hβ1 hβα hq hβq lam Lam M hex hh₀ hr₀
      hγ0 hγ hγK hgraph

/-- **Lowering the exponent of boundary charts.** The boundary charts of a set `s` with
`C^{1,α}` boundary can be replaced by charts, with the same coordinates and cylinders, whose graphs
have `β`-Hölder derivatives on the whole space, for every `β ≤ min α 1`. So the global estimate
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph` applies with a coefficient
exponent below the exponent of the boundary graphs. The charts make `E` finite-dimensional, so
that the graphs can be cut off outside a ball (`ContDiff.exists_eqOn_ball_holderWith_fderiv`). -/
theorem forall_frontier_chart_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} {α β : ℝ≥0} (hβα : β ≤ α) (hβ1 : β ≤ 1)
    (hbdry : ∀ x ∈ frontier s,
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ s ↔ γ z.snd < z.fst)) :
    ∀ x ∈ frontier s,
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ β (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ s ↔ γ z.snd < z.fst) := by
  intro x hx
  obtain ⟨e, γ, h₀, r₀, Kγ, hex, hh₀, hr₀, hγ0, hγ, hγK, hgraph⟩ := hbdry x hx
  have : FiniteDimensional ℝ (WithLp 2 (ℝ × E)) :=
    e.linearIsometryEquiv.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E := Module.Finite.of_surjective
    ((LinearMap.snd ℝ ℝ E).comp (WithLp.linearEquiv 2 ℝ (ℝ × E)).toLinearMap)
    fun y => ⟨WithLp.toLp 2 (0, y), by simp⟩
  obtain ⟨γ', K, -, hγ', heq, hK, -⟩ := hγ.exists_eqOn_ball_holderWith_fderiv hγK hβα hβ1 0 hr₀
  refine ⟨e, γ', h₀, r₀, K, hex, hh₀, hr₀, by rw [heq (mem_ball_self hr₀), hγ0], hγ', hK,
    fun z hz => ?_⟩
  rw [hgraph z hz, heq (mem_ball_zero_iff.2 (mem_normalCylinder.1 hz).2.2)]

/-- **The global Schauder estimate for divergence-form equations with zero boundary values.** Let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary: at each point `x` of its frontier
there are rigid coordinates `e` with `e x = 0` in which, inside a normal cylinder, `Ω` is the
region above the graph of a `C¹` function `γ` with `γ 0 = 0` and `α`-Hölder derivative. Let
`0 < β < 1` with `β ≤ α`, let `2 ≤ q ≤ ∞` and `β ≤ 1 - (n + 1) / q`, and fix `λ`, `Λ` and `M`.
There is a constant `C` such that the following holds. Let `a` be uniformly elliptic with
constants `λ`, `Λ` and `α`-Hölder on `closure Ω` with constant `K_a ≤ M`, the oscillation of `a`
measured in the operator norm of the attached bilinear forms, let `G` be `α`-Hölder on
`closure Ω` with constant `K_G`, let `f ∈ L^q(Ω)`, and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test
function `φ`. Then `∇u` agrees almost everywhere on `Ω` with a function `g` that is `β`-Hölder on
`closure Ω` with constant `C Q` and bounded there by `C Q`, where
`Q = K_G + ‖f‖_{L^q(Ω)} + ‖u‖_{H¹(Ω)}`.

The constant depends on `Ω`, its boundary charts, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, and not on
`u`, `a`, `G` or `f` otherwise. This is Gilbarg–Trudinger's Theorem 8.33 for zero boundary
values, with an `L^q` datum `f`. -/
theorem exists_holderOnWith_gradient_closure_of_forall_graph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞}
    (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hbdry : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : W1p0 volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x))
        (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) → (Ka : ℝ) ≤ M →
      HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      MemLp f q (volume.restrict Ω) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 (u : W1p volume Ω 2)
          (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        (W1p.gradient (u : W1p volume Ω 2) : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) =ᵐ[volume.restrict Ω] g ∧
        HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖)).toNNReal β g
          (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) ∧
        ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          ‖g y‖ ≤ C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖) := by
  set s := closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hs : IsCompact s := hΩ.isCompact_closure
  -- Local estimates at every point of `closure Ω`: interior points and boundary points.
  choose! ρ C hρ hC hloc using
    exists_hasLocalGradientEstimate_of_mem_closure hβ hβ1 hβα hq hβq hbdry lam Lam M
  -- A finite subcover bounds the local constants, and a Lebesgue number glues the Hölder bounds.
  obtain ⟨t, hts, hcover⟩ := hs.elim_nhds_subcover (fun x => ball x (ρ x)) fun x hx =>
    ball_mem_nhds x (hρ x hx)
  set Cmax : ℝ := 1 + ∑ x ∈ t, C x
  have hCx : ∀ x ∈ t, C x ≤ Cmax := fun x hxt => by
    have := Finset.single_le_sum (f := C) (fun i hi => hC i (hts i hi)) hxt
    linarith
  have hCmax1 : 1 ≤ Cmax :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun i hi => hC i (hts i hi))
  obtain ⟨A, hA⟩ := hs.exists_holderOnWith_of_forall_holderOnWith_ball_inter
    (Y := EuclideanSpace ℝ (Fin (n + 1))) (α := β) hρ fun x => (C x).toNNReal
  refine ⟨((A : ℝ) + 1) * Cmax, by positivity, ?_⟩
  intro u a G f Ka KG hell haK hKa hGK hf hu
  set Q := KG + (eLpNorm f q (volume.restrict Ω)).toReal + ‖u‖
  have hQ : 0 ≤ Q := by positivity
  choose! g hgae hghol hgsup using fun x hx => hloc x hx hell haK hKa hGK hf hu
  have hFeq := Ω.isOpen.eqOn_diag_of_forall_ae_eq hρ hgae fun x hx =>
    (hghol x hx).continuousOn hβ
  -- The glued function is bounded on `closure Ω` by the bounds on the finite subcover.
  have hFb : ∀ y ∈ s, ‖g y y‖ ≤ Cmax * Q := by
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover hy)
    rw [show g y y = g x y from hFeq x (hts x hxt) ⟨hy, hyx⟩]
    exact (hgsup x (hts x hxt) y ⟨hy, hyx⟩).trans
      (mul_le_mul_of_nonneg_right (hCx x hxt) hQ)
  -- It is Hölder on `closure Ω` by the local Hölder bounds.
  have hFhol : HolderOnWith (A * (Cmax * Q).toNNReal) β (fun y => g y y) s := by
    refine hA (fun y hy => by rw [Real.coe_toNNReal _ (by positivity)]; exact hFb y hy)
      fun x hx => ?_
    rw [inter_comm]
    refine ((hghol x hx).congr (hFeq x hx).symm).mono_const ?_
    rw [← Real.toNNReal_mul (hC x hx)]
    exact Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_left (by nlinarith) (hC x hx))
  have hCQ : 0 ≤ Cmax * Q := by positivity
  refine ⟨fun y => g y y, ?_, hFhol.mono_const ?_, fun y hy => (hFb y hy).trans ?_⟩
  · -- `∇u` agrees with the glued function on each piece of the finite subcover of `Ω`.
    have hsub : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆
        ⋃ x ∈ t, (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball x (ρ x) := fun y hy => by
      obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover (subset_closure hy))
      exact mem_iUnion₂.2 ⟨x, hxt, hy, hyx⟩
    refine ae_restrict_of_ae_restrict_of_subset hsub
      ((ae_restrict_biUnion_finset_iff _ t _).2 fun x hxt => ?_)
    filter_upwards [hgae x (hts x hxt),
      ae_restrict_mem (Ω.isOpen.inter isOpen_ball).measurableSet] with y hy hyU
    rw [hy, show g y y = g x y from hFeq x (hts x hxt) ⟨subset_closure hyU.1, hyU.2⟩]
  · rw [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ hCQ,
      Real.coe_toNNReal _ (by positivity)]
    nlinarith [hCQ]
  · nlinarith [mul_nonneg A.coe_nonneg hCQ]

end PDE

end TauCeti
