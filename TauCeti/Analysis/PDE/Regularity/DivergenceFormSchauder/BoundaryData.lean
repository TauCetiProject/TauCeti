/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundedDomain
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate for divergence-form equations with boundary values

Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary: near every frontier point, in
rigid coordinates, `Ω` is the region above the graph of a `C¹` function with `α`-Hölder
derivative. Let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, `u = g` on `∂Ω`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`, with the boundary
values attained in the sense that `u - g ∈ H¹₀(Ω)`. Suppose that on `closure Ω` the coefficient
`a` is uniformly elliptic with constants `λ, Λ` and `α`-Hölder with constant `K_a ≤ M`, the field
`G` is `α`-Hölder with constant `K_G`, and the boundary datum `g ∈ H¹(Ω)` has a gradient that
agrees almost everywhere with a field `Dg`, `α`-Hölder on `closure Ω` with constant `K_g` and
bounded by `M_g`; let `f ∈ L^q(Ω)`. This file proves the global `C^{1,β}` estimate: for
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, the gradient `∇u` agrees almost everywhere on
`Ω` with a function that is `β`-Hölder on `closure Ω`, with Hölder constant and supremum at most

`C (K_G + ‖f‖_{L^q(Ω)} + ‖u - g‖_{H¹(Ω)} + K_g + M_g)`,

where `C` depends only on `Ω`, its boundary charts, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`). This is
Gilbarg–Trudinger, Theorem 8.33, with boundary values whose gradient is `α`-Hölder up to the
boundary; for `g = 0` it is `TauCeti.PDE.exists_holderOnWith_gradient_closure_of_isBounded`.

The Dirichlet problem with these data is moreover uniquely solvable: there is exactly one
`u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`, and its gradient is `β`-Hölder up to the boundary with the estimate above (in the
`TauCeti.PDE` namespace,
`existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_and_holderOnWith_gradient_closure`).
This is Gilbarg–Trudinger, Theorem 8.34, for the operator without lower-order terms.

A `C^{1,α}` boundary is also a `C^{1,α'}` boundary for every `α' ≤ min α 1`: near the chart
centres the boundary graphs agree with graphs whose derivative is `α'`-Hölder
(`TauCeti.PDE.forall_frontier_chart_of_le`). So the estimate applies at
every smaller exponent.

## The argument

The difference `w = u - g` lies in `H¹₀(Ω)` and solves the equation with zero boundary values
`-∂ᵢ(aⁱʲ ∂ⱼw) = f - div (G - H)`, where `H(x)` is the vector `a(x) Dg(x)`, written as the Riesz
representative of `η ↦ ⟨a(x) Dg(x), η⟩`. The field `H` is `α`-Hölder on `closure Ω` with constant
`K_a M_g + Λ K_g`, so the estimate with zero boundary values applies to `w`, and `∇u = ∇w + Dg`.
Existence and uniqueness of the weak solution is Lax–Milgram on `H¹₀(Ω)`, which is coercive since
`Ω` lies in a ball (in the `TauCeti.PDE` namespace,
`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the global `C^{1,α}` estimate) and Theorem 8.34 (solvability of the Dirichlet
  problem in `C^{1,α}(closure Ω)`).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Gradient InnerProductSpace Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The field `H(x) = a(x) Dg(x)`, written as the Riesz representative of
`η ↦ ⟨a(x) Dg(x), η⟩`, is `α`-Hölder on `s` with constant `K_a M_g + Λ K_g` and bounded by
`Λ M_g`, when on `s` the coefficient `a` is uniformly elliptic and `α`-Hölder with constant `K_a`
and `Dg` is `α`-Hölder with constant `K_g` and bounded by `M_g`. -/
private theorem holderOnWith_and_norm_le_continuousLinearMapOfBilin_flip_matrixBilinearForm
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {lam Lam : ℝ}
    {α Ka Kg Mg : ℝ≥0} (hell : UniformlyEllipticOn s a lam Lam)
    (hKa : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) s)
    (hDgK : HolderOnWith Kg α Dg s) (hDgM : ∀ y ∈ s, ‖Dg y‖ ≤ Mg) :
    HolderOnWith (Ka * Mg + Lam.toNNReal * Kg) α
        (fun x => continuousLinearMapOfBilin (matrixBilinearForm (a x)).flip (Dg x)) s ∧
      ∀ x ∈ s, ‖continuousLinearMapOfBilin (matrixBilinearForm (a x)).flip (Dg x)‖ ≤
        (Lam.toNNReal * Mg : ℝ≥0) := by
  have hBM : ∀ x ∈ s, ‖matrixBilinearForm (a x)‖ ≤ (Lam.toNNReal : ℝ) := fun x hx =>
    (hell.opNorm_matrixBilinearForm_le hx).trans (Real.le_coe_toNNReal _)
  refine ⟨(toDual ℝ _).symm.isometry.comp_holderOnWith
    (ContinuousLinearMap.holderOnWith_flip_apply hKa hDgK hBM hDgM), fun x hx => ?_⟩
  rw [continuousLinearMapOfBilin, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map, NNReal.coe_mul]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ContinuousLinearMap.opNorm_flip]
  exact mul_le_mul (hBM x hx) (hDgM x hx) (norm_nonneg _) (by positivity)

/-- **Lifting the boundary values.** Let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly in `Ω` and let
`∇g` agree almost everywhere on `Ω` with a field `Dg`. Then `u - g` solves the same equation with
`G` replaced by `G - H`, where `H(x)` is the vector `a(x) Dg(x)`, written as the Riesz
representative of `η ↦ ⟨a(x) Dg(x), η⟩`. -/
private theorem energyFormH1_sub_ofTestFunctionₗ_eq {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u g : W1p volume Ω 2}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict Ω))
    (hG : MemLp G 2 (volume.restrict Ω))
    (hH : MemLp (fun x => continuousLinearMapOfBilin (matrixBilinearForm (a x)).flip (Dg x)) 2
      (volume.restrict Ω))
    (hDg : ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg)
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x) (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 a 0 0 (u - g) (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x - continuousLinearMapOfBilin (matrixBilinearForm (a x)).flip (Dg x),
        ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x := by
  have hg : energyFormH1 a 0 0 g (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪continuousLinearMapOfBilin (matrixBilinearForm (a x)).flip (Dg x),
        ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
    rw [energyFormH1_def]
    refine integral_congr_ae ?_
    filter_upwards [hDg, gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx hφx
    rw [continuousLinearMapOfBilin_apply, ContinuousLinearMap.flip_apply]
    simp [energyIntegrand_apply, hx, hφx]
  simp_rw [inner_sub_left]
  rw [integral_sub (integrable_inner_gradient_testFunction hG φ)
    (integrable_inner_gradient_testFunction hH φ), ← hg,
    energyFormH1_sub_left (b := 0) (c := 0) hcoeff, hu]
  ring

/-- The bookkeeping of the constants in the global estimate with boundary values. -/
private theorem mul_add_add_le_mul {C₀ M Λ Dβ KG Ka Kg Mg F W : ℝ} (hC₀ : 0 ≤ C₀) (hKa : 0 ≤ Ka)
    (hKaM : Ka ≤ M) (hΛ : 0 ≤ Λ) (hDβ : 0 ≤ Dβ) (hKG : 0 ≤ KG) (hKg : 0 ≤ Kg) (hMg : 0 ≤ Mg)
    (hF : 0 ≤ F) (hW : 0 ≤ W) :
    C₀ * (KG + (Ka * Mg + Λ * Kg) + F + W) + (Kg * Dβ + Mg) ≤
      (C₀ * (1 + M + Λ) + Dβ + 1) * (KG + F + W + Kg + Mg) := by
  nlinarith [mul_nonneg (mul_nonneg hC₀ (sub_nonneg.2 hKaM)) hMg,
    mul_nonneg (mul_nonneg hC₀ (hKa.trans hKaM)) (by positivity : 0 ≤ KG + F + W + Kg),
    mul_nonneg (mul_nonneg hC₀ hΛ) (by positivity : 0 ≤ KG + F + W + Mg),
    mul_nonneg hDβ (by positivity : 0 ≤ KG + F + W + Mg), mul_nonneg hC₀ (add_nonneg hKg hMg)]

/-- **The global `C^{1,β}` estimate with boundary values.** Let `Ω ⊆ ℝ^{n+1}` be a bounded open
set with `C^{1,α}` boundary: for every frontier point `x` there are rigid coordinates `e` with
`e x = 0` and a `C¹` function `γ` with `γ 0 = 0` and `α`-Hölder derivative such that, inside a
normal cylinder, `Ω` is the region above the graph of `γ`. Let `0 < β < 1` with `β ≤ α`, let
`2 ≤ q` with `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`, and let `λ, Λ, M` be given. Then
there is a constant `C`, depending only on these data, with the following property.

Let `u, g ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly in
`Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`. Suppose that on
`closure Ω` the coefficient `a` is uniformly elliptic with constants `λ, Λ` and `α`-Hölder with
constant `K_a ≤ M`, `G` is `α`-Hölder with constant `K_G`, and `∇g` agrees almost everywhere on `Ω`
with a field `Dg` that is `α`-Hölder with constant `K_g` and bounded by `M_g`; let `f ∈ L^q(Ω)`.
Then `∇u` agrees almost everywhere on `Ω` with a function `h` that is `β`-Hölder on `closure Ω`,
with Hölder constant and supremum at most
`C (K_G + ‖f‖_{L^q(Ω)} + ‖u - g‖_{H¹(Ω)} + K_g + M_g)`. -/
theorem exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1)
    (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u g : W1p volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG Kg Mg : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      u - g ∈ w1p0Submodule volume Ω 2 →
      ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg →
      HolderOnWith Kg α Dg (closure (Ω : Set _)) → (∀ y ∈ closure (Ω : Set _), ‖Dg y‖ ≤ Mg) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        ⇑(W1p.gradient u) =ᵐ[volume.restrict Ω] h ∧
        HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u - g‖ +
          Kg + Mg)).toNNReal β h (closure (Ω : Set _)) ∧
        ∀ y ∈ closure (Ω : Set _), ‖h y‖ ≤
          C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u - g‖ + Kg + Mg) := by
  set s := closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  obtain ⟨C₀, hC₀, H₀⟩ :=
    exists_holderOnWith_gradient_closure_of_isBounded hβ hβ1 hβα hq hβq hΩ hchart lam Lam M
  -- A bound `D` for the distances in `closure Ω`, to lower the exponent of `Dg` from `α` to `β`.
  obtain ⟨D, hD⟩ : ∃ D : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D :=
    ⟨_, fun x hx y hy => Metric.edist_le_diam_of_mem hΩ.closure hx hy⟩
  set M' : ℝ := max M 0
  have : 0 ≤ M' := le_max_right _ _
  set Dβ : ℝ := (D : ℝ) ^ ((α : ℝ) - β) with hDβdef
  have hDβ : 0 ≤ Dβ := by positivity
  refine ⟨C₀ * (1 + M' + Lam.toNNReal) + Dβ + 1, by positivity,
    fun {u g a G Dg f Ka KG Kg Mg} hell hKa hKaM hKG hf hug hDg hDgK hDgM hu => ?_⟩
  have hα : 0 < α := hβ.trans_le hβα
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  -- The field `H(x) = a(x) Dg(x)`, through the Riesz representation, is Hölder and bounded.
  obtain ⟨hH, hHM⟩ :=
    holderOnWith_and_norm_le_continuousLinearMapOfBilin_flip_matrixBilinearForm hell hKa hDgK hDgM
  -- The data `G`, `H` and the coefficient are integrable on `Ω`.
  obtain ⟨MG, hMG⟩ := (hKG.isBounded_image hΩ.closure).exists_norm_le
  obtain ⟨hcoeff, hG2⟩ := memLp_energyIntegrand_and_memLp_of_holderOnWith (mu := volume) hα
    (D := Ω) subset_closure hell hKa hKG (forall_mem_image.1 hMG)
  have hH2 := (memLp_energyIntegrand_and_memLp_of_holderOnWith (mu := volume) hα (D := Ω)
    subset_closure hell hKa hH hHM).2
  -- `w = u - g ∈ H¹₀(Ω)` solves the equation with zero boundary values and the datum `G - H`.
  obtain ⟨hw', hwae, hwK, hwM⟩ := H₀ (u := ⟨u - g, hug⟩) hell hKa hKaM (hKG.sub hH) hf
    (energyFormH1_sub_ofTestFunctionₗ_eq hcoeff hG2 hH2 hDg hu)
  rw [← Submodule.norm_coe (⟨u - g, hug⟩ : W1p0 volume Ω 2), Submodule.coe_mk] at hwK hwM
  push_cast at hwK hwM
  -- The constants: `K_a ≤ M ≤ M'`.
  have key := mul_add_add_le_mul hC₀ Ka.coe_nonneg (hKaM.trans (le_max_left M 0))
    Lam.toNNReal.coe_nonneg hDβ KG.coe_nonneg Kg.coe_nonneg Mg.coe_nonneg ENNReal.toReal_nonneg
    (norm_nonneg (u - g)) (Mg := Mg)
    (F := (eLpNorm f q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))).toReal)
  refine ⟨fun x => hw' x + Dg x, ?_, ?_, fun y hy => ?_⟩
  · filter_upwards [W1p.gradient_sub_ae u g, hwae, hDg] with x h₁ h₂ h₃
    rw [Subtype.coe_mk] at h₂
    rw [← h₂, h₁, ← h₃, Pi.sub_apply, sub_add_cancel]
  · refine (hwK.add (hDgK.of_le hD hβα)).mono_const ?_
    have hw₀ : 0 ≤ C₀ * (KG + (Ka * Mg + Lam.toNNReal * Kg) +
        (eLpNorm f q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))).toReal +
          ‖u - g‖) := by
      positivity
    rw [← NNReal.coe_le_coe]
    push_cast [Real.coe_toNNReal _ hw₀, ← hDβdef]
    refine le_trans ?_ (Real.le_coe_toNNReal _)
    linarith [Mg.coe_nonneg]
  · calc ‖hw' y + Dg y‖ ≤ ‖hw' y‖ + ‖Dg y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hwM y hy) (hDgM y hy)
      _ ≤ _ := by linarith [mul_nonneg Kg.coe_nonneg hDβ]


attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace in
/-- **The Dirichlet problem with `C^{1,α}` boundary values on a `C^{1,α}` domain is uniquely
solvable, with a gradient Hölder up to the boundary.** Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with
`C^{1,α}` boundary, given by rigid graph charts at its frontier points as in
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`, and let `0 < β < 1`
with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, `q ≥ 2`. Let `λ`, `Λ` and `M` be given. Then there is a
constant `C ≥ 0` with the following property.

Let `a` be uniformly elliptic with constants `λ, Λ` and `α`-Hölder with constant `K_a ≤ M` on
`closure Ω`, let `G` be `α`-Hölder with constant `K_G` on `closure Ω`, and let `f ∈ L^q(Ω)`. Let
`g ∈ H¹(Ω)` have a gradient that agrees almost everywhere on `Ω` with a function `Dg` that is
`α`-Hölder with constant `K_g` and bounded by `M_g` on `closure Ω`. Then there is exactly one
`u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and

`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

the weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, `u = g` on `∂Ω`, and its gradient agrees
almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, with Hölder constant and
supremum at most `C (K_G + ‖f‖_{L^q(Ω)} + ‖u - g‖_{H¹(Ω)} + K_g + M_g)`.

This is Gilbarg–Trudinger's Theorem 8.34 for the operator without lower-order terms. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_and_holderOnWith_gradient_closure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β)
    (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : W1p volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG Kg Mg : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg →
      HolderOnWith Kg α Dg (closure (Ω : Set _)) → (∀ y ∈ closure (Ω : Set _), ‖Dg y‖ ≤ Mg) →
      ∃! u : W1p volume Ω 2, (u - g ∈ w1p0Submodule volume Ω 2 ∧
          ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
            (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
              ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x) ∧
        ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
          ⇑(W1p.gradient u) =ᵐ[volume.restrict Ω] h ∧
          HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u - g‖ +
            Kg + Mg)).toNNReal β h (closure (Ω : Set _)) ∧
          ∀ y ∈ closure (Ω : Set _), ‖h y‖ ≤
            C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u - g‖ + Kg + Mg) := by
  obtain ⟨C, hC, hreg⟩ := exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule hβ hβ1
    hβα hq hβq hΩ hchart lam Lam M
  refine ⟨C, hC, fun {g a G Dg f Ka KG Kg Mg} hell hKa hKaM hG hf hgD hDg hMg => ?_⟩
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hα : 0 < α := hβ.trans_le hβα
  have hellΩ := hell.mono_set (subset_closure (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
  have ha := aestronglyMeasurable_of_holderOnWith_matrixBilinearForm (mu := volume)
    Ω.isOpen.measurableSet subset_closure hα hKa
  have hG2 : MemLp G 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (hG.memLp_top hα hΩ.closure Ω.isOpen.measurableSet subset_closure).mono_exponent le_top
  have hf2 : MemLp f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    hf.mono_exponent hq
  -- The right-hand side as a functional on `H¹₀(Ω)`.
  set ℓ := dirichletForcing (hf2.toLp f) - divergenceForcing (hG2.toLp G)
  have hℓ : ∀ v : W1p0 volume Ω 2, ℓ v =
      (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
        ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x := fun v => by
    rw [sub_apply, divergenceForcing_toLp_apply hG2,
      dirichletForcing_apply_eq_setIntegral, sub_neg_eq_add, add_comm]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  obtain ⟨R, hR⟩ := hΩ.subset_ball 0
  obtain ⟨u, ⟨hu0, hu⟩, huniq⟩ :=
    hellΩ.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) (beta := 0) (gamma := 0) ha aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) hR
      (by simpa using hellΩ.pos) ℓ g
  have hu' : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
        ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x := fun v => (hu v).trans (hℓ v)
  -- The weak equation against `H¹₀(Ω)` gives it against the test functions.
  have htest : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x := by
    simpa only [neg_neg] using energyFormH1_ofTestFunctionₗ_eq_of_forall_w1p0 (F := -G)
      fun v => by rw [hu' v, Pi.neg_def]; simp only [inner_neg_left, integral_neg, sub_neg_eq_add,
        add_comm]
  refine ⟨u, ⟨⟨hu0, hu'⟩, hreg hell hKa hKaM hG hf hu0 hgD hDg hMg htest⟩, fun u' hu'' => ?_⟩
  exact huniq u' ⟨hu''.1.1, fun v => (hu''.1.2 v).trans (hℓ v).symm⟩

end PDE

end TauCeti
