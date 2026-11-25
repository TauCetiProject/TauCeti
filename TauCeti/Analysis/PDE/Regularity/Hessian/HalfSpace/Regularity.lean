/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.IntegrabilityGain
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.PDE.Regularity.Hessian.ContinuousCoefficient.Regularity
import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.ContinuousCoefficient
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# `W^{2,q}` regularity near a flat boundary portion for continuous principal coefficients

Let `E` be a finite-dimensional real inner product space, `1 < p, q < ∞`, and let
`H = {x | a < x.fst}` be a half-space of `ℝ × E`. Let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`, so
that inside `U` the domain is the half-space and its boundary is the hyperplane `∂H`. This file
proves the boundary part of Gilbarg–Trudinger, Lemma 9.16, near a flat boundary portion: a strong
solution `u ∈ W^{2,p}(Ω)` of

`tr (A D²u) = f` in `Ω`, `u = 0` on `∂Ω ∩ U`,

with `f`, `u` and the weak gradient `∇u` in `L^q(Ω)`, lies in `W^{2,q}` near every point `x₀` of
`U` at which the coefficient field `A` is continuous within `Ω`, and elliptic if `x₀` lies in the
closure of `Ω`
(`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_normalHalfSpace`).
The point `x₀` may lie on the boundary hyperplane, where `A x₀` is the boundary value of `A`. The
boundary condition is that `ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` compactly supported in `U`, as
in the boundary estimate
`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace`. Together
with the interior statement
`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_continuousOn`, this is
Lemma 9.16 near a flat boundary portion. After flattening the boundary of a `C^{1,1}` domain in
charts, Lemma 9.16 is the regularity input of Gilbarg–Trudinger's Lemma 9.17, the a priori estimate
behind the solvability of the Dirichlet problem in `W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` (Theorem 9.15).

Lower-order terms `⟪b, ∇u⟫ + c u` with bounded measurable `b` and `c` are covered by moving them
into `f`, which keeps `f` in `L^q(Ω)` because `u` and `∇u` lie there.

## The argument

This follows the interior statement, with the half-space integrability gain in place of the
whole-space one. Let `δ` be the constant of the half-space integrability gain
(`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`).
Freeze the coefficient at an operator `A₀` with ellipticity constant `λ`, namely `A₀ = A x₀`
when `x₀` lies in the closure of `Ω` and the identity otherwise: by continuity within `Ω` there
is `ρ > 0` with `K = closedBall x₀ (2ρ) ⊆ U` and `‖A x - A₀‖ ≤ δ λ` on `Ω ∩ K`
(`TauCeti.exists_ball_subset_forall_norm_sub_le`). Let `ζ` be a smooth cutoff equal to `1` on
`closedBall x₀ ρ` and supported in `B(x₀, 2ρ)`. The product `w = ζ u` has zero boundary values
and vanishes off `K`, so its extension by zero `W` to `H` lies in `W^{2,p}(H)` with first-order
part in `W^{1,p}_0(H)`, and its weak Hessian is `ζ D²u + T` on `Ω`, where
`T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ` is the Leibniz remainder
(`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`). So `W` solves

`tr (Ã D²W) = 1_{Ω ∩ K} (ζ f + tr (A T))` on `H`,

where `Ã = A` on `Ω ∩ K` and `Ã = A₀` elsewhere, so that `‖Ã - A₀‖ ≤ δ λ` everywhere. The right
side lies in `L^q(H)` since `A` is bounded on `Ω ∩ K` and `u, ∇u ∈ L^q(Ω)`, and so does the value
`ζ u` of `W`. The half-space integrability gain places `W` in `W^{2,q}(H)`, and on
`Ω ∩ B(x₀, ρ)`, where `ζ = 1`, `W` is `u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.16 and the proof of Theorem 9.13 (the estimate near a flat boundary portion).
-/

public section

noncomputable section

namespace TauCeti

open Filter _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **The cutoff of `u`, extended by zero to the half-space.** Let `Ω ∩ U = H ∩ U`, let `K ⊆ U` be
compact, and let `ζ` be smooth with compact support in `K`. If `ψ u ∈ W^{1,p}_0(Ω)` for every
smooth `ψ` compactly supported in `U`, some `W ∈ W^{2,p}(H)`, with first-order part in
`W^{1,p}_0(H)`, has value `1_Ω ζ u` and weak Hessian `1_Ω (ζ D²u + T)` on `H`, where `T` is the
Leibniz remainder; the remainder is measurable on `Ω`. -/
private theorem exists_wkp_normalHalfSpace_value_ae_eq_indicator_mul {a : ℝ}
    {Omega U : Opens (WithLp 2 (ℝ × E))}
    (hΩU : (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKU : K ⊆ U) {zeta : WithLp 2 (ℝ × E) → ℝ}
    (hzeta : ContDiff ℝ ∞ zeta) (hcpt : HasCompactSupport zeta) (htsK : tsupport zeta ⊆ K)
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
    (hu0 : ∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
        W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
          fun x => ψ x * Wkp.value 2 u x) :
    ∃ W : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2,
      Wkp.firstOrder 1 W ∈ w1p0Submodule volume (normalHalfSpace a) p ∧
      (Wkp.value 2 W : WithLp 2 (ℝ × E) → ℝ)
          =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
        (Omega : Set (WithLp 2 (ℝ × E))).indicator (fun x => zeta x * Wkp.value 2 u x) ∧
      (Wkp.iteratedGradient 1 W : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
          =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
        (Omega : Set (WithLp 2 (ℝ × E))).indicator (fun x => zeta x • Wkp.iteratedGradient 1 u x +
          leibnizRemainder zeta (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
            (Wkp.value 2 u x) x) ∧
      AEStronglyMeasurable (fun x => leibnizRemainder zeta
          (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x)
        (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) := by
  have hΩm : MeasurableSet (Omega : Set (WithLp 2 (ℝ × E))) := Omega.isOpen.measurableSet
  -- Inside `U`, which contains `K`, the domain `Ω` is the half-space `H`.
  have hHK : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ K ⊆ Omega :=
    fun x hx => ((hΩU.symm ▸ ⟨hx.1, hKU hx.2⟩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)).1
  -- The cutoff `w = ζ u`, with zero boundary values and weak Hessian `ζ D²u + T`.
  obtain ⟨w, hwv⟩ := Wkp.exists_value_ae_eq_mul_of_hasCompactSupport 2 hzeta hcpt u
  have hwD := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hzeta hwv
  have hwK : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      x ∉ K → Wkp.value 2 w x = 0 := by
    filter_upwards [hwv] with x hx hxK
    rw [hx, image_eq_zero_of_notMem_tsupport fun h => hxK (htsK h), zero_mul]
  have hw0 : Wkp.firstOrder 1 w ∈ w1p0Submodule volume Omega p := by
    obtain ⟨v, hv⟩ := hu0 zeta hzeta hcpt (htsK.trans hKU)
    have hfo : Wkp.firstOrder 1 w = (v : W1p volume Omega p) := by
      refine W1p.ext_value (Lp.ext ?_)
      rw [Wkp.value_firstOrder]
      exact hwv.trans hv.symm
    exact hfo ▸ v.property
  -- Its extension `W` by zero to `H` has zero boundary values on `∂H`.
  obtain ⟨W, hW⟩ := Wkp.exists_value_ae_eq_indicator_of_isClosed (V := normalHalfSpace a)
    hK.isClosed hHK 2 w hwK
  refine ⟨W, W1p.mem_w1p0Submodule_of_inter_eq_of_isCompact hΩU hK hKU hw0
    (by simpa only [Wkp.value_firstOrder] using hwK)
    (by simpa only [Wkp.value_firstOrder] using hW), ?_, ?_, ?_⟩
  · filter_upwards [hW, ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hwv)] with x h₁ h₂
    by_cases hx : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
    · rw [h₁, indicator_of_mem hx, indicator_of_mem hx, h₂ hx]
    · rw [h₁, indicator_of_notMem hx, indicator_of_notMem hx]
  · filter_upwards [Wkp.iteratedGradient_ae_eq_indicator_of_isClosed hK.isClosed hHK 1 hwK hW,
      ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hwD)] with x h₁ h₂
    by_cases hx : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
    · rw [h₁, indicator_of_mem hx, indicator_of_mem hx, h₂ hx]
    · rw [h₁, indicator_of_notMem hx, indicator_of_notMem hx]
  · refine ((Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 w)).sub
      (hzeta.continuous.aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 u)))).congr ?_
    filter_upwards [hwD] with x hx
    simp only [Pi.sub_apply, Pi.smul_apply']
    rw [hx, add_sub_cancel_left]

/-- **The localized equation.** If `D = 1_Ω (ζ D²u + T)` and `tr (A D²u) = f` on `Ω`, where `ζ`
vanishes off `K`, then `tr (Ã D) = 1_{Ω ∩ K} (ζ f + tr (A T))` for
`Ã = A₀ + 1_{Ω ∩ K} (A - A₀)`, which is `A` on `Ω ∩ K` and `A₀` elsewhere. -/
private theorem ae_traceCLM_comp_eq_indicator {μ : Measure (WithLp 2 (ℝ × E))}
    {Omega : Opens (WithLp 2 (ℝ × E))}
    {K : Set (WithLp 2 (ℝ × E))} {zeta : WithLp 2 (ℝ × E) → ℝ} (htsK : tsupport zeta ⊆ K)
    (A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2} {f : WithLp 2 (ℝ × E) → ℝ}
    (htr : ∀ᵐ x ∂μ, x ∈ (Omega : Set (WithLp 2 (ℝ × E))) →
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x)
    {D : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hD : ∀ᵐ x ∂μ, D x = (Omega : Set (WithLp 2 (ℝ × E))).indicator (fun x =>
      zeta x • Wkp.iteratedGradient 1 u x + leibnizRemainder zeta
        (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x) x) :
    ∀ᵐ x ∂μ, traceCLM ℝ (WithLp 2 (ℝ × E))
        ((A₀ + ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K).indicator (fun y => A y - A₀) x) ∘L D x) =
      ((Omega : Set (WithLp 2 (ℝ × E))) ∩ K).indicator (fun x =>
        zeta x * f x + traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L leibnizRemainder zeta
          (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x) (Wkp.value 2 u x) x)) x := by
  filter_upwards [hD, htr] with x h₁ h₂
  rw [h₁]
  by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
  · rw [indicator_of_mem hxΩ]
    by_cases hxK : x ∈ K
    · have hx : x ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ K := ⟨hxΩ, hxK⟩
      rw [indicator_of_mem hx, indicator_of_mem hx, add_sub_cancel, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.comp_smul, map_add, map_smul, smul_eq_mul, h₂ hxΩ]
    · have hx : x ∉ (Omega : Set (WithLp 2 (ℝ × E))) ∩ K := fun h => hxK h.2
      rw [image_eq_zero_of_notMem_tsupport fun h => hxK (htsK h), zero_smul, zero_add,
        leibnizRemainder_eq_zero_of_notMem_tsupport (fun h => hxK (htsK h)),
        ContinuousLinearMap.comp_zero, map_zero, indicator_of_notMem hx]
  · have hx : x ∉ (Omega : Set (WithLp 2 (ℝ × E))) ∩ K := fun h => hxΩ h.1
    rw [indicator_of_notMem hxΩ, ContinuousLinearMap.comp_zero, map_zero, indicator_of_notMem hx]

/-- **`W^{2,q}` regularity near a flat boundary portion for continuous principal coefficients**
(Gilbarg–Trudinger, Lemma 9.16). Let `1 < p, q < ∞`, let `H = {x | a < x.fst}` be a half-space of
`ℝ × E`, and let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`. Let `A` be a field of endomorphisms of
`ℝ × E`, measurable on `Ω`, and let `x₀ ∈ U` be a point at which `A` is continuous within `Ω` and,
if `x₀` lies in the closure of `Ω`, elliptic: `λ ‖ξ‖² ≤ ⟪A x₀ ξ, ξ⟫` for some `λ > 0`. Let
`u ∈ W^{2,p}(Ω)` vanish on the flat boundary
portion, in the sense that `ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` compactly supported in `U`,
and solve `tr (A D²u) = f` almost everywhere on `Ω`, where `f`, the value of `u` and its weak
gradient `∇u = TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)` lie in `L^q(Ω)`.
Then there is a ball `B(x₀, ρ) ⊆ U` such that `u` lies in `W^{2,q}(Ω ∩ B(x₀, ρ))`: some element `v`
of that space has the value and the weak Hessian of `u` there.

The point `x₀` may lie on the boundary hyperplane, and `A x₀` is then the boundary value of `A`.
No relation between `p` and `q` is assumed, `A` need not be symmetric, and nothing is assumed
about `∂Ω` outside `U`. -/
theorem exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hq : 1 < q) (hq_top : q ≠ ⊤) (a : ℝ)
    {Omega U : Opens (WithLp 2 (ℝ × E))}
    (hΩU : (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    {x₀ : WithLp 2 (ℝ × E)} (hx₀ : x₀ ∈ U) (hcont : ContinuousWithinAt A Omega x₀)
    (hell : x₀ ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x₀ ξ, ξ⟫_ℝ)
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) {f : WithLp 2 (ℝ × E) → ℝ}
    (hu0 : ∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
        W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
          fun x => ψ x * Wkp.value 2 u x)
    (hf : MemLp f q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (huq : MemLp (Wkp.value 2 u) q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hgq : MemLp (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) q
      (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (htr : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧
      ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩) q 2,
        (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict
            ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ : Opens (WithLp 2 (ℝ × E))) :
              Set (WithLp 2 (ℝ × E)))]
          Wkp.value 2 u ∧
        (Wkp.iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
            =ᵐ[volume.restrict
              ((Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩ : Opens (WithLp 2 (ℝ × E))) :
                Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient 1 u := by
  obtain ⟨δ, hδ, hgain⟩ :=
    exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace (E := E) hp
      hp_top hq hq_top
  -- Freeze the coefficient at `A₀`, within `δ λ` of `A` on `Ω ∩ B(x₀, 3ρ)`.
  obtain ⟨A₀, lam, hlam, hA₀, ρ₀, hρ₀, hρ₀U, hosc₀⟩ :=
    exists_ball_subset_forall_norm_sub_le U.isOpen hx₀ hcont hell hδ
  set ρ := ρ₀ / 3 with hρ_def
  have hρ : 0 < ρ := by positivity
  set K := closedBall x₀ (2 * ρ)
  have hKρ₀ : K ⊆ ball x₀ ρ₀ := closedBall_subset_ball (by linarith)
  have hKU : K ⊆ U := hKρ₀.trans hρ₀U
  have hKc : IsCompact K := isCompact_closedBall x₀ (2 * ρ)
  have hΩm : MeasurableSet (Omega : Set (WithLp 2 (ℝ × E))) := Omega.isOpen.measurableSet
  have hBK : ball x₀ ρ ⊆ K :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ))
  -- A cutoff `ζ`, equal to `1` on `closedBall x₀ ρ` and supported in `B(x₀, 2ρ) ⊆ K`.
  obtain ⟨zeta, hzeta, -, hone, hcpt, hts⟩ :=
    (isCompact_closedBall x₀ ρ).exists_contDiff_cutoff isOpen_ball
      (closedBall_subset_ball (by linarith : ρ < 2 * ρ))
  have htsK : tsupport zeta ⊆ K := hts.trans ball_subset_closedBall
  have hzetaTop : MemLp zeta ∞ volume := hzeta.continuous.memLp_top_of_hasCompactSupport hcpt _
  -- The cutoff `ζ u`, extended by zero to `H`, solves `tr (Ã D²W) = G` on `H` with
  -- `Ã = A₀ + 1_{Ω ∩ K} (A - A₀)` within `δ λ` of `A₀` and `G = 1_{Ω ∩ K} (ζ f + tr (A T))`.
  obtain ⟨W, hW0, hWv, hWD, hR⟩ :=
    exists_wkp_normalHalfSpace_value_ae_eq_indicator_mul hΩU hKc hKU hzeta hcpt htsK u hu0
  obtain ⟨hb, hbδ⟩ := aestronglyMeasurable_add_indicator_sub_and_norm_sub_le
    (hΩm.inter hKc.measurableSet) (hA.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    (mul_pos hδ hlam).le fun x hx => hosc₀ x hx.1 (hKρ₀ hx.2)
  have hG := memLp_indicator_mul_add_traceCLM_comp_leibnizRemainder hKc hzeta hzetaTop hA
    (Λ := ‖A₀‖ + δ * lam)
    (fun x hx => (norm_le_norm_add_norm_sub' (A x) A₀).trans
      (by linarith [hosc₀ x hx.1 (hKρ₀ hx.2)]))
    u hf huq hgq hR
  have hWq : MemLp (Wkp.value 2 W : WithLp 2 (ℝ × E) → ℝ) q
      ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) :=
    (((memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2
      ((hzetaTop.restrict _).fun_mul huq)).restrict _).ae_eq hWv.symm
  -- The half-space integrability gain for `W`.
  obtain ⟨V, hV, -⟩ := hgain a hlam hA₀ hb.restrict (ae_of_all _ hbδ) W hW0 (hG.restrict _) hWq
    (ae_traceCLM_comp_eq_indicator htsK A₀ (ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 htr))
      hWD)
  -- On `Ω ∩ B(x₀, ρ) ⊆ H`, where `ζ = 1`, the value of `W` is that of `u`.
  set B : Opens (WithLp 2 (ℝ × E)) := Omega ⊓ ⟨ball x₀ ρ, isOpen_ball⟩
  have hBH : B ≤ normalHalfSpace (E := E) a := fun x hx =>
    ((hΩU ▸ ⟨hx.1, hKU (hBK hx.2)⟩ :
      x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)).1
  have hval : (Wkp.value 2 V : WithLp 2 (ℝ × E) → ℝ)
      =ᵐ[volume.restrict (B : Set (WithLp 2 (ℝ × E)))] Wkp.value 2 u := by
    filter_upwards [ae_mono (Measure.restrict_mono hBH le_rfl) (hV.trans hWv),
      ae_restrict_mem B.isOpen.measurableSet] with x h hx
    rw [h, indicator_of_mem hx.1, interior_subset (hone (ball_subset_closedBall hx.2)), one_mul]
  exact ⟨ρ, hρ, hBK.trans hKU, Wkp.restrictL hBH 2 V, (Wkp.value_restrictL_ae hBH 2 V).trans hval,
    Wkp.iteratedGradient_restrictL_ae_eq_of_value_ae_eq hBH inf_le_left 1 hval⟩

end TauCeti
