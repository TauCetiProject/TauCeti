/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.ChangeOfVariables
public import TauCeti.Analysis.PDE.Regularity.Hessian.ContinuousCoefficient.Regularity
public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Regularity
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Flattening
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.Gluing

/-!
# `W^{2,q}` regularity up to a `C²` boundary for continuous principal coefficients

Let `E` be a finite-dimensional real inner product space, `1 < p, q < ∞`, and let `Ω ⊆ ℝ × E` be
open. This file proves Gilbarg–Trudinger's Lemma 9.16 up to a curved boundary: a strong solution
`u ∈ W^{2,p}(Ω)` of

`tr (A D²u) = f` in `Ω`, `u = 0` on `∂Ω`,

whose principal coefficient `A` is continuous up to the boundary and elliptic there, and with `f`,
`u` and the weak gradient `∇u` in `L^q(Ω)`, lies in `W^{2,q}`:

* `TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_isChangeOfVariables`:
  near every point `x₀` of an open set `U` on which a change of variables of order two straightens
  `Ω` to a half-space, for solutions vanishing on `∂Ω ∩ U`; it is the curved counterpart of the
  statement near a flat boundary portion
  (`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_normalHalfSpace`);
* `TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_contDiff_graph`:
  near a boundary point at which, in rigid coordinates, `∂Ω` is the graph of a `C²` function;
* `TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph`: on a
  bounded open set with `C²` boundary, `u ∈ W^{2,q}(Ω)` for every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)`
  solving `tr (A D²u) + ⟪b, ∇u⟫ + c u = f` with bounded measurable `b` and `c`.

The exponents `p` and `q` are unrelated: the statements improve integrability when `q > p`. The
membership of `u` and `∇u` in `L^q(Ω)` is a hypothesis, as in the interior and flat statements. The
global statement is the regularity input of the solvability of the Dirichlet problem in
`W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` (Gilbarg–Trudinger, Theorem 9.15), whose a priori estimate is
`TauCeti.exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`.

## The argument

* **Flattening.** Let `Φ` map the part of `U'` in the half-space `H = {a < x.fst}` onto `Ω ∩ U`,
  with inverse `Ψ`. Then `v = u ∘ Φ ∈ W^{2,p}(H ∩ U')` solves
  `tr (A' D²v) + ⟪b', ∇v⟫ = f ∘ Φ` with `A' = TauCeti.PDE.nondivPullbackPrincipal Φ Ψ A`, which is
  continuous and elliptic at `Ψ x₀`, and the bounded drift
  `b' = TauCeti.PDE.nondivPullbackDrift Φ Ψ A 0`, once the chart is restricted to where `A` is
  bounded. Zero boundary values carry over
  (`TauCeti.Wkp.IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_compL`).
* **The flat statement.** Since `v` and `∇v` lie in `L^q`, so does `f ∘ Φ - ⟪b', ∇v⟫`, and the
  statement near a flat boundary portion places `v` in `W^{2,q}` on a ball about `Ψ x₀`.
* **Back to `Ω`.** Precomposition with `Ψ` (`TauCeti.Wkp.compL`) takes that element back to
  `W^{2,q}` of `Ω` near `x₀`, with value `v ∘ Ψ = u`.
* **Gluing.** Interior points are covered by the interior statement
  (`TauCeti.exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_continuousOn`), and the
  local pieces near the points of the compact closure of `Ω` glue
  (`TauCeti.Wkp.exists_value_ae_eq_of_isCompact`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (straightening the boundary) and Lemma 9.16.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace Filter
open scoped ENNReal NNReal Gradient ContDiff Topology

namespace TauCeti

open Wkp

section Transport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {mu : Measure F} [mu.IsAddHaarMeasure] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] {Omega U Ω' : Opens F} {Φ Ψ : F → F} {L L' c c' : ℝ}

omit [Fact (1 ≤ q)] in
/-- The restriction to `Ω ∩ U` of `TauCeti.Wkp.IsChangeOfVariables.memLp_value_compL` and
`TauCeti.Wkp.IsChangeOfVariables.memLp_gradient_firstOrder_compL`: if the value and the weak
gradient of `u ∈ W^{2,p}(Ω)` lie in `L^q(Ω)`, so do those of `u ∘ Φ` on `Ω'`, for a change of
variables `Φ` of order two from `Ω'` into `Ω ∩ U`. -/
private theorem memLp_value_compL_restrictL_and_memLp_gradient
    (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ U) Φ L c) (u : Wkp mu Omega p 2)
    (huq : MemLp (value 2 u) q (mu.restrict (Omega : Set F)))
    (hgq : MemLp (iteratedGradient 0 (lowerOrder 1 u)) q (mu.restrict (Omega : Set F))) :
    MemLp (value 2 (compL hΦ (restrictL inf_le_left 2 u))) q (mu.restrict (Ω' : Set F)) ∧
      MemLp (iteratedGradient 0 (lowerOrder 1 (compL hΦ (restrictL inf_le_left 2 u)))) q
        (mu.restrict (Ω' : Set F)) := by
  have hD := Measure.restrict_mono (μ := mu)
    (show ((Omega ⊓ U : Opens F) : Set F) ⊆ Omega from fun y hy => hy.1) le_rfl
  refine ⟨hΦ.memLp_value_compL _ ((huq.mono_measure hD).ae_eq
    (value_restrictL_ae inf_le_left 2 u).symm), ?_⟩
  rw [← gradient_firstOrder_one]
  refine hΦ.memLp_gradient_firstOrder_compL _ ?_
  rw [gradient_firstOrder_one, lowerOrder_restrictL]
  exact (hgq.mono_measure hD).ae_eq (iteratedGradient_restrictL_ae inf_le_left 0 _).symm

/-- **Regularity back along a straightening chart.** Let `Φ` and `Ψ` be mutually inverse changes of
variables of order two between `Ω'` and `Ω ∩ U`, with `Ψ` continuous on `U`, and let `x₀ ∈ U`. If
the value of `u ∘ Φ` on `Ω' ∩ B(Ψ x₀, ρ)` is that of some `w ∈ W^{2,q}(Ω' ∩ B(Ψ x₀, ρ))`, then `u`
lies in `W^{2,q}(Ω ∩ B(x₀, ρ₁))` for a ball `B(x₀, ρ₁) ⊆ U`, with its value and weak Hessian. -/
private theorem exists_wkp_value_ae_eq_of_value_ae_eq_compL
    (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ U) Φ L c)
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ U) Ω' Ψ L' c') (hΨc : ContinuousOn Ψ U)
    (hΦΨ : RightInvOn Ψ Φ (Omega ⊓ U : Opens F)) {x₀ : F} (hx₀ : x₀ ∈ U) {ρ : ℝ} (hρ : 0 < ρ)
    (u : Wkp mu Omega p 2) (w : Wkp mu (Ω' ⊓ ⟨ball (Ψ x₀) ρ, isOpen_ball⟩) q 2)
    (hw : (value 2 w : F → ℝ) =ᵐ[mu.restrict
        ((Ω' ⊓ ⟨ball (Ψ x₀) ρ, isOpen_ball⟩ : Opens F) : Set F)]
      value 2 (compL hΦ (restrictL inf_le_left 2 u))) :
    ∃ ρ₁ > 0, ball x₀ ρ₁ ⊆ U ∧
      ∃ v : Wkp mu (Omega ⊓ ⟨ball x₀ ρ₁, isOpen_ball⟩) q 2,
        (value 2 v : F → ℝ) =ᵐ[mu.restrict
            ((Omega ⊓ ⟨ball x₀ ρ₁, isOpen_ball⟩ : Opens F) : Set F)] value 2 u ∧
        (iteratedGradient 1 v : F → IteratedGradient F 1) =ᵐ[mu.restrict
            ((Omega ⊓ ⟨ball x₀ ρ₁, isOpen_ball⟩ : Opens F) : Set F)] iteratedGradient 1 u := by
  -- A ball about `x₀` inside `U` that `Ψ` maps into `B(Ψ x₀, ρ)`.
  obtain ⟨ρ₁, hρ₁, hρ₁U⟩ := Metric.isOpen_iff.1 (hΨc.isOpen_inter_preimage U.isOpen isOpen_ball)
    x₀ ⟨hx₀, mem_ball_self hρ⟩
  set B : Opens F := Omega ⊓ ⟨ball x₀ ρ₁, isOpen_ball⟩
  have hBΩ : B ≤ Omega := inf_le_left
  have hBD : B ≤ Omega ⊓ U := fun y hy => ⟨hy.1, (hρ₁U hy.2).1⟩
  have hΨB : IsChangeOfVariables 2 B (Ω' ⊓ ⟨ball (Ψ x₀) ρ, isOpen_ball⟩) Ψ L' c' :=
    hΨ.mono_set hBD fun y hy => ⟨hΨ.mapsTo (hBD hy), (hρ₁U hy.2).2⟩
  have hB'Ω' : ((Ω' ⊓ ⟨ball (Ψ x₀) ρ, isOpen_ball⟩ : Opens F) : Set F) ⊆ Ω' := fun y hy => hy.1
  -- On `B`, the value of `w ∘ Ψ` is `u ∘ Φ ∘ Ψ = u`.
  have hval : (value 2 (compL hΨB w) : F → ℝ) =ᵐ[mu.restrict (B : Set F)] value 2 u := by
    filter_upwards [value_compL_ae hΨB w, hΨB.ae_comp hw,
      hΨB.ae_comp (ae_restrict_of_ae_restrict_of_subset hB'Ω'
        (value_compL_ae hΦ (restrictL inf_le_left 2 u))),
      ae_restrict_of_ae_restrict_of_subset hBD (value_restrictL_ae inf_le_left 2 u),
      ae_restrict_mem B.isOpen.measurableSet] with y h1 h2 h3 h4 hy
    rw [h1, h2, h3, hΦΨ (hBD hy), h4]
  exact ⟨ρ₁, hρ₁, fun y hy => (hρ₁U hy).1, compL hΨB w, hval,
    (iteratedGradient_ae_eq_of_value_ae_eq 1 (hval.trans (value_restrictL_ae hBΩ 2 u).symm)).trans
      (iteratedGradient_restrictL_ae hBΩ 1 u)⟩

omit [MeasurableSpace F] [BorelSpace F] in
/-- **The pulled-back principal coefficient at `Ψ x₀`.** Let `Φ` and `Ψ` be mutually inverse
changes of variables of order two between `U'` and `U`, with `Φ` mapping `s` into `Ω`, and let
`x₀ ∈ U`. If `A` is continuous within `Ω` at `x₀`, and elliptic there when `x₀` lies in the closure
of `Ω`, then `TauCeti.PDE.nondivPullbackPrincipal Φ Ψ A` is continuous within `s` at `Ψ x₀`, and
elliptic there when `Ψ x₀` lies in the closure of `s`. -/
private theorem continuousWithinAt_nondivPullbackPrincipal_and_elliptic {U' : Opens F}
    (hΦ : IsChangeOfVariables 2 U' U Φ L c) (hΨ : IsChangeOfVariables 2 U U' Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {s : Set F} (hs : MapsTo Φ s Omega)
    {A : F → F →L[ℝ] F} {x₀ : F} (hx₀ : x₀ ∈ U) (hcont : ContinuousWithinAt A Omega x₀)
    (hell : x₀ ∈ closure (Omega : Set F) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x₀ ξ, ξ⟫_ℝ) :
    ContinuousWithinAt (PDE.nondivPullbackPrincipal Φ Ψ A) s (Ψ x₀) ∧
      (Ψ x₀ ∈ closure s → ∃ lam : ℝ, 0 < lam ∧
        ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪PDE.nondivPullbackPrincipal Φ Ψ A (Ψ x₀) ξ, ξ⟫_ℝ) := by
  have hx₀' : Ψ x₀ ∈ U' := hΨ.mapsTo hx₀
  have hΦx₀ : Φ (Ψ x₀) = x₀ := hΦΨ hx₀
  have hΦc : ContinuousAt Φ (Ψ x₀) :=
    hΦ.differentiableOn.continuousOn.continuousAt (U'.isOpen.mem_nhds hx₀')
  refine ⟨PDE.continuousWithinAt_nondivPullbackPrincipal hΨ hΦc hs (by rwa [hΦx₀])
    (by rwa [hΦx₀]), fun hcl => ?_⟩
  -- `x₀ = Φ (Ψ x₀)` lies in the closure of `Φ '' s ⊆ Ω`.
  have hcl' := hΦc.continuousWithinAt.mem_closure_image hcl
  rw [hΦx₀] at hcl'
  obtain ⟨lam, hlam, hA₀⟩ := hell (closure_mono hs.image_subset hcl')
  obtain ⟨hpos, hbound⟩ := PDE.nondivPullbackPrincipal_elliptic hΦ hΨ hΨΦ hΦΨ hx₀' hlam
    (by rwa [hΦx₀])
  exact ⟨_, hpos, hbound⟩

omit [Fact (1 ≤ q)] in
/-- **Moving bounded lower-order terms to the right side.** If `f`, the value of `u ∈ W^{2,p}(Ω)`
and its weak gradient lie in `L^q(Ω)`, and `b` and `c` are measurable with `‖b‖ ≤ β` and
`|c| ≤ γ` almost everywhere, then `f - ⟪b, ∇u⟫ - c u` lies in `L^q(Ω)`. -/
private theorem memLp_sub_inner_sub_mul {b : F → F} {β : ℝ}
    (hb : AEStronglyMeasurable b (mu.restrict (Omega : Set F)))
    (hbβ : ∀ᵐ x ∂mu.restrict (Omega : Set F), ‖b x‖ ≤ β) {c₀ : F → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c₀ (mu.restrict (Omega : Set F)))
    (hcγ : ∀ᵐ x ∂mu.restrict (Omega : Set F), |c₀ x| ≤ γ) (u : Wkp mu Omega p 2) {f : F → ℝ}
    (hf : MemLp f q (mu.restrict (Omega : Set F)))
    (huq : MemLp (value 2 u) q (mu.restrict (Omega : Set F)))
    (hgq : MemLp (iteratedGradient 0 (lowerOrder 1 u)) q (mu.restrict (Omega : Set F))) :
    MemLp (fun x => f x - ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ - c₀ x * value 2 u x) q
      (mu.restrict (Omega : Set F)) := by
  refine (hf.sub (hgq.of_le_mul (c := β) (hb.inner (Lp.aestronglyMeasurable _)) ?_)).sub
    (huq.of_le_mul (c := γ) (hc.mul (Lp.aestronglyMeasurable _)) ?_)
  · filter_upwards [hbβ] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · filter_upwards [hcγ] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

end Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Regularity for bounded principal coefficients.** The statement of
`TauCeti.exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_isChangeOfVariables`,
under the additional hypothesis that `A` is bounded on `Ω ∩ U`. -/
private theorem exists_wkp_value_ae_eq_of_norm_le (hp : 1 < p) (hp_top : p ≠ ⊤) (hq : 1 < q)
    (hq_top : q ≠ ⊤) (a : ℝ) {Omega U U' : Opens (WithLp 2 (ℝ × E))}
    {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {L L' c c' : ℝ}
    (hΦ : IsChangeOfVariables 2 U' U Φ L c) (hΨ : IsChangeOfVariables 2 U U' Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (himage : Φ '' ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U') =
      (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))) {Λ : ℝ}
    (hAΛ : ∀ y ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ U, ‖A y‖ ≤ Λ)
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
  -- The flat side `Ω' = H ∩ U'` and the curved side `Ω ∩ U` of the chart.
  set Ω' : Opens (WithLp 2 (ℝ × E)) := normalHalfSpace (E := E) a ⊓ U' with hΩ'_def
  have hΩ'm : MeasurableSet (Ω' : Set (WithLp 2 (ℝ × E))) := Ω'.isOpen.measurableSet
  obtain ⟨hΦ', hΨ'⟩ := hΦ.inf_of_image_eq hΨ hΨΦ himage
  have hΦmaps := hΦ'.mapsTo
  have hΦΩ : MapsTo Φ Ω' Omega := fun x hx => (hΦmaps hx).1
  have hΦc : ContinuousOn Φ U' := hΦ.differentiableOn.continuousOn
  have hΦΨ' : RightInvOn Ψ Φ (Omega ⊓ U : Opens (WithLp 2 (ℝ × E))) := hΦΨ.mono fun y hy => hy.2
  have hD : ((Omega ⊓ U : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) ⊆ Omega :=
    fun y hy => hy.1
  -- The pulled-back function `v = u ∘ Φ` and its coefficients.
  set v := compL hΦ' (restrictL inf_le_left 2 u) with hv_def
  set A' := PDE.nondivPullbackPrincipal Φ Ψ A
  set b' := PDE.nondivPullbackDrift Φ Ψ A 0
  have hac : (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))).map Φ ≪
      volume.restrict (Omega : Set (WithLp 2 (ℝ × E))) :=
    (Measure.absolutelyContinuous_of_le_smul (hΦ'.map_restrict_le volume)).trans
      (Measure.restrict_mono hD le_rfl).absolutelyContinuous
  obtain ⟨hA', hb'⟩ := PDE.aestronglyMeasurable_nondivPullbackPrincipal_and_nondivPullbackDrift
    hΨ (s := (Ω' : Set (WithLp 2 (ℝ × E)))) (hΦc.mono fun x hx => hx.2) hΩ'm
    (fun x hx => (hΦmaps hx).2)
    ((hA.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable) (b := 0) aestronglyMeasurable_const
  have hb'Λ : ∀ x ∈ (Ω' : Set (WithLp 2 (ℝ × E))),
      ‖b' x‖ ≤ L' * 0 + Module.finrank ℝ (WithLp 2 (ℝ × E)) * (L' * Λ) := fun x hx =>
    PDE.norm_nondivPullbackDrift_le hΨ (hΦmaps hx).2 (by simp) (hAΛ _ (hΦmaps hx))
  -- `v` solves `tr (A' D²v) = f ∘ Φ - ⟪b', ∇v⟫` on `Ω'`.
  have hpull :=
    PDE.ae_traceCLM_nondivPullbackPrincipal_comp_add_inner_nondivPullbackDrift_add_mul_eq
    hΦ' hΨ' hΦΨ' hp_top (restrictL inf_le_left 2 u) (A := A) (b := 0) (c₀ := 0) (f := f) (by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hD htr,
        iteratedGradient_restrictL_ae inf_le_left 1 u] with y h1 h2
      rw [h2, h1]
      simp)
  -- `u ∘ Φ` and its gradient lie in `L^q(Ω')`, hence so does the right side.
  obtain ⟨hvq, hgvq⟩ := memLp_value_compL_restrictL_and_memLp_gradient hΦ' u huq hgq
  have hf'q := memLp_sub_inner_sub_mul hb' ((ae_restrict_iff' hΩ'm).2 (ae_of_all _ hb'Λ))
    (aestronglyMeasurable_const (b := (0 : ℝ))) (ae_of_all _ fun _ => abs_zero.le) v
    (hΦ'.memLp_comp hΩ'm subset_rfl hΦΩ hf) hvq hgvq
  -- The flat statement for `v` near `Ψ x₀`.
  have hx₀' : Ψ x₀ ∈ U' := hΨ.mapsTo hx₀
  obtain ⟨hcont', hell'⟩ :=
    continuousWithinAt_nondivPullbackPrincipal_and_elliptic hΦ hΨ hΨΦ hΦΨ hΦΩ hx₀ hcont hell
  obtain ⟨ρ, hρ, -, w, hwv, -⟩ :=
    exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_normalHalfSpace hp hp_top
      hq hq_top a (Omega := Ω') (U := U') (by simp [hΩ'_def]) hA' hx₀' hcont' hell' v
      (hΦ'.exists_w1p0_value_ae_eq_mul_value_compL hp_top hΦc hΦ.mapsTo
        (hΨ.differentiableOn.continuousOn.mono fun y hy => hy.2) hΨ'.mapsTo
        (hΨΦ.mono fun x hx => hx.2) hu0)
      hf'q hvq hgvq (by
        filter_upwards [hpull] with x hx
        rw [← hv_def] at hx
        simp [← hx])
  -- Back to `Ω` along `Ψ`.
  exact exists_wkp_value_ae_eq_of_value_ae_eq_compL hΦ' hΨ' hΨ.differentiableOn.continuousOn hΦΨ'
    hx₀ hρ u w hwv

/-- **`W^{2,q}` regularity near a straightened boundary portion for continuous principal
coefficients** (Gilbarg–Trudinger, Lemma 9.16). Let `1 < p, q < ∞`, let `Ω, U, U' ⊆ ℝ × E` be open,
and let `Φ` and `Ψ` be mutually inverse changes of variables of order two between `U'` and `U` such
that `Φ` maps the part of `U'` in the half-space `H = {a < x.fst}` onto `Ω ∩ U`. Let `A` be a field
of endomorphisms of `ℝ × E`, measurable on `Ω`, and let `x₀ ∈ U` be a point at which `A` is
continuous within `Ω` and, if `x₀` lies in the closure of `Ω`, elliptic:
`λ ‖ξ‖² ≤ ⟪A x₀ ξ, ξ⟫` for some `λ > 0`. Let `u ∈ W^{2,p}(Ω)` vanish on `∂Ω ∩ U`, in the sense that
`ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` compactly supported in `U`, and solve `tr (A D²u) = f`
almost everywhere on `Ω`, where `f`, the value of `u` and its weak gradient lie in `L^q(Ω)`. Then
there is a ball `B(x₀, ρ) ⊆ U` such that `u` lies in `W^{2,q}(Ω ∩ B(x₀, ρ))`: some element `v` of
that space has the value and the weak Hessian of `u` there.

The point `x₀` may lie on `∂Ω`, no relation between `p` and `q` is assumed, `A` need not be
symmetric, and nothing is assumed about `∂Ω` outside `U`. -/
theorem exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_isChangeOfVariables
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hq : 1 < q) (hq_top : q ≠ ⊤) (a : ℝ)
    {Omega U U' : Opens (WithLp 2 (ℝ × E))} {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}
    {L L' c c' : ℝ} (hΦ : IsChangeOfVariables 2 U' U Φ L c)
    (hΨ : IsChangeOfVariables 2 U U' Ψ L' c') (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (himage : Φ '' ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U') =
      (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)
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
  -- `A` is bounded on `Ω ∩ W` for an open `W ∋ x₀`, by continuity within `Ω`.
  have hnorm := ContinuousWithinAt.norm (f := A) hcont
  obtain ⟨t, ht, htO, hxt⟩ := _root_.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1
    (hnorm.tendsto.eventually_lt_const (lt_add_one ‖A x₀‖)))
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨t, htO⟩
  -- Restrict the chart to `U ∩ W`.
  obtain ⟨U'₁, hΦ₁, hΨ₁, hΨΦ₁, hΦΨ₁, himage₁⟩ := hΦ.exists_inf_of_image_eq hΨ hΨΦ hΦΨ himage W
  obtain ⟨ρ, hρ, hρU, hv⟩ := exists_wkp_value_ae_eq_of_norm_le hp hp_top hq hq_top a hΦ₁ hΨ₁ hΨΦ₁
    hΦΨ₁ himage₁ hA (fun y hy => (ht y hy.2.2 hy.1).le) (U := U ⊓ W) ⟨hx₀, hxt⟩ hcont hell u
    (fun ψ hψ hψc hψs => hu0 ψ hψ hψc fun x hx => (hψs hx).1) hf huq hgq htr
  exact ⟨ρ, hρ, fun y hy => (hρU hy).1, hv⟩

/-- **`W^{2,q}` regularity near a `C²` boundary graph for continuous principal coefficients**
(Gilbarg–Trudinger, Lemma 9.16). Let `1 < p, q < ∞` and let `Ω ⊆ ℝ × E` be open. Suppose that
inside the normal cylinder of half-height `h₀` and radius `r₀`, in rigid coordinates `e`, `Ω` is the
region `{φ(y) < t}` above the graph of a `C²` function `φ : E → ℝ` with `φ 0 = 0`, so that `e⁻¹ 0`
is a boundary point. Let `W` be an open neighbourhood of `e⁻¹ 0`, and let `A` be a measurable field
of endomorphisms of `ℝ × E`, continuous within `Ω` and elliptic at `e⁻¹ 0`. Let `u ∈ W^{2,p}(Ω)`
vanish on `∂Ω ∩ W`, in the sense that `ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` compactly
supported in `W`, and solve `tr (A D²u) = f` almost everywhere on `Ω`, where `f`, the value of `u`
and its weak gradient lie in `L^q(Ω)`. Then there is a ball `B(e⁻¹ 0, ρ) ⊆ W` such that `u` lies in
`W^{2,q}(Ω ∩ B(e⁻¹ 0, ρ))`. -/
theorem exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_contDiff_graph
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hq : 1 < q) (hq_top : q ≠ ⊤)
    {Omega W : Opens (WithLp 2 (ℝ × E))} {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
    {φ : E → ℝ} {h₀ r₀ : ℝ} (hh₀ : 0 < h₀) (hr₀ : 0 < r₀) (hφ0 : φ 0 = 0) (hφ : ContDiff ℝ 2 φ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hW : e.symm 0 ∈ W)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ContinuousWithinAt A Omega (e.symm 0))
    (hell : ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A (e.symm 0) ξ, ξ⟫_ℝ)
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2) {f : WithLp 2 (ℝ × E) → ℝ}
    (hu0 : ∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
        W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
          fun x => ψ x * Wkp.value 2 u x)
    (hf : MemLp f q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (huq : MemLp (Wkp.value 2 u) q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hgq : MemLp (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) q
      (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (htr : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x) :
    ∃ ρ > 0, ball (e.symm 0) ρ ⊆ W ∧
      ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E)))
          (Omega ⊓ ⟨ball (e.symm 0) ρ, isOpen_ball⟩) q 2,
        (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict
            ((Omega ⊓ ⟨ball (e.symm 0) ρ, isOpen_ball⟩ : Opens (WithLp 2 (ℝ × E))) :
              Set (WithLp 2 (ℝ × E)))]
          Wkp.value 2 u ∧
        (Wkp.iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
            =ᵐ[volume.restrict
              ((Omega ⊓ ⟨ball (e.symm 0) ρ, isOpen_ball⟩ : Opens (WithLp 2 (ℝ × E))) :
                Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient 1 u := by
  -- Flatten the boundary by `Φ = e⁻¹ ∘ G⁻¹`, `G` graph flattening by `φ`, with inverse `G ∘ e`.
  obtain ⟨U', U, L, h0, -, hΦ, hΨ, himage⟩ :=
    exists_isChangeOfVariables_normalHalfSpace_of_contDiff one_le_two hh₀ hr₀ hφ0 hφ hgraph
  set G := graphFlattening φ hφ.continuous
  have hΦ0 : (e.symm ∘ G.symm) 0 = e.symm 0 := by simp [G, hφ0]
  -- Restrict the chart to `U ∩ W`.
  obtain ⟨U'₂, hΦ₂, hΨ₂, hΨΦ₂, hΦΨ₂, himage₂⟩ :=
    hΦ.exists_inf_of_image_eq hΨ (fun x _ => by simp) (fun y _ => by simp) himage W
  obtain ⟨ρ, hρ, hρU, hv⟩ :=
    exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_isChangeOfVariables hp
      hp_top hq hq_top 0 hΦ₂ hΨ₂ hΨΦ₂ hΦΨ₂ himage₂ hA (x₀ := e.symm 0)
      ⟨hΦ0 ▸ hΦ.mapsTo h0, hW⟩ hcont (fun _ => hell) u
      (fun ψ hψ hψc hψs => hu0 ψ hψ hψc fun x hx => (hψs hx).2) hf huq hgq htr
  exact ⟨ρ, hρ, fun y hy => (hρU hy).2, hv⟩

/-- **Global `W^{2,q}` regularity on a bounded `C²` domain for continuous principal coefficients**
(Gilbarg–Trudinger, Lemma 9.16). Let `1 < p, q < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with
`C²` boundary: at every boundary point `x`, in rigid coordinates `e` with `e x = 0`, inside a normal
cylinder, `Ω` is the region above the graph of a `C²` function `φ` with `φ 0 = 0`. Let `A` be a
field of endomorphisms of `ℝ × E`, continuous within `Ω` and elliptic at every
point of the closure of `Ω`, and let `b` and `c` be measurable with `‖b x‖ ≤ β` and `|c x| ≤ γ`
for almost every `x ∈ Ω`. Let `u ∈ W^{2,p}(Ω)` with `u ∈ W^{1,p}_0(Ω)` solve

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `Ω`,

where `f`, the value of `u` and its weak gradient lie in `L^q(Ω)`. Then `u ∈ W^{2,q}(Ω)`: some
`v ∈ W^{2,q}(Ω)` has the value and the weak Hessian of `u`. -/
theorem exists_wkp_value_ae_eq_of_traceCLM_comp_add_inner_add_mul_eq_of_contDiff_graph
    (hp : 1 < p) (hp_top : p ≠ ⊤) (hq : 1 < q) (hq_top : q ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
    (hu : firstOrder 1 u ∈ w1p0Submodule volume Omega p) {f : WithLp 2 (ℝ × E) → ℝ}
    (hf : MemLp f q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (huq : MemLp (Wkp.value 2 u) q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hgq : MemLp (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) q
      (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (heq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) +
        ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) :
    ∃ v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega q 2,
      (Wkp.value 2 v : WithLp 2 (ℝ × E) → ℝ)
          =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] Wkp.value 2 u ∧
        (Wkp.iteratedGradient 1 v : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1)
          =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))] Wkp.iteratedGradient 1 u := by
  have hcontΩ : ContinuousOn A Omega := fun y hy => hcont y (subset_closure hy)
  have hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    hcontΩ.aestronglyMeasurable Omega.isOpen.measurableSet
  -- The lower-order terms move to the right side, which stays in `L^q(Ω)`.
  set f₀ := fun x => f x - ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ -
    c x * Wkp.value 2 u x
  have hf₀ : MemLp f₀ q (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
    memLp_sub_inner_sub_mul hb hbβ hc hcγ u hf huq hgq
  have htr : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f₀ x := by
    filter_upwards [heq] with x hx
    simp only [f₀, ← hx]
    ring
  -- Zero boundary values give `ψ u ∈ W^{1,p}_0(Ω)` for every smooth compactly supported `ψ`.
  have hu0 : ∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
        W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
          fun x => ψ x * Wkp.value 2 u x := fun ψ hψ hψc => by
    simpa only [value_firstOrder] using
      W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hu
  -- Every point of the closure of `Ω` has a neighbourhood `V` with `u ∈ W^{2,q}(Ω ∩ V)`.
  have hloc : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ V : Opens (WithLp 2 (ℝ × E)), x ∈ V ∧
        ∃ w : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (Omega ⊓ V) q 2,
          (Wkp.value 2 w : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume.restrict
            ((Omega ⊓ V : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))]
            Wkp.value 2 u := fun x hx => by
    by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
    · -- At an interior point, by the interior statement.
      obtain ⟨ρ, hρ, -, w, hw, -⟩ :=
        exists_wkp_value_ae_eq_of_trace_comp_iteratedGradient_eq_of_continuousOn hp hp_top hq
          hq_top hcontΩ (fun y hy => hell y (subset_closure hy)) u hf₀ huq hgq
          (htr.mono fun y hy => (traceCLM_apply _).symm.trans hy) hxΩ
      refine ⟨⟨ball x ρ, isOpen_ball⟩, mem_ball_self hρ, restrictL inf_le_right 2 w, ?_⟩
      have hsub : ((Omega ⊓ ⟨ball x ρ, isOpen_ball⟩ : Opens (WithLp 2 (ℝ × E))) :
          Set (WithLp 2 (ℝ × E))) ⊆ ball x ρ := fun y hy => hy.2
      exact (value_restrictL_ae inf_le_right 2 w).trans
        (ae_restrict_of_ae_restrict_of_subset hsub hw)
    · -- At a boundary point, by flattening the boundary.
      obtain ⟨e, φ, h₀, r₀, hex, hh₀, hr₀, hφ0, hφ, hgraph⟩ :=
        hbdry x ⟨hx, by rwa [Omega.isOpen.interior_eq]⟩
      have hx₀ : e.symm 0 = x := by rw [← hex, e.symm_apply_apply]
      obtain ⟨ρ, hρ, -, w, hw, -⟩ :=
        exists_wkp_value_ae_eq_of_traceCLM_comp_eq_of_continuousWithinAt_of_contDiff_graph hp
          hp_top hq hq_top (W := ⊤) hh₀ hr₀ hφ0 hφ hgraph trivial hA (hx₀ ▸ hcont x hx)
          (hx₀ ▸ hell x hx) u (fun ψ hψ hψc _ => hu0 ψ hψ hψc) hf₀ huq hgq htr
      exact ⟨⟨ball (e.symm 0) ρ, isOpen_ball⟩, hx₀ ▸ mem_ball_self hρ, w, hw⟩
  -- The local pieces glue along a finite subcover of the compact closure of `Ω`.
  obtain ⟨v, hv⟩ := Wkp.exists_value_ae_eq_of_isCompact hΩ.isCompact_closure subset_closure 2 hloc
  exact ⟨v, hv, iteratedGradient_ae_eq_of_value_ae_eq 1 hv⟩

end TauCeti
