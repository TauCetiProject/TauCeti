/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Analysis.Analytic.Inverse

/-!
# Nash implicit functions for finite systems

A finite system of Nash equations with invertible derivative in the unknown variables has a
Nash implicit solution. The equations are expressed on `σ ⊕ τ → ℝ`, with parameter coordinates
`σ` and unknown coordinates `τ`; the differential uses the corresponding product space.
The equation coordinates may have any finite index type `ρ`.

`HasStrictFDerivAt.isNashAt_implicitFunctionOfProdDomain` identifies Mathlib's chosen implicit
function as Nash, coordinatewise. The existence theorem also retains its local level-set
characterization. Finally, any continuous solution through the same point agrees with this
implicit function as a germ, so it is Nash without a separate analyticity assumption.
These results supply implicit coordinate changes for Nash charts, not just scalar root sections.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 8.1.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.

The analytic solution and local uniqueness are those of
`HasStrictFDerivAt.implicitFunctionOfProdDomain`; Nashness follows from the local Nash graph
criterion by identifying its graph with a level set on a smaller semialgebraic neighborhood.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
  {F : (σ ⊕ τ → ℝ) → (ρ → ℝ)} {u : (σ → ℝ) × (τ → ℝ)}

private theorem analyticAt_implicit_system
    (hF : ∀ i, IsNashAt (fun z ↦ F z i) (Sum.elim u.1 u.2)) :
    AnalyticAt ℝ (fun p : (σ → ℝ) × (τ → ℝ) ↦ F (Sum.elim p.1 p.2)) u := by
  have haF : AnalyticAt ℝ F (Sum.elim u.1 u.2) :=
    AnalyticAt.pi fun i ↦ (hF i).analyticAt
  apply haF.comp_of_eq (f := fun p : (σ → ℝ) × (τ → ℝ) ↦ Sum.elim p.1 p.2) _ rfl
  apply AnalyticAt.pi
  intro i
  cases i with
  | inl i => exact (analyticAt_pi_iff.mp analyticAt_fst) i
  | inr i => exact (analyticAt_pi_iff.mp analyticAt_snd) i

omit [Fintype ρ] in
/-- A locally unique continuous solution of a finite Nash system has a semialgebraic graph on a
smaller neighborhood. This helper keeps the graph inside the neighborhood of uniqueness. -/
private theorem isSemialgebraicOn_implicit_system [Finite ρ]
    (hF : ∀ i, IsNashAt (fun z ↦ F z i) (Sum.elim u.1 u.2))
    {g : (σ → ℝ) → (τ → ℝ)} (hg : ContinuousAt g u.1) (hgu : g u.1 = u.2)
    (hiff : ∀ᶠ z in 𝓝 (Sum.elim u.1 u.2),
      F z = F (Sum.elim u.1 u.2) ↔ g (z ∘ Sum.inl) = z ∘ Sum.inr) :
    ∃ U, IsOpen U ∧ u.1 ∈ U ∧ IsSemialgebraicOn g U := by
  let := Fintype.ofFinite ρ
  obtain ⟨-, W, hWo, huW, hFW⟩ :=
    forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mp hF
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hWo.mem_nhds huW) hiff)
  let B := Metric.ball (Sum.elim u.1 u.2) r
  have hB : IsSemialgebraic B := isSemialgebraic_ball _ _
  have hFB := hFW.mono hB (fun z hz ↦ (hball hz).1)
  have hlevel : IsSemialgebraic (B ∩ {z | F z = F (Sum.elim u.1 u.2)}) :=
    hFB.isSemialgebraic_inter_setOf_eq (isSemialgebraicOn_const _ hB)
  have hgraph : Tendsto (fun x ↦ Sum.elim x (g x)) (𝓝 u.1)
      (𝓝 (Sum.elim u.1 u.2)) := by
    have hc : ContinuousAt (fun x ↦ Sum.elim x (g x)) u.1 := by
      apply continuousAt_pi.mpr
      intro i
      cases i with
      | inl i => exact (continuousAt_pi.mp continuousAt_id) i
      | inr i => exact (continuousAt_pi.mp hg) i
    simpa only [hgu] using hc.tendsto
  obtain ⟨s, hs, hsB⟩ := Metric.mem_nhds_iff.mp
    (hgraph.eventually (Metric.ball_mem_nhds _ hr))
  let U := Metric.ball u.1 s
  have hU : IsSemialgebraic U := isSemialgebraic_ball _ _
  refine ⟨U, Metric.isOpen_ball, Metric.mem_ball_self hs,
    isSemialgebraicOn_def.mpr ⟨hU, ?_⟩⟩
  convert hlevel.inter (hU.preimage_comp Sum.inl) using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨hzU, hgz⟩
    have hzB : z ∈ B := by
      have hz := hsB hzU
      simpa only [B, Metric.mem_ball, mem_ofPred_eq, hgz, Sum.elim_comp_inl_inr] using hz
    exact ⟨⟨hzB, (hball hzB).2.mpr hgz⟩, hzU⟩
  · rintro ⟨⟨hzB, hzF⟩, hzU⟩
    exact ⟨hzU, (hball hzB).2.mp hzF⟩

/-- **Nash implicit function theorem for systems.** If the coordinates of a finite system are
Nash at `u` and its partial derivative in the unknown variables is invertible, every coordinate
of Mathlib's chosen implicit function is a Nash germ at the parameter point. -/
theorem _root_.HasStrictFDerivAt.isNashAt_implicitFunctionOfProdDomain
    {D : ((σ → ℝ) × (τ → ℝ)) →L[ℝ] (ρ → ℝ)}
    (hD : HasStrictFDerivAt (fun p ↦ F (Sum.elim p.1 p.2)) D u)
    (hInv : (D ∘L .inr ℝ (σ → ℝ) (τ → ℝ)).IsInvertible)
    (hF : ∀ i, IsNashAt (fun z ↦ F z i) (Sum.elim u.1 u.2)) (i : τ) :
    IsNashAt (fun x ↦ hD.implicitFunctionOfProdDomain hInv x i) u.1 := by
  have ha := analyticAt_implicit_system hF
  have hg := hD.analyticAt_implicitFunctionOfProdDomain hInv ha
  have hgu := eq_of_tendsto_nhds (hD.tendsto_implicitFunctionOfProdDomain hInv)
  have hsplit : Tendsto (fun z : σ ⊕ τ → ℝ ↦ (z ∘ Sum.inl, z ∘ Sum.inr))
      (𝓝 (Sum.elim u.1 u.2)) (𝓝 u) := by
    have hc : Continuous (fun z : σ ⊕ τ → ℝ ↦ (z ∘ Sum.inl, z ∘ Sum.inr)) := by fun_prop
    have hpoint : ((Sum.elim u.1 u.2) ∘ Sum.inl, (Sum.elim u.1 u.2) ∘ Sum.inr) = u :=
      Prod.ext (funext fun _ ↦ rfl) (funext fun _ ↦ rfl)
    simpa only [hpoint] using hc.tendsto (Sum.elim u.1 u.2)
  have hiff := hsplit.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv)
  simp only [Sum.elim_comp_inl_inr] at hiff
  obtain ⟨U, hUo, huU, hgU⟩ := isSemialgebraicOn_implicit_system hF hg.continuousAt hgu hiff
  exact (forall_isNashAt_apply_iff_exists_isSemialgebraicOn.mpr
    ⟨hg, U, hUo, huU, hgU⟩) i

omit [Fintype ρ] in
/-- A finite Nash system with invertible partial derivative admits a coordinatewise Nash
implicit solution. Near the original point its level set is exactly the graph of that solution.
No nonemptiness assumption on the parameter or unknown coordinate types is required. -/
theorem exists_isNashAt_implicit_system [Finite ρ]
    (hF : ∀ i, IsNashAt (fun z ↦ F z i) (Sum.elim u.1 u.2))
    (hInv : (fderiv ℝ (fun p : (σ → ℝ) × (τ → ℝ) ↦ F (Sum.elim p.1 p.2)) u ∘L
      .inr ℝ (σ → ℝ) (τ → ℝ)).IsInvertible) :
    ∃ g : (σ → ℝ) → (τ → ℝ), (∀ i, IsNashAt (fun x ↦ g x i) u.1) ∧ g u.1 = u.2 ∧
      (∀ᶠ x in 𝓝 u.1, F (Sum.elim x (g x)) = F (Sum.elim u.1 u.2)) ∧
      ∀ᶠ p in 𝓝 u, F (Sum.elim p.1 p.2) = F (Sum.elim u.1 u.2) ↔ g p.1 = p.2 := by
  let := Fintype.ofFinite ρ
  have ha := analyticAt_implicit_system hF
  exact ⟨ha.hasStrictFDerivAt.implicitFunctionOfProdDomain hInv,
    ha.hasStrictFDerivAt.isNashAt_implicitFunctionOfProdDomain hInv hF,
    eq_of_tendsto_nhds (ha.hasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain hInv),
    ha.hasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain hInv,
    ha.hasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv⟩

omit [Fintype ρ] in
/-- Every continuous solution of a nonsingular finite Nash system through the original point
is Nash there. Analyticity of the solution is a conclusion, not a hypothesis. -/
theorem isNashAt_of_implicit_system [Finite ρ]
    (hF : ∀ i, IsNashAt (fun z ↦ F z i) (Sum.elim u.1 u.2))
    (hInv : (fderiv ℝ (fun p : (σ → ℝ) × (τ → ℝ) ↦ F (Sum.elim p.1 p.2)) u ∘L
      .inr ℝ (σ → ℝ) (τ → ℝ)).IsInvertible)
    {g : (σ → ℝ) → (τ → ℝ)} (hg : ContinuousAt g u.1) (hgu : g u.1 = u.2)
    (hsol : ∀ᶠ x in 𝓝 u.1, F (Sum.elim x (g x)) = F (Sum.elim u.1 u.2)) (i : τ) :
    IsNashAt (fun x ↦ g x i) u.1 := by
  obtain ⟨ψ, hψ, -, -, hiff⟩ := exists_isNashAt_implicit_system hF hInv
  have hgraph : Tendsto (fun x ↦ (x, g x)) (𝓝 u.1) (𝓝 u) := by
    simpa only [hgu, id_eq, Prod.mk.eta] using (continuousAt_id.prodMk hg).tendsto
  apply (hψ i).congr
  filter_upwards [hgraph.eventually hiff, hsol] with x hx hs
  exact congrFun (hx.mp hs) i

end TauCeti
