/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Analysis.Analytic.Inverse

/-!
# Nash implicit roots

The analytic implicit root of a Nash scalar equation at a simple zero is a Nash germ.
The equation uses coordinates `σ ⊕ Unit`: `σ` indexes the parameters and `Unit` the
unknown. The parameter space may have dimension zero.

`TauCeti.IsNashAt.exists_isNashAt_eventually_eq_zero_iff` constructs the root and identifies
its graph with the zero set near the given point. `TauCeti.IsNashAt.implicit` applies to an
already specified solution continuous at the base point. These results allow simple-root sections
to be used as Nash functions, without requiring the defining equation to be polynomial.

The graph argument shrinks to a semialgebraic ball where the equation has semialgebraic
graph and the local uniqueness assertion holds. A smaller parameter ball keeps the entire
solution graph inside that ball. Tarski–Seidenberg makes the zero locus semialgebraic, and
the local Nash graph criterion then applies. The convergent analytic implicit function
theorem supplies existence and uniqueness, rather than either being assumed in the
simple-root theorem.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 8.1.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {σ : Type*} [Fintype σ]

/-- An analytic graph which locally is the zero set of a Nash equation is a Nash germ.
The equality of zero sets is required on a neighborhood in the full parameter/unknown space,
not only on the graph. -/
theorem IsNashAt.of_eventually_eq_zero_iff
    {f : (σ ⊕ Unit → ℝ) → ℝ} {g : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f (Sum.elim x (fun _ ↦ g x))) (hg : AnalyticAt ℝ g x)
    (hzero : ∀ᶠ p in 𝓝 (Sum.elim x (fun _ ↦ g x)),
      f p = 0 ↔ g (p ∘ Sum.inl) = p (Sum.inr ())) :
    IsNashAt g x := by
  obtain ⟨-, U, hUo, hxU, -, hfU⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hf
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hUo.mem_nhds hxU) hzero)
  let B := Metric.ball (Sum.elim x (fun _ : Unit ↦ g x)) r
  have hB : IsSemialgebraic B := isSemialgebraic_ball _ _
  have hBU : B ⊆ U := fun p hp ↦ (hball hp).1
  have hBzero : ∀ p ∈ B, f p = 0 ↔ g (p ∘ Sum.inl) = p (Sum.inr ()) :=
    fun p hp ↦ (hball hp).2
  have hgraph_cont : ContinuousAt (fun y ↦ Sum.elim y (fun _ : Unit ↦ g y)) x := by
    apply continuousAt_pi.mpr
    intro i
    cases i with
    | inl i => exact (continuous_apply i).continuousAt
    | inr i => exact hg.continuousAt
  obtain ⟨s, hs, hsmall⟩ := Metric.mem_nhds_iff.mp
    (hgraph_cont (Metric.ball_mem_nhds _ hr))
  let V := Metric.ball x s
  have hV : IsSemialgebraic V := isSemialgebraic_ball _ _
  have hfB := hfU.mono hB hBU
  have hZ : IsSemialgebraic (B ∩ {p | f p = 0}) := by
    simpa only [funext_iff, forall_const] using hfB.isSemialgebraic_inter_setOf_eq
      (isSemialgebraicOn_const (fun _ : Unit ↦ (0 : ℝ)) hB)
  have hgraph : Equiv.sumArrowEquivProdArrow σ Unit ℝ ⁻¹'
      V.graphOn (fun y (_ : Unit) ↦ g y) =
      (B ∩ {p | f p = 0}) ∩ (fun p ↦ p ∘ Sum.inl) ⁻¹' V := by
    ext p
    rw [mem_preimage_sumArrowEquivProdArrow_scalar_graphOn]
    constructor
    · rintro ⟨hpV, hgp⟩
      have hp : Sum.elim (p ∘ Sum.inl) (fun _ ↦ g (p ∘ Sum.inl)) = p := by
        ext i
        cases i with
        | inl i => rfl
        | inr i => simpa using hgp
      have hpB : p ∈ B := hp ▸ hsmall hpV
      exact ⟨⟨hpB, (hBzero p hpB).mpr hgp⟩, hpV⟩
    · rintro ⟨⟨hpB, hfp⟩, hpV⟩
      exact ⟨hpV, (hBzero p hpB).mp hfp⟩
  apply IsSemialgebraicOn.isNashAt (s := V) (f := g) _ hg
    (Metric.ball_mem_nhds _ hs)
  refine isSemialgebraicOn_def.mpr ⟨hV, ?_⟩
  rw [hgraph]
  exact hZ.inter (hV.preimage_comp Sum.inl)

/-- **The Nash implicit root theorem.** A Nash scalar equation with a simple zero admits a
Nash root germ in the parameter variables. Near the given point its zero set is exactly the
graph of this root. No polynomial equation or global semialgebraic domain is required. -/
theorem IsNashAt.exists_isNashAt_eventually_eq_zero_iff
    {f : (σ ⊕ Unit → ℝ) → ℝ} {x : σ → ℝ} {z : ℝ}
    (hf : IsNashAt f (Sum.elim x (fun _ ↦ z)))
    (hz : f (Sum.elim x (fun _ ↦ z)) = 0)
    (hd : deriv (fun t ↦ f (Sum.elim x (fun _ ↦ t))) z ≠ 0) :
    ∃ g : (σ → ℝ) → ℝ, IsNashAt g x ∧ g x = z ∧
      (∀ᶠ y in 𝓝 x, f (Sum.elim y (fun _ ↦ g y)) = 0) ∧
      ∀ᶠ p in 𝓝 (Sum.elim x (fun _ ↦ z)),
        f p = 0 ↔ g (p ∘ Sum.inl) = p (Sum.inr ()) := by
  have hjoin : AnalyticAt ℝ
      (fun q : (σ → ℝ) × ℝ ↦ Sum.elim q.1 (fun _ : Unit ↦ q.2)) (x, z) := by
    apply analyticAt_pi_iff.mpr
    intro i
    cases i with
    | inl i =>
      exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) i).analyticAt x).comp_of_eq
        (analyticAt_fst : AnalyticAt ℝ (Prod.fst : (σ → ℝ) × ℝ → (σ → ℝ)) (x, z)) rfl
    | inr i => exact analyticAt_snd
  obtain ⟨g, hg, hgz, hroot, hiff⟩ :=
    (hf.analyticAt.comp_of_eq hjoin rfl).exists_analyticAt_eventually_eq_zero_iff hz hd
  have hsplit : ContinuousAt (fun p : σ ⊕ Unit → ℝ ↦
      (p ∘ Sum.inl, p (Sum.inr ()))) (Sum.elim x (fun _ ↦ z)) := by
    fun_prop
  have hiff' : ∀ᶠ p in 𝓝 (Sum.elim x (fun _ ↦ z)),
      f p = 0 ↔ g (p ∘ Sum.inl) = p (Sum.inr ()) := by
    filter_upwards [hsplit.tendsto.eventually hiff] with p hp
    have hcoords : Sum.elim (p ∘ Sum.inl) (fun _ ↦ p (Sum.inr ())) = p := by
      ext i
      cases i with
      | inl i => rfl
      | inr i => cases i; rfl
    simpa only [Function.comp_apply, hcoords] using hp
  refine ⟨g, ?_, hgz, hroot, hiff'⟩
  exact IsNashAt.of_eventually_eq_zero_iff (f := f)
    (by simpa only [hgz] using hf) hg (by simpa only [hgz] using hiff')

/-- Any solution germ of a Nash scalar equation that is continuous at the base point is Nash
if the derivative in the unknown variable is nonzero at its central value. -/
theorem IsNashAt.implicit
    {f : (σ ⊕ Unit → ℝ) → ℝ} {g : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f (Sum.elim x (fun _ ↦ g x))) (hg : ContinuousAt g x)
    (hroot : ∀ᶠ y in 𝓝 x, f (Sum.elim y (fun _ ↦ g y)) = 0)
    (hd : deriv (fun t ↦ f (Sum.elim x (fun _ ↦ t))) (g x) ≠ 0) :
    IsNashAt g x := by
  obtain ⟨ψ, hψ, -, -, hiff⟩ :=
    hf.exists_isNashAt_eventually_eq_zero_iff hroot.self_of_nhds hd
  have hcont : ContinuousAt (fun y ↦ Sum.elim y (fun _ : Unit ↦ g y)) x := by
    apply continuousAt_pi.mpr
    intro i
    cases i with
    | inl i => exact (continuous_apply i).continuousAt
    | inr i => exact hg
  apply hψ.congr
  filter_upwards [hcont.tendsto.eventually hiff, hroot] with y hy hfy
  exact hy.mp hfy

end TauCeti
