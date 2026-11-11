/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Inverse
public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.PartialEquiv

/-!
# The Nash inverse function theorem

A map between finite real coordinate spaces whose coordinates are Nash germs and whose
Fréchet derivative is invertible admits a local Nash inverse. Both the source and target
can be chosen open and semialgebraic, with semialgebraic graphs in both directions, inside
any prescribed source neighbourhood. Nashness holds at every point of these domains,
not just at the original point. The local inverse supplied by the native inverse function
theorem has the same Nash germ.

The analytic inverse function theorem supplies convergence and local bijectivity.
The local Nash graph criterion supplies semialgebraic coordinate graphs on a common
neighbourhood; exchanging graph coordinates then proves Nashness of the analytic inverse.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 8.1.
* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {σ τ : Type*} [Fintype σ] [Fintype τ]
  {f : (σ → ℝ) → (τ → ℝ)} {a : σ → ℝ}

/-- **The Nash inverse function theorem.** A map with Nash coordinate germs and invertible
Fréchet derivative at `a` restricts, inside any prescribed neighbourhood, to a local
homeomorphism with open semialgebraic source and target and semialgebraic graphs in both
directions. Every coordinate of the map and its inverse is Nash throughout those domains.
Empty coordinate index types are allowed. -/
theorem exists_openPartialHomeomorph_of_forall_isNashAt
    (hf : ∀ i, IsNashAt (fun x ↦ f x i) a)
    {L : (σ → ℝ) ≃L[ℝ] (τ → ℝ)} (hL : fderiv ℝ f a = L)
    {s : Set (σ → ℝ)} (hs : s ∈ 𝓝 a) :
    ∃ Θ : OpenPartialHomeomorph (σ → ℝ) (τ → ℝ),
      ⇑Θ = f ∧ a ∈ Θ.source ∧ Θ.source ⊆ s ∧
      IsSemialgebraicOn Θ Θ.source ∧ IsSemialgebraicOn Θ.symm Θ.target ∧
      (∀ x ∈ Θ.source, ∀ i, IsNashAt (fun z ↦ f z i) x) ∧
      ∀ y ∈ Θ.target, ∀ i, IsNashAt (fun z ↦ Θ.symm z i) y := by
  obtain ⟨U, hUo, haU, -, hG⟩ := exists_isSemialgebraicOn_of_forall_isNashAt hf
  have hfa : AnalyticAt ℝ f a := .pi fun i ↦ (hf i).analyticAt
  obtain ⟨e, he, hae, hes, hea, heia⟩ :=
    hfa.exists_openPartialHomeomorph hL (inter_mem (hUo.mem_nhds haU) hs)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hae)
  let Θ := e.restrOpen (Metric.ball a r) Metric.isOpen_ball
  have hsource : Θ.source = Metric.ball a r := by
    exact (e.restrOpen_source _ _).trans (inter_eq_right.mpr hball)
  have hΘ : ⇑Θ = f := (e.coe_restrOpen Metric.isOpen_ball).trans he
  have hsub : Θ.source ⊆ e.source := by rw [hsource]; exact hball
  have hBU : Θ.source ⊆ U := fun x hx ↦ (hes (hsub hx)).1
  have hB : IsSemialgebraic Θ.source := hsource ▸ isSemialgebraic_ball a r
  -- Assemble the graph by imposing each coordinate graph condition on the same input.
  have hsemi : IsSemialgebraicOn Θ Θ.source := by
    refine isSemialgebraicOn_def.mpr ⟨hB, ?_⟩
    convert (hB.preimage_comp Sum.inl).inter (IsSemialgebraic.iInter fun i ↦
      (hG i).graph.preimage_comp
        (Sum.elim Sum.inl (fun _ : Unit ↦ Sum.inr i))) using 1
    ext z
    rw [mem_preimage_sumArrowEquivProdArrow_graphOn, hΘ]
    simp only [mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hz, hfz⟩
      exact ⟨hz, fun i ↦ mem_preimage_sumArrowEquivProdArrow_scalar_graphOn.mpr
        ⟨hBU hz, congr_fun hfz i⟩⟩
    · rintro ⟨hz, hfi⟩
      exact ⟨hz, funext fun i ↦
        (mem_preimage_sumArrowEquivProdArrow_scalar_graphOn.mp (hfi i)).2⟩
  have hinv : IsSemialgebraicOn Θ.symm Θ.target :=
    Θ.toPartialEquiv.isSemialgebraicOn_symm hsemi
  refine ⟨Θ, hΘ, hsource ▸ Metric.mem_ball_self hr, hsub.trans (fun x hx ↦ (hes hx).2),
    hsemi, hinv, ?_, ?_⟩
  · intro x hx i
    exact (hG i).isNashAt (analyticAt_pi_iff.mp (hea x (hsub hx)) i)
      (mem_of_superset (Θ.open_source.mem_nhds hx) hBU)
  · intro y hy i
    have hai : AnalyticAt ℝ Θ.symm y := by
      rw [e.coe_restrOpen_symm Metric.isOpen_ball]
      exact heia y hy.1
    have hcoord : IsSemialgebraicOn (fun z (_ : Unit) ↦ Θ.symm z i) Θ.target := by
      simpa only [MvPolynomial.eval_X] using
        hinv.eval_comp (fun _ : Unit ↦ MvPolynomial.X i)
    exact hcoord.isNashAt (analyticAt_pi_iff.mp hai i) (Θ.open_target.mem_nhds hy)

end TauCeti

namespace HasStrictFDerivAt

open TauCeti

/-- The native local inverse of a map with Nash coordinate germs has Nash coordinate germs.
The invertible strict derivative is the same one used by the native construction. -/
theorem isNashAt_localInverse {σ τ : Type*} [Fintype σ] [Fintype τ]
    {f : (σ → ℝ) → (τ → ℝ)} {a : σ → ℝ}
    {L : (σ → ℝ) ≃L[ℝ] (τ → ℝ)} (hL : HasStrictFDerivAt f (L : _ →L[ℝ] _) a)
    (hf : ∀ i, IsNashAt (fun x ↦ f x i) a) (i : σ) :
    IsNashAt (fun y ↦ hL.localInverse f L a y i) (f a) := by
  obtain ⟨Θ, hΘ, ha, -, -, -, -, hinv⟩ :=
    exists_openPartialHomeomorph_of_forall_isNashAt hf hL.hasFDerivAt.fderiv
      (s := univ) univ_mem
  have hleft : ∀ᶠ x in 𝓝 a, Θ.symm (f x) = x := by
    rw [← hΘ]
    exact Θ.eventually_left_inverse ha
  have heq := hL.localInverse_unique hleft
  have htarget : f a ∈ Θ.target := by rw [← hΘ]; exact Θ.map_source ha
  exact (hinv (f a) htarget i).congr (heq.mono fun y hy ↦ congr_fun hy i)

end HasStrictFDerivAt
