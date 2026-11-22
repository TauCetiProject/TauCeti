/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.SolutionGerm
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
import TauCeti.Analysis.ODE.Complex.OrdinaryPoint

/-!
# Continuation of solutions of complex linear differential equations

A local solution of a monic analytic linear equation continues along every continuous path in
an arbitrary open coefficient domain. The continuation remains a local solution at every point
of the path.

`LinearEquation.IsSolutionNear.exists_isAnalyticContinuationAlong` constructs the continuation.
`LinearEquation.IsSolutionNear.continuesInside` supplies the hypothesis of the monodromy theorem.

The proof subdivides the compact parameter interval into pieces whose images lie in discs
inside the domain. The initial-value theorem on a disc extends the germ across each piece.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §4.3, Theorem 4.7.
-/

public section

open Filter Set Topology TopologicalSpace
open scoped unitInterval

namespace TauCeti.LinearEquation

variable {U : Opens ℂ} {n : ℕ} {E : LinearEquation U n}

private theorem IsSolutionNear.exists_disc_extension {a c : ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hf : E.IsSolutionNear a f)
    (hball : (⟨Metric.ball c r, Metric.isOpen_ball⟩ : Opens ℂ) ≤ U)
    (ha : a ∈ Metric.ball c r) :
    ∃ g : ℂ → ℂ, (∀ z ∈ Metric.ball c r, E.IsSolutionNear z g) ∧ g =ᶠ[𝓝 a] f := by
  let E' := E.restrict hball
  let s := (E'.initialJetEquivOfEqEBall (c := c) (r := ENNReal.ofReal r)
    (Metric.eball_ofReal.symm) ha).symm (fun j ↦ iteratedDeriv j f a)
  let g := HolomorphicFunctions.extend s.val
  have hg : ∀ z ∈ Metric.ball c r, E.IsSolutionNear z g := fun z hz ↦
    (isSolutionNear_restrict_iff hball hz).mp
      (((E'.mem_solutionSpace _).mp s.property).isSolutionNear hz)
  refine ⟨g, hg, Germ.coe_eq.mp ?_⟩
  have heq : (⟨g, (coe_mem_solutionGerms (hball ha)).mpr (hg a ha)⟩ :
      E.solutionGerms (hball ha)) = ⟨f, (coe_mem_solutionGerms (hball ha)).mpr hf⟩ := by
    apply E.initialJetGerm_injective (hball ha)
    ext j
    simp only [initialJetGerm_mk]
    exact E'.iteratedDeriv_extend_initialJetEquivOfEqEBall_symm
      (Metric.eball_ofReal.symm) ha _ j
  exact congrArg Subtype.val heq

private theorem continuation_step {γ : I → ℂ} (hγ : Continuous γ) {a b : I} (hab : a ≤ b)
    {F : I → ℂ → ℂ} (hF : IsAnalyticContinuationAlong F γ (Iic a))
    (hsol : ∀ t ≤ a, E.IsSolutionNear (γ t) (F t)) {g : ℂ → ℂ}
    (hg : ∀ t ∈ Icc a b, E.IsSolutionNear (γ t) g)
    (hga : g =ᶠ[𝓝 (γ a)] F a) :
    ∃ G : I → ℂ → ℂ, IsAnalyticContinuationAlong G γ (Iic b) ∧
      (∀ t ≤ b, E.IsSolutionNear (γ t) (G t)) ∧ G 0 = F 0 := by
  let G : I → ℂ → ℂ := fun t ↦ if t ≤ a then F t else g
  have hleft : IsAnalyticContinuationAlong G γ (Iic a) :=
    hF.congr fun t ht ↦ by simp [G, mem_Iic.mp ht]
  have hright : IsAnalyticContinuationAlong G γ (Icc a b) := by
    apply (IsAnalyticContinuationAlong.const hγ.continuousOn
      (fun t ht ↦ (hg t ht).analyticAt)).congr
    intro t ht
    by_cases hta : t ≤ a
    · have hta' : t = a := le_antisymm hta ht.1
      subst t
      simpa only [G, ite_eq_left le_rfl] using hga.symm
    · simp [G, hta]
  refine ⟨G, ?_, ?_, by simp [G]⟩
  · simpa only [Iic_union_Icc_eq_Iic hab] using hleft.union hright isClosed_Iic isClosed_Icc
  · intro t ht
    dsimp only [G]
    split_ifs with hta
    · exact hsol t hta
    · exact hg t ⟨le_of_not_ge hta, ht⟩

/-- A local solution of an analytic linear equation continues along every continuous path in its
coefficient domain, remaining a local solution throughout the path. -/
theorem IsSolutionNear.exists_isAnalyticContinuationAlong {γ : I → ℂ} {f : ℂ → ℂ}
    (hf : E.IsSolutionNear (γ 0) f) (hγ : Continuous γ) (hγU : ∀ t, γ t ∈ U) :
    ∃ F : I → ℂ → ℂ, IsAnalyticContinuationAlong F γ univ ∧
      F 0 =ᶠ[𝓝 (γ 0)] f ∧ ∀ t, E.IsSolutionNear (γ t) (F t) := by
  choose r hr hball using fun t ↦ Metric.isOpen_iff.mp U.isOpen (γ t) (hγU t)
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ Metric.isOpen_ball.preimage hγ)
      (fun u _ ↦ mem_iUnion.mpr ⟨u, Metric.mem_ball_self (hr u)⟩)
  have hind : ∀ k, ∃ F : I → ℂ → ℂ, IsAnalyticContinuationAlong F γ (Iic (t k)) ∧
      (∀ u ≤ t k, E.IsSolutionNear (γ u) (F u)) ∧ F 0 =ᶠ[𝓝 (γ 0)] f := by
    intro k
    induction k with
    | zero =>
      rw [ht0]
      have hlocal : ∀ u ≤ (0 : I), E.IsSolutionNear (γ u) f := by
        intro u hu
        obtain rfl : u = 0 := le_antisymm hu bot_le
        exact hf
      exact ⟨fun _ ↦ f, IsAnalyticContinuationAlong.const hγ.continuousOn
        (fun u hu ↦ (hlocal u hu).analyticAt), hlocal, .rfl⟩
    | succ k ih =>
      obtain ⟨F, hF, hsol, hF0⟩ := ih
      obtain ⟨i, hi⟩ := htsub k
      have hak := hi ⟨le_rfl, htmono k.le_succ⟩
      obtain ⟨g, hg, hga⟩ := (hsol (t k) le_rfl).exists_disc_extension (hball i) hak
      obtain ⟨G, hG, hGsol, hG0⟩ := continuation_step hγ (htmono k.le_succ) hF hsol
        (fun u hu ↦ hg (γ u) (hi hu)) hga
      exact ⟨G, hG, hGsol, hG0 ▸ hF0⟩
  obtain ⟨F, hF, hsol, hF0⟩ := hind m
  rw [hm m le_rfl] at hF hsol
  have hIic : Iic (1 : I) = univ := eq_univ_of_forall fun u ↦ u.property.2
  rw [hIic] at hF
  exact ⟨F, hF, hF0, fun u ↦ hsol u le_top⟩

/-- A germ solving an analytic linear equation continues inside its coefficient domain. -/
theorem IsSolutionNear.continuesInside {a : ℂ} {f : ℂ → ℂ} (hf : E.IsSolutionNear a f) :
    ContinuesInside f U a := by
  apply ContinuesInside.of_forall
  intro γ hγ hγU hγ0
  obtain ⟨F, hF, hF0, -⟩ := (hγ0 ▸ hf).exists_isAnalyticContinuationAlong hγ hγU
  exact continuesAlong_iff_exists.mpr ⟨F, hF, hF0⟩

end TauCeti.LinearEquation
