/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.SolutionGerm
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Continuation of solutions of complex linear differential equations

A local solution of a monic analytic linear equation continues along every continuous path in
an arbitrary open coefficient domain. The continuation remains a local solution at every point
of the path.

`LinearEquation.IsSolutionNear.exists_isAnalyticContinuationAlong` constructs the continuation.
`LinearEquation.IsSolutionNear.continuesInside` supplies the hypothesis of the monodromy theorem.
`IsAnalyticContinuationAlong.isSolutionNear` preserves the equation for a caller's continuation.

The subdivision `exists_monotone_Icc_subset_open_cover_unitInterval` splits the compact parameter
interval into pieces whose images lie in discs inside the domain. The disc initial-value theorem
`LinearEquation.initialJetEquivOfEqEBall` and germ uniqueness
`LinearEquation.initialJetGermEquiv_symm_apply` supply
`LinearEquation.IsSolutionNear.exists_isSolutionNear_eball` to extend the germ across each piece.
`IsAnalyticContinuationAlong.union` glues the pieces.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §4.3, Theorem 4.7.
-/

public section

open Filter Set Topology TopologicalSpace
open scoped unitInterval

namespace TauCeti.LinearEquation

variable {U : Opens ℂ} {n : ℕ} {E : LinearEquation U n}

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
        obtain rfl : u = 0 := le_antisymm hu unitInterval.nonneg'
        exact hf
      exact ⟨fun _ ↦ f, IsAnalyticContinuationAlong.const hγ.continuousOn
        (fun u hu ↦ (hlocal u hu).analyticAt), hlocal, .rfl⟩
    | succ k ih =>
      obtain ⟨F, hF, hsol, hF0⟩ := ih
      obtain ⟨i, hi⟩ := htsub k
      have hak := hi ⟨le_rfl, htmono k.le_succ⟩
      have hdisc :
          (⟨Metric.eball (γ i) (ENNReal.ofReal (r i)), Metric.isOpen_eball⟩ : Opens ℂ) ≤ U := by
        apply SetLike.coe_subset_coe.mp
        simpa only [Opens.coe_mk, Metric.eball_ofReal] using hball i
      obtain ⟨g, hg, hga⟩ := (hsol (t k) le_rfl).exists_isSolutionNear_eball hdisc
        (by simpa only [Metric.eball_ofReal, mem_preimage] using hak)
      obtain ⟨G, hG, hGsol, hG0⟩ := continuation_step hγ (htmono k.le_succ) hF hsol
        (fun u hu ↦ hg (γ u) (by simpa only [Metric.eball_ofReal, mem_preimage] using hi hu)) hga
      exact ⟨G, hG, hGsol, hG0 ▸ hF0⟩
  obtain ⟨F, hF, hsol, hF0⟩ := hind m
  rw [hm m le_rfl] at hF hsol
  have hIic : Iic (1 : I) = univ := eq_univ_of_forall fun _ ↦ unitInterval.le_one'
  rw [hIic] at hF
  exact ⟨F, hF, hF0, fun u ↦ hsol u unitInterval.le_one'⟩

/-- A germ solving an analytic linear equation continues inside its coefficient domain. -/
theorem IsSolutionNear.continuesInside {a : ℂ} {f : ℂ → ℂ} (hf : E.IsSolutionNear a f) :
    ContinuesInside f U a := by
  apply ContinuesInside.of_forall
  intro γ hγ hγU hγ0
  obtain ⟨F, hF, hF0, -⟩ := (hγ0 ▸ hf).exists_isAnalyticContinuationAlong hγ hγU
  exact continuesAlong_iff_exists.mpr ⟨F, hF, hF0⟩

end TauCeti.LinearEquation

namespace TauCeti.IsAnalyticContinuationAlong

/-- A continuation inside the coefficient domain of an analytic linear equation over a
preconnected parameter set remains a local solution wherever its germ at one parameter solves the
equation. -/
theorem isSolutionNear {X : Type*} [TopologicalSpace X] {U : Opens ℂ} {n : ℕ}
    {E : LinearEquation U n} {F : X → ℂ → ℂ} {γ : X → ℂ} {s : Set X}
    (hF : IsAnalyticContinuationAlong F γ s) (hs : IsPreconnected s)
    (hγU : MapsTo γ s U) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
    (hsol : E.IsSolutionNear (γ a) (F a)) : E.IsSolutionNear (γ b) (F b) := by
  rw [LinearEquation.isSolutionNear_iff] at hsol ⊢
  let R : X → ℂ → ℂ := fun t z ↦ iteratedDeriv n (F t) z +
    ∑ j, HolomorphicFunctions.extend (E.coeff j) z * iteratedDeriv j (F t) z
  have hderiv (t : X) (ht : t ∈ s) (k : ℕ) :
      AnalyticAt ℂ (iteratedDeriv k (F t)) (γ t) := by
    simpa only [iteratedDeriv_eq_iterate] using (hF.analyticAt t ht).iterated_deriv k
  have hR : IsAnalyticContinuationAlong R γ s := by
    refine ⟨hF.continuousOn, ?_, ?_⟩
    · intro t ht
      exact (hderiv t ht n).add (Finset.analyticAt_fun_sum _ fun j _ ↦
        (HolomorphicFunctions.analyticOnNhd_extend (s := U) Subset.rfl (E.coeff j)
          (γ t) (hγU ht)).mul (hderiv t ht j))
    · intro t ht
      filter_upwards [hF.locallyEq t ht] with u hu
      filter_upwards [hu.eventuallyEq_nhds] with z hz
      simp only [R, hz.iteratedDeriv_eq]
  have hzero : R b =ᶠ[𝓝 (γ b)] 0 :=
    hR.eventuallyEq (IsAnalyticContinuationAlong.const hF.continuousOn
      (fun _ _ ↦ analyticAt_const)) hs ha hb (hsol.mono fun _ hz ↦ hz.2.2)
  filter_upwards [U.isOpen.mem_nhds (hγU hb), (hF.analyticAt b hb).eventually_analyticAt,
    hzero] with z hzU hzF hz
  exact ⟨hzU, hzF, hz⟩

end TauCeti.IsAnalyticContinuationAlong
