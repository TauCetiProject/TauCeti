/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.SolutionGerm
public import TauCeti.Analysis.Complex.Conformal.GlobalBranch

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

On a simply connected domain, the monodromy theorem `TauCeti.ContinuesInside.exists_analyticOnNhd`
turns every local solution into the germ of a global solution
(`LinearEquation.IsSolutionNear.exists_isSolution`); the global branch solves the equation because
continuation preserves it. Hence every unscaled initial jet has a unique solution on the whole
domain (`LinearEquation.exists_isSolution_of_isSimplyConnected`), the initial jet at any point is a
linear isomorphism `LinearEquation.initialJetEquivOfIsSimplyConnected` from the solution space onto
`Fin n → ℂ`, and the solution space has dimension `n`
(`LinearEquation.finrank_solutionSpace_of_isSimplyConnected`).

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §4.3, Theorem 4.7 and
  its proof.
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

namespace TauCeti.LinearEquation

variable {U : Opens ℂ} {n : ℕ} {E : LinearEquation U n} {a : ℂ} {y : ℂ → ℂ}

/-! ### Global solutions on simply connected domains -/

/-- **Global solutions on a simply connected domain.** On a simply connected domain, every solution
of `E` near a point of the domain agrees near that point with a solution on the whole domain. -/
theorem IsSolutionNear.exists_isSolution (hU : IsSimplyConnected (U : Set ℂ))
    (hy : E.IsSolutionNear a y) : ∃ F : ℂ → ℂ, E.IsSolution F ∧ F =ᶠ[𝓝 a] y := by
  obtain ⟨F, hF, hFy⟩ := hy.continuesInside.exists_analyticOnNhd U.isOpen hU hy.mem
  refine ⟨F, (isSolution_iff _ _).mpr ⟨hF, fun z hz ↦ ?_⟩, hFy⟩
  -- `F` continues itself along a path from `a` to `z`, starting at a solution germ.
  have hjoin := hU.isPathConnected.joinedIn a hy.mem z hz
  have hcont : IsAnalyticContinuationAlong (fun _ ↦ F) hjoin.somePath univ :=
    .const hjoin.somePath.continuous.continuousOn fun t _ ↦ hF _ (hjoin.somePath_mem t)
  have h0 : E.IsSolutionNear (hjoin.somePath 0) F := by
    rw [hjoin.somePath.source]
    exact hy.congr hFy.symm
  obtain ⟨-, -, hzE⟩ := (isSolutionNear_iff.mp (hcont.isSolutionNear isPreconnected_univ
    (fun t _ ↦ hjoin.somePath_mem t) (mem_univ 0) (mem_univ 1) h0)).self_of_nhds
  simpa only [hjoin.somePath.target] using hzE

/-- On a simply connected domain, every unscaled initial jet at a point of the domain is the jet of
a solution on the whole domain. -/
theorem initialJet_surjective_of_isSimplyConnected (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) : Function.Surjective (E.initialJet ha) := by
  intro v
  obtain ⟨φ, rfl⟩ := initialJetGerm_surjective (E := E) ha v
  obtain ⟨y, hy, hyφ⟩ := (mem_solutionGerms_iff ha).mp φ.property
  obtain ⟨F, hF, hFy⟩ := hy.exists_isSolution hU
  refine ⟨hF.toSolutionSpace, funext fun j ↦ ?_⟩
  rw [hF.initialJet_toSolutionSpace ha, initialJetGerm_apply ha φ hyφ.symm j]
  exact hFy.iteratedDeriv_eq j

variable (E) in
/-- **The initial-jet isomorphism on a simply connected domain.** On a simply connected domain, the
unscaled initial jet at any point of the domain is a complex linear isomorphism from the solution
space onto `Fin n → ℂ`: every jet has exactly one solution on the whole domain. -/
noncomputable def initialJetEquivOfIsSimplyConnected (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet ha)
    ⟨E.initialJet_injective_of_isPreconnected hU.isPathConnected.isConnected.isPreconnected ha,
      initialJet_surjective_of_isSimplyConnected hU ha⟩

/-- The forward map of `initialJetEquivOfIsSimplyConnected` is the unscaled initial jet. -/
@[simp]
theorem initialJetEquivOfIsSimplyConnected_apply (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) (f : E.solutionSpace) :
    E.initialJetEquivOfIsSimplyConnected hU ha f = E.initialJet ha f := by
  unfold initialJetEquivOfIsSimplyConnected
  exact LinearEquiv.ofBijective_apply _ f

/-- **The global initial-value theorem.** On a simply connected domain, every unscaled initial jet
at a point `a` of the domain is the jet at `a` of a solution on the whole domain, unique on the
domain. -/
theorem exists_isSolution_of_isSimplyConnected (hU : IsSimplyConnected (U : Set ℂ)) (ha : a ∈ U)
    (v : Fin n → ℂ) :
    ∃ y : ℂ → ℂ, E.IsSolution y ∧ (∀ j : Fin n, iteratedDeriv j y a = v j) ∧
      ∀ w : ℂ → ℂ, E.IsSolution w → (∀ j : Fin n, iteratedDeriv j w a = v j) → EqOn w y U := by
  obtain ⟨f, hf⟩ := initialJet_surjective_of_isSimplyConnected (E := E) hU ha v
  have hjet (j : Fin n) : iteratedDeriv j (HolomorphicFunctions.extend f.val) a = v j := by
    rw [← initialJet_apply ha, hf]
  have hfE := (E.mem_solutionSpace _).mp f.property
  exact ⟨_, hfE, hjet, fun w hw hwv ↦
    hw.eqOn_of_isPreconnected_of_iteratedDeriv_eq hU.isPathConnected.isConnected.isPreconnected
      hfE ha fun j ↦ (hwv j).trans (hjet j).symm⟩

/-- The inverse of `initialJetEquivOfIsSimplyConnected` has the prescribed initial jet. -/
@[simp]
theorem initialJet_initialJetEquivOfIsSimplyConnected_symm (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) (v : Fin n → ℂ) :
    E.initialJet ha ((E.initialJetEquivOfIsSimplyConnected hU ha).symm v) = v := by
  rw [← initialJetEquivOfIsSimplyConnected_apply hU ha, LinearEquiv.apply_symm_apply]

/-- The underlying linear map of `initialJetEquivOfIsSimplyConnected` is the unscaled initial
jet. -/
@[simp]
theorem initialJetEquivOfIsSimplyConnected_toLinearMap (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) :
    (E.initialJetEquivOfIsSimplyConnected hU ha).toLinearMap = E.initialJet ha :=
  LinearMap.ext fun f ↦ by
    rw [LinearEquiv.coe_coe, initialJetEquivOfIsSimplyConnected_apply hU ha]

/-- The inverse of `initialJetEquivOfIsSimplyConnected` recovers a solution from its initial
jet. -/
@[simp]
theorem initialJetEquivOfIsSimplyConnected_symm_initialJet (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) (f : E.solutionSpace) :
    (E.initialJetEquivOfIsSimplyConnected hU ha).symm (E.initialJet ha f) = f := by
  rw [← initialJetEquivOfIsSimplyConnected_apply hU ha, LinearEquiv.symm_apply_apply]

/-- The `j`-th derivative at `a` of the extended solution
`(E.initialJetEquivOfIsSimplyConnected hU ha).symm v` is `v j`. -/
@[simp]
theorem iteratedDeriv_extend_initialJetEquivOfIsSimplyConnected_symm
    (hU : IsSimplyConnected (U : Set ℂ)) (ha : a ∈ U) (v : Fin n → ℂ) (j : Fin n) :
    iteratedDeriv j
      (HolomorphicFunctions.extend ((E.initialJetEquivOfIsSimplyConnected hU ha).symm v).val) a =
      v j := by
  rw [← initialJet_apply ha, initialJet_initialJetEquivOfIsSimplyConnected_symm]

/-- On a simply connected domain the solution space of a monic equation of order `n` has complex
dimension `n`. -/
theorem finrank_solutionSpace_of_isSimplyConnected (hU : IsSimplyConnected (U : Set ℂ)) :
    Module.finrank ℂ E.solutionSpace = n := by
  obtain ⟨a, ha⟩ := hU.isPathConnected.nonempty
  simpa using (E.initialJetEquivOfIsSimplyConnected hU ha).finrank_eq

end TauCeti.LinearEquation
