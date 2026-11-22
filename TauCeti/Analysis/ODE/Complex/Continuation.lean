/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.SolutionGerm
public import TauCeti.Analysis.ODE.Complex.OrdinaryPoint
public import TauCeti.Analysis.Complex.Conformal.GlobalBranch

/-!
# Continuation of solutions of analytic linear equations, and global solutions

Let `E : TauCeti.LinearEquation U n` be a monic analytic linear equation on an open domain `U`.
A solution germ of `E` at a point of `U` continues analytically along every path in `U`, and every
germ met along the way is again a solution germ. Consequently, on a simply connected domain every
local solution is the germ of a solution on the whole domain, and the unscaled initial jet at any
point of the domain is a linear isomorphism from the solution space onto `Fin n → ℂ`.

## Main results

* `LinearEquation.IsSolutionNear.exists_isAnalyticContinuationAlong`: a local solution at the
  starting point of a path in `U` has an analytic continuation along the path all of whose germs
  are local solutions.
* `IsAnalyticContinuationAlong.isSolutionNear`: **continuation preserves the equation** — any
  analytic continuation along a path in `U` that starts at a solution germ consists of solution
  germs.
* `LinearEquation.IsSolutionNear.continuesInside`: a solution germ continues inside `U`, in the
  sense of `TauCeti.ContinuesInside`.
* `LinearEquation.IsSolutionNear.exists_isSolution`: on a simply connected domain every local
  solution is the germ of a global solution.
* `LinearEquation.exists_isSolution_of_isSimplyConnected`: **the global initial-value theorem** —
  on a simply connected domain every unscaled initial jet has a solution on the whole domain,
  unique there.
* `LinearEquation.initialJetEquivOfIsSimplyConnected` and
  `LinearEquation.finrank_solutionSpace_of_isSimplyConnected`: on a simply connected domain the
  unscaled initial jet at any point is a linear isomorphism onto `Fin n → ℂ`, so the solution
  space has dimension `n`.

## Implementation notes

Continuation along a path `c : I → ℂ` is proved by a connectedness argument on the parameter
interval: the set of times `T` such that the germ continues, through solution germs, along `c` over
`[0, T]` is locally constant in `T`. Near a time `T`, the path stays in an open disc inside `U`
around `c T`; on that disc the disc initial-value theorem
(`LinearEquation.initialJetEquivOfEqEBall`) extends the solution germ reached at any nearby time to
a solution on the whole disc, which continues the germ further as a constant family. Global
solutions on a simply connected domain then come from the monodromy theorem
`TauCeti.ContinuesInside.exists_analyticOnNhd`; the branch it produces solves the equation because
continuation preserves the equation.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §4.3, Theorem 4.7 and
  its proof.
-/

public noncomputable section

open Filter Metric Set Topology TopologicalSpace unitInterval
open scoped ENNReal

namespace TauCeti

namespace LinearEquation

variable {U : Opens ℂ} {n : ℕ} {E : LinearEquation U n} {a : ℂ} {y : ℂ → ℂ}

/-- A solution of `E` near a point `a` of an open disc `V` contained in the domain agrees near `a`
with a solution of the equation restricted to `V`. Once global solutions are available, this is the
special case of `IsSolutionNear.exists_isSolution` for the restricted equation on a disc. -/
private theorem IsSolutionNear.exists_isSolution_restrict (hy : E.IsSolutionNear a y) {V : Opens ℂ}
    (hVU : V ≤ U) {z : ℂ} {r : ℝ≥0∞} (hV : (V : Set ℂ) = eball z r) (haV : a ∈ V) :
    ∃ w : ℂ → ℂ, (E.restrict hVU).IsSolution w ∧ w =ᶠ[𝓝 a] y := by
  let e := (E.restrict hVU).initialJetEquivOfEqEBall hV haV
  let w := HolomorphicFunctions.extend (e.symm fun j ↦ iteratedDeriv j y a).val
  have hw : (E.restrict hVU).IsSolution w :=
    ((E.restrict hVU).mem_solutionSpace _).mp (e.symm _).property
  have hwy : E.IsSolutionNear a w :=
    (isSolutionNear_restrict_iff hVU haV).mp (hw.isSolutionNear haV)
  have hjet : E.initialJetGerm hy.mem ⟨w, (coe_mem_solutionGerms _).mpr hwy⟩ =
      E.initialJetGerm hy.mem ⟨y, (coe_mem_solutionGerms _).mpr hy⟩ :=
    funext fun j ↦ by
      simp only [initialJetGerm_mk, w, e, iteratedDeriv_extend_initialJetEquivOfEqEBall_symm]
  exact ⟨w, hw, Germ.coe_eq.mp (congrArg Subtype.val (initialJetGerm_injective hy.mem hjet))⟩

/-! ### Continuation along a path -/

/-- The germ of `y` continues along `c` over the parameter times `[0, T]`, through solution germs
of `E`, with the continuation starting at `y` itself. -/
private def ContinuesUpTo (E : LinearEquation U n) (c : I → ℂ) (y : ℂ → ℂ) (T : I) : Prop :=
  ∃ f : I → ℂ → ℂ, IsAnalyticContinuationAlong f c (Iic T) ∧ f 0 = y ∧
    ∀ t ∈ Iic T, E.IsSolutionNear (c t) (f t)

/-- The germ of a local solution at `c 0` continues over the single time `0`. -/
private theorem continuesUpTo_zero {c : I → ℂ} (hc : Continuous c)
    (hy : E.IsSolutionNear (c 0) y) : ContinuesUpTo E c y 0 := by
  have h0 : ∀ t ∈ Iic (0 : I), t = 0 := fun t ht ↦ le_antisymm ht nonneg'
  exact ⟨fun _ ↦ y, .const hc.continuousOn fun t ht ↦ h0 t ht ▸ hy.analyticAt, rfl,
    fun t ht ↦ h0 t ht ▸ hy⟩

/-- **The extension step.** If the path stays in an open disc inside the domain between the times
`s ≤ t`, a continuation through solution germs up to time `s` extends to one up to time `t`: the
germ reached at time `s` extends to a solution on the disc, carried on as a constant family. -/
private theorem ContinuesUpTo.of_le {c : I → ℂ} (hc : Continuous c) {s t : I} (hst : s ≤ t)
    {V : Opens ℂ} (hVU : V ≤ U) {z : ℂ} {r : ℝ≥0∞} (hV : (V : Set ℂ) = eball z r)
    (hcV : ∀ u ∈ Icc s t, c u ∈ V) (h : ContinuesUpTo E c y s) : ContinuesUpTo E c y t := by
  classical
  obtain ⟨f, hf, hf0, hfE⟩ := h
  obtain ⟨w, hw, hwf⟩ :=
    (hfE s le_rfl).exists_isSolution_restrict hVU hV (hcV s ⟨le_rfl, hst⟩)
  refine ⟨fun u ↦ if u ≤ s then f u else w, ?_, ite_eq_left nonneg' |>.trans hf0, fun u hu ↦ ?_⟩
  · rw [← Iic_union_Icc_eq_Iic hst]
    refine .union (hf.congr fun u hu ↦ .of_eq (ite_eq_left hu))
      ((IsAnalyticContinuationAlong.const hc.continuousOn fun u hu ↦
        hw.analyticOnNhd _ (hcV u hu)).congr fun u hu ↦ ?_) isClosed_Iic isClosed_Icc
    by_cases hus : u ≤ s
    · obtain rfl := le_antisymm hus hu.1
      exact (EventuallyEq.of_eq (ite_eq_left le_rfl)).trans hwf.symm
    · exact .of_eq (ite_eq_right hus)
  · by_cases hus : u ≤ s
    · simpa only [ite_eq_left hus] using hfE u hus
    · have huV := hcV u ⟨(not_le.mp hus).le, hu⟩
      simpa only [ite_eq_right hus] using
        (isSolutionNear_restrict_iff hVU huV).mp (hw.isSolutionNear huV)

/-- **Continuability through solution germs is locally constant in the time.** Near a time `T`, the
path stays in an open disc inside the domain around `c T`, across which continuations extend
(`ContinuesUpTo.of_le`) and to which they restrict. -/
private theorem eventually_continuesUpTo_eq {c : I → ℂ} (hc : Continuous c)
    (hcU : ∀ t, c t ∈ U) (T : I) :
    ∀ᶠ u in 𝓝 T, ContinuesUpTo E c y u = ContinuesUpTo E c y T := by
  obtain ⟨r, hr, hrU⟩ := EMetric.isOpen_iff.mp U.isOpen (c T) (hcU T)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.preimage_mem_nhds (isOpen_eball.mem_nhds (mem_eball_self hr)))
  have hball : (ball T ε).OrdConnected :=
    (Real.ball_eq_Ioo (T : ℝ) ε ▸ ordConnected_Ioo).preimage_mono (Subtype.mono_coe _)
  have key : ∀ s ∈ ball T ε, ∀ t ∈ ball T ε, ContinuesUpTo E c y s → ContinuesUpTo E c y t := by
    intro s hs t ht h
    rcases le_total s t with hst | hts
    · exact h.of_le (V := ⟨eball (c T) r, isOpen_eball⟩) hc hst hrU rfl
        fun u hu ↦ hεV (hball.out hs ht hu)
    · obtain ⟨f, hf, hf0, hfE⟩ := h
      exact ⟨f, hf.mono (Iic_subset_Iic.mpr hts), hf0, fun u hu ↦ hfE u (le_trans hu hts)⟩
  filter_upwards [ball_mem_nhds T hε] with u hu
  exact propext ⟨key u hu T (mem_ball_self hε), key T (mem_ball_self hε) u hu⟩

/-- **Continuation of solutions along a path.** A solution of `E` near the starting point of a path
`c` in the domain has an analytic continuation along `c` that starts at the solution itself and
whose germ at every time is a solution germ of `E`. -/
theorem IsSolutionNear.exists_isAnalyticContinuationAlong {c : I → ℂ}
    (hy : E.IsSolutionNear (c 0) y) (hc : Continuous c) (hcU : ∀ t, c t ∈ U) :
    ∃ f : I → ℂ → ℂ, IsAnalyticContinuationAlong f c univ ∧ f 0 = y ∧
      ∀ t, E.IsSolutionNear (c t) (f t) := by
  have h1 : ContinuesUpTo E c y 1 :=
    isPreconnected_univ.apply_eq_of_eventually_eq (f := ContinuesUpTo E c y)
      (fun T _ ↦ by simpa only [nhdsWithin_univ] using eventually_continuesUpTo_eq hc hcU T)
      (mem_univ 0) (mem_univ 1) ▸ continuesUpTo_zero hc hy
  obtain ⟨f, hf, hf0, hfE⟩ := h1
  have hI : Iic (1 : I) = univ := eq_univ_of_forall fun _ ↦ le_one'
  exact ⟨f, hI ▸ hf, hf0, fun t ↦ hfE t le_one'⟩

/-- A solution germ of `E` continues along every path in the domain issuing from its base point. -/
theorem IsSolutionNear.continuesInside (hy : E.IsSolutionNear a y) :
    ContinuesInside y U a :=
  .of_forall fun c hc hcU hc0 ↦ by
    subst hc0
    obtain ⟨f, hf, hf0, -⟩ := hy.exists_isAnalyticContinuationAlong hc hcU
    exact continuesAlong_iff_exists.mpr ⟨f, hf, .of_eq hf0⟩

/-- **Analytic continuation preserves the equation.** An analytic continuation along a path in the
domain of `E` whose initial germ is a solution germ of `E` carries a solution germ of `E` at every
time. -/
theorem _root_.TauCeti.IsAnalyticContinuationAlong.isSolutionNear {f : I → ℂ → ℂ} {c : I → ℂ}
    (hf : IsAnalyticContinuationAlong f c univ) (hcU : ∀ t, c t ∈ U)
    (h0 : E.IsSolutionNear (c 0) (f 0)) (t : I) : E.IsSolutionNear (c t) (f t) := by
  obtain ⟨g, hg, hg0, hgE⟩ :=
    h0.exists_isAnalyticContinuationAlong (continuousOn_univ.mp hf.continuousOn) hcU
  exact (hgE t).congr
    (hg.eventuallyEq hf isPreconnected_univ (mem_univ 0) (mem_univ t) (.of_eq hg0))

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
  simpa only [hjoin.somePath.target] using
    (isSolutionNear_iff.mp (hcont.isSolutionNear hjoin.somePath_mem h0 1)).self_of_nhds.2.2

/-- On a simply connected domain, every unscaled initial jet at a point of the domain is the jet of
a solution on the whole domain. -/
theorem initialJet_surjective_of_isSimplyConnected (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) : Function.Surjective (E.initialJet ha) := by
  intro v
  obtain ⟨φ, rfl⟩ := initialJetGerm_surjective (E := E) ha v
  obtain ⟨y, hy, hyφ⟩ := (mem_solutionGerms_iff ha).mp φ.property
  obtain ⟨F, hF, hFy⟩ := hy.exists_isSolution hU
  let G := HolomorphicFunctions.of U F hF.analyticOnNhd.differentiableOn
  have hGF : EqOn F (HolomorphicFunctions.extend G) U := fun z hz ↦
    (HolomorphicFunctions.extend_of _ hz).symm
  have hGF' : HolomorphicFunctions.extend G =ᶠ[𝓝 a] F :=
    eventually_of_mem (U.isOpen.mem_nhds ha) fun z hz ↦ (hGF hz).symm
  have hext : HolomorphicFunctions.extend G =ᶠ[𝓝 a] y := hGF'.trans hFy
  refine ⟨⟨G, (E.mem_solutionSpace G).mpr (hF.congr hGF)⟩, funext fun j ↦ ?_⟩
  rw [initialJet_apply, initialJetGerm_apply ha φ hyφ.symm j]
  exact hext.iteratedDeriv_eq j

variable (E) in
/-- **The initial-jet isomorphism on a simply connected domain.** On a simply connected domain, the
unscaled initial jet at any point of the domain is a complex linear isomorphism from the solution
space onto `Fin n → ℂ`: every jet has exactly one solution on the whole domain. -/
def initialJetEquivOfIsSimplyConnected (hU : IsSimplyConnected (U : Set ℂ)) (ha : a ∈ U) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet ha)
    ⟨E.initialJet_injective_of_isPreconnected hU.isPathConnected.isConnected.isPreconnected ha,
      initialJet_surjective_of_isSimplyConnected hU ha⟩

/-- The forward map of `initialJetEquivOfIsSimplyConnected` is the unscaled initial jet. -/
@[simp]
theorem initialJetEquivOfIsSimplyConnected_apply (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) (f : E.solutionSpace) :
    E.initialJetEquivOfIsSimplyConnected hU ha f = E.initialJet ha f := (rfl)

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
    E.initialJet ha ((E.initialJetEquivOfIsSimplyConnected hU ha).symm v) = v :=
  (E.initialJetEquivOfIsSimplyConnected hU ha).apply_symm_apply v

/-- The underlying linear map of `initialJetEquivOfIsSimplyConnected` is the unscaled initial
jet. -/
@[simp]
theorem initialJetEquivOfIsSimplyConnected_toLinearMap (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) :
    (E.initialJetEquivOfIsSimplyConnected hU ha).toLinearMap = E.initialJet ha :=
  LinearMap.ext fun _ ↦ rfl

/-- The inverse of `initialJetEquivOfIsSimplyConnected` recovers a solution from its initial
jet. -/
@[simp]
theorem initialJetEquivOfIsSimplyConnected_symm_initialJet (hU : IsSimplyConnected (U : Set ℂ))
    (ha : a ∈ U) (f : E.solutionSpace) :
    (E.initialJetEquivOfIsSimplyConnected hU ha).symm (E.initialJet ha f) = f :=
  (E.initialJetEquivOfIsSimplyConnected hU ha).symm_apply_apply f

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

end LinearEquation

end TauCeti
