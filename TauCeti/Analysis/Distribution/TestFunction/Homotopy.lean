/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Prod
public import TauCeti.Analysis.Distribution.TestFunction.CylinderHomotopy
public import TauCeti.Analysis.Distribution.TestFunction.Prod
public import TauCeti.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The homotopy formula for currents

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces and let `H : E × ℝ → E'` be a
homotopy which is smooth near `Ω × [0, 1]` and *proper on `Ω × [0, 1]`*: the set
`(Ω × [0, 1]) ∩ H ⁻¹' K` is compact for every compact `K ⊆ Ω'`. Its slices `Hₜ = H (·, t)`,
`t ∈ [0, 1]`, are then smooth and proper from `Ω` to `Ω'`, so they push currents on `Ω` forward to
currents on `Ω'` (`TestFunction.pullbackCLM`).

The **homotopy operator** `TestFunction.homotopyPullbackCLM` sends a test `(k + 1)`-form `ω` on
`Ω'` to the test `k`-form

`x ↦ ∫₀¹ (H^* ω)(x, t)(∂ₜ, ·) dt`

on `Ω`, the cylinder homotopy operator `TauCeti.cylinderHomotopy` of the pullback `H^* ω`
(`TestFunction.homotopyPullbackCLM_apply_of_mem`). It is continuous for the LF topologies, so for
a `k`-current `T` on `Ω` the composite `T ∘ homotopyPullbackCLM` is a `(k + 1)`-current on `Ω'`:
the pushforward `H_# ([[0, 1]] × T)` of the product of `T` with the unit interval. The homotopy
identity `K ∘ d = H₁^* - H₀^* - d ∘ K` on test forms gives the **homotopy formula**

`∂ H_# ([[0, 1]] × T) + H_# ([[0, 1]] × ∂ T) = H₁# T - H₀# T`,

where `∂ T = T ∘ d`; in degree zero the second term is absent. If `‖∂ₜ H‖ ≤ A` and the spatial
derivative of `H` has operator norm at most `L` on `Ω × [0, 1]`, then
`M(H_# ([[0, 1]] × T)) ≤ A L ^ k M(T)`. A short homotopy therefore gives a small filling of
`H₁# T - H₀# T - H_# ([[0, 1]] × ∂ T)`.

No properness of `H` on all of `Ω × ℝ` is assumed, and `T` need not have compact support. In the
construction, `H` is reparametrized in time by `Real.smoothTransition`, which makes it smooth on
`Ω × ℝ` and proper on every slab `Ω × [c, d]`. The graph map `(x, t) ↦ (H (x, σ t), t)` is then
proper from `Ω × ℝ` to `Ω' × ℝ`, and the pulled-back form is cut off in time by tensoring with a
fixed test function `ψ` equal to one near `[0, 1]` (`TestFunction.prodSMulCLM`). The cylinder
homotopy operator only sees the times `t ∈ [0, 1]`, where the cutoff is one, and the change of
variables `s = σ t` removes the reparametrization.

## Main declarations

* `TestFunction.homotopyPullbackCLM`: the homotopy operator `K = h ∘ H^*` on test forms.
* `TestFunction.homotopyPullbackCLM_apply_of_mem`: on `Ω`, it is the cylinder homotopy operator of
  the pullback `H^* ω`; `TestFunction.homotopyPullbackCLM_apply_of_notMem`: it vanishes off `Ω`.
* `TestFunction.tsupport_homotopyPullbackCLM_subset`: its support lies over the points whose track
  under `H` meets the support of the form.
* `TestFunction.homotopyPullbackCLM_eq_cylinderHomotopyCLM_comp_pullbackCLM`: when `H` is proper
  on an open set containing `Ω × [0, 1]`, `H_# ([[0, 1]] × T)` is the pushforward along `H` of the
  product current `T ∘ TestFunction.cylinderHomotopyCLM`.
* `TestFunction.homotopyPullbackCLM_comp_extDerivCLM`: `K ∘ d = H₁^* - H₀^* - d ∘ K`, and
  `TestFunction.homotopyPullbackCLM_comp_extDerivCLM_finZero` in degree zero.
* `ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM`: the homotopy formula for
  currents, and `ContinuousLinearMap.comp_homotopyPullbackCLM_comp_extDerivCLM_finZero` in degree
  zero.
* `Distribution.mass_comp_homotopyPullbackCLM_le`: `M(H_# ([[0, 1]] × T)) ≤ A L ^ k M(T)`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.9 (the homotopy formula and its mass estimate).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula).
-/

public section

noncomputable section

open Set Filter TopologicalSpace ContinuousAlternatingMap
open scoped Distributions Topology NNReal ENNReal Interval

namespace TestFunction

open TauCeti

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {H : E × ℝ → E'} {k m : ℕ}

section Construction

/-- The homotopy reparametrized in time by `Real.smoothTransition`, defined for all times. -/
private def reparam (H : E × ℝ → E') (p : E × ℝ) : E' :=
  H (p.1, Real.smoothTransition p.2)

/-- The graph map `(x, t) ↦ (H (x, σ t), t)` of the reparametrized homotopy. -/
private def graph (H : E × ℝ → E') (p : E × ℝ) : E' × ℝ :=
  (reparam H p, p.2)

/-- The open cylinder `Ω × ℝ`. -/
private def cyl (Ω : Opens E) : Opens (E × ℝ) :=
  ⟨(Ω : Set E) ×ˢ univ, Ω.isOpen.prod isOpen_univ⟩

omit [NormedSpace ℝ E] in
private theorem mem_cyl {p : E × ℝ} : p ∈ cyl Ω ↔ p.1 ∈ Ω := by
  simp [cyl, ← SetLike.mem_coe]

omit [NormedSpace ℝ E'] in
private theorem prod_top_subset_cyl : (Ω' : Set E') ×ˢ ((⊤ : Opens ℝ) : Set ℝ) ⊆ cyl Ω' :=
  fun _ hp ↦ mem_cyl.2 hp.1

/-- A test function of time equal to one near `[0, 1]`. -/
private def timeCutoff : 𝓓((⊤ : Opens ℝ), ℝ) :=
  (exists_eventually_eq_one (Ω := ⊤) (n := ⊤) isCompact_Icc
    (subset_univ (Icc (0 : ℝ) 1))).choose

private theorem timeCutoff_eventually_eq_one : ∀ᶠ t in 𝓝ˢ (Icc (0 : ℝ) 1), timeCutoff t = 1 :=
  (exists_eventually_eq_one (Ω := ⊤) (n := ⊤) isCompact_Icc
    (subset_univ (Icc (0 : ℝ) 1))).choose_spec.1

private theorem timeCutoff_eq_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : timeCutoff t = 1 :=
  timeCutoff_eventually_eq_one.self_of_nhdsSet t ht

omit [NormedSpace ℝ E] in
private theorem mem_prod_smoothTransition {x : E} (hx : x ∈ Ω) (t : ℝ) :
    (x, Real.smoothTransition t) ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1 :=
  ⟨hx, Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

variable (hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p)
  (hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
    IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K))
include hH

private theorem contDiffAt_reparam {p : E × ℝ} (hp : p.1 ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) (reparam H) p :=
  (hH _ (mem_prod_smoothTransition hp p.2)).comp p
    (contDiffAt_fst.prodMk (Real.smoothTransition.contDiffAt.comp p contDiffAt_snd))

/-- The derivative of the reparametrized homotopy: the time derivative is multiplied by `σ'`. -/
private theorem fderiv_reparam {p : E × ℝ} (hp : p.1 ∈ Ω) :
    fderiv ℝ (reparam H) p = (fderiv ℝ H (p.1, Real.smoothTransition p.2)).comp
      ((ContinuousLinearMap.fst ℝ E ℝ).prod
        (deriv Real.smoothTransition p.2 • ContinuousLinearMap.snd ℝ E ℝ)) := by
  have hσ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition p.2) p.2 :=
    (Real.smoothTransition.contDiffAt (n := 1)).differentiableAt one_ne_zero |>.hasDerivAt
  exact (((hH _ (mem_prod_smoothTransition hp p.2)).differentiableAt (by simp)).hasFDerivAt.comp p
    (hasFDerivAt_fst.prodMk (hσ.comp_hasFDerivAt p hasFDerivAt_snd))).fderiv

private theorem contDiffOn_graph : ContDiffOn ℝ (⊤ : ℕ∞) (graph H) (cyl Ω) := fun _ hp ↦
  ((contDiffAt_reparam hH (mem_cyl.1 hp)).prodMk contDiffAt_snd).contDiffWithinAt

private theorem fderiv_graph {p : E × ℝ} (hp : p.1 ∈ Ω) :
    fderiv ℝ (graph H) p = (fderiv ℝ (reparam H) p).prod (ContinuousLinearMap.snd ℝ E ℝ) :=
  ((contDiffAt_reparam hH hp).differentiableAt (by simp)).hasFDerivAt.prodMk
    hasFDerivAt_snd |>.fderiv

include hHp in
/-- The graph map is proper from `Ω × ℝ` to `Ω' × ℝ`. -/
private theorem isCompact_inter_preimage_graph (C : Set (E' × ℝ)) (hC : IsCompact C)
    (hCΩ' : C ⊆ cyl Ω') : IsCompact ((cyl Ω : Set (E × ℝ)) ∩ graph H ⁻¹' C) := by
  -- The part of the cylinder over the times in `C` that `H (·, σ ·)` maps into the projection of
  -- `C` is compact, and contains the preimage.
  set S := ((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' (Prod.fst '' C)
  have hS : IsCompact S := hHp _ (hC.image continuous_fst) fun y ⟨q, hq, hqy⟩ ↦
    hqy ▸ mem_cyl.1 (hCΩ' hq)
  set A := (fun p : E × ℝ ↦ (p.1, Real.smoothTransition p.2)) ⁻¹' S ∩ univ ×ˢ (Prod.snd '' C)
  have hA : IsCompact A :=
    ((hS.image continuous_fst).prod (hC.image continuous_snd)).of_isClosed_subset
      ((hS.isClosed.preimage (continuous_fst.prodMk
        (Real.smoothTransition.continuous.comp continuous_snd))).inter
          (isClosed_univ.prod (hC.image continuous_snd).isClosed))
      fun p hp ↦ ⟨⟨_, hp.1, rfl⟩, hp.2.2⟩
  have hAcyl : A ⊆ cyl Ω := fun p hp ↦ mem_cyl.2 hp.1.1.1
  have heq : (cyl Ω : Set (E × ℝ)) ∩ graph H ⁻¹' C = A ∩ graph H ⁻¹' C := by
    refine Subset.antisymm (fun p hp ↦ ⟨⟨?_, ?_⟩, hp.2⟩) fun p hp ↦ ⟨hAcyl hp.1, hp.2⟩
    · exact ⟨mem_prod_smoothTransition (mem_cyl.1 hp.1) p.2, _, hp.2, rfl⟩
    · exact ⟨trivial, _, hp.2, rfl⟩
  rw [heq]
  exact hA.of_isClosed_subset (((contDiffOn_graph hH).continuousOn.mono
    hAcyl).preimage_isClosed_of_isClosed hA.isClosed hC.isClosed) inter_subset_left

/-- The pullback of `ω` along the reparametrized homotopy, cut off in time by `timeCutoff`: the
pullback along the graph map of the tensor product of `ω` with the cutoff. -/
private def cutoffPullback :
    𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F) →L[ℝ] 𝓓(cyl Ω, (E × ℝ) [⋀^Fin m]→L[ℝ] F) :=
  pullbackCLM (graph H) (contDiffOn_graph hH) (isCompact_inter_preimage_graph hH hHp) ∘L
    prodSMulCLM timeCutoff prod_top_subset_cyl ∘L
    postcompCLM (compContinuousLinearMapCLM (ContinuousLinearMap.fst ℝ E' ℝ))

omit hH in
private theorem cutoffPullback_apply_of_notMem (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {p : E × ℝ}
    (hp : p.1 ∉ Ω) {hH} : cutoffPullback (H := H) hH hHp ω p = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦
    hp (mem_cyl.1 ((cutoffPullback hH hHp ω).tsupport_subset h))

include hHp in
private theorem cutoffPullback_apply (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {p : E × ℝ}
    (hp : p.1 ∈ Ω) :
    cutoffPullback hH hHp ω p =
      timeCutoff p.2 • (ω (reparam H p)).compContinuousLinearMap (fderiv ℝ (reparam H) p) := by
  rw [cutoffPullback, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    pullbackCLM_apply_of_mem _ (mem_cyl.2 hp), prodSMulCLM_apply, postcompCLM_apply,
    fderiv_graph hH hp]
  ext v
  simp [graph, Function.comp_def]

include hHp in
/-- Near `{x} × [0, 1]` with `x ∈ Ω`, the cut-off pullback is the pullback along the
reparametrized homotopy. -/
private theorem cutoffPullback_eventuallyEq (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {x : E} {t : ℝ}
    (hx : x ∈ Ω) (ht : t ∈ Icc (0 : ℝ) 1) :
    ⇑(cutoffPullback hH hHp ω) =ᶠ[𝓝 (x, t)]
      fun p ↦ (ω (reparam H p)).compContinuousLinearMap (fderiv ℝ (reparam H) p) := by
  filter_upwards [(cyl Ω).isOpen.mem_nhds (mem_cyl.2 hx),
    (continuous_snd.tendsto (x, t)).eventually
      (timeCutoff_eventually_eq_one.filter_mono (nhds_le_nhdsSet ht))] with p hp hψ
  rw [cutoffPullback_apply hH hHp ω (mem_cyl.1 hp), hψ, one_smul]

end Construction

variable [CompleteSpace F]

/-- The **homotopy operator** of a homotopy `H` that is smooth near `Ω × [0, 1]` and proper on
`Ω × [0, 1]`: the continuous linear map sending a test `(k + 1)`-form `ω` on `Ω'` to the test
`k`-form `x ↦ ∫₀¹ (H^* ω)(x, t)(∂ₜ, ·) dt` on `Ω`, see
`TestFunction.homotopyPullbackCLM_apply_of_mem`. Precomposing a `k`-current `T` on `Ω` with it
gives the pushforward `H_# ([[0, 1]] × T)`. -/
def homotopyPullbackCLM (hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p)
    (hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
      IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)) :
    𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  cylinderHomotopyCLM (fun _ hp _ ↦ mem_cyl.1 hp) ∘L cutoffPullback hH hHp

variable {hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p}
  {hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
    IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)}

/-- The homotopy operator is the cylinder homotopy operator of the cut-off pullback. -/
private theorem homotopyPullbackCLM_eq (hW : ∀ p ∈ cyl Ω, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω)
    (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) :
    homotopyPullbackCLM hH hHp ω = cylinderHomotopyCLM hW (cutoffPullback hH hHp ω) :=
  rfl

/-- On `Ω`, the homotopy operator is the cylinder homotopy operator of the pullback `H^* ω`:
`x ↦ ∫₀¹ (H^* ω)(x, t)(∂ₜ, ·) dt`. -/
@[simp]
theorem homotopyPullbackCLM_apply_of_mem (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E}
    (hx : x ∈ Ω) :
    homotopyPullbackCLM hH hHp ω x =
      cylinderHomotopy (fun p ↦ (ω (H p)).compContinuousLinearMap (fderiv ℝ H p)) x := by
  set σ := Real.smoothTransition
  -- the integrand of the cylinder homotopy operator of `H^* ω` at time `s`
  set g : ℝ → E [⋀^Fin k]→L[ℝ] F := fun s ↦
    (((ω (H (x, s))).compContinuousLinearMap (fderiv ℝ H (x, s))).curryLeft
      (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ)
  have hint : ∀ t ∈ [[(0 : ℝ), 1]],
      (((cutoffPullback hH hHp ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ)) =
        deriv σ t • g (σ t) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [(cutoffPullback_eventuallyEq hH hHp ω hx ht).eq_of_nhds, fderiv_reparam hH hx]
    ext v
    have h0 : (fderiv ℝ H (x, Real.smoothTransition t)) (0, deriv Real.smoothTransition t) =
        deriv Real.smoothTransition t • (fderiv ℝ H (x, Real.smoothTransition t)) (0, 1) := by
      rw [← map_smul, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
    simp [g, reparam, σ, ContinuousAlternatingMap.curryLeft_apply_apply, h0,
      Function.comp_def]
  have hσ : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt σ (deriv σ t) t := fun t _ ↦
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt one_ne_zero).hasDerivAt
  have hσ' : ContinuousOn (deriv σ) [[(0 : ℝ), 1]] :=
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).continuousOn
  have hg : ContinuousOn g (σ '' [[(0 : ℝ), 1]]) := by
    refine ContinuousOn.mono (s := Icc 0 1) (fun s hs ↦ ?_) ?_
    · have hHs := hH (x, s) ⟨hx, hs⟩
      have hD : ContinuousAt (fun s ↦ fderiv ℝ H (x, s)) s :=
        ((hHs.fderiv_right (m := 0) (by simp)).continuousAt).comp
          (continuous_const.prodMk continuous_id).continuousAt
      have hω : ContinuousAt (fun s ↦ ω (H (x, s))) s :=
        ω.continuous.continuousAt.comp (hHs.continuousAt.comp
          (continuous_const.prodMk continuous_id).continuousAt)
      have hP : ContinuousAt (fun s ↦ (ω (H (x, s))).compContinuousLinearMap (fderiv ℝ H (x, s)))
          s :=
        ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (𝕜 := ℝ) (E := E × ℝ)
          (F := E') (G := F) (ι := Fin (k + 1)) 0).continuous.continuousAt.comp hD).clm_apply hω
      have hc : Continuous fun α : (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F ↦
          (α.curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) :=
        (compContinuousLinearMapCLM (.inl ℝ E ℝ)).continuous.comp
          ((curryLeftLI (𝕜 := ℝ) (E := E × ℝ) (F := F) (n := k)).toContinuousLinearMap.flip
            (0, 1)).continuous
      exact (hc.continuousAt.comp hP).continuousWithinAt
    · rintro _ ⟨t, -, rfl⟩
      exact ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  rw [homotopyPullbackCLM, ContinuousLinearMap.comp_apply, coe_cylinderHomotopyCLM,
    cylinderHomotopy_apply, cylinderHomotopy_apply, intervalIntegral.integral_congr hint]
  have h := intervalIntegral.integral_deriv_smul_comp' hσ hσ' hg
  simp only [σ, Function.comp_def, Real.smoothTransition.zero, Real.smoothTransition.one] at h
  exact h

/-- Off `Ω`, the homotopy operator vanishes. -/
@[simp]
theorem homotopyPullbackCLM_apply_of_notMem (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E}
    (hx : x ∉ Ω) : homotopyPullbackCLM hH hHp ω x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx ((homotopyPullbackCLM hH hHp ω).tsupport_subset h)

/-- The homotopy operator is supported in the points `x ∈ Ω` whose track `H (x, t)`,
`t ∈ [0, 1]`, meets the support of the form. -/
theorem tsupport_homotopyPullbackCLM_subset (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (homotopyPullbackCLM hH hHp ω) ⊆
      Prod.fst '' (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' tsupport ω) := by
  refine closure_minimal (fun x hx ↦ ?_)
    ((hHp _ ω.hasCompactSupport ω.tsupport_subset).image continuous_fst).isClosed
  by_contra hxS
  have hxΩ : x ∈ Ω := by_contra fun h ↦ hx (homotopyPullbackCLM_apply_of_notMem ω h)
  refine hx ?_
  rw [homotopyPullbackCLM_apply_of_mem ω hxΩ]
  refine (cylinderHomotopy_congr fun t ht ↦ ?_).trans (congrFun cylinderHomotopy_zero x)
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hxS ⟨(x, t), ⟨⟨hxΩ, ht⟩, h⟩, rfl⟩,
    Pi.zero_apply]
  ext v
  simp

/-- **Agreement with the pushforward of the product current**: if `H` is smooth and proper on an
open `W ⊇ Ω × [0, 1]` whose part over `[0, 1]` lies over `Ω`, then the homotopy operator is the
cylinder homotopy operator on `W` composed with the pullback along `H`, so that
`H_# ([[0, 1]] × T)` is the pushforward along `H` of the product current `T ∘ h`. -/
theorem homotopyPullbackCLM_eq_cylinderHomotopyCLM_comp_pullbackCLM {W : Opens (E × ℝ)}
    (hW : ∀ p ∈ W, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) (hΩW : (Ω : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    {hHW : ContDiffOn ℝ (⊤ : ℕ∞) H W}
    {hHWp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((W : Set (E × ℝ)) ∩ H ⁻¹' K)} :
    (homotopyPullbackCLM hH hHp : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      cylinderHomotopyCLM hW ∘L pullbackCLM H hHW hHWp := by
  ext ω x : 2
  rw [ContinuousLinearMap.comp_apply, coe_cylinderHomotopyCLM]
  by_cases hx : x ∈ Ω
  · rw [homotopyPullbackCLM_apply_of_mem ω hx]
    exact cylinderHomotopy_congr fun t ht ↦ (pullbackCLM_apply_of_mem ω (hΩW ⟨hx, ht⟩)).symm
  · rw [homotopyPullbackCLM_apply_of_notMem ω hx, ← coe_cylinderHomotopyCLM (hW := hW),
      image_eq_zero_of_notMem_tsupport fun h ↦ hx ((cylinderHomotopyCLM hW _).tsupport_subset h)]

omit [CompleteSpace F] in
/-- At the end times, the slices of the cut-off pullback are the pullbacks along the slices of
`H`. -/
private theorem pullbackCLM_prodMk_left_cutoffPullback {t : ℝ} (ht : t = 0 ∨ t = 1)
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ cyl Ω →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, t)) ⁻¹' K)}
    {ht' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, t)) Ω}
    {htp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ (fun x ↦ H (x, t)) ⁻¹' K)}
    (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
    pullbackCLM (fun x ↦ (x, t)) (contDiffOn_id.prodMk contDiffOn_const) hp
        (cutoffPullback hH hHp ω) =
      pullbackCLM (fun x ↦ H (x, t)) ht' htp ω := by
  have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hσ : Real.smoothTransition t = t := by
    rcases ht with rfl | rfl
    exacts [Real.smoothTransition.zero, Real.smoothTransition.one]
  ext x : 1
  rw [pullbackCLM_prodMk_left_apply (fun _ hp _ ↦ mem_cyl.1 hp) htI]
  by_cases hx : x ∈ Ω
  · have hxt : ((x, t) : E × ℝ).1 ∈ Ω := hx
    have hD : fderiv ℝ (fun y ↦ H (y, t)) x = (fderiv ℝ H (x, t)).comp (.inl ℝ E ℝ) :=
      (((hH _ ⟨hx, htI⟩).differentiableAt (by simp)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x t)).fderiv
    rw [pullbackCLM_apply_of_mem _ hx, cutoffPullback_apply hH hHp ω hxt, timeCutoff_eq_one htI,
      one_smul, fderiv_reparam hH hxt, hD]
    ext v
    simp [reparam, hσ, Function.comp_def]
  · rw [pullbackCLM_apply_of_notMem _ hx, cutoffPullback_apply_of_notMem hHp ω hx]
    ext v
    simp

/-- Along `Ω × [0, 1]`, where the cutoff is one, the cut-off pullback commutes with `d`; so the
cylinder homotopy operator does not see the difference. -/
private theorem cylinderHomotopyCLM_cutoffPullback_extDerivCLM
    (hW : ∀ p ∈ cyl Ω, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
    cylinderHomotopyCLM hW (cutoffPullback hH hHp (extDerivCLM ω)) =
      cylinderHomotopyCLM hW (extDerivCLM (cutoffPullback hH hHp ω)) := by
  ext x : 1
  rw [coe_cylinderHomotopyCLM, coe_cylinderHomotopyCLM]
  refine cylinderHomotopy_congr fun t ht ↦ ?_
  by_cases hx : x ∈ Ω
  · have hxt : ((x, t) : E × ℝ).1 ∈ Ω := hx
    rw [(cutoffPullback_eventuallyEq hH hHp _ hx ht).eq_of_nhds,
      extDerivCLM_apply (cutoffPullback hH hHp ω),
      (cutoffPullback_eventuallyEq hH hHp ω hx ht).extDeriv_eq, coe_extDerivCLM]
    exact (extDeriv_pullback (ω.contDiff.differentiable (by simp) _)
      (contDiffAt_reparam hH hxt) (by simp)).symm
  · rw [cutoffPullback_apply_of_notMem hHp _ hx, image_eq_zero_of_notMem_tsupport fun h ↦
      hx (mem_cyl.1 ((extDerivCLM (cutoffPullback hH hHp ω)).tsupport_subset h))]

/-- **The homotopy formula on test forms**: `K ∘ d = H₁^* - H₀^* - d ∘ K` on test `(k + 1)`-forms,
where `K` is the homotopy operator and `Hₜ^*` is the pullback along the slice `Hₜ = H (·, t)`. -/
theorem homotopyPullbackCLM_comp_extDerivCLM :
    (homotopyPullbackCLM hH hHp ∘L extDerivCLM :
        𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ H (x, 1)) (contDiffOn_comp_prodMk_left hH ⟨zero_le_one, le_rfl⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨zero_le_one, le_rfl⟩) -
        pullbackCLM (fun x ↦ H (x, 0)) (contDiffOn_comp_prodMk_left hH ⟨le_rfl, zero_le_one⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨le_rfl, zero_le_one⟩) -
        extDerivCLM ∘L homotopyPullbackCLM hH hHp := by
  ext ω : 1
  have hW : ∀ p ∈ cyl Ω, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun _ hp _ ↦ mem_cyl.1 hp
  have hd := cylinderHomotopyCLM_cutoffPullback_extDerivCLM (hH := hH) (hHp := hHp) hW ω
  have h := congr($(cylinderHomotopyCLM_comp_extDerivCLM (hW := hW) (k := k))
    (cutoffPullback hH hHp ω))
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, homotopyPullbackCLM_eq hW] at h ⊢
  rw [hd, h, pullbackCLM_prodMk_left_cutoffPullback (Or.inr rfl),
    pullbackCLM_prodMk_left_cutoffPullback (Or.inl rfl)]

/-- **The homotopy formula on test `0`-forms**: `K ∘ d = H₁^* - H₀^*`, where `K` is the homotopy
operator and `Hₜ^*` is the pullback along the slice `Hₜ = H (·, t)`. -/
theorem homotopyPullbackCLM_comp_extDerivCLM_finZero :
    (homotopyPullbackCLM hH hHp ∘L extDerivCLM : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) =
      pullbackCLM (fun x ↦ H (x, 1)) (contDiffOn_comp_prodMk_left hH ⟨zero_le_one, le_rfl⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨zero_le_one, le_rfl⟩) -
        pullbackCLM (fun x ↦ H (x, 0)) (contDiffOn_comp_prodMk_left hH ⟨le_rfl, zero_le_one⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨le_rfl, zero_le_one⟩) := by
  ext ω : 1
  have hW : ∀ p ∈ cyl Ω, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun _ hp _ ↦ mem_cyl.1 hp
  have hd := cylinderHomotopyCLM_cutoffPullback_extDerivCLM (hH := hH) (hHp := hHp) hW ω
  have h := congr($(cylinderHomotopyCLM_comp_extDerivCLM_finZero (hW := hW))
    (cutoffPullback hH hHp ω))
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, homotopyPullbackCLM_eq hW] at h ⊢
  rw [hd, h, pullbackCLM_prodMk_left_cutoffPullback (Or.inr rfl),
    pullbackCLM_prodMk_left_cutoffPullback (Or.inl rfl)]

end TestFunction

namespace ContinuousLinearMap

open TestFunction TauCeti

variable {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  {Ω : Opens E} {Ω' : Opens E'} {H : E × ℝ → E'} {k : ℕ}
  {hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p}
  {hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
    IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)}

/-- **The homotopy formula**: for a `(k + 1)`-current `T` on `Ω`,
`∂ H_# ([[0, 1]] × T) = H₁# T - H₀# T - H_# ([[0, 1]] × ∂ T)`, where
`H_# ([[0, 1]] × T) = T ∘ K` for the homotopy operator `K`, `Hₜ# T = T ∘ Hₜ^*` and `∂ T = T ∘ d`. -/
theorem comp_homotopyPullbackCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L homotopyPullbackCLM hH hHp) ∘L extDerivCLM =
      T ∘L pullbackCLM (fun x ↦ H (x, 1)) (contDiffOn_comp_prodMk_left hH ⟨zero_le_one, le_rfl⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨zero_le_one, le_rfl⟩) -
        T ∘L pullbackCLM (fun x ↦ H (x, 0)) (contDiffOn_comp_prodMk_left hH ⟨le_rfl, zero_le_one⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨le_rfl, zero_le_one⟩) -
        (T ∘L extDerivCLM) ∘L homotopyPullbackCLM hH hHp := by
  rw [comp_assoc, homotopyPullbackCLM_comp_extDerivCLM, comp_sub, comp_sub, comp_assoc]

/-- **The homotopy formula in degree zero**: for a `0`-current `T` on `Ω`,
`∂ H_# ([[0, 1]] × T) = H₁# T - H₀# T`, where `H_# ([[0, 1]] × T) = T ∘ K` for the homotopy operator
`K` and `Hₜ# T = T ∘ Hₜ^*`. -/
theorem comp_homotopyPullbackCLM_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G) :
    (T ∘L homotopyPullbackCLM hH hHp) ∘L extDerivCLM =
      T ∘L pullbackCLM (fun x ↦ H (x, 1)) (contDiffOn_comp_prodMk_left hH ⟨zero_le_one, le_rfl⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨zero_le_one, le_rfl⟩) -
        T ∘L pullbackCLM (fun x ↦ H (x, 0)) (contDiffOn_comp_prodMk_left hH ⟨le_rfl, zero_le_one⟩)
          (isCompact_inter_preimage_comp_prodMk_left hHp ⟨le_rfl, zero_le_one⟩) := by
  rw [comp_assoc, homotopyPullbackCLM_comp_extDerivCLM_finZero, comp_sub]

end ContinuousLinearMap

namespace Distribution

open TestFunction TauCeti
open scoped BoundedContinuousFunction

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {Ω' : Opens E'} {H : E × ℝ → E'} {k : ℕ}
  {hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p}
  {hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
    IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)}

/-- **The mass of a homotopy current**: if `‖∂ₜ H‖ ≤ A` and the spatial derivative of `H` has
operator norm at most `L` on `Ω × [0, 1]`, then `M(H_# ([[0, 1]] × T)) ≤ A L ^ k M(T)` for a
`k`-current `T` on `Ω`, where `H_# ([[0, 1]] × T) = T ∘ K` for the homotopy operator `K`. -/
theorem mass_comp_homotopyPullbackCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] (T : 𝓕) {A L : ℝ≥0}
    (hA : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ H p (0, 1)‖ ≤ A)
    (hL : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ‖(fderiv ℝ H p).comp (.inl ℝ E ℝ)‖ ≤ L) :
    mass (T ∘ homotopyPullbackCLM hH hHp) ≤ A * L ^ k * mass T := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  have hpt (x : E) : ‖homotopyPullbackCLM hH hHp ω x‖ ≤ A * L ^ k := by
    by_cases hx : x ∈ Ω
    · rw [homotopyPullbackCLM_apply_of_mem ω hx, cylinderHomotopy_apply]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := A * L ^ k)
        fun t ht ↦ ?_).trans_eq
        (by simp)
      rw [uIoc_of_le zero_le_one] at ht
      have hp : (x, t) ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1 := ⟨hx, Ioc_subset_Icc_self ht⟩
      rw [curryLeft_compContinuousLinearMap]
      calc _ ≤ ‖(ω (H (x, t))).curryLeft (fderiv ℝ H (x, t) (0, 1))‖ *
            ‖(fderiv ℝ H (x, t)).comp (.inl ℝ E ℝ)‖ ^ k := by
            have hcomp : (((ω (H (x, t))).curryLeft
                (fderiv ℝ H (x, t) (0, 1))).compContinuousLinearMap
                  (fderiv ℝ H (x, t))).compContinuousLinearMap (.inl ℝ E ℝ) =
                ((ω (H (x, t))).curryLeft (fderiv ℝ H (x, t) (0, 1))).compContinuousLinearMap
                  ((fderiv ℝ H (x, t)).comp (.inl ℝ E ℝ)) := by
              ext v
              rfl
            rw [hcomp]
            exact (norm_compContinuousLinearMap_le
              ((ω (H (x, t))).curryLeft (fderiv ℝ H (x, t) (0, 1)))
              ((fderiv ℝ H (x, t)).comp (.inl ℝ E ℝ))).trans_eq (by simp)
        _ ≤ (‖ω (H (x, t))‖ * ‖fderiv ℝ H (x, t) (0, 1)‖) * L ^ k := by
            gcongr
            · exact ((ω (H (x, t))).curryLeft.le_opNorm _).trans_eq (by rw [norm_curryLeft])
            · exact hL _ hp
        _ ≤ (1 * A) * L ^ k := by
            gcongr
            exacts [hω _, hA _ hp]
        _ = A * L ^ k := by ring
    · rw [homotopyPullbackCLM_apply_of_notMem ω hx, norm_zero]
      positivity
  have hb : ‖(homotopyPullbackCLM hH hHp ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ ≤ A * L ^ k :=
    (BoundedContinuousFunction.norm_le (by positivity)).2 hpt
  calc ‖T (homotopyPullbackCLM hH hHp ω)‖ₑ
      ≤ mass T * ‖(homotopyPullbackCLM hH hHp ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ :=
        enorm_apply_le_mass_mul T _
    _ ≤ mass T * (A * L ^ k : ℝ≥0) := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (by simpa using hb)
    _ = A * L ^ k * mass T := by
        rw [mul_comm]
        push_cast
        ring

end Distribution
