/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Prod
public import TauCeti.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.CylinderHomotopy
public import TauCeti.Analysis.Distribution.TestFunction.Prod
public import TauCeti.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Alternating.Curry

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

For a current `T` whose support is a compact subset of `Ω` no properness of `H` is needed, as for
the pushforward with a cutoff (`TestFunction.cutoffPullbackCLM`). For `H` smooth on `Ω × ℝ` and a
test function `χ` on `Ω`, the **homotopy operator with a cutoff**
`TestFunction.cutoffHomotopyPullbackCLM` sends `ω` to `x ↦ χ x • ∫₀¹ (H^* ω)(x, t)(∂ₜ, ·) dt`; it
pulls `ω` back to the cylinder with the cutoff `(x, t) ↦ τ t • χ x`
(`TestFunction.cylinderCutoff`). When `χ` is equal to one near the support of `T`, the same
homotopy formula holds with `Hₜ# T = T ∘ (χ Hₜ^*)`, the current `T ∘ K` is supported in the union
of the tracks `H ({x} × [0, 1])` of the points `x` of the support of `T`, and its mass is at most
`A L ^ k M(T)` when `|χ| ≤ 1` and the bounds on `H` hold over the support of `χ`.

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
* `Distribution.mass_comp_homotopyPullbackCLM_le`: `M(H_# ([[0, 1]] × T)) ≤ A L ^ k M(T)`, from
  the pointwise bound `TauCeti.norm_cylinderHomotopy_pullback_le`.
* `TestFunction.cutoffHomotopyPullbackCLM`: the homotopy operator with a cutoff, with its values
  `TestFunction.cutoffHomotopyPullbackCLM_apply`, its support
  `TestFunction.tsupport_cutoffHomotopyPullbackCLM_subset` and the homotopy identities
  `TestFunction.cutoffHomotopyPullbackCLM_extDerivCLM_apply` and
  `TestFunction.cutoffHomotopyPullbackCLM_extDerivCLM_apply_finZero` where `χ` is one.
* `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_congr` and
  `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_eq_comp_homotopyPullbackCLM`: the homotopy
  current does not depend on the cutoff, and agrees with that of a proper homotopy.
* `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM` and
  `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero`: the homotopy
  formula for a current with compact support.
* `Distribution.dsupport_comp_cutoffHomotopyPullbackCLM_subset`,
  `Distribution.mass_comp_cutoffHomotopyPullbackCLM_le`: the support and mass of the homotopy
  current.

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

private theorem contDiffOn_graph : ContDiffOn ℝ (⊤ : ℕ∞) (graph H) Ω.cylinder := fun _ hp ↦
  ((contDiffAt_reparam hH (Opens.mem_cylinder.1 hp)).prodMk contDiffAt_snd).contDiffWithinAt

private theorem fderiv_graph {p : E × ℝ} (hp : p.1 ∈ Ω) :
    fderiv ℝ (graph H) p = (fderiv ℝ (reparam H) p).prod (ContinuousLinearMap.snd ℝ E ℝ) :=
  ((contDiffAt_reparam hH hp).differentiableAt (by simp)).hasFDerivAt.prodMk
    hasFDerivAt_snd |>.fderiv

include hHp in
/-- The graph map is proper from `Ω × ℝ` to `Ω' × ℝ`. -/
private theorem isCompact_inter_preimage_graph (C : Set (E' × ℝ)) (hC : IsCompact C)
    (hCΩ' : C ⊆ Ω'.cylinder) : IsCompact ((Ω.cylinder : Set (E × ℝ)) ∩ graph H ⁻¹' C) := by
  -- The part of the cylinder over the times in `C` that `H (·, σ ·)` maps into the projection of
  -- `C` is compact, and contains the preimage.
  set S := ((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' (Prod.fst '' C)
  have hS : IsCompact S := hHp _ (hC.image continuous_fst) fun y ⟨q, hq, hqy⟩ ↦
    hqy ▸ Opens.mem_cylinder.1 (hCΩ' hq)
  set A := (fun p : E × ℝ ↦ (p.1, Real.smoothTransition p.2)) ⁻¹' S ∩ univ ×ˢ (Prod.snd '' C)
  have hA : IsCompact A :=
    ((hS.image continuous_fst).prod (hC.image continuous_snd)).of_isClosed_subset
      ((hS.isClosed.preimage (continuous_fst.prodMk
        (Real.smoothTransition.continuous.comp continuous_snd))).inter
          (isClosed_univ.prod (hC.image continuous_snd).isClosed))
      fun p hp ↦ ⟨⟨_, hp.1, rfl⟩, hp.2.2⟩
  have hAcyl : A ⊆ Ω.cylinder := fun p hp ↦ Opens.mem_cylinder.2 hp.1.1.1
  have heq : (Ω.cylinder : Set (E × ℝ)) ∩ graph H ⁻¹' C = A ∩ graph H ⁻¹' C := by
    refine Subset.antisymm (fun p hp ↦ ⟨⟨?_, ?_⟩, hp.2⟩) fun p hp ↦ ⟨hAcyl hp.1, hp.2⟩
    · exact ⟨mem_prod_smoothTransition (Opens.mem_cylinder.1 hp.1) p.2, _, hp.2, rfl⟩
    · exact ⟨trivial, _, hp.2, rfl⟩
  rw [heq]
  exact hA.of_isClosed_subset (((contDiffOn_graph hH).continuousOn.mono
    hAcyl).preimage_isClosed_of_isClosed hA.isClosed hC.isClosed) inter_subset_left

/-- The pullback of `ω` along the reparametrized homotopy, cut off in time by `timeCutoff`: the
pullback along the graph map of the tensor product of `ω` with the cutoff. -/
private def cutoffPullback :
    𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F) →L[ℝ] 𝓓(Ω.cylinder, (E × ℝ) [⋀^Fin m]→L[ℝ] F) :=
  pullbackCLM (graph H) (contDiffOn_graph hH) (isCompact_inter_preimage_graph hH hHp) ∘L
    prodSMulCLM timeCutoff Opens.prod_top_subset_cylinder ∘L
    postcompCLM (compContinuousLinearMapCLM (ContinuousLinearMap.fst ℝ E' ℝ))

omit hH in
private theorem cutoffPullback_apply_of_notMem (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {p : E × ℝ}
    (hp : p.1 ∉ Ω) {hH} : cutoffPullback (H := H) hH hHp ω p = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦
    hp (Opens.mem_cylinder.1 ((cutoffPullback hH hHp ω).tsupport_subset h))

include hHp in
private theorem cutoffPullback_apply (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {p : E × ℝ}
    (hp : p.1 ∈ Ω) :
    cutoffPullback hH hHp ω p =
      timeCutoff p.2 • (ω (reparam H p)).compContinuousLinearMap (fderiv ℝ (reparam H) p) := by
  rw [cutoffPullback, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    pullbackCLM_apply_of_mem _ (Opens.mem_cylinder.2 hp), prodSMulCLM_apply, postcompCLM_apply,
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
  filter_upwards [Ω.cylinder.isOpen.mem_nhds (Opens.mem_cylinder.2 hx),
    (continuous_snd.tendsto (x, t)).eventually
      (timeCutoff_eventually_eq_one.filter_mono (nhds_le_nhdsSet ht))] with p hp hψ
  rw [cutoffPullback_apply hH hHp ω (Opens.mem_cylinder.1 hp), hψ, one_smul]

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
  cylinderHomotopyCLM (fun _ hp _ ↦ Opens.mem_cylinder.1 hp) ∘L cutoffPullback hH hHp

variable {hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p}
  {hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
    IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)}

/-- The homotopy operator is the cylinder homotopy operator of the cut-off pullback. -/
private theorem homotopyPullbackCLM_eq (hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω)
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
        ((compContinuousLinearMapCLM (.inl ℝ E ℝ)).continuous.comp
          (curryLeftFlipL (𝕜 := ℝ) (F := F) (n := k) ((0, 1) : E × ℝ)).continuous).congr
            fun α ↦ by simp
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
  ext _
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
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ Ω.cylinder →
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
  rw [pullbackCLM_prodMk_left_apply (fun _ hp _ ↦ Opens.mem_cylinder.1 hp) htI]
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
    ext _
    simp

/-- Along `Ω × [0, 1]`, where the cutoff is one, the cut-off pullback commutes with `d`; so the
cylinder homotopy operator does not see the difference. -/
private theorem cylinderHomotopyCLM_cutoffPullback_extDerivCLM
    (hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω) (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
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
      hx (Opens.mem_cylinder.1 ((extDerivCLM (cutoffPullback hH hHp ω)).tsupport_subset h))]

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
  have hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun _ hp _ ↦ Opens.mem_cylinder.1 hp
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
  have hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun _ hp _ ↦ Opens.mem_cylinder.1 hp
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
    · rw [homotopyPullbackCLM_apply_of_mem ω hx]
      exact (norm_cylinderHomotopy_pullback_le ω H x (fun t ht ↦ hA _ ⟨hx, ht⟩)
        (fun t ht ↦ hL _ ⟨hx, ht⟩) fun t _ ↦ hω _).trans_eq (by ring)
    · rw [homotopyPullbackCLM_apply_of_notMem ω hx, norm_zero]
      positivity
  simpa using enorm_apply_le_mul_mass_of_forall_norm_le T (b := A * L ^ k) (by simpa using hpt)

end Distribution

/-! ### The homotopy operator with a cutoff

For a current whose support is a compact subset of `Ω`, no properness of the homotopy is needed:
the pulled-back form is multiplied by the cylinder cutoff `TestFunction.cylinderCutoff` of a test
function `χ` equal to one near the support of the current, as for the pushforward with a cutoff
`TestFunction.cutoffPullbackCLM`. -/

namespace TestFunction

open TauCeti

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {Ω' : Opens E'} {H : E × ℝ → E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)}

/-- The **homotopy operator with a cutoff** `χ` of a homotopy `H` smooth on `Ω × ℝ`: the continuous
linear map sending a test `(k + 1)`-form `ω` on `Ω'` to the test `k`-form
`x ↦ χ x • ∫₀¹ (H^* ω)(x, t)(∂ₜ, ·) dt` on `Ω`, see `TestFunction.cutoffHomotopyPullbackCLM_apply`.
No properness of `H` is needed. Precomposing a `k`-current `T` on `Ω` with it gives the pushforward
`H_# ([[0, 1]] × T)` when `χ` is equal to one near the support of `T`. -/
def cutoffHomotopyPullbackCLM (χ : 𝓓(Ω, ℝ)) (H : E × ℝ → E')
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω.cylinder) :
    𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  cylinderHomotopyCLM (fun _ hp _ ↦ Opens.mem_cylinder.1 hp) ∘L
    cutoffPullbackCLM (cylinderCutoff χ) H hH

variable {hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω.cylinder}

/-- The homotopy operator with a cutoff is the cylinder homotopy operator of the pullback with the
cylinder cutoff. -/
private theorem cutoffHomotopyPullbackCLM_eq
    (hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω)
    (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) :
    cutoffHomotopyPullbackCLM χ H hH ω =
      cylinderHomotopyCLM hW (cutoffPullbackCLM (cylinderCutoff χ) H hH ω) :=
  rfl

/-- The homotopy operator with a cutoff is `χ` times the cylinder homotopy operator of the pullback
`H^* ω`: `x ↦ χ x • ∫₀¹ (H^* ω)(x, t)(∂ₜ, ·) dt`. -/
@[simp]
theorem cutoffHomotopyPullbackCLM_apply (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    cutoffHomotopyPullbackCLM χ H hH ω x =
      χ x • cylinderHomotopy (fun p ↦ (ω (H p)).compContinuousLinearMap (fderiv ℝ H p)) x := by
  rw [cutoffHomotopyPullbackCLM, ContinuousLinearMap.comp_apply, cylinderHomotopyCLM_apply,
    cylinderHomotopy_apply, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  ext v
  simp [cutoffPullbackCLM_apply, cylinderCutoff_apply_of_mem_Icc ht, Function.comp_def]

/-- The homotopy operator with a cutoff is supported in the points `x` of the support of `χ` whose
track `H (x, t)`, `t ∈ [0, 1]`, meets the support of the form. -/
theorem tsupport_cutoffHomotopyPullbackCLM_subset (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (cutoffHomotopyPullbackCLM χ H hH ω) ⊆
      Prod.fst '' ((tsupport χ ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' tsupport ω) := by
  have hc : IsCompact ((tsupport χ ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' tsupport ω) :=
    (χ.hasCompactSupport.prod isCompact_Icc).of_isClosed_subset
      ((hH.continuousOn.mono fun p (hp : p ∈ tsupport χ ×ˢ Icc (0 : ℝ) 1) ↦
        Opens.mem_cylinder.2 (χ.tsupport_subset hp.1)).preimage_isClosed_of_isClosed
          ((isClosed_tsupport χ).prod isClosed_Icc) (isClosed_tsupport ω)) inter_subset_left
  refine closure_minimal (fun x hx ↦ ?_) (hc.image continuous_fst).isClosed
  by_contra hxS
  refine hx ?_
  rw [cutoffHomotopyPullbackCLM_apply]
  by_cases hχx : χ x = 0
  · rw [hχx, zero_smul]
  have hxχ : x ∈ tsupport χ := subset_tsupport _ hχx
  refine (congrArg (χ x • ·) ((cylinderHomotopy_congr fun t ht ↦ ?_).trans
    (congrFun cylinderHomotopy_zero x))).trans (smul_zero _)
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hxS ⟨(x, t), ⟨⟨hxχ, ht⟩, h⟩, rfl⟩, Pi.zero_apply]
  ext _
  simp

omit [CompleteSpace F] in
/-- At the times `t ∈ [0, 1]`, the slice of the pullback with the cylinder cutoff is the pullback
with the cutoff `χ` along the slice `H (·, t)`. -/
private theorem pullbackCLM_prodMk_left_cutoffPullbackCLM_cylinderCutoff {m : ℕ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ Ω.cylinder →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, t)) ⁻¹' K)}
    {hHt : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, t)) Ω} (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) :
    pullbackCLM (fun x ↦ (x, t)) (contDiffOn_id.prodMk contDiffOn_const) hp
        (cutoffPullbackCLM (cylinderCutoff χ) H hH ω) =
      cutoffPullbackCLM χ (fun x ↦ H (x, t)) hHt ω := by
  ext x : 1
  rw [pullbackCLM_prodMk_left_apply (fun _ hp _ ↦ Opens.mem_cylinder.1 hp) ht,
    cutoffPullbackCLM_apply, cutoffPullbackCLM_apply, cylinderCutoff_apply_of_mem_Icc ht]
  by_cases hx : x ∈ Ω
  · have hD : fderiv ℝ (fun y ↦ H (y, t)) x = (fderiv ℝ H (x, t)).comp (.inl ℝ E ℝ) :=
      (((hH.contDiffAt (Ω.cylinder.isOpen.mem_nhds (Opens.mem_cylinder.2 hx))).differentiableAt
        (by simp)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)).fderiv
    ext v
    simp [hD, Function.comp_def]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (χ.tsupport_subset h)]
    ext v
    simp

/-- Where `χ` is one, the homotopy operator with a cutoff of `d ω` is the cylinder homotopy operator
of the exterior derivative of the pullback with the cylinder cutoff. -/
private theorem cutoffHomotopyPullbackCLM_extDerivCLM_apply_eq {m : ℕ}
    (hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω)
    (ω : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F)) {x : E} (hx : ∀ᶠ y in 𝓝 x, χ y = 1) :
    cutoffHomotopyPullbackCLM χ H hH (extDerivCLM ω) x =
      cylinderHomotopyCLM hW (extDerivCLM (cutoffPullbackCLM (cylinderCutoff χ) H hH ω)) x := by
  rw [cutoffHomotopyPullbackCLM_eq hW, coe_cylinderHomotopyCLM, coe_cylinderHomotopyCLM]
  exact cylinderHomotopy_congr fun t ht ↦
    (extDerivCLM_cutoffPullbackCLM_apply ω (cylinderCutoff_eventually_eq_one hx ht)).symm

/-- **The homotopy formula with a cutoff on test forms**: at every point near which `χ` is one,
`K d ω = χ H₁^* ω - χ H₀^* ω - d K ω` for a test `(k + 1)`-form `ω`, where `K` is the homotopy
operator with cutoff `χ` and `χ Hₜ^*` is the pullback with cutoff `χ` along `Hₜ = H (·, t)`. -/
theorem cutoffHomotopyPullbackCLM_extDerivCLM_apply
    {hH₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, 0)) Ω}
    {hH₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, 1)) Ω}
    (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E} (hx : ∀ᶠ y in 𝓝 x, χ y = 1) :
    cutoffHomotopyPullbackCLM χ H hH (extDerivCLM ω) x =
      cutoffPullbackCLM χ (fun y ↦ H (y, 1)) hH₁ ω x -
        cutoffPullbackCLM χ (fun y ↦ H (y, 0)) hH₀ ω x -
        extDerivCLM (cutoffHomotopyPullbackCLM χ H hH ω) x := by
  have hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun _ hp _ ↦ Opens.mem_cylinder.1 hp
  have h := congr($(cylinderHomotopyCLM_comp_extDerivCLM (hW := hW) (k := k) (F := F))
    (cutoffPullbackCLM (cylinderCutoff χ) H hH ω) x)
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply] at h
  rw [cutoffHomotopyPullbackCLM_extDerivCLM_apply_eq hW ω hx, h,
    pullbackCLM_prodMk_left_cutoffPullbackCLM_cylinderCutoff ⟨zero_le_one, le_rfl⟩,
    pullbackCLM_prodMk_left_cutoffPullbackCLM_cylinderCutoff ⟨le_rfl, zero_le_one⟩,
    cutoffHomotopyPullbackCLM_eq hW]

/-- **The homotopy formula with a cutoff on test `0`-forms**: at every point near which `χ` is one,
`K d ω = χ H₁^* ω - χ H₀^* ω`, where `K` is the homotopy operator with cutoff `χ` and `χ Hₜ^*` is
the pullback with cutoff `χ` along `Hₜ = H (·, t)`. -/
theorem cutoffHomotopyPullbackCLM_extDerivCLM_apply_finZero
    {hH₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, 0)) Ω}
    {hH₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, 1)) Ω}
    (ω : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F)) {x : E} (hx : ∀ᶠ y in 𝓝 x, χ y = 1) :
    cutoffHomotopyPullbackCLM χ H hH (extDerivCLM ω) x =
      cutoffPullbackCLM χ (fun y ↦ H (y, 1)) hH₁ ω x -
        cutoffPullbackCLM χ (fun y ↦ H (y, 0)) hH₀ ω x := by
  have hW : ∀ p ∈ Ω.cylinder, p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ Ω := fun _ hp _ ↦ Opens.mem_cylinder.1 hp
  have h := congr($(cylinderHomotopyCLM_comp_extDerivCLM_finZero (hW := hW) (F := F))
    (cutoffPullbackCLM (cylinderCutoff χ) H hH ω) x)
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply] at h
  rw [cutoffHomotopyPullbackCLM_extDerivCLM_apply_eq hW ω hx, h,
    pullbackCLM_prodMk_left_cutoffPullbackCLM_cylinderCutoff ⟨zero_le_one, le_rfl⟩,
    pullbackCLM_prodMk_left_cutoffPullbackCLM_cylinderCutoff ⟨le_rfl, zero_le_one⟩]

end TestFunction

namespace ContinuousLinearMap

open TestFunction TauCeti Distribution

variable {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  {Ω : Opens E} {Ω' : Opens E'} {H : E × ℝ → E'} {k : ℕ} {χ χ₁ χ₂ : 𝓓(Ω, ℝ)}
  {hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω.cylinder} {hH₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, 0)) Ω}
  {hH₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, 1)) Ω}

omit [IsTopologicalAddGroup G] in
/-- **Independence of the cutoff**: the homotopy current `T ∘ K` with cutoff `χ` depends only on
the germ of `χ` along the support of `T`. -/
theorem comp_cutoffHomotopyPullbackCLM_congr (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    (h : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₂) :
    (T ∘L cutoffHomotopyPullbackCLM χ₁ H hH : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) =
      T ∘L cutoffHomotopyPullbackCLM χ₂ H hH := by
  ext ω
  exact map_eq_map_of_eventuallyEq T (h.mono fun x hx ↦ by simp [hx])

omit [IsTopologicalAddGroup G] in
/-- **Agreement with the proper homotopy operator**: if `H` is moreover proper on `Ω × [0, 1]` and
`χ` is equal to one near the support of `T`, then `T ∘ K_χ = T ∘ K` for the homotopy operators
`K_χ` with cutoff `χ` and `K` of `TestFunction.homotopyPullbackCLM`, so `T ∘ K_χ` is
`H_# ([[0, 1]] × T)`. -/
theorem comp_cutoffHomotopyPullbackCLM_eq_comp_homotopyPullbackCLM
    (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
      IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)) :
    (T ∘L cutoffHomotopyPullbackCLM χ H hH : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) =
      T ∘L homotopyPullbackCLM (fun _ hp ↦
        hH.contDiffAt (Ω.cylinder.isOpen.mem_nhds (Opens.mem_cylinder.2 hp.1))) hHp := by
  ext ω
  refine map_eq_map_of_eventuallyEq T (hχ.mono fun x hx ↦ ?_)
  have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ (by simp [hx]))
  simp [hx, hxΩ]

/-- **The homotopy formula with a cutoff**: if `χ` is equal to one near the support of a
`(k + 1)`-current `T` on `Ω`, then `∂ H_# ([[0, 1]] × T) = H₁# T - H₀# T - H_# ([[0, 1]] × ∂ T)`,
where `H_# ([[0, 1]] × T) = T ∘ K` for the homotopy operator `K` with cutoff `χ`,
`Hₜ# T = T ∘ (χ Hₜ^*)` and `∂ T = T ∘ d`. -/
theorem comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (T ∘L cutoffHomotopyPullbackCLM χ H hH) ∘L
        (extDerivCLM : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 1)) hH₁ -
        T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 0)) hH₀ -
        (T ∘L extDerivCLM) ∘L cutoffHomotopyPullbackCLM χ H hH := by
  ext ω
  simp only [comp_apply, _root_.sub_apply, ← map_sub]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  simp [cutoffHomotopyPullbackCLM_extDerivCLM_apply (hH₀ := hH₀) (hH₁ := hH₁) ω hx]

/-- **The homotopy formula with a cutoff in degree zero**: if `χ` is equal to one near the support
of a `0`-current `T` on `Ω`, then `∂ H_# ([[0, 1]] × T) = H₁# T - H₀# T`, where
`H_# ([[0, 1]] × T) = T ∘ K` for the homotopy operator `K` with cutoff `χ` and
`Hₜ# T = T ∘ (χ Hₜ^*)`. -/
theorem comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (T ∘L cutoffHomotopyPullbackCLM χ H hH) ∘L
        (extDerivCLM : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) =
      T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 1)) hH₁ -
        T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 0)) hH₀ := by
  ext ω
  simp only [comp_apply, _root_.sub_apply, ← map_sub]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  simp [cutoffHomotopyPullbackCLM_extDerivCLM_apply_finZero (hH₀ := hH₀) (hH₁ := hH₁) ω hx]

end ContinuousLinearMap

namespace Distribution

open TestFunction TauCeti
open scoped BoundedContinuousFunction

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {Ω' : Opens E'} {H : E × ℝ → E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)}
  {hH : ContDiffOn ℝ (⊤ : ℕ∞) H Ω.cylinder} {𝓕 : Type*}

/-- **The support of a homotopy current with a cutoff**: the support of `T ∘ K`, for the homotopy
operator `K` with cutoff `χ`, lies in the image under `H` of the part of `(spt T ∩ tsupport χ)
× [0, 1]`, the union of the tracks of the points of the support of `T` in the support of `χ`. -/
theorem dsupport_comp_cutoffHomotopyPullbackCLM_subset [AddCommMonoid V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) :
    dsupport (T ∘ (cutoffHomotopyPullbackCLM χ H hH :
        𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) ⊆
      H '' ((tsupport χ ∩ dsupport T) ×ˢ Icc (0 : ℝ) 1) :=
  dsupport_comp_subset_of_disjoint T (((IsCompact.inter_right χ.hasCompactSupport
    isClosed_dsupport).prod isCompact_Icc).image_of_continuousOn (hH.continuousOn.mono
      fun p hp ↦ Opens.mem_cylinder.2 (χ.tsupport_subset hp.1.1))).isClosed
    fun ω hω ↦ disjoint_left.2 fun x hx hxT ↦ by
      obtain ⟨p, ⟨⟨hpχ, hpt⟩, hpω⟩, rfl⟩ := tsupport_cutoffHomotopyPullbackCLM_subset ω hx
      exact disjoint_left.1 hω hpω ⟨p, ⟨⟨hpχ, hxT⟩, hpt⟩, rfl⟩

/-- **The mass of a homotopy current with a cutoff**: if `|χ| ≤ 1`, `‖∂ₜ H‖ ≤ A` and the spatial
derivative of `H` has operator norm at most `L` on `tsupport χ × [0, 1]`, then
`M(T ∘ K) ≤ A L ^ k M(T)` for a `k`-current `T` on `Ω` and the homotopy operator `K` with cutoff
`χ`. -/
theorem mass_comp_cutoffHomotopyPullbackCLM_le [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) (hχ : ∀ x, |χ x| ≤ 1) {A L : ℝ≥0}
    (hA : ∀ p ∈ tsupport χ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ H p (0, 1)‖ ≤ A)
    (hL : ∀ p ∈ tsupport χ ×ˢ Icc (0 : ℝ) 1, ‖(fderiv ℝ H p).comp (.inl ℝ E ℝ)‖ ≤ L) :
    mass (T ∘ (cutoffHomotopyPullbackCLM χ H hH :
        𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) ≤ A * L ^ k * mass T := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  have hpt (x : E) : ‖cutoffHomotopyPullbackCLM χ H hH ω x‖ ≤ A * L ^ k := by
    by_cases hx : x ∈ tsupport χ
    · rw [cutoffHomotopyPullbackCLM_apply, norm_smul, Real.norm_eq_abs]
      calc |χ x| * ‖cylinderHomotopy (fun p ↦ (ω (H p)).compContinuousLinearMap
              (fderiv ℝ H p)) x‖
          ≤ 1 * (1 * A * L ^ k) := by
            gcongr
            · exact hχ x
            · exact norm_cylinderHomotopy_pullback_le ω H x (fun t ht ↦ hA _ ⟨hx, ht⟩)
                (fun t ht ↦ hL _ ⟨hx, ht⟩) fun t _ ↦ hω _
        _ = A * L ^ k := by ring
    · rw [cutoffHomotopyPullbackCLM_apply, image_eq_zero_of_notMem_tsupport hx, zero_smul,
        norm_zero]
      positivity
  simpa using enorm_apply_le_mul_mass_of_forall_norm_le T (b := A * L ^ k) (by simpa using hpt)

end Distribution
