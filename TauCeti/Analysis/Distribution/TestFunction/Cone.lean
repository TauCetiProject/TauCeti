/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.CylinderHomotopy
public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
public import TauCeti.Analysis.Distribution.TestFunction.Prod

/-!
# The cone over a current

Let `Ω` be an open subset of a finite-dimensional real normed space `E`, let `p : E` and let `T`
be a `k`-current on `Ω` whose support is a compact subset of `Ω`. The **cone** `δ_p × T` over `T`
with vertex `p` is the pushforward of the product `[[0, 1]] × T` along the contraction
`(x, t) ↦ p + t • (x - p)` onto `p`. On a test `(k + 1)`-form `ω` it is

`(δ_p × T) ω = T (x ↦ ∫₀¹ t ^ k ω(p + t • (x - p))(x - p, ·) dt)`,

where the integral is cut off away from the support of `T` (`Distribution.cone`). The cone is
supported in the union of the segments from `p` to the support of `T`, so it lies in `Ω` when `Ω`
is star-shaped with respect to `p`; in general it is the restriction to `Ω` of the cone taken in
`E`, and no hypothesis on `Ω` or on `p` is needed.

The cone satisfies the **cone formula**

`∂ (δ_p × T) = T - δ_p × ∂ T` in positive degree, and `∂ (δ_p × T) = T - aug(T) δ_p` in degree zero,

where `∂ T = T ∘ d` and `aug(T)` is the augmentation (`Distribution.augmentation`). Thus the cone
over a cycle of positive degree, and over a `0`-cycle of augmentation zero, fills it. If the
support of `T` lies in the closed ball of radius `r` about `p` and `T` has finite mass, then
`M(δ_p × T) ≤ r M(T) / (k + 1)`. These are the basic inputs of local filling arguments for
currents.

On test forms, the operator `TestFunction.coneCLM p χ` sends `ω` to `χ • K ω`, where `χ` is a test
function and `K ω = x ↦ ∫₀¹ t ^ k ω(p + t • (x - p))(x - p, ·) dt` is the Poincaré homotopy
operator `TauCeti.poincareHomotopy` with centre `p`. Wherever `χ` is equal to one it satisfies the
homotopy formula of the Poincaré lemma, `K d ω + d K ω = ω` on forms of positive degree and
`K d ω = ω - ω p` on functions. Continuity for the LF topologies comes from writing it as the
cylinder homotopy operator `TestFunction.cylinderHomotopyCLM` of the pullback with cutoff
`TestFunction.cutoffPullbackCLM` along the contraction.

## Main declarations

* `TestFunction.coneCLM`: the cone operator on test forms, with values
  `TestFunction.coneCLM_apply` and pointwise bound `TestFunction.norm_coneCLM_apply_le`.
* `TestFunction.coneCLM_extDerivCLM_add_extDerivCLM_coneCLM_apply`,
  `TestFunction.coneCLM_extDerivCLM_apply_finZero`: the homotopy formula on test forms.
* `ContinuousLinearMap.comp_coneCLM_congr`, `ContinuousLinearMap.comp_coneCLM_comp_extDerivCLM`,
  `ContinuousLinearMap.comp_coneCLM_extDerivCLM_finZero`: independence of the cutoff and the cone
  formula for `T ∘ coneCLM p χ`.
* `Distribution.cone`: the cone `δ_p × T` over a current, and `Distribution.cone_eq`.
* `Distribution.cone_comp_extDerivCLM`, `Distribution.cone_extDerivCLM_finZero`: the cone
  formula.
* `Distribution.dsupport_cone_subset`: the support of the cone.
* `Distribution.mass_comp_coneCLM_le`, `Distribution.mass_cone_le`: `M(δ_p × T) ≤ r M(T) / (k + 1)`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.11 (the cone over a current, its boundary and its
  mass).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the cone construction).
-/

public section

noncomputable section

open Set Filter TopologicalSpace ContinuousAlternatingMap Distribution
open scoped Distributions Topology NNReal ENNReal Interval BoundedContinuousFunction

namespace TestFunction

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {k : ℕ} {p : E} {χ : 𝓓(Ω, ℝ)}

section Construction

/-- The contraction `(x, t) ↦ p + t • (x - p)` of `E` onto `p`. -/
private def coneMap (p : E) (q : E × ℝ) : E :=
  p + q.2 • (q.1 - p)

private theorem contDiff_coneMap (p : E) : ContDiff ℝ (⊤ : ℕ∞) (coneMap p) :=
  contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))

private theorem hasFDerivAt_coneMap (p x : E) (t : ℝ) :
    HasFDerivAt (coneMap p)
      (t • ContinuousLinearMap.fst ℝ E ℝ + (ContinuousLinearMap.snd ℝ E ℝ).smulRight (x - p))
      (x, t) := by
  have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, t))).smul
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (x, t))).sub_const p)
  exact h.const_add p

private theorem fderiv_coneMap_apply (p x : E) (t : ℝ) (v : E) (s : ℝ) :
    fderiv ℝ (coneMap p) (x, t) (v, s) = t • v + s • (x - p) := by
  simp [(hasFDerivAt_coneMap p x t).fderiv]

private theorem fderiv_coneMap_comp_inl (p x : E) (t : ℝ) :
    (fderiv ℝ (coneMap p) (x, t)).comp (.inl ℝ E ℝ) = t • ContinuousLinearMap.id ℝ E := by
  ext v
  simp [fderiv_coneMap_apply]

/-- The open cylinder `Ω × ℝ`. -/
private def cyl (Ω : Opens E) : Opens (E × ℝ) :=
  ⟨(Ω : Set E) ×ˢ univ, Ω.isOpen.prod isOpen_univ⟩

omit [NormedSpace ℝ E] in
private theorem mem_cyl {q : E × ℝ} : q ∈ cyl Ω ↔ q.1 ∈ Ω := by
  simp [cyl, ← SetLike.mem_coe]

omit [NormedSpace ℝ E] in
private theorem prod_top_subset_cyl : (Ω : Set E) ×ˢ ((⊤ : Opens ℝ) : Set ℝ) ⊆ cyl Ω :=
  fun _ hq ↦ mem_cyl.2 hq.1

/-- A test function of time equal to one near `[0, 1]`. -/
private def timeCutoff : 𝓓((⊤ : Opens ℝ), ℝ) :=
  (exists_eventually_eq_one (Ω := ⊤) (n := ⊤) isCompact_Icc
    (subset_univ (Icc (0 : ℝ) 1))).choose

private theorem timeCutoff_eventually_eq_one : ∀ᶠ t in 𝓝ˢ (Icc (0 : ℝ) 1), timeCutoff t = 1 :=
  (exists_eventually_eq_one (Ω := ⊤) (n := ⊤) isCompact_Icc
    (subset_univ (Icc (0 : ℝ) 1))).choose_spec.1

/-- The cutoff `(x, t) ↦ τ t • χ x` on the cylinder, for the time cutoff `τ`. -/
private def cylCutoff (χ : 𝓓(Ω, ℝ)) : 𝓓(cyl Ω, ℝ) :=
  prodSMulCLM timeCutoff prod_top_subset_cyl χ

/-- Near every point `(x, t)` with `t ∈ [0, 1]` near which `χ` is one, the cylinder cutoff is
one. -/
private theorem cylCutoff_eventually_eq_one {x : E} (hx : ∀ᶠ y in 𝓝 x, χ y = 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ∀ᶠ q in 𝓝 (x, t), cylCutoff χ q = 1 := by
  have hτ : ∀ᶠ s in 𝓝 t, timeCutoff s = 1 := timeCutoff_eventually_eq_one.filter_mono
    (nhds_le_nhdsSet ht)
  filter_upwards [continuous_fst.continuousAt.eventually hx,
    continuous_snd.continuousAt.eventually hτ] with q hq₁ hq₂
  simp [cylCutoff, hq₁, hq₂]

private theorem cylCutoff_apply {x : E} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cylCutoff χ (x, t) = χ x := by
  simp [cylCutoff, timeCutoff_eventually_eq_one.self_of_nhdsSet t ht]

/-- The pullback with cutoff along the contraction onto `p`. -/
private def conePullback (p : E) (χ : 𝓓(Ω, ℝ)) {m : ℕ} :
    𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] 𝓓(cyl Ω, (E × ℝ) [⋀^Fin m]→L[ℝ] F) :=
  cutoffPullbackCLM (cylCutoff χ) (coneMap p) (contDiff_coneMap p).contDiffOn

omit [NormedSpace ℝ E] in
private theorem cyl_fst_mem : ∀ q ∈ cyl Ω, q.2 ∈ Icc (0 : ℝ) 1 → q.1 ∈ Ω :=
  fun _ hq _ ↦ mem_cyl.1 hq

/-- At times `t ∈ [0, 1]`, the slices of the pulled-back form are `χ x` times the pullback of
`ω` along `x ↦ p + t • (x - p)`. -/
private theorem conePullback_apply_comp_inl {m : ℕ} (ω : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)) {x : E}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (conePullback p χ ω (x, t)).compContinuousLinearMap (.inl ℝ E ℝ) =
      χ x • (ω (coneMap p (x, t))).compContinuousLinearMap (t • ContinuousLinearMap.id ℝ E) := by
  ext v
  simp [conePullback, cylCutoff_apply ht, Function.comp_def, fderiv_coneMap_apply]

/-- The integrand of the cone operator. -/
private theorem curryLeft_conePullback_apply (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((conePullback p χ ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) =
      χ x • t ^ k • (ω (p + t • (x - p))).curryLeft (x - p) := by
  ext v
  have h := (ω (p + t • (x - p))).curryLeft (x - p) |>.map_smul_univ (fun _ ↦ t) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  simp only [conePullback, cutoffPullbackCLM_apply, cylCutoff_apply ht,
    ContinuousAlternatingMap.smul_apply, curryLeft_apply_apply, compContinuousLinearMap_apply]
  rw [← curryLeft_apply_apply, ← h, curryLeft_apply_apply]
  congr 2
  funext i
  cases i using Fin.cases <;> simp [fderiv_coneMap_apply]

/-- At time one, the slice of the pulled-back form is `χ • ω`. -/
private theorem pullbackCLM_prodMk_left_conePullback_one {m : ℕ}
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ cyl Ω →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, (1 : ℝ))) ⁻¹' K)}
    (ω : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)) (x : E) :
    pullbackCLM (fun x ↦ (x, (1 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const) hp
      (conePullback p χ ω) x = χ x • ω x := by
  rw [pullbackCLM_prodMk_left_apply cyl_fst_mem ⟨zero_le_one, le_rfl⟩,
    conePullback_apply_comp_inl ω ⟨zero_le_one, le_rfl⟩]
  ext v
  simp [coneMap]

/-- At time zero, the slice of the pulled-back form is `χ` times the pullback along the constant
map `p`. -/
private theorem pullbackCLM_prodMk_left_conePullback_zero {m : ℕ}
    {hp : ∀ K : Set (E × ℝ), IsCompact K → K ⊆ cyl Ω →
      IsCompact ((Ω : Set E) ∩ (fun x ↦ (x, (0 : ℝ))) ⁻¹' K)}
    (ω : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F)) (x : E) :
    pullbackCLM (fun x ↦ (x, (0 : ℝ))) (contDiffOn_id.prodMk contDiffOn_const) hp
      (conePullback p χ ω) x =
        χ x • (ω p).compContinuousLinearMap (0 : E →L[ℝ] E) := by
  rw [pullbackCLM_prodMk_left_apply cyl_fst_mem ⟨le_rfl, zero_le_one⟩,
    conePullback_apply_comp_inl ω ⟨le_rfl, zero_le_one⟩]
  simp [coneMap]

end Construction

variable [CompleteSpace F]

/-- The **cone operator** with vertex `p` and cutoff `χ`: the continuous linear map sending a test
`(k + 1)`-form `ω` on `Ω` to the test `k`-form
`x ↦ χ x • ∫₀¹ t ^ k ω(p + t • (x - p))(x - p, ·) dt`, see `TestFunction.coneCLM_apply`.
Precomposing a `k`-current `T` on `Ω` with it gives the cone over `T` with vertex `p` when `χ` is
equal to one near the support of `T`. -/
def coneCLM (p : E) (χ : 𝓓(Ω, ℝ)) :
    𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  cylinderHomotopyCLM cyl_fst_mem ∘L conePullback p χ

/-- The cone operator is `χ` times the Poincaré homotopy operator with centre `p`:
`x ↦ χ x • ∫₀¹ t ^ k ω(p + t • (x - p))(x - p, ·) dt`. -/
@[simp]
theorem coneCLM_apply (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    coneCLM p χ ω x = χ x • poincareHomotopy p ω x := by
  rw [coneCLM, ContinuousLinearMap.comp_apply, cylinderHomotopyCLM_apply, poincareHomotopy_apply,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [curryLeft_conePullback_apply ω ht, AffineMap.lineMap_apply_module', add_comm (t • (x - p)) p]

/-- The cone operator of a test form is pointwise bounded by `|χ x| ‖x - p‖ B / (k + 1)` for any
bound `B` of the form along the segment from `p` to `x`. -/
theorem norm_coneCLM_apply_le (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) {B : ℝ}
    (hB : ∀ y ∈ segment ℝ p x, ‖ω y‖ ≤ B) :
    ‖coneCLM p χ ω x‖ ≤ |χ x| * (‖x - p‖ * B / (k + 1)) := by
  rw [coneCLM_apply, norm_smul, Real.norm_eq_abs, poincareHomotopy_apply]
  gcongr
  have hint : ∫ t in (0 : ℝ)..1, t ^ k * (‖x - p‖ * B) = ‖x - p‖ * B / (k + 1) := by
    rw [intervalIntegral.integral_mul_const, integral_pow]
    simp only [one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, sub_zero]
    ring
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall fun t ht ↦ ?_)
    (((continuous_pow k).mul continuous_const).intervalIntegrable 0 1)).trans_eq hint
  have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht'.1 k)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht'.1 k)
  calc ‖(ω (AffineMap.lineMap p x t)).curryLeft (x - p)‖
      ≤ ‖ω (AffineMap.lineMap p x t)‖ * ‖x - p‖ :=
        ((ω (AffineMap.lineMap p x t)).curryLeft.le_opNorm _).trans_eq (by rw [norm_curryLeft])
    _ ≤ ‖x - p‖ * B := by
        rw [mul_comm]
        gcongr
        exact hB _ (lineMap_mem_segment ℝ p x ht')

/-- Where `χ` is one, the cone operator of `d ω` is the cylinder homotopy operator of the exterior
derivative of the pulled-back form. -/
private theorem coneCLM_extDerivCLM_apply_eq {m : ℕ} (ω : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F))
    {x : E} (hx : ∀ᶠ y in 𝓝 x, χ y = 1) :
    coneCLM p χ (extDerivCLM ω) x =
      cylinderHomotopyCLM cyl_fst_mem (extDerivCLM (conePullback p χ ω)) x := by
  rw [coneCLM, ContinuousLinearMap.comp_apply, coe_cylinderHomotopyCLM, coe_cylinderHomotopyCLM]
  exact cylinderHomotopy_congr fun t ht ↦
    (extDerivCLM_cutoffPullbackCLM_apply ω (cylCutoff_eventually_eq_one hx ht)).symm

/-- **The homotopy formula of the cone operator**: `K d ω + d K ω = ω` on test `(k + 1)`-forms, at
every point near which the cutoff `χ` is one. -/
theorem coneCLM_extDerivCLM_add_extDerivCLM_coneCLM_apply
    (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E} (hx : ∀ᶠ y in 𝓝 x, χ y = 1) :
    coneCLM p χ (extDerivCLM ω) x + extDerivCLM (coneCLM p χ ω) x = ω x := by
  have hK : (coneCLM p χ ω : E → E [⋀^Fin k]→L[ℝ] F) =ᶠ[𝓝 x] poincareHomotopy p ω :=
    hx.mono fun y hy ↦ by rw [coneCLM_apply, hy, one_smul]
  rw [coneCLM_apply, hx.self_of_nhds, one_smul, extDerivCLM_apply, coe_extDerivCLM,
    hK.extDeriv_eq]
  exact (add_comm _ _).trans <|
    (starConvex_univ p).extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv isOpen_univ
      (ω.contDiff.of_le (by simp)).contDiffOn (mem_univ x)

/-- **The homotopy formula of the cone operator on functions**: `K d ω = ω - ω p` for a test
`0`-form `ω`, at every point near which the cutoff `χ` is one. -/
theorem coneCLM_extDerivCLM_apply_finZero (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F)) {x : E}
    (hx : ∀ᶠ y in 𝓝 x, χ y = 1) :
    coneCLM p χ (extDerivCLM ω) x = ω x - ω p := by
  have h := congr($(cylinderHomotopyCLM_comp_extDerivCLM_finZero (hW := cyl_fst_mem) (F := F))
    (conePullback p χ ω) x)
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply] at h
  rw [coneCLM_extDerivCLM_apply_eq ω hx, h, pullbackCLM_prodMk_left_conePullback_one,
    pullbackCLM_prodMk_left_conePullback_zero, hx.self_of_nhds, one_smul, one_smul]
  congr 1
  ext v
  simp [Subsingleton.elim v 0]

end TestFunction

namespace ContinuousLinearMap

open TestFunction

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {Ω : Opens E} {k : ℕ} {p : E} {χ χ₁ χ₂ : 𝓓(Ω, ℝ)}

/-- **Independence of the cutoff**: the cone `T ∘ coneCLM p χ` over a current `T` depends only on
the germ of `χ` along the support of `T`. -/
theorem comp_coneCLM_congr (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    (h : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₂) :
    (T ∘L coneCLM p χ₁ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) = T ∘L coneCLM p χ₂ := by
  ext ω
  exact map_eq_map_of_eventuallyEq T (h.mono fun x hx ↦ by simp only [coe_coe, coneCLM_apply, hx])

/-- **The cone formula**: if `χ` is equal to one near the support of a current `T` on test
`(k + 1)`-forms, then `∂ (T ∘ coneCLM p χ) = T - (∂ T) ∘ coneCLM p χ`, where `∂ T = T ∘ d`. The
support of `∂ T` lies in that of `T`, so the last term is the cone over `∂ T`. -/
theorem comp_coneCLM_comp_extDerivCLM [IsTopologicalAddGroup G]
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (T ∘L coneCLM p χ) ∘L (extDerivCLM : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      T - (T ∘L extDerivCLM) ∘L coneCLM p χ := by
  ext ω
  rw [comp_apply, comp_apply, _root_.sub_apply, comp_apply, comp_apply, eq_sub_iff_add_eq,
    ← map_add]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  simpa using coneCLM_extDerivCLM_add_extDerivCLM_coneCLM_apply ω hx

/-- **The cone formula in degree zero**: if `χ` is equal to one near the support of a current `T`
on test `0`-forms, then `∂ (T ∘ coneCLM p χ) = T - aug(T) δ_p`, where `aug` is the augmentation. -/
theorem comp_coneCLM_extDerivCLM_finZero (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F)) :
    T (coneCLM p χ (extDerivCLM ω)) = T ω - augmentation T (ω p) := by
  rw [augmentation_eq T hχ, ← map_sub]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet, hχ] with x hx hx₁
  simp [coneCLM_extDerivCLM_apply_finZero ω hx, hx₁]

end ContinuousLinearMap

namespace Distribution

open TestFunction TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {Ω : Opens E} {k : ℕ} {p : E} {χ : 𝓓(Ω, ℝ)}

open Classical in
/-- The **cone** `δ_p × T` over a `k`-current `T` on `Ω` with vertex `p`: the `(k + 1)`-current
`T ∘ coneCLM p χ`, for a test function `χ` equal to one on a neighbourhood of the support of `T`
(`Distribution.cone_eq`). It is the pushforward of `[[0, 1]] × T` along `(x, t) ↦ p + t • (x - p)`.
It is zero when no such `χ` exists, that is when the support of `T` is not a compact subset
of `Ω`. -/
def cone (p : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G) :
    𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G :=
  if h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 then T ∘L coneCLM p h.choose else 0

/-- The cone is zero when no test function is equal to one on a neighbourhood of the support. -/
@[simp]
theorem cone_of_not_exists {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G}
    (h : ¬∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) : cone p T = 0 := by
  rw [cone, dite_eq_right h]

variable [FiniteDimensional ℝ E]

/-- **Independence of the cutoff**: the cone over `T` is `T ∘ coneCLM p χ` for every test function
`χ` equal to one on a neighbourhood of the support of `T`. -/
theorem cone_eq {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) : cone p T = T ∘L coneCLM p χ := by
  have h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 := ⟨χ, hχ⟩
  rw [cone, dite_eq_left h]
  exact T.comp_coneCLM_congr ((h.choose_spec.and hχ).mono fun x hx ↦ hx.1.trans hx.2.symm)

/-- **The cone formula**: `∂ (δ_p × T) = T - δ_p × ∂ T` for a current `T` on test
`(k + 1)`-forms whose support is a compact subset of `Ω`, where `∂ T = T ∘ d`. In particular the
cone over a cycle fills it. -/
theorem cone_comp_extDerivCLM [IsTopologicalAddGroup G] (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G)
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    cone p T ∘L extDerivCLM = T - cone p (T ∘L extDerivCLM) := by
  obtain ⟨χ, hχ, -⟩ := exists_eventually_eq_one (n := ⊤) hT hTΩ
  have hχd : ∀ᶠ x in 𝓝ˢ (dsupport (T ∘L extDerivCLM)), χ x = 1 :=
    hχ.filter_mono (nhdsSet_mono (dsupport_comp_extDerivCLM_subset T))
  rw [cone_eq hχ, cone_eq hχd, T.comp_coneCLM_comp_extDerivCLM hχ]

/-- **The cone formula in degree zero**: `∂ (δ_p × T) = T - aug(T) δ_p` for a current `T` on test
`0`-forms whose support is a compact subset of `Ω`, where `aug` is the augmentation. In particular
the cone over a `0`-current of augmentation zero fills it. -/
theorem cone_extDerivCLM_finZero (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G)
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F)) :
    cone p T (extDerivCLM ω) = T ω - augmentation T (ω p) := by
  obtain ⟨χ, hχ, -⟩ := exists_eventually_eq_one (n := ⊤) hT hTΩ
  rw [cone_eq hχ, ContinuousLinearMap.comp_apply, T.comp_coneCLM_extDerivCLM_finZero hχ]

/-- **The support of the cone** over `T` lies in the union of the segments from `p` to the points
of the support of `T`. -/
theorem dsupport_cone_subset (p : E) (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G) :
    dsupport (cone p T) ⊆ ⋃ x ∈ dsupport T, segment ℝ p x := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  swap
  · rw [cone_of_not_exists h, (dsupport_eq_empty_iff (0 : _ →L[ℝ] G)).2 rfl]
    exact empty_subset _
  obtain ⟨χ, hχ⟩ := h
  have hTc : IsCompact (dsupport T) :=
    χ.hasCompactSupport.of_isClosed_subset isClosed_dsupport fun x hx ↦
      subset_tsupport _ (by simp [hχ.self_of_nhdsSet x hx])
  have hC : (fun q : E × ℝ ↦ p + q.2 • (q.1 - p)) '' (dsupport T ×ˢ Icc 0 1) =
      ⋃ x ∈ dsupport T, segment ℝ p x := by
    ext y
    simp only [mem_image, mem_prod, Prod.exists, mem_iUnion, segment_eq_image', exists_prop]
    grind
  rw [← hC]
  have hCc : IsCompact ((fun q : E × ℝ ↦ p + q.2 • (q.1 - p)) '' (dsupport T ×ˢ Icc 0 1)) :=
    (hTc.prod isCompact_Icc).image (by fun_prop)
  -- A test form supported off the cone vanishes along every segment from `p` to points near the
  -- support of `T`, so its cone vanishes near the support of `T`.
  have hvan : IsVanishingOn (cone p T)
      ((fun q : E × ℝ ↦ p + q.2 • (q.1 - p)) '' (dsupport T ×ˢ Icc 0 1))ᶜ := fun ω hω ↦ by
    rw [cone_eq hχ, ContinuousLinearMap.comp_apply, ← map_zero T]
    refine map_eq_map_of_eventuallyEq T (eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_)
    have hseg : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (y - p) ∉ tsupport ω :=
      isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦
        (show Continuous fun q : E × ℝ ↦ p + q.2 • (q.1 - p) by fun_prop).continuousAt.eventually
          ((isClosed_tsupport ω).isOpen_compl.mem_nhds fun hmem ↦ hω hmem ⟨(x, t), ⟨hx, ht⟩, rfl⟩)
    filter_upwards [hseg] with y hy
    have h0 : poincareHomotopy p ω y = 0 := by
      rw [poincareHomotopy_congr (ω₂ := 0) fun z hz ↦ ?_, poincareHomotopy_zero, Pi.zero_apply]
      rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact image_eq_zero_of_notMem_tsupport (hy t ht)
    simp [h0]
  have hsub := (hvan.disjoint_dsupport hCc.isClosed.isOpen_compl).subset_compl_left
  rwa [compl_compl] at hsub

section Mass

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [FiniteDimensional ℝ E] in
/-- **The mass of a cone**: if `|χ| ≤ 1` and `‖x - p‖ ≤ r` on the support of `χ`, then
`M(T ∘ coneCLM p χ) ≤ r M(T) / (k + 1)` for a `k`-current `T`. -/
theorem mass_comp_coneCLM_le {𝓕 : Type*} [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] (T : 𝓕) (hχ : ∀ x, |χ x| ≤ 1) {r : ℝ≥0}
    (hr : ∀ x ∈ tsupport χ, ‖x - p‖ ≤ r) :
    mass (T ∘ (coneCLM p χ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) ≤
      ((r / (k + 1) : ℝ≥0) : ℝ≥0∞) * mass T := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  have hb : ‖(coneCLM p χ ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ ≤ (r / (k + 1) : ℝ≥0) := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [coe_toBoundedContinuousFunction]
    by_cases hx : x ∈ tsupport χ
    · refine (norm_coneCLM_apply_le ω x fun t _ ↦ hω _).trans ?_
      calc |χ x| * (‖x - p‖ * 1 / (k + 1)) ≤ 1 * (r * 1 / (k + 1)) := by
            gcongr
            exacts [hχ x, hr x hx]
        _ = (r / (k + 1) : ℝ≥0) := by simp
    · have h0 : coneCLM p χ ω x = 0 := by
        rw [coneCLM_apply, image_eq_zero_of_notMem_tsupport hx, zero_smul]
      rw [h0, norm_zero]
      positivity
  calc ‖T (coneCLM p χ ω)‖ₑ
      ≤ mass T * ‖(coneCLM p χ ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ :=
        enorm_apply_le_mass_mul T _
    _ ≤ mass T * ((r / (k + 1) : ℝ≥0) : ℝ≥0∞) := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hb
    _ = ((r / (k + 1) : ℝ≥0) : ℝ≥0∞) * mass T := mul_comm _ _

/-- **The mass of the cone**: if the support of a `k`-current `T` of finite mass lies in the closed
ball of radius `r` about `p`, then `M(δ_p × T) ≤ r M(T) / (k + 1)`. -/
theorem mass_cone_le (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) {r : ℝ≥0}
    (hr : dsupport T ⊆ Metric.closedBall p r) (hT : mass T ≠ ⊤) :
    mass (cone p T) ≤ ((r / (k + 1) : ℝ≥0) : ℝ≥0∞) * mass T := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  swap
  · rw [cone_of_not_exists h, FunLike.coe_zero, mass_zero]
    exact zero_le
  obtain ⟨χ₀, hχ₀⟩ := h
  have hTΩ : dsupport T ⊆ Ω := fun x hx ↦
    χ₀.tsupport_subset (subset_tsupport _ (by simp [hχ₀.self_of_nhdsSet x hx]))
  have hTc : IsCompact (dsupport T) :=
    (isCompact_closedBall p r).of_isClosed_subset isClosed_dsupport hr
  -- For every `ε > 0`, a cutoff supported in the ball of radius `r + ε` gives the bound with
  -- `r + ε` in place of `r`.
  have key (ε : ℝ≥0) (hε : 0 < ε) :
      mass (cone p T) ≤ (((r + ε) / (k + 1) : ℝ≥0) : ℝ≥0∞) * mass T := by
    let U : Opens E := Ω ⊓ ⟨Metric.ball p (r + ε), Metric.isOpen_ball⟩
    have hTU : dsupport T ⊆ U := fun x hx ↦
      ⟨hTΩ hx, Metric.mem_ball.2 ((Metric.mem_closedBall.1 (hr hx)).trans_lt (by simpa))⟩
    obtain ⟨χ, hχ, hχ01⟩ := exists_eventually_eq_one (n := ⊤) hTc hTU
    have hUΩ : U ≤ Ω := inf_le_left
    have hχΩ : ((monoCLM ℝ χ : 𝓓(Ω, ℝ)) : E → ℝ) = χ := by
      simp [hUΩ]
    rw [cone_eq (χ := monoCLM ℝ χ) (by rwa [hχΩ])]
    refine mass_comp_coneCLM_le T (fun x ↦ ?_) fun x hx ↦ ?_
    · rw [hχΩ, abs_le]
      exact ⟨(neg_nonpos.2 zero_le_one).trans (hχ01 x).1, (hχ01 x).2⟩
    · rw [hχΩ] at hx
      simpa [dist_eq_norm] using (Metric.mem_ball.1 (χ.tsupport_subset hx).2).le
  have hlim : Tendsto (fun ε : ℝ≥0 ↦ (((r + ε) / (k + 1) : ℝ≥0) : ℝ≥0∞) * mass T) (𝓝[>] 0)
      (𝓝 (((r / (k + 1) : ℝ≥0) : ℝ≥0∞) * mass T)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hT)
    refine (ENNReal.continuous_coe.tendsto _).comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    simpa using ((continuous_const.add continuous_id).div_const (k + 1 : ℝ≥0)).tendsto 0
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

end Mass

end Distribution
