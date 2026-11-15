/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Analysis.Complex.HolomorphicFunctions.ComparisonMetric
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Jet
public import TauCeti.Topology.ContinuousMap.CompactConvergence

/-!
# Complex differentiation on `holomorphicFunctions U`

For an open subset `U : Opens ℂ` of the complex plane, complex differentiation sends every
`f : holomorphicFunctions U` to the restriction of `_root_.deriv (HolomorphicFunctions.extend f)`
back to `U`. Because locally uniform limits of holomorphic functions have locally uniform
derivatives (`TendstoLocallyUniformlyOn.deriv`) and convergence in `holomorphicFunctions U` is
locally uniform convergence of zero extensions (`tendsto_iff_tendstoLocallyUniformlyOn`),
differentiation is a continuous complex-linear endomorphism
`HolomorphicFunctions.deriv : holomorphicFunctions U →L[ℂ] holomorphicFunctions U` for the
compact-open topology.

This file provides:

* the `IsUniformAddGroup (holomorphicFunctions U)` instance inherited from compact convergence on
  `C(U, ℂ)`, together with continuous point evaluation `HolomorphicFunctions.eval` and
  `HolomorphicFunctions.evalCLM`;
* the continuous linear derivative `HolomorphicFunctions.deriv`, its Leibniz rule `deriv_mul`, its
  bundling `HolomorphicFunctions.derivation` as a `ℂ`-derivation, and compatibility with open
  restriction (`restrict_deriv`);
* Cauchy derivative estimates on closed discs (`norm_extend_deriv_le_of_closedBall_subset`) and
  compact thickenings (`norm_extend_deriv_le_of_cthickening_subset`), together with uniform
  continuity (`uniformContinuous_deriv`) and an explicit quantitative modulus in
  `comparisonDist U` (`exists_pos_forall_comparisonDist_deriv_lt`);
* agreement of `deriv^[k]` with `iteratedDeriv k`, deducing compact-open continuity of the finite
  jet map `HolomorphicFunctions.jet` (`continuous_jet`) and closedness of its kernel
  (`isClosed_ker_jet`);
* the unit-disc sequence $f_n(z) = z^{n + 1} / (n + 1)$, which tends to `0` in
  `holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩` together with its derivatives $f_n'(z) = z^n$,
  even though $\sup_{|z| < 1} |f_n(z)| = 1 / (n + 1)$ while $\sup_{|z| < 1} |f_n'(z)| = 1$, showing
  that differentiation is unbounded for the global supremum norm on `ball 0 1`.

## References

* Armin Rainer, *Advanced Complex Analysis*, §11, Exercise 20.
* Walter Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.28.
-/

public noncomputable section

open Filter Function Metric Set Topology TopologicalSpace

namespace TauCeti

/-- `holomorphicFunctions U` is a uniform additive group for the compact-convergence uniformity
inherited from `C(U, ℂ)`. -/
instance (U : Opens ℂ) : IsUniformAddGroup (holomorphicFunctions U) :=
  _root_.IsUniformInducing.isUniformAddGroup
    (AddMonoidHom.mk' Subtype.val fun _ _ ↦ rfl) ⟨rfl⟩

namespace HolomorphicFunctions

section PointEvaluation

variable {U V : Opens ℂ}

/-- Point evaluation at `z : U` as a complex algebra homomorphism `holomorphicFunctions U →ₐ[ℂ] ℂ`.
-/
def eval (z : U) : holomorphicFunctions U →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : U ↦ ℂ) z).comp
    ((ContinuousMap.coeFnAlgHom ℂ).comp (holomorphicFunctions U).val)

/-- Evaluating `eval z` at `f` returns `f.val z`. -/
@[simp]
theorem eval_apply (z : U) (f : holomorphicFunctions U) : eval z f = f.val z := (rfl)

/-- Point evaluation agrees with the zero extension `extend f` at points of `U`. -/
theorem eval_apply_eq_extend (z : U) (f : holomorphicFunctions U) : eval z f = extend f z :=
  (extend_apply f z).symm

/-- Point evaluation of `of U g hg` at `z : U` returns `g z`. -/
theorem eval_of (z : U) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    eval z (of U g hg) = g z :=
  of_apply g hg z

/-- Point evaluation commutes with open restriction along `V ≤ U`. -/
theorem eval_restrict (h : V ≤ U) (z : V) (f : holomorphicFunctions U) :
    eval z (restrict h f) = eval (Set.inclusion h z) f :=
  restrict_apply h f z

/-- Point evaluation on `holomorphicFunctions U` is continuous for the compact-open topology. -/
theorem continuous_eval (z : U) : Continuous (eval z) :=
  (continuous_eval_const z).comp continuous_subtype_val

/-- Point evaluation at `z : U` as a continuous complex-linear functional
`holomorphicFunctions U →L[ℂ] ℂ`. -/
def evalCLM (z : U) : holomorphicFunctions U →L[ℂ] ℂ where
  toLinearMap := (eval z).toLinearMap
  cont := continuous_eval z

/-- Evaluating `evalCLM z` at `f` returns `f.val z`. -/
@[simp]
theorem evalCLM_apply (z : U) (f : holomorphicFunctions U) : evalCLM z f = f.val z := (rfl)

/-- Point evaluation on `holomorphicFunctions U` is uniformly continuous. -/
theorem uniformContinuous_eval (z : U) : UniformContinuous (eval z) :=
  uniformContinuous_addMonoidHom_of_continuous (continuous_eval z)

end PointEvaluation

section Deriv

variable {U V : Opens ℂ}

private def derivFun (f : holomorphicFunctions U) : holomorphicFunctions U :=
  of U (_root_.deriv (extend f)) ((differentiableOn_extend f).deriv U.isOpen)

private theorem derivFun_add (f g : holomorphicFunctions U) :
    derivFun (f + g) = derivFun f + derivFun g := by
  apply Subtype.ext
  ext z
  have heq : extend (f + g) =ᶠ[𝓝 (z : ℂ)] extend f + extend g := by
    filter_upwards [U.isOpen.mem_nhds z.2] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [derivFun, Subalgebra.coe_add, ContinuousMap.add_apply, of_apply]
  rw [heq.deriv_eq, deriv_add
    ((differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds z.2))
    ((differentiableOn_extend g).differentiableAt (U.isOpen.mem_nhds z.2))]

private theorem derivFun_smul (c : ℂ) (f : holomorphicFunctions U) :
    derivFun (c • f) = c • derivFun f := by
  apply Subtype.ext
  ext z
  have heq : extend (c • f) =ᶠ[𝓝 (z : ℂ)] c • extend f := by
    filter_upwards [U.isOpen.mem_nhds z.2] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [derivFun, SetLike.val_smul, ContinuousMap.smul_apply, of_apply]
  rw [heq.deriv_eq, deriv_const_smul c
    ((differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds z.2))]

private theorem continuous_derivFun : Continuous (derivFun (U := U)) := by
  refine continuous_iff_continuousAt.mpr fun f ↦ ?_
  change Tendsto _ (𝓝 f) (𝓝 _)
  rw [tendsto_iff_tendstoLocallyUniformlyOn]
  have hid : TendstoLocallyUniformlyOn extend (extend f) (𝓝 f) U :=
    tendsto_iff_tendstoLocallyUniformlyOn.mp tendsto_id
  have hd := hid.deriv (Eventually.of_forall fun g ↦ differentiableOn_extend g) U.isOpen
  refine (hd.congr fun g z hz ↦ ?_).congr_right fun z hz ↦ ?_
  · exact ((extend_apply _ ⟨z, hz⟩).trans (of_apply _ _ ⟨z, hz⟩)).symm
  · exact ((extend_apply _ ⟨z, hz⟩).trans (of_apply _ _ ⟨z, hz⟩)).symm

/-- Complex differentiation as a continuous complex-linear endomorphism of
`holomorphicFunctions U` with the compact-open topology. -/
def deriv : holomorphicFunctions U →L[ℂ] holomorphicFunctions U where
  toFun := derivFun
  map_add' := derivFun_add
  map_smul' := derivFun_smul
  cont := continuous_derivFun

/-- Evaluating `deriv f` at `z : U` computes `_root_.deriv (extend f) z`. -/
@[simp]
theorem deriv_apply (f : holomorphicFunctions U) (z : U) :
    (deriv f).val z = _root_.deriv (extend f) z :=
  of_apply (_root_.deriv (extend f)) _ z

/-- On `U`, the zero extension of `deriv f` agrees with `_root_.deriv (extend f)`. -/
@[simp]
theorem extend_deriv_of_mem (f : holomorphicFunctions U) {z : ℂ} (hz : z ∈ U) :
    extend (deriv f) z = _root_.deriv (extend f) z :=
  (extend_apply (deriv f) ⟨z, hz⟩).trans (deriv_apply f ⟨z, hz⟩)

/-- `extend (deriv f)` and `_root_.deriv (extend f)` agree on `U`. -/
theorem eqOn_extend_deriv (f : holomorphicFunctions U) :
    EqOn (extend (deriv f)) (_root_.deriv (extend f)) U :=
  fun _ hz ↦ extend_deriv_of_mem f hz

/-- Differentiation of `of U g hg` agrees with restricting `_root_.deriv g` to `U`. -/
@[simp]
theorem deriv_of (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    deriv (of U g hg) = of U (_root_.deriv g) (hg.deriv U.isOpen) := by
  apply Subtype.ext
  ext z
  rw [deriv_apply, of_apply]
  apply EventuallyEq.deriv_eq
  filter_upwards [U.isOpen.mem_nhds z.2] with w hw
  exact (extend_apply (of U g hg) ⟨w, hw⟩).trans (of_apply g hg ⟨w, hw⟩)

/-- Constant holomorphic functions have derivative `0`. -/
@[simp]
theorem deriv_algebraMap (c : ℂ) : deriv (algebraMap ℂ (holomorphicFunctions U) c) = 0 := by
  apply Subtype.ext
  ext z
  have heq : extend (algebraMap ℂ (holomorphicFunctions U) c) =ᶠ[𝓝 (z : ℂ)] fun _ ↦ c := by
    filter_upwards [U.isOpen.mem_nhds z.2] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [deriv_apply, Subalgebra.coe_zero, ContinuousMap.zero_apply]
  rw [heq.deriv_eq, deriv_const]

/-- The multiplicative identity `1 : holomorphicFunctions U` has derivative `0`. -/
@[simp]
theorem deriv_one : deriv (1 : holomorphicFunctions U) = 0 := by
  rw [← map_one (algebraMap ℂ (holomorphicFunctions U)), deriv_algebraMap]

/-- Every natural-number cast `(n : holomorphicFunctions U)` has derivative `0`. -/
@[simp]
theorem deriv_natCast (n : ℕ) : deriv (n : holomorphicFunctions U) = 0 := by
  rw [← map_natCast (algebraMap ℂ (holomorphicFunctions U)), deriv_algebraMap]

/-- Leibniz product rule for `HolomorphicFunctions.deriv`. -/
theorem deriv_mul (f g : holomorphicFunctions U) :
    deriv (f * g) = f * deriv g + g * deriv f := by
  apply Subtype.ext
  ext z
  have heq : extend (f * g) =ᶠ[𝓝 (z : ℂ)] extend f * extend g := by
    filter_upwards [U.isOpen.mem_nhds z.2] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [deriv_apply, Subalgebra.coe_add, Subalgebra.coe_mul, ContinuousMap.add_apply,
    ContinuousMap.mul_apply]
  rw [heq.deriv_eq, _root_.deriv_mul
    ((differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds z.2))
    ((differentiableOn_extend g).differentiableAt (U.isOpen.mem_nhds z.2)),
    extend_apply, extend_apply]
  ring

/-- Complex differentiation on `holomorphicFunctions U` bundled as a `ℂ`-derivation. -/
def derivation : Derivation ℂ (holomorphicFunctions U) (holomorphicFunctions U) where
  toLinearMap := deriv.toLinearMap
  map_one_eq_zero' := deriv_one
  leibniz' f g := by simp only [smul_eq_mul, ContinuousLinearMap.coe_coe, deriv_mul]

/-- Applying `derivation` agrees with `deriv`. -/
@[simp]
theorem derivation_apply (f : holomorphicFunctions U) : derivation f = deriv f := (rfl)

/-- Power rule for `HolomorphicFunctions.deriv`. -/
theorem deriv_pow (f : holomorphicFunctions U) (n : ℕ) :
    deriv (f ^ n) = n • (f ^ (n - 1) * deriv f) := by
  simpa only [derivation_apply, smul_eq_mul] using derivation.leibniz_pow f n

/-- Complex differentiation commutes with restriction to a smaller open domain. -/
@[simp]
theorem restrict_deriv (h : V ≤ U) (f : holomorphicFunctions U) :
    restrict h (deriv f) = deriv (restrict h f) := by
  apply Subtype.ext
  ext z
  symm
  simp only [restrict_apply, deriv_apply]
  apply EventuallyEq.deriv_eq
  filter_upwards [V.isOpen.mem_nhds z.2] with w hw
  simp only [extend_apply _ ⟨w, hw⟩, restrict_apply, extend_apply _ ⟨w, h hw⟩]

/-- Complex differentiation is uniformly continuous for the compact-convergence uniformity on
`holomorphicFunctions U`. -/
theorem uniformContinuous_deriv :
    UniformContinuous ⇑(deriv : holomorphicFunctions U →L[ℂ] holomorphicFunctions U) :=
  uniformContinuous_addMonoidHom_of_continuous
    (f := AddMonoidHom.mk' (deriv (U := U)) (map_add deriv)) deriv.continuous

end Deriv

section CauchyEstimates

variable {U : Opens ℂ}

/-- **Cauchy derivative estimate on a closed disc.** If `closedBall z r ⊆ U` with `0 < r` and
`‖extend f w‖ ≤ M` on the boundary circle `sphere z r`, then `‖extend (deriv f) z‖ ≤ M / r`. -/
theorem norm_extend_deriv_le_of_closedBall_subset {z : ℂ} {r M : ℝ} (hr : 0 < r)
    (hsub : closedBall z r ⊆ U) (f : holomorphicFunctions U)
    (hM : ∀ w ∈ sphere z r, ‖extend f w‖ ≤ M) :
    ‖extend (deriv f) z‖ ≤ M / r := by
  rw [extend_deriv_of_mem f (hsub (mem_closedBall_self hr.le)),
    ← Complex.cderiv_eq_deriv U.isOpen (differentiableOn_extend f) hr hsub]
  exact Complex.norm_cderiv_le hr hM

/-- **Cauchy derivative estimate on a closed thickening.** If `cthickening δ K ⊆ U` with `0 < δ`
and `‖extend f w‖ ≤ M` on `cthickening δ K`, then `‖extend (deriv f) z‖ ≤ M / δ` for every
`z ∈ K`. -/
theorem norm_extend_deriv_le_of_cthickening_subset {K : Set ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hδU : cthickening δ K ⊆ U) (f : holomorphicFunctions U)
    (hM : ∀ w ∈ cthickening δ K, ‖extend f w‖ ≤ M) {z : ℂ} (hz : z ∈ K) :
    ‖extend (deriv f) z‖ ≤ M / δ :=
  norm_extend_deriv_le_of_closedBall_subset hδ
    ((closedBall_subset_cthickening hz δ).trans hδU) f
    fun w hw ↦ hM w (closedBall_subset_cthickening hz δ (sphere_subset_closedBall hw))

/-- Quantitative Cauchy bound for differences of derivatives on a compact subset `K ⊆ U` with
`cthickening δ K ⊆ U`. -/
theorem norm_restrictContinuousMap_deriv_sub_le {K : Set ℂ} [CompactSpace K] {δ : ℝ} (hδ : 0 < δ)
    (hδU : cthickening δ K ⊆ U) (f g : holomorphicFunctions U) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ cthickening δ K, ‖extend f w - extend g w‖ ≤ M) :
    ‖restrictContinuousMap ((self_subset_cthickening K).trans hδU) (deriv f) -
      restrictContinuousMap ((self_subset_cthickening K).trans hδU) (deriv g)‖ ≤ M / δ := by
  rw [ContinuousMap.norm_le _ (div_nonneg hM0 hδ.le)]
  intro z
  have hfg : ∀ w ∈ cthickening δ K, ‖extend (f - g) w‖ ≤ M := by
    intro w hw
    simpa only [extend_apply _ ⟨w, hδU hw⟩, Subalgebra.coe_sub, ContinuousMap.sub_apply] using
      hM w hw
  have hbound := norm_extend_deriv_le_of_cthickening_subset hδ hδU (f - g) hfg z.2
  have hzU : z.1 ∈ U := ((self_subset_cthickening K).trans hδU) z.2
  rw [map_sub deriv f g, extend_apply _ ⟨z.1, hzU⟩, Subalgebra.coe_sub,
    ContinuousMap.sub_apply] at hbound
  simpa only [ContinuousMap.sub_apply, restrictContinuousMap_apply] using hbound

/-- Quantitative modulus of uniform continuity for `deriv` with respect to `comparisonDist U`:
for every `ε > 0`, sufficiently `comparisonDist U`-close holomorphic functions have
`comparisonDist U`-close derivatives. -/
theorem exists_pos_forall_comparisonDist_deriv_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ f g : holomorphicFunctions U,
      comparisonDist U f g < η → comparisonDist U (deriv f) (deriv g) < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow : (1 / 2 : ℝ) ^ (N + 1) < ε / 2 :=
    (pow_le_pow_of_le_one (by positivity) (by norm_num) (Nat.le_succ N)).trans_lt hN
  let K : Set ℂ := ((↑) : U → ℂ) '' U.compactExhaustion 0 N
  have hK : IsCompact K := (U.compactExhaustion 0).isCompact N |>.image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨z, -, rfl⟩; exact z.2
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  have : CompactSpace (cthickening δ K) := isCompact_iff_compactSpace.mp hK.cthickening
  obtain ⟨η, hη, hmod⟩ :=
    exists_pos_forall_norm_restrictContinuousMap_sub_lt hδU (mul_pos (half_pos hε) hδ)
  refine ⟨η, hη, fun f g hfg ↦ ?_⟩
  have hsup := hmod f g hfg
  have hstage : dist ((deriv f).val.restrict (U.compactExhaustion 0 N))
      ((deriv g).val.restrict (U.compactExhaustion 0 N)) ≤ ε / 2 := by
    rw [ContinuousMap.dist_le (half_pos hε).le]
    intro z
    have hzK : (z : ℂ) ∈ K := mem_image_of_mem _ z.2
    have hpt : ∀ w ∈ cthickening δ K, ‖extend (f - g) w‖ ≤ ε / 2 * δ := by
      intro w hw
      have hle := ContinuousMap.norm_coe_le_norm
        (restrictContinuousMap hδU f - restrictContinuousMap hδU g) ⟨w, hw⟩
      simpa only [extend_apply _ ⟨w, hδU hw⟩, Subalgebra.coe_sub, ContinuousMap.sub_apply,
        restrictContinuousMap_apply] using hle.trans hsup.le
    have hbound := norm_extend_deriv_le_of_cthickening_subset hδ hδU (f - g) hpt hzK
    rw [mul_div_cancel_right₀ _ hδ.ne', map_sub deriv f g, extend_apply _ z.1,
      Subalgebra.coe_sub, ContinuousMap.sub_apply] at hbound
    simpa only [ContinuousMap.restrict_apply, dist_eq_norm] using hbound
  exact (comparisonDist_le_dist_restrict_add_pow_half (deriv f) (deriv g) N).trans_lt
    (by linarith)

end CauchyEstimates

section IteratedDerivAndJets

variable {U : Opens ℂ}

/-- Iterating `HolomorphicFunctions.deriv` `k` times computes `iteratedDeriv k (extend f)` on `U`.
-/
@[simp]
theorem iterate_deriv_apply (k : ℕ) (f : holomorphicFunctions U) (z : U) :
    (deriv^[k] f).val z = iteratedDeriv k (extend f) z := by
  induction k generalizing f z with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', deriv_apply, iteratedDeriv_succ]
    apply EventuallyEq.deriv_eq
    filter_upwards [U.isOpen.mem_nhds z.2] with w hw
    exact (extend_apply _ ⟨w, hw⟩).trans (ih f ⟨w, hw⟩)

/-- On `U`, the zero extension of `deriv^[k] f` agrees with `iteratedDeriv k (extend f)`. -/
@[simp]
theorem extend_iterate_deriv_of_mem (k : ℕ) (f : holomorphicFunctions U) {z : ℂ} (hz : z ∈ U) :
    extend (deriv^[k] f) z = iteratedDeriv k (extend f) z :=
  (extend_apply _ ⟨z, hz⟩).trans (iterate_deriv_apply k f ⟨z, hz⟩)

/-- Each coordinate of the finite jet `jet ha n` is point evaluation of an iterated derivative. -/
theorem jet_apply_eq_eval_iterate_deriv {a : ℂ} (ha : a ∈ U) (n : ℕ)
    (f : holomorphicFunctions U) (i : Fin n) :
    jet ha n f i = eval ⟨a, ha⟩ (deriv^[i] f) := by
  rw [jet_apply, eval_apply, iterate_deriv_apply]

/-- The finite jet map `jet ha n : holomorphicFunctions U →ₗ[ℂ] (Fin n → ℂ)` is continuous for the
compact-open topology. -/
theorem continuous_jet {a : ℂ} (ha : a ∈ U) (n : ℕ) : Continuous (jet ha n) := by
  refine continuous_pi fun i ↦ ?_
  have heq : (fun f ↦ jet ha n f i) = fun f ↦ eval ⟨a, ha⟩ (deriv^[i] f) :=
    funext fun f ↦ jet_apply_eq_eval_iterate_deriv ha n f i
  rw [heq]
  exact (continuous_eval ⟨a, ha⟩).comp (deriv.continuous.iterate i)

/-- The kernel of a finite jet `jet ha n` is closed in `holomorphicFunctions U`. -/
theorem isClosed_ker_jet {a : ℂ} (ha : a ∈ U) (n : ℕ) :
    IsClosed ((jet ha n).ker : Set (holomorphicFunctions U)) := by
  change IsClosed (jet ha n ⁻¹' {0})
  exact isClosed_singleton.preimage (continuous_jet ha n)

end IteratedDerivAndJets

section UnitDiscCheck

/-- The holomorphic monomials $f_n(z) = z^{n + 1} / (n + 1)$ on the open unit disc `ball 0 1`. -/
def unitDiscPowDivSucc (n : ℕ) : holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩ :=
  of ⟨ball 0 1, isOpen_ball⟩ (fun z ↦ z ^ (n + 1) / (n + 1 : ℂ))
    ((differentiableOn_pow (n + 1)).div_const _)

/-- Evaluating `unitDiscPowDivSucc n` at `z` returns `z ^ (n + 1) / (n + 1)`. -/
@[simp]
theorem unitDiscPowDivSucc_apply (n : ℕ) (z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)) :
    (unitDiscPowDivSucc n).val z = (z : ℂ) ^ (n + 1) / (n + 1 : ℂ) :=
  of_apply _ _ z

/-- Differentiating $f_n(z) = z^{n + 1} / (n + 1)$ on the unit disc yields $f_n'(z) = z^n$. -/
@[simp]
theorem deriv_unitDiscPowDivSucc (n : ℕ) :
    deriv (unitDiscPowDivSucc n) =
      of ⟨ball 0 1, isOpen_ball⟩ (fun z ↦ z ^ n) (differentiableOn_pow n) := by
  apply Subtype.ext
  ext z
  rw [unitDiscPowDivSucc, deriv_of, of_apply, of_apply]
  have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [deriv_div_const, (hasDerivAt_pow (n + 1) (z : ℂ)).deriv,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hne]

/-- On the open unit disc, $f_n(z) = z^{n + 1} / (n + 1)$ converges to `0` in
`holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩`. -/
theorem tendsto_unitDiscPowDivSucc :
    Tendsto unitDiscPowDivSucc atTop (𝓝 0) := by
  rw [tendsto_iff_tendstoLocallyUniformlyOn]
  refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hle : ‖z ^ (n + 1) / (n + 1 : ℂ)‖ ≤ 1 / ((n : ℝ) + 1) := by
    rw [norm_div, norm_pow, hnorm]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz1) (by positivity)
  simpa only [extend_apply _ ⟨z, hz⟩, Subalgebra.coe_zero, ContinuousMap.zero_apply,
    unitDiscPowDivSucc_apply, dist_zero_left] using hle.trans_lt hn

/-- On the open unit disc, the derivatives $f_n'(z) = z^n$ also converge to `0` in the compact-open
topology. -/
theorem tendsto_deriv_unitDiscPowDivSucc :
    Tendsto (fun n ↦ deriv (unitDiscPowDivSucc n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, map_zero] using
    (deriv.continuous.tendsto 0).comp tendsto_unitDiscPowDivSucc

/-- Over the whole open unit disc, the supremum of $|f_n'(z)| = |z^n|$ is `1` for every `n : ℕ`. -/
theorem iSup_norm_deriv_unitDiscPowDivSucc (n : ℕ) :
    (⨆ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
      ‖(deriv (unitDiscPowDivSucc n)).val z‖) = 1 := by
  have hval : ∀ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
      ‖(deriv (unitDiscPowDivSucc n)).val z‖ = ‖(z : ℂ)‖ ^ n := by
    intro z
    rw [deriv_unitDiscPowDivSucc, of_apply, norm_pow]
  simp_rw [hval]
  have hbdd : BddAbove (range fun z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ↦ ‖(z : ℂ)‖ ^ n) :=
    ⟨1, by rintro _ ⟨z, rfl⟩; exact pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.2).le⟩
  refine le_antisymm ?_ ?_
  · have : Nonempty (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) := ⟨⟨0, mem_ball_self one_pos⟩⟩
    exact ciSup_le fun z ↦ pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.2).le
  · have hr_tend : Tendsto (fun k : ℕ ↦ (1 - 1 / ((k : ℝ) + 2)) ^ n) atTop (𝓝 1) := by
      have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
        refine ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (tendsto_add_atTop_nat 1)).congr fun k ↦ ?_
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
        ring
      simpa only [sub_zero, one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).pow n
    refine le_of_tendsto hr_tend (Eventually.of_forall fun k ↦ ?_)
    have hkpos : (0 : ℝ) < 1 - 1 / ((k : ℝ) + 2) := by
      have : 1 / ((k : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    have hklt : 1 - 1 / ((k : ℝ) + 2) < 1 := sub_lt_self 1 (by positivity)
    have hmem : ((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_of_nonneg hkpos.le]
      exact hklt
    let zk : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) := ⟨_, hmem⟩
    have hzk : ‖(zk : ℂ)‖ ^ n = (1 - 1 / ((k : ℝ) + 2)) ^ n := by
      change ‖((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ)‖ ^ n = _
      rw [Complex.norm_of_nonneg hkpos.le]
    exact hzk ▸ le_ciSup hbdd zk

/-- Over the whole open unit disc, the supremum of $|f_n(z)| = |z^{n + 1} / (n + 1)|$ is
`1 / (n + 1)`. -/
theorem iSup_norm_unitDiscPowDivSucc (n : ℕ) :
    (⨆ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
      ‖(unitDiscPowDivSucc n).val z‖) = 1 / ((n : ℝ) + 1) := by
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  have hval : ∀ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
      ‖(unitDiscPowDivSucc n).val z‖ =
        ‖(deriv (unitDiscPowDivSucc (n + 1))).val z‖ / ((n : ℝ) + 1) := by
    intro z
    rw [unitDiscPowDivSucc_apply, deriv_unitDiscPowDivSucc, of_apply, norm_div, hnorm]
  simp_rw [hval]
  have : Nonempty (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) := ⟨⟨0, mem_ball_self one_pos⟩⟩
  have hbdd : BddAbove (range fun z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ↦
      ‖(deriv (unitDiscPowDivSucc (n + 1))).val z‖ / ((n : ℝ) + 1)) :=
    ⟨1 / ((n : ℝ) + 1), by
      rintro _ ⟨z, rfl⟩
      dsimp only
      rw [deriv_unitDiscPowDivSucc, of_apply, norm_pow]
      exact div_le_div_of_nonneg_right
        (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.2).le) (by positivity)⟩
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun z ↦ div_le_div_of_nonneg_right ?_ (by positivity)
    rw [deriv_unitDiscPowDivSucc, of_apply, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.2).le
  · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc 1 / ((n : ℝ) + 1)
        = (⨆ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
            ‖(deriv (unitDiscPowDivSucc (n + 1))).val z‖) / ((n : ℝ) + 1) := by
          rw [iSup_norm_deriv_unitDiscPowDivSucc]
      _ ≤ _ := by
          rw [div_le_iff₀ hpos]
          refine ciSup_le fun z ↦ ?_
          exact (div_le_iff₀ hpos).mp (le_ciSup hbdd z)

/-- **Differentiation is unbounded for the global supremum norm on the open unit disc.** No
constant `C : ℝ` bounds `⨆ z, ‖(deriv f).val z‖` by `C * (⨆ z, ‖f.val z‖)` across all
`f : holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩` (or even across bounded polynomials). -/
theorem not_exists_iSup_norm_deriv_le_mul_unitDisc :
    ¬ ∃ C : ℝ, ∀ f : holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩,
      (⨆ z, ‖(deriv f).val z‖) ≤ C * (⨆ z, ‖f.val z‖) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  have hbound := hC (unitDiscPowDivSucc n)
  rw [iSup_norm_deriv_unitDiscPowDivSucc, iSup_norm_unitDiscPowDivSucc] at hbound
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hCle : C * (1 / ((n : ℝ) + 1)) ≤ max C 0 / ((n : ℝ) + 1) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (le_max_left C 0) hpos.le
  have hlt : max C 0 / ((n : ℝ) + 1) < 1 :=
    (div_lt_one hpos).mpr (hn.trans (lt_add_one (n : ℝ)))
  linarith

end UnitDiscCheck

end HolomorphicFunctions

end TauCeti
