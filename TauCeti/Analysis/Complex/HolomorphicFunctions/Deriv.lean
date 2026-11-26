/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic

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

* the continuous linear derivative `HolomorphicFunctions.deriv`, its Leibniz rule `deriv_mul`, its
  bundling `HolomorphicFunctions.derivation` as a `ℂ`-derivation, and compatibility with open
  restriction (`restrict_deriv`);
* Cauchy derivative estimates on closed discs (`norm_extend_deriv_le_of_closedBall_subset`) and
  closed thickenings (`norm_extend_deriv_le_of_cthickening_subset`,
  `norm_restrictContinuousMap_deriv_le`, `norm_restrictContinuousMap_deriv_sub_le`);
* agreement of `deriv^[k]` with `iteratedDeriv k` (`iterate_deriv_apply`,
  `extend_iterate_deriv_of_mem`);
* the unit-disc sequence $f_n(z) = z^{n + 1} / (n + 1)$, which tends to `0` in
  `holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩` together with its derivatives $f_n'(z) = z^n$,
  even though $\sup_{|z| < 1} |f_n(z)| = 1 / (n + 1)$ while $\sup_{|z| < 1} |f_n'(z)| = 1$, showing
  that differentiation is unbounded for the global supremum norm across holomorphic functions on
  `ball 0 1` with bounded values and bounded derivative
  (`not_exists_iSup_norm_deriv_le_mul_unitDisc`).

## References

* Armin Rainer, *Advanced Complex Analysis*, §11, Exercise 20.
* Walter Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.28.
-/

public noncomputable section

open Filter Function Metric Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

section Deriv

variable {U V : Opens ℂ}

private def derivFun (f : holomorphicFunctions U) : holomorphicFunctions U :=
  of U (_root_.deriv (extend f)) ((differentiableOn_extend f).deriv U.isOpen)

private theorem derivFun_add (f g : holomorphicFunctions U) :
    derivFun (f + g) = derivFun f + derivFun g := by
  apply Subtype.ext
  ext z
  have heq : extend (f + g) =ᶠ[𝓝 (z : ℂ)] extend f + extend g := by
    filter_upwards [U.isOpen.mem_nhds z.property] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [derivFun, Subalgebra.coe_add, ContinuousMap.add_apply, of_apply]
  rw [heq.deriv_eq, deriv_add
    ((differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds z.property))
    ((differentiableOn_extend g).differentiableAt (U.isOpen.mem_nhds z.property))]

private theorem derivFun_smul (c : ℂ) (f : holomorphicFunctions U) :
    derivFun (c • f) = c • derivFun f := by
  apply Subtype.ext
  ext z
  have heq : extend (c • f) =ᶠ[𝓝 (z : ℂ)] c • extend f := by
    filter_upwards [U.isOpen.mem_nhds z.property] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [derivFun, SetLike.val_smul, ContinuousMap.smul_apply, of_apply]
  rw [heq.deriv_eq, deriv_const_smul c
    ((differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds z.property))]

private theorem continuous_derivFun : Continuous (derivFun (U := U)) := by
  refine continuous_iff_continuousAt.mpr fun f ↦ ?_
  rw [ContinuousAt, tendsto_iff_tendstoLocallyUniformlyOn]
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
  filter_upwards [U.isOpen.mem_nhds z.property] with w hw
  exact (extend_apply (of U g hg) ⟨w, hw⟩).trans (of_apply g hg ⟨w, hw⟩)

/-- Leibniz product rule for `HolomorphicFunctions.deriv`. -/
theorem deriv_mul (f g : holomorphicFunctions U) :
    deriv (f * g) = f * deriv g + g * deriv f := by
  apply Subtype.ext
  ext z
  have heq : extend (f * g) =ᶠ[𝓝 (z : ℂ)] extend f * extend g := by
    filter_upwards [U.isOpen.mem_nhds z.property] with w hw
    simp [extend_apply _ ⟨w, hw⟩]
  simp only [deriv_apply, Subalgebra.coe_add, Subalgebra.coe_mul, ContinuousMap.add_apply,
    ContinuousMap.mul_apply]
  rw [heq.deriv_eq, _root_.deriv_mul
    ((differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds z.property))
    ((differentiableOn_extend g).differentiableAt (U.isOpen.mem_nhds z.property)),
    extend_apply, extend_apply]
  ring

/-- Complex differentiation on `holomorphicFunctions U` bundled as a `ℂ`-derivation. -/
def derivation : Derivation ℂ (holomorphicFunctions U) (holomorphicFunctions U) where
  toLinearMap := deriv.toLinearMap
  map_one_eq_zero' := (add_eq_left (a := deriv (1 : holomorphicFunctions U))).mp <| by
    simpa only [ContinuousLinearMap.coe_coe, one_mul] using
      (deriv_mul (1 : holomorphicFunctions U) 1).symm
  leibniz' f g := by simp only [smul_eq_mul, ContinuousLinearMap.coe_coe, deriv_mul]

/-- Coercing `derivation` to a function recovers `deriv`. -/
@[simp]
theorem coe_derivation : ⇑(derivation (U := U)) = ⇑(deriv (U := U)) := (rfl)

/-- Underlying linear map of `derivation`. -/
@[simp]
theorem toLinearMap_derivation :
    (derivation (U := U)).toLinearMap = (deriv (U := U)).toLinearMap := (rfl)

/-- Applying `derivation` agrees with `deriv`. -/
theorem derivation_apply (f : holomorphicFunctions U) : derivation f = deriv f := (rfl)

/-- Constant holomorphic functions have derivative `0`. -/
@[simp]
theorem deriv_algebraMap (c : ℂ) : deriv (algebraMap ℂ (holomorphicFunctions U) c) = 0 := by
  rw [← coe_derivation]
  exact derivation.map_algebraMap c

/-- The multiplicative identity `1 : holomorphicFunctions U` has derivative `0`. -/
@[simp]
theorem deriv_one : deriv (1 : holomorphicFunctions U) = 0 := by
  rw [← coe_derivation]
  exact derivation.map_one_eq_zero

/-- Every natural-number cast `(n : holomorphicFunctions U)` has derivative `0`. -/
@[simp]
theorem deriv_natCast (n : ℕ) : deriv (n : holomorphicFunctions U) = 0 := by
  rw [← coe_derivation]
  exact derivation.map_natCast n

/-- Complex differentiation commutes with negation. -/
@[simp]
theorem deriv_neg (f : holomorphicFunctions U) : deriv (-f) = -deriv f := by
  rw [← coe_derivation]
  exact map_neg derivation f

/-- Complex differentiation commutes with subtraction. -/
@[simp]
theorem deriv_sub (f g : holomorphicFunctions U) :
    deriv (f - g) = deriv f - deriv g := by
  rw [← coe_derivation]
  exact map_sub derivation f g

/-- Every integer cast `(n : holomorphicFunctions U)` has derivative `0`. -/
@[simp]
theorem deriv_intCast (n : ℤ) : deriv (n : holomorphicFunctions U) = 0 := by
  rw [← coe_derivation, ← zsmul_one, derivation.map_smul_of_tower n,
    derivation.map_one_eq_zero, smul_zero]

/-- Every numeric literal `ofNat(n)` (`n ≥ 2`) in `holomorphicFunctions U` has derivative `0`. -/
@[simp]
theorem deriv_ofNat (n : ℕ) [n.AtLeastTwo] :
    deriv (ofNat(n) : holomorphicFunctions U) = 0 := by
  rw [← coe_derivation]
  exact derivation.map_natCast n

/-- Power rule for `HolomorphicFunctions.deriv`. -/
theorem deriv_pow (f : holomorphicFunctions U) (n : ℕ) :
    deriv (f ^ n) = n • (f ^ (n - 1) * deriv f) := by
  simpa only [coe_derivation, smul_eq_mul] using derivation.leibniz_pow f n

/-- Complex differentiation commutes with restriction to a smaller open domain. -/
@[simp]
theorem restrict_deriv (h : V ≤ U) (f : holomorphicFunctions U) :
    restrict h (deriv f) = deriv (restrict h f) := by
  apply Subtype.ext
  ext z
  symm
  simp only [restrict_apply, deriv_apply]
  apply EventuallyEq.deriv_eq
  filter_upwards [V.isOpen.mem_nhds z.property] with w hw
  simp only [extend_apply _ ⟨w, hw⟩, restrict_apply, extend_apply _ ⟨w, h hw⟩]

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

/-- Quantitative Cauchy bound on a compact subset `K ⊆ U` with `cthickening δ K ⊆ U`. -/
theorem norm_restrictContinuousMap_deriv_le {K : Set ℂ} [CompactSpace K] (hKU : K ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) (hδU : cthickening δ K ⊆ U) (f : holomorphicFunctions U) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ w ∈ cthickening δ K, ‖extend f w‖ ≤ M) :
    ‖restrictContinuousMap hKU (deriv f)‖ ≤ M / δ := by
  rw [ContinuousMap.norm_le _ (div_nonneg hM0 hδ.le)]
  intro z
  simpa only [restrictContinuousMap_apply_eq_extend] using
    norm_extend_deriv_le_of_cthickening_subset hδ hδU f hM z.property

/-- Quantitative Cauchy bound for differences of derivatives on a compact subset `K ⊆ U` with
`cthickening δ K ⊆ U`. -/
theorem norm_restrictContinuousMap_deriv_sub_le {K : Set ℂ} [CompactSpace K] (hKU : K ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) (hδU : cthickening δ K ⊆ U) (f g : holomorphicFunctions U) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ w ∈ cthickening δ K, ‖extend f w - extend g w‖ ≤ M) :
    ‖restrictContinuousMap hKU (deriv f) - restrictContinuousMap hKU (deriv g)‖ ≤ M / δ := by
  rw [← map_sub, ← deriv_sub]
  refine norm_restrictContinuousMap_deriv_le hKU hδ hδU (f - g) hM0 fun w hw ↦ ?_
  simpa only [extend_apply _ ⟨w, hδU hw⟩, Subalgebra.coe_sub, ContinuousMap.sub_apply] using
    hM w hw

end CauchyEstimates

section IteratedDeriv

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
    filter_upwards [U.isOpen.mem_nhds z.property] with w hw
    exact (extend_apply _ ⟨w, hw⟩).trans (ih f ⟨w, hw⟩)

/-- On `U`, the zero extension of `deriv^[k] f` agrees with `iteratedDeriv k (extend f)`. -/
@[simp]
theorem extend_iterate_deriv_of_mem (k : ℕ) (f : holomorphicFunctions U) {z : ℂ} (hz : z ∈ U) :
    extend (deriv^[k] f) z = iteratedDeriv k (extend f) z :=
  (extend_apply _ ⟨z, hz⟩).trans (iterate_deriv_apply k f ⟨z, hz⟩)

end IteratedDeriv

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
    ((deriv (U := ⟨ball 0 1, isOpen_ball⟩)).continuous.tendsto 0).comp
      tendsto_unitDiscPowDivSucc

private theorem bddAbove_range_norm_deriv_unitDiscPowDivSucc (n : ℕ) :
    BddAbove (range fun z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ↦
      ‖(deriv (unitDiscPowDivSucc n)).val z‖) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨z, rfl⟩
  dsimp only
  rw [deriv_unitDiscPowDivSucc, of_apply, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.property).le

private theorem bddAbove_range_norm_unitDiscPowDivSucc (n : ℕ) :
    BddAbove (range fun z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ↦
      ‖(unitDiscPowDivSucc n).val z‖) := by
  refine ⟨1 / ((n : ℝ) + 1), ?_⟩
  rintro _ ⟨z, rfl⟩
  dsimp only
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [unitDiscPowDivSucc_apply, norm_div, norm_pow, hnorm]
  exact div_le_div_of_nonneg_right
    (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.property).le) (by positivity)

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
    ⟨1, by
      rintro _ ⟨z, rfl⟩
      exact pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.property).le⟩
  refine le_antisymm ?_ ?_
  · have : Nonempty (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) := ⟨⟨0, mem_ball_self one_pos⟩⟩
    exact ciSup_le fun z ↦ pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp z.property).le
  · have hr_tend : Tendsto (fun k : ℕ ↦ (1 - 1 / ((k : ℝ) + 2)) ^ n) atTop (𝓝 1) := by
      have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
          (tendsto_add_atTop_iff_nat 1).mpr (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa only [sub_zero, one_pow] using ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).pow n
    refine le_of_tendsto hr_tend (Eventually.of_forall fun k ↦ ?_)
    have hkpos : (0 : ℝ) < 1 - 1 / ((k : ℝ) + 2) := by
      have : 1 / ((k : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      linarith
    have hklt : 1 - 1 / ((k : ℝ) + 2) < 1 := sub_lt_self 1 (by positivity)
    have hmem : ((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, Complex.norm_of_nonneg hkpos.le]
      exact hklt
    simpa only [Complex.norm_of_nonneg hkpos.le] using
      le_ciSup hbdd (⟨((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ), hmem⟩ :
        (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ))

/-- Over the whole open unit disc, the supremum of $|f_n(z)| = |z^{n + 1} / (n + 1)|$ is
`1 / (n + 1)`. -/
theorem iSup_norm_unitDiscPowDivSucc (n : ℕ) :
    (⨆ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
      ‖(unitDiscPowDivSucc n).val z‖) = 1 / ((n : ℝ) + 1) := by
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  have hval : ∀ z : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ),
      ‖(unitDiscPowDivSucc n).val z‖ =
        ‖(deriv (unitDiscPowDivSucc (n + 1))).val z‖ * ((n : ℝ) + 1)⁻¹ := by
    intro z
    rw [unitDiscPowDivSucc_apply, deriv_unitDiscPowDivSucc, of_apply, norm_div, hnorm,
      div_eq_mul_inv]
  simp_rw [hval, ← Real.iSup_mul_of_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n + 1)),
    iSup_norm_deriv_unitDiscPowDivSucc, one_mul, one_div]

/-- **Differentiation is unbounded for the global supremum norm on the open unit disc.** No
constant `C : ℝ` bounds `⨆ z, ‖(deriv f).val z‖` by `C * (⨆ z, ‖f.val z‖)` across all
`f : holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩` whose values and derivative values are bounded
on `ball 0 1`. -/
theorem not_exists_iSup_norm_deriv_le_mul_unitDisc :
    ¬ ∃ C : ℝ, ∀ f : holomorphicFunctions ⟨ball 0 1, isOpen_ball⟩,
      BddAbove (range fun z ↦ ‖f.val z‖) → BddAbove (range fun z ↦ ‖(deriv f).val z‖) →
        (⨆ z, ‖(deriv f).val z‖) ≤ C * (⨆ z, ‖f.val z‖) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  have hbound := hC (unitDiscPowDivSucc n) (bddAbove_range_norm_unitDiscPowDivSucc n)
    (bddAbove_range_norm_deriv_unitDiscPowDivSucc n)
  rw [iSup_norm_deriv_unitDiscPowDivSucc, iSup_norm_unitDiscPowDivSucc] at hbound
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hCle : C * (1 / ((n : ℝ) + 1)) ≤ max C 0 / ((n : ℝ) + 1) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (le_max_left C 0) hpos.le
  have hlt : max C 0 / ((n : ℝ) + 1) < 1 :=
    (div_lt_one hpos).mpr (hn.trans (lt_add_one (n : ℝ)))
  linarith

end UnitDiscCheck

end TauCeti.HolomorphicFunctions
