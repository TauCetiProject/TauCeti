/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.Semigroups.Group.PhaseShift
import TauCeti.Analysis.Bochner.CharFun.Bochner
import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener

/-!
# Continuous-time mean ergodic projection and spectral atomic mass

For a complex-linear strongly continuous group `U` on a complex normed space `X`, the common fixed
subspace `{x | ∀ t : ℝ, U t x = x}` (`fixedSubmodule`) and the common eigenspace
`{x | ∀ t : ℝ, U t x = exp (ω * t * I) • x}` (`eigenspace`) at any angular frequency `ω : ℝ` are
closed complex submodules; `eigenspace` at `ω` is the fixed subspace of the phase shift
`U.phaseShift hU ω`.

When `U` is a unitary C₀-group on a complete complex Hilbert space `H`, the continuous-time
von Neumann mean ergodic theorem holds without separability: the time averages
`T⁻¹ • ∫ t in (0 : ℝ)..T, U t v` converge in norm as `T → ∞` to the orthogonal projection of `v`
onto the common fixed subspace (`IsUnitary.tendsto_average_starProjection`), and the twisted
averages `T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) • U t v` converge in norm to the orthogonal
projection onto the common eigenspace at `ω` (`IsUnitary.tendsto_twistedAverage_starProjection`).

Furthermore, for each vector `v`, the correlation function `t ↦ ⟪v, U t v⟫_ℂ` is continuous and
positive definite (`IsUnitary.isPositiveDefiniteSub_inner`), so Bochner's theorem supplies a unique
finite Borel spectral measure `σ` on `ℝ` with `⟪v, U t v⟫_ℂ = charFun σ t`
(`IsUnitary.existsUnique_spectralMeasure`). Combining the twisted mean ergodic theorem with
atomic-mass inversion for characteristic functions identifies the squared norm of the
eigenprojection as the spectral atomic mass `σ.real {ω}`
(`IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`).

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.fixedSubmodule`: the closed complex submodule of
  vectors fixed by `U t` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace`: the closed complex submodule of vectors
  satisfying `U t x = exp (ω * t * I) • x` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_starProjection`:
  continuous-time von Neumann mean ergodic theorem for unitary C₀-groups.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_twistedAverage_starProjection`:
  twisted continuous-time mean ergodic projection onto `eigenspace`.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isPositiveDefiniteSub_inner` and
  `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.existsUnique_spectralMeasure`: positive
  definiteness of `t ↦ ⟪v, U t v⟫_ℂ` and existence and uniqueness of its Bochner spectral measure.
* `IsUnitary.norm_starProjection_eigenspace_sq_eq_measureReal_singleton`:
  `‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω}`.

## References

* J. von Neumann, *Proof of the quasi-ergodic hypothesis*, Proc. Natl. Acad. Sci. USA 18 (1932),
  70–82.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section V.4 (mean ergodic semigroups).
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

/-! ## Common fixed subspace and eigenspaces -/

section FixedAndEigenspace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The complex submodule of vectors fixed by every operator `U t` of a complex-linear C₀-group. -/
def fixedSubmodule (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    Submodule ℂ X where
  carrier := {x : X | ∀ t : ℝ, U t x = x}
  zero_mem' t := _root_.map_zero (U t)
  add_mem' {x y} hx hy t := by
    rw [_root_.map_add, hx t, hy t]
  smul_mem' c {x} hx t := by
    rw [U.map_smul_of_isComplexLinear hU, hx t]

/-- Membership in `fixedSubmodule` means being fixed by `U t` at every real time `t`. -/
@[simp]
theorem mem_fixedSubmodule_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (x : X) :
    x ∈ U.fixedSubmodule hU ↔ ∀ t : ℝ, U t x = x :=
  Iff.rfl

/-- The underlying set of `fixedSubmodule` is `{x | ∀ t : ℝ, U t x = x}`. -/
theorem coe_fixedSubmodule (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    (U.fixedSubmodule hU : Set X) = {x : X | ∀ t : ℝ, U t x = x} :=
  (rfl)

/-- The common fixed subspace of a complex-linear C₀-group is closed. -/
theorem isClosed_fixedSubmodule (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    IsClosed (U.fixedSubmodule hU : Set X) := by
  have hcar : (U.fixedSubmodule hU : Set X) = ⋂ t : ℝ, {x : X | U t x = x} := by
    ext x
    simp
  rw [hcar]
  exact isClosed_iInter fun t ↦ isClosed_eq (U t).continuous continuous_id

/-- The common eigenspace at angular frequency `ω : ℝ` of a complex-linear C₀-group: the complex
submodule of vectors satisfying `U t x = exp (ω * t * I) • x` for every `t : ℝ`. -/
def eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    Submodule ℂ X where
  carrier := {x : X | ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x}
  zero_mem' t := by simp
  add_mem' {x y} hx hy t := by
    rw [_root_.map_add, hx t, hy t, smul_add]
  smul_mem' c {x} hx t := by
    rw [U.map_smul_of_isComplexLinear hU, hx t, smul_comm]

/-- Membership in `eigenspace` at frequency `ω` means `U t x = exp (ω * t * I) • x` for every
`t : ℝ`. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) (x : X) :
    x ∈ U.eigenspace hU ω ↔ ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x :=
  Iff.rfl

/-- The underlying set of `eigenspace` at `ω` is `{x | ∀ t : ℝ, U t x = exp (ω * t * I) • x}`. -/
theorem coe_eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    (U.eigenspace hU ω : Set X) = {x : X | ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x} :=
  (rfl)

/-- The common eigenspace at frequency `ω` is the common fixed subspace of the phase-shifted group
`U.phaseShift hU ω`. -/
theorem eigenspace_eq_fixedSubmodule_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    U.eigenspace hU ω =
      (U.phaseShift hU ω).fixedSubmodule (U.isComplexLinear_phaseShift hU ω) := by
  ext x
  simp only [mem_eigenspace_iff, mem_fixedSubmodule_iff, phaseShift_apply_apply]
  refine forall_congr' fun t ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, smul_smul, ← Complex.exp_add]
    have hexp : -(ω * t : ℂ) * Complex.I + ω * t * Complex.I = 0 := by ring
    rw [hexp, Complex.exp_zero, one_smul]
  · calc U t x = Complex.exp ((ω * t : ℂ) * Complex.I) •
            (Complex.exp (-(ω * t : ℂ) * Complex.I) • U t x) := by
          rw [smul_smul, ← Complex.exp_add]
          have hexp : (ω * t : ℂ) * Complex.I + -(ω * t : ℂ) * Complex.I = 0 := by ring
          rw [hexp, Complex.exp_zero, one_smul]
      _ = Complex.exp (ω * t * Complex.I) • x := by rw [h]

/-- The common eigenspace at frequency `0` is the common fixed subspace. -/
@[simp]
theorem eigenspace_zero (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    U.eigenspace hU 0 = U.fixedSubmodule hU := by
  ext x
  simp

/-- The common eigenspace at any angular frequency `ω` is closed. -/
theorem isClosed_eigenspace (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    IsClosed (U.eigenspace hU ω : Set X) := by
  rw [eigenspace_eq_fixedSubmodule_phaseShift]
  exact isClosed_fixedSubmodule _ _

end FixedAndEigenspace

/-! ## Continuous-time mean ergodic projection for unitary C₀-groups -/

section MeanErgodic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The common fixed subspace of a complex-linear C₀-group on a complete complex Hilbert space
admits an orthogonal projection. -/
instance hasOrthogonalProjection_fixedSubmodule [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) : (U.fixedSubmodule hU).HasOrthogonalProjection :=
  have := (U.isClosed_fixedSubmodule hU).completeSpace_coe
  inferInstance

/-- The common eigenspace at frequency `ω` of a complex-linear C₀-group on a complete complex
Hilbert space admits an orthogonal projection. -/
instance hasOrthogonalProjection_eigenspace [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.eigenspace hU ω).HasOrthogonalProjection :=
  have := (U.isClosed_eigenspace hU ω).completeSpace_coe
  inferInstance

namespace IsUnitary

variable {U : StronglyContinuousGroup H}

/-- The orthogonal complement of the coboundary span `{U s x - x}` is the common fixed subspace. -/
private theorem orthogonal_span_coboundaries (hU : U.IsUnitary) :
    (Submodule.span ℂ {y : H | ∃ (s : ℝ) (x : H), y = U s x - x})ᗮ =
      U.fixedSubmodule hU.isComplexLinear := by
  ext u
  rw [Submodule.mem_orthogonal, mem_fixedSubmodule_iff]
  constructor
  · intro hu t
    have hperp : ∀ x : H, ⟪x, U t u - u⟫_ℂ = 0 := fun x ↦ by
      have hmem : U (-t) x - x ∈ Submodule.span ℂ {y : H | ∃ (s : ℝ) (x : H), y = U s x - x} :=
        Submodule.subset_span ⟨-t, x, rfl⟩
      have h0 := hu _ hmem
      calc ⟪x, U t u - u⟫_ℂ
          = ⟪x, U t u⟫_ℂ - ⟪x, u⟫_ℂ := inner_sub_right _ _ _
        _ = ⟪U (-t) x, U (-t) (U t u)⟫_ℂ - ⟪x, u⟫_ℂ := by rw [hU.inner_map_map]
        _ = ⟪U (-t) x, u⟫_ℂ - ⟪x, u⟫_ℂ := by rw [U.map_neg_apply_map_apply]
        _ = ⟪U (-t) x - x, u⟫_ℂ := (inner_sub_left _ _ _).symm
        _ = 0 := h0
    have hself := hperp (U t u - u)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)
  · intro hu y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨s, x, rfl⟩
      rw [inner_sub_left, ← hu s, hU.inner_map_map, hu s, sub_self]
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
    | smul c y₁ _ h₁ => rw [inner_smul_left, h₁, mul_zero]

/-- Averaging an orbit of a unitary C₀-group over `[0, T]` is a contraction for `T > 0`. -/
private theorem norm_average_le (hU : U.IsUnitary) {T : ℝ} (hT : 0 < T) (v : H) :
    ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) T, ‖U t v‖ ≤ ‖v‖ := fun t _ ↦ (hU.norm_map t v).le
  calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, U t v‖
      ≤ T⁻¹ * (‖v‖ * |T - 0|) := by
        gcongr
        exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ‖v‖ := by
        rw [sub_zero, abs_of_pos hT]
        field_simp

/-- Time averages of a coboundary `U s x - x` vanish as `T → ∞`. -/
private theorem tendsto_average_sub_apply (hU : U.IsUnitary) (s : ℝ) (x : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s x - x)) atTop (𝓝 0) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun t : ℝ ↦ U t x) volume a b :=
    (U.continuous_orbit x).intervalIntegrable a b
  have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ * (2 * (‖x‖ * |s|))) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const (2 * (‖x‖ * |s|))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hsub : ∫ t in (0 : ℝ)..T, U t (U s x - x) =
      (∫ t in T..(T + s), U t x) - ∫ t in (0 : ℝ)..s, U t x := by
    have hsplit : (fun t : ℝ ↦ U t (U s x - x)) = fun t : ℝ ↦ U (t + s) x - U t x := by
      funext t
      rw [map_sub, U.map_add_apply]
    have hshift : ∫ t in (0 : ℝ)..T, U (t + s) x = ∫ t in s..(T + s), U t x := by
      rw [intervalIntegral.integral_comp_add_right (a := 0) (b := T) (f := fun t : ℝ ↦ U t x) s,
        zero_add]
    have hint_shift : IntervalIntegrable (fun t : ℝ ↦ U (t + s) x) volume 0 T :=
      ((U.continuous_orbit x).comp (continuous_id.add continuous_const)).intervalIntegrable 0 T
    have hadj₁ := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (T + s))
    have hadj₂ := intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T (T + s))
    rw [hsplit, intervalIntegral.integral_sub hint_shift (hint 0 T), hshift]
    exact sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm, hadj₁, ← hadj₂, add_comm])
  rw [hsub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  gcongr
  have h1 : ‖∫ t in T..(T + s), U t x‖ ≤ ‖x‖ * |s| := by
    simpa [add_sub_cancel_left] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := T + s)
        (f := fun t : ℝ ↦ U t x) (C := ‖x‖) fun t _ ↦ (hU.norm_map t x).le
  have h2 : ‖∫ t in (0 : ℝ)..s, U t x‖ ≤ ‖x‖ * |s| := by
    simpa [sub_zero] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
        (f := fun t : ℝ ↦ U t x) (C := ‖x‖) fun t _ ↦ (hU.norm_map t x).le
  calc ‖(∫ t in T..(T + s), U t x) - ∫ t in (0 : ℝ)..s, U t x‖
      ≤ ‖∫ t in T..(T + s), U t x‖ + ‖∫ t in (0 : ℝ)..s, U t x‖ := norm_sub_le _ _
    _ ≤ 2 * (‖x‖ * |s|) := by linarith

/-- Time averages vanish on the orthogonal complement of the common fixed subspace. -/
private theorem tendsto_average_of_mem_orthogonal [CompleteSpace H] (hU : U.IsUnitary) {z : H}
    (hz : z ∈ (U.fixedSubmodule hU.isComplexLinear)ᗮ) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t z) atTop (𝓝 0) := by
  let N : Submodule ℂ H := Submodule.span ℂ {y : H | ∃ (s : ℝ) (x : H), y = U s x - x}
  have hN : ∀ y ∈ N, Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t y) atTop (𝓝 0) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      rcases hw with ⟨s, x, rfl⟩
      exact hU.tendsto_average_sub_apply s x
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ =>
      have hadd (T : ℝ) : T⁻¹ • ∫ t in (0 : ℝ)..T, U t (y₁ + y₂) =
          (T⁻¹ • ∫ t in (0 : ℝ)..T, U t y₁) + T⁻¹ • ∫ t in (0 : ℝ)..T, U t y₂ := by
        simp only [_root_.map_add, intervalIntegral.integral_add
          ((U.continuous_orbit y₁).intervalIntegrable 0 T)
          ((U.continuous_orbit y₂).intervalIntegrable 0 T), smul_add]
      simpa only [hadd, add_zero] using h₁.add h₂
    | smul c y₁ _ h₁ =>
      have hsmul (T : ℝ) : T⁻¹ • ∫ t in (0 : ℝ)..T, U t (c • y₁) =
          c • (T⁻¹ • ∫ t in (0 : ℝ)..T, U t y₁) := by
        simp only [hU.map_smul, intervalIntegral.integral_smul, smul_comm T⁻¹ c]
      simpa only [hsmul, smul_zero] using h₁.const_smul c
  have hclos : z ∈ closure (N : Set H) := by
    rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe,
      ← Submodule.orthogonal_orthogonal_eq_closure, hU.orthogonal_span_coboundaries]
    exact hz
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hyN, hyz⟩ := Metric.mem_closure_iff.mp hclos (ε / 2) (half_pos hε)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp (hN y hyN) (ε / 2) (half_pos hε)
  refine ⟨max T₀ 1, fun T hT ↦ ?_⟩
  have hTpos : 0 < T := one_pos.trans_le (le_of_max_le_right hT)
  have hdiff : T⁻¹ • ∫ t in (0 : ℝ)..T, U t z =
      (T⁻¹ • ∫ t in (0 : ℝ)..T, U t (z - y)) + T⁻¹ • ∫ t in (0 : ℝ)..T, U t y := by
    have hsplit : (fun t : ℝ ↦ U t z) = fun t : ℝ ↦ U t (z - y) + U t y := by
      funext t
      rw [← _root_.map_add, sub_add_cancel]
    rw [hsplit, intervalIntegral.integral_add
      ((U.continuous_orbit (z - y)).intervalIntegrable 0 T)
      ((U.continuous_orbit y).intervalIntegrable 0 T), smul_add]
  rw [dist_zero_right, hdiff]
  have h1 := hU.norm_average_le hTpos (z - y)
  have h2 := hT₀ T (le_of_max_le_left hT)
  rw [dist_eq_norm] at hyz
  rw [dist_zero_right] at h2
  calc ‖(T⁻¹ • ∫ t in (0 : ℝ)..T, U t (z - y)) + T⁻¹ • ∫ t in (0 : ℝ)..T, U t y‖
      ≤ ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t (z - y)‖ + ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t y‖ :=
        norm_add_le _ _
    _ < ε := by linarith

/-- **Continuous-time von Neumann mean ergodic theorem.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H` and any `v : H`, the time averages `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`
converge in norm as `T → ∞` to the orthogonal projection of `v` onto the common fixed subspace
`U.fixedSubmodule hU.isComplexLinear`. -/
theorem tendsto_average_starProjection [CompleteSpace H] (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 ((U.fixedSubmodule hU.isComplexLinear).starProjection v)) := by
  set w : H := (U.fixedSubmodule hU.isComplexLinear).starProjection v
  have hw_mem : w ∈ U.fixedSubmodule hU.isComplexLinear := Submodule.starProjection_apply_mem _ v
  have hw_lim : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t w) atTop (𝓝 w) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hconst : (fun t : ℝ ↦ U t w) = fun _ ↦ w := funext fun t ↦ hw_mem t
    rw [hconst, intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ hT.ne',
      one_smul]
  have hperp_lim : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t (v - w)) atTop (𝓝 0) :=
    hU.tendsto_average_of_mem_orthogonal (Submodule.sub_starProjection_mem_orthogonal v)
  have hsum (T : ℝ) : T⁻¹ • ∫ t in (0 : ℝ)..T, U t v =
      (T⁻¹ • ∫ t in (0 : ℝ)..T, U t w) + T⁻¹ • ∫ t in (0 : ℝ)..T, U t (v - w) := by
    have hsplit : (fun t : ℝ ↦ U t v) = fun t : ℝ ↦ U t w + U t (v - w) := by
      funext t
      rw [← _root_.map_add, add_sub_cancel]
    rw [hsplit, intervalIntegral.integral_add
      ((U.continuous_orbit w).intervalIntegrable 0 T)
      ((U.continuous_orbit (v - w)).intervalIntegrable 0 T), smul_add]
  simpa only [hsum, add_zero] using hw_lim.add hperp_lim

/-- **Twisted continuous-time mean ergodic projection.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H`, an angular frequency `ω : ℝ`, and `v : H`, the twisted averages
`T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) • U t v` converge in norm as `T → ∞` to the orthogonal
projection of `v` onto the common eigenspace `U.eigenspace hU.isComplexLinear ω`. -/
theorem tendsto_twistedAverage_starProjection [CompleteSpace H] (hU : U.IsUnitary) (ω : ℝ) (v : H) :
    Tendsto (fun T : ℝ ↦
        T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v)
      atTop (𝓝 ((U.eigenspace hU.isComplexLinear ω).starProjection v)) := by
  have h := (hU.phaseShift ω).tendsto_average_starProjection v
  have hproj : ((U.phaseShift hU.isComplexLinear ω).fixedSubmodule
      (hU.phaseShift ω).isComplexLinear).starProjection v =
      (U.eigenspace hU.isComplexLinear ω).starProjection v := by
    have heq := (U.eigenspace_eq_fixedSubmodule_phaseShift hU.isComplexLinear ω).symm
    refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
    · rw [← heq]
      exact Submodule.starProjection_apply_mem _ v
    · rw [← heq]
      exact Submodule.sub_starProjection_mem_orthogonal v
  rw [hproj] at h
  refine h.congr fun T ↦ ?_
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [phaseShift_apply_apply]
  congr 2
  ring

/-! ## Spectral measure and atomic-mass identity -/

/-- The correlation function `t ↦ ⟪v, U t v⟫_ℂ` of a unitary C₀-group is positive definite. -/
theorem isPositiveDefiniteSub_inner (hU : U.IsUnitary) (v : H) :
    TauCeti.IsPositiveDefiniteSub fun t : ℝ ↦ ⟪v, U t v⟫_ℂ := by
  refine TauCeti.IsPositiveDefiniteSub.of_posSemidef ?_
  have hgram : (fun a b : ℝ ↦ ⟪v, U (a - b) v⟫_ℂ) =
      Matrix.gram ℂ (fun t : ℝ ↦ U (-t) v) := by
    ext a b
    rw [Matrix.gram_apply]
    calc ⟪v, U (a - b) v⟫_ℂ
        = ⟪U (-a) v, U (-a) (U (a - b) v)⟫_ℂ := (hU.inner_map_map (-a) _ _).symm
      _ = ⟪U (-a) v, U (-b) v⟫_ℂ := by
          rw [← U.map_add_apply, ← add_sub_assoc, neg_add_cancel, zero_sub]
  rw [hgram]
  exact TauCeti.posSemidef_gram ℂ (fun t : ℝ ↦ U (-t) v)

/-- **Spectral measure of a unitary C₀-group.** For every vector `v` in a complex inner product
space and every unitary C₀-group `U`, there is a unique finite Borel measure `σ` on `ℝ` whose
characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem existsUnique_spectralMeasure (hU : U.IsUnitary) (v : H) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have hboch := (TauCeti.bochner_charFun fun t : ℝ ↦ ⟪v, U t v⟫_ℂ).mp
    ⟨continuous_const.inner (U.continuous_orbit v), hU.isPositiveDefiniteSub_inner v⟩
  simpa only [funext_iff, eq_comm (a := ⟪v, U _ v⟫_ℂ)] using hboch

/-- **Spectral atomic-mass identity.** For a unitary C₀-group `U` on a complete complex Hilbert
space `H`, an angular frequency `ω : ℝ`, a vector `v : H`, and any finite Borel measure `σ` on `ℝ`
representing `t ↦ ⟪v, U t v⟫_ℂ` as `charFun σ`, the squared norm of the orthogonal projection of
`v` onto `U.eigenspace hU.isComplexLinear ω` equals `σ.real {ω}`. -/
theorem norm_starProjection_eigenspace_sq_eq_measureReal_singleton [CompleteSpace H]
    (hU : U.IsUnitary) (ω : ℝ) (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω} := by
  set P := (U.eigenspace hU.isComplexLinear ω).starProjection
  have hlim₁ : Tendsto (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ)
      atTop (𝓝 ⟪v, P v⟫_ℂ) :=
    ((innerSL ℂ v).continuous.continuousAt.tendsto).comp
      (hU.tendsto_twistedAverage_starProjection ω v)
  have hlim₂ : Tendsto (fun T : ℝ ↦
      (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t)
      atTop (𝓝 (σ.real {ω} : ℂ)) :=
    MeasureTheory.tendsto_average_exp_mul_charFun σ ω
  have hfun : (fun T : ℝ ↦
      ⟪v, T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ) =
      fun T : ℝ ↦
        (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) * charFun σ t := by
    funext T
    have hint : IntervalIntegrable
        (fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I)) • U t v) volume 0 T :=
      ((by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (-(ω * t * Complex.I))).smul
        (U.continuous_orbit v)).intervalIntegrable 0 T
    rw [inner_smul_right_eq_smul, Complex.real_smul, Complex.ofReal_inv]
    congr 1
    have hcomm := (innerSL ℂ v).intervalIntegral_comp_comm hint
    simpa only [innerSL_apply_apply, inner_smul_right, hσ] using hcomm.symm
  rw [hfun] at hlim₁
  have heq : ⟪v, P v⟫_ℂ = (σ.real {ω} : ℂ) := tendsto_nhds_unique hlim₁ hlim₂
  have hinner : ⟪v, P v⟫_ℂ = ⟪P v, P v⟫_ℂ := by
    calc ⟪v, P v⟫_ℂ = ⟪(v - P v) + P v, P v⟫_ℂ := by rw [sub_add_cancel]
      _ = ⟪v - P v, P v⟫_ℂ + ⟪P v, P v⟫_ℂ := inner_add_left _ _ _
      _ = ⟪P v, P v⟫_ℂ := by
          rw [Submodule.starProjection_inner_eq_zero v (P v)
            (Submodule.starProjection_apply_mem _ v), zero_add]
  have hre := congrArg Complex.re (hinner.symm.trans heq)
  simpa only [← inner_self_eq_norm_sq (𝕜 := ℂ), RCLike.re_to_complex, Complex.ofReal_re]
    using hre

end IsUnitary

end MeanErgodic

end TauCeti.Semigroups.StronglyContinuousGroup

end
