/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# The spectral measure of a self-adjoint partial linear map

Let `A` be a self-adjoint partial linear map on a complex Hilbert space `H`, and let `U` be its
Cayley transform `LinearPMap.cayley A`, the unitary operator `(A - i)(A + i)⁻¹`. The spectral
measure of `U` is a projection-valued measure on the spectrum of `U`, which lies on the unit
circle. The **spectral measure** `P_A = LinearPMap.spectralPVM A hA` of `A` is its pushforward to
the real line along the real inverse Cayley coordinate

`κ(w) = re (i (1 + w) / (1 - w))`,

so that `P_A(B) = P_U(κ⁻¹ B)` for every Borel set `B ⊆ ℝ`. At the pole `w = 1` the coordinate takes
the value `κ(1) = 0`, by the convention `x / 0 = 0`. This value is immaterial: `1` is not an
eigenvalue of `U`, so the spectral measure of `U` assigns no mass to `{1}`. At every other point `w`
of the spectrum of `U`, the inverse Cayley image `i (1 + w) / (1 - w)` lies in the spectrum of `A`,
which is real, so there `κ` is the inverse Cayley transform itself.

The spectral measure represents the resolvents of `A`. At a resolvent point `z` the resolvent is
the continuous function `(1 - w) / ((z - i) - (z + i) w)` of `U`
(`IsSelfAdjoint.resolvent_eq_cfc_cayley`), which is `(z - κ(w))⁻¹` away from `w = 1`. Its
diagonal matrix elements are therefore the Cauchy–Stieltjes transforms of the diagonal measures of
`P_A`: `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`.

The spectral projections commute with `U`, and so does every bounded Borel function of `P_A`.
Hence these operators intertwine `A` with itself: they preserve the domain of `A`, commute with `A`
on it, and commute with every resolvent of `A`. Moreover `P_A` lives on the spectrum of `A`: the
spectral projection of a Borel set of resolvent points vanishes.

Finally, spectral support controls the quadratic form of `A`. Every `x ∈ dom A` is `v - U v`,
and then `re ⟪A x, x⟫ = ∫ κ(w) ‖1 - w‖² dμ_v(w)` and `‖x‖² = ∫ ‖1 - w‖² dμ_v(w)` for the
diagonal measure `μ_v` of `U`. So if `P_A(B)` vanishes off `[β, ∞)`, then
`β ‖x‖² ≤ re ⟪A x, x⟫` for every `x ∈ dom A` in its range, and similarly for upper bounds. In
particular `P_A` vanishes on `(-∞, c)` exactly when `c ‖x‖² ≤ re ⟪A x, x⟫` on `dom A`: a nonzero
`P_A((-∞, c - ε])` would contain a nonzero vector `w - U w` of the domain violating this bound.

## Main declarations

* `LinearPMap.spectralPVM A hA`: the spectral measure of a self-adjoint partial linear map, a
  projection-valued measure on `ℝ`.
* `IsSelfAdjoint.diagMeasure_cayley_preimage_singleton_one_eq_zero`: the diagonal measures of the
  Cayley transform assign no mass to the point `1`.
* `IsSelfAdjoint.inner_resolvent_apply_eq_integral`: the resolvent formula
  `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`.
* `IsSelfAdjoint.intertwines_spectralPVM_integral`, `IsSelfAdjoint.intertwines_spectralPVM_proj`:
  bounded Borel functions of `P_A`, in particular spectral projections, preserve the domain of
  `A` and commute with `A` on it.
* `IsSelfAdjoint.commute_spectralPVM_integral_resolvent`,
  `IsSelfAdjoint.commute_spectralPVM_proj_resolvent`: they commute with the resolvents.
* `IsSelfAdjoint.spectralPVM_proj_eq_zero_of_forall_mem_resolventSet`: the spectral projection of
  a Borel set of resolvent points vanishes.
* `IsSelfAdjoint.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj`,
  `IsSelfAdjoint.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj`: form bounds on a
  spectral range.
* `IsSelfAdjoint.spectralPVM_proj_Iio_eq_zero_iff`,
  `IsSelfAdjoint.spectralPVM_proj_Ioi_eq_zero_iff`: the spectral measure vanishes on a half-line
  exactly when the corresponding form bound holds.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Section VIII.3 (the spectral theorem through the Cayley transform).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Sections 5.5 and 13.1.
-/

public section

noncomputable section

open Complex MeasureTheory TauCeti
open scoped InnerProductSpace

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- The **spectral measure** of a self-adjoint partial linear map `A`: the spectral measure of its
Cayley transform `U`, pushed forward to the real line along the real inverse Cayley coordinate
`w ↦ re (i (1 + w) / (1 - w))`. The pole `w = 1` carries no spectral mass of `U`
(`IsSelfAdjoint.diagMeasure_cayley_preimage_singleton_one_eq_zero`). -/
def spectralPVM (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure ℝ H :=
  haveI := hA.isStarNormal_cayley
  A.cayley.spectralPVM.map (fun w => (I * (1 + (w : ℂ)) / (1 - w)).re) (by fun_prop)

/-- The spectral measure of `A` is the pushforward of the spectral measure of its Cayley transform
along the real inverse Cayley coordinate. -/
theorem _root_.IsSelfAdjoint.spectralPVM_eq_map (hA : IsSelfAdjoint A) :
    haveI := hA.isStarNormal_cayley
    A.spectralPVM hA =
      A.cayley.spectralPVM.map (fun w => (I * (1 + (w : ℂ)) / (1 - w)).re) (by fun_prop) :=
  (rfl)

/-- The spectral projection of `A` on a Borel set `B` is the spectral projection of its Cayley
transform on the preimage of `B` under the real inverse Cayley coordinate. -/
@[simp]
theorem _root_.IsSelfAdjoint.spectralPVM_proj (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) :
    haveI := hA.isStarNormal_cayley
    (A.spectralPVM hA).proj B hB =
      A.cayley.spectralPVM.proj
        ((fun w : _root_.spectrum ℂ A.cayley => (I * (1 + (w : ℂ)) / (1 - w)).re) ⁻¹' B)
        ((by fun_prop : Measurable _) hB) := by
  rw [hA.spectralPVM_eq_map, ProjValMeasure.map_proj]

/-- The diagonal measures of the spectral measure of `A` are the pushforwards of the diagonal
measures of its Cayley transform along the real inverse Cayley coordinate. -/
@[simp]
theorem _root_.IsSelfAdjoint.spectralPVM_diag (hA : IsSelfAdjoint A) (ξ : H) :
    haveI := hA.isStarNormal_cayley
    (A.spectralPVM hA).diag ξ =
      (A.cayley.diagMeasure ξ).map fun w : _root_.spectrum ℂ A.cayley =>
        (I * (1 + (w : ℂ)) / (1 - w)).re := by
  rw [hA.spectralPVM_eq_map, ProjValMeasure.map_diag, ContinuousLinearMap.spectralPVM_diag]

/-- **The pole of the inverse Cayley transform carries no spectral mass.** Since `1` is not an
eigenvalue of the Cayley transform `U` of a self-adjoint partial linear map, every diagonal measure
of `U` assigns mass zero to `{1}`. -/
theorem _root_.IsSelfAdjoint.diagMeasure_cayley_preimage_singleton_one_eq_zero
    (hA : IsSelfAdjoint A) (ξ : H) :
    haveI := hA.isStarNormal_cayley
    A.cayley.diagMeasure ξ (Subtype.val ⁻¹' {1}) = 0 := by
  have := hA.isStarNormal_cayley
  have h := (A.cayley.spectralPVM_proj_preimage_singleton_eq_zero_iff 1).mpr fun x hx =>
    (cayley_apply_eq_self_iff hA.neg_I_mem_resolventSet).mp (by simpa using hx)
  rw [ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero] at h
  simpa using h ξ

/-- **The resolvent formula.** At every resolvent point `z`, in particular at every nonreal `z`,
the diagonal matrix elements of the resolvent of a self-adjoint partial linear map are the
Cauchy–Stieltjes transforms of the diagonal measures of its spectral measure:
`⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`. -/
theorem _root_.IsSelfAdjoint.inner_resolvent_apply_eq_integral (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ A.resolventSet) (ξ : H) :
    ⟪ξ, A.resolvent z ξ⟫_ℂ = ∫ s : ℝ, (z - s)⁻¹ ∂(A.spectralPVM hA).diag ξ := by
  have := hA.isStarNormal_cayley
  have hmeas : Measurable fun s : ℝ => (z - s)⁻¹ := by fun_prop
  rw [hA.spectralPVM_diag, integral_map (by fun_prop) hmeas.aestronglyMeasurable,
    hA.resolvent_eq_cfc_cayley hz, ← ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc _ _
      (fun w => (1 - w) / (z - I - (z + I) * w))
      (continuousOn_one_sub_div_sub_I_sub_add_I_mul hA.neg_I_mem_resolventSet hz)]
  -- Away from the null point `1`, the two symbols agree.
  have h1 : ∀ᵐ w : _root_.spectrum ℂ A.cayley ∂(A.cayley.diagMeasure ξ), (w : ℂ) ≠ 1 := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not]
    exact hA.diagMeasure_cayley_preimage_singleton_one_eq_zero ξ
  refine integral_congr_ae ?_
  filter_upwards [h1] with w hw
  have h1w : 1 - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [(hA.ofReal_re_inverseCayley_eq_and_mem_spectrum w.property hw).1]
  field_simp
  ring

/-- The spectral projections of a self-adjoint partial linear map commute with its Cayley
transform. -/
theorem _root_.IsSelfAdjoint.commute_cayley_spectralPVM_proj (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) : Commute A.cayley ((A.spectralPVM hA).proj B hB) := by
  have := hA.isStarNormal_cayley
  rw [hA.spectralPVM_eq_map, ProjValMeasure.map_proj]
  exact (A.cayley.forall_commute_spectralPVM_proj_iff A.cayley).2 (Commute.refl _) _ _

/-- Every bounded Borel function of the spectral measure of a self-adjoint partial linear map
commutes with its Cayley transform. -/
theorem _root_.IsSelfAdjoint.commute_cayley_spectralPVM_integral (hA : IsSelfAdjoint A)
    (f : BoundedBorelFunction ℝ) : Commute A.cayley ((A.spectralPVM hA).integral f) :=
  ((A.spectralPVM hA).forall_commute_integral_iff A.cayley).mpr
    hA.commute_cayley_spectralPVM_proj f

/-- **Bounded Borel functions of the spectral measure reduce the operator.** The integral `T` of a
bounded Borel function against the spectral measure of a self-adjoint partial linear map `A` maps
the domain of `A` into itself and satisfies `T (A x) = A (T x)` there: it intertwines `A` with
itself. -/
theorem _root_.IsSelfAdjoint.intertwines_spectralPVM_integral (hA : IsSelfAdjoint A)
    (f : BoundedBorelFunction ℝ) : A.Intertwines A ((A.spectralPVM hA).integral f) := by
  rw [intertwines_iff_comp_cayley_eq hA.neg_I_mem_resolventSet hA.neg_I_mem_resolventSet,
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  exact (hA.commute_cayley_spectralPVM_integral f).eq.symm

/-- **Spectral projections reduce the operator.** A spectral projection `P` of a self-adjoint
partial linear map `A` maps the domain of `A` into itself and satisfies `P (A x) = A (P x)` there:
it intertwines `A` with itself. -/
theorem _root_.IsSelfAdjoint.intertwines_spectralPVM_proj (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) : A.Intertwines A ((A.spectralPVM hA).proj B hB) := by
  simpa using hA.intertwines_spectralPVM_integral (BoundedBorelFunction.indicator B hB 1)

/-- Every bounded Borel function of the spectral measure of a self-adjoint partial linear map
commutes with its resolvent at every resolvent point. -/
theorem _root_.IsSelfAdjoint.commute_spectralPVM_integral_resolvent (hA : IsSelfAdjoint A)
    (f : BoundedBorelFunction ℝ) {z : ℂ} (hz : z ∈ A.resolventSet) :
    Commute ((A.spectralPVM hA).integral f) (A.resolvent z) := by
  have h := (intertwines_iff_comp_resolvent_eq hz hz).mp (hA.intertwines_spectralPVM_integral f)
  rwa [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at h

/-- The spectral projections of a self-adjoint partial linear map commute with its resolvent at
every resolvent point. -/
theorem _root_.IsSelfAdjoint.commute_spectralPVM_proj_resolvent (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) {z : ℂ} (hz : z ∈ A.resolventSet) :
    Commute ((A.spectralPVM hA).proj B hB) (A.resolvent z) := by
  simpa using
    hA.commute_spectralPVM_integral_resolvent (BoundedBorelFunction.indicator B hB 1) hz

/-- **The spectral measure lives on the spectrum.** The spectral projection of a Borel set of real
resolvent points of a self-adjoint partial linear map vanishes. -/
theorem _root_.IsSelfAdjoint.spectralPVM_proj_eq_zero_of_forall_mem_resolventSet
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B)
    (hBA : ∀ s ∈ B, (s : ℂ) ∈ A.resolventSet) :
    (A.spectralPVM hA).proj B hB = 0 := by
  have := hA.isStarNormal_cayley
  rw [ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero]
  intro ξ
  rw [hA.spectralPVM_diag, Measure.map_apply (by fun_prop) hB]
  refine measure_mono_null (fun w hw => ?_)
    (hA.diagMeasure_cayley_preimage_singleton_one_eq_zero ξ)
  -- A point `w ≠ 1` of the spectrum of `U` has its inverse Cayley image in the spectrum of `A`.
  by_contra h1
  obtain ⟨hre, hmem⟩ := hA.ofReal_re_inverseCayley_eq_and_mem_spectrum w.property h1
  exact (A.mem_spectrum_iff _).mp hmem (hre ▸ hBA _ hw)

/-- For `x = v - U v` in the domain, the quadratic form is `re ⟪A x, x⟫ = -2 im ⟪v, U v⟫` and
`‖x‖² = ‖(1 - U) v‖²`, both integrals against the diagonal measure of `v`. -/
private theorem re_inner_eq_integral_and_norm_sq_eq_integral (hA : IsSelfAdjoint A)
    {x : A.domain} {v : H} (hx : (x : H) = v - A.cayley v) :
    haveI := hA.isStarNormal_cayley
    re ⟪A x, x⟫_ℂ = ∫ w, -2 * (w : ℂ).im ∂A.cayley.diagMeasure v ∧
      ‖(x : H)‖ ^ 2 = ∫ w, ‖1 - (w : ℂ)‖ ^ 2 ∂A.cayley.diagMeasure v := by
  have := hA.isStarNormal_cayley
  have hm := hA.neg_I_mem_resolventSet
  have hAx : A x = I • (v + A.cayley v) :=
    A.mem_graph_snd_inj (A.mem_graph x) ((mem_graph_iff_exists_cayley hm).mpr ⟨v, rfl⟩) hx
  have hUint : ∫ w, (w : ℂ) ∂A.cayley.diagMeasure v = ⟪v, A.cayley v⟫_ℂ := by
    rw [A.cayley.integral_diagMeasure_eq_inner_cfc v (fun w => w), cfc_id' ℂ A.cayley]
  have hint : Integrable (fun w : _root_.spectrum ℂ A.cayley => (w : ℂ))
      (A.cayley.diagMeasure v) :=
    continuous_subtypeVal.integrable_of_hasCompactSupport (.of_compactSpace _)
  have him : ∫ w, (w : ℂ).im ∂A.cayley.diagMeasure v = (⟪v, A.cayley v⟫_ℂ).im := by
    simpa [hUint] using integral_im hint
  have hself : ⟪A.cayley v, A.cayley v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hA.norm_cayley_apply v]
  constructor
  · rw [integral_const_mul, him, hAx, hx, inner_smul_left, inner_add_left,
      inner_sub_right, inner_sub_right, hself]
    simp only [conj_I, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, zero_sub, one_mul]
    rw [← inner_conj_symm (A.cayley v) v]
    simp only [add_im, sub_im, conj_im]
    ring
  · -- `x = (1 - U) v` is the continuous functional calculus of `w ↦ 1 - w` at `v`.
    have h := A.cayley.integral_norm_sq_diagMeasure v
      (1 - (ContinuousMap.id ℂ).restrict (_root_.spectrum ℂ A.cayley))
    simpa [hx, cfcHom_id] using h.symm

/-- The **quadratic form through the Cayley transform**: at `x = v - U v`,
`re ⟪A x, x⟫ - c ‖x‖² = ∫ (κ(w) - c) ‖1 - w‖² dμ_v(w)`, where `κ` is the real inverse Cayley
coordinate. -/
private theorem re_inner_sub_mul_norm_sq_eq_integral (hA : IsSelfAdjoint A) (c : ℝ)
    {x : A.domain} {v : H} (hx : (x : H) = v - A.cayley v) :
    haveI := hA.isStarNormal_cayley
    re ⟪A x, x⟫_ℂ - c * ‖(x : H)‖ ^ 2 =
      ∫ w, ((I * (1 + (w : ℂ)) / (1 - w)).re - c) * ‖1 - (w : ℂ)‖ ^ 2
        ∂A.cayley.diagMeasure v := by
  have := hA.isStarNormal_cayley
  obtain ⟨hre, hnorm⟩ := re_inner_eq_integral_and_norm_sq_eq_integral hA hx
  have hint (f : _root_.spectrum ℂ A.cayley → ℝ) (hf : Continuous f) :
      Integrable f (A.cayley.diagMeasure v) :=
    hf.integrable_of_hasCompactSupport (.of_compactSpace f)
  rw [hre, hnorm, ← integral_const_mul, ← integral_sub (hint _ (by fun_prop))
    (hint (fun w => c * ‖1 - (w : ℂ)‖ ^ 2) (by fun_prop))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [sub_mul, re_I_mul_one_add_div_one_sub_mul_norm_one_sub_sq]

/-- If the spectral measure of `v` vanishes on `(-∞, c)`, then `c ‖x‖² ≤ re ⟪A x, x⟫` at
`x = v - U v`. -/
private theorem mul_norm_sq_le_re_inner_of_diag_Iio (hA : IsSelfAdjoint A) {c : ℝ}
    {x : A.domain} {v : H} (hx : (x : H) = v - A.cayley v)
    (hv : (A.spectralPVM hA).diag v (Set.Iio c) = 0) :
    c * ‖(x : H)‖ ^ 2 ≤ re ⟪A x, x⟫_ℂ := by
  have := hA.isStarNormal_cayley
  have h : ∀ᵐ s ∂(A.spectralPVM hA).diag v, c ≤ s := by
    refine ae_iff.mpr ?_
    simp only [not_le]
    exact hv
  rw [hA.spectralPVM_diag] at h
  rw [← sub_nonneg, re_inner_sub_mul_norm_sq_eq_integral hA c hx]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_of_ae_map (by fun_prop) h] with w hw
  exact mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg _)

/-- If the spectral measure of `v` vanishes on `(c, ∞)`, then `re ⟪A x, x⟫ ≤ c ‖x‖²` at
`x = v - U v`. -/
private theorem re_inner_le_mul_norm_sq_of_diag_Ioi (hA : IsSelfAdjoint A) {c : ℝ}
    {x : A.domain} {v : H} (hx : (x : H) = v - A.cayley v)
    (hv : (A.spectralPVM hA).diag v (Set.Ioi c) = 0) :
    re ⟪A x, x⟫_ℂ ≤ c * ‖(x : H)‖ ^ 2 := by
  have := hA.isStarNormal_cayley
  have h : ∀ᵐ s ∂(A.spectralPVM hA).diag v, s ≤ c := by
    refine ae_iff.mpr ?_
    simp only [not_le]
    exact hv
  rw [hA.spectralPVM_diag] at h
  rw [← sub_nonpos, re_inner_sub_mul_norm_sq_eq_integral hA c hx]
  refine integral_nonpos_of_ae ?_
  filter_upwards [ae_of_ae_map (by fun_prop) h] with w hw
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hw) (sq_nonneg _)

/-- A domain vector `x` in the range of the spectral projection `P(B)` is `v - U v` for a vector
`v` whose spectral measure vanishes off `B`: take `v = P(B) v₀` for any `v₀` with `x = v₀ - U v₀`,
using that `P(B)` commutes with `U`. -/
private theorem exists_eq_sub_cayley_diag_compl_eq_zero (hA : IsSelfAdjoint A) {B : Set ℝ}
    (hB : MeasurableSet B) {x : A.domain}
    (hx : (x : H) ∈ ((A.spectralPVM hA).proj B hB).range) :
    ∃ v : H, (x : H) = v - A.cayley v ∧ (A.spectralPVM hA).diag v Bᶜ = 0 := by
  set P := A.spectralPVM hA
  obtain ⟨v, hv⟩ := (mem_graph_iff_exists_cayley hA.neg_I_mem_resolventSet).mp (A.mem_graph x)
  obtain ⟨y, hy⟩ := hx
  rw [ContinuousLinearMap.coe_coe] at hy
  have hPx : P.proj B hB x = x := by rw [← hy, P.proj_apply_proj]
  have hUP : A.cayley (P.proj B hB v) = P.proj B hB (A.cayley v) := by
    simpa only [mul_apply_eq_comp] using
      congr($((hA.commute_cayley_spectralPVM_proj B hB).eq) v)
  refine ⟨P.proj B hB v, ?_, ?_⟩
  · have hxv : v - A.cayley v = x := congrArg Prod.fst hv
    rw [hUP, ← ContinuousLinearMap.map_sub, hxv, hPx]
  · rw [← P.enorm_sq_proj_apply Bᶜ hB.compl, ← mul_apply_eq_comp,
      P.proj_mul_eq_zero_of_disjoint hB.compl hB disjoint_compl_left]
    simp

/-- **Lower form bound on a spectral range.** If `B ⊆ [β, ∞)`, then `β ‖x‖² ≤ re ⟪A x, x⟫` for
every `x ∈ dom A` in the range of the spectral projection `P(B)`. -/
theorem _root_.IsSelfAdjoint.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B) {β : ℝ} (hβ : B ⊆ Set.Ici β)
    {x : A.domain} (hx : (x : H) ∈ ((A.spectralPVM hA).proj B hB).range) :
    β * ‖(x : H)‖ ^ 2 ≤ re ⟪A x, x⟫_ℂ := by
  obtain ⟨v, hxv, hv⟩ := exists_eq_sub_cayley_diag_compl_eq_zero hA hB hx
  have hsub : Set.Iio β ⊆ Bᶜ := fun s hs hsB => not_le.mpr hs (Set.mem_Ici.mp (hβ hsB))
  exact mul_norm_sq_le_re_inner_of_diag_Iio hA hxv (measure_mono_null hsub hv)

/-- **Upper form bound on a spectral range.** If `B ⊆ (-∞, α]`, then `re ⟪A x, x⟫ ≤ α ‖x‖²` for
every `x ∈ dom A` in the range of the spectral projection `P(B)`. -/
theorem _root_.IsSelfAdjoint.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B) {α : ℝ} (hα : B ⊆ Set.Iic α)
    {x : A.domain} (hx : (x : H) ∈ ((A.spectralPVM hA).proj B hB).range) :
    re ⟪A x, x⟫_ℂ ≤ α * ‖(x : H)‖ ^ 2 := by
  obtain ⟨v, hxv, hv⟩ := exists_eq_sub_cayley_diag_compl_eq_zero hA hB hx
  have hsub : Set.Ioi α ⊆ Bᶜ := fun s hs hsB => not_le.mpr hs (Set.mem_Iic.mp (hα hsB))
  exact re_inner_le_mul_norm_sq_of_diag_Ioi hA hxv (measure_mono_null hsub hv)

/-- A nonzero spectral projection `P(B)` has a nonzero vector of the domain in its range: for
`P(B) v ≠ 0`, the vector `x = P(B) v - U P(B) v = P(B) (v - U v)`, which is nonzero because `1` is
not an eigenvalue of `U`. -/
private theorem exists_ne_zero_mem_range_spectralPVM_proj (hA : IsSelfAdjoint A) {B : Set ℝ}
    (hB : MeasurableSet B) (h : (A.spectralPVM hA).proj B hB ≠ 0) :
    ∃ x : A.domain, (x : H) ≠ 0 ∧ (x : H) ∈ ((A.spectralPVM hA).proj B hB).range := by
  set P := (A.spectralPVM hA).proj B hB
  have hm := hA.neg_I_mem_resolventSet
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra! h'
    exact h (ContinuousLinearMap.ext h')
  have hUP : A.cayley (P v) = P (A.cayley v) := by
    simpa only [mul_apply_eq_comp] using
      congr($((hA.commute_cayley_spectralPVM_proj B hB).eq) v)
  refine ⟨⟨P v - A.cayley (P v),
    mem_domain_of_mem_graph ((mem_graph_iff_exists_cayley hm).mpr ⟨P v, rfl⟩)⟩, fun h0 => ?_,
    v - A.cayley v, by simp [hUP]⟩
  exact hv ((cayley_apply_eq_self_iff hm).mp (sub_eq_zero.mp h0).symm)

/-- **Spectral support above `c` and the lower form bound.** The spectral measure of a
self-adjoint partial linear map `A` vanishes on `(-∞, c)` exactly when `c ‖x‖² ≤ re ⟪A x, x⟫` for
every `x ∈ dom A`. -/
theorem _root_.IsSelfAdjoint.spectralPVM_proj_Iio_eq_zero_iff (hA : IsSelfAdjoint A) (c : ℝ) :
    (A.spectralPVM hA).proj (Set.Iio c) measurableSet_Iio = 0 ↔
      ∀ x : A.domain, c * ‖(x : H)‖ ^ 2 ≤ re ⟪A x, x⟫_ℂ := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_graph_iff_exists_cayley hA.neg_I_mem_resolventSet).mp (A.mem_graph x)
    exact mul_norm_sq_le_re_inner_of_diag_Iio hA (congrArg Prod.fst hv).symm
      ((ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _ _).mp h v)
  -- Conversely, a nonzero `P((-∞, c - ε])` would contain a domain vector violating the bound.
  have hε (n : ℕ) :
      (A.spectralPVM hA).proj (Set.Iic (c - 1 / ((n : ℝ) + 1))) measurableSet_Iic = 0 := by
    by_contra hne
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_range_spectralPVM_proj hA measurableSet_Iic hne
    have h1 := hA.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj _ subset_rfl hx
    have h2 : 0 < ‖(x : H)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h3 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    nlinarith [h x]
  refine (A.spectralPVM hA).proj_eq_zero_of_subset (fun s hs => ?_) measurableSet_Iio
    (MeasurableSet.iUnion fun _ => measurableSet_Iic)
    ((A.spectralPVM hA).proj_iUnion_eq_zero _ _ hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (Set.mem_Iio.mp hs))
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_Iic.mpr (by linarith)⟩

/-- **Spectral support below `c` and the upper form bound.** The spectral measure of a
self-adjoint partial linear map `A` vanishes on `(c, ∞)` exactly when `re ⟪A x, x⟫ ≤ c ‖x‖²` for
every `x ∈ dom A`. -/
theorem _root_.IsSelfAdjoint.spectralPVM_proj_Ioi_eq_zero_iff (hA : IsSelfAdjoint A) (c : ℝ) :
    (A.spectralPVM hA).proj (Set.Ioi c) measurableSet_Ioi = 0 ↔
      ∀ x : A.domain, re ⟪A x, x⟫_ℂ ≤ c * ‖(x : H)‖ ^ 2 := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_graph_iff_exists_cayley hA.neg_I_mem_resolventSet).mp (A.mem_graph x)
    exact re_inner_le_mul_norm_sq_of_diag_Ioi hA (congrArg Prod.fst hv).symm
      ((ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _ _).mp h v)
  -- Conversely, a nonzero `P([c + ε, ∞))` would contain a domain vector violating the bound.
  have hε (n : ℕ) :
      (A.spectralPVM hA).proj (Set.Ici (c + 1 / ((n : ℝ) + 1))) measurableSet_Ici = 0 := by
    by_contra hne
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_range_spectralPVM_proj hA measurableSet_Ici hne
    have h1 := hA.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj _ subset_rfl hx
    have h2 : 0 < ‖(x : H)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h3 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    nlinarith [h x]
  refine (A.spectralPVM hA).proj_eq_zero_of_subset (fun s hs => ?_) measurableSet_Ioi
    (MeasurableSet.iUnion fun _ => measurableSet_Ici)
    ((A.spectralPVM hA).proj_iUnion_eq_zero _ _ hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (Set.mem_Ioi.mp hs))
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_Ici.mpr (by linarith)⟩

end LinearPMap
