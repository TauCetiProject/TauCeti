/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map

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

The spectral measure is pinned down by the resolvents of `A`. At a resolvent point `z` the
resolvent is the continuous function `(1 - w) / ((z - i) - (z + i) w)` of `U`, which is
`(z - κ(w))⁻¹` away from `w = 1`. Its diagonal matrix elements are therefore the Cauchy–Stieltjes
transforms of the diagonal measures of `P_A`: `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`.

The spectral projections commute with `U`, so they intertwine `A` with itself: they preserve the
domain of `A`, commute with `A` on it, and commute with every resolvent of `A`. Moreover `P_A` lives
on the spectrum of `A`: the spectral projection of a Borel set of resolvent points vanishes.

Finally, spectral support controls the quadratic form of `A`. Every `x ∈ dom A` is `v - U v`,
and then `re ⟪A x, x⟫ = ∫ κ(w) ‖1 - w‖² dμ_v(w)` and `‖x‖² = ∫ ‖1 - w‖² dμ_v(w)` for the
diagonal measure `μ_v` of `U`. So if `P_A` vanishes on `(-∞, c)`, then `c ‖x‖² ≤ re ⟪A x, x⟫`
on `dom A`, and similarly for upper bounds and for vectors in the range of a spectral
projection `P_A(B)`.

## Main declarations

* `LinearPMap.spectralPVM A hA`: the spectral measure of a self-adjoint partial linear map, a
  projection-valued measure on `ℝ`.
* `IsSelfAdjoint.diagMeasure_cayley_preimage_singleton_one_eq_zero`: the diagonal measures of the
  Cayley transform assign no mass to the point `1`.
* `IsSelfAdjoint.resolvent_eq_cfc_cayley`: the resolvent `R(z)` is a continuous function of the
  Cayley transform.
* `IsSelfAdjoint.inner_resolvent_apply_eq_integral`: the resolvent formula
  `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`.
* `IsSelfAdjoint.intertwines_spectralPVM_proj`: spectral projections preserve the domain of `A`
  and commute with `A` on it.
* `IsSelfAdjoint.commute_spectralPVM_proj_resolvent`: spectral projections commute with the
  resolvents.
* `IsSelfAdjoint.spectralPVM_proj_eq_zero`: the spectral projection of a Borel set of resolvent
  points vanishes.
* `IsSelfAdjoint.mul_norm_sq_le_re_inner_of_proj_Iio_eq_zero`,
  `IsSelfAdjoint.re_inner_le_mul_norm_sq_of_proj_Ioi_eq_zero`: form bounds from spectral support.
* `IsSelfAdjoint.mul_norm_sq_le_re_inner_of_mem_range_proj`,
  `IsSelfAdjoint.re_inner_le_mul_norm_sq_of_mem_range_proj`: form bounds on a spectral range.

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

/-- The diagonal measures of the spectral measure of `A` are the pushforwards of the diagonal
measures of its Cayley transform along the real inverse Cayley coordinate. -/
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
  have h := A.cayley.spectralPVM_proj_preimage_singleton_eq_zero (z := 1) fun x hx =>
    (cayley_apply_eq_self_iff hA.neg_I_mem_resolventSet).mp (by simpa using hx)
  rw [ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero] at h
  simpa using h ξ

/-- The spectrum of the Cayley transform of a self-adjoint partial linear map lies on the unit
circle, since the Cayley transform is unitary. -/
private theorem norm_eq_one_of_mem_spectrum_cayley (hA : IsSelfAdjoint A) {w : ℂ}
    (hw : w ∈ _root_.spectrum ℂ A.cayley) : ‖w‖ = 1 :=
  mem_sphere_zero_iff_norm.mp (spectrum.subset_circle_of_unitary hA.cayley_mem_unitary hw)

/-- Away from `1`, a point `w` of the spectrum of the Cayley transform has a real inverse Cayley
image `i (1 + w) / (1 - w)`, which lies in the spectrum of `A`. -/
private theorem ofReal_re_inverseCayley_eq_and_mem_spectrum (hA : IsSelfAdjoint A) {w : ℂ}
    (hw : w ∈ _root_.spectrum ℂ A.cayley) (h1 : w ≠ 1) :
    (((I * (1 + w) / (1 - w)).re : ℝ) : ℂ) = I * (1 + w) / (1 - w) ∧
      I * (1 + w) / (1 - w) ∈ A.spectrum := by
  have hmem := (mem_spectrum_cayley_iff hA.neg_I_mem_resolventSet h1).mp hw
  exact ⟨Complex.ext (by simp) (by simpa using (hA.spectrum_subset_im_eq_zero hmem).symm), hmem⟩

/-- At a resolvent point `z`, the denominator `(z - i) - (z + i) w` of the resolvent symbol does
not vanish on the spectrum of the Cayley transform: at `w = 1` it is `-2i`, and otherwise its
vanishing would make `z = i (1 + w) / (1 - w)` a point of the spectrum of `A`. -/
private theorem sub_I_sub_add_I_mul_ne_zero (hA : IsSelfAdjoint A) {z w : ℂ}
    (hz : z ∈ A.resolventSet) (hw : w ∈ _root_.spectrum ℂ A.cayley) :
    z - I - (z + I) * w ≠ 0 := by
  intro h
  by_cases h1 : w = 1
  · have h2 : (2 : ℂ) * I = 0 := by linear_combination -h - (z + I) * h1
    simp at h2
  · refine (A.mem_spectrum_iff z).mp ?_ hz
    convert (ofReal_re_inverseCayley_eq_and_mem_spectrum hA hw h1).2 using 1
    rw [eq_div_iff (sub_ne_zero.mpr (Ne.symm h1))]
    linear_combination h

/-- **The resolvent as a function of the Cayley transform.** At every resolvent point `z`, the
resolvent of a self-adjoint partial linear map is `R(z) = (1 - U) ((z - i) - (z + i) U)⁻¹`, the
continuous functional calculus of the Cayley transform `U` at
`w ↦ (1 - w) / ((z - i) - (z + i) w)`. -/
theorem _root_.IsSelfAdjoint.resolvent_eq_cfc_cayley (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ A.resolventSet) :
    A.resolvent z = cfc (fun w => (1 - w) / (z - I - (z + I) * w)) A.cayley := by
  have := hA.isStarNormal_cayley
  have hd : ∀ w ∈ _root_.spectrum ℂ A.cayley, z - I - (z + I) * w ≠ 0 := fun _ hw =>
    sub_I_sub_add_I_mul_ne_zero hA hz hw
  set U := A.cayley with hU
  -- `K = ((z - i) - (z + i) U)⁻¹`, a two-sided inverse of `D = (z - i) - (z + i) U`.
  set K := cfc (fun w => (z - I - (z + I) * w)⁻¹) U with hK
  have hcd : ContinuousOn (fun w => z - I - (z + I) * w) (_root_.spectrum ℂ U) := by fun_prop
  have hci : ContinuousOn (fun w => (z - I - (z + I) * w)⁻¹) (_root_.spectrum ℂ U) :=
    hcd.inv₀ hd
  have hD : cfc (fun w => z - I - (z + I) * w) U = (z - I) • 1 - (z + I) • U := by
    rw [cfc_sub (fun _ => z - I) (fun w => (z + I) * w) U, cfc_const (z - I) U,
      cfc_const_mul (z + I) (fun w => w) U, cfc_id' ℂ U, Algebra.algebraMap_eq_smul_one]
  have hDK : ((z - I) • 1 - (z + I) • U) * K = 1 := by
    rw [← hD, hK, ← cfc_mul _ _ U hcd hci, ← cfc_one ℂ U]
    exact cfc_congr fun w hw => mul_inv_cancel₀ (hd w hw)
  have hKD : K * ((z - I) • 1 - (z + I) • U) = 1 := by
    rw [← hD, hK, ← cfc_mul _ _ U hci hcd, ← cfc_one ℂ U]
    exact cfc_congr fun w hw => inv_mul_cancel₀ (hd w hw)
  have hG : cfc (fun w => (1 - w) / (z - I - (z + I) * w)) U = (1 - U) * K := by
    simp_rw [div_eq_mul_inv]
    rw [cfc_mul (fun w => 1 - w) _ U (by fun_prop) hci, cfc_sub (fun _ => 1) (fun w => w) U,
      cfc_const_one ℂ U, cfc_id' ℂ U]
  rw [hG]
  have hm := hA.neg_I_mem_resolventSet
  -- The graph of `A` is `{(x - U x, i (x + U x))}`, on which `z • p.1 - p.2 = D x`.
  refine resolvent_eq_of_isResolventAt (isResolventAt_iff_forall_mem_graph.mpr ⟨fun y => ?_, ?_⟩)
  · have hy : (z - I) • K y - (z + I) • U (K y) = y := by
      simpa using congrArg (· y) hDK
    refine (mem_graph_iff_exists_cayley hm).mpr ⟨K y, ?_⟩
    simp only [mul_apply_eq_comp, _root_.sub_apply, one_apply_eq_self]
    generalize K y = x at hy ⊢
    subst hy
    rw [← hU, Prod.mk.injEq]
    exact ⟨rfl, by module⟩
  · rintro p hp
    obtain ⟨x, rfl⟩ := (mem_graph_iff_exists_cayley hm).mp hp
    have hx : K ((z - I) • x - (z + I) • U x) = x := by
      simpa using congrArg (· x) hKD
    simp only [mul_apply_eq_comp, _root_.sub_apply, one_apply_eq_self]
    rw [← hU, show z • (x - U x) - I • (x + U x) = (z - I) • x - (z + I) • U x by module, hx]

/-- **The resolvent formula.** At every resolvent point `z`, in particular at every nonreal `z`,
the diagonal matrix elements of the resolvent of a self-adjoint partial linear map are the
Cauchy–Stieltjes transforms of the diagonal measures of its spectral measure:
`⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`. -/
theorem _root_.IsSelfAdjoint.inner_resolvent_apply_eq_integral (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ A.resolventSet) (ξ : H) :
    ⟪ξ, A.resolvent z ξ⟫_ℂ = ∫ s : ℝ, (z - s)⁻¹ ∂(A.spectralPVM hA).diag ξ := by
  have := hA.isStarNormal_cayley
  have hmeas : Measurable fun s : ℝ => (z - s)⁻¹ := by fun_prop
  have hd : ∀ w ∈ _root_.spectrum ℂ A.cayley, z - I - (z + I) * w ≠ 0 := fun _ hw =>
    sub_I_sub_add_I_mul_ne_zero hA hz hw
  rw [hA.spectralPVM_diag, integral_map (by fun_prop) hmeas.aestronglyMeasurable,
    hA.resolvent_eq_cfc_cayley hz, ← ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc _ _
      (fun w => (1 - w) / (z - I - (z + I) * w)) (ContinuousOn.div (by fun_prop) (by fun_prop) hd)]
  -- Away from the null point `1`, the two symbols agree.
  have h1 : ∀ᵐ w : _root_.spectrum ℂ A.cayley ∂(A.cayley.diagMeasure ξ), (w : ℂ) ≠ 1 := by
    refine ae_iff.mpr ?_
    simp only [ne_eq, not_not]
    exact hA.diagMeasure_cayley_preimage_singleton_one_eq_zero ξ
  refine integral_congr_ae ?_
  filter_upwards [h1] with w hw
  have h1w : 1 - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [(ofReal_re_inverseCayley_eq_and_mem_spectrum hA w.2 hw).1]
  field_simp
  ring

/-- The spectral projections of a self-adjoint partial linear map commute with its Cayley
transform. -/
theorem _root_.IsSelfAdjoint.commute_cayley_spectralPVM_proj (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) : Commute A.cayley ((A.spectralPVM hA).proj B hB) := by
  have := hA.isStarNormal_cayley
  rw [hA.spectralPVM_eq_map, ProjValMeasure.map_proj]
  exact (A.cayley.forall_commute_spectralPVM_proj_iff A.cayley).2 (Commute.refl _) _ _

/-- **Spectral projections reduce the operator.** A spectral projection `P` of a self-adjoint
partial linear map `A` maps the domain of `A` into itself and satisfies `P (A x) = A (P x)` there:
it intertwines `A` with itself. -/
theorem _root_.IsSelfAdjoint.intertwines_spectralPVM_proj (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) : A.Intertwines A ((A.spectralPVM hA).proj B hB) := by
  rw [intertwines_iff_comp_cayley_eq hA.neg_I_mem_resolventSet hA.neg_I_mem_resolventSet,
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  exact (hA.commute_cayley_spectralPVM_proj B hB).eq.symm

/-- The spectral projections of a self-adjoint partial linear map commute with its resolvent at
every resolvent point. -/
theorem _root_.IsSelfAdjoint.commute_spectralPVM_proj_resolvent (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) {z : ℂ} (hz : z ∈ A.resolventSet) :
    Commute ((A.spectralPVM hA).proj B hB) (A.resolvent z) := by
  have h := (intertwines_iff_comp_resolvent_eq hz hz).mp (hA.intertwines_spectralPVM_proj B hB)
  rwa [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def] at h

/-- **The spectral measure lives on the spectrum.** The spectral projection of a Borel set of real
resolvent points of a self-adjoint partial linear map vanishes. -/
theorem _root_.IsSelfAdjoint.spectralPVM_proj_eq_zero (hA : IsSelfAdjoint A) {B : Set ℝ}
    (hB : MeasurableSet B) (hBA : ∀ s ∈ B, (s : ℂ) ∈ A.resolventSet) :
    (A.spectralPVM hA).proj B hB = 0 := by
  have := hA.isStarNormal_cayley
  rw [ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero]
  intro ξ
  rw [hA.spectralPVM_diag, Measure.map_apply (by fun_prop) hB]
  refine measure_mono_null (fun w hw => ?_)
    (hA.diagMeasure_cayley_preimage_singleton_one_eq_zero ξ)
  -- A point `w ≠ 1` of the spectrum of `U` has its inverse Cayley image in the spectrum of `A`.
  by_contra h1
  obtain ⟨hre, hmem⟩ := ofReal_re_inverseCayley_eq_and_mem_spectrum hA w.2 h1
  exact (A.mem_spectrum_iff _).mp hmem (hre ▸ hBA _ hw)

/-- On the unit circle, `re (i (1 + w) / (1 - w)) * ‖1 - w‖² = -2 im w`. -/
private theorem re_inverseCayley_mul_eq {w : ℂ} (hw : ‖w‖ = 1) :
    (I * (1 + w) / (1 - w)).re * (2 - 2 * w.re) = -2 * w.im := by
  have h : w.re ^ 2 + w.im ^ 2 = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, Complex.sq_norm, normSq_apply] at hw
    linarith
  by_cases h1 : w = 1
  · subst h1
    simp
  have hn : normSq (1 - w) = 2 - 2 * w.re := by
    simp only [normSq_apply, sub_re, one_re, sub_im, one_im]
    nlinarith
  have hn0 : normSq (1 - w) ≠ 0 := normSq_eq_zero.not.mpr (sub_ne_zero.mpr (Ne.symm h1))
  rw [← hn, div_re]
  simp only [mul_re, mul_im, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im]
  field_simp
  nlinarith [h]

/-- The coordinate function is integrable for the diagonal measures of the Cayley transform. -/
private theorem integrable_diagMeasure_cayley (hA : IsSelfAdjoint A) (v : H) :
    haveI := hA.isStarNormal_cayley
    Integrable (fun w : _root_.spectrum ℂ A.cayley => (w : ℂ)) (A.cayley.diagMeasure v) := by
  have := hA.isStarNormal_cayley
  exact .of_bound (by fun_prop) 1
    (Filter.Eventually.of_forall fun w => (norm_eq_one_of_mem_spectrum_cayley hA w.2).le)

/-- For `x = v - U v` in the domain, the quadratic form is `re ⟪A x, x⟫ = -2 im ⟪v, U v⟫` and
`‖x‖² = 2 ‖v‖² - 2 re ⟪v, U v⟫`, both integrals against the diagonal measure of `v`. -/
private theorem re_inner_eq_integral_and_norm_sq_eq_integral (hA : IsSelfAdjoint A)
    {x : A.domain} {v : H} (hx : (x : H) = v - A.cayley v) :
    haveI := hA.isStarNormal_cayley
    re ⟪A x, x⟫_ℂ = ∫ w, -2 * (w : ℂ).im ∂A.cayley.diagMeasure v ∧
      ‖(x : H)‖ ^ 2 = ∫ w, (2 - 2 * (w : ℂ).re) ∂A.cayley.diagMeasure v := by
  have := hA.isStarNormal_cayley
  have hm := hA.neg_I_mem_resolventSet
  have hAx : A x = I • (v + A.cayley v) :=
    A.mem_graph_snd_inj (A.mem_graph x) ((mem_graph_iff_exists_cayley hm).mpr ⟨v, rfl⟩) hx
  have hUv : ‖A.cayley v‖ = ‖v‖ := hA.norm_cayley_apply v
  have hint := integrable_diagMeasure_cayley hA v
  have hUint : ∫ w, (w : ℂ) ∂A.cayley.diagMeasure v = ⟪v, A.cayley v⟫_ℂ := by
    rw [A.cayley.integral_diagMeasure_eq_inner_cfc v (fun w => w), cfc_id' ℂ A.cayley]
  have him : ∫ w, (w : ℂ).im ∂A.cayley.diagMeasure v = (⟪v, A.cayley v⟫_ℂ).im := by
    simpa [hUint] using integral_im hint
  have hre : ∫ w, (w : ℂ).re ∂A.cayley.diagMeasure v = (⟪v, A.cayley v⟫_ℂ).re := by
    simpa [hUint] using integral_re hint
  have hself : ⟪A.cayley v, A.cayley v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hUv]
  constructor
  · rw [integral_const_mul, him, hAx, hx, inner_smul_left, inner_add_left,
      inner_sub_right, inner_sub_right, hself]
    simp only [conj_I, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, zero_sub, one_mul]
    rw [← inner_conj_symm (A.cayley v) v]
    simp only [add_im, sub_im, conj_im]
    ring
  · have hint_re : Integrable (fun w : _root_.spectrum ℂ A.cayley => (w : ℂ).re)
        (A.cayley.diagMeasure v) := by simpa using hint.re
    rw [integral_sub (integrable_const _) (hint_re.const_mul 2), integral_const_mul,
      integral_const, hre, hx, norm_sub_sq (𝕜 := ℂ), hUv]
    simp
    ring

/-- The **quadratic form through the Cayley transform**: at `x = v - U v`,
`re ⟪A x, x⟫ - c ‖x‖² = ∫ (κ(w) - c) ‖1 - w‖² dμ_v(w)`, where `κ` is the real inverse Cayley
coordinate and `‖1 - w‖² = 2 - 2 re w` on the unit circle. -/
private theorem re_inner_sub_mul_norm_sq_eq_integral (hA : IsSelfAdjoint A) (c : ℝ)
    {x : A.domain} {v : H} (hx : (x : H) = v - A.cayley v) :
    haveI := hA.isStarNormal_cayley
    re ⟪A x, x⟫_ℂ - c * ‖(x : H)‖ ^ 2 =
      ∫ w, ((I * (1 + (w : ℂ)) / (1 - w)).re - c) * (2 - 2 * (w : ℂ).re)
        ∂A.cayley.diagMeasure v := by
  have := hA.isStarNormal_cayley
  obtain ⟨hre, hnorm⟩ := re_inner_eq_integral_and_norm_sq_eq_integral hA hx
  have hint := integrable_diagMeasure_cayley hA v
  have hint_re : Integrable (fun w : _root_.spectrum ℂ A.cayley => (w : ℂ).re)
      (A.cayley.diagMeasure v) := by simpa using hint.re
  have hint_im : Integrable (fun w : _root_.spectrum ℂ A.cayley => (w : ℂ).im)
      (A.cayley.diagMeasure v) := by simpa using hint.im
  have hint_norm : Integrable (fun w : _root_.spectrum ℂ A.cayley => c * (2 - 2 * (w : ℂ).re))
      (A.cayley.diagMeasure v) := ((integrable_const 2).sub (hint_re.const_mul 2)).const_mul c
  rw [hre, hnorm, ← integral_const_mul, ← integral_sub (hint_im.const_mul (-2)) hint_norm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [sub_mul, re_inverseCayley_mul_eq (norm_eq_one_of_mem_spectrum_cayley hA w.2)]

/-- On the spectrum of the Cayley transform, `‖1 - w‖² = 2 - 2 re w` is nonnegative. -/
private theorem two_sub_two_mul_re_nonneg (hA : IsSelfAdjoint A)
    (w : _root_.spectrum ℂ A.cayley) : 0 ≤ 2 - 2 * (w : ℂ).re := by
  linarith [(re_le_norm (w : ℂ)).trans (norm_eq_one_of_mem_spectrum_cayley hA w.2).le]

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
  exact mul_nonneg (sub_nonneg.mpr hw) (two_sub_two_mul_re_nonneg hA w)

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
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hw) (two_sub_two_mul_re_nonneg hA w)

/-- **Lower form bound from spectral support.** If the spectral measure of a self-adjoint partial
linear map `A` vanishes on `(-∞, c)`, then `c ‖x‖² ≤ re ⟪A x, x⟫` for every `x ∈ dom A`. -/
theorem _root_.IsSelfAdjoint.mul_norm_sq_le_re_inner_of_proj_Iio_eq_zero (hA : IsSelfAdjoint A)
    {c : ℝ} (h : (A.spectralPVM hA).proj (Set.Iio c) measurableSet_Iio = 0) (x : A.domain) :
    c * ‖(x : H)‖ ^ 2 ≤ re ⟪A x, x⟫_ℂ := by
  obtain ⟨v, hv⟩ := (mem_graph_iff_exists_cayley hA.neg_I_mem_resolventSet).mp (A.mem_graph x)
  exact mul_norm_sq_le_re_inner_of_diag_Iio hA (congrArg Prod.fst hv).symm
    ((ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _ _).mp h v)

/-- **Upper form bound from spectral support.** If the spectral measure of a self-adjoint partial
linear map `A` vanishes on `(c, ∞)`, then `re ⟪A x, x⟫ ≤ c ‖x‖²` for every `x ∈ dom A`. -/
theorem _root_.IsSelfAdjoint.re_inner_le_mul_norm_sq_of_proj_Ioi_eq_zero (hA : IsSelfAdjoint A)
    {c : ℝ} (h : (A.spectralPVM hA).proj (Set.Ioi c) measurableSet_Ioi = 0) (x : A.domain) :
    re ⟪A x, x⟫_ℂ ≤ c * ‖(x : H)‖ ^ 2 := by
  obtain ⟨v, hv⟩ := (mem_graph_iff_exists_cayley hA.neg_I_mem_resolventSet).mp (A.mem_graph x)
  exact re_inner_le_mul_norm_sq_of_diag_Ioi hA (congrArg Prod.fst hv).symm
    ((ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _ _).mp h v)

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
    simpa using congr($((hA.commute_cayley_spectralPVM_proj B hB).eq) v)
  refine ⟨P.proj B hB v, ?_, ?_⟩
  · have hxv : v - A.cayley v = x := congrArg Prod.fst hv
    rw [hUP, ← ContinuousLinearMap.map_sub, hxv, hPx]
  · rw [← P.enorm_sq_proj_apply Bᶜ hB.compl, ← mul_apply_eq_comp,
      P.proj_mul_eq_zero_of_disjoint hB.compl hB disjoint_compl_left]
    simp

/-- **Lower form bound on a spectral range.** If `B ⊆ [β, ∞)`, then `β ‖x‖² ≤ re ⟪A x, x⟫` for
every `x ∈ dom A` in the range of the spectral projection `P(B)`. -/
theorem _root_.IsSelfAdjoint.mul_norm_sq_le_re_inner_of_mem_range_proj (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B) {β : ℝ} (hβ : B ⊆ Set.Ici β) {x : A.domain}
    (hx : (x : H) ∈ ((A.spectralPVM hA).proj B hB).range) :
    β * ‖(x : H)‖ ^ 2 ≤ re ⟪A x, x⟫_ℂ := by
  obtain ⟨v, hxv, hv⟩ := exists_eq_sub_cayley_diag_compl_eq_zero hA hB hx
  have hsub : Set.Iio β ⊆ Bᶜ := fun s hs hsB => not_le.mpr hs (Set.mem_Ici.mp (hβ hsB))
  exact mul_norm_sq_le_re_inner_of_diag_Iio hA hxv (measure_mono_null hsub hv)

/-- **Upper form bound on a spectral range.** If `B ⊆ (-∞, α]`, then `re ⟪A x, x⟫ ≤ α ‖x‖²` for
every `x ∈ dom A` in the range of the spectral projection `P(B)`. -/
theorem _root_.IsSelfAdjoint.re_inner_le_mul_norm_sq_of_mem_range_proj (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B) {α : ℝ} (hα : B ⊆ Set.Iic α) {x : A.domain}
    (hx : (x : H) ∈ ((A.spectralPVM hA).proj B hB).range) :
    re ⟪A x, x⟫_ℂ ≤ α * ‖(x : H)‖ ^ 2 := by
  obtain ⟨v, hxv, hv⟩ := exists_eq_sub_cayley_diag_compl_eq_zero hA hB hx
  have hsub : Set.Ioi α ⊆ Bᶜ := fun s hs hsB => not_le.mpr hs (Set.mem_Iic.mp (hα hsB))
  exact re_inner_le_mul_norm_sq_of_diag_Ioi hA hxv (measure_mono_null hsub hv)

end LinearPMap
