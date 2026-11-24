/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Reducing
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Resolvent
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# The spectral measure of a self-adjoint partial linear map

Let `A` be a self-adjoint partial linear map on a complex Hilbert space `H`, and let `U` be its
Cayley transform `LinearPMap.cayley A`, the unitary operator `(A - i)(A + i)⁻¹`. The spectral
measure of `U` is a projection-valued measure on the spectrum of `U`, which lies on the unit
circle. The **spectral measure** `P_A = LinearPMap.spectralPVM A hA` of `A` is its pushforward to
the real line along the real inverse Cayley coordinate (`Complex.inverseCayleyCoord`)

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
`P_A`: `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`. For nonreal `z` the resolvent is moreover the
spectral integral of the bounded Borel symbol `s ↦ (z - s)⁻¹` itself. The resolvent formula
characterizes `P_A`: by Stieltjes inversion a finite measure on `ℝ` is determined by its
Cauchy–Stieltjes transform on the upper half-plane, so any projection-valued measure on `ℝ` whose
diagonal measures represent the resolvent there is `P_A`. In particular, for a bounded
self-adjoint operator `T`, viewed as an everywhere defined partial linear map, `P_T` is the
spectral measure of `T` on its real spectrum, pushed forward to `ℝ` along the real part.

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

*Spectral restrictions.* Since the spectral projection `P_A(B)` intertwines `A` with itself, its
range, the spectral subspace of `B`, reduces `A`, and the part of `A` in it is self-adjoint. If
`P_A` vanishes on `B ∩ (c - δ, c + δ)`, every domain vector `x` of the spectral subspace splits as
`x₁ + x₂` with spectral support in `(-∞, c - δ]` and `[c + δ, ∞)`; the form bounds give
`δ ‖xᵢ‖ ≤ ‖c xᵢ - A xᵢ‖`, and the two pieces are orthogonal, so `δ ‖x‖ ≤ ‖c x - A x‖`. Hence `c` is
a resolvent point of the part of `A` in the spectral subspace, with resolvent of norm at most
`δ⁻¹`.

## Main declarations

* `LinearPMap.spectralPVM A hA`: the spectral measure of a self-adjoint partial linear map, a
  projection-valued measure on `ℝ`.
* `LinearPMap.cayley_spectralPVM_proj_singleton_one`,
  `LinearPMap.cayley_diagMeasure_singleton_one`: the spectral measure of the Cayley transform
  does not charge the point `1`.
* `IsSelfAdjoint.inner_resolvent_apply_eq_integral`: the resolvent formula
  `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`.
* `IsSelfAdjoint.neg_inner_resolvent_apply_eq_resolventTransform`: the same formula as
  `-⟪ξ, R(z) ξ⟫ = resolventTransform μ_ξ z`, in the convention `(s - z)⁻¹`.
* `IsSelfAdjoint.integral_spectralPVM_eq_resolvent`,
  `IsSelfAdjoint.integral_spectralPVM_resolventSymbol`: for nonreal `z`,
  `∫ (z - s)⁻¹ dP_A(s) = R(z)`.
* `IsSelfAdjoint.eq_spectralPVM_iff`: the resolvent formula on the upper half-plane characterizes
  the spectral measure.
* `IsSelfAdjoint.spectralPVM_toPMap_top`: for a bounded self-adjoint operator, the spectral measure
  is the bounded spectral measure pushed forward along the real part.
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
* `IsSelfAdjoint.isReducing_range_spectralPVM_proj`,
  `IsSelfAdjoint.isSelfAdjoint_restrict_range_spectralPVM_proj`: spectral subspaces reduce `A`, and
  the part of `A` in a spectral subspace is self-adjoint.
* `IsSelfAdjoint.mul_norm_le_norm_smul_sub_of_mem_range_spectralPVM_proj`: if `P_A` vanishes on
  `B ∩ (c - δ, c + δ)`, then `δ ‖x‖ ≤ ‖c x - A x‖` on the domain vectors of the spectral subspace
  of `B`.
* `IsSelfAdjoint.mem_resolventSet_restrict_range_spectralPVM_proj`,
  `IsSelfAdjoint.norm_resolvent_restrict_range_spectralPVM_proj_le`: under the same gap, with
  `δ > 0`, `c` is a resolvent point of the part of `A` in that spectral subspace, and the resolvent
  there has norm at most `δ⁻¹`.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 13.30 (the spectral
  theorem for unbounded self-adjoint operators, through the Cayley transform).
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

/-- **The Cayley singular point carries no spectral mass.** If `-i` is a resolvent point of `A`
and its Cayley transform is normal, the spectral projection of `{1}` vanishes, since `1` is not
an eigenvalue of the Cayley transform. -/
theorem cayley_spectralPVM_proj_singleton_one [IsStarNormal A.cayley] (h : -I ∈ A.resolventSet) :
    A.cayley.spectralPVM.proj (Subtype.val ⁻¹' {1}) (measurableSet_preimage_val_singleton 1) =
      0 :=
  (A.cayley.spectralPVM_proj_preimage_singleton_eq_zero_iff 1).mpr fun x hx =>
    (cayley_apply_eq_self_iff h).mp (by simpa using hx)

/-- Every diagonal measure of the spectral measure of the Cayley transform assigns mass zero to
the singular point `1`. -/
theorem cayley_diagMeasure_singleton_one [IsStarNormal A.cayley] (h : -I ∈ A.resolventSet)
    (ξ : H) : A.cayley.diagMeasure ξ (Subtype.val ⁻¹' {1}) = 0 := by
  rw [← ContinuousLinearMap.spectralPVM_diag]
  exact (ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _ _).1
    (cayley_spectralPVM_proj_singleton_one h) ξ

/-- The **spectral measure** of a self-adjoint partial linear map `A`: the spectral measure of its
Cayley transform `U`, pushed forward to the real line along the real inverse Cayley coordinate
`Complex.inverseCayleyCoord w = re (i (1 + w) / (1 - w))`. The pole `w = 1` carries no spectral
mass of `U` (`LinearPMap.cayley_spectralPVM_proj_singleton_one`). -/
def spectralPVM (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) : TauCeti.ProjValMeasure ℝ H :=
  haveI := hA.isStarNormal_cayley
  A.cayley.spectralPVM.map (fun w => inverseCayleyCoord w) (by fun_prop)

/-- The spectral measure of `A` is the pushforward of the spectral measure of its Cayley transform
along the real inverse Cayley coordinate. -/
theorem _root_.IsSelfAdjoint.spectralPVM_eq_map (hA : IsSelfAdjoint A) :
    haveI := hA.isStarNormal_cayley
    A.spectralPVM hA = A.cayley.spectralPVM.map (fun w => inverseCayleyCoord w) (by fun_prop) :=
  (rfl)

/-- The spectral projection of `A` on a Borel set `B` is the spectral projection of its Cayley
transform on the preimage of `B` under the real inverse Cayley coordinate. -/
@[simp]
theorem _root_.IsSelfAdjoint.spectralPVM_proj (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) :
    haveI := hA.isStarNormal_cayley
    (A.spectralPVM hA).proj B hB =
      A.cayley.spectralPVM.proj ((fun w : _root_.spectrum ℂ A.cayley => inverseCayleyCoord w) ⁻¹' B)
        ((by fun_prop : Measurable _) hB) := by
  rw [hA.spectralPVM_eq_map, ProjValMeasure.map_proj]

/-- The diagonal measures of the spectral measure of `A` are the pushforwards of the diagonal
measures of its Cayley transform along the real inverse Cayley coordinate. -/
@[simp]
theorem _root_.IsSelfAdjoint.spectralPVM_diag (hA : IsSelfAdjoint A) (ξ : H) :
    haveI := hA.isStarNormal_cayley
    (A.spectralPVM hA).diag ξ =
      (A.cayley.diagMeasure ξ).map fun w : _root_.spectrum ℂ A.cayley => inverseCayleyCoord w := by
  rw [hA.spectralPVM_eq_map, ProjValMeasure.map_diag, ContinuousLinearMap.spectralPVM_diag]

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
    exact cayley_diagMeasure_singleton_one hA.neg_I_mem_resolventSet ξ
  refine integral_congr_ae ?_
  filter_upwards [h1] with w hw
  have h1w : 1 - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [inverseCayleyCoord_def, (hA.ofReal_re_inverseCayley_eq_and_mem_spectrum w.property hw).1]
  field_simp
  ring

/-- In the resolvent convention `(A - z)⁻¹ = -R(z)`, the diagonal matrix element
`⟪ξ, (A - z)⁻¹ ξ⟫` is the resolvent transform `∫ (s - z)⁻¹ dμ_ξ(s)` of the diagonal measure of
the spectral measure. -/
theorem _root_.IsSelfAdjoint.neg_inner_resolvent_apply_eq_resolventTransform
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z ∈ A.resolventSet) (ξ : H) :
    -⟪ξ, A.resolvent z ξ⟫_ℂ = resolventTransform ((A.spectralPVM hA).diag ξ) z := by
  rw [hA.inner_resolvent_apply_eq_integral hz, resolventTransform_eq_neg_integral_inv_sub]

/-- **The resolvent is a spectral integral.** For nonreal `z`, integrating any bounded Borel
symbol equal to `s ↦ (z - s)⁻¹` against the spectral measure of `A` gives the resolvent
`(z - A)⁻¹`. -/
theorem _root_.IsSelfAdjoint.integral_spectralPVM_eq_resolvent (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (f : BoundedBorelFunction ℝ) (hf : ∀ s : ℝ, f s = (z - s)⁻¹) :
    (A.spectralPVM hA).integral f = A.resolvent z := by
  have := hA.isStarNormal_cayley
  have hzA : z ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simpa using hz)
  have hI : -I ∈ A.resolventSet := hA.neg_I_mem_resolventSet
  set U := A.cayley with hU
  rw [hA.spectralPVM_eq_map, ProjValMeasure.integral_map,
    ContinuousLinearMap.integral_spectralPVM]
  set g := BoundedBorelFunction.compStarAlgHom'
    (fun w : _root_.spectrum ℂ U => inverseCayleyCoord w) (by fun_prop) f
  set w : BoundedBorelFunction (_root_.spectrum ℂ U) :=
    BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (_root_.spectrum ℂ U))
  have hw : U.borelCalculus w = U := U.borelCalculus_restrict_id
  -- On the Cayley side `z - A` has the symbol `w ↦ (z - i) - (z + i) w`, and `g` times this symbol
  -- is `1 - w` away from the null point `1`.
  have hgp : U.borelCalculus (g * (algebraMap ℂ _ (z - I) - (z + I) • w)) =
      U.borelCalculus (1 - w) := by
    refine U.borelCalculus_congr_ae fun ξ => ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (cayley_diagMeasure_singleton_one hI ξ)]
      with v hv
    have hv1 : (v : ℂ) ≠ 1 := hv
    have hnorm : ‖(v : ℂ)‖ = 1 := spectrum.norm_eq_one_of_unitary hA.cayley_mem_unitary v.property
    have hne : z - (inverseCayleyCoord v : ℂ) ≠ 0 := fun h => hz (by simpa using congrArg im h)
    have key : (z - I) - (z + I) * v = (z - inverseCayleyCoord v) * (1 - v) := by
      rw [ofReal_inverseCayleyCoord hnorm]
      field_simp [sub_ne_zero.2 hv1.symm]
      ring
    simp [g, w, hf, key, hne]
  -- Both operators invert `z - A` on its range, which is all of `H`.
  ext y
  obtain ⟨x, rfl⟩ := (isResolventAt_resolvent hzA).smul_sub_surjective y
  dsimp only
  rw [resolvent_smul_sub_apply hzA]
  -- The graph of `A` is `{(v - U v, i (v + U v))}`.
  obtain ⟨v, hv⟩ := (mem_graph_iff_exists_cayley hI).1 (A.mem_graph x)
  simp only [Prod.mk.injEq] at hv
  have hx : z • (x : H) - A x = U.borelCalculus (algebraMap ℂ _ (z - I) - (z + I) • w) v := by
    rw [_root_.map_sub, AlgHomClass.commutes, _root_.map_smul, hw, ← hv.1, ← hv.2]
    simp [Algebra.algebraMap_eq_smul_one]
    module
  rw [hx, ← mul_apply_eq_comp, ← map_mul, hgp, _root_.map_sub, map_one, hw, ← hv.1, hU]
  simp

/-- **The resolvent is a spectral integral.** For nonreal `z`, the spectral integral of the
resolvent symbol `s ↦ (z - s)⁻¹` (`BoundedBorelFunction.resolventSymbol`) is the resolvent
`(z - A)⁻¹`. -/
theorem _root_.IsSelfAdjoint.integral_spectralPVM_resolventSymbol (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) :
    (A.spectralPVM hA).integral (BoundedBorelFunction.resolventSymbol z hz) = A.resolvent z :=
  hA.integral_spectralPVM_eq_resolvent hz _ (BoundedBorelFunction.resolventSymbol_apply z hz)

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
    (cayley_diagMeasure_singleton_one hA.neg_I_mem_resolventSet ξ)
  -- A point `w ≠ 1` of the spectrum of `U` has its inverse Cayley image in the spectrum of `A`.
  by_contra h1
  obtain ⟨hre, hmem⟩ := hA.ofReal_re_inverseCayley_eq_and_mem_spectrum w.property h1
  rw [Set.mem_preimage, inverseCayleyCoord_def] at hw
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
  rw [inverseCayleyCoord_def] at hw
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
  rw [inverseCayleyCoord_def] at hw
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

/-- **Uniqueness of the spectral measure.** A projection-valued measure `P` on `ℝ` is the spectral
measure of a self-adjoint partial linear map `A` iff its diagonal measures represent the
resolvent of `A` on the upper half-plane: `⟪ξ, R(z) ξ⟫ = ∫ (z - s)⁻¹ dP_ξ(s)` whenever `0 < im z`.
-/
theorem _root_.IsSelfAdjoint.eq_spectralPVM_iff (hA : IsSelfAdjoint A)
    (P : TauCeti.ProjValMeasure ℝ H) :
    P = A.spectralPVM hA ↔
      ∀ z : ℂ, 0 < z.im → ∀ ξ : H, ⟪ξ, A.resolvent z ξ⟫_ℂ = ∫ s : ℝ, (z - s)⁻¹ ∂P.diag ξ := by
  -- A projection-valued measure is determined by its diagonal measures, and by Stieltjes inversion
  -- a finite measure on `ℝ` by its Cauchy–Stieltjes transform on the upper half-plane.
  refine ⟨?_, fun h => ProjValMeasure.ext_of_diag fun ξ =>
    Measure.ext_of_resolventTransform fun z hz => ?_⟩
  · rintro rfl z hz ξ
    exact hA.inner_resolvent_apply_eq_integral (hA.mem_resolventSet_of_im_ne_zero hz.ne') ξ
  -- Mathlib's resolvent transform has the kernel `(s - z)⁻¹ = -(z - s)⁻¹`.
  rw [resolventTransform_eq_neg_integral_inv_sub, ← h z hz ξ,
    hA.neg_inner_resolvent_apply_eq_resolventTransform (hA.mem_resolventSet_of_im_ne_zero hz.ne')]

/-- **Compatibility with the bounded spectral measure.** For a bounded self-adjoint operator `T`,
viewed as an everywhere defined partial linear map, the spectral measure is the spectral measure
of `T` on its spectrum, which is real, pushed forward to `ℝ` along the real part. -/
theorem _root_.IsSelfAdjoint.spectralPVM_toPMap_top {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    haveI := hT.isStarNormal
    ((T : H →ₗ[ℂ] H).toPMap ⊤).spectralPVM (isSelfAdjoint_toPMap_top hT) =
      T.spectralPVM.map (fun w => (w : ℂ).re) (by fun_prop) := by
  have := hT.isStarNormal
  symm
  refine ((isSelfAdjoint_toPMap_top hT).eq_spectralPVM_iff _).mpr fun z hz ξ => ?_
  have hzT : z ∈ _root_.resolventSet ℂ T :=
    Set.notMem_compl_iff.mp fun h => hz.ne' (hT.im_eq_zero_of_mem_spectrum h)
  -- On the spectrum `w = re w`, so the symbol is `w ↦ (z - w)⁻¹`.
  have hsymb : (fun w : _root_.spectrum ℂ T => (z - ((w : ℂ).re : ℂ))⁻¹) =
      fun w : _root_.spectrum ℂ T => (z - (w : ℂ))⁻¹ := by
    funext w
    rw [← hT.mem_spectrum_eq_re w.property]
  rw [ContinuousLinearMap.resolvent_toPMap_top T hzT, ProjValMeasure.map_diag,
    integral_map (by fun_prop) (by fun_prop), ContinuousLinearMap.spectralPVM_diag, hsymb,
    ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc _ _ (fun w => (z - w)⁻¹)
      (continuousOn_inv_sub_of_mem_resolventSet hzT), cfc_inv_sub_eq_resolvent hzT]

/-! ### Spectral restrictions -/

/-- **Spectral subspaces reduce the operator.** The range of every spectral projection of a
self-adjoint partial linear map `A` reduces `A`. -/
theorem _root_.IsSelfAdjoint.isReducing_range_spectralPVM_proj (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) : A.IsReducing ((A.spectralPVM hA).proj B hB).range := by
  rw [isReducing_iff_intertwines_starProjection, ProjValMeasure.starProjection_range_proj]
  exact hA.intertwines_spectralPVM_proj B hB

/-- **Self-adjoint spectral restriction.** The part of a self-adjoint partial linear map `A` in
the range of a spectral projection of `A` is self-adjoint. -/
theorem _root_.IsSelfAdjoint.isSelfAdjoint_restrict_range_spectralPVM_proj (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint
      (A.restrict (hA.isReducing_range_spectralPVM_proj B hB).isInvariant.apply_mem) :=
  (hA.isReducing_range_spectralPVM_proj B hB).isSelfAdjoint_restrict hA

/-- On the range of a spectral projection `P(C)` with `C` inside one of the half-lines
`(-∞, c - δ]` or `[c + δ, ∞)`, the form bounds give `δ ‖x‖² ≤ |re ⟪c x - A x, x⟫|`, hence
`δ ‖x‖ ≤ ‖c x - A x‖` by the Cauchy–Schwarz inequality. -/
private theorem mul_norm_le_norm_smul_sub_of_subset_Iic_or_Ici (hA : IsSelfAdjoint A)
    {C : Set ℝ} (hC : MeasurableSet C) {c δ : ℝ}
    (hCδ : C ⊆ Set.Iic (c - δ) ∨ C ⊆ Set.Ici (c + δ)) {x : A.domain}
    (hx : (x : H) ∈ ((A.spectralPVM hA).proj C hC).range) :
    δ * ‖(x : H)‖ ≤ ‖(c : ℂ) • (x : H) - A x‖ := by
  have hre : re ⟪(c : ℂ) • (x : H) - A x, x⟫_ℂ = c * ‖(x : H)‖ ^ 2 - re ⟪A x, x⟫_ℂ := by
    rw [inner_sub_left, inner_smul_left, conj_ofReal, sub_re, re_ofReal_mul,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  have hq : δ * ‖(x : H)‖ ^ 2 ≤ ‖(c : ℂ) • (x : H) - A x‖ * ‖(x : H)‖ := by
    refine le_trans ?_ ((abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _))
    rcases hCδ with h | h
    · have := hA.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj hC h hx
      exact le_abs.mpr (Or.inl (by linarith))
    · have := hA.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj hC h hx
      exact le_abs.mpr (Or.inr (by linarith))
  rcases (norm_nonneg (x : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith) hpos

/-- **Lower bound on a spectral subspace across a gap.** If the spectral measure of a
self-adjoint partial linear map `A` vanishes on `B ∩ (c - δ, c + δ)`, then
`δ ‖x‖ ≤ ‖c x - A x‖` for every `x ∈ dom A` in the range of the spectral projection `P(B)`. -/
theorem _root_.IsSelfAdjoint.mul_norm_le_norm_smul_sub_of_mem_range_spectralPVM_proj
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B) {c δ : ℝ}
    (hgap : (A.spectralPVM hA).proj (B ∩ Set.Ioo (c - δ) (c + δ))
      (hB.inter measurableSet_Ioo) = 0)
    {x : A.domain} (hx : (x : H) ∈ ((A.spectralPVM hA).proj B hB).range) :
    δ * ‖(x : H)‖ ≤ ‖(c : ℂ) • (x : H) - A x‖ := by
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (norm_nonneg _)).trans (norm_nonneg _)
  set P := A.spectralPVM hA
  have h₁ : MeasurableSet (B ∩ Set.Iic (c - δ)) := hB.inter measurableSet_Iic
  have h₂ : MeasurableSet (B ∩ Set.Ici (c + δ)) := hB.inter measurableSet_Ici
  have hd : Disjoint (B ∩ Set.Iic (c - δ)) (B ∩ Set.Ici (c + δ)) :=
    Set.disjoint_left.mpr fun s hs₁ hs₂ => by grind
  -- Up to the null part `B ∩ (c - δ, c + δ)`, `B` is the union of its parts `B₁` below `c - δ`
  -- and `B₂` above `c + δ`; the squared norms of the two components add up.
  have hsplit : P.proj B hB = P.proj _ (h₁.union h₂) := by
    rw [← add_zero (P.proj _ (h₁.union h₂)), ← hgap,
      ← P.proj_union _ _ (Set.disjoint_left.mpr fun s hs hs' => by grind)]
    exact P.proj_congr (Set.ext fun s => by grind) _ _
  have hpyth (ξ : H) : ‖P.proj _ (h₁.union h₂) ξ‖ ^ 2 =
      ‖P.proj _ h₁ ξ‖ ^ 2 + ‖P.proj _ h₂ ξ‖ ^ 2 := by
    rw [P.norm_sq_proj_apply, P.norm_sq_proj_apply, P.norm_sq_proj_apply, measure_union hd h₂,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  -- Each component `P(Bᵢ) x` lies in the domain, where `c - A` maps it to `P(Bᵢ) (c x - A x)`
  -- with norm at least `δ ‖P(Bᵢ) x‖`.
  have hpart {C : Set ℝ} (hC : MeasurableSet C)
      (hCδ : C ⊆ Set.Iic (c - δ) ∨ C ⊆ Set.Ici (c + δ)) :
      (δ * ‖P.proj C hC x‖) ^ 2 ≤ ‖P.proj C hC ((c : ℂ) • (x : H) - A x)‖ ^ 2 := by
    have hI := hA.intertwines_spectralPVM_proj C hC
    have h := mul_norm_le_norm_smul_sub_of_subset_Iic_or_Ici hA hC hCδ
      (x := ⟨_, hI.mem_domain x⟩) ⟨x, rfl⟩
    rw [← hI.apply_eq x, ← ContinuousLinearMap.map_smul, ← ContinuousLinearMap.map_sub] at h
    exact pow_le_pow_left₀ (by positivity) h 2
  have hx' : ‖(x : H)‖ ^ 2 = ‖P.proj _ h₁ x‖ ^ 2 + ‖P.proj _ h₂ x‖ ^ 2 := by
    obtain ⟨z, hz⟩ := hx
    rw [← hpyth, ← hsplit, ← hz, ContinuousLinearMap.coe_coe, P.proj_apply_proj]
  have hy := pow_le_pow_left₀ (norm_nonneg _) (P.norm_proj_apply_le _ (h₁.union h₂)
    ((c : ℂ) • (x : H) - A x)) 2
  rw [hpyth] at hy
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  have hb₁ := hpart h₁ (Or.inl Set.inter_subset_right)
  have hb₂ := hpart h₂ (Or.inr Set.inter_subset_right)
  rw [mul_pow] at hb₁ hb₂ ⊢
  rw [hx']
  linarith

/-- The lower bound `δ ‖x‖ ≤ ‖c x - A x‖` on the domain of the part of `A` in the range of
`P(B)`, read off from `IsSelfAdjoint.mul_norm_le_norm_smul_sub_of_mem_range_spectralPVM_proj`. -/
private theorem mul_norm_le_norm_smul_sub_restrict_range_spectralPVM_proj
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B) {c δ : ℝ}
    (hgap : (A.spectralPVM hA).proj (B ∩ Set.Ioo (c - δ) (c + δ))
      (hB.inter measurableSet_Ioo) = 0)
    (x : (A.restrict (hA.isReducing_range_spectralPVM_proj B hB).isInvariant.apply_mem).domain) :
    δ * ‖(x : ((A.spectralPVM hA).proj B hB).range)‖ ≤
      ‖(c : ℂ) • (x : ((A.spectralPVM hA).proj B hB).range) -
        A.restrict (hA.isReducing_range_spectralPVM_proj B hB).isInvariant.apply_mem x‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe, Submodule.coe_sub, Submodule.coe_smul,
    coe_restrict_apply]
  exact hA.mul_norm_le_norm_smul_sub_of_mem_range_spectralPVM_proj hB hgap
    (x := ⟨_, (mem_restrict_domain _).1 x.property⟩) x.val.property

/-- **Gap resolvent for a spectral restriction.** If the spectral measure of a self-adjoint
partial linear map `A` vanishes on `B ∩ (c - δ, c + δ)` with `δ > 0`, then the real point `c` is a
resolvent point of the part of `A` in the range of the spectral projection `P(B)`. -/
theorem _root_.IsSelfAdjoint.mem_resolventSet_restrict_range_spectralPVM_proj
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B) {c δ : ℝ} (hδ : 0 < δ)
    (hgap : (A.spectralPVM hA).proj (B ∩ Set.Ioo (c - δ) (c + δ))
      (hB.inter measurableSet_Ioo) = 0) :
    (c : ℂ) ∈
      (A.restrict (hA.isReducing_range_spectralPVM_proj B hB).isInvariant.apply_mem).resolventSet :=
  (hA.isSelfAdjoint_restrict_range_spectralPVM_proj B hB).mem_resolventSet_of_norm_le hδ
    (mul_norm_le_norm_smul_sub_restrict_range_spectralPVM_proj hA hB hgap)

/-- **Gap resolvent bound for a spectral restriction.** If the spectral measure of a self-adjoint
partial linear map `A` vanishes on `B ∩ (c - δ, c + δ)` with `δ > 0`, then the resolvent at `c` of
the part of `A` in the range of the spectral projection `P(B)` has norm at most `δ⁻¹`. -/
theorem _root_.IsSelfAdjoint.norm_resolvent_restrict_range_spectralPVM_proj_le
    (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B) {c δ : ℝ} (hδ : 0 < δ)
    (hgap : (A.spectralPVM hA).proj (B ∩ Set.Ioo (c - δ) (c + δ))
      (hB.inter measurableSet_Ioo) = 0) :
    ‖(A.restrict (hA.isReducing_range_spectralPVM_proj B hB).isInvariant.apply_mem).resolvent
      (c : ℂ)‖ ≤ δ⁻¹ :=
  (hA.isSelfAdjoint_restrict_range_spectralPVM_proj B hB).norm_resolvent_le_of_norm_le hδ
    (mul_norm_le_norm_smul_sub_restrict_range_spectralPVM_proj hA hB hgap)

end LinearPMap
