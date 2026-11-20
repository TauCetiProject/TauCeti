/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Map
public import TauCeti.MeasureTheory.Function.SpecialFunctions.Cayley

/-!
# The spectral measure of an unbounded self-adjoint operator

Let `A` be a self-adjoint partial linear map on a complex Hilbert space `H`. Its Cayley transform
`U = (A - i)(A + i)⁻¹` (`LinearPMap.cayley`) is a bounded unitary operator, so it has a spectral
measure on its spectrum, a subset of the unit circle. The inverse Cayley map
`w ↦ i (1 + w) / (1 - w)` (`Complex.invCayley`) sends the circle with `1` removed onto the real
line, and pushing the spectral measure of `U` forward along it gives a projection-valued measure
on `ℝ`: the **spectral measure** `P_A` of `A` (`LinearPMap.spectralPVM`).

The point `1`, where the inverse Cayley map is singular, carries no mass: the spectral projection
of a point is the eigenprojection there, and `1` is never an eigenvalue of a Cayley transform.
The value assigned to `1` is therefore immaterial. With this, every nonreal `z` satisfies the
**resolvent formula**: the resolvent `(z - A)⁻¹` is the spectral integral of `s ↦ (z - s)⁻¹`, so
`⟪ξ, (z - A)⁻¹ ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)` for the diagonal measures `μ_ξ` of `P_A`. Consequently
the spectral projections preserve the domain of `A` and commute with `A` there, hence with every
resolvent of `A`, and the spectral measure is carried by the spectrum: it vanishes on every Borel
set of real resolvent points.

## Main definitions

* `LinearPMap.spectralPVM`: the spectral measure of a self-adjoint partial linear map.

## Main results

* `LinearPMap.cayley_spectralPVM_proj_singleton_one`,
  `LinearPMap.cayley_diagMeasure_singleton_one`: the spectral measure of the Cayley transform
  does not charge `1`.
* `IsSelfAdjoint.integral_spectralPVM_eq_resolvent`,
  `IsSelfAdjoint.integral_spectralPVM_resolventSymbol`: `∫ (z - s)⁻¹ dP_A(s) = (z - A)⁻¹`.
* `IsSelfAdjoint.inner_resolvent_self_eq_integral`: the resolvent formula
  `⟪ξ, (z - A)⁻¹ ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`.
* `IsSelfAdjoint.commute_spectralPVM_proj_resolvent`,
  `IsSelfAdjoint.spectralPVM_proj_apply_mem_domain`,
  `IsSelfAdjoint.apply_spectralPVM_proj_apply`: spectral projections commute with every
  resolvent, preserve the domain and commute with `A` there.
* `IsSelfAdjoint.spectralPVM_proj_eq_zero_of_subset_resolventSet`: the spectral measure vanishes
  on Borel sets of resolvent points.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 13.30 (the spectral
  theorem for unbounded self-adjoint operators, through the Cayley transform).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265 (2012),
  Section 13.1 (the Cayley transform).
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped InnerProductSpace ComplexConjugate

open Complex

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-! ### The Cayley singular point -/

/-- **The Cayley singular point carries no spectral mass.** If `-i` is a resolvent point of `A`
and its Cayley transform is normal, the spectral projection of `{1}` vanishes, since `1` is not
an eigenvalue of the Cayley transform. -/
theorem cayley_spectralPVM_proj_singleton_one [IsStarNormal A.cayley] (h : -I ∈ A.resolventSet) :
    A.cayley.spectralPVM.proj (Subtype.val ⁻¹' {1}) (measurableSet_preimage_val_singleton 1) =
      0 := by
  rw [ContinuousLinearMap.spectralPVM_proj_singleton_eq_zero_iff, Module.End.hasEigenvalue_iff,
    not_not, Submodule.eq_bot_iff]
  intro x hx
  rw [Module.End.mem_eigenspace_iff, one_smul, ContinuousLinearMap.coe_coe] at hx
  exact (cayley_apply_eq_self_iff h).1 hx

/-- Every diagonal measure of the spectral measure of the Cayley transform assigns mass zero to
the singular point `1`. -/
theorem cayley_diagMeasure_singleton_one [IsStarNormal A.cayley] (h : -I ∈ A.resolventSet)
    (ξ : H) : A.cayley.diagMeasure ξ (Subtype.val ⁻¹' {1}) = 0 := by
  rw [← ContinuousLinearMap.spectralPVM_diag]
  exact (ProjValMeasure.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _ _).1
    (cayley_spectralPVM_proj_singleton_one h) ξ

/-! ### The spectral measure -/

/-- The **spectral measure** of a self-adjoint partial linear map `A`: the spectral measure of its
unitary Cayley transform, pushed forward to `ℝ` along the inverse Cayley map. -/
def spectralPVM (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) : ProjValMeasure ℝ H :=
  letI := hA.isStarNormal_cayley
  A.cayley.spectralPVM.map (fun w => invCayley w) (measurable_invCayley.comp measurable_subtype_coe)

/-- The spectral measure of `A` is the spectral measure of its Cayley transform, pushed forward
along the inverse Cayley map. -/
theorem spectralPVM_eq_map [IsStarNormal A.cayley] (hA : IsSelfAdjoint A) :
    A.spectralPVM hA =
      A.cayley.spectralPVM.map (fun w => invCayley w)
        (measurable_invCayley.comp measurable_subtype_coe) :=
  (rfl)

/-- The spectral projection `P_A(B)` is the spectral projection of the Cayley transform on the
preimage of `B` under the inverse Cayley map. -/
theorem spectralPVM_proj [IsStarNormal A.cayley] (hA : IsSelfAdjoint A) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (A.spectralPVM hA).proj B hB =
      A.cayley.spectralPVM.proj ((fun w : _root_.spectrum ℂ A.cayley => invCayley w) ⁻¹' B)
        (hB.preimage (measurable_invCayley.comp measurable_subtype_coe)) := by
  rw [spectralPVM_eq_map hA, ProjValMeasure.map_proj]

/-- The diagonal measures of `P_A` are those of the Cayley transform, pushed forward along the
inverse Cayley map. -/
theorem spectralPVM_diag [IsStarNormal A.cayley] (hA : IsSelfAdjoint A) (ξ : H) :
    (A.spectralPVM hA).diag ξ =
      (A.cayley.diagMeasure ξ).map fun w : _root_.spectrum ℂ A.cayley => invCayley w := by
  rw [spectralPVM_eq_map hA, ProjValMeasure.map_diag, ContinuousLinearMap.spectralPVM_diag]

end LinearPMap

namespace IsSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-! ### The resolvent formula -/

/-- **The resolvent is a spectral integral.** For nonreal `z`, integrating any bounded Borel
symbol equal to `s ↦ (z - s)⁻¹` against the spectral measure of `A` gives the resolvent
`(z - A)⁻¹`. -/
theorem integral_spectralPVM_eq_resolvent (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (f : BoundedBorelFunction ℝ) (hf : ∀ s : ℝ, f s = (z - s)⁻¹) :
    (A.spectralPVM hA).integral f = A.resolvent z := by
  have := hA.isStarNormal_cayley
  have hzA : z ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simpa using hz)
  have hI : -I ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simp)
  set U := A.cayley with hU
  rw [LinearPMap.spectralPVM_eq_map hA, ProjValMeasure.integral_map,
    ContinuousLinearMap.integral_spectralPVM]
  set g := BoundedBorelFunction.compStarAlgHom' (fun w : spectrum ℂ U => invCayley w)
    (measurable_invCayley.comp measurable_subtype_coe) f
  set w : BoundedBorelFunction (spectrum ℂ U) :=
    BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ U))
  have hw : U.borelCalculus w = U := U.borelCalculus_restrict_id
  -- On the Cayley side `z - A` has the symbol `w ↦ (z - i) - (z + i) w`, and `g` times this symbol
  -- is `1 - w` away from the null point `1`.
  have hgp : U.borelCalculus (g * (algebraMap ℂ _ (z - I) - (z + I) • w)) =
      U.borelCalculus (1 - w) := by
    refine U.borelCalculus_congr_ae fun ξ => ?_
    filter_upwards
      [measure_eq_zero_iff_ae_notMem.1 (LinearPMap.cayley_diagMeasure_singleton_one hI ξ)]
      with v hv
    have hv1 : (v : ℂ) ≠ 1 := hv
    have hnorm : ‖(v : ℂ)‖ = 1 := spectrum.norm_eq_one_of_unitary hA.cayley_mem_unitary v.2
    have hne : z - (invCayley v : ℂ) ≠ 0 := fun h => hz (by simpa using congrArg im h)
    have key : (z - I) - (z + I) * v = (z - invCayley v) * (1 - v) := by
      rw [ofReal_invCayley hnorm]
      field_simp [sub_ne_zero.2 hv1.symm]
      ring
    simp [g, w, hf, key, hne]
  -- Both operators invert `z - A` on its range, which is all of `H`.
  ext y
  obtain ⟨x, rfl⟩ := (LinearPMap.isResolventAt_resolvent hzA).smul_sub_surjective y
  dsimp only
  rw [LinearPMap.resolvent_smul_sub_apply hzA]
  -- The graph of `A` is `{(v - U v, i (v + U v))}`.
  obtain ⟨v, hv⟩ := (LinearPMap.mem_graph_iff_exists_cayley hI).1 (A.mem_graph x)
  simp only [Prod.mk.injEq] at hv
  have hx : z • (x : H) - A x = U.borelCalculus (algebraMap ℂ _ (z - I) - (z + I) • w) v := by
    rw [map_sub, AlgHomClass.commutes, map_smul, hw, ← hv.1, ← hv.2]
    simp [Algebra.algebraMap_eq_smul_one]
    module
  rw [hx, ← mul_apply_eq_comp, ← map_mul, hgp, map_sub, map_one, hw, ← hv.1, hU]
  simp

/-- **The resolvent is a spectral integral.** For nonreal `z`, the spectral integral of the
resolvent symbol `s ↦ (z - s)⁻¹` (`BoundedBorelFunction.resolventSymbol`) is the resolvent
`(z - A)⁻¹`. -/
theorem integral_spectralPVM_resolventSymbol (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    (A.spectralPVM hA).integral (BoundedBorelFunction.resolventSymbol z hz) = A.resolvent z :=
  hA.integral_spectralPVM_eq_resolvent hz _ (BoundedBorelFunction.resolventSymbol_apply z hz)

/-- **The resolvent formula.** For nonreal `z`, the diagonal matrix elements of the resolvent
are the Cauchy–Stieltjes transforms of the diagonal spectral measures:
`⟪ξ, (z - A)⁻¹ ξ⟫ = ∫ (z - s)⁻¹ dμ_ξ(s)`. -/
theorem inner_resolvent_self_eq_integral (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (ξ : H) : ⟪ξ, A.resolvent z ξ⟫_ℂ = ∫ s, (z - s)⁻¹ ∂((A.spectralPVM hA).diag ξ) := by
  rw [← hA.integral_spectralPVM_resolventSymbol hz,
    ← ProjValMeasure.integral_diag_eq_inner_integral]
  simp only [BoundedBorelFunction.resolventSymbol_apply]

/-! ### Spectral projections, resolvents and the domain -/

/-- Every spectral projection of `A` commutes with every resolvent at a nonreal point. -/
private theorem commute_spectralPVM_proj_resolvent_of_im_ne_zero (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B) {z : ℂ} (hz : z.im ≠ 0) :
    Commute ((A.spectralPVM hA).proj B hB) (A.resolvent z) := by
  rw [← hA.integral_spectralPVM_resolventSymbol hz, ← ProjValMeasure.integral_indicator]
  exact (Commute.all _ _).map _

/-- Every spectral projection of `A` maps the domain of `A` into itself. -/
theorem spectralPVM_proj_apply_mem_domain (hA : IsSelfAdjoint A) {B : Set ℝ}
    (hB : MeasurableSet B) {x : H} (hx : x ∈ A.domain) :
    (A.spectralPVM hA).proj B hB x ∈ A.domain := by
  have hI : I ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simp)
  -- The domain is the range of the resolvent `R(i)`, which commutes with `P_A(B)`.
  have hx' : A.resolvent I (I • x - A ⟨x, hx⟩) = x :=
    LinearPMap.resolvent_smul_sub_apply hI ⟨x, hx⟩
  rw [← hx', ← mul_apply_eq_comp,
    (commute_spectralPVM_proj_resolvent_of_im_ne_zero hA hB (by simp)).eq, mul_apply_eq_comp]
  exact LinearPMap.resolvent_mem_domain hI _

/-- Every spectral projection of `A` commutes with `A` on its domain:
`A (P_A(B) x) = P_A(B) (A x)`. -/
theorem apply_spectralPVM_proj_apply (hA : IsSelfAdjoint A) {B : Set ℝ} (hB : MeasurableSet B)
    (x : A.domain) :
    A ⟨(A.spectralPVM hA).proj B hB x, hA.spectralPVM_proj_apply_mem_domain hB x.2⟩ =
      (A.spectralPVM hA).proj B hB (A x) := by
  set P := (A.spectralPVM hA).proj B hB
  have hI : I ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simp)
  -- `P` commutes with `R(i) = (i - A)⁻¹`, whose range is the domain of `A`.
  have hPx : P x = A.resolvent I (P (I • (x : H) - A x)) := by
    rw [← mul_apply_eq_comp,
      ← (commute_spectralPVM_proj_resolvent_of_im_ne_zero hA hB (z := I) (by simp)).eq,
      mul_apply_eq_comp, LinearPMap.resolvent_smul_sub_apply hI]
  have hx : (⟨P x, hA.spectralPVM_proj_apply_mem_domain hB x.2⟩ : A.domain) =
      ⟨A.resolvent I (P (I • (x : H) - A x)), LinearPMap.resolvent_mem_domain hI _⟩ :=
    Subtype.ext hPx
  rw [hx, LinearPMap.apply_resolvent hI, ← hPx, map_sub, map_smul, sub_sub_cancel]

/-- Every spectral projection of `A` commutes with every resolvent of `A`, at real resolvent
points as well as nonreal ones. -/
theorem commute_spectralPVM_proj_resolvent (hA : IsSelfAdjoint A) {B : Set ℝ}
    (hB : MeasurableSet B) {z : ℂ} (hz : z ∈ A.resolventSet) :
    Commute ((A.spectralPVM hA).proj B hB) (A.resolvent z) := by
  -- `P` commutes with `z - A` on the domain, and therefore with its inverse `R(z)`.
  ext y
  obtain ⟨x, rfl⟩ := (LinearPMap.isResolventAt_resolvent hz).smul_sub_surjective y
  rw [mul_apply_eq_comp, mul_apply_eq_comp, LinearPMap.resolvent_smul_sub_apply hz, map_sub,
    map_smul, ← hA.apply_spectralPVM_proj_apply hB x]
  exact (LinearPMap.resolvent_smul_sub_apply hz
    ⟨_, hA.spectralPVM_proj_apply_mem_domain hB x.2⟩).symm

/-! ### Spectral support -/

/-- **The spectral measure is carried by the spectrum.** The spectral projection of a Borel set
of real resolvent points of `A` vanishes. -/
theorem spectralPVM_proj_eq_zero_of_subset_resolventSet (hA : IsSelfAdjoint A) {B : Set ℝ}
    (hB : MeasurableSet B) (hBA : ∀ s ∈ B, (s : ℂ) ∈ A.resolventSet) :
    (A.spectralPVM hA).proj B hB = 0 := by
  have := hA.isStarNormal_cayley
  have hI : -I ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero (by simp)
  rw [LinearPMap.spectralPVM_proj]
  refine ProjValMeasure.proj_eq_zero_of_subset _ (fun w hw => ?_) _ _
    (LinearPMap.cayley_spectralPVM_proj_singleton_one hI)
  -- A point `w ≠ 1` of the spectrum of the Cayley transform has `invCayley w` in `σ(A)`.
  by_contra hw1
  have hnorm : ‖(w : ℂ)‖ = 1 := spectrum.norm_eq_one_of_unitary hA.cayley_mem_unitary w.2
  have hmem := (LinearPMap.mem_spectrum_cayley_iff hI hw1).1 w.2
  rw [← ofReal_invCayley hnorm, LinearPMap.mem_spectrum_iff] at hmem
  exact hmem (hBA _ hw)

end IsSelfAdjoint
