/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Current.Mass
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Mass of the point current

The point current evaluates the scalar coefficient of an intrinsic test zero-form at a point.
On a Hausdorff manifold its mass is one, and its variational local mass on a set is one
precisely at interior points of the set. At a boundary point every smooth test supported in the
set vanishes. This accounts for the open-set hypothesis in the mass measure formula.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
-/

public noncomputable section

open Bundle Set Filter Topology
open scoped Manifold ContDiff ENNReal

namespace TauCeti.Current

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- The unit point current at `x`, acting on the scalar coefficient of a test zero-form. -/
def dirac (x : M) : Current I M 0 :=
  letI := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
    (E := (TangentSpace I x [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
    (F := DensityBundle I M x)
  BundleTest.delta x
    ((ContinuousAlternatingMap.apply ℝ (TangentSpace I x) ℝ ![]).comp
      (I.formDensityDoubleDualEquiv 0 x).symm.toContinuousLinearMap)

/-- The point current reads the scalar value of the test at its point. -/
@[simp]
theorem dirac_apply (x : M) (s : TestForm I M 0) : dirac x s = TestForm.formEquiv s x ![] := by
  let := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
    (E := (TangentSpace I x [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
    (F := DensityBundle I M x)
  rw [dirac, BundleTest.delta_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousAlternatingMap.apply_apply,
    ← TestForm.formDensityDoubleDualEquiv_formEquiv_apply s x,
    ContinuousLinearEquiv.symm_apply_apply]

/-- On a Hausdorff manifold, the distributional support of the unit point current is its point. -/
@[simp]
theorem dsupport_dirac [T2Space M] (x : M) : BundleTest.dsupport (dirac (I := I) x) = {x} := by
  rw [dirac]
  apply BundleTest.dsupport_delta
  intro h
  let α := ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I x) (Fin 0) (1 : ℝ)
  have hval := DFunLike.congr_fun h (I.formDensityDoubleDualEquiv 0 x α)
  simp [α] at hval

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {U : Set M} {x : M}

/-- Point evaluation has mass at most one for any fibre metric. -/
theorem mass_dirac_le_one (x : M) : mass (dirac (I := I) x) ≤ 1 := by
  refine mass_le_iff.2 fun s hs ↦ ?_
  rw [dirac_apply, ← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((by simpa using (TestForm.formEquiv s x).le_opNorm ![] :
    ‖TestForm.formEquiv s x ![]‖ ≤ ‖TestForm.formEquiv s x‖).trans (hs x))

/-- Point evaluation has locally finite mass. -/
@[simp]
theorem hasLocallyFiniteMass_dirac (x : M) : HasLocallyFiniteMass (dirac (I := I) x) :=
  hasLocallyFiniteMass_of_mass_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (mass_dirac_le_one x))

/-- The variational local mass of the point current vanishes outside the interior. -/
@[simp]
theorem localMass_dirac_of_notMem_interior (hx : x ∉ interior U) :
    localMass (dirac (I := I) x) U = 0 := by
  refine le_antisymm (localMass_le_iff.2 fun s hs _ ↦ ?_) bot_le
  have hα : IsSmoothForm I ∞ (fun y ↦ TestForm.formEquiv s y) :=
    (isSmoothForm_def _ _).2 (TestForm.formEquiv s).contMDiff
  have hz : TestForm.formEquiv s x = 0 := by
    by_contra h
    apply hx
    apply interior_maximal (t := {y | TestForm.formEquiv s y ≠ 0}) _
      hα.isClosed_zeroSet.isOpen_compl h
    exact fun y hy ↦ hs (subset_closure fun hsy ↦ hy (TestForm.formEquiv_apply_eq_zero_iff.2 hsy))
  rw [dirac_apply, hz]
  exact (eNorm_zero (E := ℝ)).le

/-- The variational local mass of the point current is one at each interior point. -/
@[simp]
theorem localMass_dirac_of_mem_interior [T2Space M] (hx : x ∈ interior U) :
    localMass (dirac (I := I) x) U = 1 := by
  refine le_antisymm (localMass_le_mass.trans (mass_dirac_le_one x)) ?_
  obtain ⟨ρ, hρ, hone, hc, hsupp, hρ₁⟩ :=
    isCompact_singleton.exists_contMDiff_one_nhds_tsupport_subset I isOpen_interior
      (singleton_subset_iff.2 hx)
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨ρ, hρ⟩
  let η := (SmoothForm.ofFunction (I := I) (1 : C^∞⟮I, M; ℝ⟯)).toContMDiffSection
  let α := BundleTest.ofCompactlySupported I _ _ ⟨χ • η,
    ContMDiffSection.smul_function_mem_compactlySupported_of_hasCompactSupport χ hc η⟩
  let s : TestForm I M 0 := TestForm.formEquiv.symm α
  have hα (y : M) : TestForm.formEquiv s y =
      ρ y • ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I y) (Fin 0) (1 : ℝ) := by
    simp only [s, ContinuousLinearEquiv.apply_symm_apply, α, BundleTest.coe_ofCompactlySupported,
      ContMDiffSection.smul_apply, η, SmoothForm.toContMDiffSection_apply,
      SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply_eq_constOfIsEmpty]
    rfl
  have hs : closure {y | s y ≠ 0} ⊆ U := by
    refine (closure_minimal (t := tsupport ρ) (fun y hy ↦ ?_) (isClosed_tsupport _)).trans
      (hsupp.trans interior_subset)
    by_contra hn
    exact hy (TestForm.formEquiv_apply_eq_zero_iff.1 (by
      rw [hα, image_eq_zero_of_notMem_tsupport hn, zero_smul]))
  have hb := eNorm_apply_le_localMass (T := dirac x) hs fun y ↦ by
    rw [hα, norm_smul_of_nonneg (hρ₁ y).1
      (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I y) (Fin 0) (1 : ℝ)),
      ContinuousAlternatingMap.norm_constOfIsEmpty, norm_one, mul_one]
    exact (hρ₁ y).2
  simpa only [dirac_apply, hα, hone.self_of_nhdsSet x (mem_singleton x), one_smul,
    ContinuousAlternatingMap.constOfIsEmpty_apply, eNorm_one] using hb

/-- The unit point current has mass one. -/
@[simp]
theorem mass_dirac [T2Space M] (x : M) : mass (dirac (I := I) x) = 1 := by
  simpa using localMass_dirac_of_mem_interior (I := I) (U := univ) (x := x) (by simp)

end TauCeti.Current
