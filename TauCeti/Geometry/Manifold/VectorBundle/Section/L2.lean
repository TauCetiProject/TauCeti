/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.LpSection.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteSpan
import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Smooth sections are dense in geometric L²

On a compact smooth manifold, a smooth section of a bundle with continuous fibre inner
products defines a square-integrable section for every locally finite Borel measure.
`ContMDiffSection.toL2` sends the section to its almost-everywhere class in `TauCeti.LpSection`.
For finite-rank real smooth bundles this map has dense range.

The density proof uses a finite smooth family spanning every fibre and the fundamental lemma
for scalar test functions. An L² section orthogonal to every smooth section pairs to zero
almost everywhere with each member of that family, hence vanishes. No orientation,
boundarylessness, smoothness of the metric, or positivity assumption on the measure is needed.
This gives a dense smooth domain for differential operators in the geometric L² space.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3.
-/

public noncomputable section

open Bundle MeasureTheory Set TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContinuousFiberNorm F V]
  {μ : Measure M} [IsLocallyFiniteMeasure μ] {n : ℕ∞ω}

/-- A smooth section on a compact base defines a geometric L² class, with the given fibre
inner products and measure. -/
def toL2 (μ : Measure M) [IsLocallyFiniteMeasure μ] :
    Cₛ^n⟮I; F, V⟯ →ₗ[ℝ] TauCeti.LpSection ℝ F V 2 μ where
  toFun s :=
    let hnorm := Continuous.norm_bundle_of_continuousFiberNorm s.contMDiff.continuous
    TauCeti.LpSection.mk s (.of_continuous s.contMDiff.continuous)
      (hnorm.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_add' s t := by
    rw [TauCeti.LpSection.mk_add, TauCeti.LpSection.mk_eq_mk_iff]
    exact .of_forall fun _ ↦ rfl
  map_smul' c s := by
    rw [TauCeti.LpSection.mk_smul, TauCeti.LpSection.mk_eq_mk_iff]
    exact .of_forall fun _ ↦ rfl

/-- The L² class of a smooth section agrees almost everywhere with that section. -/
theorem coeFn_toL2 (s : Cₛ^n⟮I; F, V⟯) :
    ∀ᵐ x ∂μ, toL2 μ s x = s x :=
  TauCeti.LpSection.coeFn_mk _ _

/-- Pairing a smooth section with an L² section is the integral of the fibre inner product. -/
theorem inner_toL2_left (s : Cₛ^n⟮I; F, V⟯) (u : TauCeti.LpSection ℝ F V 2 μ) :
    ⟪toL2 μ s, u⟫_ℝ = ∫ x, ⟪s x, u x⟫_ℝ ∂μ := by
  rw [TauCeti.LpSection.inner_def]
  exact integral_congr_ae ((coeFn_toL2 s).mono fun x hx ↦ congrArg (fun v ↦ ⟪v, u x⟫_ℝ) hx)

/-- The pointwise pairing of a smooth section with an L² section is integrable on a compact
base. -/
theorem integrable_inner_l2 (s : Cₛ^n⟮I; F, V⟯) (u : TauCeti.LpSection ℝ F V 2 μ) :
    Integrable (fun x ↦ ⟪s x, u x⟫_ℝ) μ :=
  (TauCeti.LpSection.integrable_inner (toL2 μ s) u).congr
    ((coeFn_toL2 s).mono fun x hx ↦ congrArg (fun v ↦ ⟪v, u x⟫_ℝ) hx)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M]
  [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- An L² section orthogonal to all smooth sections vanishes. The fibre metric may be merely
continuous, and the measure need not have full support. -/
theorem eq_zero_of_forall_inner_toL2_eq_zero {u : TauCeti.LpSection ℝ F V 2 μ}
    (hu : ∀ s : Cₛ^∞⟮I; F, V⟯, ⟪toL2 μ s, u⟫_ℝ = 0) : u = 0 := by
  obtain ⟨r, s, hspan⟩ := TauCeti.exists_fin_spanning_contMDiffSection (I := I) (F := F) (V := V)
  have hs (i : Fin r) : ∀ᵐ x ∂μ, ⟪s i x, u x⟫_ℝ = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      (integrable_inner_l2 (s i) u).locallyIntegrable fun φ hφ _ ↦ ?_
    let ψ : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have h := hu (ψ • s i)
    rw [inner_toL2_left] at h
    convert h using 1
    apply integral_congr_ae
    exact .of_forall fun x ↦
      (congrArg (fun v : V x ↦ ⟪v, u x⟫_ℝ) (smul_apply ψ (s i) x) |>.trans
        (real_inner_smul_left _ _ _)).symm
  refine (TauCeti.LpSection.ext_iff _ _).2 ?_
  filter_upwards [ae_all_iff.2 hs, TauCeti.LpSection.coeFn_zero
    (𝕜 := ℝ) (F := F) (E := V) (μ := μ)] with x hx hzero
  rw [hzero]
  have horth : u x ∈ (Submodule.span ℝ (range fun i ↦ s i x))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    refine Submodule.span_induction (fun v hv ↦ ?_) ?_ ?_ ?_ hv
    · obtain ⟨i, rfl⟩ := hv
      exact hx i
    · simp
    · intro v w _ _ hv hw
      simp [inner_add_left, hv, hw]
    · intro c v _ hv
      simp [real_inner_smul_left, hv]
  simpa [hspan x] using horth

/-- Smooth sections of a finite-rank real bundle over a compact smooth manifold are dense in
its geometric L² space for every locally finite Borel measure. -/
theorem denseRange_toL2 :
    DenseRange (toL2 μ : Cₛ^∞⟮I; F, V⟯ → TauCeti.LpSection ℝ F V 2 μ) := by
  rw [DenseRange, ← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  exact eq_zero_of_forall_inner_toL2_eq_zero fun s ↦
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ s) hu

end ContMDiffSection
