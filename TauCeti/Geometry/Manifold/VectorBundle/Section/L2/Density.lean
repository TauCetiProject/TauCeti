/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.L2.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteSpan
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Smooth sections are dense in geometric L²

For a finite-rank real smooth bundle with continuous fibre inner products over a smooth manifold,
the compactly supported smooth sections have dense image under `ContMDiffSection.toL2` in the
geometric L² space, for every Borel measure that is finite on compact sets. The base need not be
compact.

An L² section `u` orthogonal to every compactly supported smooth section vanishes. Near each
point, `TauCeti.exists_compactlySupported_spanning_nhds` supplies compactly supported smooth
sections spanning every nearby fibre. Testing against their products with scalar test
functions, Mathlib's fundamental lemma `ae_eq_zero_of_integral_contMDiff_smul_eq_zero` shows that
`u` pairs to zero with each of them almost everywhere, so `u` vanishes almost everywhere near each
point, hence almost everywhere. No orientation, boundarylessness, smoothness of the metric, or
positivity assumption on the measure is needed.

Density is a prerequisite for realizing differential operators as unbounded operators on the
geometric L² space: the smooth image is a candidate domain, provided the operator descends to
almost-everywhere classes.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3.
-/

public noncomputable section

open Bundle MeasureTheory Set TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [ContinuousFiberNorm F V] {μ : Measure M} [IsFiniteMeasureOnCompacts μ]

/-- An L² section orthogonal to all compactly supported smooth sections vanishes. The fibre
metric may be merely continuous, and the measure need not have full support. -/
theorem eq_zero_of_forall_inner_toL2_eq_zero {u : LpSection ℝ F V 2 μ}
    (hu : ∀ s : compactlySupported I F ∞ V, ⟪toL2 μ s, u⟫_ℝ = 0) : u = 0 := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- `u` pairs to zero almost everywhere with each compactly supported smooth section.
  have hpair (s : compactlySupported I F ∞ V) :
      ∀ᵐ x ∂μ, ⟪(s : Cₛ^∞⟮I; F, V⟯) x, u x⟫_ℝ = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I
      (integrable_inner_l2 s u).locallyIntegrable fun φ hφ _ ↦ ?_
    let ψ : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have h := hu ⟨ψ • (s : Cₛ^∞⟮I; F, V⟯), smul_function_mem_compactlySupported ψ s.property⟩
    rw [inner_toL2_left] at h
    refine (integral_congr_ae (.of_forall fun x ↦ ?_)).trans h
    exact ((congrArg (fun v : V x ↦ ⟪v, u x⟫_ℝ) (smul_apply ψ _ x)).trans
      (real_inner_smul_left _ _ _)).symm
  -- Near each point, such sections span every fibre, so `u` vanishes there almost everywhere.
  have hzero : ∀ᵐ x ∂μ, u x = 0 := by
    rw [ae_iff]
    refine measure_null_of_locally_null _ fun x _ ↦ ?_
    obtain ⟨s, hs, hspan⟩ :=
      TauCeti.exists_compactlySupported_spanning_nhds (I := I) (F := F) (V := V) x
    refine ⟨_, inter_mem_nhdsWithin _ hspan, measure_mono_null ?_
      (ae_iff.1 (ae_all_iff.2 fun i ↦ hpair ⟨s i, hs i⟩))⟩
    rintro y ⟨hy, hyspan⟩ hall
    have hker : Submodule.span ℝ (range fun i ↦ s i y) ≤ LinearMap.ker (innerₛₗ ℝ (u y)) :=
      Submodule.span_le.2 <| by
        rintro _ ⟨i, rfl⟩
        simpa [real_inner_comm] using hall i
    exact hy (inner_self_eq_zero.1 (hker (hyspan.symm ▸ Submodule.mem_top)))
  refine (LpSection.ext_iff _ _).2 ?_
  filter_upwards [hzero, LpSection.coeFn_zero (𝕜 := ℝ) (F := F) (E := V) (μ := μ)]
    with x hx h0
  rw [hx, h0]

/-- Compactly supported smooth sections of a finite-rank real bundle over a smooth manifold are
dense in its geometric L² space, for every Borel measure that is finite on compact sets. -/
theorem denseRange_toL2 :
    DenseRange (toL2 μ : compactlySupported I F ∞ V → LpSection ℝ F V 2 μ) := by
  rw [DenseRange, ← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  exact eq_zero_of_forall_inner_toL2_eq_zero fun s ↦
    Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ s) hu

end ContMDiffSection
