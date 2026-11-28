/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Restriction
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Examples of intrinsic restriction of native bundle distributions

On proper open intervals of the real line, intrinsic test extension carries an actual intrinsic
density to a nonzero ambient coefficient, and restricting a point mass directly or in two steps
through an intermediate interval gives the same nonzero pairing.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology ContMDiffSection
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney CompactConvergenceCLM

namespace TauCeti.Examples.BundleDistributionRestriction

/-- A genuine proper open interval in the real line. -/
def properRealOpen : Opens ℝ := ⟨Set.Ioo (-2) 2, isOpen_Ioo⟩

/-- The intrinsic dual densities of the trivial line bundle on the proper interval. -/
abbrev openHomBundle := TauCeti.DensityBundle.openHomBundle (I := 𝓘(ℝ, ℝ))
  (V := Bundle.Trivial ℝ ℝ) (U := properRealOpen)

/-- Extension transports an actual intrinsic density to an ambient coefficient with value one. -/
theorem exists_nonzero_actual_density_extension :
    ∃ s : TauCeti.BundleTest 𝓘(ℝ, ℝ) (ℝ →L[ℝ] ℝ) openHomBundle,
      (TauCeti.BundleDistribution.testExtensionCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ)
        (V := Bundle.Trivial ℝ ℝ) s 0) 1 (Module.finBasis ℝ ℝ) = 1 := by
  let x : properRealOpen := ⟨0, by constructor <;> norm_num⟩
  let b := Module.finBasis ℝ ℝ
  let μ : TauCeti.DensityBundle 𝓘(ℝ, ℝ) properRealOpen x := b.density 1
  let ℓ : openHomBundle x :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight μ
  obtain ⟨s, hs⟩ := TauCeti.BundleTest.exists_apply_eq (I := 𝓘(ℝ, ℝ)) (F := ℝ →L[ℝ] ℝ)
    (V := openHomBundle) x ℓ
  refine ⟨s, ?_⟩
  rw [TauCeti.BundleDistribution.testExtensionCLM_apply_of_mem s x, hs,
    TauCeti.DensityBundle.openHomEquiv_apply]
  -- The scalar-to-density smulRight map is now evaluated at one in the chosen density frame.
  change (1 : ℝ) * ((b.density 1) b) = 1
  rw [b.density_apply_self]
  norm_num

/-- A larger proper interval for the independently instantiated nesting client. -/
def outer : Opens ℝ := ⟨Set.Ioo (-3) 3, isOpen_Ioo⟩

/-- A strictly smaller proper interval. -/
def inner : Opens ℝ := ⟨Set.Ioo (-1) 1, isOpen_Ioo⟩

/-- The smaller interval is contained in the larger proper interval. -/
theorem inner_le_outer : inner ≤ outer := by
  intro x hx
  exact ⟨lt_trans (by norm_num) hx.1, lt_trans hx.2 (by norm_num)⟩

/-- The native continuous inclusion of an open subset. -/
abbrev inclusion {M : Type*} [TopologicalSpace M] (U : Opens M) : C(U, M) :=
  ⟨Subtype.val, continuous_subtypeVal⟩
/-- The smaller interval viewed as an open subset of the larger interval. -/
abbrev nestedOpen : Opens outer := Opens.comap (inclusion outer) inner
/-- Intrinsic dual densities of the double-pullback bundle. -/
abbrev doubleHomBundle := TauCeti.DensityBundle.openHomBundle (I := 𝓘(ℝ, ℝ))
  (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) (U := nestedOpen)

private def coordinateFunctional : (TauCeti.DensityBundle.ambientHomBundle (I := 𝓘(ℝ, ℝ))
    (V := Bundle.Trivial ℝ ℝ)) 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
    ((trivializationAt (ℝ →L[ℝ] ℝ) (TauCeti.DensityBundle.ambientHomBundle (I := 𝓘(ℝ, ℝ))
    (V := Bundle.Trivial ℝ ℝ)) 0).continuousLinearMapAt ℝ 0)

/-- An actual native bundle point distribution, tested in a continuous local coefficient frame. -/
def actualPointMass : TauCeti.BundleDistribution 𝓘(ℝ, ℝ) ℝ ℝ (Bundle.Trivial ℝ ℝ) :=
  TauCeti.BundleTest.delta (I := 𝓘(ℝ, ℝ)) (F := ℝ →L[ℝ] ℝ) 0 coordinateFunctional

/-- A nonzero intrinsic test witnesses the independent direct/successive nesting law on actual
proper double-pullback carriers; both pairings are one. -/
theorem exists_proper_nested_density_pairing_one :
    ∃ s : TauCeti.BundleTest 𝓘(ℝ, ℝ) (ℝ →L[ℝ] ℝ) doubleHomBundle,
      TauCeti.BundleDistribution.nestedComparisonCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ)
        (V := Bundle.Trivial ℝ ℝ) inner_le_outer
        (TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ)
          (V := Bundle.Trivial ℝ ℝ) (U := inner) actualPointMass) s = 1 ∧
      TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (M := outer)
        (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) (U := nestedOpen)
        (TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ)
          (V := Bundle.Trivial ℝ ℝ) (U := outer) actualPointMass) s = 1 := by
  let xD : outer := ⟨0, by constructor <;> norm_num⟩
  let xN : nestedOpen := ⟨xD, by constructor <;> norm_num⟩
  let e := trivializationAt (ℝ →L[ℝ] ℝ) (TauCeti.DensityBundle.ambientHomBundle (I := 𝓘(ℝ, ℝ))
    (V := Bundle.Trivial ℝ ℝ)) 0
  let vM := e.symmL ℝ 0 (ContinuousLinearMap.id ℝ ℝ)
  let ψ := (TauCeti.DensityBundle.openHomEquiv (I := 𝓘(ℝ, ℝ)) (M := outer)
      (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) xN).trans
    (TauCeti.DensityBundle.openHomEquiv (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial ℝ ℝ) xD)
  obtain ⟨s, hs⟩ := TauCeti.BundleTest.exists_apply_eq (I := 𝓘(ℝ, ℝ)) (F := ℝ →L[ℝ] ℝ)
    (V := doubleHomBundle) xN (ψ.symm vM)
  have hright : TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (M := outer)
      (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) (U := nestedOpen)
      (TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ)
        (V := Bundle.Trivial ℝ ℝ) (U := outer) actualPointMass) s = 1 := by
    rw [TauCeti.BundleDistribution.restrictCLM_apply,
      TauCeti.BundleDistribution.restrictCLM_apply]
    rw [actualPointMass, TauCeti.BundleTest.delta_apply]
    rw [TauCeti.BundleDistribution.testExtensionCLM_apply_of_mem _ xD,
      TauCeti.BundleDistribution.testExtensionCLM_apply_of_mem s xN, hs]
    -- The two public density-evaluation laws give the actual composed fibre equivalence ψ.
    change coordinateFunctional (ψ (ψ.symm vM)) = 1
    rw [ψ.apply_symm_apply]
    unfold coordinateFunctional
    -- coordinateFunctional is evaluation at one after this continuous local frame map.
    change (e.continuousLinearMapAt ℝ 0
      (e.symmL ℝ 0 (ContinuousLinearMap.id ℝ ℝ))) 1 = 1
    rw [e.continuousLinearMapAt_symmL (mem_baseSet_trivializationAt _ _ _)]
    rfl
  refine ⟨s, ?_, hright⟩
  exact (congrArg (fun T ↦ T s)
    (TauCeti.BundleDistribution.restrictCLM_nested (I := 𝓘(ℝ, ℝ)) (F := ℝ)
      (V := Bundle.Trivial ℝ ℝ) inner_le_outer actualPointMass)).trans hright

end TauCeti.Examples.BundleDistributionRestriction
