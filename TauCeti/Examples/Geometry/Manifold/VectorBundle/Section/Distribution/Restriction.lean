/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Restriction
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Nonzero open-extension and intrinsic-restriction examples

The clients use genuine proper opens and an actual intrinsic density, a boundary point of a
manifold with corners, zero-rank fibres, and the empty open subset. The nested example compares
independently instantiated intrinsic restrictions on actual double-pullback test carriers.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology ContMDiffSection
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney CompactConvergenceCLM

namespace TauCeti.Examples.BundleDistributionRestriction

/-- A genuine proper open interval in the real line. -/
def properRealOpen : Opens ℝ := ⟨Set.Ioo (-2) 2, isOpen_Ioo⟩
/-- The native continuous inclusion of the proper interval. -/
abbrev properRealIncl : C(properRealOpen, ℝ) := ⟨Subtype.val, continuous_subtypeVal⟩

/-- A proper-open test extends to a nonzero value at zero and vanishes at an exterior point. -/
theorem exists_nonzero_proper_open_extension :
    ∃ s : TauCeti.BundleTest 𝓘(ℝ, ℝ) ℝ (properRealIncl *ᵖ (Bundle.Trivial ℝ ℝ)),
      TauCeti.BundleTest.extendByZeroCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (V := Bundle.Trivial ℝ ℝ)
        (U := properRealOpen) s 0 = 1 ∧
      TauCeti.BundleTest.extendByZeroCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (V := Bundle.Trivial ℝ ℝ)
        (U := properRealOpen) s 3 = 0
        := by
  let x : properRealOpen := ⟨0, by constructor <;> norm_num⟩
  obtain ⟨s, hs⟩ := TauCeti.BundleTest.exists_apply_eq (I := 𝓘(ℝ, ℝ)) (F := ℝ)
    (V := properRealIncl *ᵖ (Bundle.Trivial ℝ ℝ)) x (1 : ℝ)
  refine ⟨s, ?_, ?_⟩
  · erw [TauCeti.BundleTest.extendByZeroCLM_apply_of_mem s x]
    exact hs
  · apply TauCeti.BundleTest.extendByZeroCLM_apply_of_notMem s
    norm_num [properRealOpen]

/-- A native test with zero-rank fibre is zero. -/
theorem zero_rank_test (s : TauCeti.BundleTest 𝓘(ℝ, ℝ) (Fin 0 → ℝ) (Bundle.Trivial ℝ (Fin 0 → ℝ))) :
    s = 0 := by
  apply TauCeti.BundleTest.ext
  intro x
  exact Subsingleton.elim _ _

/-- Tests on the empty open subset extend to zero. -/
theorem empty_open_extension :
    let U : Opens ℝ := ⊥
    let c : C(U, ℝ) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ s : TauCeti.BundleTest 𝓘(ℝ, ℝ) ℝ (c *ᵖ (Bundle.Trivial ℝ ℝ)),
      TauCeti.BundleTest.extendByZeroCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (V := Bundle.Trivial ℝ ℝ) (U :=
        U) s = 0 := by
  intro U c s
  apply TauCeti.BundleTest.ext
  intro x
  exact TauCeti.BundleTest.extendByZeroCLM_apply_of_notMem s (by simp [U])

/-- The actual intrinsic dual-density coefficient family on the proper interval. -/
abbrev localCoefficients := TauCeti.DensityBundle.localCoefficients (I := 𝓘(ℝ, ℝ))
  (V := Bundle.Trivial ℝ ℝ) (U := properRealOpen)

/-- Extension transports an actual intrinsic density to an ambient coefficient with value one. -/
theorem exists_nonzero_actual_density_extension :
    ∃ s : TauCeti.BundleTest 𝓘(ℝ, ℝ) (ℝ →L[ℝ] ℝ)
      localCoefficients,
      (TauCeti.BundleDistribution.testExtensionCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (V := Bundle.Trivial ℝ
        ℝ) s 0) 1
        (Module.finBasis ℝ ℝ) = 1 := by
  let x : properRealOpen := ⟨0, by constructor <;> norm_num⟩
  let b := Module.finBasis ℝ ℝ
  let μ : TauCeti.DensityBundle 𝓘(ℝ, ℝ) properRealOpen x := b.density 1
  let ℓ : localCoefficients x :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight μ
  obtain ⟨s, hs⟩ := TauCeti.BundleTest.exists_apply_eq (I := 𝓘(ℝ, ℝ)) (F := ℝ →L[ℝ] ℝ)
    (V := localCoefficients) x ℓ
  refine ⟨s, ?_⟩
  erw [TauCeti.BundleDistribution.testExtensionCLM_apply_of_mem s x]
  rw [hs, TauCeti.DensityBundle.openHomEquiv_apply]
  -- The scalar-to-density smulRight map is now evaluated at one in the chosen density frame.
  change (1 : ℝ) * ((b.density 1) b) = 1
  rw [b.density_apply_self]
  norm_num

/-- Native extension is nonzero at the boundary point of the Euclidean half-space. -/
theorem exists_nonzero_boundary_test_extension :
    letI : T2Space (EuclideanHalfSpace 1) := by
      dsimp [EuclideanHalfSpace]
      infer_instance
    let U : Opens (EuclideanHalfSpace 1) := ⊤
    let c : C(U, EuclideanHalfSpace 1) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∃ s : TauCeti.BundleTest (modelWithCornersEuclideanHalfSpace 1) ℝ (c *ᵖ (Bundle.Trivial
      (EuclideanHalfSpace 1) ℝ)),
      TauCeti.BundleTest.extendByZeroCLM (I := modelWithCornersEuclideanHalfSpace 1) (F := ℝ)
        (V := Bundle.Trivial (EuclideanHalfSpace 1) ℝ) s 0 = 1 := by
  let : T2Space (EuclideanHalfSpace 1) := by
    dsimp [EuclideanHalfSpace]
    infer_instance
  intro U c
  let x : U := ⟨0, Set.mem_univ _⟩
  obtain ⟨s, hs⟩ := TauCeti.BundleTest.exists_apply_eq (I := modelWithCornersEuclideanHalfSpace 1)
    (F := ℝ)
    (V := c *ᵖ (Bundle.Trivial (EuclideanHalfSpace 1) ℝ)) x (1 : ℝ)
  refine ⟨s, ?_⟩
  erw [TauCeti.BundleTest.extendByZeroCLM_apply_of_mem s x]
  exact hs


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
/-- Actual intrinsic coefficients on the double-pullback bundle. -/
abbrev doubleCoefficients := TauCeti.DensityBundle.localCoefficients (I := 𝓘(ℝ, ℝ))
  (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) (U := nestedOpen)

private def coordinateFunctional : (TauCeti.DensityBundle.ambientCoefficients (I := 𝓘(ℝ, ℝ))
    (V := Bundle.Trivial ℝ ℝ)) 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
    ((trivializationAt (ℝ →L[ℝ] ℝ) (TauCeti.DensityBundle.ambientCoefficients (I := 𝓘(ℝ, ℝ))
    (V := Bundle.Trivial ℝ ℝ)) 0).continuousLinearMapAt ℝ 0)

/-- An actual native bundle point distribution, tested in a continuous local coefficient frame. -/
def actualPointMass : TauCeti.BundleDistribution 𝓘(ℝ, ℝ) ℝ ℝ (Bundle.Trivial ℝ ℝ) :=
  TauCeti.BundleTest.delta (I := 𝓘(ℝ, ℝ)) (F := ℝ →L[ℝ] ℝ) 0 coordinateFunctional

/-- A nonzero intrinsic test witnesses the independent direct/successive nesting law on actual
proper double-pullback carriers; both pairings are one. -/
theorem exists_proper_nested_density_pairing_one :
    ∃ s : TauCeti.BundleTest 𝓘(ℝ, ℝ) (ℝ →L[ℝ] ℝ) doubleCoefficients,
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
  let e := trivializationAt (ℝ →L[ℝ] ℝ) (TauCeti.DensityBundle.ambientCoefficients (I := 𝓘(ℝ, ℝ))
    (V := Bundle.Trivial ℝ ℝ)) 0
  let vM := e.symmL ℝ 0 (ContinuousLinearMap.id ℝ ℝ)
  let ψ := (TauCeti.DensityBundle.openHomEquiv (I := 𝓘(ℝ, ℝ)) (M := outer)
      (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) xN).trans
    (TauCeti.DensityBundle.openHomEquiv (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial ℝ ℝ) xD)
  obtain ⟨s, hs⟩ := TauCeti.BundleTest.exists_apply_eq (I := 𝓘(ℝ, ℝ)) (F := ℝ →L[ℝ] ℝ)
    (V := doubleCoefficients) xN (ψ.symm vM)
  have hright : TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ) (M := outer)
      (V := inclusion outer *ᵖ (Bundle.Trivial ℝ ℝ)) (U := nestedOpen)
      (TauCeti.BundleDistribution.restrictCLM (I := 𝓘(ℝ, ℝ)) (F := ℝ)
        (V := Bundle.Trivial ℝ ℝ) (U := outer) actualPointMass) s = 1 := by
    erw [TauCeti.BundleDistribution.restrictCLM_apply,
      TauCeti.BundleDistribution.restrictCLM_apply]
    rw [actualPointMass, TauCeti.BundleTest.delta_apply]
    erw [TauCeti.BundleDistribution.testExtensionCLM_apply_of_mem _ xD,
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
