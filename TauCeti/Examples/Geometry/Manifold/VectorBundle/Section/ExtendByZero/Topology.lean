/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Nonzero open-extension examples for native bundle tests

The clients extend native tests from a genuine proper open interval, from the universal open of
a manifold with corners at a boundary point, from the empty open subset, and with zero-rank
fibres.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology ContMDiffSection
open scoped Manifold ContDiff

namespace TauCeti.Examples.BundleTestOpenExtension

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

end TauCeti.Examples.BundleTestOpenExtension
