/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# A tubular neighbourhood retracts onto its core

Radial scaling in the fibers of a tubular neighbourhood gives a deformation from the identity
to the zero section. Consequently its open tubular domain has the homotopy type of the embedded
base. The result applies to the star-shaped tubular domains used in the tubular-neighbourhood
theorem, without choosing a radius or a trivialization of the normal bundle.

The tubular-neighbourhood theorem and its radial deformation are described in J. M. Lee,
*Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24.
-/

public section

open Bundle Set Topology
open scoped unitInterval ContinuousMap

namespace TauCeti.IsTubularNeighborhood

variable {B F N : Type*} {E : B → Type*}
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [TopologicalSpace N]
  {f : B → N} {U : Set (TotalSpace F E)} {toFun : U → N}

/-- Include the core of a tubular neighbourhood in its open tubular domain. -/
def core (T : IsTubularNeighborhood f U toFun) (x : B) : U :=
  ⟨zeroSection F E x, T.zero_mem x⟩

/-- The tubular chart agrees with the original embedding on the core. -/
theorem toFun_core (T : IsTubularNeighborhood f U toFun) (x : B) :
    toFun (T.core x) = f x := T.map_zeroSection x

/-- The core inclusion is an embedding, because the tubular chart is an embedding and its
restriction to the core is the given embedding `f`. -/
theorem isEmbedding_core (T : IsTubularNeighborhood f U toFun) : IsEmbedding T.core := by
  apply T.isOpenEmbedding.isEmbedding.of_comp_iff.mp
  convert T.isEmbedding_f using 1
  ext x
  exact T.toFun_core x

/-- Forget the normal vector and retain the base point of a tubular-domain point. -/
def projection (_T : IsTubularNeighborhood f U toFun) (u : U) : B := u.1.1

@[simp]
theorem projection_core (T : IsTubularNeighborhood f U toFun) (x : B) :
    T.projection (T.core x) = x := (rfl)

@[simp]
theorem core_projection (T : IsTubularNeighborhood f U toFun) (u : U) :
    T.core (T.projection u) = T.radialContraction (0, u) := by
  rw [T.radialContraction_zero]
  rfl

/-- Projection to the base is continuous. The radial contraction at time zero factors as the
projection followed by the core embedding, so its continuity detects continuity of projection. -/
theorem continuous_projection (T : IsTubularNeighborhood f U toFun) :
    Continuous T.projection := by
  apply T.isEmbedding_core.continuous_iff.mpr
  have h : (T.core ∘ T.projection) = fun u : U => T.radialContraction (0, u) := by
    funext u
    exact T.core_projection u
  rw [h]
  exact T.continuous_radialContraction.comp (continuous_const.prodMk continuous_id)

/-- The radial deformation fixes the core pointwise at every time. -/
@[simp]
theorem radialContraction_core (T : IsTubularNeighborhood f U toFun)
    (t : I) (x : B) : T.radialContraction (t, T.core x) = T.core x := by
  apply Subtype.ext
  rw [T.coe_radialContraction]
  simp only [core, zeroSection]
  exact congrArg (fun v : E x => (⟨x, v⟩ : TotalSpace F E))
    (smul_zero (t : ℝ) : (t : ℝ) • (0 : E x) = 0)

/-- Radial contraction is a homotopy from the core retraction to the identity on the tubular
domain. -/
def radialHomotopy (T : IsTubularNeighborhood f U toFun) :
    ContinuousMap.Homotopy
      (⟨T.core ∘ T.projection, T.isEmbedding_core.continuous.comp T.continuous_projection⟩)
      (ContinuousMap.id U) where
  toFun := T.radialContraction
  continuous_toFun := T.continuous_radialContraction
  map_zero_left u := by
    exact (T.core_projection u).symm
  map_one_left u := T.radialContraction_one u

/-- The tubular domain is homotopy equivalent to the core. The forward map is fiber projection
and the inverse is the zero-section inclusion. -/
def homotopyEquiv (T : IsTubularNeighborhood f U toFun) : U ≃ₕ B where
  toFun := ⟨T.projection, T.continuous_projection⟩
  invFun := ⟨T.core, T.isEmbedding_core.continuous⟩
  left_inv := ⟨T.radialHomotopy⟩
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id B) using 1
    ext x
    exact T.projection_core x

/-- The forward map of the tubular homotopy equivalence is fiber projection. -/
@[simp]
theorem homotopyEquiv_apply (T : IsTubularNeighborhood f U toFun) (u : U) :
    T.homotopyEquiv u = T.projection u := (rfl)

/-- The inverse map of the tubular homotopy equivalence is the core inclusion. -/
@[simp]
theorem homotopyEquiv_symm_apply (T : IsTubularNeighborhood f U toFun) (x : B) :
    T.homotopyEquiv.symm x = T.core x := (rfl)

/-- The open image of a tubular chart has the homotopy type of the embedded base. This is the
ambient-space form of `homotopyEquiv`, obtained through the chart's homeomorphism onto its image.
-/
noncomputable def imageHomotopyEquiv (T : IsTubularNeighborhood f U toFun) :
    Set.range toFun ≃ₕ B :=
  T.isOpenEmbedding.isEmbedding.toHomeomorph.symm.toHomotopyEquiv.trans T.homotopyEquiv

end TauCeti.IsTubularNeighborhood
