/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.SymmetricBilinear.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Data.Sym.Card

/-!
# Dimension of symmetric continuous bilinear maps

A basis identifies a symmetric bilinear map with its values on unordered pairs of basis
vectors. These coordinates show that the space of scalar-valued symmetric bilinear forms on
an `n`-dimensional space has dimension `n * (n + 1) / 2`. More generally, for values in a
finite-dimensional space `G`, this dimension is multiplied by `finrank 𝕜 G`.

When two is nonzero, symmetrization is surjective onto this space, so its range has the same
dimension. In particular, symmetric covariant two-tensors have the expected fibre dimension.
The coordinate equivalence itself does not require two to be invertible.
-/

public section

noncomputable section

open TauCeti Module

namespace Module.Basis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]
  {ι : Type*}

/-- A symmetric continuous bilinear map is determined by its values on unordered pairs of
basis vectors. -/
def symmetricBilinearCoordinates (b : Basis ι 𝕜 V) :
    symmetricBilinearMaps 𝕜 V G ≃ₗ[𝕜] (Sym2 ι → G) where
  toFun B := Sym2.lift ⟨fun i j ↦ B.val (b i) (b j),
    fun i j ↦ (mem_symmetricBilinearMaps 𝕜 V G _).1 B.property _ _⟩
  invFun f := by
    let B := b.constr 𝕜 fun i ↦ b.constr 𝕜 fun j ↦ f s(i, j)
    refine ⟨B.toContinuousBilinearMap, (mem_symmetricBilinearMaps 𝕜 V G _).2 fun v w ↦ ?_⟩
    have h : B = B.flip := b.ext fun i ↦ b.ext fun j ↦ by
      simp [B, Sym2.eq_swap]
    simpa using LinearMap.congr_fun₂ h v w
  left_inv B := by
    apply Subtype.ext
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    simp
  right_inv f := by
    funext p
    induction p using Sym2.ind with
    | _ i j => simp
  map_add' B C := by
    funext p
    induction p using Sym2.ind with
    | _ i j => simp
  map_smul' c B := by
    funext p
    induction p using Sym2.ind with
    | _ i j => simp

/-- Symmetric coordinates are evaluation on the corresponding pair of basis vectors. -/
@[simp]
theorem symmetricBilinearCoordinates_apply (b : Basis ι 𝕜 V)
    (B : symmetricBilinearMaps 𝕜 V G) (i j : ι) :
    b.symmetricBilinearCoordinates B s(i, j) = B.val (b i) (b j) :=
  (rfl)

/-- The inverse coordinates prescribe the values on pairs of basis vectors. -/
@[simp]
theorem symmetricBilinearCoordinates_symm_apply (b : Basis ι 𝕜 V)
    (f : Sym2 ι → G) (i j : ι) :
    (b.symmetricBilinearCoordinates.symm f).val (b i) (b j) = f s(i, j) := by
  simp [symmetricBilinearCoordinates]

end Module.Basis

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  (V : Type*) [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  (G : Type*) [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G] [FiniteDimensional 𝕜 G]

/-- The dimension of symmetric bilinear maps is the number of unordered pairs of basis
vectors times the dimension of the codomain. This also holds in characteristic two. -/
theorem finrank_symmetricBilinearMaps :
    finrank 𝕜 (symmetricBilinearMaps 𝕜 V G) =
      (finrank 𝕜 V * (finrank 𝕜 V + 1) / 2) * finrank 𝕜 G := by
  rw [((Module.finBasis 𝕜 V).symmetricBilinearCoordinates (G := G)).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Sym2.card, Nat.choose_two_right, Nat.mul_comm]

/-- The symmetric scalar-valued bilinear forms have dimension `n * (n + 1) / 2`. -/
theorem finrank_symmetricBilinearMaps_self :
    finrank 𝕜 (symmetricBilinearMaps 𝕜 V 𝕜) =
      finrank 𝕜 V * (finrank 𝕜 V + 1) / 2 := by
  simp [finrank_symmetricBilinearMaps]

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NeZero (2 : 𝕜)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Symmetrization has rank `n * (n + 1) / 2` times the codomain dimension. -/
theorem finrank_range_symmetrizeBilinear [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 G] :
    finrank 𝕜 (LinearMap.range
      (symmetrizeBilinear (𝕜 := 𝕜) (V := V) (G := G)).toLinearMap) =
      (finrank 𝕜 V * (finrank 𝕜 V + 1) / 2) * finrank 𝕜 G := by
  rw [LinearMap.range_eq_top.mpr symmetrizeBilinear_surjective,
    finrank_top, finrank_symmetricBilinearMaps]

end ContinuousLinearMap
