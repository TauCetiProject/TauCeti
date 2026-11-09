/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum
public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum

/-!
# The total-degree decomposition of a finite tensor product

If each factor is the internal direct sum of its homogeneous pieces, the total-degree pieces
of their finite tensor product also form an internal direct sum. This equips the existing
`TauCeti.PiTensorProduct.totalDegreePiece` with `DirectSum.Decomposition`, so that every tensor
has a unique finite homogeneous expansion. In particular the construction applies to tensor
products of total resolutions, where a comparison map is assembled degree by degree.

The construction distributes the tensor product over the direct sums using Mathlib's
`PiTensorProduct.ofDirectSumEquiv`, then collects multidegrees with the same sum. It needs no
flatness hypothesis: the inclusions of the homogeneous pieces are split. For an empty family,
the empty tensor product is concentrated in degree zero; the same construction covers this case.
-/

public section

open scoped TensorProduct
open DirectSum

namespace TauCeti.PiTensorProduct

universe u v w z

variable {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι]
  {A : Type w} [AddCommMonoid A] [DecidableEq A]
  {M : ι → Type z} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  (ℳ : ∀ i, A → Submodule R (M i)) [hℳ : ∀ i, DirectSum.Decomposition (ℳ i)]

/-- The total-degree pieces of a finite tensor product decompose it whenever the homogeneous
pieces decompose every factor. The inverse to recomposition first expands each factor and then
collects the finitely many multidegrees by their sum. -/
noncomputable instance totalDegreePieceDecomposition :
    DirectSum.Decomposition (totalDegreePiece ι ℳ) := by
  classical
  -- First expand into the direct sum indexed by the degree of every factor.
  let e : (⨂[R] i, M i) ≃ₗ[R] ⨁ p : ι → A, ⨂[R] i, ℳ i (p i) :=
    (_root_.PiTensorProduct.congr fun i ↦ DirectSum.decomposeLinearEquiv (ℳ i)).trans
      _root_.PiTensorProduct.ofDirectSumEquiv
  let Q (p : ι → A) :=
    (DirectSum.summand R (fun p : ι → A ↦ ⨂[R] i, ℳ i (p i)) p).comap e.toLinearMap
  have hQ : DirectSum.IsInternal Q :=
    TauCeti.DirectSum.isInternal_comap _ Q e.toLinearMap e.injective
      (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ e.surjective _)
  -- Each multidegree summand is exactly the tensor product of the corresponding pieces.
  have hQeq : Q = fun p ↦
      LinearMap.range (_root_.PiTensorProduct.map fun i ↦ (ℳ i (p i)).subtype) := by
    funext p
    have he : e.symm.toLinearMap ∘ₗ DirectSum.lof R _ _ p =
        _root_.PiTensorProduct.map (fun i ↦ (ℳ i (p i)).subtype) := by
      apply _root_.PiTensorProduct.ext
      ext m
      apply e.injective
      simp [e]
    dsimp only [Q]
    rw [Submodule.comap_equiv_eq_map_symm, DirectSum.summand_def,
      ← LinearMap.range_comp, he]
  -- Collecting an internal sum over the fibers of the total-degree map remains internal.
  have h := hQ.iSup_fiber fun p ↦ ∑ i, p i
  rw [hQeq] at h
  simpa only [← totalDegreePiece_eq_iSup] using h.chooseDecomposition

end TauCeti.PiTensorProduct
