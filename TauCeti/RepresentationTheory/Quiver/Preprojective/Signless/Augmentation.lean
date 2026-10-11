/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.KoszulComplex
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.PathsInto

/-!
# The augmentation endpoint of the signless preprojective Koszul complex

In the corner at a vertex `v`, the positive-degree part of the signless preprojective algebra
consists exactly of sums of incoming arrows times elements of their source corners. Thus the
incoming-arrow Koszul map has image the kernel of the vertex augmentation, for any finite quiver
with involutive arrow reversal.

The last-arrow decomposition in the path algebra supplies the forward implication. The reverse
implication uses the induced grading, and does not depend on injectivity of the left-hand Koszul
map.

The vertex Koszul complex follows Etingof and Eu, *Koszulity and the Hilbert series of
preprojective algebras*, Sections 2–3; the signless relation is the quadratic-dual convention of
Huerfano and Khovanov, *A category for the adjoint representation*, Section 3.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) (R : Type u) [CommRing k] [Quiver.{v} R] [HasInvolutiveReverse R]
  [Fintype R] [∀ i j : R, Fintype (i ⟶ j)] [∀ x : R, Fintype (Quiver.Star x)]

/-- An element of the vertex corner has positive path degree exactly when it is a sum of
incoming arrows times elements of their source corners. This is exactness at the augmentation
endpoint of the signless Koszul complex. -/
theorem mem_iSup_signlessPreprojectiveGrade_add_one_iff_exists_eq_sum (v : R)
    {x : signlessPreprojectiveAlgebra k R}
    (hx : signlessPreprojectiveMk k R (vertexIdempotent k v) * x = x) :
    x ∈ ⨆ n, signlessPreprojectiveGrade k R (n + 1) ↔
      ∃ z : (i : R) → (i ⟶ v) → signlessPreprojectiveAlgebra k R,
        (∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) ∧
          x = ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨z, hz, hxz⟩ : ∃ z : (i : R) → (i ⟶ v) → signlessPreprojectiveAlgebra k R,
        (∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) ∧
          signlessPreprojectiveMk k R (vertexIdempotent k v) * x =
            ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b := by
      refine Submodule.iSup_induction (motive := fun x => ∃ z : (i : R) →
          (i ⟶ v) → signlessPreprojectiveAlgebra k R,
          (∀ i b, signlessPreprojectiveMk k R (vertexIdempotent k i) * z i b = z i b) ∧
            signlessPreprojectiveMk k R (vertexIdempotent k v) * x =
              ∑ i, ∑ b, signlessPreprojectiveMk k R (ofArrow b) * z i b) _ h
        (fun n x hx' => ?_) ⟨0, fun _ _ => mul_zero _, by simp⟩
        fun x x' hx hx' => ?_
      · obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k R).1 hx'
        obtain ⟨w, hw, hwy⟩ := exists_eq_sum_ofArrow_mul
          (vertexIdempotent_mul_mem_pathsInto v hy)
        refine ⟨fun i b => signlessPreprojectiveMk k R (w i b), fun i b => ?_, ?_⟩
        · rw [← map_mul, vertexIdempotent_mul_of_mem_pathsInto (hw i b)]
        · rw [← map_mul, hwy]
          simp only [map_sum, map_mul]
      · obtain ⟨z, hz, hxz⟩ := hx
        obtain ⟨z', hz', hxz'⟩ := hx'
        refine ⟨z + z', fun i b => ?_, ?_⟩
        · rw [Pi.add_apply, Pi.add_apply, mul_add, hz, hz']
        · simp only [mul_add, hxz, hxz', Pi.add_apply, Finset.sum_add_distrib]
    exact ⟨z, hz, hx.symm.trans hxz⟩
  · rintro ⟨z, -, rfl⟩
    exact sum_mem fun i _ => sum_mem fun b _ =>
      signlessPreprojectiveMk_ofArrow_mul_mem_iSup k R b (z i b)

end TauCeti
