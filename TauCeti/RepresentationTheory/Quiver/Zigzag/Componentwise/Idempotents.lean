/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Grading
public import Mathlib.RingTheory.Idempotents

/-!
# Homogeneous vertex idempotents of the componentwise zigzag algebra

The vertex vectors form a complete orthogonal family of idempotents. They span the
degree-zero piece of the signed grading, including on isolated-vertex dual-number factors.
These are the homogeneous generators of the vertex projectives.

The proofs use the existing componentwise multiplication table and homogeneous
vertex–arrow–volume basis, together with Mathlib's graded projections.
-/

public section

namespace TauCeti

universe u w
variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

/-- The vertex vectors of the public algebra are a complete orthogonal family of idempotents. -/
theorem completeOrthogonalIdempotents_zigzagAlgebraBasis_inl [Fintype V] :
    CompleteOrthogonalIdempotents (e) := by
  classical
  refine ⟨⟨fun i ↦ isIdempotentElem_zigzagAlgebraBasis_inl k G i,
    fun i j hij ↦ by simp [hij]⟩, ?_⟩
  have h : LinearMap.mulLeft k (∑ i, e i) =
      (LinearMap.id : zigzagAlgebra k G →ₗ[k] zigzagAlgebra k G) := by
    apply (zigzagAlgebraBasis k G).ext
    intro b
    simp only [LinearMap.mulLeft_apply, LinearMap.id_apply, Finset.sum_mul]
    rcases b with i | d | i
    · calc
        _ = e i * zigzagAlgebraBasis k G (.inl i) :=
          Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji]) (by simp)
        _ = _ := by simp
    · calc
        _ = e d.snd * zigzagAlgebraBasis k G (.inr (.inl d)) :=
          Finset.sum_eq_single d.snd (fun j _ hji ↦ by simp [hji]) (by simp)
        _ = _ := by simp
    · calc
        _ = e i * zigzagAlgebraBasis k G (.inr (.inr i)) :=
          Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji]) (by simp)
        _ = _ := by simp
  simpa only [LinearMap.mulLeft_apply, mul_one, LinearMap.id_apply] using
    congrArg (fun f : zigzagAlgebra k G →ₗ[k] zigzagAlgebra k G ↦ f 1) h

/-- The signed degree-zero piece of the public algebra is spanned by the vertex idempotents. -/
theorem zigzagAlgebraIntegerGrade_zero_eq_span_range :
    zigzagAlgebraIntegerGrade k G 0 = Submodule.span k (Set.range (e)) := by
  classical
  have hg : zigzagAlgebraIntegerGrade k G 0 = zigzagAlgebraGrade k G 0 := by
    simpa only [Int.natCast_zero] using zigzagAlgebraIntegerGrade_ofNat k G 0
  rw [hg]
  let _ := zigzagAlgebraGradedAlgebra k G
  let _ : Fintype V := Fintype.ofFinite _
  let _ : Fintype (ZigzagBasisIndex G) := inferInstance
  let p := GradedAlgebra.proj (zigzagAlgebraGrade k G) 0
  have hb (b : ZigzagBasisIndex G) :
      p (zigzagAlgebraBasis k G b) ∈ Submodule.span k (Set.range (e)) := by
    dsimp only [p]
    rw [GradedAlgebra.proj_apply]
    rcases b with i | d | i
    · rw [DirectSum.decompose_of_mem_same _ (zigzagAlgebraBasis_inl_mem_grade_zero k G i)]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne _ (zigzagAlgebraBasis_inr_inl_mem_grade_one k G d)
        (by decide : (1 : ℕ) ≠ 0)]
      exact Submodule.zero_mem _
    · rw [DirectSum.decompose_of_mem_ne _ (zigzagAlgebraBasis_inr_inr_mem_grade_two k G i)
        (by decide : (2 : ℕ) ≠ 0)]
      exact Submodule.zero_mem _
  apply le_antisymm
  · intro x hx
    have hpx : p x = x :=
      DirectSum.decompose_of_mem_same (zigzagAlgebraGrade k G) hx
    rw [← hpx, ← (zigzagAlgebraBasis k G).sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun b _ ↦ by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hb b)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact zigzagAlgebraBasis_inl_mem_grade_zero k G i

end TauCeti
