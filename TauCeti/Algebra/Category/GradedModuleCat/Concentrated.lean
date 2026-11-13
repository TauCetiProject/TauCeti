/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Degree-zero action on concentrated graded modules

A graded module concentrated in a single internal degree is its own piece in that degree, and is
annihilated by positive-degree scalars. Concentration is preserved by graded surjections.
Such modules are the test targets for detecting the generating degrees of minimal
projective resolution terms via Ext. The algebra itself need not be nonnegatively graded.
For a decomposed graded algebra, every scalar acts through its degree-zero component, so a
linear map over the degree-zero subalgebra between two modules concentrated in the same degree
is a graded map over the original algebra.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for the concentrated targets of the diagonal Ext criterion.
-/

public section

namespace TauCeti.GradedModuleCat

open CategoryTheory _root_.DirectSum

universe uk uA v

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- A graded module concentrated in degree `p` is its own degree-`p` piece. -/
theorem piece_eq_top_of_concentrated {N : GradedModuleCat.{v} 𝒜} {p : ℤ}
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) : N.grading.piece p = ⊤ := by
  refine top_unique ?_
  rw [← N.grading.isInternal.submodule_iSup_eq_top]
  refine iSup_le fun q => ?_
  rcases eq_or_ne q p with rfl | hq
  · exact le_rfl
  · rw [hN q hq]
    exact bot_le

/-- Positive-degree scalars annihilate any module concentrated in one internal degree. -/
theorem positive_smul_top_eq_bot_of_concentrated (N : GradedModuleCat.{v} 𝒜) (p : ℤ)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) :
    (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥ := by
  apply le_antisymm _ bot_le
  refine Submodule.smul_le.mpr fun a ha y hy ↦ ?_
  clear hy
  refine Submodule.iSup_induction _ (motive := fun a => a • y ∈ (⊥ : Submodule k N))
    ha (fun i a ha => ?_) (by simp)
    (fun a b ha hb => by simpa only [add_smul] using Submodule.add_mem _ ha hb)
  refine Submodule.iSup_induction _ (motive := fun a => a • y ∈ (⊥ : Submodule k N))
    ha (fun hi a ha => ?_) (by simp)
    (fun a b ha hb => by simpa only [add_smul] using Submodule.add_mem _ ha hb)
  induction y using DirectSum.Decomposition.inductionOn N.grading.piece with
  | zero => simp
  | add y z hy hz => simpa [smul_add] using Submodule.add_mem _ hy hz
  | @homogeneous q y =>
    by_cases hq : q = p
    · have hz := SetLike.GradedSMul.smul_mem (B := N.grading.piece) ha y.property
      simpa only [vadd_eq_add, hN (i + q) (by omega), Submodule.mem_bot] using hz
    · have hz : (y : N) = 0 := by simpa only [hN q hq, Submodule.mem_bot] using y.property
      simp [hz]

/-- On a module concentrated in one degree, a scalar acts through its degree-zero component. -/
theorem smul_eq_decompose_zero_smul_of_concentrated [DirectSum.Decomposition 𝒜]
    (N : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) (a : A) (x : N) :
    a • x = (DirectSum.decompose 𝒜 a 0 : A) • x := by
  have hmem (y : N) : y ∈ N.grading.piece p :=
    (piece_eq_top_of_concentrated hN).symm ▸ Submodule.mem_top
  have h := DirectSum.coe_decompose_smul_add_of_right_mem 𝒜 N.grading.piece
    (a := a) (i := 0) (hmem x)
  rw [zero_add, decompose_of_mem_same N.grading.piece (hmem (a • x))] at h
  exact h

/-- Shifting a module concentrated in degree `p` by `n` concentrates it in degree `p + n`. -/
theorem shiftObj_piece_eq_bot_of_concentrated (N : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (n : ℤ) (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) (q : ℤ) (hq : q ≠ p + n) :
    (N.shiftObj n).grading.piece q = ⊥ := by
  rw [InternalGrading.shift_piece]
  exact hN _ (by omega)

private def liftGradeZeroLinearMapOfConcentrated [GradedAlgebra 𝒜]
    (M N : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hM : ∀ q, q ≠ p → M.grading.piece q = ⊥)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥)
    (f : M →ₗ[SetLike.GradeZero.subalgebra 𝒜] N) : M ⟶ N :=
  ofHom
    { toFun := f
      map_add' := f.map_add
      map_smul' a x := by
        rw [smul_eq_decompose_zero_smul_of_concentrated M hM,
          smul_eq_decompose_zero_smul_of_concentrated N hN]
        -- The degree-zero subalgebra has definitionally the same carrier as the zero piece.
        let a₀ : SetLike.GradeZero.subalgebra 𝒜 :=
          ⟨(DirectSum.decompose 𝒜 a 0 : A), (DirectSum.decompose 𝒜 a 0).property⟩
        exact f.map_smul a₀ x }
    (LinearMap.isHomogeneous_def.2 fun q x hx => by
      by_cases hq : q = p
      · subst q
        simpa only [add_zero, piece_eq_top_of_concentrated hN] using Submodule.mem_top
      · have hx0 : x = 0 := by simpa only [hM q hq, Submodule.mem_bot] using hx
        simp [hx0])

/-- Between modules concentrated in the same degree, graded `A`-linear maps are exactly the
maps linear over the degree-zero subalgebra. Both directions preserve the underlying function.
The degree-zero scalar actions are restrictions of the given `A`-actions. -/
def gradeZeroLinearMapEquivOfConcentrated [GradedAlgebra 𝒜]
    (M N : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hM : ∀ q, q ≠ p → M.grading.piece q = ⊥)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) :
    (M ⟶ N) ≃ₗ[k] (M →ₗ[SetLike.GradeZero.subalgebra 𝒜] N) where
  toFun f := f.hom.restrictScalars (SetLike.GradeZero.subalgebra 𝒜)
  invFun := liftGradeZeroLinearMapOfConcentrated M N hM hN
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- Restricting a graded map to degree-zero scalars preserves its value on every element. -/
@[simp]
theorem gradeZeroLinearMapEquivOfConcentrated_apply [GradedAlgebra 𝒜]
    (M N : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hM : ∀ q, q ≠ p → M.grading.piece q = ⊥)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥) (f : M ⟶ N) (x : M) :
    gradeZeroLinearMapEquivOfConcentrated M N hM hN f x = f.hom x := by rfl

/-- Lifting a degree-zero-linear map to a graded map preserves its value on every element. -/
@[simp]
theorem gradeZeroLinearMapEquivOfConcentrated_symm_apply [GradedAlgebra 𝒜]
    (M N : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hM : ∀ q, q ≠ p → M.grading.piece q = ⊥)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥)
    (f : M →ₗ[SetLike.GradeZero.subalgebra 𝒜] N) (x : M) :
    ((gradeZeroLinearMapEquivOfConcentrated M N hM hN).symm f).hom x = f x := by rfl

/-- The degree-zero-linear presentation sends the graded identity to the linear identity. -/
@[simp]
theorem gradeZeroLinearMapEquivOfConcentrated_id [GradedAlgebra 𝒜]
    (M : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hM : ∀ q, q ≠ p → M.grading.piece q = ⊥) :
    gradeZeroLinearMapEquivOfConcentrated M M hM hM (𝟙 M) =
      LinearMap.id := by rfl

/-- The degree-zero-linear presentation preserves composition. -/
theorem gradeZeroLinearMapEquivOfConcentrated_comp [GradedAlgebra 𝒜]
    (M N P : GradedModuleCat.{v} 𝒜) {p : ℤ}
    (hM : ∀ q, q ≠ p → M.grading.piece q = ⊥)
    (hN : ∀ q, q ≠ p → N.grading.piece q = ⊥)
    (hP : ∀ q, q ≠ p → P.grading.piece q = ⊥) (f : M ⟶ N) (g : N ⟶ P) :
    gradeZeroLinearMapEquivOfConcentrated M P hM hP (f ≫ g) =
      (gradeZeroLinearMapEquivOfConcentrated N P hN hP g).comp
        (gradeZeroLinearMapEquivOfConcentrated M N hM hN f) := by rfl

end TauCeti.GradedModuleCat
