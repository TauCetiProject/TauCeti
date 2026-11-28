/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.Automorphism.Realization
public import TauCeti.Algebra.Lie.Symplectic.Automorphism.Uniqueness

/-!
# Automorphisms of the symplectic Lie algebra

For a nondegenerate alternating space over a field of characteristic different from two in which
every scalar is a square, every automorphism of its symplectic Lie algebra is conjugation by a
symplectic isometry. This isometry is unique up to sign. In particular this holds over every
algebraically closed field of characteristic zero, in arbitrary dimension.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

/-- Every Lie automorphism of a symplectic space over a quadratically closed field of
characteristic different from two is induced by an isometry, unique up to sign. -/
theorem exists_isometryEquiv_lieConj_unique_up_to_sign [NeZero (2 : K)] (hsq : ∀ a : K, IsSquare a)
    (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (f : skewAdjointLieSubalgebra B ≃ₗ⁅K⁆ skewAdjointLieSubalgebra B) :
    ∃ h : B.IsometryEquiv B,
      (∀ X : skewAdjointLieSubalgebra B, (f X).val = h.toLinearEquiv.lieConj X.val) ∧
      ∀ g : B.IsometryEquiv B,
        (∀ X : skewAdjointLieSubalgebra B, (f X).val = g.toLinearEquiv.lieConj X.val) →
          g = h ∨ ∀ v, g v = -(h v) := by
  obtain ⟨h, hh⟩ := exists_isometryEquiv_lieConj_of_skewAdjoint hsq hB hB (Or.inl hnd) f
  refine ⟨h, hh, fun g hg ↦ ?_⟩
  by_cases hb : B = 0
  · have : Subsingleton V := ⟨fun v w ↦ sub_eq_zero.mp (hnd.1 (v - w) (by simp [hb]))⟩
    left
    exact DFunLike.ext _ _ fun _ ↦ Subsingleton.elim _ _
  · exact (g.conj_eq_on_skewAdjoint_iff h hB hb).mp fun X ↦ (hg X).symm.trans (hh X)

end LinearMap.BilinForm
