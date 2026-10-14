/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.ClosedCategory

/-!
# Closed boundaries of odd homotopies of curved right modules

An odd right-linear homotopy has a closed boundary `dN ∘ k + k ∘ dM`. Its class in the
existing curved homotopy category is zero, and two closed maps have the same class precisely
when their difference is such a boundary. The construction reuses the zero-cocycle equivalence
and square-zero Hom differential of curved modules of the same curvature.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
-/

public section

open CategoryTheory

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The quotient and its object wrappers retain the original curved modules.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}

/-- The boundary of an odd homotopy is a closed morphism of curved right modules. -/
noncomputable def closedHomotopyBoundary
    (k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1)) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N := by
  refine (dgClosedHomEquivZeroCocycles M N).symm
    ⟨dgRightModuleCochains.curvedDifferential
      (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) (-1) k,
        LinearMap.mem_ker.mpr ?_⟩
  simpa only [Int.reduceAdd, LinearMap.comp_apply, LinearMap.zero_apply] using
    congrArg (fun l ↦ l k) (dgRightModuleCochains.curvedDifferential_comp_self
      (hM := M.isCurvedDGRightModule) (hN := N.isCurvedDGRightModule) (-1))

/-- The underlying map of the closed boundary is `dN ∘ k + k ∘ dM`. -/
@[simp]
theorem closedHom_closedHomotopyBoundary_apply
    (k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1))
    (x : M) :
    closedHom (closedHomotopyBoundary k) x = N.differential (k.1 x) + k.1 (M.differential x) := by
  rw [closedHom_eq]
  simp only [closedHomotopyBoundary, dgClosedHom_dgClosedHomEquivZeroCocycles_symm_apply,
    LinearEquiv.apply_symm_apply]
  exact dgRightModuleCochains.curvedDifferential_neg_one_apply k x

/-- The class of a closed homotopy boundary is zero. -/
-- Keep zero at the quotient-functor object types so `simp` closes functor-map goals as well.
@[simp]
theorem homOf_closedHomotopyBoundary
    (k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1)) :
    DGHomotopyCategory.homOf R (dgClosedHom R (closedHomotopyBoundary k))
      (dgClosedHom_mem_dgCycles R (closedHomotopyBoundary k)) =
        (0 : (dgClosedToHomotopy R).obj
          (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) ⟶
            (dgClosedToHomotopy R).obj
              (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)) := by
  rw [DGHomotopyCategory.homOf_eq_zero_iff, mem_dgBoundaries_iff]
  refine ⟨k, fun x ↦ ?_⟩
  rw [← closedHom_eq]
  exact closedHom_closedHomotopyBoundary_apply k x

/-- Two closed maps have the same homotopy class exactly when an odd homotopy gives their
pointwise difference as a boundary. -/
theorem quotient_map_eq_iff_exists_homotopy
    (f g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    (dgClosedToHomotopy R).map f = (dgClosedToHomotopy R).map g ↔
      ∃ k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1),
        ∀ x : M, closedHom f x - closedHom g x =
          N.differential (k.1 x) + k.1 (M.differential x) := by
  rw [dgClosedToHomotopy_map_eq_iff, mem_dgBoundaries_iff]
  simp only [map_sub, ForgetEnrichment.to_of]
  -- The cochains are subtypes of right-linear maps, with subtraction inherited pointwise.
  -- `LinearMap.sub_apply` applies only after this projection reduces to subtraction of maps;
  -- the closed-map computation lemmas then identify the two underlying maps.
  change (∃ k : dgRightModuleCochains (R := R) (A := A)
      (ℳ := M.grading) (ℳN := N.grading) (-1), ∀ x : M,
      ((dgHomLinearEquivCochains M N 0 (dgClosedHom R f)).1 -
        (dgHomLinearEquivCochains M N 0 (dgClosedHom R g)).1) x =
          N.differential (k.1 x) + k.1 (M.differential x)) ↔ _
  simp only [LinearMap.sub_apply, ← closedHom_eq]

end TauCeti.CurvedDGRightModuleCat
