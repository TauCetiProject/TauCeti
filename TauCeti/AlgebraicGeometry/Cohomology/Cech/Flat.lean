/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Flat
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Flat

/-!
# Flat Čech complexes from flat stalks

For a quasi-coherent module with stalks flat over an affine base on each open of a
finite family with affine intersections, the Čech complex consists of flat modules
over the base.
The hypothesis is on stalks, not on sections: the affine local criterion for flatness
supplies flatness of the sections appearing in the complex.

Together with the Čech comparison and arbitrary base-change isomorphism, this
supplies the degreewise flat complex used in cohomology and base change. The complex
here is the ordinary, unbounded Čech complex; no boundedness or finiteness of its
cohomology is asserted.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 12.2.
* D. Mumford, *Abelian Varieties*, Section 5.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- A quasi-coherent sheaf with stalks flat over the base on each open of a finite
family with affine nonempty finite intersections gives a degreewise flat Čech complex.
The family need not cover the scheme. -/
theorem flat_cechComplexFunctor_obj_X_of_flat_stalk {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (M : X.Modules) [M.IsQuasicoherent]
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))
    (hM : ∀ (i : ι) (x : U i), Module.Flat R (M.presheaf.stalk x)) (n : ℕ) :
    Module.Flat R (((cechComplexFunctor U).obj
      ((sectionsBasePresheafFunctor R).obj M)).X n) := by
  apply TauCeti.CategoryTheory.flat_cechComplexFunctor_obj_X
  intro s hs
  obtain ⟨i, hi⟩ := hs
  exact flat_sections_of_flat_stalk R M (hU s ⟨i, hi⟩) fun x ↦
    hM i ⟨x, (Finset.inf_le (f := U) hi) x.2⟩

end AlgebraicGeometry.Scheme.Modules
