/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Coordinates

/-!
# The fan of affine space

Let `b` be an integral basis of the lattice `N`, indexed by a finite type `ι` of size `n`. The
fan of `n`-dimensional affine space consists of the faces of the positive orthant, the cone
spanned by the basis vectors `b j`. This orthant is the maximal cone of the fan of projective
space omitting the extra ray `-∑ j, b j`, so the fan of affine space is the open subfan of the
projective-space fan formed by the faces of that cone. Classically, its toric variety is the
standard affine chart of projective space on which the extra homogeneous coordinate does not
vanish. Using the projective-space cone, rather than a second copy of the orthant, lets the
dual-semigroup coordinates and complex-point charts of projective space apply to it unchanged.

The fan of affine space is regular. It is complete exactly when `ι` is empty: otherwise the
character `b.coord j` is nonnegative on the orthant but negative at `-b j`.

## Main declarations

* `TauCeti.Toric.Fan.affineSpace`: the fan of affine space.
* `TauCeti.Toric.Fan.affineSpaceMaximalCone`: its maximal cone, the positive orthant.
* `TauCeti.Toric.Fan.isRegular_affineSpace`: it is regular.
* `TauCeti.Toric.Fan.affineSpace_eq_subfan`: it is the open subfan of the fan of projective
  space formed by the faces of the maximal cone omitting the extra ray.
* `TauCeti.Toric.Fan.isComplete_affineSpace_iff`: it is complete exactly in rank zero.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.1 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open Set

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V}

/-- The fan of affine space attached to an integral basis `b`: the faces of the positive orthant
spanned by `b`. The orthant is represented as the maximal cone of the fan of projective space
omitting the extra ray, see `projectiveSpaceCone_compl_none`. -/
noncomputable abbrev affineSpace (hi : IsIntegralLattice i) : Fan i :=
  ofCone hi (isRegularCone_projectiveSpaceCone b hi (S := {none}ᶜ) (by simp)).toIsToricCone

/-- The cones of the fan of affine space are the faces of the positive orthant. -/
theorem mem_affineSpace_cones (hi : IsIntegralLattice i) {σ : PointedCone ℝ V} :
    σ ∈ (affineSpace b hi).cones ↔ σ.IsFaceOf (PointedCone.hull ℝ (range fun j ↦ i (b j))) := by
  rw [mem_ofCone_cones, projectiveSpaceCone_compl_none]

/-- The positive orthant, as the maximal cone of the fan of affine space: every cone of the fan
is a face of it. -/
noncomputable abbrev affineSpaceMaximalCone (hi : IsIntegralLattice i) : (affineSpace b hi).cones :=
  ⟨projectiveSpaceCone b i {none}ᶜ, (mem_ofCone_cones hi _).2 (.refl _)⟩

/-- The support of the fan of affine space is the positive orthant. -/
theorem support_affineSpace (hi : IsIntegralLattice i) :
    (affineSpace b hi).support = PointedCone.hull ℝ (range fun j ↦ i (b j)) := by
  rw [support_ofCone, projectiveSpaceCone_compl_none]

/-- The fan of affine space is regular. -/
theorem isRegular_affineSpace (hi : IsIntegralLattice i) : (affineSpace b hi).IsRegular :=
  isRegular_ofCone hi (isRegularCone_projectiveSpaceCone b hi (by simp))

/-- Each coordinate character `b.coord j` is nonnegative on every cone of the fan of affine
space, so it defines a monomial function on its toric variety. -/
theorem coord_mem_dualSemigroup_affineSpace (hi : IsIntegralLattice i) (j : ι)
    (σ : (affineSpace b hi).cones) :
    (b.coord j).toAddMonoidHom ∈ dualSemigroup (affineSpace b hi).lattice σ.1 := by
  refine dualSemigroup_anti hi ((mem_ofCone_cones hi _).1 σ.2).le ?_
  rw [← projectiveSpaceRatioCharacter_some_none]
  exact projectiveSpaceRatioCharacter_mem_dualSemigroup b hi _ _ (by simp)

/-- The fan of affine space is the open subfan of the fan of projective space formed by the
faces of the maximal cone omitting the extra ray. -/
theorem affineSpace_eq_subfan (hi : IsIntegralLattice i) :
    affineSpace b hi = (projectiveSpace b hi).subfan
      {τ | τ.IsFaceOf (projectiveSpaceCone b i {none}ᶜ)}
      ((projectiveSpace b hi).isFaceOf_subset_cones (projectiveSpaceMaximalCone b hi none).2)
      fun _ _ hτ hυ ↦ hυ.trans hτ :=
  (projectiveSpace b hi).ofCone_eq_subfan (projectiveSpaceMaximalCone b hi none).2

/-- The fan of affine space is complete exactly when the lattice has rank zero. -/
theorem isComplete_affineSpace_iff (hi : IsIntegralLattice i) :
    (affineSpace b hi).IsComplete ↔ IsEmpty ι := by
  refine ⟨fun h ↦ ⟨fun j ↦ ?_⟩, fun _ ↦ ?_⟩
  · -- The character `b.coord j` is nonnegative on the orthant, but takes the value `-1` at
    -- `-b j`.
    obtain ⟨σ, hσ, hx⟩ := (isComplete_iff _).1 h (-i (b j))
    have := (mem_dualSemigroup hi _).1
      (coord_mem_dualSemigroup_affineSpace b hi j ⟨σ, hσ⟩) hx
    norm_num at this
  · -- In rank zero the lattice is trivial, hence so is the real space it spans.
    have : Subsingleton N := b.repr.injective.subsingleton
    have hspan : Submodule.span ℝ (range i) = ⊥ := Submodule.span_eq_bot.2 <| by
      rintro _ ⟨n, rfl⟩
      rw [Subsingleton.elim n 0, map_zero]
    refine (isComplete_iff _).2 fun x ↦ ⟨_, (mem_ofCone_cones hi _).2 (.refl _), ?_⟩
    have hx : x ∈ Submodule.span ℝ (range i) := hi.span_range_eq_top ▸ Submodule.mem_top
    rw [hspan, Submodule.mem_bot] at hx
    exact hx ▸ zero_mem _

end TauCeti.Toric.Fan
