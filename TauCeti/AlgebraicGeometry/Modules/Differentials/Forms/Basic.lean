/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.VectorBundle.Determinant.LocallyConstantRank
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic

/-!
# Sheaves of relative differential forms

For a scheme `X` with a structure morphism `f : X ⟶ Spec R`, the sheaf `Ωᵖ_{X/R}` of relative
differential `p`-forms is the `p`-th exterior power, as a sheaf of `𝒪_X`-modules, of the sheaf of
relative differentials `Ω_{X/R}`. The exterior power is taken of the sheaf, not of its global
sections: on a smooth scheme it is the sheaf whose local frames are the wedge products of a local
frame of `Ω_{X/R}`.

The structure morphism is an explicit argument, so that a base change `X_K ⟶ Spec K` or any other
morphism to `Spec R` can be used directly; the statements below that compare with `Ω_{X/R}` use
the structure morphism `X ↘ Spec R` of an `X.Over (Spec R)` instance.

In degree zero `Ωᵖ_{X/R}` is `𝒪_X` and in degree one it is `Ω_{X/R}`. If `X` is smooth of
relative dimension `n` over `Spec R`, then `Ωᵖ_{X/R}` is finite locally free of rank `n.choose p`;
in particular the top-degree forms `Ωⁿ_{X/R}` are an invertible sheaf, identified with the
determinant `det Ω_{X/R}` (the canonical sheaf of `X` over `R`), and `Ωᵖ_{X/R}` vanishes for
`p > n`.

## Main declarations

* `TauCeti.AlgebraicGeometry.differentialForms R f p`: the sheaf `Ωᵖ_{X/R}`;
* `differentialFormsZeroIso` and `differentialFormsOneIso`: `Ω⁰_{X/R} ≅ 𝒪_X` and
  `Ω¹_{X/R} ≅ Ω_{X/R}`;
* `FiniteLocallyFreeSheaf.differentialForms R X p`, `FiniteLocallyFreeSheaf.differentialForms_def`,
  `FiniteLocallyFreeSheaf.rank_differentialForms_apply'` and
  `FiniteLocallyFreeSheaf.rank_differentialForms_apply`: on a smooth scheme `Ωᵖ_{X/R}` is the
  finite locally free exterior power of `Ω_{X/R}`, of rank `n.choose p` in relative dimension `n`;
* `isZero_differentialForms`: `Ωᵖ_{X/R} = 0` for `p` above the relative dimension;
* `isInvertible_differentialForms` and `differentialFormsIsoDet`: the top-degree forms are
  invertible and are the determinant of `Ω_{X/R}`.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.8 (the sheaves `Ωᵖ = ⋀ᵖ Ω` and the canonical
  sheaf `ω = ⋀ⁿ Ω` of a nonsingular variety of dimension `n`).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] {X : Scheme.{u}}

/-- The sheaf `Ωᵖ_{X/R}` of **relative differential `p`-forms** of a scheme `X` along a structure
morphism `f : X ⟶ Spec R`: the `p`-th exterior power, as a sheaf of `𝒪_X`-modules, of the sheaf of
relative differentials `Ω_{X/R}` defined by `f`. The body is exposed so that morphisms of
differential forms, such as their pullback, can be built from exterior powers of morphisms. -/
@[expose] def differentialForms (f : X ⟶ Spec (.of R)) (p : ℕ) : X.Modules :=
  letI : X.Over (Spec (.of R)) := ⟨f⟩
  (SheafOfModules.exteriorPower X.sheaf p).obj (X.relativeDifferentials R)

/-- The sheaf of differential `0`-forms is the structure sheaf. -/
def differentialFormsZeroIso (f : X ⟶ Spec (.of R)) :
    differentialForms R f 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.exteriorPowerZeroIso X.sheaf).app _

variable (X) [X.Over (Spec (.of R))]

/-- For the structure morphism of a scheme over `Spec R`, `Ωᵖ_{X/R}` is the `p`-th exterior power
of `Ω_{X/R}`. -/
lemma differentialForms_def (p : ℕ) :
    differentialForms R (X ↘ Spec (.of R)) p =
      (SheafOfModules.exteriorPower X.sheaf p).obj (X.relativeDifferentials R) :=
  (rfl)

/-- The sheaf of differential `1`-forms is the sheaf of relative differentials. -/
def differentialFormsOneIso :
    differentialForms R (X ↘ Spec (.of R)) 1 ≅ X.relativeDifferentials R :=
  (SheafOfModules.exteriorPowerOneIso X.sheaf).app _

/-- The identification `Ω¹_{X/R} ≅ Ω_{X/R}` is the degree-one identification of the exterior power
with the module itself. -/
lemma differentialFormsOneIso_hom :
    (differentialFormsOneIso R X).hom =
      (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.app (X.relativeDifferentials R) :=
  (rfl)

/-- The sheaf `Ωᵖ_{X/R}` of differential `p`-forms of a scheme smooth over `Spec R`, as a finite
locally free sheaf. -/
def FiniteLocallyFreeSheaf.differentialForms [Smooth (X ↘ Spec (.of R))] (p : ℕ) :
    FiniteLocallyFreeSheaf X :=
  (exteriorPower X p).obj (relativeDifferentials R X)

/-- The underlying sheaf of `FiniteLocallyFreeSheaf.differentialForms R X p` is `Ωᵖ_{X/R}`. -/
@[simp]
lemma FiniteLocallyFreeSheaf.differentialForms_obj [Smooth (X ↘ Spec (.of R))] (p : ℕ) :
    (differentialForms R X p).obj =
      TauCeti.AlgebraicGeometry.differentialForms R (X ↘ Spec (.of R)) p := by
  rw [differentialForms, exteriorPower_obj_obj, relativeDifferentials_obj, differentialForms_def]

/-- On a scheme smooth over `Spec R`, `FiniteLocallyFreeSheaf.differentialForms R X p` is the
`p`-th exterior power of the finite locally free sheaf `Ω_{X/R}`. -/
lemma FiniteLocallyFreeSheaf.differentialForms_def [Smooth (X ↘ Spec (.of R))] (p : ℕ) :
    differentialForms R X p = (exteriorPower X p).obj (relativeDifferentials R X) :=
  (rfl)

variable {X}

/-- On a scheme smooth over `Spec R`, the rank of the sheaf of differential `p`-forms at `x` is
`r.choose p`, where `r` is the rank of `Ω_{X/R}` at `x`. -/
@[simp]
theorem FiniteLocallyFreeSheaf.rank_differentialForms_apply' [Smooth (X ↘ Spec (.of R))] (p : ℕ)
    (x : X) : (differentialForms R X p).rank x = ((relativeDifferentials R X).rank x).choose p := by
  rw [differentialForms_def, rank_exteriorPower_apply]

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the sheaf of differential
`p`-forms has rank `n.choose p` at every point. -/
theorem FiniteLocallyFreeSheaf.rank_differentialForms_apply (n p : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] (x : X) :
    haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    (differentialForms R X p).rank x = n.choose p := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  rw [rank_differentialForms_apply', rank_relativeDifferentials_apply R n]

variable (X)

/-- On a scheme smooth of relative dimension `n` over `Spec R`, there are no nonzero differential
`p`-forms for `p > n`. -/
theorem isZero_differentialForms {n p : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
    (hp : n < p) : IsZero (differentialForms R (X ↘ Spec (.of R)) p) := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  rw [← FiniteLocallyFreeSheaf.differentialForms_obj]
  exact (FiniteLocallyFreeSheaf.differentialForms R X p).isZero_obj_iff_forall_rank_eq_zero.2
    fun x ↦ by
      rw [FiniteLocallyFreeSheaf.rank_differentialForms_apply R n, Nat.choose_eq_zero_of_lt hp]

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the sheaf `Ωⁿ_{X/R}` of top-degree
differential forms is invertible. -/
theorem isInvertible_differentialForms (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    SheafOfModules.isInvertible X (differentialForms R (X ↘ Spec (.of R)) n) := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  rw [← FiniteLocallyFreeSheaf.differentialForms_obj]
  exact (FiniteLocallyFreeSheaf.differentialForms R X n).isInvertible_iff_forall_rank_eq_one.2
    fun x ↦ by rw [FiniteLocallyFreeSheaf.rank_differentialForms_apply R n, Nat.choose_self]

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the sheaf `Ωⁿ_{X/R}` of top-degree
differential forms is the determinant `det Ω_{X/R}` of the sheaf of relative differentials: the
determinant is the exterior power in the degree given by the rank, which is `n` everywhere. -/
def differentialFormsIsoDet (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    differentialForms R (X ↘ Spec (.of R)) n ≅
      (FiniteLocallyFreeSheaf.det (FiniteLocallyFreeSheaf.relativeDifferentials R X)).obj :=
  haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  eqToIso (differentialForms_def R X n) ≪≫
    ((locallyConstantExteriorPowerIso _
      (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n)).app _).symm ≪≫
    eqToIso (by
      rw [FiniteLocallyFreeSheaf.det_obj, FiniteLocallyFreeSheaf.relativeDifferentials_obj])

end

end TauCeti.AlgebraicGeometry
