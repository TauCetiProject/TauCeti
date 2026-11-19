/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.VectorBundle.Determinant.Basic

/-!
# Sheaves of relative differential forms

For a scheme `X` over a commutative ring `R`, the sheaf of relative differential `p`-forms
`Ω^p_{X/R}` is the `p`-th exterior power of the sheaf of relative differentials `Ω_{X/R}`, taken
in the category of sheaves of `𝒪_X`-modules. The exterior power is that of the sheaf, not the
sheaf associated with the exterior powers of the global sections.

In degrees zero and one it is the structure sheaf and `Ω_{X/R}` itself. When `X` is smooth of
relative dimension `n` over `Spec R`, `Ω_{X/R}` is finite locally free of rank `n`, so `Ω^p_{X/R}`
is finite locally free of rank `n.choose p`. In particular the top power `Ω^n_{X/R}` is the
determinant `det Ω_{X/R}` of the cotangent bundle, an invertible sheaf, and `Ω^p_{X/R}` vanishes
for `p > n`. These are the sheaves of differential forms whose triviality and cohomology enter the
definition of a K3 surface (`n = 2`).

## Main declarations

* `AlgebraicGeometry.Scheme.differentialForms`: the sheaf `Ω^p_{X/R}`;
* `AlgebraicGeometry.Scheme.differentialFormsZeroIso` and
  `AlgebraicGeometry.Scheme.differentialFormsOneIso`: `Ω^0_{X/R} ≅ 𝒪_X` and
  `Ω^1_{X/R} ≅ Ω_{X/R}`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_differentialForms_apply`: in relative
  dimension `n`, `Ω^p_{X/R}` has rank `n.choose p` everywhere;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.determinant_obj_relativeDifferentials_obj`:
  the top power `Ω^n_{X/R}` is the determinant of `Ω_{X/R}`, so it is invertible
  (`TauCeti.AlgebraicGeometry.isInvertible_differentialForms`);
* `TauCeti.AlgebraicGeometry.isZero_differentialForms_of_lt`: `Ω^p_{X/R} = 0` for `p > n`.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.8, definitions before Example 8.20.1.
* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 1, Section 1.1.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The sheaf `Ω^p_{X/R}` of relative differential `p`-forms of a scheme `X` over `R`: the `p`-th
exterior power of the sheaf of relative differentials `Ω_{X/R}`, as a sheaf of `𝒪_X`-modules. -/
def _root_.AlgebraicGeometry.Scheme.differentialForms (p : ℕ) : X.Modules :=
  (SheafOfModules.exteriorPower X.sheaf p).obj (X.relativeDifferentials R)

/-- The sheaf of differential `0`-forms is the structure sheaf. -/
def _root_.AlgebraicGeometry.Scheme.differentialFormsZeroIso :
    X.differentialForms R 0 ≅ 𝟙_ X.Modules :=
  (SheafOfModules.exteriorPowerZeroIso X.sheaf).app (X.relativeDifferentials R)

/-- The sheaf of differential `1`-forms is the sheaf of relative differentials. -/
def _root_.AlgebraicGeometry.Scheme.differentialFormsOneIso :
    X.differentialForms R 1 ≅ X.relativeDifferentials R :=
  (SheafOfModules.exteriorPowerOneIso X.sheaf).app (X.relativeDifferentials R)

namespace FiniteLocallyFreeSheaf

/-- The sheaf `Ω^p_{X/R}` of relative differential `p`-forms of a scheme smooth over `Spec R`, as
a finite locally free sheaf. -/
def differentialForms [Smooth (X ↘ Spec (.of R))] (p : ℕ) : FiniteLocallyFreeSheaf X :=
  (exteriorPower X p).obj (relativeDifferentials R X)

/-- The underlying sheaf of `FiniteLocallyFreeSheaf.differentialForms R X p` is `Ω^p_{X/R}`. -/
@[simp]
lemma differentialForms_obj [Smooth (X ↘ Spec (.of R))] (p : ℕ) :
    (differentialForms R X p).obj = X.differentialForms R p := by
  rw [differentialForms, exteriorPower_obj_obj, relativeDifferentials_obj,
    Scheme.differentialForms]

variable {X}

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the sheaf of differential
`p`-forms has rank `n.choose p` at every point. -/
theorem rank_differentialForms_apply (n p : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] (x : X) :
    haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    (differentialForms R X p).rank x = n.choose p := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  rw [differentialForms, rank_exteriorPower_apply, rank_relativeDifferentials_apply R n]

variable (X)

/-- The sheaf of relative differentials of a scheme smooth of relative dimension `n` over
`Spec R`, as a finite locally free sheaf of constant rank `n`. -/
def FixedRank.relativeDifferentials (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    FixedRank X n :=
  haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  ⟨FiniteLocallyFreeSheaf.relativeDifferentials R X,
    (isConstantRank_iff _ n).mpr (rank_relativeDifferentials_apply R n)⟩

/-- The underlying sheaf of `FixedRank.relativeDifferentials R X n` is `Ω_{X/R}`. -/
@[simp]
lemma FixedRank.relativeDifferentials_obj_obj (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    (FixedRank.relativeDifferentials R X n).obj.obj = X.relativeDifferentials R :=
  haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  FiniteLocallyFreeSheaf.relativeDifferentials_obj R X

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the determinant of the cotangent
bundle `Ω_{X/R}` is the sheaf `Ω^n_{X/R}` of top-degree differential forms. -/
theorem determinant_obj_relativeDifferentials_obj (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    ((determinant X n).obj (FixedRank.relativeDifferentials R X n)).obj =
      X.differentialForms R n := by
  rw [determinant_obj_obj, FixedRank.relativeDifferentials_obj_obj, Scheme.differentialForms]

end FiniteLocallyFreeSheaf

variable {X}

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the sheaf `Ω^n_{X/R}` of
top-degree differential forms is invertible. -/
theorem isInvertible_differentialForms (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    SheafOfModules.isInvertible X (X.differentialForms R n) :=
  FiniteLocallyFreeSheaf.determinant_obj_relativeDifferentials_obj R X n ▸
    ((FiniteLocallyFreeSheaf.determinant X n).obj
      (FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials R X n)).property

/-- On a scheme smooth of relative dimension `n` over `Spec R`, there are no nonzero differential
`p`-forms for `p > n`: the sheaf `Ω^p_{X/R}` is zero. -/
theorem isZero_differentialForms_of_lt {n p : ℕ} (h : n < p)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] :
    IsZero (X.differentialForms R p) := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  rw [← FiniteLocallyFreeSheaf.differentialForms_obj,
    FiniteLocallyFreeSheaf.isZero_obj_iff_forall_rank_eq_zero]
  intro x
  rw [FiniteLocallyFreeSheaf.rank_differentialForms_apply R n, Nat.choose_eq_zero_of_lt h]

end

end TauCeti.AlgebraicGeometry
