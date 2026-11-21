/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# Locally free quotients of the sheaf of differentials

For a commutative ring `k`, a scheme `X` over `Spec k` and `d : ℕ`, the sheaf of relative
differentials `Ω_{X/k}` *admits a locally free quotient of rank `d`* when there is an epimorphism
of `𝒪_X`-modules `Ω_{X/k} ⟶ E` onto a finite locally free sheaf `E` of constant rank `d`. This is
the condition of Nobile's triviality criterion for the Nash blowup and the hypothesis of the
differential smoothness criteria.

On the empty scheme the predicate holds for every `d`, the zero sheaf having every constant rank.
The predicate is sensitive to the characteristic: for the cusp `y² = x³` and `d = 1` it holds over
`𝔽_2`, where `dx` is torsion and `dx ↦ 0`, `dy ↦ 1` is a free quotient, but not over `ℚ`.

## Main declarations

* `HasLocallyFreeQuotientOfDifferentials k X d`: `Ω_{X/k}` admits a locally free quotient of
  rank `d`;
* `hasLocallyFreeQuotientOfDifferentials_iff`: the defining existential condition;
* `HasLocallyFreeQuotientOfDifferentials.of_isOpenImmersion` and
  `HasLocallyFreeQuotientOfDifferentials.restrict`: the predicate passes to open subschemes;
* `hasLocallyFreeQuotientOfDifferentials_of_smoothOfRelativeDimension`: on a scheme smooth of
  relative dimension `d`, the identity of `Ω_{X/k}` witnesses the predicate.

## References

* A. Nobile, *Notes on Nash modification*, Section 2 and Proposition 2.3.
* D. Duarte and L. Núñez-Betancourt, *Nash blowups in prime characteristic*, Lemma 2.4.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (k : Type u) [CommRing k]

/-- The sheaf of relative differentials `Ω_{X/k}` admits a locally free quotient of rank `d`:
there are a finite locally free `𝒪_X`-module `E` of constant rank `d` and an epimorphism of
`𝒪_X`-modules `Ω_{X/k} ⟶ E`. -/
def HasLocallyFreeQuotientOfDifferentials (X : Scheme.{u}) [X.Over (Spec (.of k))] (d : ℕ) :
    Prop :=
  ∃ (E : FiniteLocallyFreeSheaf.FixedRank X d) (q : X.relativeDifferentials k ⟶ E.obj.obj), Epi q

/-- `Ω_{X/k}` admits a locally free quotient of rank `d` if and only if there is an epimorphism
from it onto a finite locally free sheaf of constant rank `d`. -/
theorem hasLocallyFreeQuotientOfDifferentials_iff (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (d : ℕ) :
    HasLocallyFreeQuotientOfDifferentials k X d ↔
      ∃ (E : FiniteLocallyFreeSheaf.FixedRank X d) (q : X.relativeDifferentials k ⟶ E.obj.obj),
        Epi q :=
  Iff.rfl

variable {k}

namespace HasLocallyFreeQuotientOfDifferentials

/-- A locally free quotient of rank `d` of `Ω_{X/k}` restricts along an open immersion
`f : Y ⟶ X` over `Spec k`: the pullback of the quotient, composed with the identification of
`Ω_{Y/k}` with the restriction of `Ω_{X/k}`, is a locally free quotient of rank `d` of
`Ω_{Y/k}`. -/
theorem of_isOpenImmersion {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : Y ⟶ X) [IsOpenImmersion f] [f.IsOver (Spec (.of k))] {d : ℕ}
    (h : HasLocallyFreeQuotientOfDifferentials k X d) :
    HasLocallyFreeQuotientOfDifferentials k Y d := by
  obtain ⟨E, q, hq⟩ := h
  refine ⟨(FiniteLocallyFreeSheaf.FixedRank.pullback f).obj E,
    (relativeDifferentialsRestrictIso k f).inv ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app _ ≫
      (Scheme.Modules.pullback f).map q ≫ eqToHom (by simp), ?_⟩
  -- Pullback is a left adjoint, so it preserves epimorphisms.
  exact epi_comp' inferInstance (epi_comp' inferInstance (epi_comp' inferInstance inferInstance))

/-- A locally free quotient of rank `d` of `Ω_{X/k}` restricts to every open subscheme of `X`. -/
theorem restrict {X : Scheme.{u}} [X.Over (Spec (.of k))] {d : ℕ}
    (h : HasLocallyFreeQuotientOfDifferentials k X d) (V : X.Opens) :
    HasLocallyFreeQuotientOfDifferentials k V d :=
  h.of_isOpenImmersion V.ι

end HasLocallyFreeQuotientOfDifferentials

variable (k) (X : Scheme.{u}) [X.Over (Spec (.of k))] (d : ℕ)
  [SmoothOfRelativeDimension d (X ↘ Spec (.of k))]

/-- On a scheme smooth of relative dimension `d` over `Spec k`, the identity of `Ω_{X/k}`, which
is finite locally free of constant rank `d`, is a locally free quotient of rank `d`. -/
theorem hasLocallyFreeQuotientOfDifferentials_of_smoothOfRelativeDimension :
    HasLocallyFreeQuotientOfDifferentials k X d :=
  ⟨FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials k X d, eqToHom (by simp),
    inferInstance⟩

end

end TauCeti.AlgebraicGeometry
