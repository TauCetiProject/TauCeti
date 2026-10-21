/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.NonDynkin
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Koszul.NonDynkin

/-!
# Koszulity of the affine `E₈` example

The arm-labelled affine `E₈ = T_{2,3,6}` graph `Γ = TauCeti.zigzagAffineE8Graph` is the graph of
the affine diagram `E₈`, so it is not a finite Dynkin diagram
(`TauCeti.not_exists_dynkinType_iso_zigzagAffineE8Graph`). The non-Dynkin theory of preprojective
and zigzag algebras therefore applies to it, although, being a tree, it has no orientation without
sinks. Over every field `k` and for every orientation `o`:

* the preprojective algebra `Π_k(Γ, o)` is infinite-dimensional;
* the left Koszul differential of `Π_k(Γ, o)` is injective at every vertex, so every right
  vertex module has a linear Koszul resolution of length two;
* the matrix Hilbert series of `Π_k(Γ, o)` is `C(-X)⁻¹`, where `C(q) = (1 + q²) I + q A` is the
  graded Cartan matrix of the zigzag algebra of affine `E₈`;
* every graded vertex simple of the zigzag algebra of affine `E₈` has a linear graded projective
  resolution.

These are the affine counterparts of the finite `D₄` and `E₈` examples, whose preprojective
algebras are finite-dimensional.

## Main results

* `TauCeti.not_finiteDimensional_preprojectiveAlgebra_affineE8`: the preprojective algebras of
  affine `E₈` are infinite-dimensional.
* `TauCeti.preprojectiveKoszulLeft_injective_affineE8`: their left Koszul differentials are
  injective.
* `TauCeti.preprojectiveHilbertSeries_affineE8_eq_inv_zigzagGradedCartanMatrix`: their Hilbert
  series is the inverse zigzag Cartan matrix at `q = -X`.
* `TauCeti.exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_affineE8`: the zigzag
  algebra of affine `E₈` is Koszul, in the sense that every graded vertex simple is linearly
  resolved.

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), for the non-Dynkin Koszul theorem and Hilbert series.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001), Section 3, for the zigzag algebra and its graded Cartan matrix.
* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, for the affine diagram
  `E₈`, which is `T_{2,3,6}`.
-/

public section

namespace TauCeti

open DoubledQuiver PowerSeries

universe w

variable (k : Type w) [Field k] (o : Orientation zigzagAffineE8Graph)

/-- **The preprojective algebra of affine `E₈` is infinite-dimensional**, for every orientation
and over every field. -/
theorem not_finiteDimensional_preprojectiveAlgebra_affineE8 :
    ¬ FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver zigzagAffineE8Graph o)) :=
  not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_exists_dynkinType_iso k
    connected_zigzagAffineE8Graph not_exists_dynkinType_iso_zigzagAffineE8Graph o

/-- **The preprojective algebra of affine `E₈` is Koszul**: for every orientation and over every
field, the left Koszul differential is injective at every vertex, so the Koszul complex of every
right vertex module is a linear projective resolution of length two. -/
theorem preprojectiveKoszulLeft_injective_affineE8
    (v : OrientedQuiver zigzagAffineE8Graph o) :
    Function.Injective (preprojectiveKoszulLeft k v) :=
  preprojectiveKoszulLeft_injective_of_not_exists_dynkinType_iso k connected_zigzagAffineE8Graph
    not_exists_dynkinType_iso_zigzagAffineE8Graph o v

/-- **The Hilbert series of the preprojective algebra of affine `E₈`** is `C(-X)⁻¹`, where
`C(q) = (1 + q²) I + q A` is the graded Cartan matrix of the zigzag algebra of affine `E₈`
(`TauCeti.zigzagGradedCartanMatrix_affineE8_eq`), for every orientation and over every field. -/
theorem preprojectiveHilbertSeries_affineE8_eq_inv_zigzagGradedCartanMatrix :
    (preprojectiveHilbertSeries k (OrientedQuiver zigzagAffineE8Graph o)).submatrix
        (OrientedQuiver.vertex zigzagAffineE8Graph o)
        (OrientedQuiver.vertex zigzagAffineE8Graph o) =
      ((zigzagGradedCartanMatrix k zigzagAffineE8Graph).map (Polynomial.aeval (-X : ℤ⟦X⟧)))⁻¹ :=
  preprojectiveHilbertSeries_eq_inv_zigzagGradedCartanMatrix_of_not_exists_dynkinType_iso k
    connected_zigzagAffineE8Graph not_exists_dynkinType_iso_zigzagAffineE8Graph o

/-- **The zigzag algebra of affine `E₈` is Koszul**: over every field, the graded simple module
at every vertex has a linear graded projective resolution. -/
theorem exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_affineE8 (v : Fin 9) :
    ∃ r : GradedProjectiveResolution.{w, w, w, w} (zigzagIntegerGrade k zigzagAffineE8Graph)
      (zigzagGradedSimple k zigzagAffineE8Graph v).grading, r.IsLinear :=
  exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_exists_dynkinType_iso k
    connected_zigzagAffineE8Graph not_exists_dynkinType_iso_zigzagAffineE8Graph v

end TauCeti
