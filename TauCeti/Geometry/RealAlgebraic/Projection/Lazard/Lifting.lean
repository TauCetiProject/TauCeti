/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Projection.Lazard.Product
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Coordinate
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.IrreducibleBasis
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Lifting
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Product
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Lazard lifting of irreducible bases and families

On a preconnected analytic submanifold, invariance of the Lazard projection gives a common
Lazard delineation of any subfamily of an irreducible basis whose members have nonzero formal
constant coefficients. The original fibers may be nullified, and the formal projection
polynomials may vanish everywhere on the base.

The projection controls the leading coefficient, constant coefficient and discriminant of the
subfamily product. Single-polynomial analytic lifting applies to this product, and recovering
its factors gives simultaneous root membership, multiplicities and removed base exponents.
Pairwise resultants enter through the discriminant of the product; separate delineations of
the members would not by themselves supply this common stack.

The excluded irreducible factors are associates of the distinguished coordinate; by
pairwise nonassociation there is at most one. Its delineation is the zero section. The trailing
coefficients in the projection decide uniformly whether `0` is a root of the Lazard evaluations
of the other members, so the zero section can be adjoined to their common stack. This gives a
Lazard delineation of the whole basis, and, since the contents lie in the projection, of the
original family.

## Main results

* `TauCeti.nonempty_lazardDelineation_subfamily_of_lazardProjection`: a common Lazard
  delineation of the basis members with nonzero constant coefficient.
* `TauCeti.nonempty_lazardDelineation_basis_of_lazardProjection`: a Lazard delineation of the
  whole irreducible basis.
* `TauCeti.nonempty_lazardDelineation_of_lazardProjection`: a Lazard delineation of the family.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.3.
-/

public section

open MvPolynomial Polynomial Set

namespace TauCeti

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B A : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- The noncoordinate members of any subfamily of an irreducible basis have a common Lazard
delineation over a preconnected analytic submanifold on which the full Lazard projection is
valuation-invariant. The hypothesis on constant coefficients concerns formal polynomials, not
their values on the base. No nonnullification or preservation of fiber degrees is required.

In particular, take `A` to be the members of `B` with nonzero constant coefficient. Basis
members outside `A`, including associates of the distinguished coordinate, are unrestricted. -/
theorem nonempty_lazardDelineation_subfamily_of_lazardProjection
    (hB : F.IsIrreducibleBasis B) (hAB : A ⊆ B)
    (hconst : ∀ b ∈ A, b.coeff 0 ≠ 0)
    (hS : IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hproj : ∀ q ∈ F.lazardProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.lazardValuation x = q.lazardValuation y) :
    Nonempty (LazardDelineation
      (fun b : A ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)) S) := by
  classical
  let p : Polynomial (MvPolynomial (Fin n) ℝ) := ∏ b ∈ A, b
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b hb ↦ (hB.irreducible b (hAB hb)).ne_zero
  have hpconst : p.coeff 0 ≠ 0 := by
    rw [coeff_zero_prod]
    exact Finset.prod_ne_zero_iff.mpr hconst
  obtain ⟨D⟩ := p.nonempty_lazardDelineation_of_lazardValuation_eq hS hconn
    hp (hB.isSquarefreeBasis.discr_prod_ne_zero hAB)
    (fun x hx y hy ↦ Finset.lazardValuation_leadingCoeff_prod_eq_of_lazardProjection hAB x y
      (fun q hq ↦ hproj q hq x hx y hy))
    (fun x hx y hy ↦ by
      rw [trailingCoeff_eq_coeff_zero hpconst]
      exact Finset.lazardValuation_coeff_zero_prod_eq_of_lazardProjection hAB x y
        (fun q hq ↦ hproj q hq x hx y hy))
    (fun x hx y hy ↦ hB.lazardValuation_discr_prod_eq_of_lazardProjection hAB x y
      (fun q hq ↦ hproj q hq x hx y hy))
  -- The two equivalences and renaming preserve products. Restate the singleton product
  -- family extensionally before transporting its dependent delineation type.
  have hfamily :
      (fun _ : Unit ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm p)) =
        (fun _ : Unit ↦ ∏ b : A,
          rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)) := by
    funext _
    simp only [p, map_prod]
    exact (Finset.prod_coe_sort A _).symm
  rw [hfamily] at D
  exact ⟨D.ofProd hconn (by
    rw [← congrFun hfamily ()]
    exact (map_ne_zero_iff _ (rename_injective _ finSuccEquivLast.symm.injective)).mpr
      (EmbeddingLike.map_ne_zero_iff.mpr hp))⟩

/-- **Lazard lifting of an irreducible basis.** Over a preconnected analytic submanifold on which
the Lazard projection is valuation-invariant, an irreducible basis has a Lazard delineation.

The members with nonzero constant coefficient are lifted together through their product. The
remaining member, if any, is an associate of the distinguished coordinate; it contributes the zero
section. Invariance of the constant coefficients of the other members makes `0` a root of their
Lazard evaluations either over every base point or over none. -/
theorem nonempty_lazardDelineation_basis_of_lazardProjection (hB : F.IsIrreducibleBasis B)
    (hS : IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hproj : ∀ q ∈ F.lazardProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.lazardValuation x = q.lazardValuation y) :
    Nonempty (LazardDelineation
      (fun b : B ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)) S) := by
  classical
  let A := B.filter fun b ↦ b.coeff 0 ≠ 0
  have hAB : A ⊆ B := Finset.filter_subset _ _
  obtain ⟨D⟩ := nonempty_lazardDelineation_subfamily_of_lazardProjection hB hAB
    (fun b hb ↦ (Finset.mem_filter.1 hb).2) hS hconn hproj
  refine nonempty_lazardDelineation_of_comp (f := fun b : A ↦ ⟨b.1, hAB b.2⟩) D hconn ?_ ?_
  · -- A basis member with zero constant coefficient is a nonzero multiple of the coordinate.
    rintro ⟨b, hb⟩ hbA
    have h0 : b.coeff 0 = 0 := not_not.1 fun h ↦ hbA ⟨⟨b, Finset.mem_filter.2 ⟨hb, h⟩⟩, rfl⟩
    obtain ⟨u, hu⟩ := Polynomial.irreducible_X.associated_of_dvd (hB.irreducible b hb)
      (Polynomial.X_dvd_iff.2 h0)
    obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.1 u.isUnit
    obtain ⟨a, ha, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hc
    have hbX : b = Polynomial.C (MvPolynomial.C a) * Polynomial.X := by
      rw [← hu, ← hcu, mul_comm]
    exact ⟨a, ha.ne_zero, by simp [hbX]⟩
  · -- Constancy of the constant-coefficient valuation decides the root `0` uniformly.
    rintro ⟨b, hbA⟩
    refine D.isRoot_zero_of_lazardValuation_coeff_zero_eq (k := ⟨b, hbA⟩) rfl fun x hx y hy ↦ ?_
    rw [← trailingCoeff_eq_coeff_zero (Finset.mem_filter.1 hbA).2]
    exact hproj _ (Finset.trailingCoeff_mem_lazardProjection (hAB hbA)) x hx y hy

/-- **Lazard lifting of a family.** Over a preconnected analytic submanifold on which the Lazard
projection of a family with respect to an irreducible basis is valuation-invariant, the family has
a Lazard delineation. Its members may be nullified at points of the base. -/
theorem nonempty_lazardDelineation_of_lazardProjection (hB : F.IsIrreducibleBasis B)
    (hS : IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hproj : ∀ q ∈ F.lazardProjection B, ∀ x ∈ S, ∀ y ∈ S,
      q.lazardValuation x = q.lazardValuation y) :
    Nonempty (LazardDelineation
      (fun f : F ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm f.1)) S) :=
  (nonempty_lazardDelineation_basis_of_lazardProjection hB hS hconn hproj).map fun D ↦
    D.ofIrreducibleBasis hB fun _ hf ↦ hproj _ (Finset.content_mem_lazardProjection hf)

end TauCeti
