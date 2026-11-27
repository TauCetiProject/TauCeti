/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.SquareMinor

/-!
# The square-minor formula for the torsion of a two-periodic complex

Let `C` be a two-periodic complex of vector spaces over a field `F`, a complex for the shape
`ComplexShape.up (ZMod 2)`, with ordered bases `c i` of its even and odd spaces `C₀` and `C₁`.
Split each basis into a first block `Eᵢ` of `q i` vectors followed by a second block `Dᵢ` of `p i`
vectors, so that `n i = q i + p i`, and assume `p (i + 1) = q i`: the block `D₁` of `C₁` has as
many vectors as the block `E₀` of `C₀`, and the block `D₀` as many as `E₁`. The *square minor*
`HomologicalComplex.parityTorsionMinor c hn hpq i` is the square matrix of the differential
`d : Cᵢ₊₁ → Cᵢ` restricted to the span of `Dᵢ₊₁` and followed by the coordinate projection onto
the span of `Eᵢ`; its rows are indexed by `Eᵢ` and its columns by `Dᵢ₊₁`. The differential itself
need not map `Dᵢ₊₁` into the span of `Eᵢ`.

If both square minors are invertible, then `C` is acyclic
(`HomologicalComplex.acyclic_of_det_parityTorsionMinor_ne_zero`): in each degree `i` the
boundaries `d (Dᵢ₊₁)` and the vectors `Dᵢ` form a basis of `Cᵢ`, whose matrix with respect to `c i`
is block triangular with diagonal blocks the square minor and the identity. Applied to these
boundary bases and to the lifts `Dᵢ₊₁`, the two brackets defining the torsion
`HomologicalComplex.parityTorsion` become the determinants of the minors, which gives the
*square-minor formula* (`HomologicalComplex.parityTorsion_eq_det_parityTorsionMinor_mul_inv`)

`τ(C) = det (A₁) · det (A₀)⁻¹`,

where `Aᵢ = parityTorsionMinor c hn hpq i` is the square minor of `d : Cᵢ₊₁ → Cᵢ`. There is no
additional sign when each `Eᵢ` precedes `Dᵢ` in the basis `c i`; coordinate blocks in any other
position are obtained by reordering the bases, which multiplies the torsion by a sign
(`HomologicalComplex.parityTorsion_reindex`). This is the two-periodic counterpart of the formula
`HomologicalComplex.reidemeisterTorsion_eq_finprod_det_torsionMinor` for bounded `ℤ`-graded
complexes, and both are derived from the shape-independent square-minor API
(`HomologicalComplex.squareMinor`, `HomologicalComplex.exactAt_of_det_squareMinor_ne_zero`,
`HomologicalComplex.torsionBracket_eq_det_squareMinor`). No boundedness enters: there are only two
minors. For the complex `F → F` given by
multiplication by `a` from the odd to the even degree, with `E₀` and `D₁` the two basis vectors, the
only nontrivial minor is `A₀ = (a)`, recovering the normalization `τ = a⁻¹` of
`HomologicalComplex.parityTorsion_of_d_zero_one`.

Expressing the torsion through minors makes it a rational function of the matrix coefficients of
the differentials near any complex whose minors are invertible; this is how its continuity is
proved in `TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Topology`.

## Main definitions

* `HomologicalComplex.parityTorsionMinor`: the square minor of the differential `Cᵢ₊₁ → Cᵢ`, with
  columns the last `p (i + 1)` basis vectors of `Cᵢ₊₁` and rows the first `q i` coordinates
  of `Cᵢ`.

## Main results

* `HomologicalComplex.acyclic_of_det_parityTorsionMinor_ne_zero`: a two-periodic complex whose two
  square minors are invertible is acyclic.
* `HomologicalComplex.parityTorsion_eq_det_parityTorsionMinor_mul_inv`: the square-minor formula.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002), §2
  (torsion through nonvanishing minors).
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I, Section 2
  (matrices and τ-chains).
* M. Hutchings, Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and Seiberg–Witten
  invariants of 3-manifolds*, Topology 38 (1999), §2 (the torsion of a two-periodic complex).
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F] {C : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))}
  {n q p : ZMod 2 → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (hn : ∀ i, n i = q i + p i)
  (hpq : ∀ i, p (i + 1) = q i)

/-- The square minor of the differential `d : Cᵢ₊₁ → Cᵢ` of a two-periodic complex in the bases
`c (i + 1)` and `c i`, each split by `hn` into a first block `E` of `q` vectors followed by a second
block `D` of `p` vectors: its entry at `(r, k)` is the coordinate along the `r`-th vector of `Eᵢ` of
the image under `d` of the `k`-th vector of `Dᵢ₊₁`. It is square because `p (i + 1) = q i`. -/
def parityTorsionMinor (i : ZMod 2) : Matrix (Fin (q i)) (Fin (q i)) F :=
  squareMinor c hn i (i + 1) (hpq i)

/-- The entries of the square minor `parityTorsionMinor c hn hpq i`. -/
@[simp]
theorem parityTorsionMinor_apply (i : ZMod 2) (r k : Fin (q i)) :
    parityTorsionMinor c hn hpq i r k = (c i).repr ((C.d (i + 1) i).hom (c (i + 1)
      (Fin.cast (hn (i + 1)).symm (Fin.natAdd (q (i + 1)) (Fin.cast (hpq i).symm k)))))
      (Fin.cast (hn i).symm (Fin.castAdd (p i) r)) :=
  squareMinor_apply ..

/-- The square minor `parityTorsionMinor c hn hpq i` is the square minor `squareMinor` of the
differential `Cⱼ → Cᵢ` for `j = i + 1`. The degree `j` is arbitrary so that the identification
`i + 1 + 1 = i` never has to be made inside dependent types. -/
theorem parityTorsionMinor_eq_squareMinor {i j : ZMod 2} (hj : i + 1 = j) (h : p j = q i) :
    parityTorsionMinor c hn hpq i = squareMinor c hn i j h := by
  subst hj
  rfl

variable {c hn hpq}

/-- A two-periodic complex whose two square minors `parityTorsionMinor c hn hpq i` are invertible
is acyclic. -/
theorem acyclic_of_det_parityTorsionMinor_ne_zero
    (hA : ∀ i, (parityTorsionMinor c hn hpq i).det ≠ 0) : C.Acyclic := fun i ↦ by
  have hi : i + 1 + 1 = i := CharTwo.add_cancel_right i 1
  have h₂ : p i = q (i + 1) := by simpa [hi] using hpq (i + 1)
  refine exactAt_of_det_squareMinor_ne_zero (c := c) (hn := hn) (h₁ := hpq i) (h₂ := h₂)
    ((ComplexShape.up _).prev_eq' hi) ((ComplexShape.up _).next_eq' rfl) ?_ ?_
  · exact hA i
  · rw [← parityTorsionMinor_eq_squareMinor c hn hpq hi]
    exact hA (i + 1)

/-- **The square-minor formula.** Let `C` be a two-periodic complex with bases `c i`, each split by
`hn` into a first block `Eᵢ` of `q i` vectors followed by a second block `Dᵢ` of `p i` vectors,
with `p (i + 1) = q i`. If both square minors `Aᵢ = parityTorsionMinor c hn hpq i` of the
differentials `Cᵢ₊₁ → Cᵢ` are invertible, then the torsion of `C` is `det (A₁) · det (A₀)⁻¹`; the
complex is then acyclic by `acyclic_of_det_parityTorsionMinor_ne_zero`, so this is nonzero. -/
theorem parityTorsion_eq_det_parityTorsionMinor_mul_inv
    (hA : ∀ i, (parityTorsionMinor c hn hpq i).det ≠ 0) :
    C.parityTorsion c =
      (parityTorsionMinor c hn hpq 1).det * ((parityTorsionMinor c hn hpq 0).det)⁻¹ := by
  have h01 : (0 : ZMod 2) + 1 = 1 := zero_add 1
  have h10 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hp₁ : p 1 = q 0 := by simpa [h01] using hpq 0
  have hp₀ : p 0 = q 1 := by simpa [h10] using hpq 1
  have hA₀ : (squareMinor c hn 0 1 hp₁).det ≠ 0 := by
    rw [← parityTorsionMinor_eq_squareMinor c hn hpq h01]
    exact hA 0
  have hA₁ : (squareMinor c hn 1 0 hp₀).det ≠ 0 := by
    rw [← parityTorsionMinor_eq_squareMinor c hn hpq h10]
    exact hA 1
  rw [parityTorsion_eq (acyclic_of_det_parityTorsionMinor_ne_zero hA)
      (squareMinorBoundaryBasis hA₀ hA₁) (squareMinorBoundaryBasis hA₁ hA₀) _
      (fun l ↦ (coe_squareMinorBoundaryBasis hA₁ hA₀ l).symm) _
      (fun l ↦ (coe_squareMinorBoundaryBasis hA₀ hA₁ l).symm),
    torsionBracket_eq_det_squareMinor c hn _ _ _ _ _ (coe_squareMinorBoundaryBasis hA₀ hA₁),
    torsionBracket_eq_det_squareMinor c hn _ _ _ _ _ (coe_squareMinorBoundaryBasis hA₁ hA₀),
    parityTorsionMinor_eq_squareMinor c hn hpq h01, parityTorsionMinor_eq_squareMinor c hn hpq h10]

end HomologicalComplex
