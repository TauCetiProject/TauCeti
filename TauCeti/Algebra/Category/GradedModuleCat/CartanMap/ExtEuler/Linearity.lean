/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Poincare
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Poincare

/-!
# Bigraded Ext diagonality and the Cartan--Poincare identity

Let `A` be a finite-dimensional nonnegatively graded algebra, and let the `S i` be the
simple-class basis used by a graded Cartan matrix, with the projective basis consisting of the
corresponding idempotent projectives. If the full bigraded Ext Poincare matrix of the `S i` is
diagonal, the general linear-resolution criterion shows that chosen minimal resolutions of the
`S i` are linear. The Cartan--Poincare identity then gives

`C^T * P(-q) = 1`.

The bigraded condition is essential in the converse.  The diagonal polynomial `P` forgets all
off-diagonal Ext groups, while the q-Euler form can cancel groups in different cohomological
degrees.  Consequently the matrix identity alone is not asserted to imply linearity.

## Main result

* `TauCeti.cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal`: full bigraded
  diagonality implies the graded Cartan--Poincare identity.
* `TauCeti.cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal_of_semisimple`: the same
  implication over a semisimple degree-zero part, without chosen resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for diagonal bigraded Ext and the Cartan--Poincare identity.
* C. Nastasescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for minimal graded
  projective resolutions and the diagonal Ext criterion.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI}

section Cartan

variable [Module.Finite k A] [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- **Full bigraded diagonality implies the Cartan--Poincare identity.**  If every entry of the
full bigraded Ext Poincare matrix is diagonal, then the chosen minimal resolutions are linear and
`C^T * P(-q) = 1` in the chosen projective and simple bases.

The hypothesis retains the off-diagonal Ext data needed to detect linearity.  The conclusion uses
the diagonal Poincare matrix because, after linearity is known, those are all the surviving Ext
groups. -/
theorem cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)]
    (hr : ∀ i, (r i).IsMinimal) (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b)
    (hdiag : ∀ i j,
      Bigraded.IsDiagonal
        (bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
          (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
          b i j)) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS))ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) = 1 := by
  have hlin : ∀ i, (r i).IsLinear :=
    (forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
      S hS hconc h r hr hneg hb).2 hdiag
  exact gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one
    S he he₀ hI hne hself hS bP hbP h (fun i ↦ ⟨r i, hlin i⟩) hconc hb

include hbP in
/-- **The Cartan--Poincare identity over a semisimple degree-zero part.** If `A` is
finite-dimensional and nonnegatively graded, its degree-zero part is semisimple, the chosen
simples are concentrated in degree zero, and their full bigraded Ext Poincare matrix is diagonal,
then `C^T * P(-q) = 1`.

The semisimplicity hypothesis supplies minimal projective resolutions with finite-dimensional
terms, so no resolutions or minimality witnesses occur in the public statement. -/
theorem cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal_of_semisimple
    [IsSemisimpleRing (𝒜 0)]
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b)
    (hdiag : ∀ i j,
      Bigraded.IsDiagonal
        (bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
          (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
          b i j)) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS))ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) = 1 := by
  classical
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  exact cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal
    S he he₀ hI hne hself hS bP hbP h r hr hneg hconc hb hdiag

end Cartan

end TauCeti
