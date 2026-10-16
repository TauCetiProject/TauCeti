/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Poincare
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Poincare

/-!
# Detecting linear simple resolutions in the Cartan--Poincare identity

Let `A` be a finite-dimensional nonnegatively graded algebra, let `S i` be finite graded
modules concentrated in degree zero, and choose a minimal graded projective resolution `r i` of
each `S i`.  The resolutions are linear exactly when the full bigraded Ext Poincare series from
every `S i` to every finite simple degree-zero target is diagonal.

When the `S i` are the simple-class basis used by a graded Cartan matrix and the projective
basis consists of the corresponding idempotent projectives, this criterion combines with the
Cartan--Poincare identity.  Linearity is equivalent to the conjunction of full bigraded
diagonality and

`C^T * P(-q) = 1`.

The bigraded condition is essential in the converse.  The diagonal polynomial `P` forgets all
off-diagonal Ext groups, while the q-Euler form can cancel groups in different cohomological
degrees.  Consequently the matrix identity alone is not asserted to imply linearity.

## Main results

* `TauCeti.bigradedExtPoincareMatrix`: the full bigraded Ext Poincare matrix of a finite
  graded-module family.
* `TauCeti.forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal`: simultaneous
  linearity of chosen minimal resolutions is equivalent to diagonal support of every entry of
  that matrix.
* `TauCeti.cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal`: full bigraded
  diagonality implies the graded Cartan--Poincare identity.

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

variable (S : I → (gradedFiniteModules 𝒜).FullSubcategory) in
/-- The **full bigraded Ext Poincare matrix** of a finite graded-module family, truncated below a
common cohomological degree `b`.  Its `(i,j)` entry records all dimensions
`dim_k Ext^n(S_i,S_j{p})`, not only the diagonal terms `n = p`. -/
noncomputable def bigradedExtPoincareMatrix
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (b : ℕ) : Matrix I I Bigraded.Series :=
  fun i j ↦ bigradedExtPoincareSeries.{uA} k (GradedModuleCat.shift 𝒜)
    (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite b

omit [GradedAlgebra 𝒜] in
/-- An entry of the full bigraded Ext Poincare matrix is the bigraded Ext Poincare series of the
corresponding pair of modules. -/
@[simp]
theorem bigradedExtPoincareMatrix_apply
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) (b : ℕ) (i j : I) :
    bigradedExtPoincareMatrix S h b i j =
      bigradedExtPoincareSeries.{uA} k (GradedModuleCat.shift 𝒜)
        (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite b :=
  (rfl)

omit [GradedAlgebra 𝒜] in
/-- Raising the common truncation degree past a common cohomological vanishing bound does not
change the full bigraded Ext Poincare matrix. -/
theorem bigradedExtPoincareMatrix_eq_of_le
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) {b b' : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b)
    (hbb' : b ≤ b') :
    bigradedExtPoincareMatrix S h b' = bigradedExtPoincareMatrix S h b :=
  Matrix.ext fun i j ↦ bigradedExtPoincareSeries_eq_of_le
    (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite (hb i j) hbb'

/-- **Chosen minimal resolutions of an exhaustive simple family are linear exactly when every
entry of its full bigraded Ext Poincare matrix is diagonal.**  The family is exhaustive up to
internal shift, while its chosen representatives are concentrated in degree zero.  The matrix
uses any common cohomological Ext bound. -/
theorem forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory) (hS : IsExhaustiveGradedSimpleFamily S)
    (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (∀ i, (r i).IsLinear) ↔
      ∀ i j, Bigraded.IsDiagonal (bigradedExtPoincareMatrix S h b i j) := by
  constructor
  · intro hlin i j
    apply (isDiagonal_bigradedExtPoincareSeries_iff _ (hb i j)).2
    intro n p hnp
    have hshift : Subsingleton (Ext.{uA} (S i).obj ((S j).obj.shiftObj p) n) :=
      (hlin i).subsingleton_ext_shiftObj_of_ne (hSzero j) n p hnp
    rw [← GradedModuleCat.shiftFunctor_obj] at hshift
    exact (extLinearEquivOfIso k (Iso.refl (S i).obj)
      ((GradedModuleCat.shiftPowIso 𝒜 p).app (S j).obj) n).injective.subsingleton
  · intro hdiag i
    apply ((hr i).isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N hNfinite hNsimple hNzero n p hnp
    let _ : Module.Finite k N := hNfinite
    let _ : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
    let N' : (gradedFiniteModules 𝒜).FullSubcategory :=
      ⟨N, gradedFiniteModules_iff.2 inferInstance⟩
    obtain ⟨j, ⟨eN⟩⟩ := hS.exists_iso_of_concentrated S hSzero N' hNsimple hNzero
    change N ≅ (S j).obj at eN
    have hExt : Subsingleton
        (GradedExt.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj n p) :=
      ((isDiagonal_bigradedExtPoincareSeries_iff
        (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite
        (hb i j)).1 (hdiag i j)) n p hnp
    rw [← GradedModuleCat.shiftFunctor_obj]
    exact (extLinearEquivOfIso k (Iso.refl (S i).obj)
      ((GradedModuleCat.shiftFunctor (𝒜 := 𝒜) p).mapIso eN ≪≫
        ((GradedModuleCat.shiftPowIso 𝒜 p).app (S j).obj).symm) n).injective.subsingleton

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
      Bigraded.IsDiagonal (bigradedExtPoincareMatrix S h b i j)) :
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS))ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) = 1 := by
  have hlin : ∀ i, (r i).IsLinear :=
    (forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
      S hS hconc h r hr hneg hb).2 hdiag
  exact gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_one
    S he he₀ hI hne hself hS bP hbP h (fun i ↦ ⟨r i, hlin i⟩) hconc hb

end Cartan

end TauCeti
