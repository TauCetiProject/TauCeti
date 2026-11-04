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

`C^T * P(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`.

The diagonal polynomial `P` forgets all off-diagonal Ext groups, while the q-Euler form can
cancel groups in different cohomological degrees, so this identity alone is not asserted to imply
linearity.

The converse does hold for the total Ext Poincaré matrix `P_tot`, whose `(i, j)` entry is
`∑ n, dim_k Extⁿ(Sᵢ, ⨁ p, Sⱼ{p}) tⁿ`: linearity of the minimal resolutions is equivalent to
`C^T * P_tot(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`. Here `P_tot(-q)` is the matrix of
Maslov-graded Euler characteristics `TauCeti.Bigraded.maslovEuler` of the full bigraded Ext
Poincaré matrix. Comparing this identity with the conjugate-transpose relation for the q-Euler
matrix gives `TauCeti.Bigraded.euler = TauCeti.Bigraded.maslovEuler` entrywise. Minimality places
every Ext group on or above the diagonal. By `TauCeti.Bigraded.euler_eq_maslovEuler_iff_isDiagonal`
no cancellation is then possible, and the bigraded matrix is diagonal.

## Main results

* `TauCeti.cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal`: full bigraded
  diagonality implies the graded Cartan--Poincare identity.
* `TauCeti.cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal_of_semisimple`: the same
  implication over a semisimple degree-zero part, without chosen resolutions.
* `TauCeti.forall_isLinear_iff_cartan_poincare_maslovEuler`: chosen minimal resolutions are
  linear exactly when the Cartan--Poincaré identity holds for the total Ext Poincaré matrix.
* `TauCeti.forall_exists_isLinear_iff_cartan_poincare_maslovEuler`: the same equivalence over a
  semisimple degree-zero part, without chosen resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for diagonal bigraded Ext and the Cartan--Poincare identity.
* L. Positselski, *The correspondence between Hilbert series of quadratically dual algebras does
  not imply their having the Koszul property*, Funct. Anal. Appl. **29** (1995), 213--217, for
  quadratic algebras satisfying the diagonal identity without being Koszul.
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
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- **Full bigraded diagonality implies the Cartan--Poincare identity.**  If every entry of the
full bigraded Ext Poincare matrix is diagonal, then the chosen minimal resolutions are linear and
`C^T * P(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))` in the chosen projective and simple bases.

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
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS))ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) =
      Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  have hlin : ∀ i, (r i).IsLinear :=
    (forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal
      S hS hconc h r hr hneg hb).2 hdiag
  exact gradedCartanMatrix_transpose_mul_diagonalExtPoincareMatrix_map_eq_diagonal
    S he he₀ hI hne bP hbP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)
    (fun i ↦ gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS i)
    h (fun i ↦ ⟨r i, hlin i⟩) hconc hb

include hbP in
/-- **The Cartan--Poincare identity over a semisimple degree-zero part.** If `A` is
finite-dimensional and nonnegatively graded, its degree-zero part is semisimple, the chosen
simples are concentrated in degree zero, and their full bigraded Ext Poincare matrix is diagonal,
then `C^T * P(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`.

The diagonal entries are nonzero and need not be one; for projective covers of degree-zero
simples they are the constants `dim_k End_A(Sᵢ)`. The semisimplicity hypothesis supplies minimal
projective resolutions with finite-dimensional terms, so no resolutions or minimality witnesses
occur in the public statement. -/
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
    (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS))ᵀ *
        (diagonalExtPoincareMatrix.{uA} k (fun i ↦ (S i).obj) b).map
          (Polynomial.eval₂RingHom C (-T 1)) =
      Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  classical
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  exact cartan_poincare_of_bigradedExtPoincareMatrix_isDiagonal
    S he he₀ hI hne hself hS bP hbP h r hr hneg hconc hb hdiag

include hbP in
/-- **Linearity is the Cartan--Poincaré identity for the total Ext Poincaré series.** Let `P` be
the full bigraded Ext Poincaré matrix of the `Sᵢ`, and apply the Maslov-graded Euler
characteristic to each entry. The result is `P_tot(-q)`, where `P_tot` has `(i, j)` entry
`∑ n, dim_k Extⁿ(Sᵢ, ⨁ p, Sⱼ{p}) tⁿ`. Chosen minimal resolutions with finite-dimensional terms are
all linear exactly when `Cᵀ · P_tot(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`.

The diagonal Poincaré matrix `TauCeti.diagonalExtPoincareMatrix` cannot replace `P_tot` here: it
discards the off-diagonal Ext groups, whose contributions to the q-Euler form can cancel. -/
theorem forall_isLinear_iff_cartan_poincare_maslovEuler
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)]
    (hr : ∀ i, (r i).IsMinimal) (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (∀ i, (r i).IsLinear) ↔
      (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS))ᵀ *
          (bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
            (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
            b).map Bigraded.maslovEuler =
        Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  set bM := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
  set P := bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
    (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
      b with hP
  have hbM := gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS
  -- The inverted q-Euler matrix is the matrix of Alexander-graded Euler characteristics of `P`.
  have key : (gradedCartanMatrix 𝒜 bP bM)ᵀ * P.map Bigraded.euler =
      Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
    convert gradedCartanMatrix_transpose_mul_gradedExtEulerMatrix_map_invert_eq_diagonal
      S he he₀ hI hne bP hbP bM hbM h hconc using 2
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.map_apply, Matrix.map_apply, gradedExtEulerMatrix_of_of (X := S i) (Y := S j)
      (hi := hbM i) (hj := hbM j), hP, bigradedExtPoincareMatrix_apply,
      invert_gradedExtEuler_eq_euler_bigradedExtPoincareSeries k _ _ (hb i j)]
  -- Minimality puts every Ext group on or above the diagonal.
  have hiff (i j : I) :
      Bigraded.euler (P i j) = Bigraded.maslovEuler (P i j) ↔ Bigraded.IsDiagonal (P i j) :=
    Bigraded.euler_eq_maslovEuler_iff_isDiagonal _ fun _ _ hlt ↦ by
      rw [hP, bigradedExtPoincareMatrix_apply]
      exact (hr i).coeff_bigradedExtPoincareSeries_eq_zero_of_lt (fun p hp ↦ hconc i p hp.ne)
        (hconc j) _ b (by omega)
  rw [forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal S hS hconc h r hr hneg hb]
  constructor
  · intro hdiag
    rw [← key]
    congr 1
    exact Matrix.ext fun i j ↦ ((hiff i j).2 (hdiag i j)).symm
  · intro hid i j
    -- The diagonal matrix has nonzero determinant, so `Cᵀ` cancels on the left.
    have hdet : (gradedCartanMatrix 𝒜 bP bM)ᵀ.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det key
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_diagonal] at this
      exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hself i) this.symm
    have hP := (Matrix.isRegular_of_isLeftRegular_det
      (isRegular_iff_ne_zero.mpr hdet).left).left (hid.trans key.symm)
    exact (hiff i j).1 (congrFun (congrFun hP i) j).symm

include hbP in
/-- **Linearity is the Cartan--Poincaré identity over a semisimple degree-zero part.** If `A` is
finite-dimensional and nonnegatively graded with semisimple degree-zero part, every `Sᵢ` has a
linear graded projective resolution exactly when `Cᵀ · P_tot(-q) = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`
for the total Ext Poincaré matrix `P_tot`, as in
`TauCeti.forall_isLinear_iff_cartan_poincare_maslovEuler`. -/
theorem forall_exists_isLinear_iff_cartan_poincare_maslovEuler
    [IsSemisimpleRing (𝒜 0)]
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {b : ℕ}
    (hb : ∀ i j, IsGradedExtBoundedBy.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj b) :
    (∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear) ↔
      (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS))ᵀ *
          (bigradedExtPoincareMatrix (fun i ↦ (S i).obj)
            (fun i j ↦ (h.isGradedEulerAdmissible (S i).property (S j).property).internallyFinite)
            b).map Bigraded.maslovEuler =
        Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  classical
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  rw [forall_exists_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal S hS hconc h hneg hb,
    ← forall_isLinear_iff_cartan_poincare_maslovEuler S he he₀ hI hne hself hS bP hbP h r hr
      hneg hconc hb,
    forall_isLinear_iff_bigradedExtPoincareMatrix_isDiagonal S hS hconc h r hr hneg hb]

end Cartan

end TauCeti
