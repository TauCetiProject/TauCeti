/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Matrix
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ModuleResolution

/-!
# The graded Cartan matrix and the q-Euler matrix

Let `A` be a finite-dimensional algebra over a field `k`, graded by `𝒜 : ℤ → Submodule k A`. The
q-Euler form `χ_q` pairs `K₀^gr(proj A)` with `G₀^gr(mod A)`, and, when every pair of finite graded
modules is graded Euler-admissible, it also pairs `G₀^gr(mod A)` with itself. The two forms are
related by the graded Cartan map `c`: `χ_q(c x, y) = χ_q(x, y)`
(`TauCeti.gradedExtEulerSesquilinear_gradedCartanMap`).

In matrices this reads as follows. Write `C` for the graded Cartan matrix, whose `(l, i)` entry is
the `l`th coordinate of `c [Pᵢ]`, and `E` for the matrix of `χ_q` on `G₀^gr(mod A)`. Since `χ_q` is
q-antilinear in its first argument, `Cᴴ * E` is the matrix of the projective/module pairing, where
`Cᴴ` is the transpose of `C` with `q ↦ q⁻¹` applied to every entry.

If the projective basis consists of the classes `[A eᵢ]` of degree-zero idempotents `eᵢ`, and the
module basis consists of classes `[Sⱼ]` with `gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`, then the
projective/module pairing matrix is diagonal with entries `gdim(eᵢ • Sᵢ)`, so
`Cᴴ * E = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`. Over a general field, for `Sᵢ` the simple head of
`A eᵢ` (for instance, `eᵢ` a primitive idempotent of a finite-dimensional algebra) concentrated in
degree zero, this entry is the constant `dim_k End_A(Sᵢ)`, the dimension of a division algebra by
Schur, as in the ungraded identity
`TauCeti.cartanMatrix_transpose_mul_extEulerMatrix_eq_diagonal`. If every finite graded module has a
finite graded-projective resolution, the graded Cartan matrix is invertible
(`TauCeti.isUnit_det_gradedCartanMatrix_of_le_admitsFiniteResolution`), and therefore
`E = (Cᴴ)⁻¹ * diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`.

When `gdim(eᵢ • Sⱼ) = δᵢⱼ`, the projective/module pairing matrix is the identity. Such a
projective basis is, for instance, `TauCeti.gradedIndecomposableProjectiveClassBasis` for an
exhaustive family of indecomposable `A eᵢ`. Hence `Cᴴ * E = 1`: the q-Euler matrix of the graded
simples is the inverse of the conjugate transpose of the graded Cartan matrix, and the determinant
of the graded Cartan matrix is a unit of `ℤ[q,q⁻¹]`. These are the graded analogues of
`TauCeti.cartanMatrix_transpose_mul_extEulerMatrix_eq_one` and
`TauCeti.extEulerMatrix_eq_inverseCartanMatrix_transpose`.

Euler-admissibility of all pairs of finite graded modules is a genuine hypothesis. For the dual
numbers `k[ε]/(ε²)` with `ε` in degree two, the graded Cartan matrix is `[1 + q²]`
(`TauCeti.gradedCartanMatrix_dualNumber`), whose determinant is not a unit, so the residue field is
not graded Euler-admissible against itself
(`TauCeti.not_isGradedEulerAdmissible_dualNumberGradedResidue`).

## Main results

* `TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix`: in arbitrary bases,
  `Cᴴ * E` is the matrix of the projective/module q-Euler form.
* `TauCeti.gradedExtEulerMatrix_eq_diagonal_smulGradedDimension`: the classes `[A eᵢ]` and `[Sⱼ]`
  have diagonal pairing matrix with entries `gdim(eᵢ • Sᵢ)`.
* `TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_diagonal`:
  `Cᴴ * E = diagonal (fun i ↦ gdim(eᵢ • Sᵢ))` over a general field.
* `TauCeti.gradedExtEulerMatrix_eq_inv_gradedCartanMatrix_map_invert_transpose_mul_diagonal` and
  `TauCeti.gradedExtEuler_eq_inv_gradedCartanMatrix_map_invert_transpose_mul_smulGradedDimension`:
  under finite graded-projective resolutions, `E = (Cᴴ)⁻¹ * diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`.
* `TauCeti.gradedExtEulerMatrix_gradedSimpleClassBasis_eq_one`: the classes `[A eᵢ]` and the graded
  simple-class basis have identity pairing matrix.
* `TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one`: `Cᴴ * E = 1`.
* `TauCeti.gradedExtEulerMatrix_eq_inv_gradedCartanMatrix_map_invert_transpose`:
  `E = (Cᴴ)⁻¹`.
* `TauCeti.gradedExtEuler_eq_inv_gradedCartanMatrix_map_invert_transpose`: `χ_q(Sᵢ, Sⱼ)` is the
  `(i, j)` entry of `(Cᴴ)⁻¹`.
* `TauCeti.isUnit_det_gradedCartanMatrix`: the graded Cartan matrix has unit determinant.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Sections 2.2 and 3.1--3.2, for the q-Euler form,
  its sesquilinearity convention and the conjugate-transpose relation with the graded Cartan
  matrix.
* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Proposition 3.13, for the ungraded relation between the
  Cartan matrix and the Euler form.
* Peter Webb, *A Course in Finite Group Representation Theory*, Chapter 7, Section 7.4, for the
  division-algebra correction over a general field.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe uk uA uI uJ uJ'

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

/-! ### Matrices -/

variable {I : Type uI} {J : Type uJ} {J' : Type uJ'} [Fintype I] [Fintype J]

omit [Fintype I] in
/-- An entry of the projective/module q-Euler matrix is the projective/module q-Euler form of the
corresponding basis vectors. -/
@[simp]
theorem gradedExtEulerMatrix_apply_eq_gradedProjectiveExtEuler
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J' (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) (i : I) (j : J') :
    gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteProjectiveModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteProjectiveModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
        isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules bP bM i j =
      gradedProjectiveExtEuler 𝒜 (bP i) (bM j) := by
  rw [gradedProjectiveExtEuler_def]
  exact gradedExtEulerMatrix_apply _ _ _ _ _ _ _ _ bP bM i j

/-- **The conjugate-transposed graded Cartan matrix times the q-Euler matrix is the
projective/module q-Euler matrix.** For bases `bP` of `K₀^gr(proj A)` and `bM`, `bM'` of
`G₀^gr(mod A)`, write `C` for the graded Cartan matrix in `bP` and `bM`, and `E` for the q-Euler
matrix of `G₀^gr(mod A)` in `bM` and `bM'`. Then `(C.map invert)ᵀ * E` is the matrix of the
projective/module q-Euler form in `bP` and `bM'`. -/
theorem gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (bM' : Module.Basis J' (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    ((gradedCartanMatrix 𝒜 bP bM).map (LaurentPolynomial.invert (R := ℤ)))ᵀ *
        gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteModules 𝒜)
          (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
          isExtensionClosed_gradedFiniteModules_gradedAbelian
          gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift h bM bM' =
      gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteProjectiveModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteProjectiveModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
        isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules bP bM' := by
  refine Matrix.ext fun i j ↦ ?_
  -- The entry lemma is applied through a `have`: the two sides type the Grothendieck groups as
  -- `gradedFiniteModulesExactStructure 𝒜` and as the full-subcategory structure it unfolds to,
  -- which `rw` does not identify.
  have hE (l : J) : gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteModules 𝒜)
      (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
      isExtensionClosed_gradedFiniteModules_gradedAbelian
      gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift h bM bM' l j =
      gradedExtEulerSesquilinear isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift
        gradedFiniteModules_gradedAbelian_shift h (bM l) (bM' j) :=
    gradedExtEulerMatrix_apply _ _ _ _ _ _ _ h bM bM' l j
  rw [Matrix.mul_apply, gradedExtEulerMatrix_apply_eq_gradedProjectiveExtEuler,
    ← gradedExtEulerSesquilinear_gradedCartanMap h, gradedCartanMap_basis_apply_eq_sum 𝒜 bP bM i]
  -- Retype the form on `gradedFiniteModulesExactStructure 𝒜`, so that `map_sum` applies.
  let B : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)
      →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
        LaurentPolynomial ℤ :=
    gradedExtEulerSesquilinear.{uA} isExtensionClosed_gradedFiniteModules_gradedAbelian
      isExtensionClosed_gradedFiniteModules_gradedAbelian gradedFiniteModules_gradedAbelian_shift
      gradedFiniteModules_gradedAbelian_shift h
  change _ = B _ _
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hE, Matrix.transpose_apply, Matrix.map_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
  -- `B` is the form on the right, typed on the other presentation of `G₀^gr(mod A)`.
  rfl

section Diagonal

variable [DecidableEq I] (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  (bM : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
  (hbM : ∀ i, bM i = LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) (S i))

omit [Fintype I] in
include he₀ hne hbP hbM in
/-- **The classes `[A eᵢ]` and `[Sⱼ]` pair diagonally under the q-Euler form**: if
`gdim(eᵢ • Sⱼ) = 0` for `i ≠ j`, then in a projective basis of classes `[A eᵢ]` and a module basis
of classes `[Sⱼ]`, the matrix of the projective/module q-Euler form is diagonal with entries
`gdim(eᵢ • Sᵢ)`. Over a general field this entry is the constant `dim_k End_A(Sᵢ)` when `Sᵢ` is
the simple head of `A eᵢ` (for instance, `eᵢ` a primitive idempotent of a finite-dimensional
algebra) concentrated in degree zero, so it need not be `1`. -/
theorem gradedExtEulerMatrix_eq_diagonal_smulGradedDimension :
    gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteProjectiveModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteProjectiveModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
        isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules bP bM =
      Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  refine Matrix.ext fun i j ↦ ?_
  rw [gradedExtEulerMatrix_apply_eq_gradedProjectiveExtEuler, hbP, hbM,
    gradedProjectiveExtEuler_ofIdeal_span_singleton (he i) (he₀ i) (hI i),
    gradedIdempotentCoordinate_of, Matrix.diagonal_apply]
  split_ifs with hij
  · rw [hij]
  · exact hne hij

include he₀ hne hbP hbM in
/-- **The general-field graded Cartan/q-Euler identity.** Let `C` be the graded Cartan matrix in a
projective basis of classes `[A eᵢ]` and a module basis of classes `[Sⱼ]`, with `gdim(eᵢ • Sⱼ) = 0`
for `i ≠ j`, and let `E` be the q-Euler matrix of the `Sᵢ`. If every pair of finite graded modules
is graded Euler-admissible, then `(C.map invert)ᵀ * E` is the diagonal matrix of the graded
dimensions `gdim(eᵢ • Sᵢ)`. -/
theorem gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_diagonal
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) :
    ((gradedCartanMatrix 𝒜 bP bM).map (LaurentPolynomial.invert (R := ℤ)))ᵀ *
        gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteModules 𝒜)
          (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
          isExtensionClosed_gradedFiniteModules_gradedAbelian
          gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift h bM bM =
      Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  rw [gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix,
    gradedExtEulerMatrix_eq_diagonal_smulGradedDimension S he he₀ hI hne bP hbP bM hbM]

variable (hres : gradedFiniteModules 𝒜 ≤
  (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
    (gradedFiniteProjectiveModules 𝒜))

include he₀ hne hbP hbM in
/-- **The q-Euler matrix in terms of the inverse graded Cartan matrix, over a general field.** If
every finite graded module has a finite graded-projective resolution, then in the bases of
`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_diagonal`,
`E = ((C.map invert)ᵀ)⁻¹ * diagonal (fun i ↦ gdim(eᵢ • Sᵢ))`. -/
theorem gradedExtEulerMatrix_eq_inv_gradedCartanMatrix_map_invert_transpose_mul_diagonal :
    gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
        (isGradedEulerAdmissibleOn_gradedFiniteModules hres) bM bM =
      ((gradedCartanMatrix 𝒜 bP bM).map (LaurentPolynomial.invert (R := ℤ)))ᵀ⁻¹ *
        Matrix.diagonal fun i ↦ (S i).obj.smulGradedDimension (e i) := by
  have hdet : IsUnit
      ((gradedCartanMatrix 𝒜 bP bM).map (LaurentPolynomial.invert (R := ℤ)))ᵀ.det := by
    rw [Matrix.det_transpose, ← AlgEquiv.mapMatrix_apply, ← AlgEquiv.map_det]
    exact (isUnit_map_iff (LaurentPolynomial.invert (R := ℤ)) _).2
      (isUnit_det_gradedCartanMatrix_of_le_admitsFiniteResolution 𝒜 hres bP bM)
  rw [← gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_diagonal S he he₀ hI
    hne bP hbP bM hbM, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

include he₀ hne hbP hbM in
/-- **The q-Euler characteristic of two simples over a general field**: if every finite graded
module has a finite graded-projective resolution, then `χ_q(Sᵢ, Sⱼ)` is the `(i, j)` entry of
`((C.map invert)ᵀ)⁻¹` times `gdim(eⱼ • Sⱼ)`, in the bases of
`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_diagonal`. -/
theorem gradedExtEuler_eq_inv_gradedCartanMatrix_map_invert_transpose_mul_smulGradedDimension
    (i j : I) :
    gradedExtEuler k (GradedModuleCat.shift 𝒜)
        ((isGradedEulerAdmissibleOn_gradedFiniteModules hres).isGradedEulerAdmissible
          (S i).property (S j).property) =
      ((gradedCartanMatrix 𝒜 bP bM).map (LaurentPolynomial.invert (R := ℤ)))ᵀ⁻¹ i j *
        (S j).obj.smulGradedDimension (e j) := by
  have hE := congrFun (congrFun
    (gradedExtEulerMatrix_eq_inv_gradedCartanMatrix_map_invert_transpose_mul_diagonal S he he₀ hI
      hne bP hbP bM hbM hres) i) j
  rwa [Matrix.mul_diagonal,
    gradedExtEulerMatrix_of_of (X := S i) (Y := S j) (hi := hbM i) (hj := hbM j)] at hE

end Diagonal

section Simple

variable [DecidableEq I] (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
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

omit [Fintype I] in
include hbP in
/-- **The classes `[A eᵢ]` are dual to the graded simples under the q-Euler form**: in a projective
basis consisting of the classes `[A eᵢ]` and the graded simple-class basis `[Sⱼ]`, the matrix of the
projective/module q-Euler form is the identity. -/
theorem gradedExtEulerMatrix_gradedSimpleClassBasis_eq_one :
    gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteProjectiveModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteProjectiveModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift
        isGradedEulerAdmissibleOn_gradedFiniteProjectiveModules_gradedFiniteModules bP
        (gradedSimpleClassBasis S he he₀ hne hself hS) = 1 := by
  rw [gradedExtEulerMatrix_eq_diagonal_smulGradedDimension S he he₀ hI hne bP hbP _
    (gradedSimpleClassBasis_apply S he he₀ hne hself hS), funext hself, Matrix.diagonal_one]

include hbP in
/-- **The conjugate-transposed graded Cartan matrix inverts the q-Euler matrix of the graded
simples.** Let `C` be the graded Cartan matrix in a projective basis of classes `[A eᵢ]` and the
graded simple-class basis `[Sⱼ]`, with `gdim(eᵢ • Sⱼ) = δᵢⱼ`, and let `E` be the q-Euler matrix of
the graded simples. If every pair of finite graded modules is graded Euler-admissible, then
`(C.map invert)ᵀ * E = 1`. -/
theorem gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) :
    ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS)).map
        (LaurentPolynomial.invert (R := ℤ)))ᵀ *
      gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift h
        (gradedSimpleClassBasis S he he₀ hne hself hS)
        (gradedSimpleClassBasis S he he₀ hne hself hS) = 1 := by
  rw [gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix,
    gradedExtEulerMatrix_gradedSimpleClassBasis_eq_one S he he₀ hI hne hself hS bP hbP]

include hbP in
/-- **The q-Euler matrix of the graded simples is the inverse of the conjugate-transposed graded
Cartan matrix**: `E = ((C.map invert)ᵀ)⁻¹`, in the bases of
`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one`. -/
theorem gradedExtEulerMatrix_eq_inv_gradedCartanMatrix_map_invert_transpose
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) :
    gradedExtEulerMatrix (GradedModuleCat.shift 𝒜) (gradedFiniteModules 𝒜)
        (gradedFiniteModules 𝒜) isExtensionClosed_gradedFiniteModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteModules_gradedAbelian_shift gradedFiniteModules_gradedAbelian_shift h
        (gradedSimpleClassBasis S he he₀ hne hself hS)
        (gradedSimpleClassBasis S he he₀ hne hself hS) =
      ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS)).map
        (LaurentPolynomial.invert (R := ℤ)))ᵀ⁻¹ :=
  (Matrix.inv_eq_right_inv
    (gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one S he he₀ hI hne
      hself hS bP hbP h)).symm

include hbP in
/-- **The q-Euler characteristic of two graded simples is an entry of the inverse
conjugate-transposed graded Cartan matrix**: `χ_q(Sᵢ, Sⱼ)` is the `(i, j)` entry of
`((C.map invert)ᵀ)⁻¹`, in the bases of
`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one`. -/
theorem gradedExtEuler_eq_inv_gradedCartanMatrix_map_invert_transpose
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) (i j : I) :
    gradedExtEuler k (GradedModuleCat.shift 𝒜)
        (h.isGradedEulerAdmissible (S i).property (S j).property) =
      ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS)).map
        (LaurentPolynomial.invert (R := ℤ)))ᵀ⁻¹ i j := by
  rw [← gradedExtEulerMatrix_eq_inv_gradedCartanMatrix_map_invert_transpose S he he₀ hI hne hself hS
      bP hbP h,
    gradedExtEulerMatrix_of_of (X := S i) (Y := S j) (hi := gradedSimpleClassBasis_apply ..)
      (hj := gradedSimpleClassBasis_apply ..)]

include hbP in
/-- **Graded Cartan unimodularity**: in the bases of
`TauCeti.gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one`, if every pair of
finite graded modules is graded Euler-admissible, then the determinant of the graded Cartan matrix
is a unit of `ℤ[q,q⁻¹]`. -/
theorem isUnit_det_gradedCartanMatrix
    (h : IsGradedEulerAdmissibleOn.{uA} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜)) :
    IsUnit (gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS)).det := by
  have hdet := Matrix.isUnit_det_of_right_inverse
    (gradedCartanMatrix_map_invert_transpose_mul_gradedExtEulerMatrix_eq_one S he he₀ hI hne
      hself hS bP hbP h)
  rw [Matrix.det_transpose, ← AlgEquiv.mapMatrix_apply, ← AlgEquiv.map_det] at hdet
  exact (isUnit_map_iff (LaurentPolynomial.invert (R := ℤ)) _).1 hdet

end Simple

end TauCeti
