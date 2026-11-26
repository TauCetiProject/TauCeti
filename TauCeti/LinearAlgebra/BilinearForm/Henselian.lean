/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.RingTheory.Henselian.Basic

/-!
# Unimodular symmetric forms and Jordan splittings over Henselian local rings

Over a Henselian local ring with finite residue field and two invertible, symmetric forms
with unit Gram determinant are classified by their rank and their determinant modulo squares.
The determinant may be computed in any caller-provided basis. The conclusion is an isometry
over the coefficient ring, preserving the bilinear forms themselves.

Diagonalization over the local ring gives an orthogonal basis with unit coefficients. The
unit diagonal classification then identifies the forms. This applies to `ℤ_p` for odd `p`,
including forms which arise by localizing an integral lattice that is unimodular only at `p`.

Such a form is already determined by its reduction modulo the maximal ideal: if a linear map
carries one form to the other modulo `𝔪`, the two determinants differ by a unit whose residue is
a square, hence by a square. Applied to the unimodular rescalings of the constituents of two
Jordan splittings, compared through the projections between them, this shows that the
constituents of a Jordan splitting are unique up to isometry, and that a symmetric form over a
Henselian local domain with finite residue field and two invertible is classified by the isometry
classes of its Jordan constituents, that is, by the rank and the determinant square class of each
of them.

For a form with an orthogonal basis whose self-pairings are `u i * π ^ k i`, with units `u i`,
the basis vectors with a given exponent `k i = m` span a constituent which is `π ^ m` times the
diagonal unimodular form of the units `u i`. Two such forms are therefore isometric when, for
every exponent, they have equally many basis vectors with that exponent and the products of the
corresponding units lie in one square class. At an odd prime every nondegenerate form over `ℤ_p`
has such a basis, so this reads the local isometry class off diagonal Jordan data.

## Main results

* `LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det`: unimodular forms are
  classified by rank and determinant square class.
* `LinearMap.BilinForm.IsSymm.equivalent_of_sub_mem_maximalIdeal`: unimodular forms which agree
  modulo the maximal ideal up to a linear map are isometric.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_of_equivalent`: isometric forms have
  isometric Jordan constituents at every index.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_forall_equivalent_restrict`: forms are
  isometric exactly when their Jordan constituents are.
* `LinearMap.BilinForm.iIsOrtho.equivalent_of_card_eq_of_isSquare_prod_mul_prod`: forms with
  orthogonal bases of self-pairings `u i * π ^ k i` are isometric when, for every exponent, the
  numbers of basis vectors and the square classes of the products of their units agree.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open Module QuadraticMap
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {R M N : Type*} [CommRing R]
  [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Unimodular classification at odd residue characteristic.** Symmetric forms with unit Gram
determinants on modules with bases of the same size are integrally isometric exactly when the
product of those determinants is a square. The bases and hence the determinant representatives
are arbitrary; positive rank is not required. -/
theorem IsSymm.equivalent_iff_isSquare_det_mul_det
    {B : BilinForm R M} {C : BilinForm R N} (hB : B.IsSymm) (hC : C.IsSymm)
    (h2 : IsUnit (2 : R)) {n : ℕ} (b : Basis (Fin n) R M) (c : Basis (Fin n) R N)
    (hBdet : IsUnit (B.toMatrix b).det) (hCdet : IsUnit (C.toMatrix c).det) :
    B.Equivalent C ↔ IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) := by
  classical
  constructor
  · exact fun h ↦ h.isSquare_det_mul_det b c
  · intro hdet
    -- Orthogonal diagonalization retains an explicit determinant change-of-basis equation.
    obtain ⟨w, hw, d, hd⟩ := hB.exists_equivalent_weightedSumSquares_of_isUnit_det h2 b hBdet
    obtain ⟨v, hv, e, he⟩ := hC.exists_equivalent_weightedSumSquares_of_isUnit_det h2 c hCdet
    have hsq : IsSquare ((∏ i, w i) * ∏ i, v i) := by
      rw [← Units.isSquare_coe_iff]
      have h := hdet.mul (IsSquare.sq (d * e))
      convert h using 1
      simp only [Units.val_mul, Units.coe_prod, hd, he]
      ring
    have hdiag := (TauCeti.equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
      h2 w v).mpr hsq
    exact (hB.equivalent_iff_toQuadraticMap_equivalent hC h2.mem_nonZeroDivisors).mpr
      (hw.trans (hdiag.trans hv.symm))

open IsLocalRing in
/-- **A unimodular form is determined by its reduction.** Let `C` and `C'` be symmetric forms with
unit Gram determinants in bases of the same size, over a Henselian local ring with finite residue
field and two invertible. If a linear map `φ` carries `C'` to `C` modulo the maximal ideal, that is
`C' x y - C (φ x) (φ y) ∈ 𝔪` for all `x` and `y`, then `C` and `C'` are isometric. -/
theorem IsSymm.equivalent_of_sub_mem_maximalIdeal {C : BilinForm R M} {C' : BilinForm R N}
    (hC : C.IsSymm) (hC' : C'.IsSymm) (h2 : IsUnit (2 : R)) {n : ℕ} (b : Basis (Fin n) R M)
    (b' : Basis (Fin n) R N) (hdet : IsUnit (C.toMatrix b).det)
    (hdet' : IsUnit (C'.toMatrix b').det) (φ : N →ₗ[R] M)
    (hφ : ∀ x y, C' x y - C (φ x) (φ y) ∈ maximalIdeal R) : C.Equivalent C' := by
  classical
  set A := LinearMap.toMatrix b' b φ
  -- Modulo `𝔪`, the Gram matrix of `C'` is congruent by `A` to that of `C`.
  have hmap : (residue R).mapMatrix (C'.toMatrix b') =
      (residue R).mapMatrix (A.transpose * C.toMatrix b * A) := by
    rw [← BilinForm.toMatrix_comp b b' C φ φ]
    ext k l
    simpa [sub_eq_zero] using (residue_eq_zero_iff _).mpr (hφ (b' k) (b' l))
  have hres : residue R ((C.toMatrix b).det * (C'.toMatrix b').det) =
      residue R (A.det * (C.toMatrix b).det) ^ 2 := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, hmap, ← RingHom.map_det, ← RingHom.map_det,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    simp only [map_mul]
    ring
  have hunit : IsUnit (A.det * (C.toMatrix b).det) := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    rw [h0, zero_pow two_ne_zero, residue_eq_zero_iff] at hres
    exact notMem_maximalIdeal.mpr (hdet.mul hdet') hres
  obtain ⟨x, hx, -⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq (n := 2)
    (by exact_mod_cast h2) hunit hres.symm
  exact (hC.equivalent_iff_isSquare_det_mul_det hC' h2 b b' hdet hdet').mpr
    ⟨x, by rw [← hx, _root_.sq]⟩

section JordanSplitting

variable [IsDomain R] {B : BilinForm R M} {B' : BilinForm R N} {π : R} {S : ℕ → Submodule R M}
  {S' : ℕ → Submodule R N}

open IsLocalRing in
/-- **Jordan constituents are unique up to isometry at odd residue characteristic.** Over a
Henselian local domain with finite residue field and two invertible, let `B` be a symmetric form on
a finite free module, isometric to a form `B'`. Then for Jordan splittings `S` of `B` and `S'` of
`B'` with respect to the same nonzero non-unit `π`, the constituents `S j` and `S' j` are isometric
at every index `j`. In particular the constituents of a Jordan splitting do not depend on the
splitting up to isometry. -/
theorem IsJordanSplitting.equivalent_restrict_of_equivalent [Module.Free R M] [Module.Finite R M]
    (hS : B.IsJordanSplitting π S) (hS' : B'.IsJordanSplitting π S') (hB : B.IsSymm)
    (h2 : IsUnit (2 : R)) (hπ : π ≠ 0) (hπ' : ¬IsUnit π) (hBB' : B.Equivalent B') (j : ℕ) :
    (B.restrict (S j)).Equivalent (B'.restrict (S' j)) :=
  hS.equivalent_restrict_of_forall_unimodular hS' hB hBB' hπ hπ' j
    fun _ _ hCs hC's _ _ b b' hdet hdet' φ hφ _ ↦ hCs.equivalent_of_sub_mem_maximalIdeal hC's h2
      b b' hdet hdet' φ fun x y ↦ Ideal.mem_of_dvd _ (hφ x y) ((mem_maximalIdeal π).mpr hπ')

/-- **Jordan splittings classify forms at odd residue characteristic.** Over a Henselian local
domain with finite residue field and two invertible, let `B` be a symmetric form on a finite free
module, and let `S` and `S'` be Jordan splittings of `B` and `B'` with respect to the same nonzero
non-unit `π`. Then `B` and `B'` are isometric exactly when their constituents of each index are
isometric. Each constituent is `π ^ j` times a unimodular form, classified by its rank and the
square class of its determinant (`LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det`).
-/
theorem IsJordanSplitting.equivalent_iff_forall_equivalent_restrict [Module.Free R M]
    [Module.Finite R M] (hS : B.IsJordanSplitting π S) (hS' : B'.IsJordanSplitting π S')
    (hB : B.IsSymm) (h2 : IsUnit (2 : R)) (hπ : π ≠ 0) (hπ' : ¬IsUnit π) :
    B.Equivalent B' ↔ ∀ j, (B.restrict (S j)).Equivalent (B'.restrict (S' j)) :=
  ⟨fun h j ↦ hS.equivalent_restrict_of_equivalent hS' hB h2 hπ hπ' h j,
    equivalent_of_isInternal hS.isInternal hS'.isInternal hS.apply_eq_zero hS'.apply_eq_zero⟩

end JordanSplitting

section OrthogonalBasis

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {B : BilinForm R M} {b : Basis ι R M} {π : R} {u : ι → Rˣ} {k : ι → ℕ}

omit [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)] in
/-- In an orthogonal basis with self-pairings `u i * π ^ k i`, the span of the basis vectors with
`k i = m` carries `π ^ m` times the diagonal form of the units `u i`. -/
private theorem restrict_span_image_fiber_eq_smul [DecidableEq ι] (hb : B.iIsOrtho b)
    (hbu : ∀ i, B (b i) (b i) = u i * π ^ k i) (m : ℕ) :
    B.restrict (Submodule.span R (b '' {i | k i = m})) =
      π ^ m • Matrix.toBilin (b.spanImageFiber k m) (Matrix.diagonal fun i ↦ (u i : R)) := by
  refine ext_basis (b.spanImageFiber k m) fun i j ↦ ?_
  have hD := congrFun₂ (toMatrix_toBilin (b.spanImageFiber k m)
    (Matrix.diagonal fun i : {i // k i = m} ↦ (u i : R))) i j
  rw [toMatrix_apply] at hD
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hD, restrict_apply,
    LinearMap.domRestrict_apply, Basis.spanImageFiber_apply, Basis.spanImageFiber_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [hbu, Matrix.diagonal_apply_eq, i.property, mul_comm]
  · rw [Matrix.diagonal_apply_ne _ hij, mul_zero]
    exact hb fun h ↦ hij (Subtype.ext h)

omit [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)] [Fintype ι] in
/-- The diagonal form of a family of units is symmetric, and its Gram determinant in any reindexing
of the basis is the product of the units. -/
private theorem isSymm_toBilin_diagonal_and_det_toMatrix_reindex {κ' : Type*} [Fintype κ']
    [DecidableEq κ'] (b : Basis κ' R M) (u : κ' → Rˣ) {n : ℕ} (e : κ' ≃ Fin n) :
    (Matrix.toBilin b (Matrix.diagonal fun i ↦ (u i : R))).IsSymm ∧
      ((Matrix.toBilin b (Matrix.diagonal fun i ↦ (u i : R))).toMatrix (b.reindex e)).det =
        ((∏ i, u i : Rˣ) : R) :=
  ⟨(Matrix.isSymm_toBilin_iff_isSymm _).mpr (Matrix.isSymm_diagonal _), by
    rw [det_toMatrix_reindex, toMatrix_toBilin, Matrix.det_diagonal, Units.coe_prod]⟩

/-- **Orthogonal bases over a Henselian local ring at odd residue characteristic.** Let `R` be a
Henselian local ring with finite residue field in which `2` is invertible, and let `b` and `c` be
orthogonal bases for bilinear forms `B` and `B'` with self-pairings `B (b i) (b i) = u i * π ^ k i`
and `B' (c j) (c j) = v j * π ^ l j`, for units `u i` and `v j`. If for every exponent `m` the two
bases have equally many vectors with exponent `m`, and the products of the units `u i` and `v j`
over these vectors lie in the same square class, then `B` and `B'` are isometric. -/
theorem iIsOrtho.equivalent_of_card_eq_of_isSquare_prod_mul_prod (h2 : IsUnit (2 : R))
    {B' : BilinForm R N} {c : Basis κ R N} {v : κ → Rˣ} {l : κ → ℕ} (hb : B.iIsOrtho b)
    (hc : B'.iIsOrtho c) (hbu : ∀ i, B (b i) (b i) = u i * π ^ k i)
    (hcv : ∀ j, B' (c j) (c j) = v j * π ^ l j) (hcard : ∀ m, #{i | k i = m} = #{j | l j = m})
    (hsq : ∀ m, IsSquare ((∏ i with k i = m, u i) * ∏ j with l j = m, v j)) :
    B.Equivalent B' := by
  classical
  refine equivalent_of_isInternal (b.isInternal_span_image_fiber k)
    (c.isInternal_span_image_fiber l) (fun m m' hm _ hx _ hy ↦
      hb.apply_eq_zero_of_mem_span_image_fiber hm hx hy) (fun m m' hm _ hx _ hy ↦
      hc.apply_eq_zero_of_mem_span_image_fiber hm hx hy) fun m ↦ ?_
  rw [restrict_span_image_fiber_eq_smul hb hbu, restrict_span_image_fiber_eq_smul hc hcv]
  -- The constituents are `π ^ m` times diagonal unimodular forms with determinants the products
  -- of the units, which the rank and determinant classification compares.
  obtain ⟨hC, hdet⟩ := isSymm_toBilin_diagonal_and_det_toMatrix_reindex (b.spanImageFiber k m)
    (fun i ↦ u i) (Fintype.equivFinOfCardEq (Fintype.card_subtype (k · = m)))
  obtain ⟨hC', hdet'⟩ := isSymm_toBilin_diagonal_and_det_toMatrix_reindex (c.spanImageFiber l m)
    (fun j ↦ v j)
    (Fintype.equivFinOfCardEq ((Fintype.card_subtype (l · = m)).trans (hcard m).symm))
  obtain ⟨f⟩ := (hC.equivalent_iff_isSquare_det_mul_det hC' h2 _ _ (hdet ▸ Units.isUnit _)
    (hdet' ▸ Units.isUnit _)).mpr (by
      rw [hdet, hdet', ← Units.val_mul]
      rw [Units.isSquare_coe_iff, ← prod_subtype _ (fun _ ↦ mem_filter_univ _) u,
        ← prod_subtype _ (fun _ ↦ mem_filter_univ _) v]
      exact hsq m)
  exact ⟨⟨f.toLinearEquiv, fun x y ↦ by simp⟩⟩

end OrthogonalBasis

end LinearMap.BilinForm
