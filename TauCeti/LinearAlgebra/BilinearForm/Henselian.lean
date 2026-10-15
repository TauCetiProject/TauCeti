/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
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

## Main results

* `LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det`: unimodular forms are
  classified by rank and determinant square class.
* `LinearMap.BilinForm.IsSymm.equivalent_of_sub_mem_maximalIdeal`: unimodular forms which agree
  modulo the maximal ideal up to a linear map are isometric.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_of_equivalent`: isometric forms have
  isometric Jordan constituents at every index.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_forall_equivalent_restrict`: forms are
  isometric exactly when their Jordan constituents are.

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
  let := h2.invertible
  constructor
  · exact fun h ↦ h.isSquare_det_mul_det b c
  · intro hdet
    -- Orthogonal diagonalization retains an explicit determinant change-of-basis equation.
    obtain ⟨w, hw, d, hd⟩ := hB.exists_equivalent_weightedSumSquares_of_isUnit_det h2 b hBdet
    obtain ⟨v, hv, e, he⟩ := hC.exists_equivalent_weightedSumSquares_of_isUnit_det h2 c hCdet
    have hsq : IsSquare ((∏ i, w i) * ∏ i, v i) := by
      rw [← TauCeti.isSquare_units_val_iff]
      have h := hdet.mul (IsSquare.sq (d * e))
      convert h using 1
      simp only [Units.val_mul, Units.coe_prod, hd, he]
      ring
    have hdiag := (TauCeti.equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
      h2 w v).mpr hsq
    exact (hB.equivalent_iff_toQuadraticMap_equivalent hC).mpr
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
    (B.restrict (S j)).Equivalent (B'.restrict (S' j)) := by
  obtain ⟨e⟩ := _root_.id hBB'
  set ε := e.toLinearEquiv
  have hε (u v : M) : B' (ε u) (ε v) = B u v := e.map_app v u
  have hεs (u v : N) : B (ε.symm u) (ε.symm v) = B' u v := by
    rw [← hε, ε.apply_symm_apply, ε.apply_symm_apply]
  have : Module.Finite R N := Module.Finite.equiv ε
  have : Module.Free R N := Module.Free.of_equiv ε
  have := hS.finite j
  have := hS.free j
  have := hS'.finite j
  have := hS'.free j
  have hπj : π ^ j ∈ nonZeroDivisors R := pow_mem (mem_nonZeroDivisors_of_ne_zero hπ) j
  -- Write the constituents as `π ^ j` times the unimodular forms `C` and `C'`.
  obtain ⟨C, hC, hCp⟩ := isModular_def.mp (hS.isModular j)
  obtain ⟨C', hC', hC'p⟩ := isModular_def.mp (hS'.isModular j)
  have hCapp (x y : S j) : π ^ j * C x y = B x y := by
    simpa using LinearMap.congr_fun₂ hC x y
  have hC'app (x y : S' j) : π ^ j * C' x y = B' x y := by
    simpa using LinearMap.congr_fun₂ hC' x y
  have hB' : B'.IsSymm := ⟨fun x y ↦ by rw [← hεs, ← hεs, hB.eq]⟩
  have hCs : C.IsSymm := ⟨fun x y ↦ (mul_cancel_left_mem_nonZeroDivisors hπj).mp (by
    rw [hCapp, hCapp, hB.eq])⟩
  have hC's : C'.IsSymm := ⟨fun x y ↦ (mul_cancel_left_mem_nonZeroDivisors hπj).mp (by
    rw [hC'app, hC'app, hB'.eq])⟩
  -- The projection to `S j` carries `C'` to `C` modulo `π`.
  obtain ⟨f, -, hf⟩ := hS.exists_pow_succ_dvd_sub (mem_nonZeroDivisors_of_ne_zero hπ) j
  have hdvd (x : S' j) (z : M) : π ^ j ∣ B (ε.symm x) z := by
    rw [← hε, ε.apply_symm_apply]
    exact hS'.pow_dvd_apply x.2 (ε z)
  let b := Module.finBasis R (S j)
  let b' := (Module.finBasis R (S' j)).reindex
    (finCongr (hS.finrank_eq_of_equivalent hS' hBB' hπ hπ' j).symm)
  obtain ⟨u⟩ := hCs.equivalent_of_sub_mem_maximalIdeal hC's h2 b b'
    (b.isUnit_det_of_isPerfPair C hCp) (b'.isUnit_det_of_isPerfPair C' hC'p)
    (f ∘ₗ ε.symm.toLinearMap ∘ₗ (S' j).subtype) fun x y ↦ by
      obtain ⟨c, hc⟩ := hf (ε.symm x) (ε.symm y) (hdvd x) (hdvd y)
      have hsub : C' x y - C (f (ε.symm x)) (f (ε.symm y)) = π * c :=
        (mul_cancel_left_mem_nonZeroDivisors hπj).mp (by
          rw [mul_sub, hC'app, hCapp, ← mul_assoc, ← pow_succ, ← hc, hεs])
      simpa [hsub] using Ideal.mul_mem_right c _ ((mem_maximalIdeal π).mpr hπ')
  rw [← hC, ← hC']
  exact (equivalent_smul_iff hπj).mpr ⟨u⟩

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

end LinearMap.BilinForm
