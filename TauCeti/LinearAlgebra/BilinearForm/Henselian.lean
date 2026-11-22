/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.Fiber
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Henselian
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
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

## Main results

* `LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det`: unimodular forms are
  classified by rank and determinant square class.
* `LinearMap.BilinForm.IsSymm.equivalent_of_sub_mem_maximalIdeal`: unimodular forms which agree
  modulo the maximal ideal up to a linear map are isometric.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict_of_equivalent`: isometric forms have
  isometric Jordan constituents at every index.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_forall_equivalent_restrict`: forms are
  isometric exactly when their Jordan constituents are.
* `LinearMap.BilinForm.iIsOrtho.equivalent_of_forall_occCount_eq_and_isSquare` and
  `LinearMap.BilinForm.iIsOrtho.equivalent_iff_forall_occCount_eq_and_isSquare`: diagonal Jordan
  forms are classified by the multiplicity and unit-product square class at every scale `m`.

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

/-- Two forms with orthogonal bases whose diagonal entries have the shape `u i * π ^ k i` and
`v j * π ^ l j` for units `u i`, `v j` are isometric whenever, at every exponent `m`, the fiber
multiplicities agree and the product of the fiber units is a square. -/
theorem iIsOrtho.equivalent_of_forall_occCount_eq_and_isSquare
    {ι κ : Type*} [Fintype ι] [Fintype κ] {B : BilinForm R M} {C : BilinForm R N}
    {b : Basis ι R M} {c : Basis κ R N} (hb : B.iIsOrtho b) (hc : C.iIsOrtho c)
    (h2 : IsUnit (2 : R)) {u : ι → Rˣ} {v : κ → Rˣ} {k : ι → ℕ} {l : κ → ℕ} {π : R}
    (hbu : ∀ i, B (b i) (b i) = u i * π ^ k i)
    (hcv : ∀ j, C (c j) (c j) = v j * π ^ l j)
    (h : ∀ m : ℕ, Function.occCount k m = Function.occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i.val) * ∏ j : {j // l j = m}, v j.val)) :
    B.Equivalent C := by
  classical
  rw [hb.isSymm.equivalent_iff_toQuadraticMap_equivalent hc.isSymm h2.mem_nonZeroDivisors]
  refine (hb.equivalent_weightedSumSquares.trans ?_).trans hc.equivalent_weightedSumSquares.symm
  simp_rw [hbu, hcv]
  refine TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber k l
    (fun i ↦ (u i : R)) (fun j ↦ (v j : R)) (fun m ↦ π ^ m) fun m ↦ ?_
  let F := {i : ι // k i = m}; let G := {j : κ // l j = m}
  have hcard : Fintype.card F = Fintype.card G := by
    simpa only [F, G, Function.occCount_def, Nat.card_eq_fintype_card] using (h m).1
  let τF : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let τG : Fin (Fintype.card F) ≃ G := τF.trans (Fintype.equivOfCardEq hcard)
  have hsq : IsSquare ((∏ r, u (τF r).val) * ∏ r, v (τG r).val) := by
    rw [τF.prod_comp (fun i : F ↦ u i.val), τG.prod_comp (fun j : G ↦ v j.val)]; exact (h m).2
  have heqFin := (TauCeti.equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
    h2 (fun r ↦ u (τF r).val) (fun r ↦ v (τG r).val)).mpr hsq
  rw [weightedSumSquares_units, weightedSumSquares_units] at heqFin
  exact QuadraticMap.Equivalent.trans
    ⟨QuadraticForm.isometryEquivWeightedSumSquaresReindex (fun i : F ↦ (u i.val : R)) τF⟩
    (heqFin.trans
      ⟨(QuadraticForm.isometryEquivWeightedSumSquaresReindex
        (fun j : G ↦ (v j.val : R)) τG).symm⟩)

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

/-- **Diagonal Jordan classification at odd residue characteristic.** Over a Henselian local domain
with finite residue field and two invertible, two forms with orthogonal bases of diagonal entries
`u i * π ^ k i` and `v j * π ^ l j` (for units `u i`, `v j` and a nonzero non-unit `π`) are
isometric if and only if, at every scale `m`, the fiber multiplicities agree and the product of the
fiber units is a square. -/
theorem iIsOrtho.equivalent_iff_forall_occCount_eq_and_isSquare
    {ι κ : Type*} [Fintype ι] [Fintype κ] {b : Basis ι R M} {c : Basis κ R N}
    (hb : B.iIsOrtho b) (hc : B'.iIsOrtho c) (h2 : IsUnit (2 : R)) (hπ : π ≠ 0) (hπ' : ¬IsUnit π)
    {u : ι → Rˣ} {v : κ → Rˣ} {k : ι → ℕ} {l : κ → ℕ}
    (hbu : ∀ i, B (b i) (b i) = u i * π ^ k i)
    (hcv : ∀ j, B' (c j) (c j) = v j * π ^ l j) :
    B.Equivalent B' ↔ ∀ m : ℕ, Function.occCount k m = Function.occCount l m ∧
      IsSquare ((∏ i : {i // k i = m}, u i.val) * ∏ j : {j // l j = m}, v j.val) := by
  classical
  refine ⟨fun hBB' m ↦ ?_, hb.equivalent_of_forall_occCount_eq_and_isSquare hc h2 hbu hcv⟩
  have : Module.Free R M := .of_basis b; have : Module.Finite R M := .of_basis b
  have hS := hb.isJordanSplitting_span hπ hbu
  have hS' := hc.isJordanSplitting_span hπ hcv
  obtain ⟨e⟩ := hS.equivalent_restrict_of_equivalent hS' hb.isSymm h2 hπ hπ' hBB' m
  have hlib : LinearIndependent R (fun i : {i // k i = m} ↦ b i.val) :=
    b.linearIndependent.comp _ Subtype.val_injective
  have hlic : LinearIndependent R (fun j : {j // l j = m} ↦ c j.val) :=
    c.linearIndependent.comp _ Subtype.val_injective
  let bm := Basis.span hlib; let cm := Basis.span hlic
  have hcard : Fintype.card {i // k i = m} = Fintype.card {j // l j = m} := by
    rw [← Module.finrank_eq_card_basis bm, ← Module.finrank_eq_card_basis cm,
      e.toLinearEquiv.finrank_eq]
  refine ⟨by simpa only [Function.occCount_def, Nat.card_eq_fintype_card] using hcard, ?_⟩
  -- Divide out `π ^ m` on the `m`-th Jordan constituents and compare their diagonal determinants.
  obtain ⟨UB, hUB, -⟩ := isModular_def.mp (hS.isModular m)
  obtain ⟨UC, hUC, -⟩ := isModular_def.mp (hS'.isModular m)
  have hπm : π ^ m ≠ 0 := pow_ne_zero m hπ
  have hUeq : UB.Equivalent UC := ⟨{
    toLinearEquiv := e.toLinearEquiv
    map_app' := fun x y ↦ mul_left_cancel₀ hπm (by
      have h1 : π ^ m * UB x y = (B.restrict _) x y := by simpa using LinearMap.congr_fun₂ hUB x y
      have h2 : π ^ m * UC (e x) (e y) = (B'.restrict _) (e x) (e y) := by
        simpa using LinearMap.congr_fun₂ hUC (e x) (e y)
      rw [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
        LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, h1, h2]
      simpa using e.map_app y x) }⟩
  have hdet := hUeq.isSquare_det_mul_det bm (cm.reindex (Fintype.equivOfCardEq hcard.symm))
  rw [det_toMatrix_reindex,
    hb.toMatrix_span_of_smul_eq Subtype.val_injective (fun _ _ hab ↦ mul_left_cancel₀ hπm hab)
      (fun i ↦ by rw [hbu i.val, i.property, mul_comm]) hUB,
    hc.toMatrix_span_of_smul_eq Subtype.val_injective (fun _ _ hab ↦ mul_left_cancel₀ hπm hab)
      (fun j ↦ by rw [hcv j.val, j.property, mul_comm]) hUC,
    Matrix.det_diagonal, Matrix.det_diagonal,
    ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul, Units.isSquare_coe_iff] at hdet
  exact hdet

end JordanSplitting

end LinearMap.BilinForm
