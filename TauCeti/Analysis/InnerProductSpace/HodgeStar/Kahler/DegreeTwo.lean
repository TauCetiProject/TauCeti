/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.TwoForm
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
import TauCeti.Analysis.InnerProductSpace.Complex
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
import TauCeti.Geometry.Symplectic.Wirtinger

/-!
# Degree-two Wirtinger inequality and Kähler two-form calibration

This file develops the degree-two Wirtinger theory for orthogonal almost complex structures and
complex inner product spaces:

* On any complex inner product space (without finite-dimensionality), `TauCeti.kahlerTwoForm E` has
  comass at most `1` (`TauCeti.norm_kahlerTwoForm_le`), comass equal to `1` when `E` is nontrivial
  (`TauCeti.norm_kahlerTwoForm`), and calibrates precisely the ordered pairs `(v₀, i • v₀)` with
  `‖v₀‖ = 1` (`TauCeti.isCalibratedFrame_kahlerTwoForm_iff`).
* For linearly independent `(v, w)` in a finite-dimensional real inner product space with an
  orthogonal almost complex structure `J` (`AlmostComplexStructure.inner_apply_eq_norm_ιMulti_iff`),
  or in a finite-dimensional Hermitian space (`TauCeti.kahlerTwoForm_apply_eq_norm_ιMulti_iff`),
  `ω(v, w) = ‖v ∧ w‖` holds exactly when `w = a • v + b • J v` with `0 < b`.
* In finite dimensions, `TauCeti.alternatingFormEquiv_ofComplexModule_kahlerForm` identifies
  `kahlerTwoForm E` as the Riesz dual of `(AlmostComplexStructure.ofComplexModule E).kahlerForm`,
  and `TauCeti.ofComplexModule_kahlerForm_eq_sum` expands that bivector in any complex orthonormal
  basis.

## Main results

* `TauCeti.AlmostComplexStructure.inner_apply_eq_norm_ιMulti_iff`: non-orthonormal degree-two
  Wirtinger equality for an orthogonal almost complex structure.
* `TauCeti.norm_kahlerTwoForm_le`, `TauCeti.norm_kahlerTwoForm`: degree-two Wirtinger comass
  bound and equality on arbitrary complex inner product spaces.
* `TauCeti.isCalibratedFrame_kahlerTwoForm_iff`: calibrated-pair classification on arbitrary
  complex inner product spaces.
* `TauCeti.kahlerTwoForm_apply_eq_norm_ιMulti_iff`: non-orthonormal degree-two Wirtinger equality
  on finite-dimensional Hermitian vector spaces.
* `TauCeti.alternatingFormEquiv_ofComplexModule_kahlerForm` and
  `TauCeti.ofComplexModule_kahlerForm_eq_sum`: Riesz identification and orthonormal basis expansion
  of `(AlmostComplexStructure.ofComplexModule E).kahlerForm`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), §II.6.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Lemma 2.2.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Non-orthonormal degree-two Wirtinger equality** for an orthogonal almost complex structure:
for linearly independent `v` and `w`, `⟪J v, w⟫ = ‖v ∧ w‖` exactly when `w = a • v + b • J v`
with `0 < b`. -/
theorem inner_apply_eq_norm_ιMulti_iff {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {v w : V} (h : LinearIndependent ℝ ![v, w]) :
    ⟪J v, w⟫ = ‖ιMulti ℝ 2 ![v, w]‖ ↔ ∃ a b : ℝ, 0 < b ∧ w = a • v + b • J v := by
  have hcompat : (J.symplecticForm hJ).Compatible J := symplecticForm_compatible hJ
  have hwedge : (J.symplecticForm hJ).wedgeNorm J v w = ‖ιMulti ℝ 2 ![v, w]‖ := by
    rw [SymplecticForm.wedgeNorm_def, symplecticForm_associatedBilinForm_apply hJ,
      symplecticForm_associatedBilinForm_apply hJ, symplecticForm_associatedBilinForm_apply hJ,
      ← Real.sqrt_sq (norm_nonneg _), norm_ιMulti_sq]
    congr 1
    simp [Matrix.gram, Matrix.det_fin_two, sq, real_inner_comm]
  rw [← J.symplecticForm_apply hJ, ← hwedge]
  exact hcompat.apply_eq_wedgeNorm_iff_of_linearIndependent h

end AlmostComplexStructure

section DegreeTwo

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The Kähler two-form has comass at most one on every complex inner product space. -/
theorem norm_kahlerTwoForm_le : ‖kahlerTwoForm E‖ ≤ 1 := by
  refine (kahlerTwoForm E).opNorm_le_bound zero_le_one fun v ↦ ?_
  rw [kahlerTwoForm_apply, Real.norm_eq_abs, one_mul, Fin.prod_univ_two]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm (v 0) (v 1))

end DegreeTwo

section DegreeTwoNormed

/-- **Wirtinger inequality in degree two**: on every nontrivial complex inner product space (no
finite-dimensionality required), the Kähler two-form has comass one. -/
theorem norm_kahlerTwoForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [Nontrivial E] :
    ‖kahlerTwoForm E‖ = 1 := by
  refine le_antisymm norm_kahlerTwoForm_le ?_
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  set u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hx
  have hval : kahlerTwoForm E ![u, Complex.I • u] = 1 := by
    simp [kahlerTwoForm_apply, inner_smul_right, hu]
  simpa [hval, Fin.prod_univ_two, norm_smul, hu] using
    (kahlerTwoForm E).le_opNorm ![u, Complex.I • u]

end DegreeTwoNormed

section DegreeTwoEquality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- **Equality case of degree-two Wirtinger** on any Hermitian inner product space (no
finite-dimensionality required): an ordered pair `(v₀, v₁)` is calibrated by `kahlerTwoForm E`
precisely when `‖v₀‖ = 1` and `v₁ = i • v₀`. -/
theorem isCalibratedFrame_kahlerTwoForm_iff (v : Fin 2 → E) :
    (kahlerTwoForm E).IsCalibratedFrame v ↔ ‖v 0‖ = 1 ∧ v 1 = Complex.I • v 0 := by
  rw [ContinuousAlternatingMap.isCalibratedFrame_iff]
  constructor
  · rintro ⟨hv, hval⟩
    refine ⟨hv.1 0, ?_⟩
    have hre : (inner ℂ (v 0) (v 1)).re = 0 := by
      rw [← RCLike.re_to_complex, ← TauCeti.inner_real_eq_re_inner ℂ]
      exact hv.2 (by decide : (0 : Fin 2) ≠ 1)
    have hinner : inner ℂ (v 0) (v 1) = Complex.I :=
      Complex.ext hre (by simpa [kahlerTwoForm_apply] using hval)
    have hinner' : inner ℂ (Complex.I • v 0) (v 1) = 1 := by
      rw [inner_smul_left, hinner]
      simp
    have hI : ‖Complex.I • v 0‖ = 1 := by simp [norm_smul, hv.1 0]
    exact ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℂ) hI (hv.1 1)).1 hinner').symm
  · rintro ⟨hv0, hv1⟩
    refine ⟨?_, ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [TauCeti.inner_real_eq_re_inner ℂ, hv1, inner_smul_left, inner_smul_right,
          inner_self_eq_norm_sq_to_K, norm_smul, hv0]
    · simp [kahlerTwoForm_apply, hv1, inner_smul_right, hv0]

/-- **Non-orthonormal degree-two Wirtinger equality**: for linearly independent `v` and `w` in a
finite-dimensional Hermitian vector space, `ω(v, w) = ‖v ∧ w‖` exactly when
`w = a • v + b • (i • v)` with `0 < b`. -/
theorem kahlerTwoForm_apply_eq_norm_ιMulti_iff [FiniteDimensional ℝ E] {v w : E}
    (h : LinearIndependent ℝ ![v, w]) :
    kahlerTwoForm E ![v, w] = ‖ιMulti ℝ 2 ![v, w]‖ ↔
      ∃ a b : ℝ, 0 < b ∧ w = a • v + b • (Complex.I • v) := by
  rw [kahlerTwoForm_apply_eq_inner]
  simpa only [AlmostComplexStructure.ofComplexModule_apply] using
    AlmostComplexStructure.inner_apply_eq_norm_ιMulti_iff
      (J := AlmostComplexStructure.ofComplexModule E)
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule h

end DegreeTwoEquality

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- The Riesz dual of `(AlmostComplexStructure.ofComplexModule E).kahlerForm` is
`kahlerTwoForm E`. -/
@[simp]
theorem alternatingFormEquiv_ofComplexModule_kahlerForm :
    alternatingFormEquiv E 2 (AlmostComplexStructure.ofComplexModule E).kahlerForm =
      kahlerTwoForm E := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, alternatingFormEquiv_apply,
    AlmostComplexStructure.inner_kahlerForm_ιMulti
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule,
    AlmostComplexStructure.ofComplexModule_apply, kahlerTwoForm_apply_eq_inner]

/-- In any complex orthonormal basis `b` of `E`, the Kähler bivector is
`∑ j, b j ∧ (i • b j)`. -/
theorem ofComplexModule_kahlerForm_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) :
    (AlmostComplexStructure.ofComplexModule E).kahlerForm =
      ∑ j : ι, ιMulti ℝ 2 ![b j, Complex.I • b j] := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let u : Fin (Fintype.card ι) → E := b ∘ e
  have hu : Orthonormal ℂ u := b.orthonormal.comp e e.injective
  have hon : Orthonormal ℝ (complexToRealFamily u) := orthonormal_complexToRealFamily hu
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  have hcard : Fintype.card (Fin (2 * Fintype.card ι)) = finrank ℝ E := by
    rw [Fintype.card_fin, finrank_real_eq_two_mul_finrank_complex,
      Module.finrank_eq_card_basis b.toBasis]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ E :=
    (basisOfLinearIndependentOfCardEqFinrank' (complexToRealFamily u) hon.linearIndependent
      hcard).toOrthonormalBasis
      (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hon)
  have hb₀ (i : Fin (2 * Fintype.card ι)) : b₀ i = complexToRealFamily u i := by
    simp [b₀]
  have hadapt (k : Fin (Fintype.card ι)) :
      b₀ ⟨2 * (k : ℕ) + 1, by omega⟩ =
        AlmostComplexStructure.ofComplexModule E (b₀ ⟨2 * (k : ℕ), by omega⟩) := by
    simp only [hb₀]
    exact complexToRealFamily_odd_eq_ofComplexModule u k
  rw [AlmostComplexStructure.kahlerForm_eq_sum_of_adapted b₀ hadapt]
  simp_rw [hb₀, complexToRealFamily_even, complexToRealFamily_odd, u, Function.comp_apply]
  exact Fintype.sum_equiv e _ (fun j ↦ ιMulti ℝ 2 ![b j, Complex.I • b j]) (fun _ ↦ rfl)

end FiniteDimensional

end TauCeti
