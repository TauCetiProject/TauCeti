/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.TwoForm
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Geometry.Symplectic.Wirtinger
import TauCeti.Analysis.InnerProductSpace.Complex

/-!
# Degree-two Wirtinger inequality and Kähler two-form calibration

This file develops the degree-two Wirtinger inequality and equality criteria for orthogonal almost
complex structures and complex inner product spaces:

* For an orthogonal almost complex structure `J` on a finite-dimensional real inner product space
  `V`, `alternatingFormEquiv V 2 J.kahlerForm` has comass `1` when `V` is nontrivial
  (`TauCeti.AlmostComplexStructure.norm_alternatingFormEquiv_kahlerForm`), calibrates precisely the
  pairs `(v, J v)` with `‖v‖ = 1`
  (`TauCeti.AlmostComplexStructure.isCalibratedFrame_alternatingFormEquiv_kahlerForm_iff`), and for
  `v ≠ 0` attains the area `‖v ∧ w‖` precisely when `w = a v + b J v` with `b ≥ 0`
  (`TauCeti.AlmostComplexStructure.alternatingFormEquiv_kahlerForm_apply_eq_norm_ιMulti_iff`).
* On any normed complex inner product space with a compatible real inner product (without
  finite-dimensionality), `TauCeti.kahlerTwoForm E` calibrates precisely the ordered pairs
  `(v₀, i • v₀)` with `‖v₀‖ = 1` (`TauCeti.isCalibratedFrame_kahlerTwoForm_iff`).
* On finite-dimensional Hermitian vector spaces, `TauCeti.kahlerTwoForm E` attains `‖v ∧ w‖` for
  `v ≠ 0` precisely when `w = c • v` with `0 ≤ Im c`
  (`TauCeti.kahlerTwoForm_apply_eq_norm_ιMulti_iff_of_ne_zero`).

## Main results

* `TauCeti.AlmostComplexStructure.norm_ιMulti_two_eq_wedgeNorm_symplecticForm`: `‖v ∧ w‖` is the
  wedge norm of the canonical symplectic form `J.symplecticForm hJ`.
* `TauCeti.AlmostComplexStructure.isCalibratedFrame_alternatingFormEquiv_kahlerForm_iff`:
  calibrated-pair classification for `alternatingFormEquiv V 2 J.kahlerForm`.
* `TauCeti.AlmostComplexStructure.norm_alternatingFormEquiv_kahlerForm`: degree-two comass one
  for `alternatingFormEquiv V 2 J.kahlerForm` when `V` is nontrivial.
* `TauCeti.AlmostComplexStructure.alternatingFormEquiv_kahlerForm_apply_eq_norm_ιMulti_iff`:
  non-orthonormal area equality criterion for `alternatingFormEquiv V 2 J.kahlerForm`.
* `TauCeti.isCalibratedFrame_kahlerTwoForm_iff`: calibrated-pair classification on any normed
  complex inner product space with a compatible real inner product.
* `TauCeti.kahlerTwoForm_apply_eq_norm_ιMulti_iff_of_ne_zero`: non-orthonormal area equality
  criterion on finite-dimensional Hermitian vector spaces.

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

/-- The area `‖v ∧ w‖` of the parallelogram on `(v, w)` is the wedge norm
`√(‖v‖² ‖w‖² - ⟪v, w⟫²)` of the canonical symplectic form `ω(x, y) = ⟪J x, y⟫`. -/
theorem norm_ιMulti_two_eq_wedgeNorm_symplecticForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (v w : V) :
    ‖ιMulti ℝ 2 ![v, w]‖ = (J.symplecticForm hJ).wedgeNorm J v w := by
  rw [SymplecticForm.wedgeNorm_def, norm_eq_sqrt_real_inner, inner_ιMulti_two]
  simp only [SymplecticForm.associatedBilinForm_apply, symplecticForm_apply, hJ,
    real_inner_comm v w, sq]

section DegreeTwo

variable {J : AlmostComplexStructure V} (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
include hJ

/-- The pair `(v, J v)` is calibrated by the Kähler form whenever `v` is a unit vector. -/
private theorem isCalibratedFrame_alternatingFormEquiv_kahlerForm_of_norm_eq_one {v : V}
    (hv : ‖v‖ = 1) :
    (alternatingFormEquiv V 2 J.kahlerForm).IsCalibratedFrame ![v, J v] := by
  refine ⟨?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hv, norm_apply hJ, inner_apply_self hJ, inner_self_apply hJ]
  · simp [alternatingFormEquiv_kahlerForm_apply hJ, hJ, hv]

/-- **Wirtinger's inequality, frame form**: an ordered pair of vectors is calibrated by the Kähler
form of an orthogonal complex structure exactly when it is `(v, J v)` for a unit vector `v`. -/
theorem isCalibratedFrame_alternatingFormEquiv_kahlerForm_iff {v : Fin 2 → V} :
    (alternatingFormEquiv V 2 J.kahlerForm).IsCalibratedFrame v ↔
      ‖v 0‖ = 1 ∧ v 1 = J (v 0) := by
  refine ⟨fun h ↦ ⟨h.orthonormal.1 0, ?_⟩, fun ⟨h₀, h₁⟩ ↦ ?_⟩
  · have h₁ := h.apply_eq_one
    rw [alternatingFormEquiv_kahlerForm_apply hJ,
      inner_eq_one_iff_of_norm_eq_one (by rw [norm_apply hJ, h.orthonormal.1 0])
        (h.orthonormal.1 1)] at h₁
    exact h₁.symm
  · have hv : v = ![v 0, J (v 0)] := by ext i; fin_cases i <;> simp [h₁]
    rw [hv]
    exact isCalibratedFrame_alternatingFormEquiv_kahlerForm_of_norm_eq_one hJ h₀

/-- **Wirtinger's inequality**: the Kähler form of an orthogonal complex structure on a nonzero
space has comass one. The bound `‖ω‖ ≤ 1` is `norm_alternatingFormEquiv_kahlerForm_le`; it is
attained on every pair `(v, J v)` with `‖v‖ = 1`. -/
theorem norm_alternatingFormEquiv_kahlerForm [Nontrivial V] :
    ‖alternatingFormEquiv V 2 J.kahlerForm‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_norm_eq V zero_le_one
  exact (norm_alternatingFormEquiv_kahlerForm_le hJ).antisymm
    (isCalibratedFrame_alternatingFormEquiv_kahlerForm_of_norm_eq_one hJ hv).one_le_norm

/-- **The equality case of Wirtinger's inequality**: for `v ≠ 0`, the Kähler form attains the area
`‖v ∧ w‖` of the parallelogram on `(v, w)` exactly when `w = a v + b J v` with `b ≥ 0`. For
linearly independent `v, w` this says that their plane is `J`-invariant and that `(v, w)` is
oriented like `(v, J v)`. -/
theorem alternatingFormEquiv_kahlerForm_apply_eq_norm_ιMulti_iff {v w : V} (hv : v ≠ 0) :
    alternatingFormEquiv V 2 J.kahlerForm ![v, w] = ‖ιMulti ℝ 2 ![v, w]‖ ↔
      ∃ a b : ℝ, 0 ≤ b ∧ w = a • v + b • J v := by
  rw [alternatingFormEquiv_kahlerForm_apply hJ, norm_ιMulti_two_eq_wedgeNorm_symplecticForm hJ,
    Matrix.cons_val_zero, Matrix.cons_val_one, ← symplecticForm_apply hJ]
  exact (symplecticForm_compatible hJ).apply_eq_wedgeNorm_iff hv w

end DegreeTwo

end AlmostComplexStructure

section DegreeTwoEquality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- **Equality case of degree-two Wirtinger** on any normed complex inner product space with a
compatible real inner product (no finite-dimensionality required): an ordered pair `(v₀, v₁)` is
calibrated by `kahlerTwoForm E` precisely when `‖v₀‖ = 1` and `v₁ = i • v₀`. -/
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

end DegreeTwoEquality

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- **Non-orthonormal degree-two Wirtinger equality**: for `v ≠ 0` in a finite-dimensional
Hermitian vector space, `kahlerTwoForm E` attains the area `‖v ∧ w‖` exactly when `w` is a complex
multiple `c • v` with `0 ≤ Im c`. -/
theorem kahlerTwoForm_apply_eq_norm_ιMulti_iff_of_ne_zero {v w : E} (hv : v ≠ 0) :
    kahlerTwoForm E ![v, w] = ‖ιMulti ℝ 2 ![v, w]‖ ↔ ∃ c : ℂ, 0 ≤ c.im ∧ w = c • v := by
  rw [← alternatingFormEquiv_ofComplexModule_kahlerForm,
    AlmostComplexStructure.alternatingFormEquiv_kahlerForm_apply_eq_norm_ιMulti_iff
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule hv]
  simp only [AlmostComplexStructure.ofComplexModule_apply]
  exact ⟨fun ⟨a, b, hb, hw⟩ ↦ ⟨⟨a, b⟩, hb, hw.trans (Complex.re_smul_add_im_smul ⟨a, b⟩ v)⟩,
    fun ⟨c, hc, hw⟩ ↦ ⟨c.re, c.im, hc, hw.trans (Complex.re_smul_add_im_smul c v).symm⟩⟩

end FiniteDimensional

end TauCeti
