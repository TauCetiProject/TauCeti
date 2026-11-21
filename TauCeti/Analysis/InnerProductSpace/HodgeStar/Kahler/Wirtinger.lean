/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Mass
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Geometry.Symplectic.Wirtinger

/-!
# The Wirtinger inequality in degree two

Let `J` be an orthogonal almost complex structure on a finite-dimensional real inner product
space `V`, and let `ω(u, w) = ⟪J u, w⟫` be its Kähler form, the alternating form of the Kähler
two-vector `TauCeti.AlmostComplexStructure.kahlerForm J`. The **Wirtinger inequality** says that
`ω(v, w) ≤ ‖v ∧ w‖` for all `v, w`; for `v ≠ 0`, equality holds exactly when `w` lies in the
complex line `span {v, J v}` and `(v, w)` is oriented like `(v, J v)`. In the language of
calibrations: `ω` has comass one, and its calibrated frames are the pairs `(v, J v)` with
`‖v‖ = 1`. Both statements come from the Lagrange-type identity

`‖v‖² (‖v ∧ w‖² - ω(v, w)²) = ‖‖v‖² w - ⟪v, w⟫ v - ω(v, w) J v‖²`,

the defect `‖v ∧ w‖² - ω(v, w)²` is `‖v‖²` times the squared distance from `w` to the complex
line `span {v, J v}`. No integrability or closedness enters.

On `ℂⁿ = EuclideanSpace ℂ (Fin n)`, with its real Euclidean structure `Re ⟪·, ·⟫_ℂ` and the
complex structure of multiplication by `i`, the Kähler form is the standard Kähler form
`ω(v, w) = Im ⟪v, w⟫_ℂ = ∑ⱼ dxⱼ ∧ dyⱼ` (`TauCeti.standardKahlerForm`), with `ω(1, i) = 1` on `ℂ`.
Its calibrated planes are the complex lines of `ℂⁿ` with their complex orientation.

## Main definitions

* `TauCeti.standardKahlerForm n`: the standard Kähler form on `ℂⁿ`, a real continuous alternating
  two-form.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`, for an orthogonal `J`:

* `norm_alternatingFormEquiv_kahlerForm`: the Kähler form has comass one on a nonzero space.
* `isCalibratedFrame_alternatingFormEquiv_kahlerForm_iff`: its calibrated frames are the pairs
  `(v, J v)` with `‖v‖ = 1`.
* `norm_ιMulti_two_eq_wedgeNorm_symplecticForm`: `‖v ∧ w‖` is the wedge norm of the canonical
  symplectic form `J.symplecticForm hJ`.
* `alternatingFormEquiv_kahlerForm_apply_eq_norm_ιMulti_iff`: for `v ≠ 0`, the equality
  `ω(v, w) = ‖v ∧ w‖` holds exactly when `w = a v + b J v` with `b ≥ 0`.

For the standard Kähler form on `ℂⁿ`:

* `TauCeti.standardKahlerForm_apply`: `ω(v, w) = Im ⟪v, w⟫_ℂ`.
* `TauCeti.norm_standardKahlerForm`: `ω` has comass one for `n ≠ 0`; for `n = 0` it vanishes
  (`TauCeti.standardKahlerForm_zero`).
* `TauCeti.isCalibratedFrame_standardKahlerForm_iff`: the calibrated frames are `(v, i v)` with
  `‖v‖ = 1`.
* `TauCeti.standardKahlerForm_apply_eq_norm_ιMulti_iff`: for `v ≠ 0`, `ω(v, w) = ‖v ∧ w‖`
  exactly when `w = c v` for a complex number `c` with `0 ≤ Im c`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), Theorem II.6.11
  (the case `p = 1`).
-/

public section

noncomputable section

open exteriorPower
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : AlmostComplexStructure V} (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
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

/-- The area `‖v ∧ w‖` of the parallelogram on `(v, w)` is the wedge norm
`√(‖v‖² ‖w‖² - ⟪v, w⟫²)` of the canonical symplectic form `ω(x, y) = ⟪J x, y⟫`. -/
theorem norm_ιMulti_two_eq_wedgeNorm_symplecticForm (v w : V) :
    ‖ιMulti ℝ 2 ![v, w]‖ = (J.symplecticForm hJ).wedgeNorm J v w := by
  rw [SymplecticForm.wedgeNorm_def, norm_eq_sqrt_real_inner, inner_ιMulti_two]
  simp only [SymplecticForm.associatedBilinForm_apply, symplecticForm_apply, hJ,
    real_inner_comm v w, sq]

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

end TauCeti.AlmostComplexStructure

namespace TauCeti

/-- The **standard Kähler form** `ω(v, w) = Im ⟪v, w⟫_ℂ = ∑ⱼ dxⱼ ∧ dyⱼ` on `ℂⁿ`, a real continuous
alternating two-form on the underlying real Euclidean space. It is the Kähler form of the
complex structure `v ↦ i v`, so `ω(1, i) = 1` on `ℂ`. -/
def standardKahlerForm (n : ℕ) : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
  alternatingFormEquiv _ 2
    (AlmostComplexStructure.ofComplexModule (EuclideanSpace ℂ (Fin n))).kahlerForm

/-- The standard Kähler form is the alternating form of the Kähler two-vector of `v ↦ i v`. -/
theorem standardKahlerForm_def (n : ℕ) :
    standardKahlerForm n = alternatingFormEquiv _ 2
      (AlmostComplexStructure.ofComplexModule (EuclideanSpace ℂ (Fin n))).kahlerForm :=
  (rfl)

/-- The standard Kähler form evaluates on `(v, w)` as `Im ⟪v, w⟫_ℂ`. -/
@[simp]
theorem standardKahlerForm_apply (n : ℕ) (v : Fin 2 → EuclideanSpace ℂ (Fin n)) :
    standardKahlerForm n v = (⟪v 0, v 1⟫_ℂ).im := by
  rw [standardKahlerForm_def, AlmostComplexStructure.alternatingFormEquiv_kahlerForm_apply
    AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule]
  simp only [AlmostComplexStructure.ofComplexModule_apply, PiLp.inner_apply, PiLp.smul_apply,
    Complex.inner, Complex.im_sum]
  refine Finset.sum_congr rfl fun _ _ ↦ ?_
  simp [sub_eq_neg_add]

/-- The standard Kähler form on `ℂ⁰` is zero; this is why `norm_standardKahlerForm` needs
`n ≠ 0`. -/
@[simp]
theorem standardKahlerForm_zero : standardKahlerForm 0 = 0 := by
  ext v
  simp [PiLp.inner_apply]

/-- **Wirtinger's inequality on `ℂⁿ`**: for `n ≠ 0` the standard Kähler form has comass one. -/
theorem norm_standardKahlerForm (n : ℕ) [NeZero n] : ‖standardKahlerForm n‖ = 1 :=
  AlmostComplexStructure.norm_alternatingFormEquiv_kahlerForm
    AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule

/-- The frames calibrated by the standard Kähler form on `ℂⁿ` are the pairs `(v, i v)` with
`‖v‖ = 1`. -/
theorem isCalibratedFrame_standardKahlerForm_iff {n : ℕ}
    {v : Fin 2 → EuclideanSpace ℂ (Fin n)} :
    (standardKahlerForm n).IsCalibratedFrame v ↔ ‖v 0‖ = 1 ∧ v 1 = Complex.I • v 0 := by
  rw [standardKahlerForm_def,
    AlmostComplexStructure.isCalibratedFrame_alternatingFormEquiv_kahlerForm_iff
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule,
    AlmostComplexStructure.ofComplexModule_apply]

/-- **The equality case of Wirtinger's inequality on `ℂⁿ`**: for `v ≠ 0`, the standard Kähler
form attains the area `‖v ∧ w‖` exactly when `w` is a complex multiple `c v` with `0 ≤ Im c`,
that is, when `(v, w)` lies in the complex line of `v` with its complex orientation. -/
theorem standardKahlerForm_apply_eq_norm_ιMulti_iff {n : ℕ} {v w : EuclideanSpace ℂ (Fin n)}
    (hv : v ≠ 0) :
    standardKahlerForm n ![v, w] = ‖ιMulti ℝ 2 ![v, w]‖ ↔ ∃ c : ℂ, 0 ≤ c.im ∧ w = c • v := by
  rw [standardKahlerForm_def,
    AlmostComplexStructure.alternatingFormEquiv_kahlerForm_apply_eq_norm_ιMulti_iff
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule hv]
  simp only [AlmostComplexStructure.ofComplexModule_apply]
  exact ⟨fun ⟨a, b, hb, hw⟩ ↦ ⟨⟨a, b⟩, hb, hw.trans (Complex.re_smul_add_im_smul ⟨a, b⟩ v)⟩,
    fun ⟨c, hc, hw⟩ ↦ ⟨c.re, c.im, hc, hw.trans (Complex.re_smul_add_im_smul c v).symm⟩⟩

end TauCeti
