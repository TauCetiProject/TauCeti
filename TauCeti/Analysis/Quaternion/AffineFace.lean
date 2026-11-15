/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.Basic
public import TauCeti.Analysis.Quaternion.Forms
public import TauCeti.MeasureTheory.Integral.Bochner.Star
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Affine
import TauCeti.MeasureTheory.Integral.Bochner.Affine

/-!
# Affine face integrals of the quaternionic surface element

`rawAffineBoundary L p B` integrates the ordered coefficient `B x (Dq v)` over the
eight parametrized faces of `u ↦ p + L u`, with the orientation induced by the parameter
cube. The linear map `L` need not be invertible. Each tangent triple already contains
all three face scale factors; there is no additional Jacobian multiplier. Orientation
signs are encoded in `affineFaceNormal` and the front-minus-back sum, rather than by
changing the face parameters.

The coefficient `B x` is real-linear in the quaternionic surface element. In particular,
`ContinuousLinearMap.mulLeftRight ℝ ℍ (g x) (f x)` gives the ordered integrand
`g x * Dq v * f x`, encompassing both Cauchy integrands and both kernel-weighted ones.
The codomain may be any real normed space.

This file develops the geometric and reparametrization calculus of `rawAffineBoundary`:
* `TauCeti.Quaternion.norm_Dq_sq` and `ContinuousLinearMap.norm_affineFaceNormal_sq`: the squared
  norm of `affineFaceNormal L j` is the `3 × 3` Gram determinant of the three face tangent vectors,
  matching the 3-dimensional surface-area Jacobian of the `j`-face;
* degenerate-face and degenerate-direction vanishing (`integral_affineFace_eq_zero`,
  `rawAffineBoundary_eq_zero_of_apply_single_eq_zero`), plus face and boundary norm bounds;
* coordinate reflection `negCoord ℝ k` (`rawAffineBoundary_comp_negCoord`), quaternionic
  conjugation `tupleConj` (`rawAffineBoundary_tupleConj_comp`), and their orientation-preserving
  composition (`rawAffineBoundary_tupleConj_comp_negCoord`,
  `star_rawAffineBoundary_tupleConj_comp_negCoord_mulLeftRight`) exchanging left and right ordered
  integrands;
* rectangular subdivision additivity (`rawAffineBoundary_split`,
  `rawAffineBoundary_split_of_continuousOn`) along `u k = t`;
* compatibility with `ContinuousLinearEquiv.affineFluxBoundary` for invertible `L`, with
  `TauCeti.boxBoundarySum a b` on axis-aligned boxes `a ≤ b` (`rawAffineBoundary_piMap_smul_id`),
  and with `BoxIntegral.integral` (`rawAffineBoundary_eq_boxIntegral`).

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, equation (18), for the ordered surface
  element and outward-first convention.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225,
  for the surface element `Dq` and its reflection symmetry.
-/

public section

open MeasureTheory Set TauCeti.Quaternion
open scoped Quaternion RealInnerProductSpace ENNReal

namespace TauCeti.Quaternion

/-- The squared Euclidean norm of `Dq v` equals the `3 × 3` Gram determinant of the three tangent
vectors `dq (v 0), dq (v 1), dq (v 2)` in `ℍ`, i.e. the squared 3-dimensional volume of the
parallelepiped they span. -/
theorem norm_Dq_sq (v : Fin 3 → Fin 4 → ℝ) :
    ‖Dq v‖ ^ 2 = (Matrix.of fun r s : Fin 3 ↦ ⟪dq (v r), dq (v s)⟫).det := by
  rw [sq, ← _root_.Quaternion.normSq_eq_norm_mul_self, _root_.Quaternion.normSq_def']
  simp only [re_Dq, imI_Dq, imJ_Dq, imK_Dq, minorForm_apply, Matrix.det_fin_three,
    Matrix.of_apply, _root_.Quaternion.inner_def, Fin.succAbove]
  norm_num
  ring

/-- Quaternionic conjugation in real coordinates `(t, x, y, z) ↦ (t, -x, -y, -z)`, as a continuous
linear equivalence of `Fin 4 → ℝ`. -/
def tupleConj : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight
    (Function.update (fun _ : Fin 4 ↦ ContinuousLinearEquiv.neg ℝ) 0
      (ContinuousLinearEquiv.refl ℝ ℝ))

theorem tupleConj_def :
    tupleConj = ContinuousLinearEquiv.piCongrRight
      (Function.update (fun _ : Fin 4 ↦ ContinuousLinearEquiv.neg ℝ) 0
        (ContinuousLinearEquiv.refl ℝ ℝ)) :=
  (rfl)

@[simp]
theorem tupleConj_zero (x : Fin 4 → ℝ) : tupleConj x 0 = x 0 := by
  simp [tupleConj_def]

@[simp]
theorem tupleConj_of_ne_zero {i : Fin 4} (hi : i ≠ 0) (x : Fin 4 → ℝ) :
    tupleConj x i = -x i := by
  simp [tupleConj_def, hi]

/-- `dq` intertwines `tupleConj` with quaternion conjugation `star`. -/
@[simp]
theorem dq_tupleConj (x : Fin 4 → ℝ) : dq (tupleConj x) = star (dq x) := by
  ext <;> simp [tupleConj_def]

@[simp]
theorem symm_tupleConj : tupleConj.symm = tupleConj := by
  ext x i
  by_cases hi : i = 0
  · subst hi
    simp [tupleConj_def]
  · simp [tupleConj_def, hi]

@[simp]
theorem tupleConj_tupleConj (x : Fin 4 → ℝ) : tupleConj (tupleConj x) = x := by
  ext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi]

/-- Quaternionic conjugation negates the three imaginary axes and fixes the real axis, so it has
determinant `-1`. -/
@[simp]
theorem det_tupleConj : LinearMap.det (tupleConj : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) = -1 := by
  simp [tupleConj_def, ContinuousLinearEquiv.det_piCongrRight, Fin.prod_univ_four]

end TauCeti.Quaternion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousLinearMap

/-- The oriented quaternionic surface coefficient on the front parameter face `u j = 1`
of `u ↦ p + L u`. The back face has its negative. This includes the face scale exactly once. -/
noncomputable def affineFaceNormal (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) : ℍ :=
  (-1 : ℝ) ^ (j : ℕ) • Dq (fun r ↦ L (Pi.single (j.succAbove r) 1))

theorem affineFaceNormal_eq (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) :
    affineFaceNormal L j =
      (-1 : ℝ) ^ (j : ℕ) • Dq (fun r ↦ L (Pi.single (j.succAbove r) 1)) :=
  (rfl)

/-- On the identity cube the front-face coefficients are `1, i, j, k`, all with positive sign. -/
@[simp]
theorem affineFaceNormal_id (j : Fin 4) :
    affineFaceNormal (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) j = dq (Pi.single j 1) := by
  rw [affineFaceNormal_eq]
  simp only [ContinuousLinearMap.id_apply, Dq_succAbove, smul_smul]
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num [dq_single]

/-- The orientation sign `(-1) ^ j` has unit modulus, so `‖affineFaceNormal L j‖` is the norm of
`Dq` on the three tangent vectors of the `j`-face. -/
@[simp]
theorem norm_affineFaceNormal (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) :
    ‖affineFaceNormal L j‖ = ‖Dq (fun r ↦ L (Pi.single (j.succAbove r) 1))‖ := by
  simp [affineFaceNormal_eq, norm_smul]

/-- The squared norm of `affineFaceNormal L j` is the `3 × 3` Gram determinant of the three
tangent vectors of the `j`-face, i.e. the squared 3-dimensional surface-area Jacobian of that
face. -/
theorem norm_affineFaceNormal_sq (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) :
    ‖affineFaceNormal L j‖ ^ 2 =
      (Matrix.of fun r s : Fin 3 ↦
        ⟪dq (L (Pi.single (j.succAbove r) 1)), dq (L (Pi.single (j.succAbove s) 1))⟫).det := by
  rw [norm_affineFaceNormal, norm_Dq_sq]

/-- Precomposing `L` with a diagonal scaling `diag d` multiplies the `j`-th face normal by the
product `∏ r, d (j.succAbove r)` of the three tangential scale factors, including when some scale
factor is zero or negative. -/
theorem affineFaceNormal_comp_piMap_smul_id (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (d : Fin 4 → ℝ) (j : Fin 4) :
    affineFaceNormal
        (L.comp (ContinuousLinearMap.piMap fun i ↦ d i • ContinuousLinearMap.id ℝ ℝ)) j =
      (∏ r : Fin 3, d (j.succAbove r)) • affineFaceNormal L j := by
  have hvec (r : Fin 3) :
      L ((ContinuousLinearMap.piMap fun i ↦ d i • ContinuousLinearMap.id ℝ ℝ)
        (Pi.single (j.succAbove r) 1)) =
        d (j.succAbove r) • L (Pi.single (j.succAbove r) 1) := by
    have hsingle : (ContinuousLinearMap.piMap fun i ↦ d i • ContinuousLinearMap.id ℝ ℝ)
        (Pi.single (j.succAbove r) 1) = d (j.succAbove r) • Pi.single (j.succAbove r) 1 := by
      ext i
      by_cases hi : i = j.succAbove r
      · subst hi
        simp
      · simp [hi]
    rw [hsingle, map_smul]
  simp only [affineFaceNormal_eq, comp_apply, hvec]
  rw [Dq.map_smul_univ, smul_comm]

/-- For a diagonal linear map `diag d`, the `j`-th face normal is `(∏ r, d (j.succAbove r))` times
the `j`-th quaternion unit `1, i, j, k`. -/
theorem affineFaceNormal_piMap_smul_id (d : Fin 4 → ℝ) (j : Fin 4) :
    affineFaceNormal (ContinuousLinearMap.piMap fun i ↦ d i • ContinuousLinearMap.id ℝ ℝ) j =
      (∏ r : Fin 3, d (j.succAbove r)) • dq (Pi.single j 1) := by
  simpa using affineFaceNormal_comp_piMap_smul_id (ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) d j

/-- Postcomposing `L` with coordinate conjugation `tupleConj` sends `affineFaceNormal L j` to
`-star (affineFaceNormal L j)`. -/
theorem affineFaceNormal_tupleConj_comp (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) :
    affineFaceNormal (tupleConj.toContinuousLinearMap.comp L) j = -star (affineFaceNormal L j) := by
  rw [affineFaceNormal_eq, affineFaceNormal_eq]
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Dq_star (fun r ↦ dq_tupleConj (L (Pi.single (j.succAbove r) 1))), smul_neg, star_smul,
    star_trivial ((-1 : ℝ) ^ (j : ℕ))]

/-- A degenerate tangent triple contributes zero, without any nonsingularity hypothesis. -/
theorem affineFaceNormal_eq_zero (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4)
    (h : ¬LinearIndependent ℝ (fun r : Fin 3 ↦ L (Pi.single (j.succAbove r) 1))) :
    affineFaceNormal L j = 0 := by
  have hz := Dq.toAlternatingMap.map_linearDependent _ h
  rw [ContinuousAlternatingMap.coe_toAlternatingMap] at hz
  rw [affineFaceNormal_eq, hz, smul_zero]

/-- Any parametrized face integral vanishes when the three face tangent vectors of `L` are linearly
dependent, without continuity or integrability assumptions on `B`. -/
theorem integral_affineFace_eq_zero (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (j : Fin 4) (c : ℝ)
    (h : ¬LinearIndependent ℝ (fun r : Fin 3 ↦ L (Pi.single (j.succAbove r) 1))) :
    ∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth c u)) (affineFaceNormal L j) = 0 := by
  simp [affineFaceNormal_eq_zero L j h]

/-- Norm bound on a single parametrized face integral: since the unit 3-cube has Lebesgue measure
`1`, an operator-norm bound `M` on `B` along the face gives `M * ‖affineFaceNormal L j‖`. -/
theorem norm_integral_affineFace_le (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E} {j : Fin 4} {c M : ℝ}
    (hB : ∀ u ∈ Icc (0 : Fin 3 → ℝ) 1, ‖B (p + L (j.insertNth c u))‖ ≤ M) :
    ‖∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth c u)) (affineFaceNormal L j)‖ ≤
      M * ‖affineFaceNormal L j‖ := by
  have hvol : volume.real (Icc (0 : Fin 3 → ℝ) 1) = 1 := by
    simp [measureReal_def, Real.volume_Icc_pi_toReal (zero_le_one : (0 : Fin 3 → ℝ) ≤ 1)]
  have hfin : volume (Icc (0 : Fin 3 → ℝ) 1) < ∞ := isCompact_Icc.measure_lt_top
  have hbound : ∀ u ∈ Icc (0 : Fin 3 → ℝ) 1,
      ‖B (p + L (j.insertNth c u)) (affineFaceNormal L j)‖ ≤ M * ‖affineFaceNormal L j‖ :=
    fun u hu ↦ (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB u hu) (norm_nonneg _))
  simpa [hvol] using norm_setIntegral_le_of_norm_le_const hfin hbound

/-- The raw, parameter-oriented boundary integral of `B x (Dq v)` on the affine image
of the unit four-cube. It is defined even for singular `L` and discontinuous `B`;
continuity on the closed image ensures the individual face integrals exist. -/
noncomputable def rawAffineBoundary (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) : E :=
  ∑ j : Fin 4,
    ((∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth 1 u)) (affineFaceNormal L j)) -
      ∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth 0 u)) (affineFaceNormal L j))

theorem rawAffineBoundary_eq (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary L p B = ∑ j : Fin 4,
      ((∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth 1 u)) (affineFaceNormal L j)) -
        ∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth 0 u)) (affineFaceNormal L j)) :=
  (rfl)

@[simp]
theorem rawAffineBoundary_zero (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) :
    rawAffineBoundary L p (fun _ ↦ (0 : ℍ →L[ℝ] E)) = 0 := by
  simp [rawAffineBoundary_eq]

/-- Constant coefficients have zero boundary integral: opposite faces cancel, including
for singular affine maps. -/
@[simp]
theorem rawAffineBoundary_const (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (B : ℍ →L[ℝ] E) : rawAffineBoundary L p (fun _ ↦ B) = 0 := by
  simp [rawAffineBoundary_eq]

/-- If `L` annihilates one coordinate vector `eₖ`, then `rawAffineBoundary L p B = 0` for every
`p` and `B`: the opposite `k`-faces coincide, and every other face has zero `affineFaceNormal`. -/
theorem rawAffineBoundary_eq_zero_of_apply_single_eq_zero {L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)}
    {k : Fin 4} (hk : L (Pi.single k 1) = 0) (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary L p B = 0 := by
  rw [rawAffineBoundary_eq]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases hjk : j = k
  · subst hjk
    have hshift (u : Fin 3 → ℝ) : L (j.insertNth 1 u) = L (j.insertNth 0 u) := by
      have hu : j.insertNth (α := fun _ ↦ ℝ) 1 u =
          Pi.single j 1 + j.insertNth (α := fun _ ↦ ℝ) 0 u := by
        ext i
        exact j.succAboveCases (by simp) (fun r ↦ by simp) i
      rw [hu, map_add, hk, zero_add]
    simp [hshift]
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
    have hzero : affineFaceNormal L j = 0 :=
      affineFaceNormal_eq_zero L j fun hli ↦ hli.ne_zero r (by simp [hr, hk])
    simp [hzero]

/-- Continuity of the coefficient on the affine cube ensures integrability on each face. -/
theorem integrableOn_affineFace (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB : ContinuousOn B ((fun u ↦ p + L u) '' Icc 0 1))
    (j : Fin 4) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun u ↦ B (p + L (j.insertNth c u)) (affineFaceNormal L j))
      (Icc (0 : Fin 3 → ℝ) 1) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply ContinuousOn.clm_apply _ continuousOn_const
  apply hB.comp (by fun_prop)
  intro u hu
  exact mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc, hu⟩)

/-- The boundary functional is additive when both coefficients have integrable face integrands. -/
theorem rawAffineBoundary_add (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    {B C : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB₁ : ∀ j : Fin 4, IntegrableOn
      (fun u ↦ B (p + L (j.insertNth 1 u)) (affineFaceNormal L j)) (Icc (0 : Fin 3 → ℝ) 1))
    (hB₀ : ∀ j : Fin 4, IntegrableOn
      (fun u ↦ B (p + L (j.insertNth 0 u)) (affineFaceNormal L j)) (Icc (0 : Fin 3 → ℝ) 1))
    (hC₁ : ∀ j : Fin 4, IntegrableOn
      (fun u ↦ C (p + L (j.insertNth 1 u)) (affineFaceNormal L j)) (Icc (0 : Fin 3 → ℝ) 1))
    (hC₀ : ∀ j : Fin 4, IntegrableOn
      (fun u ↦ C (p + L (j.insertNth 0 u)) (affineFaceNormal L j)) (Icc (0 : Fin 3 → ℝ) 1)) :
    rawAffineBoundary L p (fun x ↦ B x + C x) =
      rawAffineBoundary L p B + rawAffineBoundary L p C := by
  simp only [rawAffineBoundary_eq, add_apply]
  simp_rw [integral_add (hB₁ _) (hC₁ _), integral_add (hB₀ _) (hC₀ _),
    add_sub_add_comm, Finset.sum_add_distrib]

/-- Coefficients continuous on the closed affine cube satisfy boundary additivity. -/
theorem rawAffineBoundary_add_of_continuousOn
    (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    {B C : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB : ContinuousOn B ((fun u ↦ p + L u) '' Icc 0 1))
    (hC : ContinuousOn C ((fun u ↦ p + L u) '' Icc 0 1)) :
    rawAffineBoundary L p (fun x ↦ B x + C x) =
      rawAffineBoundary L p B + rawAffineBoundary L p C :=
  rawAffineBoundary_add L p
    (fun j ↦ integrableOn_affineFace L p hB j (by simp : (1 : ℝ) ∈ Icc 0 1))
    (fun j ↦ integrableOn_affineFace L p hB j (by simp : (0 : ℝ) ∈ Icc 0 1))
    (fun j ↦ integrableOn_affineFace L p hC j (by simp : (1 : ℝ) ∈ Icc 0 1))
    (fun j ↦ integrableOn_affineFace L p hC j (by simp : (0 : ℝ) ∈ Icc 0 1))

/-- Real scalars commute with the raw boundary integral, without regularity hypotheses. -/
theorem rawAffineBoundary_smul (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (r : ℝ) :
    rawAffineBoundary L p (fun x ↦ r • B x) = r • rawAffineBoundary L p B := by
  simp [rawAffineBoundary_eq, integral_smul, smul_sub, Finset.smul_sum]

/-- Negating the coefficient negates `rawAffineBoundary`, without regularity hypotheses. -/
theorem rawAffineBoundary_neg (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary L p (fun x ↦ -B x) = -rawAffineBoundary L p B := by
  simpa using rawAffineBoundary_smul L p B (-1 : ℝ)

/-- Norm bound on `rawAffineBoundary L p B` from a uniform operator-norm bound `M` on `B` over the
closed affine image `(fun u ↦ p + L u) '' Icc 0 1`. -/
theorem norm_rawAffineBoundary_le (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E} {M : ℝ}
    (hB : ∀ u ∈ Icc (0 : Fin 4 → ℝ) 1, ‖B (p + L u)‖ ≤ M) :
    ‖rawAffineBoundary L p B‖ ≤ 2 * M * ∑ j : Fin 4, ‖affineFaceNormal L j‖ := by
  rw [rawAffineBoundary_eq]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ j : Fin 4,
        ‖(∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth 1 u)) (affineFaceNormal L j)) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth 0 u)) (affineFaceNormal L j)‖
      ≤ ∑ j : Fin 4, (M * ‖affineFaceNormal L j‖ + M * ‖affineFaceNormal L j‖) := by
        refine Finset.sum_le_sum fun j _ ↦ norm_sub_le_of_le ?_ ?_
        · exact norm_integral_affineFace_le L p fun u hu ↦
            hB _ (Fin.insertNth_mem_Icc.mpr ⟨by simp, hu⟩)
        · exact norm_integral_affineFace_le L p fun u hu ↦
            hB _ (Fin.insertNth_mem_Icc.mpr ⟨by simp, hu⟩)
    _ = 2 * M * ∑ j : Fin 4, ‖affineFaceNormal L j‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Reflecting coordinate `k = j.succAbove r` on a transverse face `j ≠ k` reflects the `r`-th
unit 3-cube parameter and negates the face integral against `-affineFaceNormal L j`. -/
private theorem setIntegral_affineFace_comp_negCoord_transverse
    (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) {j k : Fin 4} {r : Fin 3}
    (hr : j.succAbove r = k) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (c : ℝ) :
    ∫ u in Icc (0 : Fin 3 → ℝ) 1,
        B (p + L (Pi.single k 1) + L (ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 4 ↦ ℝ) k
          (j.insertNth c u))) (-affineFaceNormal L j) =
      -∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth c u)) (affineFaceNormal L j) := by
  subst hr
  have hpt (u : Fin 3 → ℝ) :
      Pi.single (j.succAbove r) (1 : ℝ) +
          ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 4 ↦ ℝ) (j.succAbove r)
            (j.insertNth c u) =
        j.insertNth c (Pi.single r 1 +
          ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 3 ↦ ℝ) r u) := by
    ext i
    refine j.succAboveCases (by simp [j.ne_succAbove r]) (fun s ↦ ?_) i
    rcases eq_or_ne s r with rfl | hsr
    · simp
    · simp [hsr]
  simp_rw [add_assoc, ← map_add, hpt, map_neg, integral_neg, neg_inj]
  exact ContinuousLinearEquiv.setIntegral_Icc_single_add_negCoord r
    (fun u ↦ B (p + L (j.insertNth c u)) (affineFaceNormal L j))

/-- Reflecting the `k`-th parameter coordinate `u k ↦ 1 - u k` (for `k = 0`,
`ρ (u₀, u₁, u₂, u₃) = (1 - u₀, u₁, u₂, u₃)`) negates `rawAffineBoundary`: the front and back
`k`-faces swap with the same `affineFaceNormal`, while every transverse face `j ≠ k` has its
`affineFaceNormal` negated and its unit 3-cube parameter reflected along one coordinate. -/
theorem rawAffineBoundary_comp_negCoord (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (k : Fin 4) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary
        (L.comp (ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 4 ↦ ℝ) k).toContinuousLinearMap)
        (p + L (Pi.single k 1)) B =
      -rawAffineBoundary L p B := by
  set ρ := ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 4 ↦ ℝ) k
  have hρ_pi : ρ.toContinuousLinearMap =
      ContinuousLinearMap.piMap (fun i ↦ Function.update (1 : Fin 4 → ℝ) k (-1 : ℝ) i •
        ContinuousLinearMap.id ℝ ℝ) := by
    ext x i
    rcases eq_or_ne i k with rfl | hik
    · simp [ρ]
    · simp [ρ, hik]
  rw [rawAffineBoundary_eq, rawAffineBoundary_eq, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hjk : j = k
  · subst hjk
    have hnorm : affineFaceNormal (L.comp ρ.toContinuousLinearMap) j = affineFaceNormal L j := by
      rw [hρ_pi, affineFaceNormal_comp_piMap_smul_id]
      have hprod : ∏ r : Fin 3, Function.update (1 : Fin 4 → ℝ) j (-1) (j.succAbove r) = 1 :=
        Finset.prod_eq_one fun r _ ↦ by simp
      rw [hprod, one_smul]
    have h1 (u : Fin 3 → ℝ) : Pi.single j (1 : ℝ) + ρ (j.insertNth 1 u) = j.insertNth 0 u := by
      ext i
      exact j.succAboveCases (by simp [ρ]) (fun r ↦ by simp [ρ, j.succAbove_ne r]) i
    have h0 (u : Fin 3 → ℝ) : Pi.single j (1 : ℝ) + ρ (j.insertNth 0 u) = j.insertNth 1 u := by
      ext i
      exact j.succAboveCases (by simp [ρ]) (fun r ↦ by simp [ρ, j.succAbove_ne r]) i
    simp only [hnorm, comp_apply, ContinuousLinearEquiv.coe_coe, add_assoc, ← map_add, h1, h0,
      neg_sub]
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
    have hnorm : affineFaceNormal (L.comp ρ.toContinuousLinearMap) j = -affineFaceNormal L j := by
      rw [hρ_pi, affineFaceNormal_comp_piMap_smul_id]
      have hprod : ∏ s : Fin 3, Function.update (1 : Fin 4 → ℝ) k (-1) (j.succAbove s) = -1 := by
        rw [Finset.prod_eq_single r]
        · simp [hr]
        · intro s _ hsr
          simp [Function.update_of_ne (hr ▸ j.succAbove_right_injective.ne hsr)]
        · exact fun hr' ↦ absurd (Finset.mem_univ r) hr'
      rw [hprod, neg_one_smul]
    simp only [hnorm, comp_apply, ContinuousLinearEquiv.coe_coe, ρ,
      setIntegral_affineFace_comp_negCoord_transverse L p hr B]
    abel

/-- Postcomposing an affine chart with quaternionic conjugation `tupleConj` pulls `Dq` back to
`-star Dq`, negating `rawAffineBoundary` and precomposing each coefficient with `starL' ℝ`. -/
theorem rawAffineBoundary_tupleConj_comp (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary (tupleConj.toContinuousLinearMap.comp L) (tupleConj p) B =
      -rawAffineBoundary L p
        (fun x ↦ (B (tupleConj x)).comp (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap) := by
  rw [← rawAffineBoundary_neg, rawAffineBoundary_eq, rawAffineBoundary_eq]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hfun (c : ℝ) (u : Fin 3 → ℝ) :
      B (tupleConj p + (tupleConj.toContinuousLinearMap.comp L) (j.insertNth c u))
          (affineFaceNormal (tupleConj.toContinuousLinearMap.comp L) j) =
        (-((B (tupleConj (p + L (j.insertNth c u)))).comp
          (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap)) (affineFaceNormal L j) := by
    rw [comp_apply, ContinuousLinearEquiv.coe_coe, ← map_add, affineFaceNormal_tupleConj_comp,
      map_neg, neg_apply, comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]
  simp only [hfun]

/-- Combining quaternionic conjugation `tupleConj` in the target with single-coordinate reflection
`negCoord ℝ k` in the parameters is orientation-preserving and cancels the two minus signs in
`rawAffineBoundary`. -/
theorem rawAffineBoundary_tupleConj_comp_negCoord (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (k : Fin 4) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary
        ((tupleConj.toContinuousLinearMap.comp L).comp
          (ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 4 ↦ ℝ) k).toContinuousLinearMap)
        (tupleConj (p + L (Pi.single k 1))) B =
      rawAffineBoundary L p
        (fun x ↦ (B (tupleConj x)).comp (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap) := by
  have hp : tupleConj (p + L (Pi.single k 1)) =
      tupleConj p + (tupleConj.toContinuousLinearMap.comp L) (Pi.single k 1) :=
    map_add tupleConj p _
  rw [hp, rawAffineBoundary_comp_negCoord, rawAffineBoundary_tupleConj_comp, neg_neg]

/-- Conjugating `rawAffineBoundary` on the orientation-preserving reflected chart `σ ∘ A ∘ ρ`
exchanges the ordered integrand `star (f (star q)) * Dq * star (g (star q))` with `g q * Dq * f q`,
turning left-sided Cauchy integrands into right-sided ones and vice versa without regularity
hypotheses. -/
theorem star_rawAffineBoundary_tupleConj_comp_negCoord_mulLeftRight
    (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) (k : Fin 4) (f g : ℍ → ℍ) :
    star (rawAffineBoundary
        ((tupleConj.toContinuousLinearMap.comp L).comp
          (ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : Fin 4 ↦ ℝ) k).toContinuousLinearMap)
        (tupleConj (p + L (Pi.single k 1)))
        (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
          (star (f (star (dq x)))) (star (g (star (dq x)))))) =
      rawAffineBoundary L p
        (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq x)) (f (dq x))) := by
  rw [rawAffineBoundary_tupleConj_comp_negCoord, rawAffineBoundary_eq, rawAffineBoundary_eq,
    star_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [star_sub, ← integral_star, ← integral_star]
  have hmul (x : Fin 4 → ℝ) (w : ℍ) :
      star (((ContinuousLinearMap.mulLeftRight ℝ ℍ
          (star (f (star (dq (tupleConj x))))) (star (g (star (dq (tupleConj x)))))).comp
            (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap) w) =
        ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq x)) (f (dq x)) w := by
    simp [mul_assoc]
  simp only [hmul]

/-- Splitting a single transverse face `j ≠ k` (`j.succAbove r = k`) along coordinate `k` at
`t ∈ Set.Icc 0 1` decomposes the parametrized face integral into the sum of the two sub-face
integrals, including at the endpoints `t = 0` and `t = 1`. -/
private theorem setIntegral_affineFace_split_transverse (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) {j k : Fin 4} {r : Fin 3} (hr : j.succAbove r = k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E} (c : ℝ)
    (hint : IntegrableOn (fun u ↦ B (p + L (j.insertNth c u)) (affineFaceNormal L j))
      (Icc (0 : Fin 3 → ℝ) 1)) :
    (∫ u in Icc (0 : Fin 3 → ℝ) 1,
        B (p + L ((ContinuousLinearMap.piMap fun i ↦
            Function.update (1 : Fin 4 → ℝ) k t i • ContinuousLinearMap.id ℝ ℝ)
          (j.insertNth c u))) (t • affineFaceNormal L j)) +
      ∫ u in Icc (0 : Fin 3 → ℝ) 1,
        B (p + L (Pi.single k t) + L ((ContinuousLinearMap.piMap fun i ↦
            Function.update (1 : Fin 4 → ℝ) k (1 - t) i • ContinuousLinearMap.id ℝ ℝ)
          (j.insertNth c u))) ((1 - t) • affineFaceNormal L j) =
      ∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth c u)) (affineFaceNormal L j) := by
  subst hr
  let S (s : ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
    ContinuousLinearMap.piMap fun i ↦
      Function.update (1 : Fin 4 → ℝ) (j.succAbove r) s i • ContinuousLinearMap.id ℝ ℝ
  have ha₀ : (0 : Fin 3 → ℝ) ≤ Function.update (1 : Fin 3 → ℝ) r t := fun q ↦ by
    rcases eq_or_ne q r with rfl | hqr
    · simpa using ht.1
    · simp [hqr]
  have hb₁ : Function.update (0 : Fin 3 → ℝ) r t ≤ (1 : Fin 3 → ℝ) := fun q ↦ by
    rcases eq_or_ne q r with rfl | hqr
    · simpa using ht.2
    · simp [hqr]
  have hp₀ : ∏ q : Fin 3, (Function.update (1 : Fin 3 → ℝ) r t q - (0 : Fin 3 → ℝ) q) = t := by
    rw [Finset.prod_eq_single r]
    · simp
    · intro q _ hqr; simp [hqr]
    · exact fun hr' ↦ absurd (Finset.mem_univ r) hr'
  have hp₁ : ∏ q : Fin 3, ((1 : Fin 3 → ℝ) q - Function.update (0 : Fin 3 → ℝ) r t q) = 1 - t := by
    rw [Finset.prod_eq_single r]
    · simp
    · intro q _ hqr; simp [hqr]
    · exact fun hr' ↦ absurd (Finset.mem_univ r) hr'
  have hlow_pt (u : Fin 3 → ℝ) :
      S t (j.insertNth c u) = j.insertNth c (fun q ↦ (0 : Fin 3 → ℝ) q +
        (Function.update (1 : Fin 3 → ℝ) r t q - (0 : Fin 3 → ℝ) q) * u q) := by
    ext i
    refine j.succAboveCases (by simp [S, j.ne_succAbove r]) (fun q ↦ ?_) i
    rcases eq_or_ne q r with rfl | hqr <;> simp [S, *]
  have hupp_pt (u : Fin 3 → ℝ) :
      Pi.single (j.succAbove r) t + S (1 - t) (j.insertNth c u) = j.insertNth c
        (fun q ↦ Function.update (0 : Fin 3 → ℝ) r t q +
          ((1 : Fin 3 → ℝ) q - Function.update (0 : Fin 3 → ℝ) r t q) * u q) := by
    ext i
    refine j.succAboveCases (by simp [S, j.ne_succAbove r]) (fun q ↦ ?_) i
    rcases eq_or_ne q r with rfl | hqr <;> simp [S, *]
  have hI₀ := setIntegral_Icc_eq_smul_integral_unitCube ha₀
    (fun w ↦ B (p + L (j.insertNth c w)) (affineFaceNormal L j))
  have hI₁ := setIntegral_Icc_eq_smul_integral_unitCube hb₁
    (fun w ↦ B (p + L (j.insertNth c w)) (affineFaceNormal L j))
  rw [hp₀] at hI₀
  rw [hp₁] at hI₁
  dsimp only [S] at hlow_pt hupp_pt
  simp_rw [map_smul, integral_smul, add_assoc, ← map_add, hlow_pt, hupp_pt]
  rw [← hI₀, ← hI₁]
  exact TauCeti.setIntegral_Icc_split r ht hint

/-- Rectangular subdivision additivity of `rawAffineBoundary`: splitting `[0, 1]⁴` along coordinate
`k` at `t ∈ Set.Icc 0 1` cancels the two opposite internal facets at `u k = t` and splits every
transverse face `j ≠ k` into two sub-faces. -/
theorem rawAffineBoundary_split (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (k : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB₁ : ∀ j : Fin 4, j ≠ k → IntegrableOn
      (fun u ↦ B (p + L (j.insertNth 1 u)) (affineFaceNormal L j)) (Icc (0 : Fin 3 → ℝ) 1))
    (hB₀ : ∀ j : Fin 4, j ≠ k → IntegrableOn
      (fun u ↦ B (p + L (j.insertNth 0 u)) (affineFaceNormal L j)) (Icc (0 : Fin 3 → ℝ) 1)) :
    rawAffineBoundary
        (L.comp (ContinuousLinearMap.piMap
          (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) k
            (t • ContinuousLinearMap.id ℝ ℝ)))) p B +
      rawAffineBoundary
        (L.comp (ContinuousLinearMap.piMap
          (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) k
            ((1 - t) • ContinuousLinearMap.id ℝ ℝ)))) (p + L (Pi.single k t)) B =
      rawAffineBoundary L p B := by
  let S (s : ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
    ContinuousLinearMap.piMap fun i ↦
      Function.update (1 : Fin 4 → ℝ) k s i • ContinuousLinearMap.id ℝ ℝ
  have hS (s : ℝ) : ContinuousLinearMap.piMap
      (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) k
        (s • ContinuousLinearMap.id ℝ ℝ)) = S s := by
    ext x i
    rcases eq_or_ne i k with rfl | hik <;> simp [S, *]
  rw [hS t, hS (1 - t), rawAffineBoundary_eq, rawAffineBoundary_eq, rawAffineBoundary_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hjk : j = k
  · subst hjk
    have hnorm (s : ℝ) : affineFaceNormal (L.comp (S s)) j = affineFaceNormal L j := by
      rw [affineFaceNormal_comp_piMap_smul_id]
      have hp : ∏ r : Fin 3, Function.update (1 : Fin 4 → ℝ) j s (j.succAbove r) = 1 :=
        Finset.prod_eq_one fun r _ ↦ by simp
      rw [hp, one_smul]
    have hlow (c : ℝ) (u : Fin 3 → ℝ) : S t (j.insertNth c u) = j.insertNth (t * c) u := by
      ext i
      exact j.succAboveCases (by simp [S]) (fun r ↦ by simp [S, j.succAbove_ne r]) i
    have hupp (c : ℝ) (u : Fin 3 → ℝ) :
        Pi.single j t + S (1 - t) (j.insertNth c u) = j.insertNth (t + (1 - t) * c) u := by
      ext i
      exact j.succAboveCases (by simp [S]) (fun r ↦ by simp [S, j.succAbove_ne r]) i
    simp only [hnorm, comp_apply, add_assoc, ← map_add, hlow, hupp, mul_one, mul_zero, add_zero,
      add_sub_cancel]
    abel
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hjk)
    have hnorm (s : ℝ) : affineFaceNormal (L.comp (S s)) j = s • affineFaceNormal L j := by
      rw [affineFaceNormal_comp_piMap_smul_id]
      have hp : ∏ q : Fin 3, Function.update (1 : Fin 4 → ℝ) k s (j.succAbove q) = s := by
        rw [Finset.prod_eq_single r]
        · simp [hr]
        · intro q _ hqr
          simp [Function.update_of_ne (hr ▸ j.succAbove_right_injective.ne hqr)]
        · exact fun hr' ↦ absurd (Finset.mem_univ r) hr'
      rw [hp]
    simp only [hnorm, comp_apply]
    rw [sub_add_sub_comm,
      setIntegral_affineFace_split_transverse L p hr ht 1 (hB₁ j hjk),
      setIntegral_affineFace_split_transverse L p hr ht 0 (hB₀ j hjk)]

/-- Rectangular subdivision additivity of `rawAffineBoundary` for coefficients continuous on the
closed affine parallelepiped `(fun u ↦ p + L u) '' Set.Icc 0 1`. -/
theorem rawAffineBoundary_split_of_continuousOn (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (k : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E} (hB : ContinuousOn B ((fun u ↦ p + L u) '' Icc 0 1)) :
    rawAffineBoundary
        (L.comp (ContinuousLinearMap.piMap
          (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) k
            (t • ContinuousLinearMap.id ℝ ℝ)))) p B +
      rawAffineBoundary
        (L.comp (ContinuousLinearMap.piMap
          (Function.update (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) k
            ((1 - t) • ContinuousLinearMap.id ℝ ℝ)))) (p + L (Pi.single k t)) B =
      rawAffineBoundary L p B :=
  rawAffineBoundary_split L p k ht
    (fun j _ ↦ integrableOn_affineFace L p hB j (by simp))
    (fun j _ ↦ integrableOn_affineFace L p hB j (by simp))

/-- For a Banach-valued coefficient `B` continuous on the closed affine image of `[0, 1]⁴`, each
parametrized Bochner face integral equals the native `BoxIntegral.integral` over the `j`-th face
of the unit 4-box `[0, 1]⁴` for any `BoxIntegral.IntegrationParams`. -/
theorem integral_affineFace_eq_boxIntegral [CompleteSpace E]
    (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB : ContinuousOn B ((fun u ↦ p + L u) '' Icc 0 1)) (j : Fin 4) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (l : BoxIntegral.IntegrationParams) :
    ∫ u in Icc (0 : Fin 3 → ℝ) 1, B (p + L (j.insertNth c u)) (affineFaceNormal L j) =
      BoxIntegral.integral ((BoxIntegral.Box.mk (0 : Fin 4 → ℝ) 1 fun _ ↦ zero_lt_one).face j) l
        (fun u ↦ B (p + L (j.insertNth c u)) (affineFaceNormal L j))
        BoxIntegral.BoxAdditiveMap.volume := by
  let I : BoxIntegral.Box (Fin 4) := BoxIntegral.Box.mk 0 1 fun _ ↦ zero_lt_one
  have hcont : ContinuousOn (fun x ↦ B (p + L x) (affineFaceNormal L j)) (Icc I.lower I.upper) :=
    (hB.comp (by fun_prop) (mapsTo_image _ _)).clm_apply continuousOn_const
  exact (I.integral_face_eq_setIntegral_Icc hcont j hc l).symm

/-- For a Banach-valued coefficient `B` continuous on the closed affine image of `[0, 1]⁴`,
`rawAffineBoundary L p B` equals the front-minus-back sum of `BoxIntegral.integral` over the
coordinate faces of the unit 4-box `[0, 1]⁴`. -/
theorem rawAffineBoundary_eq_boxIntegral [CompleteSpace E]
    (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ) {B : (Fin 4 → ℝ) → ℍ →L[ℝ] E}
    (hB : ContinuousOn B ((fun u ↦ p + L u) '' Icc 0 1)) (l : BoxIntegral.IntegrationParams) :
    rawAffineBoundary L p B =
      ∑ j : Fin 4,
        (BoxIntegral.integral ((BoxIntegral.Box.mk (0 : Fin 4 → ℝ) 1 fun _ ↦ zero_lt_one).face j) l
            (fun u ↦ B (p + L (j.insertNth 1 u)) (affineFaceNormal L j))
            BoxIntegral.BoxAdditiveMap.volume -
          BoxIntegral.integral ((BoxIntegral.Box.mk (0 : Fin 4 → ℝ) 1 fun _ ↦ zero_lt_one).face j) l
            (fun u ↦ B (p + L (j.insertNth 0 u)) (affineFaceNormal L j))
            BoxIntegral.BoxAdditiveMap.volume) := by
  rw [rawAffineBoundary_eq]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_affineFace_eq_boxIntegral L p hB j (by simp) l,
    integral_affineFace_eq_boxIntegral L p hB j (by simp) l]

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-- Evaluation of a weighted surface coefficient on an affine face is precisely the
cofactor pullback of its four coordinate fluxes. No continuity of the coefficient is needed. -/
theorem affineFaceNormal_cofactor (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) (j : Fin 4) (u : Fin 4 → ℝ) :
    B (p + L u) (affineFaceNormal L.toContinuousLinearMap j) =
      L.affineFluxPullback p (fun i x ↦ B x (dq (Pi.single i 1))) j u := by
  simp only [affineFaceNormal_eq, ContinuousLinearEquiv.coe_coe]
  rw [Dq_map_succAbove L j, _root_.map_smul, affineFluxPullback_apply]
  congr 1
  rw [pi_eq_sum_univ' (fun i ↦ L.symm (Pi.single i 1) j)]
  simp only [_root_.map_sum, _root_.map_smul]

/-- The actual affine face integral of the ordered surface form equals the cofactor
boundary sum used by the affine divergence theorem, for either sign of the determinant. -/
theorem rawAffineBoundary_eq_cofactor (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary L.toContinuousLinearMap p B =
      ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            L.affineFluxPullback p (fun i x ↦ B x (dq (Pi.single i 1))) j (j.insertNth 1 u)) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            L.affineFluxPullback p (fun i x ↦ B x (dq (Pi.single i 1))) j (j.insertNth 0 u)) := by
  simp only [rawAffineBoundary_eq, ContinuousLinearEquiv.coe_coe]
  simp_rw [affineFaceNormal_cofactor L p B]

/-- `rawAffineBoundary` on an invertible affine chart equals `L.affineFluxBoundary` of its four
coordinate fluxes, for either sign of `det L`. -/
theorem rawAffineBoundary_eq_affineFluxBoundary (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ))
    (p : Fin 4 → ℝ) (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary L.toContinuousLinearMap p B =
      L.affineFluxBoundary p (fun i x ↦ B x (dq (Pi.single i 1))) := by
  rw [L.rawAffineBoundary_eq_cofactor, L.affineFluxBoundary_eq_sum]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

/-- On an axis-aligned closed box `Set.Icc a b` (`a ≤ b`, including degenerate boxes), the raw
affine boundary integral along `u ↦ a + diag(b - a) u` equals `TauCeti.boxBoundarySum a b` with the
coordinate quaternion units `1, i, j, k`, without continuity or completeness hypotheses. -/
theorem rawAffineBoundary_piMap_smul_id {a b : Fin 4 → ℝ} (hab : a ≤ b)
    (B : (Fin 4 → ℝ) → ℍ →L[ℝ] E) :
    rawAffineBoundary
        (ContinuousLinearMap.piMap fun i ↦ (b i - a i) • ContinuousLinearMap.id ℝ ℝ) a B =
      TauCeti.boxBoundarySum a b (fun i x ↦ B x (dq (Pi.single i 1))) := by
  by_cases hdeg : ∃ k, a k = b k
  · obtain ⟨k, hk⟩ := hdeg
    have hzero : (ContinuousLinearMap.piMap fun i ↦ (b i - a i) • ContinuousLinearMap.id ℝ ℝ)
        (Pi.single k 1) = 0 := by
      ext i
      rcases eq_or_ne i k with rfl | hik
      · simp [hk]
      · simp [hik]
    rw [rawAffineBoundary_eq_zero_of_apply_single_eq_zero hzero,
      TauCeti.boxBoundarySum_eq_zero_of_eq hk]
  · push Not at hdeg
    have hlt : ∀ i, a i < b i := fun i ↦ (hab i).lt_of_ne (hdeg i)
    let L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) := ContinuousLinearEquiv.piCongrRight fun i ↦
      (ContinuousLinearEquiv.smulLeft
        (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hlt i).ne')) : ℝ ≃L[ℝ] ℝ)
    have hL : L.toContinuousLinearMap =
        ContinuousLinearMap.piMap fun i ↦ (b i - a i) • ContinuousLinearMap.id ℝ ℝ := by
      ext x i
      simp [L]
    rw [← hL, L.rawAffineBoundary_eq_affineFluxBoundary,
      ContinuousLinearEquiv.affineFluxBoundary_piCongrRight_smulLeft hlt]

/-- Specialization of `rawAffineBoundary_piMap_smul_id` to the two-sided ordered quaternionic
product `g (dq x) * Dq * f (dq x)`, matching the `TauCeti.boxBoundarySum` integrand of the box
Cauchy and Cauchy–Fueter theorems. -/
theorem rawAffineBoundary_piMap_smul_id_mulLeftRight {a b : Fin 4 → ℝ} (hab : a ≤ b)
    (g f : ℍ → ℍ) :
    rawAffineBoundary
        (ContinuousLinearMap.piMap fun i ↦ (b i - a i) • ContinuousLinearMap.id ℝ ℝ) a
        (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ (g (dq x)) (f (dq x))) =
      TauCeti.boxBoundarySum a b (fun i x ↦ g (dq x) * dq (Pi.single i 1) * f (dq x)) :=
  rawAffineBoundary_piMap_smul_id hab _

end ContinuousLinearMap
