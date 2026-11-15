/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Forms
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Affine

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

For invertible `L`, `rawAffineBoundary_eq_cofactor` identifies these actual face integrals
with the boundary sum of `L.affineFluxPullback p (fun i x ↦ B x (dq (Pi.single i 1)))`.
Thus the cofactor divergence theorem computes the same functional as integration of
the pulled-back surface form. The determinant is signed: the parameter orientation
is outward-first exactly when the determinant is positive.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, equation (18), for the ordered surface
  element and outward-first convention.
* The cofactor comparison uses `ContinuousLinearEquiv.Dq_map_succAbove`, derived from the
  determinant interpretation of `Dq`.
-/

public section

open MeasureTheory Set TauCeti.Quaternion
open scoped Quaternion

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

/-- A degenerate tangent triple contributes zero, without any nonsingularity hypothesis. -/
theorem affineFaceNormal_eq_zero (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (j : Fin 4)
    (h : ¬LinearIndependent ℝ (fun r : Fin 3 ↦ L (Pi.single (j.succAbove r) 1))) :
    affineFaceNormal L j = 0 := by
  have hz := Dq.toAlternatingMap.map_linearDependent _ h
  rw [ContinuousAlternatingMap.coe_toAlternatingMap] at hz
  rw [affineFaceNormal_eq, hz, smul_zero]

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

/-- Constant coefficients have zero boundary integral: opposite faces cancel, including
for singular affine maps. -/
@[simp]
theorem rawAffineBoundary_const (L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
    (B : ℍ →L[ℝ] E) : rawAffineBoundary L p (fun _ ↦ B) = 0 := by
  simp [rawAffineBoundary_eq]

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

end ContinuousLinearEquiv
