/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Normalize
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lebesgue measure on the symmetric subspace

`TauCeti.symmetricLebesgue p` is the pushforward of product Lebesgue measure on the
upper-triangular coordinates along `(TauCeti.symmetricCoordinates p).symm`. This is the
normalization used by the Wishart densities and the multivariate-Gamma integral: the
coordinate unit cube has measure one.

The Frobenius volume of `measureSpaceOfInnerProductSpace` is a Haar measure for the same
topology, but a different normalization: the off-diagonal coordinate directions `Eᵢⱼ + Eⱼᵢ`
have Frobenius norm `√2`, so Frobenius volume is `2 ^ (p * (p - 1) / 4)` times
`symmetricLebesgue p`, with a real exponent.

## Main declarations

* `TauCeti.symmetricLebesgue` — Lebesgue measure on the symmetric subspace, normalized by the
  upper-triangular coordinates.
* `TauCeti.measurePreserving_symmetricCoordinates_symm` — the coordinate reconstruction is
  measure preserving.
* `TauCeti.symmetricLebesgueIsAddHaarMeasure` — `symmetricLebesgue p` is an additive Haar
  measure, as required by Mathlib's Jacobian API.
* `TauCeti.symmetricOrthonormalBasis` — the Frobenius-orthonormal basis obtained by rescaling
  off-diagonal vectors of `TauCeti.symmetricBasis` by `(√2)⁻¹`.
* `TauCeti.volume_symmetricMatrix_eq_smul_symmetricLebesgue` — comparison with the Frobenius
  volume.
* `TauCeti.symmetricLebesgue_zero` — in dimension zero, `symmetricLebesgue` is the Dirac
  measure on the unique symmetric matrix.
* `TauCeti.measurePreserving_symmetricFinOneEquiv` — in dimension one, reading the single entry
  carries `symmetricLebesgue` to Lebesgue measure on `ℝ`.
-/

public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace TauCeti

/-- Lebesgue measure on the symmetric subspace: the pushforward of product Lebesgue measure on
the upper-triangular coordinates along the coordinate reconstruction. The coordinate unit cube
has measure one; this is the normalization used by the Wishart densities. -/
def symmetricLebesgue (p : ℕ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (volume : Measure (upperTriangle p → ℝ)).map (symmetricCoordinates p).symm

/-- The coordinate reconstruction maps product Lebesgue measure to `symmetricLebesgue`. -/
theorem measurePreserving_symmetricCoordinates_symm (p : ℕ) :
    MeasurePreserving (symmetricCoordinates p).symm volume (symmetricLebesgue p) :=
  ⟨(symmetricCoordinates p).symm.continuous.measurable, rfl⟩

/-- The upper-triangular coordinates map `symmetricLebesgue` to product Lebesgue measure. -/
theorem measurePreserving_symmetricCoordinates (p : ℕ) :
    MeasurePreserving (symmetricCoordinates p) (symmetricLebesgue p) volume := by
  have h := measurePreserving_symmetricCoordinates_symm p
  rw [← symmetricCoordinatesMeasurableEquiv_symm_coe] at h
  have h' := h.symm (symmetricCoordinatesMeasurableEquiv p).symm
  rwa [MeasurableEquiv.symm_symm, symmetricCoordinatesMeasurableEquiv_coe] at h'

/-- `symmetricLebesgue` is an additive Haar measure, as required by Mathlib's Jacobian API. -/
instance symmetricLebesgueIsAddHaarMeasure (p : ℕ) :
    (symmetricLebesgue p).IsAddHaarMeasure :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (symmetricCoordinates p).symm volume

/-! ### Comparison with the Frobenius volume

The comparison goes through the coordinate basis `TauCeti.symmetricBasis p`, whose vectors are
the pairwise orthogonal symmetric matrices `Eᵢⱼ + Eⱼᵢ` (Frobenius norm `√2`) and `Eᵢᵢ` (Frobenius
norm `1`). Normalizing by their norms gives the orthonormal basis
`TauCeti.symmetricOrthonormalBasis p`, and the product of their norms gives the ratio between
Frobenius volume and `TauCeti.symmetricLebesgue p`. -/

section comparison

private theorem symmetricLebesgue_eq_addHaar (p : ℕ) :
    symmetricLebesgue p = (symmetricBasis p).addHaar := by
  have hb : (Pi.basisFun ℝ (upperTriangle p)).map
      (symmetricCoordinates p).symm.toLinearEquiv = symmetricBasis p :=
    Basis.eq_of_apply_eq fun ij => by simp [symmetricBasis_apply]
  rw [symmetricLebesgue, ← Module.Basis.addHaar_basisFun, Basis.map_addHaar, hb]

private theorem sum_mul_single (p : ℕ) (A : Matrix (Fin p) (Fin p) ℝ) (k l : Fin p) :
    ∑ a, ∑ b, A a b * Matrix.single k l (1 : ℝ) a b = A k l := by
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- The coordinate basis vector at `kl` pairs with a symmetric matrix through its `kl` entry,
doubled off the diagonal. -/
private theorem inner_symmetricBasis (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (kl : upperTriangle p) :
    ⟪A, symmetricBasis p kl⟫ =
      (if kl.1.1 = kl.1.2 then 1 else 2) * (A : Matrix (Fin p) (Fin p) ℝ) kl.1.1 kl.1.2 := by
  let _ : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℝ) := Matrix.frobeniusInnerProductSpace
  obtain ⟨⟨k, l⟩, hkl⟩ := kl
  rw [selfAdjoint.coe_inner, Matrix.frobenius_real_inner_eq_sum_mul]
  by_cases h : k = l
  · subst h
    rw [coe_symmetricBasis_diag, sum_mul_single]
    simp
  · rw [coe_symmetricBasis_offDiag p hkl h]
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_single,
      selfAdjoint.coe_apply_comm A l k]
    rw [ite_eq_right h]
    ring

private theorem pairwise_inner_symmetricBasis (p : ℕ) :
    Pairwise fun ij kl ↦ ⟪symmetricBasis p ij, symmetricBasis p kl⟫ = 0 := by
  intro ij ⟨⟨k, l⟩, hkl⟩ hne
  rw [inner_symmetricBasis, coe_symmetricBasis_apply_of_le p ij hkl, ite_eq_right hne, mul_zero]

private theorem norm_symmetricBasis (p : ℕ) (ij : upperTriangle p) :
    ‖symmetricBasis p ij‖ = if ij.1.1 = ij.1.2 then 1 else Real.sqrt 2 := by
  obtain ⟨⟨k, l⟩, hkl⟩ := ij
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_symmetricBasis,
    coe_symmetricBasis_apply_of_le p _ hkl, ite_eq_left rfl, mul_one]
  split_ifs <;> simp

/-- The Frobenius-orthonormal basis of the real symmetric subspace obtained by rescaling the
off-diagonal vectors of `TauCeti.symmetricBasis` by `(√2)⁻¹`. -/
def symmetricOrthonormalBasis (p : ℕ) :
    OrthonormalBasis (upperTriangle p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (symmetricBasis p).toOrthonormalBasisOfOrthogonal (pairwise_inner_symmetricBasis p)

/-- Each vector of `TauCeti.symmetricOrthonormalBasis` is `symmetricBasis` on the diagonal and
`(√2)⁻¹ • symmetricBasis` off it. -/
theorem symmetricOrthonormalBasis_apply (p : ℕ) (ij : upperTriangle p) :
    symmetricOrthonormalBasis p ij =
      if ij.1.1 = ij.1.2 then symmetricBasis p ij
      else (Real.sqrt 2)⁻¹ • symmetricBasis p ij := by
  rw [symmetricOrthonormalBasis, Basis.toOrthonormalBasisOfOrthogonal_apply, norm_symmetricBasis]
  split_ifs <;> simp

/-- There are `∑ i < p, i = p * (p - 1) / 2` upper-triangular positions off the diagonal. -/
private theorem card_offDiag (p : ℕ) :
    (Finset.univ.filter fun ij : upperTriangle p => ij.1.1 ≠ ij.1.2).card =
      ∑ i ∈ Finset.range p, i := by
  have e : {a : Sym2 (Fin p) // ¬a.IsDiag} ≃ {ij : upperTriangle p // ij.1.1 ≠ ij.1.2} :=
    (Sym2.sortEquiv (α := Fin p)).subtypeEquiv <| Sym2.ind fun a b => by simp
  rw [← Fintype.card_subtype, ← Fintype.card_congr e, Sym2.card_subtype_not_diag,
    Fintype.card_fin, Nat.choose_two_right, Finset.sum_range_id]

/-- The triangular number of `p` doubles to `p * (p - 1)`; stated over `ℝ` so that the real
subtraction on the right is unproblematic at `p = 0`. -/
private theorem two_mul_card_offDiag (p : ℕ) :
    2 * ((∑ i ∈ Finset.range p, i : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
  have h := Finset.sum_range_id_mul_two p
  rcases p with _ | n
  · simp
  · have hcast : ((∑ i ∈ Finset.range (n + 1), i : ℕ) : ℝ) * 2 =
        ((n + 1 : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at hcast ⊢
    linarith

end comparison

/-- The Frobenius volume of the symmetric subspace is `2 ^ (p * (p - 1) / 4)` times
`symmetricLebesgue`, with a real exponent: each of the `p * (p - 1) / 2` off-diagonal
coordinate directions `Eᵢⱼ + Eⱼᵢ` has Frobenius norm `√2`. -/
theorem volume_symmetricMatrix_eq_smul_symmetricLebesgue (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) =
      ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 4)) • symmetricLebesgue p := by
  rw [symmetricLebesgue_eq_addHaar,
    (symmetricBasis p).volume_eq_smul_addHaar_of_pairwise_inner_eq_zero
      (pairwise_inner_symmetricBasis p)]
  congr 2
  simp_rw [norm_symmetricBasis]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, card_offDiag,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  linarith [two_mul_card_offDiag p]

/-- In dimension zero, the symmetric subspace is a single point and `symmetricLebesgue` is the
Dirac measure there, so the dimension-zero Wishart laws need no special casing. -/
theorem symmetricLebesgue_zero : symmetricLebesgue 0 = Measure.dirac 0 := by
  have : IsEmpty (upperTriangle 0) := ⟨fun ij => ij.1.1.elim0⟩
  rw [symmetricLebesgue, volume_pi, Measure.pi_of_empty _ 0, Measure.map_dirac, map_zero]

/-- In dimension one, reading the single entry of a symmetric matrix carries `symmetricLebesgue`
to Lebesgue measure on `ℝ`, so the one-dimensional Wishart densities are ordinary densities on
the real line. -/
theorem measurePreserving_symmetricFinOneEquiv :
    MeasurePreserving symmetricFinOneEquiv (symmetricLebesgue 1) volume := by
  have h : (symmetricFinOneEquiv : _ → ℝ) =
      MeasurableEquiv.funUnique (upperTriangle 1) ℝ ∘ symmetricCoordinates 1 := by
    funext A
    simp [symmetricCoordinates_apply, Fin.fin_one_eq_zero]
  rw [h]
  exact (volume_preserving_funUnique _ ℝ).comp (measurePreserving_symmetricCoordinates 1)

end TauCeti
