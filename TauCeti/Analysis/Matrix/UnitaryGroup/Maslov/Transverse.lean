/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Loop
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Multiplicity
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Transverse

/-!
# Souriau's index computes the Maslov index relative to `ℝⁿ`

Two Maslov indices of paths of Lagrangian subspaces of `ℂⁿ` relative to `ℝⁿ` are available.

* The native index `TauCeti.TotallyRealPath.transverseMaslovIndex`, defined for a path `Λ` of
  maximal totally real subspaces between the chart subspaces `{S₀ y + i y}` and `{S₁ y + i y}` of
  symmetric real matrices, which are transverse to `ℝⁿ`: the relative Maslov index of `Λ` against
  a path of chart subspaces. It satisfies the axioms of Robbin and Salamon (zero, catenation,
  homotopy, normalization, naturality and direct sum), but has no crossing-form formula of its own.
* Souriau's spectral index `Matrix.UnitaryGroup.maslovIndex` of a path `γ` of unitary frames, the
  Robbin–Salamon index of the path of Lagrangians `t ↦ γ t ℝⁿ`, defined for every path. It
  satisfies the localization axiom
  (`Matrix.UnitaryGroup.maslovIndex_eq_signature_sub_of_souriau_eq_cayley`) and the crossing-form
  formula (`Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`) for
  paths of graphs `{x + i A x}` of symmetric matrices.

This file shows that the two agree, and transfers the localization axiom and the crossing-form
formula to the native index.

**The comparison** (`TauCeti.TotallyRealPath.transverseMaslovIndex_eq_maslovIndex`). If a path `γ`
of unitary frames frames `Λ`, that is `Λ t = γ t ℝⁿ`, then the Maslov index of `Λ` relative to
`ℝⁿ` is Souriau's index of `γ`. By definition the former is the relative Maslov index of `Λ`
against the chart path `t ↦ {S t y + i y}` of the segment `S` from `S₀` to `S₁`, and the relative
Maslov index of two framed paths is the difference of their Souriau indices
(`Matrix.UnitaryGroup.relativeMaslovIndex_realImagePath`). The chart subspaces are framed by
`i` times the frames of the graphs of `-S t`, since `S + i = i (1 - i S)`
(`Matrix.UnitaryGroup.exists_path_realImage_eq_lagrangianChart`). Every chart subspace meets
`ℝⁿ` only in `0`, so by the zero axiom
(`Matrix.UnitaryGroup.maslovIndex_eq_zero_of_realImage_eq_lagrangianChart`) the Souriau index of
the chart path vanishes.

**Localization** (`TauCeti.TotallyRealPath.two_mul_transverseMaslovIndex_eq_signature_sub`). For
an invertible symmetric matrix `A` the graph `{x + i A x}` is the chart subspace of `A⁻¹`
(`Matrix.realImage_one_add_I_smul_eq_lagrangianChart_inv`, in
`TauCeti.LinearAlgebra.TotallyReal.Euclidean`). So a path of graphs of a continuous
path `t ↦ A t` of symmetric matrices, with `A 0` and `A 1` invertible, has a Maslov index relative
to `ℝⁿ`, and twice it is the change of the signature of `A`:

`2 μ(Λ) = sign (A 1) - sign (A 0)`.

**Crossing forms** (`TauCeti.TotallyRealPath.transverseMaslovIndex_eq_finsum_crossingForm`). If
moreover the crossings, the parameters where `A t` is singular, are regular, the Maslov index
relative to `ℝⁿ` is the sum of the signatures of the crossing forms
`x ↦ x ⬝ᵥ A' t *ᵥ x` on the kernels of `A t` (`Matrix.crossingForm`). The endpoints, where `A` is
invertible, are not crossings.

## Main results

* `Matrix.UnitaryGroup.exists_path_realImage_eq_lagrangianChart`: a continuous path of chart
  subspaces of symmetric matrices has a continuous path of unitary frames.
* `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_realImage_eq_lagrangianChart`: Souriau's index of a
  path of frames of chart subspaces is zero.
* `TauCeti.TotallyRealPath.transverseMaslovIndex_eq_maslovIndex`: the Maslov index relative to
  `ℝⁿ` of a framed path is Souriau's index of its frames.
* `TauCeti.TotallyRealPath.two_mul_transverseMaslovIndex_eq_signature_sub`: the localization
  axiom for the Maslov index relative to `ℝⁿ`.
* `TauCeti.TotallyRealPath.transverseMaslovIndex_eq_finsum_crossingForm`: the crossing-form
  formula for the Maslov index relative to `ℝⁿ`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Theorem 2.3 (the localization axiom) and Section 2 (crossing forms and the Maslov index of a
  path with regular crossings).
* J.-M. Souriau, *Construction explicite de l'indice de Maslov. Applications*, Group theoretical
  methods in physics, Lecture Notes in Physics **50** (1976), 117--148.
-/

public section

open Module Set
open scoped unitInterval

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Matrix

open TauCeti

namespace UnitaryGroup

/-- **Frames of a path of chart subspaces.** A continuous path `t ↦ S t` of symmetric real
matrices has a continuous path of unitary frames of the chart subspaces `{S t y + i y}`. The
frames are `i` times the frames of the graphs `{x - i S t x}` of `-S t`, since
`S + i = i (1 - i S)`. -/
theorem exists_path_realImage_eq_lagrangianChart {S : I → Matrix n n ℝ} (hSc : Continuous S)
    (hS : ∀ t, (S t).IsSymm) :
    ∃ (U V : unitaryGroup n ℂ) (δ : Path U V), ∀ t,
      (δ t : Matrix n n ℂ).realImage = (S t).lagrangianChart := by
  obtain ⟨U, V, δ, hδ⟩ := exists_path_realImage_eq_and_souriau_eq_cayley (A := fun t ↦ -S t)
    hSc.neg fun t ↦ (isHermitian_iff_isSymm.2 (hS t)).neg
  -- The scalar unitary matrix `i`.
  let u : unitaryGroup n ℂ := scalarHom n ℂ ⟨Complex.I, by simp [Unitary.mem_iff]⟩
  refine ⟨u * U, u * V, δ.map (continuous_const_mul u), fun t ↦ ?_⟩
  have hframe : (u : Matrix n n ℂ) * (1 + Complex.I • (-S t).map ((↑) : ℝ → ℂ)) =
      (S t).lagrangianChartFrame := by
    rw [coe_scalarHom, lagrangianChartFrame_def]
    ext i j
    simp [diagonal_mul, mul_add, ← mul_assoc, add_comm]
  rw [Path.map_coe, Function.comp_apply, Submonoid.coe_mul, realImage_mul, (hδ t).1,
    ← realImage_mul, hframe, lagrangianChart_def]

/-- **Zero axiom for chart subspaces.** Souriau's index of a path of unitary frames of chart
subspaces `{S t y + i y}` vanishes: these subspaces all meet `ℝⁿ` only in `0`. -/
theorem maslovIndex_eq_zero_of_realImage_eq_lagrangianChart {U V : unitaryGroup n ℂ}
    (γ : Path U V) {S : I → Matrix n n ℝ}
    (h : ∀ t, (γ t : Matrix n n ℂ).realImage = (S t).lagrangianChart) :
    maslovIndex γ = 0 :=
  maslovIndex_eq_zero_of_finrank_eq γ (k := 0) fun t ↦ by
    rw [h, lagrangianChart_inf_realSubspace, finrank_bot]

end UnitaryGroup

end Matrix

namespace TauCeti

namespace TotallyRealPath

open Matrix Matrix.UnitaryGroup

/-- **Souriau's index computes the Maslov index relative to `ℝⁿ`.** Let `Λ` be a path of maximal
totally real subspaces of `ℂⁿ` between the chart subspaces of the symmetric matrices `S₀` and
`S₁`, framed by a path `γ` of unitary frames: `Λ t = γ t ℝⁿ`. Then its Maslov index relative to
`ℝⁿ` is Souriau's index of `γ`. -/
theorem transverseMaslovIndex_eq_maslovIndex (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    {U V : unitaryGroup n ℂ} (γ : Path U V) (hΛ : ∀ t, Λ t = (γ t : Matrix n n ℂ).realImage)
    {S₀ S₁ : Matrix n n ℝ} (hS₀ : S₀.IsSymm) (hS₁ : S₁.IsSymm) (h₀ : Λ 0 = S₀.lagrangianChart)
    (h₁ : Λ 1 = S₁.lagrangianChart) :
    (Λ.transverseMaslovIndex hS₀ hS₁ h₀ h₁ : ℝ) = maslovIndex γ := by
  have hΛγ : Λ = realImagePath γ := ext fun t ↦ (hΛ t).trans (realImagePath_apply γ t).symm
  -- The chart path of the segment from `S₀` to `S₁` is framed, with Souriau index zero.
  obtain ⟨U', V', δ, hδ⟩ := exists_path_realImage_eq_lagrangianChart
    (Path.segment S₀ S₁).continuous (isSymm_segment hS₀ hS₁)
  have hδΓ : realImagePath δ =
      ofLagrangianChart (Path.segment S₀ S₁) (isSymm_segment hS₀ hS₁) :=
    ext fun t ↦ by rw [realImagePath_apply, hδ, ofLagrangianChart_apply]
  subst hΛγ
  rw [transverseMaslovIndex_eq_relativeMaslovIndex _ _ (isSymm_segment hS₀ hS₁),
    relativeMaslovIndex_congr_right hδΓ.symm, relativeMaslovIndex_realImagePath,
    maslovIndex_eq_zero_of_realImage_eq_lagrangianChart δ hδ, sub_zero]

/-- **The localization axiom for the Maslov index relative to `ℝⁿ`.** Let `t ↦ A t` be a
continuous path of symmetric real matrices with `A 0` and `A 1` invertible, and `Λ` the path of
their graphs `{x + i A t x}`, which starts at the chart subspace of `(A 0)⁻¹` and ends at that of
`(A 1)⁻¹`. Then twice the Maslov index of `Λ` relative to `ℝⁿ` is the change of the signature of
`A`. -/
theorem two_mul_transverseMaslovIndex_eq_signature_sub (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    {A : I → Matrix n n ℝ} (hAc : Continuous A) (hA : ∀ t, (A t).IsSymm)
    (hΛ : ∀ t, Λ t = (1 + Complex.I • (A t).map ((↑) : ℝ → ℂ)).realImage) (hA₀ : IsUnit (A 0))
    (hA₁ : IsUnit (A 1)) :
    2 * Λ.transverseMaslovIndex (hA 0).inv (hA 1).inv
        (by rw [hΛ, realImage_one_add_I_smul_eq_lagrangianChart_inv hA₀])
        (by rw [hΛ, realImage_one_add_I_smul_eq_lagrangianChart_inv hA₁]) =
      signature (A 1) - signature (A 0) := by
  have hH (t : I) : (A t).IsHermitian := isHermitian_iff_isSymm.2 (hA t)
  obtain ⟨U, V, δ, hδ⟩ := exists_path_realImage_eq_and_souriau_eq_cayley hAc hH
  have hμ := transverseMaslovIndex_eq_maslovIndex Λ δ (fun t ↦ (hΛ t).trans (hδ t).1.symm)
    (hA 0).inv (hA 1).inv (by rw [hΛ, realImage_one_add_I_smul_eq_lagrangianChart_inv hA₀])
    (by rw [hΛ, realImage_one_add_I_smul_eq_lagrangianChart_inv hA₁])
  rw [maslovIndex_eq_signature_sub_of_souriau_eq_cayley δ hAc hH fun t ↦ (hδ t).2,
    eq_div_iff two_ne_zero] at hμ
  exact_mod_cast (mul_comm _ _).trans hμ

/-- **The crossing-form formula for the Maslov index relative to `ℝⁿ`.** Let `t ↦ A t` be a path
of symmetric real matrices, continuous on `[0, 1]`, with `A 0` and `A 1` invertible, and `Λ` the
path of their graphs `{x + i A t x}`. Suppose that at every crossing `t`, where `A t` is singular,
`A` has entrywise derivative `A' t` within `[0, 1]` and the crossing form
`Matrix.crossingForm (A t) (A' t)` is nondegenerate. Then the Maslov index of `Λ` relative to `ℝⁿ`
is the sum of the signatures of the crossing forms. -/
theorem transverseMaslovIndex_eq_finsum_crossingForm (Λ : TotallyRealPath (EuclideanSpace ℂ n))
    {A A' : ℝ → Matrix n n ℝ} (hAc : ContinuousOn A (Icc 0 1))
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, (A t).IsSymm)
    (hΛ : ∀ t : I, Λ t = (1 + Complex.I • (A t).map ((↑) : ℝ → ℂ)).realImage)
    (hA₀ : IsUnit (A 0)) (hA₁ : IsUnit (A 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 →
      ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' t i j) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 → (crossingForm (A t) (A' t)).Nondegenerate) :
    Λ.transverseMaslovIndex (hA 0 (left_mem_Icc.2 zero_le_one)).inv
        (hA 1 (right_mem_Icc.2 zero_le_one)).inv
        (by rw [hΛ, Icc.coe_zero, realImage_one_add_I_smul_eq_lagrangianChart_inv hA₀])
        (by rw [hΛ, Icc.coe_one, realImage_one_add_I_smul_eq_lagrangianChart_inv hA₁]) =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        ((sigPos (crossingForm (A t) (A' t)) : ℤ) - sigNeg (crossingForm (A t) (A' t))) := by
  have hloc := two_mul_transverseMaslovIndex_eq_signature_sub Λ (A := fun t : I ↦ A t)
    (hAc.comp_continuous continuous_subtypeVal fun t ↦ t.property) (fun t ↦ hA t t.property) hΛ
    (by simpa using hA₀) (by simpa using hA₁)
  simp only [Icc.coe_zero, Icc.coe_one] at hloc
  rw [signature_sub_signature_eq_crossingForm_add_two_mul_finsum zero_lt_one hAc hA hd hreg,
    sigPos_sub_sigNeg_crossingForm_eq_zero (hA 0 (left_mem_Icc.2 zero_le_one))
      ((isUnit_iff_isUnit_det _).1 hA₀).ne_zero,
    sigPos_sub_sigNeg_crossingForm_eq_zero (hA 1 (right_mem_Icc.2 zero_le_one))
      ((isUnit_iff_isUnit_det _).1 hA₁).ne_zero] at hloc
  omega

end TotallyRealPath

end TauCeti
