/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PuncturedPlane
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Plumbing

/-!
# The conformal type of the plumbed four-punctured spheres

Composing two pair-of-pants products plumbs the output end at `∞` of one pair of pants `S'` into
an input end `q ∈ {0, 1}` of another pair of pants `S`, along a neck of length `L`. The result is
the four-punctured sphere `ℂ ∖ {0, 1, ψ_{q,L}(1)}` with output at `∞`
(`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_image_union`), where `ψ_{q,L}` is the plumbing
map. Its three inputs, in the order of the inputs of the composed operation, are:

* for `q = 0`, the composition `(x₁ x₂) x₃`: the inputs of `S'` at `0` and `ψ_{0,L}(1) = ε`,
  then the remaining input of `S` at `1`;
* for `q = 1`, the composition `x₁ (x₂ x₃)`: the remaining input of `S` at `0`, then the inputs of
  `S'` at `1` and `ψ_{1,L}(1) = 1 - ε`,

where `ε = e^{-2πL} / 4` (`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_zero_one`,
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_one_one`).

Spheres with three ordered finite input punctures `c` and output at `∞` are classified, up to
holomorphic embeddings respecting the labels, by the cross ratio
`OnePoint.crossRatio (c 0) (c 2) ∞ (c 1) = (c 1 - c 0) / (c 2 - c 0)`
(`TauCeti.exists_isPuncturedEmbedding_iff_crossRatio_eq`). This file computes it for the two
plumbing families: it is `ε` for the composition `(x₁ x₂) x₃` and `1 / (1 - ε)` for the
composition `x₁ (x₂ x₃)`. Consequently:

* within each family, different neck lengths give four-punctured spheres that are not related by
  a label-preserving holomorphic embedding, so the neck length `L ≥ 0` injectively parametrizes
  each family, tracing the real segments `(0, 1/4]` and `(1, 4/3]` of cross ratios in the moduli
  space `M(0, 4)`, and no reparametrization identifies two members of a family
  (`TauCeti.ThricePuncturedSphere.exists_isPuncturedEmbedding_plumbingMap_zero_iff`,
  `TauCeti.ThricePuncturedSphere.exists_isPuncturedEmbedding_plumbingMap_one_iff`);
* for neck lengths `L, L' ≥ 0`, no member of one family is conformally equivalent to a member of
  the other as a sphere with labelled punctures, since their cross ratios lie in `(0, 1/4]` and in
  `(1, 4/3]` (`TauCeti.ThricePuncturedSphere.not_exists_isPuncturedEmbedding_plumbingMap_zero_one`,
  `TauCeti.ThricePuncturedSphere.not_exists_isPuncturedEmbedding_plumbingMap_one_zero`);
* as `L → ∞` the cross ratio tends to `0` in the first family and to `1` in the second
  (`TauCeti.ThricePuncturedSphere.tendsto_crossRatio_plumbingMap_zero_atTop`,
  `TauCeti.ThricePuncturedSphere.tendsto_crossRatio_plumbingMap_one_atTop`): the two ways of
  composing two products are the two distinct boundary points `0` and `1` of the cross-ratio
  coordinate on `M(0, 4)` at which the four-punctured sphere breaks into two pairs of pants.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Appendix D, on the
  moduli space of four-pointed genus-zero curves and its cross ratio coordinate.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9, on gluing surfaces with
  strip-like ends with a gluing length.
-/

public noncomputable section

open Filter Function Topology Real
open scoped OnePoint

namespace TauCeti.ThricePuncturedSphere

open Puncture

/-- The inputs `0, ε, 1` of the composition `(x₁ x₂) x₃` are distinct for `L ≥ 0`. -/
theorem vecCons_plumbingMap_zero_injective {L : ℝ} (hL : 0 ≤ L) :
    Injective ![(0 : ℂ), zero.plumbingMap L 1, 1] := by
  have hε : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have h0 : zero.plumbingMap L 1 ≠ 0 := by
    rw [plumbingMap_zero_one]
    exact_mod_cast (by positivity : 0 < Real.exp (-(2 * π * L)) / 4).ne'
  have h1 : zero.plumbingMap L 1 ≠ 1 := by
    rw [plumbingMap_zero_one]
    exact_mod_cast (by linarith : Real.exp (-(2 * π * L)) / 4 < 1).ne
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The inputs `0, 1, 1 - ε` of the composition `x₁ (x₂ x₃)` are distinct for `L ≥ 0`. -/
theorem vecCons_plumbingMap_one_injective {L : ℝ} (hL : 0 ≤ L) :
    Injective ![(0 : ℂ), 1, one.plumbingMap L 1] := by
  have hε : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have h0 : one.plumbingMap L 1 ≠ 0 := by
    rw [plumbingMap_one_one, sub_ne_zero]
    exact_mod_cast (by linarith : Real.exp (-(2 * π * L)) / 4 < 1).ne'
  have h1 : one.plumbingMap L 1 ≠ 1 := by
    rw [plumbingMap_one_one, Ne, sub_eq_self]
    exact_mod_cast (by positivity : 0 < Real.exp (-(2 * π * L)) / 4).ne'
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The cross ratio of the composition `(x₁ x₂) x₃` with neck length `L` is
`ε = e^{-2πL} / 4`. -/
theorem crossRatio_plumbingMap_zero (L : ℝ) :
    OnePoint.crossRatio ((0 : ℂ) : OnePoint ℂ) (1 : ℂ) ∞ (zero.plumbingMap L 1) =
      (((Real.exp (-(2 * π * L)) / 4 : ℝ) : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.crossRatio_zero_one_infty, plumbingMap_zero_one]

/-- The cross ratio of the composition `x₁ (x₂ x₃)` with neck length `L ≥ 0` is `1 / (1 - ε)`
with `ε = e^{-2πL} / 4`. -/
theorem crossRatio_plumbingMap_one {L : ℝ} (hL : 0 ≤ L) :
    OnePoint.crossRatio ((0 : ℂ) : OnePoint ℂ) (one.plumbingMap L 1) ∞ (1 : ℂ) =
      ((((1 - Real.exp (-(2 * π * L)) / 4)⁻¹ : ℝ) : ℂ) : OnePoint ℂ) := by
  have hne : (0 : ℂ) ≠ one.plumbingMap L 1 :=
    (vecCons_plumbingMap_one_injective hL).ne (by decide : (0 : Fin 3) ≠ 2)
  rw [OnePoint.crossRatio_coe_coe_infty_coe hne, OnePoint.coe_eq_coe, plumbingMap_one_one]
  push_cast
  ring

/-- **Different neck lengths give different conformal types.** The compositions `(x₁ x₂) x₃`
with neck lengths `L` and `L'` admit a label-preserving holomorphic embedding exactly when
`L = L'`. -/
theorem exists_isPuncturedEmbedding_plumbingMap_zero_iff {L L' : ℝ} :
    (∃ f, IsPuncturedEmbedding ![(0 : ℂ), zero.plumbingMap L 1, 1]
      ![(0 : ℂ), zero.plumbingMap L' 1, 1] f) ↔ L = L' := by
  rw [exists_isPuncturedEmbedding_iff]
  refine ⟨fun ⟨a, b, _, h⟩ => ?_, fun h => ⟨1, 0, one_ne_zero, fun i => by simp [h]⟩⟩
  -- The affine map fixes `0` and `1`, so it is the identity.
  have hb : b = 0 := by simpa using (h 0).symm
  have ha : a = 1 := by simpa [hb] using (h 2).symm
  have hε := h 1
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ha, hb, one_mul, add_zero,
    plumbingMap_zero_one, Complex.ofReal_inj] at hε
  have h' : -(2 * π * L') = -(2 * π * L) := Real.exp_injective (by linarith [hε])
  nlinarith [pi_pos]

/-- **Different neck lengths give different conformal types.** The compositions `x₁ (x₂ x₃)`
with neck lengths `L` and `L'` admit a label-preserving holomorphic embedding exactly when
`L = L'`. -/
theorem exists_isPuncturedEmbedding_plumbingMap_one_iff {L L' : ℝ} :
    (∃ f, IsPuncturedEmbedding ![(0 : ℂ), 1, one.plumbingMap L 1]
      ![(0 : ℂ), 1, one.plumbingMap L' 1] f) ↔ L = L' := by
  rw [exists_isPuncturedEmbedding_iff]
  refine ⟨fun ⟨a, b, _, h⟩ => ?_, fun h => ⟨1, 0, one_ne_zero, fun i => by simp [h]⟩⟩
  -- The affine map fixes `0` and `1`, so it is the identity.
  have hb : b = 0 := by simpa using (h 0).symm
  have ha : a = 1 := by simpa [hb] using (h 1).symm
  have hε := h 2
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ha, hb, one_mul,
    add_zero, plumbingMap_one_one, sub_right_inj, Complex.ofReal_inj] at hε
  have h' : -(2 * π * L') = -(2 * π * L) := Real.exp_injective (by linarith [hε])
  nlinarith [pi_pos]

/-- **The two compositions have different conformal types.** For neck lengths `L, L' ≥ 0` there is
no label-preserving holomorphic embedding of the composition `(x₁ x₂) x₃` into the composition
`x₁ (x₂ x₃)`: their cross ratios lie in `(0, 1/4]` and in `(1, 4/3]`. -/
theorem not_exists_isPuncturedEmbedding_plumbingMap_zero_one {L L' : ℝ} (hL : 0 ≤ L)
    (hL' : 0 ≤ L') :
    ¬∃ f, IsPuncturedEmbedding ![(0 : ℂ), zero.plumbingMap L 1, 1]
      ![(0 : ℂ), 1, one.plumbingMap L' 1] f := by
  rw [exists_isPuncturedEmbedding_iff_crossRatio_eq (by simp)]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, crossRatio_plumbingMap_zero,
    crossRatio_plumbingMap_one hL', OnePoint.coe_eq_coe, Complex.ofReal_inj]
  have hε : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have hε' : Real.exp (-(2 * π * L')) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have hpos' := Real.exp_pos (-(2 * π * L'))
  intro h
  have hone : 1 < (1 - Real.exp (-(2 * π * L')) / 4)⁻¹ :=
    one_lt_inv₀ (by linarith) |>.2 (by linarith)
  linarith

/-- **The two compositions have different conformal types.** For neck lengths `L, L' ≥ 0` there is
no label-preserving holomorphic embedding of the composition `x₁ (x₂ x₃)` into the composition
`(x₁ x₂) x₃`. -/
theorem not_exists_isPuncturedEmbedding_plumbingMap_one_zero {L L' : ℝ} (hL : 0 ≤ L)
    (hL' : 0 ≤ L') :
    ¬∃ f, IsPuncturedEmbedding ![(0 : ℂ), 1, one.plumbingMap L 1]
      ![(0 : ℂ), zero.plumbingMap L' 1, 1] f := fun h =>
  not_exists_isPuncturedEmbedding_plumbingMap_zero_one hL' hL (exists_isPuncturedEmbedding_comm.1 h)

/-- As the neck of the composition `(x₁ x₂) x₃` grows, its cross ratio tends to `0`. -/
theorem tendsto_crossRatio_plumbingMap_zero_atTop :
    Tendsto (fun L : ℝ => OnePoint.crossRatio ((0 : ℂ) : OnePoint ℂ) (1 : ℂ) ∞
      (zero.plumbingMap L 1)) atTop (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  have hε : Tendsto (fun L : ℝ => Real.exp (-(2 * π * L)) / 4) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π))).div_const 4
  simp only [crossRatio_plumbingMap_zero]
  exact (OnePoint.continuous_coe.tendsto 0).comp
    ((Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).comp hε)

/-- As the neck of the composition `x₁ (x₂ x₃)` grows, its cross ratio tends to `1`. -/
theorem tendsto_crossRatio_plumbingMap_one_atTop :
    Tendsto (fun L : ℝ => OnePoint.crossRatio ((0 : ℂ) : OnePoint ℂ) (one.plumbingMap L 1) ∞
      (1 : ℂ)) atTop (𝓝 ((1 : ℂ) : OnePoint ℂ)) := by
  have hε : Tendsto (fun L : ℝ => Real.exp (-(2 * π * L)) / 4) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π))).div_const 4
  have hinv : Tendsto (fun L : ℝ => (1 - Real.exp (-(2 * π * L)) / 4)⁻¹) atTop (𝓝 1) := by
    simpa using (hε.const_sub 1).inv₀ (by norm_num)
  refine ((OnePoint.continuous_coe.tendsto 1).comp
    ((Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).comp hinv)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  exact (crossRatio_plumbingMap_one hL).symm

end TauCeti.ThricePuncturedSphere
