/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Compact
import TauCeti.Topology.MetricSpace.Lipschitz.Basic

/-!
# Extremal sectional curvatures on algebraic curvature tensors

`sectionalMin r` and `sectionalMax r` are the infimum and supremum of `r ![u, v, u, v]` over
orthonormal two-frames (`0` if none exist); both are `1`-Lipschitz, `O(V)`-invariant, and attained
in finite dimension `≥ 2`. For algebraic curvature tensors, Gram–Schmidt gives
`r ![u, v, u, v] = det(Gram(u, v)) * r ![e₀, e₁, e₀, e₁]` and global Gram-determinant bounds.

## Main definitions & statements

* `sectionalMin`, `sectionalMax`, `lipschitzWith_sectionalMin`, `lipschitzWith_sectionalMax`,
  `IsAlgebraicCurvature.exists_orthonormal_apply_self_eq_det_gram_mul`,
  `IsAlgebraicCurvature.sectionalMin_mul_det_gram_le_and_le_sectionalMax`,
  `exists_orthonormal_eq_sectionalMin`, `exists_orthonormal_eq_sectionalMax`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

open Set
open scoped InnerProductSpace NNReal Pointwise

noncomputable section

namespace TauCeti.FourTensor

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Infimum of `r ![u 0, u 1, u 0, u 1]` over orthonormal two-frames in `V` (`0` if none exist). -/
def sectionalMin (r : FourTensor V) : ℝ :=
  sInf ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u})

/-- Supremum of `r ![u 0, u 1, u 0, u 1]` over orthonormal two-frames in `V` (`0` if none exist). -/
def sectionalMax (r : FourTensor V) : ℝ :=
  sSup ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u})

/-- Defining formula for `sectionalMin`. -/
theorem sectionalMin_def (r : FourTensor V) : sectionalMin r = sInf
    ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u}) := (rfl)

/-- Defining formula for `sectionalMax`. -/
theorem sectionalMax_def (r : FourTensor V) : sectionalMax r = sSup
    ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u}) := (rfl)

/-- Negation duality between `sectionalMin` and `sectionalMax`. -/
@[simp]
theorem sectionalMin_neg (r : FourTensor V) : sectionalMin (-r) = -sectionalMax r := by
  rw [sectionalMin_def, sectionalMax_def, ← Real.sInf_neg]; congr 1; ext; simp [neg_eq_iff_eq_neg]

/-- `sectionalMax` of `-r` is `-sectionalMin r`. -/
@[simp]
theorem sectionalMax_neg (r : FourTensor V) : sectionalMax (-r) = -sectionalMin r := by
  simpa using (neg_inj.2 (sectionalMin_neg (-r))).symm

private theorem bddBelow_sectionalImage (r : FourTensor V) :
    BddBelow ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u}) :=
  ⟨-‖r‖, fun _ ⟨_, hu, h⟩ ↦ h ▸ neg_le_of_abs_le
    (abs_apply_le_norm_of_norm_eq_one r (hu.1 0) (hu.1 1) (hu.1 0) (hu.1 1))⟩

private theorem bddAbove_sectionalImage (r : FourTensor V) :
    BddAbove ((fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1]) '' {u : Fin 2 → V | Orthonormal ℝ u}) :=
  ⟨‖r‖, fun _ ⟨_, hu, h⟩ ↦ h ▸ (le_abs_self _).trans
    (abs_apply_le_norm_of_norm_eq_one r (hu.1 0) (hu.1 1) (hu.1 0) (hu.1 1))⟩

/-- `sectionalMin r` bounds `r ![u, v, u, v]` below on every orthonormal pair `(u, v)`. -/
theorem sectionalMin_le_of_orthonormal (r : FourTensor V) {u v : V}
    (huv : Orthonormal ℝ ![u, v]) : sectionalMin r ≤ r ![u, v, u, v] :=
  csInf_le (bddBelow_sectionalImage r) ⟨![u, v], huv, rfl⟩

/-- `sectionalMax r` bounds `r ![u, v, u, v]` above on every orthonormal pair `(u, v)`. -/
theorem le_sectionalMax_of_orthonormal (r : FourTensor V) {u v : V}
    (huv : Orthonormal ℝ ![u, v]) : r ![u, v, u, v] ≤ sectionalMax r :=
  le_csSup (bddAbove_sectionalImage r) ⟨![u, v], huv, rfl⟩

/-- `sectionalMin r ≤ sectionalMax r` for every four-tensor `r`. -/
theorem sectionalMin_le_sectionalMax (r : FourTensor V) : sectionalMin r ≤ sectionalMax r := by
  rcases {u : Fin 2 → V | Orthonormal ℝ u}.eq_empty_or_nonempty with h | ⟨u, hu⟩
  · simp [sectionalMin_def, sectionalMax_def, h]
  · exact (csInf_le (bddBelow_sectionalImage r) ⟨u, hu, rfl⟩).trans
      (le_csSup (bddAbove_sectionalImage r) ⟨u, hu, rfl⟩)

/-- A lower bound on all orthonormal pairs bounds `sectionalMin r` below when frames exist. -/
theorem le_sectionalMin_of_forall_le {r : FourTensor V} {c : ℝ}
    (hne : {u : Fin 2 → V | Orthonormal ℝ u}.Nonempty)
    (hc : ∀ u v : V, Orthonormal ℝ ![u, v] → c ≤ r ![u, v, u, v]) : c ≤ sectionalMin r := by
  obtain ⟨u₀, hu₀⟩ := hne
  exact le_csInf ⟨_, ⟨u₀, hu₀, rfl⟩⟩ fun _ ⟨u, hu, h⟩ ↦ h ▸ hc (u 0) (u 1) (hu.pair zero_ne_one)

/-- An upper bound on all orthonormal pairs bounds `sectionalMax r` above when frames exist. -/
theorem sectionalMax_le_of_forall_le {r : FourTensor V} {c : ℝ}
    (hne : {u : Fin 2 → V | Orthonormal ℝ u}.Nonempty)
    (hc : ∀ u v : V, Orthonormal ℝ ![u, v] → r ![u, v, u, v] ≤ c) : sectionalMax r ≤ c := by
  have h := le_sectionalMin_of_forall_le (r := -r) (c := -c) hne fun u v huv ↦ by
    simpa using neg_le_neg (hc u v huv)
  rwa [sectionalMin_neg, neg_le_neg_iff] at h

/-- `sectionalMin` is `1`-Lipschitz on `FourTensor V`. -/
theorem lipschitzWith_sectionalMin : LipschitzWith 1 (sectionalMin (V := V)) :=
  TauCeti.lipschitzWith_sInf_image bddBelow_sectionalImage fun u hu ↦
    LipschitzWith.of_dist_le_mul fun r q ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, ← sub_apply] using
        abs_apply_le_norm_of_norm_eq_one (r - q) (hu.1 0) (hu.1 1) (hu.1 0) (hu.1 1)

/-- `sectionalMax` is `1`-Lipschitz on `FourTensor V`. -/
theorem lipschitzWith_sectionalMax : LipschitzWith 1 (sectionalMax (V := V)) :=
  LipschitzWith.of_dist_le_mul fun r q ↦ by
    simpa only [sectionalMin_neg, dist_neg_neg, NNReal.coe_one, one_mul] using
      lipschitzWith_sectionalMin.dist_le_mul (-r) (-q)

/-- `sectionalMin` is continuous on `FourTensor V`. -/
theorem continuous_sectionalMin : Continuous (sectionalMin (V := V)) :=
  lipschitzWith_sectionalMin.continuous

/-- `sectionalMax` is continuous on `FourTensor V`. -/
theorem continuous_sectionalMax : Continuous (sectionalMax (V := V)) :=
  lipschitzWith_sectionalMax.continuous

/-- `sectionalMin` is invariant under pullback by linear isometric equivalences. -/
@[simp]
theorem sectionalMin_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    sectionalMin (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) = sectionalMin r := by
  rw [sectionalMin_def, sectionalMin_def]; congr 1; ext y; constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨e ∘ u, e.toLinearIsometry.orthonormal_comp_iff.2 hu,
      (compContinuousLinearMap_apply_vec r (e : W →L[ℝ] V) (u 0) (u 1) (u 0) (u 1)).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨e.symm ∘ u, e.symm.toLinearIsometry.orthonormal_comp_iff.2 hu, by
      dsimp only; rw [compContinuousLinearMap_apply_vec]; simp⟩

/-- `sectionalMax` is invariant under pullback by linear isometric equivalences. -/
@[simp]
theorem sectionalMax_compContinuousLinearMap_linearIsometryEquiv {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) :
    sectionalMax (r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) = sectionalMax r := by
  have h := sectionalMin_compContinuousLinearMap_linearIsometryEquiv e (-r)
  have hneg : (-r).compContinuousLinearMap (fun _ ↦ (e : W →L[ℝ] V)) =
      -(r.compContinuousLinearMap fun _ ↦ (e : W →L[ℝ] V)) := by ext m; rfl
  rwa [hneg, sectionalMin_neg, sectionalMin_neg, neg_inj] at h

/-- Gram–Schmidt normalization of a linearly independent pair `(u, v)` into an orthonormal pair
`(e₀, e₁)` in `span {u, v}` with `r ![u, v, u, v] = det(Gram(u, v)) * r ![e₀, e₁, e₀, e₁]`. -/
theorem IsAlgebraicCurvature.exists_orthonormal_apply_self_eq_det_gram_mul {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {u v : V} (huv : LinearIndependent ℝ ![u, v]) :
    ∃ e₀ e₁ : V, Orthonormal ℝ ![e₀, e₁] ∧
      e₀ ∈ Submodule.span ℝ {u, v} ∧ e₁ ∈ Submodule.span ℝ {u, v} ∧
      r ![u, v, u, v] = (Matrix.gram ℝ ![u, v]).det * r ![e₀, e₁, e₀, e₁] := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 (huv.ne_zero 0)
  set e₀ : V := ‖u‖⁻¹ • u; set w : V := v - ⟪e₀, v⟫_ℝ • e₀
  have he₀ : ‖e₀‖ = 1 := by simp [e₀, norm_smul, hnu.ne']
  have he₀w : ⟪e₀, w⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he₀]; ring
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 fun hw ↦
    (LinearIndependent.pair_iff' (huv.ne_zero 0)).1 huv (⟪e₀, v⟫_ℝ * ‖u‖⁻¹)
      (by rw [Matrix.cons_val_zero, mul_smul, ← sub_eq_zero.1 hw])
  set e₁ : V := ‖w‖⁻¹ • w
  have he₁ : ‖e₁‖ = 1 := by simp [e₁, norm_smul, hnw.ne']
  have he₀e₁ : ⟪e₀, e₁⟫_ℝ = 0 := by simp [e₁, real_inner_smul_right, he₀w]
  have hu_eq : u = ‖u‖ • e₀ := by simp [e₀, smul_smul, hnu.ne']
  have hv_eq : v = ⟪e₀, v⟫_ℝ • e₀ + ‖w‖ • e₁ := by simp [e₁, smul_smul, hnw.ne', w]
  have hgram : (Matrix.gram ℝ ![u, v]).det = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_lhs => rw [hu_eq, hv_eq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq, real_inner_comm e₀ e₁, he₀, he₁, he₀e₁]; ring
  have hr_eq : r ![u, v, u, v] = ‖u‖ ^ 2 * ‖w‖ ^ 2 * r ![e₀, e₁, e₀, e₁] := by
    have h1 (a c d : V) : r ![a, a, c, d] = 0 := by linarith [hr.antisymm_first a a c d]
    have h2 (a b c : V) : r ![a, b, c, c] = 0 := by linarith [hr.antisymm_last a b c c]
    conv_lhs => rw [hu_eq, hv_eq]
    simp only [r.apply_add_second, r.apply_add_fourth, r.apply_smul_first, r.apply_smul_second,
      r.apply_smul_third, r.apply_smul_fourth, h1, h2]; ring
  have he₀_mem : e₀ ∈ Submodule.span ℝ {u, v} :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact ⟨e₀, e₁, by simp [orthonormal_vecCons_iff, he₀, he₁, he₀e₁], he₀_mem,
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ he₀_mem)), by rw [hgram, hr_eq]⟩

/-- For an algebraic curvature tensor `r`, `sectionalMin r` and `sectionalMax r` bound every
sectional numerator `r ![u, v, u, v]` against `det(Gram(u, v))`. -/
theorem IsAlgebraicCurvature.sectionalMin_mul_det_gram_le_and_le_sectionalMax {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (u v : V) :
    sectionalMin r * (Matrix.gram ℝ ![u, v]).det ≤ r ![u, v, u, v] ∧
      r ![u, v, u, v] ≤ sectionalMax r * (Matrix.gram ℝ ![u, v]).det := by
  by_cases huv : LinearIndependent ℝ ![u, v]
  · obtain ⟨e₀, e₁, horth, -, -, heq⟩ := hr.exists_orthonormal_apply_self_eq_det_gram_mul huv
    have hdet := (Matrix.posDef_gram_of_linearIndependent huv).det_pos.le
    rw [heq, mul_comm (Matrix.gram ℝ ![u, v]).det]
    exact ⟨mul_le_mul_of_nonneg_right (sectionalMin_le_of_orthonormal r horth) hdet,
      mul_le_mul_of_nonneg_right (le_sectionalMax_of_orthonormal r horth) hdet⟩
  · have hdet : (Matrix.gram ℝ ![u, v]).det = 0 :=
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr huv)
    simp [hdet, hr.apply_self_eq_zero_of_not_linearIndependent huv]

end InnerProductSpace

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- In dimension at least two, `sectionalMin r` is attained at an orthonormal pair `(u, v)`. -/
theorem exists_orthonormal_eq_sectionalMin (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ∃ u v : V, Orthonormal ℝ ![u, v] ∧ r ![u, v, u, v] = sectionalMin r := by
  have hKne : {u : Fin 2 → V | Orthonormal ℝ u}.Nonempty :=
    (TauCeti.nonempty_setOfPred_orthonormal_iff (ι := Fin 2) (E := V)).2 (by simpa using hn)
  have hcont : Continuous fun u : Fin 2 → V ↦ r ![u 0, u 1, u 0, u 1] :=
    r.cont.comp (continuous_pi fun k ↦ by fin_cases k <;> exact continuous_apply _)
  obtain ⟨u, hu, hmin⟩ :=
    TauCeti.isCompact_setOfPred_orthonormal.exists_isMinOn hKne hcont.continuousOn
  have hu' : Orthonormal ℝ ![u 0, u 1] := hu.pair zero_ne_one
  exact ⟨u 0, u 1, hu', le_antisymm
    (le_sectionalMin_of_forall_le hKne fun w z hwz ↦ isMinOn_iff.1 hmin ![w, z] hwz)
    (sectionalMin_le_of_orthonormal r hu')⟩

/-- In dimension at least two, `sectionalMax r` is attained at an orthonormal pair `(u, v)`. -/
theorem exists_orthonormal_eq_sectionalMax (hn : 2 ≤ Module.finrank ℝ V) (r : FourTensor V) :
    ∃ u v : V, Orthonormal ℝ ![u, v] ∧ r ![u, v, u, v] = sectionalMax r := by
  obtain ⟨u, v, huv, heq⟩ := exists_orthonormal_eq_sectionalMin hn (-r)
  exact ⟨u, v, huv, by simpa using neg_inj.2 heq⟩

end FiniteDimensional

end TauCeti.FourTensor
