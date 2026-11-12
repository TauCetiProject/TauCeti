/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.ConstantTerm
import TauCeti.NumberTheory.ModularForms.Cusps.Residue
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.GammaSet
import TauCeti.Analysis.PSeries.RowSums

/-!
# The weight-two cusp–Eisenstein decomposition at level `Γ(N)`

In weight `k ≥ 3` the primitive residue-class Eisenstein series span a complement of the cusp
forms in `M_k(Γ(N))`
(`TauCeti.EisensteinSeries.isCompl_primitiveEisensteinSubspace_cuspFormSubmodule`). In weight
two these series do not converge, and their role is played by the weighted series `G₂^W`
(`TauCeti.EisensteinSeries.weightedG2MF`) for weights `W` on residue pairs modulo `N` that are
supported on the residues of coprime integer pairs and have total mass zero
(`TauCeti.EisensteinSeries.primitiveG2Weights`). This file proves that these series span a
complement of `S₂(Γ(N))` in `M₂(Γ(N))`.

The constant term of `G₂^W` at the cusp represented by `γ`, whose inverse has bottom row `r`
modulo `N`, is `∑_{n ∈ ℤ} W(n r) n⁻² - N⁻² (∑_x W(x)) · 2 ζ(2)`. On even weights supported on
the residues of coprime pairs, the row-sum operator `W ↦ (r ↦ ∑_n W(n r) n⁻²)` is injective: its
diagonal coefficient `2` dominates `∑_{|n| ≥ 2} n⁻² = π² / 3 - 2`
(`TauCeti.eq_zero_of_forall_tsum_zsmul_mul_zpow_neg_two_eq_zero`). Being an endomorphism of a
finite-dimensional space, it is then bijective.

* *Spanning.* The constant terms of `f ∈ M₂(Γ(N))` form such an even weight, the row sums of
  some even weight `W`. Then `f - G₂^W` has the same constant term `N⁻² (∑_x W(x)) · 2 ζ(2)` at
  every cusp. By the weight-two residue relation this common value is zero, so `f - G₂^W` is a
  cusp form and `W` has mass zero.
* *Directness.* If `G₂^W` is cuspidal, the row sums of the even part of `W` vanish, so the even
  part is zero; since `G₂^W` only depends on the even part of `W`, it is zero.

## Main definitions

* `TauCeti.EisensteinSeries.primitiveG2Weights`: the weights supported on the residues of
  coprime integer pairs, of total mass zero.
* `TauCeti.EisensteinSeries.primitiveG2Subspace`: the subspace of `M₂(Γ(N))` of the series `G₂^W`
  with such weights.

## Main results

* `TauCeti.EisensteinSeries.comp_vecMul_mem_primitiveG2Weights`: right multiplication of the
  residues by `SL(2, ℤ)` preserves the primitive weights.
* `TauCeti.EisensteinSeries.disjoint_primitiveG2Subspace_cuspFormSubmodule`: the subspace meets
  the cusp forms only in `0`.
* `TauCeti.EisensteinSeries.sup_primitiveG2Subspace_cuspFormSubmodule_eq_top`: together with the
  cusp forms it spans `M₂(Γ(N))`.
* `TauCeti.EisensteinSeries.isCompl_primitiveG2Subspace_cuspFormSubmodule`: the cusp–Eisenstein
  decomposition `M₂(Γ(N)) = E₂(Γ(N)) ⊕ S₂(Γ(N))`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2 and
  §4.6, where the weight-two Eisenstein space of `Γ(N)` is constructed by Hecke's trick and its
  dimension is obtained from the dimension formulas instead.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

/-! ### The primitive weight-two Eisenstein subspace -/

variable {N : ℕ} [NeZero N]

variable (N) in
/-- The weights of the primitive weight-two Eisenstein series: the functions `W` on residue
pairs modulo `N` supported on the residues of coprime integer pairs (those `a` with
`gammaSet N 1 a` nonempty), with total mass `∑_a W(a) = 0`. -/
def primitiveG2Weights : Submodule ℂ ((Fin 2 → ZMod N) → ℂ) where
  carrier := {W | (∀ a, W a ≠ 0 → Nonempty (gammaSet N 1 a)) ∧ ∑ a, W a = 0}
  add_mem' {W W'} hW hW' := by
    refine ⟨fun a ha ↦ ?_, by simp [Finset.sum_add_distrib, hW.2, hW'.2]⟩
    by_cases h : W a = 0
    · exact hW'.1 a (by simpa [h] using ha)
    · exact hW.1 a h
  zero_mem' := ⟨fun a ha ↦ (ha rfl).elim, by simp⟩
  smul_mem' c W hW := ⟨fun a ha ↦ hW.1 a (right_ne_zero_of_mul ha), by
    simp [← Finset.mul_sum, hW.2]⟩

/-- Membership in `primitiveG2Weights`: support on the residues of coprime pairs and mass
zero. -/
theorem mem_primitiveG2Weights_iff {W : (Fin 2 → ZMod N) → ℂ} :
    W ∈ primitiveG2Weights N ↔
      (∀ a, W a ≠ 0 → Nonempty (gammaSet N 1 a)) ∧ ∑ a, W a = 0 := Iff.rfl

/-- Right multiplication of the residues by `γ ∈ SL(2, ℤ)` preserves the primitive weight-two
weights: it permutes the residues of coprime pairs and does not change the total mass. -/
theorem comp_vecMul_mem_primitiveG2Weights {W : (Fin 2 → ZMod N) → ℂ}
    (hW : W ∈ primitiveG2Weights N) (γ : SL(2, ℤ)) :
    (fun a ↦ W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) ∈
      primitiveG2Weights N := by
  obtain ⟨hsupp, hmass⟩ := mem_primitiveG2Weights_iff.mp hW
  refine mem_primitiveG2Weights_iff.mpr ⟨fun a ha ↦ ?_, (sum_comp_vecMul W _).trans hmass⟩
  obtain ⟨x⟩ := hsupp _ ha
  have hinv : (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = a := by
    rw [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  exact ⟨hinv ▸ gammaSetEquiv _ γ⁻¹ x⟩

/-! ### The row-sum operator on even weights -/

variable (N) in
/-- Even weights supported on the residues of coprime integer pairs. -/
private def evenPrimitiveWeights : Submodule ℂ ((Fin 2 → ZMod N) → ℂ) where
  carrier := {W | (∀ a, W (-a) = W a) ∧ ∀ a, W a ≠ 0 → Nonempty (gammaSet N 1 a)}
  add_mem' {W W'} hW hW' := by
    refine ⟨fun a ↦ by simp [hW.1, hW'.1], fun a ha ↦ ?_⟩
    by_cases h : W a = 0
    · exact hW'.2 a (by simpa [h] using ha)
    · exact hW.2 a h
  zero_mem' := ⟨fun _ ↦ rfl, fun a ha ↦ (ha rfl).elim⟩
  smul_mem' c W hW := ⟨fun a ↦ by simp [hW.1], fun a ha ↦ hW.2 a (right_ne_zero_of_mul ha)⟩

variable (N) in
/-- The row sums `a ↦ ∑ₙ W(n a) n⁻²` at the residues of coprime pairs, extended by zero. -/
private def rowSums : ((Fin 2 → ZMod N) → ℂ) →ₗ[ℂ] ((Fin 2 → ZMod N) → ℂ) where
  toFun W := {a | Nonempty (gammaSet N 1 a)}.indicator fun a ↦
    ∑' n : ℤ, W (n • a) * (n : ℂ) ^ (-2 : ℤ)
  map_add' W W' := by
    classical
    ext a
    simp only [Set.indicator_apply, Pi.add_apply]
    split_ifs
    · rw [← (summable_zsmul_mul_zpow_neg_two W a).tsum_add (summable_zsmul_mul_zpow_neg_two W' a)]
      simp [add_mul]
    · simp
  map_smul' c W := by
    classical
    ext a
    simp only [Set.indicator_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rw [← tsum_mul_left]
      simp [mul_assoc]
    · simp

private lemma rowSums_apply_of_nonempty (W : (Fin 2 → ZMod N) → ℂ) {a : Fin 2 → ZMod N}
    (ha : Nonempty (gammaSet N 1 a)) :
    rowSums N W a = ∑' n : ℤ, W (n • a) * (n : ℂ) ^ (-2 : ℤ) := by
  simp only [rowSums, LinearMap.coe_mk, AddHom.coe_mk]
  exact Set.indicator_of_mem (s := {a | Nonempty (gammaSet N 1 a)}) ha _

private lemma rowSums_apply_of_isEmpty (W : (Fin 2 → ZMod N) → ℂ) {a : Fin 2 → ZMod N}
    (ha : ¬Nonempty (gammaSet N 1 a)) : rowSums N W a = 0 := by
  simp only [rowSums, LinearMap.coe_mk, AddHom.coe_mk]
  exact Set.indicator_of_notMem (s := {a | Nonempty (gammaSet N 1 a)}) ha _

private lemma rowSums_mem_evenPrimitiveWeights (W : (Fin 2 → ZMod N) → ℂ) :
    rowSums N W ∈ evenPrimitiveWeights N := by
  refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
  · by_cases h : Nonempty (gammaSet N 1 a)
    · rw [rowSums_apply_of_nonempty W h,
        rowSums_apply_of_nonempty W ((nonempty_gammaSet_neg_iff a).mpr h)]
      rw [← (Equiv.neg ℤ).tsum_eq]
      simp [neg_smul, smul_neg]
    · have h' : ¬Nonempty (gammaSet N 1 (-a)) := (nonempty_gammaSet_neg_iff a).not.mpr h
      rw [rowSums_apply_of_isEmpty W h, rowSums_apply_of_isEmpty W h']
  · by_contra h
    exact ha (rowSums_apply_of_isEmpty W h)

/-- Every even weight supported on primitive residues is the row sum of such a weight. -/
private lemma exists_rowSums_eq {c : (Fin 2 → ZMod N) → ℂ} (hc : c ∈ evenPrimitiveWeights N) :
    ∃ W ∈ evenPrimitiveWeights N, rowSums N W = c := by
  let R := (rowSums N).restrict (p := evenPrimitiveWeights N) (q := evenPrimitiveWeights N)
    fun W _ ↦ rowSums_mem_evenPrimitiveWeights W
  have hinj : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro W hW
    have hW0 : (W : (Fin 2 → ZMod N) → ℂ) = 0 := by
      refine eq_zero_of_forall_tsum_zsmul_mul_zpow_neg_two_eq_zero W.2.1 fun a ha ↦ ?_
      have h := congrFun (congrArg Subtype.val (LinearMap.mem_ker.mp hW)) a
      rwa [LinearMap.coe_restrict_apply, rowSums_apply_of_nonempty _ (W.2.2 a ha)] at h
    exact Subtype.ext hW0
  obtain ⟨W, hW⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨c, hc⟩
  exact ⟨W, W.2, congrArg Subtype.val hW⟩

/-! ### The decomposition -/

/-- The constant term of `G₂^W` at `γ`, in terms of the bottom row of `γ⁻¹` modulo `N`. -/
private lemma constantTermAt_weightedG2MF_eq (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    constantTermAt γ (weightedG2MF W) =
      ∑' n : ℤ, W (n • ((![0, 1] : Fin 2 → ZMod N) ᵥ* (γ⁻¹ : SL(2, ℤ)))) *
          (n : ℂ) ^ (-2 : ℤ) -
        ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2) := by
  simp only [constantTermAt_weightedG2MF, intCast_comp_vecCons_eq_zsmul_vecMul_inv]

variable (N) in
/-- The primitive weight-two Eisenstein subspace of `M₂(Γ(N))`: the series `G₂^W` for the weights
`W ∈ primitiveG2Weights N`. It is the weight-two counterpart of the span of the primitive
residue-class Eisenstein series in weight `k ≥ 3`, and a complement of the cusp forms
(`isCompl_primitiveG2Subspace_cuspFormSubmodule`). -/
def primitiveG2Subspace : Submodule ℂ (ModularForm Γ(N) 2) :=
  (primitiveG2Weights N).map weightedG2MFₗ

/-- The forms in the primitive weight-two Eisenstein subspace are the series `G₂^W` with
`W ∈ primitiveG2Weights N`. -/
theorem mem_primitiveG2Subspace_iff {f : ModularForm Γ(N) 2} :
    f ∈ primitiveG2Subspace N ↔ ∃ W ∈ primitiveG2Weights N, weightedG2MF W = f := by
  simp only [primitiveG2Subspace, Submodule.mem_map, weightedG2MFₗ_apply]

/-- A subspace containing the series `G₂^W` for all `W ∈ primitiveG2Weights N` contains the
primitive weight-two Eisenstein subspace. -/
theorem primitiveG2Subspace_le {V : Submodule ℂ (ModularForm Γ(N) 2)}
    (hV : ∀ W ∈ primitiveG2Weights N, weightedG2MF W ∈ V) : primitiveG2Subspace N ≤ V :=
  Submodule.map_le_iff_le_comap.mpr fun W hW ↦ by
    simpa only [Submodule.mem_comap, weightedG2MFₗ_apply] using hV W hW

/-- The primitive weight-two Eisenstein subspace and the cusp forms of weight two and level
`Γ(N)` have zero intersection. -/
theorem disjoint_primitiveG2Subspace_cuspFormSubmodule :
    Disjoint (primitiveG2Subspace N) (cuspFormSubmodule Γ(N) 2) := by
  rw [Submodule.disjoint_def]
  rintro _ hf hcusp
  obtain ⟨W, hW, rfl⟩ := mem_primitiveG2Subspace_iff.mp hf
  -- the even part `W' = W + W ∘ neg` has the same series, up to the factor `2`
  let W' : (Fin 2 → ZMod N) → ℂ := W + fun a ↦ W (-a)
  have hG : weightedG2MF W' = (2 : ℂ) • weightedG2MF W := by
    rw [weightedG2MF_add, two_smul]
    congr 1
    ext z
    simp [weightedG2_comp_neg]
  have hneg : ∑ a, W (-a) = ∑ a, W a := Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl
  have hmass : ∑ a, W' a = 0 := by
    simp only [W', Pi.add_apply, Finset.sum_add_distrib, hneg, hW.2, add_zero]
  have hcusp' : weightedG2MF W' ∈ cuspFormSubmodule Γ(N) 2 := hG ▸ Submodule.smul_mem _ _ hcusp
  have hW' : W' = 0 := by
    refine eq_zero_of_forall_tsum_zsmul_mul_zpow_neg_two_eq_zero (fun a ↦ by simp [W', add_comm])
      fun a ha ↦ ?_
    have hP : Nonempty (gammaSet N 1 a) := by
      by_cases h : W a = 0
      · exact (nonempty_gammaSet_neg_iff a).mp (hW.1 _ (by simpa [W', h] using ha))
      · exact hW.1 a h
    obtain ⟨γ, rfl⟩ := (nonempty_gammaSet_iff a).mp hP
    have h0 := (mem_cuspFormSubmodule_iff_constantTermAt_eq_zero _).mp hcusp' γ
    rwa [constantTermAt_weightedG2MF_eq, hmass, mul_zero, zero_mul, sub_zero] at h0
  have h2 : (2 : ℂ) • weightedG2MF W = 0 := by rw [← hG, hW', weightedG2MF_zero]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Every modular form of weight two and level `Γ(N)` is the sum of a series `G₂^W` with
`W ∈ primitiveG2Weights N` and a cusp form. -/
theorem sup_primitiveG2Subspace_cuspFormSubmodule_eq_top :
    primitiveG2Subspace N ⊔ cuspFormSubmodule Γ(N) 2 = ⊤ := by
  classical
  refine eq_top_iff.mpr fun f _ ↦ ?_
  -- the constant terms of `f`, read as a function of the residue of the cusp
  let c : (Fin 2 → ZMod N) → ℂ := fun a ↦
    if h : ∃ γ : SL(2, ℤ),
        ((![0, 1] : Fin 2 → ZMod N) ᵥ* (γ⁻¹ : SL(2, ℤ)) : Fin 2 → ZMod N) = a then
      constantTermAt h.choose f
    else 0
  have hc (γ : SL(2, ℤ)) : c (![0, 1] ᵥ* (γ⁻¹ : SL(2, ℤ))) = constantTermAt γ f := by
    have h : ∃ δ : SL(2, ℤ), ((![0, 1] : Fin 2 → ZMod N) ᵥ* (δ⁻¹ : SL(2, ℤ)) :
        Fin 2 → ZMod N) = ![0, 1] ᵥ* (γ⁻¹ : SL(2, ℤ)) := ⟨γ, rfl⟩
    simp only [c, h, ↓reduceDIte]
    rw [constantTermAt_eq_of_vecMul_inv_eq le_rfl h.choose_spec]
  have hcE : c ∈ evenPrimitiveWeights N := by
    refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
    · by_cases h : ∃ γ : SL(2, ℤ),
          ((![0, 1] : Fin 2 → ZMod N) ᵥ* (γ⁻¹ : SL(2, ℤ)) : Fin 2 → ZMod N) = a
      · obtain ⟨γ, rfl⟩ := h
        rw [neg_vecMul_inv, hc, hc, constantTermAt_neg]
        norm_num
      · have h' : ¬∃ γ : SL(2, ℤ),
            ((![0, 1] : Fin 2 → ZMod N) ᵥ* (γ⁻¹ : SL(2, ℤ)) : Fin 2 → ZMod N) = -a := by
          rintro ⟨γ, hγ⟩
          exact h ⟨-γ, by rw [← neg_vecMul_inv, hγ, neg_neg]⟩
        simp only [c, h, h', ↓reduceDIte]
    · refine (nonempty_gammaSet_iff a).mpr ?_
      by_contra h
      exact ha (by simp only [c, h, ↓reduceDIte])
  obtain ⟨W, hW, hWc⟩ := exists_rowSums_eq hcE
  -- `f - G₂^W` has the same constant term at every cusp, so it is cuspidal
  have hconst (γ : SL(2, ℤ)) : constantTermAt γ (f - weightedG2MF W) =
      ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2) := by
    have hrow := congrFun hWc (![0, 1] ᵥ* (γ⁻¹ : SL(2, ℤ)))
    rw [rowSums_apply_of_nonempty _ ((nonempty_gammaSet_iff _).mpr ⟨γ, rfl⟩), hc] at hrow
    rw [map_sub, constantTermAt_weightedG2MF_eq, hrow, sub_sub_cancel]
  have hzero := TauCeti.ModularForm.weight_two_eq_zero_of_forall_constantTermAt_eq hconst
  have hmass : ∑ a, W a = 0 := by
    have hN : ((N : ℂ) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 (NeZero.ne _))
    have hζ : 2 * riemannZeta 2 ≠ 0 := by
      rw [riemannZeta_two]
      exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero 2 (by exact_mod_cast
        Real.pi_ne_zero)) (by norm_num))
    simpa [hN, hζ] using hzero
  have hcusp : f - weightedG2MF W ∈ cuspFormSubmodule Γ(N) 2 :=
    (mem_cuspFormSubmodule_iff_constantTermAt_eq_zero _).mpr fun γ ↦ (hconst γ).trans hzero
  simpa using Submodule.add_mem_sup
    (mem_primitiveG2Subspace_iff.mpr ⟨W, ⟨hW.2, hmass⟩, rfl⟩) hcusp

/-- **The weight-two cusp–Eisenstein decomposition at level `Γ(N)`**: the primitive weight-two
Eisenstein subspace is a complement of the cusp forms in `M₂(Γ(N))`. -/
theorem isCompl_primitiveG2Subspace_cuspFormSubmodule :
    IsCompl (primitiveG2Subspace N) (cuspFormSubmodule Γ(N) 2) :=
  ⟨disjoint_primitiveG2Subspace_cuspFormSubmodule,
    codisjoint_iff.mpr sup_primitiveG2Subspace_cuspFormSubmodule_eq_top⟩

end TauCeti.EisensteinSeries
