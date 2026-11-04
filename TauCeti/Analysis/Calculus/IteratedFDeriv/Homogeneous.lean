/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Iterated derivatives of homogeneous maps

Let `f (x, ξ)` be a map on `E × F` that is `C^n` on `ξ ≠ 0` and positively homogeneous of degree
`m` in `ξ`, that is `f (x, t • ξ) = t ^ m • f (x, ξ)` for `t > 0` and `ξ ≠ 0`. Differentiating the
homogeneity relation shows that its derivatives in `j` directions in `x` and `l` directions in `ξ`
are homogeneous of degree `m - l` in `ξ`
(`TauCeti.iteratedFDeriv_append_smul_snd_of_smul_snd_eq`). When `F` is proper (for instance
finite-dimensional), the derivatives are bounded on the compact sets `K × {‖ξ‖ = 1}`, and rescaling
`ξ` to the unit sphere gives the estimate `≤ C ‖ξ‖ ^ (m - l)` for `x ∈ K` and `ξ ≠ 0`
(`TauCeti.exists_norm_iteratedFDeriv_append_le_of_smul_snd_eq`).

For a map `m` on a proper real normed space that is `C^N` away from the origin and homogeneous of
degree `0`, that is `m (t • ξ) = m ξ` for every `t > 0`, this gives the decay
`‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for `k ≤ N` (`TauCeti.exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq`).
This is Mihlin's condition for a Fourier multiplier symbol, so every symbol that is smooth away
from the origin and homogeneous of degree `0` is an `Lᵖ` multiplier for `1 < p < ∞`. The same
estimates for homogeneous symbols of any degree underlie the symbol classes of pseudodifferential
operators.

## Main results

* `TauCeti.iteratedFDeriv_smul_snd_of_smul_snd_eq`: homogeneity of the derivatives.
* `TauCeti.exists_norm_iteratedFDeriv_le_of_smul_snd_eq` and
  `TauCeti.exists_norm_iteratedFDeriv_append_le_of_smul_snd_eq`: the estimate
  `‖∂_x^j ∂_ξ^l f (x, ξ)‖ ≤ C ‖ξ‖ ^ (m - l)` for `x` in a compact set and `ξ ≠ 0`.
* `TauCeti.exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq`: Mihlin's condition for maps
  homogeneous of degree `0`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
* M. E. Taylor, *Pseudodifferential Operators*, Lecture I, (1.15)–(1.17).
-/

public section

open scoped NNReal
open Metric

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E × F → G} {m : ℝ}
  {n : WithTop ℕ∞}

/-- The derivatives of a map `f (x, ξ)` that is positively homogeneous of degree `m` in `ξ` are
homogeneous: rescaling `ξ` by `t > 0`, together with the `ξ`-components of the directions,
multiplies the derivative by `t ^ m`. -/
theorem iteratedFDeriv_smul_snd_of_smul_snd_eq (hf : ContDiffOn ℝ n f {p | p.2 ≠ 0})
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) {k : ℕ}
    (hk : k ≤ n) {x : E} {ξ : F} (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) (v : Fin k → E × F) :
    iteratedFDeriv ℝ k f (x, t • ξ) (fun i => ((v i).1, t • (v i).2)) =
      t ^ m • iteratedFDeriv ℝ k f (x, ξ) v := by
  set U : Set (E × F) := {p | p.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  let S : E × F →L[ℝ] E × F := (ContinuousLinearMap.id ℝ E).prodMap (t • ContinuousLinearMap.id ℝ F)
  have hSapply : ∀ p, S p = (p.1, t • p.2) := fun _ => rfl
  have hS : S ⁻¹' U = U := by
    ext p
    simp [U, hSapply, ht.ne']
  have hξ' : (x, ξ) ∈ U := hξ
  have hSξ : S (x, ξ) ∈ U := by
    rw [hSapply]
    exact smul_ne_zero ht.ne' hξ
  have hcomp : iteratedFDerivWithin ℝ k (f ∘ S) U (x, ξ) =
      iteratedFDerivWithin ℝ k (t ^ m • f) U (x, ξ) :=
    iteratedFDerivWithin_congr (fun p hp => hhom p.1 p.2 hp t ht) hξ' k
  have key := S.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    (by rw [hS]; exact hU.uniqueDiffOn) hSξ hk
  rw [hS, hcomp, iteratedFDerivWithin_of_isOpen k hU hξ', iteratedFDerivWithin_of_isOpen k hU hSξ,
    iteratedFDeriv_const_smul_apply ((hf.contDiffAt (hU.mem_nhds hξ')).of_le hk)] at key
  have := congr($key v)
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hSapply] at this
  exact this.symm

/-- The derivative of a map `f (x, ξ)` that is positively homogeneous of degree `m` in `ξ`, in
`j` directions in `x` and `l` directions in `ξ`, is homogeneous of degree `m - l` in `ξ`. -/
theorem iteratedFDeriv_append_smul_snd_of_smul_snd_eq (hf : ContDiffOn ℝ n f {p | p.2 ≠ 0})
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) {j l : ℕ}
    (hk : j + l ≤ n) {x : E} {ξ : F} (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) (u : Fin j → E)
    (w : Fin l → F) :
    iteratedFDeriv ℝ (j + l) f (x, t • ξ) (Fin.append (fun i => (u i, 0)) (fun i => (0, w i))) =
      t ^ (m - l) •
        iteratedFDeriv ℝ (j + l) f (x, ξ) (Fin.append (fun i => (u i, 0)) (fun i => (0, w i))) := by
  set D := iteratedFDeriv ℝ (j + l) f (x, t • ξ)
  set v : Fin (j + l) → E × F := Fin.append (fun i => (u i, 0)) (fun i => (0, w i))
  have hscale : (fun i => ((v i).1, t • (v i).2)) =
      fun i => (Fin.append (fun _ => (1 : ℝ)) (fun _ => t) i) • v i := by
    ext1 i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [v]
  have h := iteratedFDeriv_smul_snd_of_smul_snd_eq hf hhom (mod_cast hk) (x := x) hξ ht v
  rw [hscale, D.map_smul_univ, Fin.prod_univ_add] at h
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_mul] at h
  have htl : (t ^ l : ℝ) ≠ 0 := pow_ne_zero _ ht.ne'
  calc D v = (t ^ l)⁻¹ • (t ^ l • D v) := (inv_smul_smul₀ htl _).symm
    _ = t ^ (m - l) • iteratedFDeriv ℝ (j + l) f (x, ξ) v := by
      rw [h, smul_smul, inv_mul_eq_div, Real.rpow_sub ht, Real.rpow_natCast]

/-- Let `f (x, ξ)` be `C^n` on `ξ ≠ 0` and positively homogeneous of degree `m` in `ξ`, with `ξ`
in a proper space. For `x` in a compact set and `ξ ≠ 0`, its derivatives of order `k ≤ n` are
bounded by `C ‖ξ‖ ^ m`, once the `ξ`-components of the directions are rescaled by `‖ξ‖⁻¹`. -/
theorem exists_norm_iteratedFDeriv_le_of_smul_snd_eq [ProperSpace F] {K : Set E}
    (hK : IsCompact K) (hf : ContDiffOn ℝ n f {p | p.2 ≠ 0})
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) {k : ℕ}
    (hk : k ≤ n) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ∀ v : Fin k → E × F,
      ‖iteratedFDeriv ℝ k f (x, ξ) v‖ ≤ C * ‖ξ‖ ^ m * ∏ i, ‖((v i).1, ‖ξ‖⁻¹ • (v i).2)‖ := by
  have hU : IsOpen {p : E × F | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  -- The derivative is bounded on the compact set `K × sphere 0 1`.
  have hc : ContinuousOn (iteratedFDeriv ℝ k f) {p | p.2 ≠ 0} :=
    (hf.continuousOn_iteratedFDerivWithin hk hU.uniqueDiffOn).congr fun _ hp =>
      (iteratedFDerivWithin_of_isOpen k hU hp).symm
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere 0 1)).exists_bound_of_continuousOn
    (hc.mono fun p hp => ne_zero_of_mem_unit_sphere ⟨p.2, hp.2⟩)
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ hξ v => ?_⟩
  -- By homogeneity the derivative at `ξ` is `‖ξ‖ ^ m` times that at `θ = ‖ξ‖⁻¹ • ξ`.
  have hnξ : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set θ : F := ‖ξ‖⁻¹ • ξ
  have hθ : θ ≠ 0 := smul_ne_zero (inv_ne_zero hnξ.ne') hξ
  have hξθ : ξ = ‖ξ‖ • θ := by simp [θ, smul_smul, hnξ.ne']
  have hv : v = fun i => (((v i).1, ‖ξ‖⁻¹ • (v i).2).1, ‖ξ‖ • ((v i).1, ‖ξ‖⁻¹ • (v i).2).2) := by
    ext1 i
    simp [smul_smul, hnξ.ne']
  have hbound : ‖iteratedFDeriv ℝ k f (x, θ)‖ ≤ max C 0 :=
    (hC (x, θ) ⟨hx, by simp [θ, norm_smul, hnξ.ne']⟩).trans (le_max_left _ _)
  calc ‖iteratedFDeriv ℝ k f (x, ξ) v‖
      = ‖ξ‖ ^ m * ‖iteratedFDeriv ℝ k f (x, θ) fun i => ((v i).1, ‖ξ‖⁻¹ • (v i).2)‖ := by
        conv_lhs => rw [hξθ, hv]
        rw [iteratedFDeriv_smul_snd_of_smul_snd_eq hf hhom hk hθ hnξ, norm_smul,
          Real.norm_of_nonneg (Real.rpow_nonneg hnξ.le _)]
    _ ≤ ‖ξ‖ ^ m * (max C 0 * ∏ i, ‖((v i).1, ‖ξ‖⁻¹ • (v i).2)‖) := by
        gcongr
        exact ((iteratedFDeriv ℝ k f (x, θ)).le_opNorm _).trans (by gcongr)
    _ = max C 0 * ‖ξ‖ ^ m * ∏ i, ‖((v i).1, ‖ξ‖⁻¹ • (v i).2)‖ := by ring

/-- Let `f (x, ξ)` be `C^n` on `ξ ≠ 0` and positively homogeneous of degree `m` in `ξ`, with `ξ`
in a proper space. Its derivatives in `j` directions `u` in `x` and `l` directions `w` in `ξ`,
with `j + l ≤ n`, are bounded by `C ‖ξ‖ ^ (m - l) ∏ ‖u i‖ ∏ ‖w i‖` for `x` in a compact set and
`ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_append_le_of_smul_snd_eq [ProperSpace F] {K : Set E}
    (hK : IsCompact K) (hf : ContDiffOn ℝ n f {p | p.2 ≠ 0})
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) {j l : ℕ}
    (hk : j + l ≤ n) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ∀ (u : Fin j → E) (w : Fin l → F),
      ‖iteratedFDeriv ℝ (j + l) f (x, ξ) (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))‖ ≤
        C * ‖ξ‖ ^ (m - l) * (∏ i, ‖u i‖) * ∏ i, ‖w i‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_le_of_smul_snd_eq hK hf hhom (mod_cast hk)
  refine ⟨C, hC, fun x hx ξ hξ u w => (h x hx ξ hξ _).trans_eq ?_⟩
  have hprod : ∏ i, ‖((Fin.append (fun i => (u i, (0 : F))) (fun i => ((0 : E), w i)) i).1,
      ‖ξ‖⁻¹ • (Fin.append (fun i => (u i, (0 : F))) (fun i => ((0 : E), w i)) i).2)‖ =
      (∏ i, ‖u i‖) * (‖ξ‖⁻¹ ^ l * ∏ i, ‖w i‖) := by
    rw [Fin.prod_univ_add]
    simp [norm_smul, Finset.prod_mul_distrib, mul_nonneg]
  rw [hprod, Real.rpow_sub (norm_pos_iff.mpr hξ), Real.rpow_natCast, inv_pow]
  ring

/-- **Homogeneous maps of degree zero satisfy Mihlin's condition.** Let `m` be a map on a proper
(for instance finite-dimensional) real normed space that is `C^N` away from the origin and
homogeneous of degree `0`, that is `m (t • ξ) = m ξ` for every `t > 0`. Then there is a constant
`A` with `‖D^k m ξ‖ ≤ A / ‖ξ‖ ^ k` for every `k ≤ N` and every `ξ ≠ 0`. -/
theorem exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq {W G : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [ProperSpace W] [NormedAddCommGroup G] [NormedSpace ℝ G] {m : W → G}
    {N : ℕ} (hm : ContDiffOn ℝ N m {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ ξ, m (t • ξ) = m ξ) :
    ∃ A : ℝ≥0, ∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k := by
  -- Regard `m` as a map of `(x, ξ)` that does not depend on `x`, homogeneous of degree `0` in `ξ`.
  set P : W × W →L[ℝ] W := ContinuousLinearMap.snd ℝ W W
  have hU : IsOpen ({0}ᶜ : Set W) := isOpen_compl_singleton
  have hf : ContDiffOn ℝ N (m ∘ P) {p | p.2 ≠ 0} := hm.comp P.contDiff.contDiffOn fun _ hp => hp
  have hhom' : ∀ (x ξ : W), ξ ≠ 0 → ∀ t : ℝ, 0 < t →
      (m ∘ P) (x, t • ξ) = t ^ (0 : ℝ) • (m ∘ P) (x, ξ) := fun _ _ _ t ht => by
    simp [P, hhom t ht]
  have hbd : ∀ k ≤ N, ∃ C : ℝ, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ C / ‖ξ‖ ^ k := by
    intro k hk
    obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_le_of_smul_snd_eq (K := {0})
      isCompact_singleton hf hhom' (mod_cast hk)
    refine ⟨C, fun ξ hξ => ?_⟩
    rw [div_eq_mul_inv, ← inv_pow]
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
    -- The derivative of `m ∘ P` in the directions `(0, w i)` is the derivative of `m`.
    have key := P.iteratedFDerivWithin_comp_right hm hU.uniqueDiffOn
      (hU.preimage P.continuous).uniqueDiffOn (x := (0, ξ)) hξ (i := k) (mod_cast hk)
    rw [iteratedFDerivWithin_of_isOpen k (hU.preimage P.continuous) hξ,
      iteratedFDerivWithin_of_isOpen (x := P (0, ξ)) k hU hξ] at key
    have hD : iteratedFDeriv ℝ k (m ∘ P) (0, ξ) (fun i => (0, w i)) =
        iteratedFDeriv ℝ k m ξ w := by
      simpa [P] using congr($key fun i => ((0 : W), w i))
    refine (hD ▸ h 0 rfl ξ hξ fun i => (0, w i)).trans_eq ?_
    simp [norm_smul, Finset.prod_mul_distrib, mul_nonneg, mul_assoc]
  choose! C hC using hbd
  refine ⟨∑ k ∈ Finset.range (N + 1), (C k).toNNReal, fun k hk ξ hξ ↦ (hC k hk ξ hξ).trans ?_⟩
  rw [NNReal.coe_sum]
  refine div_le_div_of_nonneg_right ((Real.le_coe_toNNReal _).trans ?_) (by positivity)
  exact Finset.single_le_sum (f := fun k ↦ ((C k).toNNReal : ℝ)) (fun _ _ ↦ NNReal.coe_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

end TauCeti
