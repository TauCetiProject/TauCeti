/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Dual
public import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.Normed.Lp.MapCLM
import Mathlib.Topology.Order.IsLUB

/-!
# Duality for dependent ℓᵖ sums

For Hölder conjugate exponents `p` and `q` with `q < ∞`, the continuous dual of
`lp E q` is the `lp` sum of the continuous duals of the normed spaces `E i`.
The pairing is the bilinear series `∑' i, φ i (x i)`, also over complex scalars.
Neither completeness of the fibres nor countability of the index type is needed.

The equivalence is `lp.strongDualEquiv`, whose forward map is Mathlib's `lp.dualPairing`.
Evaluate it with `lp.strongDualEquiv_apply`, or with `lp.strongDualEquiv_apply_single` on
coordinate vectors; recover the representing family of a functional with
`lp.strongDualEquiv_symm_apply`, which restricts it to each summand. The norm identity
`ContinuousLinearMap.norm_rpow_eq_tsum_norm_comp_lp_single_rpow` computes the norm of a
functional from these restrictions. The coordinate estimates build on the scalar duality
estimates in `TauCeti.Analysis.Normed.Lp.Dual`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, Proposition 1.3.3.
-/

public section

noncomputable section

open Filter Metric
open scoped ENNReal Topology

variable {𝕜 ι : Type*} [RCLike 𝕜] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

namespace ContinuousLinearMap

variable [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Restricting a continuous linear map on a dependent ℓ^q sum to a coordinate summand
does not increase its norm. -/
theorem norm_comp_lp_single_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : lp E q →L[𝕜] F) (i : ι) :
    ‖f.comp (lp.singleContinuousLinearMap 𝕜 E q i)‖ ≤ ‖f‖ := by
  refine (f.comp _).opNorm_le_bound (norm_nonneg f) fun x ↦ ?_
  simpa [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ q))] using
    f.le_opNorm (lp.single q i x)

/-- The finite sums of `p`-th powers of the norms of a functional's coordinate
restrictions are bounded by the `p`-th power of its norm. -/
theorem sum_norm_comp_lp_single_rpow_le (hp : p ≠ ∞)
    (f : StrongDual 𝕜 (lp E q)) (s : Finset ι) :
    ∑ i ∈ s, ‖f.comp (lp.singleContinuousLinearMap 𝕜 E q i)‖ ^ p.toReal ≤
      ‖f‖ ^ p.toReal := by
  let L i := f.comp (lp.singleContinuousLinearMap 𝕜 E q i)
  have hex i : ∃ v : ℕ → E i, (∀ n, ‖v n‖ ≤ 1) ∧
      Tendsto (fun n ↦ ‖L i (v n)‖) atTop (𝓝 ‖L i‖) := by
    obtain ⟨a, -, ha, hamem⟩ := exists_seq_tendsto_sSup
      ((nonempty_closedBall.mpr zero_le_one).image (fun x ↦ ‖L i x‖))
      ⟨‖L i‖, by
        rintro _ ⟨x, hx, rfl⟩
        exact (L i).unit_le_opNorm x (mem_closedBall_zero_iff.mp hx)⟩
    choose v hv hav using hamem
    refine ⟨v, fun n ↦ mem_closedBall_zero_iff.mp (hv n), ?_⟩
    simpa only [hav, (L i).sSup_unitClosedBall_eq_norm] using ha
  choose v hv hlim using hex
  have hbound n : ∑ i ∈ s, ‖L i (v i n)‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
    let T := lp.mapCLM q (fun i ↦ ContinuousLinearMap.toSpanSingleton 𝕜 (v i n))
      zero_le_one (fun i ↦ by simpa using hv i n)
    have hT : ‖T‖ ≤ 1 := lp.norm_mapCLM_le _ _ _ _
    have hnorm : ‖f.comp T‖ ≤ ‖f‖ :=
      (f.opNorm_comp_le T).trans (mul_le_of_le_one_right (norm_nonneg f) hT)
    have h := (f.comp T).sum_norm_lp_single_rpow_le hp s
    simp only [coe_comp, Function.comp_apply, T, lp.mapCLM_single,
      toSpanSingleton_apply, one_smul] at h
    simp only [L, coe_comp, Function.comp_apply, lp.singleContinuousLinearMap_apply]
    exact h.trans (Real.rpow_le_rpow (norm_nonneg _) hnorm ENNReal.toReal_nonneg)
  exact le_of_tendsto (tendsto_finsetSum s fun i _ ↦
    (hlim i).rpow_const (Or.inr ENNReal.toReal_nonneg)) (Filter.Eventually.of_forall hbound)

/-- The coordinate restrictions of a functional on a dependent ℓ^q sum form an ℓᵖ
family, for conjugate exponents. -/
theorem memℓp_comp_lp_single (f : StrongDual 𝕜 (lp E q)) :
    Memℓp (fun i ↦ f.comp (lp.singleContinuousLinearMap 𝕜 E q i)) p := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact memℓp_infty ⟨‖f‖, Set.forall_mem_range.mpr f.norm_comp_lp_single_le⟩
  · exact memℓp_gen' (f.sum_norm_comp_lp_single_rpow_le hp)

/-- An ℓᵖ family equal to the coordinate restrictions of a functional on a dependent
ℓ^q sum has norm bounded by that functional's norm. -/
theorem norm_le_opNorm_of_forall_eq_comp_lp_single (f : StrongDual 𝕜 (lp E q))
    (a : lp (fun i ↦ StrongDual 𝕜 (E i)) p)
    (ha : ∀ i, a i = f.comp (lp.singleContinuousLinearMap 𝕜 E q i)) : ‖a‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · exact lp.norm_le_of_forall_le (norm_nonneg f) fun i ↦ ha i ▸ f.norm_comp_lp_single_le i
  · refine lp.norm_le_of_forall_sum_le
      (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp) (norm_nonneg f) ?_
    simpa only [ha] using f.sum_norm_comp_lp_single_rpow_le hp

end ContinuousLinearMap

namespace lp

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

omit [Fact (1 ≤ q)] in
/-- Summing coordinate functionals over a coordinate vector evaluates the functional at
that coordinate. -/
private theorem tsum_apply_single [DecidableEq ι] (a : ∀ i, StrongDual 𝕜 (E i)) (i : ι)
    (x : E i) : ∑' j, a j (lp.single q i x j) = a i x := by
  simp only [lp.single_apply]
  simp_rw [Pi.apply_single (fun j ↦ a j) (fun j ↦ (a j).map_zero)]
  exact tsum_pi_single _ _

variable (𝕜 E p q) in
/-- The duality between the ℓᵖ sum of continuous duals and the continuous dual of
the dependent ℓ^q sum, for conjugate exponents with `q < ∞`.
At `q = 1`, its domain consists of all uniformly bounded families of functionals. -/
def strongDualEquiv (hq : q ≠ ∞) :
    lp (fun i ↦ StrongDual 𝕜 (E i)) p ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp E q) := by
  classical
  -- `hid` and the surjectivity proof below carry their stated types, so that
  -- `strongDualEquiv_apply` can unfold this definition with `simp`.
  have hid i : ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 (E i))‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.norm_id_le
  let P := dualPairing p q (fun i ↦ ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 (E i))) hid
  have hP (a : lp (fun i ↦ StrongDual 𝕜 (E i)) p) i :
      (P a).comp (singleContinuousLinearMap 𝕜 E q i) = a i := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, singleContinuousLinearMap_apply,
      P, dualPairing_apply, ContinuousLinearMap.id_apply]
    exact tsum_apply_single (fun j ↦ a j) i x
  have hnorm a : ‖P a‖ = ‖a‖ := by
    refine le_antisymm ?_
      ((P a).norm_le_opNorm_of_forall_eq_comp_lp_single a fun i ↦ (hP a i).symm)
    exact (P.le_opNorm a).trans (mul_le_of_le_one_left (norm_nonneg a)
      (norm_dualPairing _ hid))
  refine LinearIsometryEquiv.ofSurjective { P.toLinearMap with norm_map' := hnorm }
    (Function.RightInverse.surjective
      (g := fun f ↦ ⟨fun i ↦ f.comp (singleContinuousLinearMap 𝕜 E q i),
        f.memℓp_comp_lp_single⟩) fun f ↦ ?_)
  exact ext_continuousLinearMap hq fun i ↦ hP _ i

/-- The duality equivalence acts by the bilinear series of coordinate evaluations. -/
theorem strongDualEquiv_apply (hq : q ≠ ∞)
    (a : lp (fun i ↦ StrongDual 𝕜 (E i)) p) (x : lp E q) :
    strongDualEquiv 𝕜 E p q hq a x = ∑' i, a i (x i) := by
  simp only [strongDualEquiv, LinearIsometryEquiv.coe_ofSurjective, LinearIsometry.coe_mk,
    ContinuousLinearMap.coe_coe, dualPairing_apply, ContinuousLinearMap.id_apply]

/-- For scalar fibres, the dependent duality agrees with scalar sequence duality
under the coordinatewise multiplication maps. -/
theorem strongDualEquiv_mapCLM_mul (hq : q ≠ ∞) (a : lp (fun _ : ι ↦ 𝕜) p) :
    strongDualEquiv 𝕜 (fun _ : ι ↦ 𝕜) p q hq
      (mapCLM p (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) zero_le_one
        (fun _ ↦ ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜) a) =
      dualEquiv 𝕜 ι p q hq a := by
  ext x
  simp [strongDualEquiv_apply, dualEquiv_apply]

variable [DecidableEq ι]

/-- Pairing with a coordinate vector evaluates the corresponding coordinate functional. -/
@[simp]
theorem strongDualEquiv_apply_single (hq : q ≠ ∞)
    (a : lp (fun i ↦ StrongDual 𝕜 (E i)) p) (i : ι) (x : E i) :
    strongDualEquiv 𝕜 E p q hq a (lp.single q i x) = a i x := by
  rw [strongDualEquiv_apply]
  exact tsum_apply_single (fun j ↦ a j) i x

/-- The inverse duality equivalence restricts a functional to a coordinate summand. -/
@[simp]
theorem strongDualEquiv_symm_apply (hq : q ≠ ∞) (f : StrongDual 𝕜 (lp E q)) (i : ι) :
    (strongDualEquiv 𝕜 E p q hq).symm f i =
      f.comp (singleContinuousLinearMap 𝕜 E q i) := by
  ext x
  have h := congrArg (fun g : StrongDual 𝕜 (lp E q) ↦ g (lp.single q i x))
    ((strongDualEquiv 𝕜 E p q hq).apply_symm_apply f)
  rw [strongDualEquiv_apply_single] at h
  simpa only [ContinuousLinearMap.comp_apply, singleContinuousLinearMap_apply] using h

end lp

namespace ContinuousLinearMap

variable [DecidableEq ι] {p q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- For finite conjugate exponents, the `p`-th power of a functional's norm is
the sum of the `p`-th powers of the norms of its coordinate restrictions. -/
theorem norm_rpow_eq_tsum_norm_comp_lp_single_rpow (hp : p ≠ ∞) (hq : q ≠ ∞)
    (f : StrongDual 𝕜 (lp E q)) :
    ‖f‖ ^ p.toReal =
      ∑' i, ‖f.comp (lp.singleContinuousLinearMap 𝕜 E q i)‖ ^ p.toReal := by
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  rw [← (lp.strongDualEquiv 𝕜 E p q hq).symm.norm_map f,
    lp.norm_rpow_eq_tsum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp)]
  simp only [lp.strongDualEquiv_symm_apply]

end ContinuousLinearMap
