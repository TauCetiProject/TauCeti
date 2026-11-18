/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import TauCeti.MeasureTheory.Integral.RiemannSum

/-!
# Discretizing the Cauchy–Pompeiu formula on a compact set

Let `K` be a compact subset of an open set `V ⊆ ℂ`. This file approximates every holomorphic
function on `V` with values in a complex normed space `F` uniformly on `K` by a combination of
simple fractions with *fixed* poles: for every `ε > 0` there are finitely many points
`ζ i ∈ V \ K` and coefficients `c i` such that

`‖f w - ∑ i, c i (w - ζ i)⁻¹ f (ζ i)‖ ≤ ε M`  for all `w ∈ K`,

whenever `f : ℂ → F` is holomorphic on `V` and bounded by `M` there
(`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`). The approximation is linear in `f`, its
poles and coefficients depend neither on `f` nor on `F`, and the values of `f` enter only at the
points `ζ i`. This is the first half of the construction of a finite-rank Runge operator:
replacing each simple fraction `(z - ζ i)⁻¹` by a function holomorphic on a larger domain, which
Runge's theorem allows when `K` has no holes in that domain, gives a linear operator through
finitely many point evaluations with the same uniform estimate, of finite rank for scalar `f`.

The proof has two steps.

* **Reconstruction through a cutoff.** If `χ` is a compactly supported `C¹` function whose
  topological support lies in `V`, the Cauchy–Pompeiu formula applied to `χ f` gives
  `χ w f w = π⁻¹ ∫ (w - z)⁻¹ \bar∂χ(z) f z` for every `w`, because `\bar∂ (χ f) = (\bar∂χ) f` for
  holomorphic `f` (`HasCompactSupport.cauchyTransform_conjWirtingerDeriv_smul`). When `χ` is equal
  to one near `K`, the weight `\bar∂χ` vanishes off a compact set `S ⊆ V` disjoint from `K`.
  For a target `F` that is not complete, the estimate is proved in its completion.
* **Uniform Riemann sums.** On `S` the integrands `z ↦ (w - z)⁻¹ f z`, for `w ∈ K` and `f` bounded
  by `M` on `V`, are uniformly Lipschitz with constant proportional to `M`: the kernel because `S`
  is at positive distance from `K`, and `f` by Cauchy's estimate. A single Riemann sum for the
  weight `\bar∂χ` on `S` therefore approximates all of them at once
  (`TotallyBounded.exists_norm_setIntegral_smul_sub_sum_le`).

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorem 10.3 (the Cauchy–Pompeiu formula
  with a cutoff) and Theorem 11.1 (Runge's theorem).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.1.
-/

public section

open MeasureTheory Complex Set Metric Filter Function
open scoped Real Topology

universe u

namespace TauCeti

/-- The cutoff representation on `K`: integration against a continuous weight `a` over a compact
set `S ⊆ V` disjoint from `K` reproduces every function holomorphic on `V` with values in a complex
Banach space at the points of `K`. -/
private theorem exists_continuous_setIntegral_representation {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ (a : ℂ → ℂ) (S : Set ℂ), Continuous a ∧ IsCompact S ∧ S ⊆ V ∧ K ⊆ Sᶜ ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : ℂ → F),
        DifferentiableOn ℂ f V → ∀ w ∈ K,
        f w = (π : ℂ)⁻¹ • ∫ z in S, a z • (w - z)⁻¹ • f z := by
  -- A cutoff `χ` equal to one near `K`; its `\bar∂` is supported in the compact shell `S`.
  obtain ⟨ψ, hψd, -, hψ1, hψc, hψV⟩ := hK.exists_contDiff_cutoff hV hKV
  set χ : ℂ → ℂ := fun z ↦ (ψ z : ℂ)
  have hχd : ContDiff ℝ 1 χ := ofRealCLM.contDiff.comp (hψd.of_le (by simp))
  have hχc : HasCompactSupport χ := hψc.comp_left ofReal_zero
  have hχV : tsupport χ ⊆ V := (tsupport_comp_subset ofReal_zero ψ).trans hψV
  have hχ1 {z : ℂ} (hz : z ∈ interior (ψ ⁻¹' {1})) : χ z = 1 := by
    simp [χ, mem_singleton_iff.1 (mem_preimage.1 (interior_subset hz))]
  set S := tsupport ψ \ interior (ψ ⁻¹' {1})
  have ha0 (z : ℂ) (hz : z ∉ S) : conjWirtingerDeriv χ z 1 = 0 := by
    have hconst : ∃ b : ℂ, χ =ᶠ[𝓝 z] fun _ ↦ b := by
      by_cases hzψ : z ∈ tsupport ψ
      · have hz1 : z ∈ interior (ψ ⁻¹' {1}) := by_contra fun h ↦ hz ⟨hzψ, h⟩
        refine ⟨1, ?_⟩
        filter_upwards [isOpen_interior.mem_nhds hz1] with y hy
        exact hχ1 hy
      · refine ⟨0, ?_⟩
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzψ] with y hy
        simp [χ, hy]
    obtain ⟨b, hb⟩ := hconst
    simp [hb.conjWirtingerDeriv_eq]
  refine ⟨fun z ↦ conjWirtingerDeriv χ z 1, S, continuous_iff_continuousAt.2 fun z ↦
      (hχd.contDiffAt.conjWirtingerDeriv_apply (m := 0) (by simp) 1).continuousAt,
    hψc.isCompact.diff isOpen_interior, sdiff_subset.trans hψV, fun w hw hwS ↦ hwS.2 (hψ1 hw),
    fun {F} _ _ _ f hf w hw ↦ ?_⟩
  have h := hχc.cauchyTransform_conjWirtingerDeriv_smul hχd hV hχV hf w
  rw [hχ1 (hψ1 hw), one_smul, cauchyTransform_apply] at h
  rw [← h, setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [ha0 z hz]]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z ↦ smul_comm _ _ _)

/-- **Discretized Cauchy–Pompeiu formula.** Let `K` be a compact subset of an open set `V ⊆ ℂ`.
For every `ε > 0` there are finitely many poles `ζ i ∈ V \ K` and coefficients `c i` such that every
`f : ℂ → F` into a complex normed space, holomorphic on `V` and bounded by `M` there, satisfies
`‖f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)‖ ≤ ε * M` for every `w ∈ K`.

The poles and coefficients depend only on `K`, `V` and `ε`, not on `f` or `F`, so the approximation
is a linear operator in `f` through the finitely many values `f (ζ i)`, uniformly accurate on the
bounded holomorphic functions; for scalar `f` it has finite rank. -/
theorem _root_.IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ), (∀ i, ζ i ∈ V \ K) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, (c i * (w - ζ i)⁻¹) • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨a, S, ha, hS, hSV, hKS, hrep⟩ :=
    exists_continuous_setIntegral_representation.{u} hK hV hKV
  -- `S` is at distance more than `d` from `K`, and its `2 * r`-neighbourhood lies in `V`.
  obtain ⟨d, hd, hdK⟩ := hK.exists_cthickening_subset_open hS.isClosed.isOpen_compl hKS
  obtain ⟨ρ, hρ, hρS⟩ := hS.exists_cthickening_subset_open hV hSV
  have hdist {w z : ℂ} (hw : w ∈ K) (hz : z ∈ S) : d ≤ ‖w - z‖ := by
    by_contra h
    refine hdK (closedBall_subset_cthickening hw d ?_) hz
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact (not_le.1 h).le
  set r := ρ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hradius : 2 * r = ρ := by rw [hr_def]; ring
  have hball {y : ℂ} (hy : y ∈ S) : closedBall y (2 * r) ⊆ V :=
    (closedBall_subset_cthickening hy _).trans (by rwa [hradius])
  -- Choose the mesh `δ` of the Riemann sums against the Lipschitz constant `M * C`.
  set A := ∫ z in S, ‖a z‖
  have hA : 0 ≤ A := setIntegral_nonneg_of_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
  set C := r⁻¹ * d⁻¹ + (d ^ 2)⁻¹
  have hC : 0 ≤ C := by positivity
  obtain ⟨δ₀, hδ₀, hδ₀ε⟩ := exists_pos_mul_lt (mul_pos hε Real.pi_pos) (C * A)
  obtain ⟨N, ζ, c, hζS, -, hsum⟩ :=
    hS.totallyBounded.exists_norm_setIntegral_smul_sub_sum_le (μ := volume) hS.measurableSet
      (ha.continuousOn.integrableOn_compact hS) (lt_min hr hδ₀)
  refine ⟨N, ζ, fun i ↦ (π : ℂ)⁻¹ * c i, fun i ↦ ⟨hSV (hζS i), fun h ↦ hKS h (hζS i)⟩,
    fun {F} _ _ f M hf hM w hw ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w (hKV hw))
  -- The Cauchy–Pompeiu integral needs a complete target, so work in the completion of `F`.
  let L : F →L[ℂ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  set g : ℂ → UniformSpace.Completion F := fun z ↦ L (f z)
  have hg : DifferentiableOn ℂ g V := L.differentiable.comp_differentiableOn hf
  have hgM (z : ℂ) (hz : z ∈ V) : ‖g z‖ ≤ M := by
    simpa [g, L] using hM z hz
  have hfg : ‖f w - ∑ i, ((π : ℂ)⁻¹ * c i * (w - ζ i)⁻¹) • f (ζ i)‖ =
      ‖g w - ∑ i, ((π : ℂ)⁻¹ * c i * (w - ζ i)⁻¹) • g (ζ i)‖ := by
    simp only [g, ← map_smul, ← map_sum, ← map_sub]
    exact (UniformSpace.Completion.norm_coe _).symm
  rw [hfg]
  have hφc : ContinuousOn (fun z ↦ (w - z)⁻¹ • g z) S := by
    refine (ContinuousOn.inv₀ (f := fun z : ℂ ↦ w - z) (by fun_prop) fun z hz h ↦ hKS hw ?_).smul
      (hg.continuousOn.mono hSV)
    rwa [sub_eq_zero.1 h]
  have hR := hsum (fun z ↦ (w - z)⁻¹ • g z) (M * C * min r δ₀)
    ((ha.continuousOn.smul hφc).integrableOn_compact hS) fun x hx y hy hxy ↦
      (norm_inv_smul_sub_inv_smul_le hV hg hr (hball hy) (fun z hz ↦ hgM z (hball hy hz)) hd
        (hxy.trans_le (min_le_left _ _)) (hdist hw hx) (hdist hw hy)).trans
        (mul_le_mul_of_nonneg_left hxy.le (mul_nonneg hM0 hC))
  have hsum_eq : ∑ i, ((π : ℂ)⁻¹ * c i * (w - ζ i)⁻¹) • g (ζ i) =
      (π : ℂ)⁻¹ • ∑ i, c i • (w - ζ i)⁻¹ • g (ζ i) := by
    simp only [Finset.smul_sum, smul_smul, mul_assoc]
  have hπ : ‖(π : ℂ)⁻¹‖ = π⁻¹ := by simp [abs_of_pos Real.pi_pos]
  rw [hsum_eq, hrep g hg w hw, ← smul_sub, norm_smul, hπ, inv_mul_le_iff₀ Real.pi_pos]
  have hδA : C * A * min r δ₀ ≤ ε * π :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg hC hA)).trans hδ₀ε.le
  calc _ ≤ M * C * min r δ₀ * A := hR
    _ = M * (C * A * min r δ₀) := by ring
    _ ≤ M * (ε * π) := mul_le_mul_of_nonneg_left hδA hM0
    _ = π * (ε * M) := by ring

end TauCeti
