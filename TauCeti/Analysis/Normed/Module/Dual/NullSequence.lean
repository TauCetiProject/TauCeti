/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Module.Annihilator
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# Approximating functionals through an injective operator along null sequences

Let `J : Y →L[𝕜] E` be an injective operator out of a Banach space `Y` over `𝕜 = ℝ` or `ℂ`, and
let `y` be a null sequence in `Y`. Every functional on `Y` agrees, up to any prescribed error and
uniformly along `y`, with a functional of the form `ψ ∘ J`; the same holds for operators from `Y`
into a finite-dimensional space.

The proof is a Hahn–Banach argument in `c₀`: a functional on `c₀` annihilating the sequences
`(ψ (J (y n)))ₙ` for all `ψ ∈ E*` is given by some `a ∈ ℓ¹`, and it annihilates `(φ (y n))ₙ` for
every `φ ∈ Y*`, because `J (∑ aₙ • yₙ) = 0` and `J` is injective.

## Main statements

* `TauCeti.exists_dual_forall_norm_sub_lt`: for an injective operator `J` out of a Banach space,
  every functional is approximated by functionals `ψ ∘ J` uniformly along each null sequence.
* `TauCeti.exists_forall_norm_sub_lt_of_finiteDimensional`: the same for operators into a
  finite-dimensional space.
-/

public section

open Filter
open scoped Topology ZeroAtInfty

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

open ZeroAtInftyContinuousMap in
/-- Let `J : Y →L[𝕜] E` be injective, with `Y` complete, and let `y` be a null sequence in `Y`.
Every continuous functional `φ` on `Y` is approximated by functionals of the form `ψ ∘ J`,
uniformly along `y`. -/
theorem exists_dual_forall_norm_sub_lt {J : Y →L[𝕜] E} (hJ : Function.Injective J) {y : ℕ → Y}
    (hy : Tendsto y atTop (𝓝 0)) (φ : StrongDual 𝕜 Y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : StrongDual 𝕜 E, ∀ n, ‖φ (y n) - ψ (J (y n))‖ < δ := by
  classical
  -- The values of a functional along `y` form a null sequence, that is, an element of `c₀`.
  have hseq (χ : StrongDual 𝕜 Y) : Tendsto (fun n ↦ χ (y n)) cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop, ← map_zero χ]
    exact (χ.continuous.tendsto 0).comp hy
  let L : StrongDual 𝕜 E →ₗ[𝕜] C₀(ℕ, 𝕜) :=
    { toFun ψ := mkOfDiscrete (fun n ↦ (ψ ∘L J) (y n)) (hseq (ψ ∘L J))
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  -- A functional `Λ` on `c₀` annihilating the range of `L` is a series `∑ aₙ eₙ*` with `a ∈ ℓ¹`.
  -- It pairs each coefficient sequence with the vector `z = ∑ aₙ • yₙ`, and `J z = 0`.
  have hmem : mkOfDiscrete _ (hseq φ) ∈ (LinearMap.range L).topologicalClosure := by
    rw [Submodule.mem_topologicalClosure_iff_forall_dual_eq_zero]
    intro Λ hΛ
    obtain ⟨C, hC⟩ := hy.norm.bddAbove_range
    have hs : Summable fun n ↦ Λ (single n 1) • y n :=
      Summable.of_norm_bounded ((summable_norm_apply_single_one Λ).mul_right C) fun n ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hC ⟨n, rfl⟩) (norm_nonneg _)
    have hval (χ : StrongDual 𝕜 Y) :
        Λ (mkOfDiscrete _ (hseq χ)) = χ (∑' n, Λ (single n 1) • y n) :=
      (hasSum_apply_single_one_mul Λ _).unique (by simpa using hs.hasSum.mapL χ)
    have hz : ∑' n, Λ (single n 1) • y n = 0 := hJ <| by
      rw [map_zero]
      refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun ψ ↦ ?_
      rw [← ContinuousLinearMap.comp_apply, ← hval]
      exact hΛ _ ⟨ψ, rfl⟩
    rw [hval, hz, map_zero]
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  obtain ⟨_, ⟨ψ, rfl⟩, hψ⟩ := Metric.mem_closure_iff.mp hmem δ hδ
  rw [dist_eq_norm] at hψ
  refine ⟨ψ, fun n ↦ lt_of_le_of_lt ?_ hψ⟩
  simpa [L] using norm_coe_le_norm (mkOfDiscrete _ (hseq φ) - L ψ) n

/-- Let `J : Y →L[𝕜] E` be injective, with `Y` complete, and let `y` be a null sequence in `Y`.
Every operator `G` from `Y` into a finite-dimensional space `V` is approximated by operators of
the form `S ∘ J`, uniformly along `y`. -/
theorem exists_forall_norm_sub_lt_of_finiteDimensional {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V] {J : Y →L[𝕜] E} (hJ : Function.Injective J)
    {y : ℕ → Y} (hy : Tendsto y atTop (𝓝 0)) (G : Y →L[𝕜] V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : E →L[𝕜] V, ∀ n, ‖G (y n) - S (J (y n))‖ < δ := by
  classical
  -- Approximate each coordinate of `G` in a basis `b` of `V`, with error `δ / (∑ i, ‖b i‖ + 1)`.
  let b := Module.finBasis 𝕜 V
  set M := ∑ i, ‖b i‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  choose ψ hψ using fun i ↦ exists_dual_forall_norm_sub_lt hJ hy
    (LinearMap.toContinuousLinearMap (b.coord i) ∘L G) (δ := δ / (M + 1)) (by positivity)
  refine ⟨∑ i, (ψ i).smulRight (b i), fun n ↦ ?_⟩
  calc ‖G (y n) - (∑ i, (ψ i).smulRight (b i)) (J (y n))‖
      = ‖∑ i, (b.coord i (G (y n)) - ψ i (J (y n))) • b i‖ := by
        conv_lhs => rw [← b.sum_repr (G (y n))]
        simp [sub_smul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖b.coord i (G (y n)) - ψ i (J (y n))‖ * ‖b i‖ :=
        (norm_sum_le _ _).trans_eq (by simp only [norm_smul])
    _ ≤ ∑ i, δ / (M + 1) * ‖b i‖ :=
        Finset.sum_le_sum fun i _ ↦ by gcongr; simpa using (hψ i n).le
    _ = δ / (M + 1) * M := by rw [Finset.mul_sum]
    _ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

end TauCeti
