/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Restriction to `(0, 1)` is not continuous for the strong Whitney topologies

Restriction of `C^n` functions from `ℝ` to the open interval `U = (0, 1)` is not continuous from
the strong Whitney topology of `ℝ` to that of `U`, for any finite or infinite smoothness order
`n`. So the closedness hypothesis of `ContMDiffMap.continuous_restrict_manifoldStrongWhitney`
cannot be dropped.

The obstruction is a tolerance tending to zero at the frontier point `0` of `U`. The functions
`g` on `U` with `|g x| < x` at every point form a strong neighbourhood of `0`
(`ContMDiffMap.setOf_forall_abs_lt_mem_nhds_manifoldStrongWhitney_Ioo`), but no restriction of a
function `f` on `ℝ` with `f 0 ≠ 0` lies in it, since `|f x|` tends to `|f 0| > 0` while the
tolerance tends to `0` (`ContMDiffMap.restrict_notMem_setOf_forall_abs_lt`). A bump function `ψ`
with `0 ≤ ψ ≤ 1` and `ψ = 1` near `0` has compact support, so its multiples `δ • ψ` tend to `0`
strongly on `ℝ` as `δ → 0` (`ContMDiffMap.tendsto_smul_manifoldStrongWhitney`). For every `δ ≠ 0`
the restriction of `δ • ψ` fails the bound at the points `0 < x < |δ|` where `ψ x = 1`, so
restriction is not continuous at `0`.

On a compact interval `[a, b] ⊆ (0, 1)` the same bound is harmless. The functions `g` on `U`
with `|g x| < x` on `[a, b]` form a weak neighbourhood of `0`
(`ContMDiffMap.setOf_forall_mem_Icc_abs_lt_mem_nhds_manifoldWeakWhitney_Ioo`), and every
restriction of `δ • ψ` with `|δ| < a` lies in it
(`ContMDiffMap.restrict_smul_mem_setOf_forall_mem_Icc_abs_lt`). This agrees with the continuity of
restriction from the strong topology of `ℝ` into the weak topology of `U`
(`ContMDiffMap.continuous_restrict_manifoldStrongWhitney_weak`).

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, pp. 34–36, for the strong `C^r`
  topology.
-/

public section

open Set Filter Topology TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

/-- The open unit interval as an open subset of `ℝ`. -/
private abbrev U₀ : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩

variable {n : ℕ∞}

/-! ### The tolerance `x` on `(0, 1)` -/

/-- **The tolerance `x` gives a strong neighbourhood on `(0, 1)`.** The functions `g` on `(0, 1)`
with `|g x| < x` at every point form a strong Whitney neighbourhood of `0`. -/
theorem setOf_forall_abs_lt_mem_nhds_manifoldStrongWhitney_Ioo :
    {g : C^n⟮𝓘(ℝ), (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ); 𝓘(ℝ), ℝ⟯ | ∀ x, |g x| < x} ∈
      @nhds _ manifoldStrongWhitneyTopology 0 := by
  have : LocallyCompactSpace U₀ := isOpen_Ioo.locallyCompactSpace
  simpa only [coe_zero, Pi.zero_apply, sub_zero, Real.norm_eq_abs] using
    setOf_forall_norm_sub_lt_mem_nhds_manifoldStrongWhitney
      (0 : C^n⟮𝓘(ℝ), U₀; 𝓘(ℝ), ℝ⟯) continuous_subtypeVal fun x ↦ x.property.1

/-- **A function on `ℝ` which does not vanish at `0` does not restrict into the neighbourhood
`|g x| < x` of `0` on `(0, 1)`**: near `0` the absolute value of `f` stays close to `|f 0| > 0`,
while the tolerance `x` tends to `0`. -/
theorem restrict_notMem_setOf_forall_abs_lt (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) (hf : f 0 ≠ 0) :
    f.restrict ⟨Ioo 0 1, isOpen_Ioo⟩ ∉
      {g : C^n⟮𝓘(ℝ), (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ); 𝓘(ℝ), ℝ⟯ | ∀ x, |g x| < x} := by
  intro h
  -- The continuous function `|f x| - x` is positive at `0`, hence at some point of `(0, 1)`.
  have hpos : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < |f x| - x :=
    (f.contMDiff.continuous.abs.sub continuous_id).continuousAt.eventually
      (lt_mem_nhds (by simpa using abs_pos.mpr hf))
  obtain ⟨x, hx, hxI⟩ :=
    ((hpos.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  have := h ⟨x, hxI⟩
  rw [restrict_apply] at this
  exact (sub_pos.mp hx).not_gt this

/-- **Restriction from `ℝ` to `(0, 1)` is not continuous for the strong Whitney topologies.** -/
theorem not_continuous_restrict_Ioo_manifoldStrongWhitney :
    ¬ Continuous[manifoldStrongWhitneyTopology, manifoldStrongWhitneyTopology]
      (fun f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ ↦ f.restrict ⟨Ioo 0 1, isOpen_Ioo⟩) := by
  intro hcont
  let := (manifoldStrongWhitneyTopology : TopologicalSpace C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯)
  let := (manifoldStrongWhitneyTopology : TopologicalSpace C^n⟮𝓘(ℝ), U₀; 𝓘(ℝ), ℝ⟯)
  -- A bump function equal to `1` on `[-1, 1]`.
  let ψ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let u : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ := ⟨ψ, ψ.contDiff.contMDiff⟩
  -- Small multiples of `u` restrict into the neighbourhood `|g x| < x`, so some nonzero one does.
  have hlim : Tendsto (fun δ : ℝ ↦ (δ • u).restrict U₀) (𝓝 0) (𝓝 0) := by
    have h := (hcont.tendsto 0).comp (tendsto_smul_manifoldStrongWhitney u ψ.hasCompactSupport)
    rwa [restrict_zero] at h
  have hev := (hlim.eventually setOf_forall_abs_lt_mem_nhds_manifoldStrongWhitney_Ioo).filter_mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  -- But `δ • u` takes the value `δ ≠ 0` at `0`.
  have hu : u 0 = 1 := ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)
  exact restrict_notMem_setOf_forall_abs_lt (δ • u) (by simpa [hu] using hδ0) hδ

/-! ### The tolerance `x` on a compact interval -/

/-- **On a compact interval inside `(0, 1)` the tolerance `x` gives a weak neighbourhood.** For
`0 < a` and `b < 1`, the functions `g` on `(0, 1)` with `|g x| < x` for `x ∈ [a, b]` form a weak
Whitney neighbourhood of `0`. -/
theorem setOf_forall_mem_Icc_abs_lt_mem_nhds_manifoldWeakWhitney_Ioo {a b : ℝ} (ha : 0 < a)
    (hb : b < 1) :
    {g : C^n⟮𝓘(ℝ), (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ); 𝓘(ℝ), ℝ⟯ |
      ∀ x : (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ), (x : ℝ) ∈ Icc a b → |g x| < x} ∈
      @nhds _ manifoldWeakWhitneyTopology 0 := by
  have hK : IsCompact (Subtype.val ⁻¹' Icc a b : Set U₀) :=
    IsInducing.subtypeVal.isCompact_preimage' isCompact_Icc fun x hx ↦
      ⟨⟨x, ha.trans_le hx.1, hx.2.trans_lt hb⟩, rfl⟩
  have h := eventually_forall_dist_lt (0 : C^n⟮𝓘(ℝ), U₀; 𝓘(ℝ), ℝ⟯) hK continuous_subtypeVal
    fun x _ ↦ x.property.1
  simp only [coe_zero, Pi.zero_apply, Real.dist_eq, sub_zero, mem_preimage] at h
  exact h

/-- **Small multiples of a function bounded by `1` pass the bound on a compact interval.** If
`|u| ≤ 1` on `[a, b]` and `|δ| < a`, the restriction of `δ • u` to `(0, 1)` satisfies
`|δ u x| < x` for every `x ∈ [a, b]`. -/
theorem restrict_smul_mem_setOf_forall_mem_Icc_abs_lt (u : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) {a b δ : ℝ}
    (hu : ∀ x ∈ Icc a b, |u x| ≤ 1) (hδ : |δ| < a) :
    (δ • u).restrict ⟨Ioo 0 1, isOpen_Ioo⟩ ∈
      {g : C^n⟮𝓘(ℝ), (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ); 𝓘(ℝ), ℝ⟯ |
        ∀ x : (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ), (x : ℝ) ∈ Icc a b → |g x| < x} := by
  intro x hx
  rw [restrict_apply, coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
  calc |δ| * |u x| ≤ |δ| := mul_le_of_le_one_right (abs_nonneg δ) (hu x hx)
    _ < a := hδ
    _ ≤ x := hx.1

end ContMDiffMap
