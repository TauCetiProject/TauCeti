/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.TestFunction.Integral
public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Gluing locally constant distributions

On a connected nonempty open set, a distribution which is locally integration against a constant
is globally integration against one unique constant. No finite-mass or order-zero assumption is
made. The constants are identified by integral-one tests on overlaps, and finite smooth
partitions of unity identify the resulting global distribution.

The result applies to Banach-valued distributions and any locally finite measure positive on
nonempty open sets. With Lebesgue measure it supplies the local-to-global step in distributional
constancy proofs: establishing the local constant formulas is a separate analytic task.

## References

* Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1: localization of
  distributions by partitions of unity.
-/

public section

open Set TopologicalSpace MeasureTheory Function Filter
open scoped Distributions Topology

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E} {n : ℕ∞} {μ : Measure E}
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- On a nonempty open domain, the constant inducing a distribution is uniquely determined. -/
theorem ofFun_const_injective (hne : (Ω : Set E).Nonempty) :
    Injective (fun c : F ↦ ofFun Ω (fun _ ↦ c) μ n) := by
  obtain ⟨φ, -, -, hφ⟩ := TestFunction.exists_nonneg_integral_eq_one
    (μ := μ) (n := n) Ω.isOpen hne Subset.rfl
  intro c d h
  have heq := congrArg (fun S : 𝓓'^{n}(Ω, F) ↦ S φ) h
  simpa only [ofFun_apply (locallyIntegrableOn_const _), integral_smul_const, hφ,
    one_smul] using heq

/-- Local constant evaluation formulas for a distribution glue to one unique global constant
on a connected nonempty domain. Neighborhoods need not form a finite cover, and their local
constants are not assumed compatible. -/
theorem existsUnique_eq_ofFun_const_of_locally (T : 𝓓'^{n}(Ω, F))
    (hΩ : IsConnected (Ω : Set E))
    (h : ∀ x ∈ Ω, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ c : F, ∀ φ : 𝓓^{n}(Ω, ℝ), tsupport φ ⊆ U →
        T φ = (∫ y, φ y ∂μ) • c) :
    ∃! c : F, T = ofFun Ω (fun _ ↦ c) μ n := by
  classical
  choose U hU hxU c hc using fun x : Ω ↦ h x x.2
  -- An integral-one test in the overlap recovers both local coefficients.
  have hceq {x y : Ω} (hy : (y : E) ∈ U x) : c y = c x := by
    obtain ⟨φ, hφ, -, hint⟩ := TestFunction.exists_nonneg_integral_eq_one
      (μ := μ) (n := n) ((hU x).inter (hU y) |>.inter Ω.isOpen)
      ⟨y, ⟨⟨hy, hxU y⟩, y.2⟩⟩ (fun _ hz ↦ hz.2)
    calc
      c y = T φ := by rw [hc y φ (fun z hz ↦ (hφ hz).1.2), hint, one_smul]
      _ = c x := by rw [hc x φ (fun z hz ↦ (hφ hz).1.1), hint, one_smul]
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [((hU x).preimage continuous_subtype_val).mem_nhds (hxU x)] with y hy
    exact hceq hy
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hΩ.isPreconnected
  obtain ⟨x₀, hx₀⟩ := hΩ.nonempty
  let x : Ω := ⟨x₀, hx₀⟩
  have hconst (y : Ω) : c y = c x := hlc.apply_eq_of_preconnectedSpace y x
  have hT : T = ofFun Ω (fun _ ↦ c x) μ n := by
    have hzero := AddMonoidHom.eq_zero_of_locally_vanishing
      (AddMonoidHom.ofClass T - AddMonoidHom.ofClass (ofFun Ω (fun _ ↦ c x) μ n))
      (fun y hy ↦ ?_)
    · ext φ
      simpa only [AddMonoidHom.sub_apply, AddMonoidHom.coe_ofClass,
        AddMonoidHom.zero_apply, sub_eq_zero] using DFunLike.congr_fun hzero φ
    · refine ⟨U ⟨y, hy⟩, hU _, hxU _, fun φ hφ ↦ ?_⟩
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_ofClass,
        ofFun_apply (locallyIntegrableOn_const _), integral_smul_const,
        hc ⟨y, hy⟩ φ hφ, hconst, sub_self]
  refine ⟨c x, hT, fun d hd ↦ ?_⟩
  exact ofFun_const_injective hΩ.nonempty (hd.symm.trans hT)

end Distribution
