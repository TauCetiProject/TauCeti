/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Topology.ExtendFrom
import TauCeti.Analysis.Calculus.ContDiff.Extension
import TauCeti.Analysis.Sobolev.Wkp.Convex.Embedding
import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative
import TauCeti.Analysis.Sobolev.Wkp.LipschitzRepresentative
import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# Smooth Sobolev representatives on convex domain closures

A scalar function that belongs to every `L²` Sobolev order on a convex open set agrees almost
everywhere with a single function smooth on its closure. On each bounded convex patch,
Sobolev–Poincaré (`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_mul_measure_rpow_of_convex`)
and Morrey (`TauCeti.W1p.exists_holderOnWith_closure_ae_eq_of_convex`) improve integrability.
`TauCeti.exists_contDiffOn_ae_eq_of_forall_wkp` gives a common interior representative, and
`TauCeti.Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex` gives uniformly
continuous derivatives. Their continuous extensions form a Taylor series on the closure by
`IsOpen.exists_contDiffOn_closure_eqOn_of_uniformContinuousOn_iteratedFDeriv`.
This supplies the Sobolev-to-smooth boundary step on straightened half-balls for harmonic
Dirichlet problems, without requiring a smooth boundary for the convex patch.

## Main result

* `Convex.exists_contDiffOn_closure_ae_eq_of_forall_wkp` is the smooth representative on the
  closure of a convex domain.
-/

public section

open Bornology Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal NNReal Topology

namespace TauCeti

section ConvexDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

section PositiveDimension

variable [Nontrivial E]

private theorem exists_contDiffOn_closure_ae_eq_of_forall_wkp_bounded
    (hb : IsBounded (Ω : Set E)) (hc : Convex ℝ (Ω : Set E)) {u : E → ℝ}
    (hu : ∀ m, ∃ w : Wkp volume Ω 2 m, Wkp.value m w =ᵐ[volume.restrict (Ω : Set E)] u) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (closure (Ω : Set E)) ∧
      u =ᵐ[volume.restrict (Ω : Set E)] g := by
  let n := finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  let q : ℝ≥0∞ := (n + 2 : ℕ)
  have hnq : (n : ℝ≥0∞) < q := by dsimp [q]; exact_mod_cast Nat.lt_add_of_pos_right (by decide)
  have hq₂ : (2 : ℝ≥0∞) ≤ q := by dsimp [q]; exact_mod_cast Nat.le_add_left 2 n
  have hq : Fact (1 ≤ q) := ⟨one_le_two.trans hq₂⟩
  have hqi : q⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 hq₂
  let t := ((2 : ℝ≥0∞)⁻¹ - q⁻¹) / n
  have hn₀ : (n : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
  have hnInf : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hn.ne')
  have ht : t < (n : ℝ≥0∞)⁻¹ := by
    simp only [t, div_eq_mul_inv]
    calc _ < 1 * (n : ℝ≥0∞)⁻¹ :=
          ENNReal.mul_lt_mul_left hn₀ hnInf (tsub_le_self.trans_lt (by norm_num))
      _ = _ := one_mul _
  have he : q⁻¹ + n * t = (2 : ℝ≥0∞)⁻¹ := by
    dsimp only [t]
    rw [ENNReal.mul_div_cancel (Nat.cast_ne_zero.2 hn.ne') (ENNReal.natCast_ne_top n),
      add_tsub_cancel_of_le hqi]
  obtain ⟨v, hv, huv⟩ := exists_contDiffOn_ae_eq_of_forall_wkp hu
  have hjets (j : ℕ) : UniformContinuousOn (iteratedFDeriv ℝ j v) Ω := by
    obtain ⟨w, hw⟩ := hu (j + 2 + n)
    obtain ⟨z, hz⟩ := hc.exists_wkp_value_ae_eq_of_inv_add_eq hb (j + 2) ht n
      (ENNReal.natCast_ne_top _) he w
    obtain ⟨B, hB⟩ := Wkp.exists_value_ae_eq_of_memLp
      (q := ⊤) (fun w ↦ W1p.memLp_value_top_of_convex w hc hb hnq) (j + 1) z
    obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex hc j
    obtain ⟨g, hg, hBg, hd⟩ := hK B
    have hvg : EqOn v g Ω := Measure.eqOn_open_of_ae_eq
      (huv.symm.trans ((hB.trans (hz.trans hw)).symm.trans hBg)) Ω.isOpen
      hv.continuousOn hg.continuousOn
    refine ((hd j le_rfl).2.uniformContinuousOn).congr ?_
    intro x hx
    exact ((hvg.eventuallyEq_of_mem (Ω.isOpen.mem_nhds hx)).iteratedFDeriv ℝ j).eq_of_nhds.symm
  obtain ⟨g, hg, hgv⟩ :=
    Ω.isOpen.exists_contDiffOn_closure_eqOn_of_uniformContinuousOn_iteratedFDeriv hc hv hjets
  exact ⟨g, hg, huv.trans ((ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx ↦ (hgv hx).symm)⟩

end PositiveDimension

/-- A real-valued function in all Sobolev orders `W^{m,2}(Ω)` on a convex open set agrees
almost everywhere on `Ω` with a single function smooth on its closure. -/
theorem _root_.Convex.exists_contDiffOn_closure_ae_eq_of_forall_wkp
    (hc : Convex ℝ (Ω : Set E)) {u : E → ℝ}
    (hu : ∀ m, ∃ w : Wkp volume Ω 2 m, Wkp.value m w =ᵐ[volume.restrict (Ω : Set E)] u) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (closure (Ω : Set E)) ∧
      u =ᵐ[volume.restrict (Ω : Set E)] g := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨u, (contDiff_const (c := u 0)).contDiffOn.congr ?_, .rfl⟩
    exact fun x _ ↦ congrArg u (Subsingleton.elim x 0)
  let U (x : E) : Opens E := ⟨(Ω : Set E) ∩ ball x 1, Ω.isOpen.inter isOpen_ball⟩
  have hU (x : E) : U x ≤ Ω := fun _ hx ↦ hx.1
  have hlocal (x : E) := exists_contDiffOn_closure_ae_eq_of_forall_wkp_bounded
    (isBounded_ball.subset (inter_subset_right : (U x : Set E) ⊆ ball x 1))
    (hc.inter (convex_ball x 1)) (u := u) fun m ↦ by
      obtain ⟨w, hw⟩ := hu m
      exact ⟨Wkp.restrictL (hU x) m w, (Wkp.value_restrictL_ae (hU x) m w).trans
        (ae_restrict_of_ae_restrict_of_subset (hU x) hw)⟩
  choose f hf hfu using hlocal
  obtain ⟨v, hv, huv⟩ := exists_contDiffOn_ae_eq_of_forall_wkp hu
  have hev (x : E) : EqOn v (f x) (U x) := by
    have huv' : u =ᵐ[volume.restrict (U x : Set E)] v :=
      ae_restrict_of_ae_restrict_of_subset (hU x) huv
    exact Measure.eqOn_open_of_ae_eq (huv'.symm.trans (hfu x)) (U x).isOpen
      (hv.continuousOn.mono (hU x)) ((hf x).continuousOn.mono subset_closure)
  let g := extendFrom (Ω : Set E) v
  have hsub (x : E) : closure (Ω : Set E) ∩ ball x 1 ⊆ closure (U x : Set E) := by
    simpa only [U, Opens.coe_mk, inter_comm] using
      (isOpen_ball (x := x) (ε := 1)).inter_closure (t := (Ω : Set E))
  have hEq (x : E) : EqOn g (f x) (closure (Ω : Set E) ∩ ball x 1) := by
    intro y hy
    apply extendFrom_eq hy.1
    have hlim := ((hf x).continuousOn y (hsub x hy)).mono subset_closure
    have he : Tendsto v (𝓝[(U x : Set E)] y) (𝓝 (f x y)) :=
      hlim.tendsto.congr' ((hev x).eventuallyEq_of_mem self_mem_nhdsWithin).symm
    simp only [U, Opens.coe_mk] at he
    rw [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hy.2))] at he
    exact he
  refine ⟨g, contDiffOn_of_locally_contDiffOn fun x _ ↦
    ⟨ball x 1, isOpen_ball, mem_ball_self zero_lt_one, ((hf x).mono (hsub x)).congr (hEq x)⟩, ?_⟩
  exact huv.trans ((ae_restrict_mem Ω.isOpen.measurableSet).mono
    fun x hx ↦ (extendFrom_extends hv.continuousOn x hx).symm)

end ConvexDomain

end TauCeti
