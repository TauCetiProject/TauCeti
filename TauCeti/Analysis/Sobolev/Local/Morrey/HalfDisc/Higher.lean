/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar
import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
import TauCeti.Topology.MetricSpace.Holder

/-!
# Higher-order continuity and local bounds on half-discs

Let `Ω ⊆ ℂ` be open and let `U = Ω ∩ {0 ≤ im}`. The half-disc Sobolev class
`TauCeti.MemWkpLoc p U k` tests weak derivatives in the interior and imposes local bounds on
compact sets that may meet the real axis. For `k p > 2` and `p ≥ 1`, its members have continuous
representatives up to that axis, including when `p ≤ 2` and higher derivatives are needed.

For real-valued maps and finite `q > 2`, this file also gives quantitative local bounds for every
derivative through order `j` of a `W^{j+1,q}` map on a half-disc. A representative extends as a
`Cʲ` map across the axis; its derivatives and their Hölder constants are bounded by a constant
times the Sobolev norm on the open half-disc. The bounds pass to the real segment by continuity.
The open `Cʲ` representative is supplied by
`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq_inter_setOf_im_nonneg` in the half-disc Morrey theory.

## Main declarations

* `TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg`: continuous
  representatives when `k p > 2`.
* `TauCeti.MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg`:
  local derivative and Hölder bounds through the real axis, with constants controlled by the
  open-half-disc Sobolev norm.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.1.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19.
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {k : ℕ} {u : ℂ → F}

variable [FiniteDimensional ℝ F]

/-- **Morrey for `kp > 2` up to the real axis: continuous representatives.** If `1 ≤ p ≤ ∞` and
`2 < k p`, every `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` agrees almost everywhere on `Ω ∩ {0 ≤ im}` with
a map continuous on `Ω ∩ {0 ≤ im}`. For `p ≤ 2` this needs `k ≥ 2`. -/
theorem MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul_inter_setOf_im_nonneg (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    ∃ g : ℂ → F, ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] g := by
  have hSV := Ω.inter_setOf_im_nonneg_subset_reflectionCore
  have hV := hu.planarReflection_higherReflectionCoeff_reflectionCore hp
  obtain ⟨g, hg, hrg⟩ := hV.exists_continuousOn_ae_eq_of_two_lt_mul hp hkp
  refine ⟨g, hg.mono hSV, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSV hrg,
    ae_restrict_mem (Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const
      Complex.measurable_im))] with z hz hzS
  rw [← hz, planarReflection_of_nonneg _ _ hzS.2]

/-! ### Local bounds -/

variable {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- **Local `C^{j,1-2/q}` bounds on a half-disc, up to the real axis.** For `2 < q < ∞`, a real
centre `x` and a radius `s` there is a constant `K` such that, for every open `Ω` containing the
closure of `ball x s`, every real `u ∈ MemWkpLoc q (Ω ∩ {0 ≤ im}) (j + 1)` is represented on the
open half-disc `ball x s ∩ {0 < im}` by some `v` in `W^{j+1,q}` of it, and agrees almost everywhere
on the half-disc `ball x s ∩ {0 ≤ im}` with a map `g` that is `Cʲ` on an open neighbourhood of it,
whose derivatives of order `i ≤ j` are bounded by `K ‖v‖` and Hölder of exponent `1 - 2 / q` with
constant `K ‖v‖` on `ball x s ∩ {0 ≤ im}`, including its segment of the real axis. -/
theorem MemWkpLoc.exists_contDiffOn_holderOnWith_iteratedFDeriv_ball_inter_setOf_im_nonneg
    (hq : 2 < q) (x s : ℝ) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ {Ω : Opens ℂ} (u : ℂ → ℝ), closure (ball (x : ℂ) s) ⊆ Ω →
      MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (j + 1) u →
      ∃ v : Wkp volume (Opens.upperHalf ⟨ball (x : ℂ) s, isOpen_ball⟩) q (j + 1),
        Wkp.value (j + 1) v =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 < z.im})] u ∧
        ∃ V : Opens ℂ, ball (x : ℂ) s ∩ {z | 0 ≤ z.im} ⊆ V ∧ ∃ g : ℂ → ℝ, ContDiffOn ℝ j g V ∧
          u =ᵐ[volume.restrict (ball (x : ℂ) s ∩ {z | 0 ≤ z.im})] g ∧ ∀ i ≤ j,
            (∀ z ∈ ball (x : ℂ) s ∩ {z | 0 ≤ z.im}, ‖iteratedFDeriv ℝ i g z‖ ≤ K * ‖v‖) ∧
              HolderOnWith (K * ‖v‖₊) (1 - 2 / q) (iteratedFDeriv ℝ i g)
                (ball (x : ℂ) s ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨K, hK⟩ := Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_complexBall_upperHalf x s hq j
  refine ⟨K, fun {Ω} u hsub hu => ?_⟩
  set B := ball (x : ℂ) s
  set O := B ∩ {z | 0 < z.im}
  -- The bounds hold for the representative `g₁` of the Sobolev space of the open half-disc `O`.
  obtain ⟨v, hv⟩ := hu.exists_wkp_upperHalf (W := ⟨B, isOpen_ball⟩)
    ((isCompact_closedBall _ s).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
    hsub
  simp only [Opens.coe_upperHalf, Opens.coe_mk] at hv
  obtain ⟨g₁, hg₁, hvg₁, hb⟩ := hK v
  -- A representative `g` that is `Cʲ` across the real axis agrees with `g₁` on `O`, with all its
  -- derivatives, and the bounds pass to the closure of `O` by continuity.
  obtain ⟨V, hSV, -, g, hg, hug⟩ :=
    hu.exists_contDiffOn_ae_eq_inter_setOf_im_nonneg (by exact_mod_cast hq)
  have hTS : B ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ (subset_closure.trans hsub)
  have hOT : O ⊆ B ∩ {z | 0 ≤ z.im} := by
    simpa only [O, Opens.coe_upperHalf, Opens.coe_mk] using
      Opens.coe_upperHalf_subset (⟨B, isOpen_ball⟩ : Opens ℂ)
  have hO : IsOpen O := by
    simpa only [O, Opens.coe_upperHalf, Opens.coe_mk] using
      (Opens.upperHalf ⟨B, isOpen_ball⟩).isOpen
  have hOV : O ⊆ V := (hOT.trans hTS).trans hSV
  have hug₁ : u =ᵐ[volume.restrict O] g₁ := hv.symm.trans hvg₁
  have hug' : u =ᵐ[volume.restrict O] g := ae_restrict_of_ae_restrict_of_subset (hOT.trans hTS) hug
  have hgg₁ : EqOn g g₁ O := Measure.eqOn_open_of_ae_eq (hug'.symm.trans hug₁) hO
    (hg.continuousOn.mono hOV) hg₁.continuousOn
  have heq (i : ℕ) : EqOn (iteratedFDeriv ℝ i g) (iteratedFDeriv ℝ i g₁) O := fun z hz =>
    ((Filter.eventuallyEq_of_mem (hO.mem_nhds hz) hgg₁).iteratedFDeriv ℝ i).eq_of_nhds
  have hcl : B ∩ {z | 0 ≤ z.im} ⊆ closure O := fun z hz => by
    have h := subset_closure_interior_inter_setOf_im_nonneg (Ω := B) isOpen_ball hz
    rwa [interior_inter_setOf_im_nonneg isOpen_ball] at h
  have hcont {i : ℕ} (hi : i ≤ j) (z : ℂ) (hz : z ∈ B ∩ {z | 0 ≤ z.im}) :
      ContinuousAt (iteratedFDeriv ℝ i g) z :=
    (ContinuousOn.continuousOn_iteratedFDeriv hg V.isOpen (by exact_mod_cast hi)).continuousAt
      (V.isOpen.mem_nhds (hSV (hTS hz)))
  refine ⟨v, hv, V, hTS.trans hSV, g, hg, ae_restrict_of_ae_restrict_of_subset hTS hug,
    fun i hi => ⟨fun z hz => ?_, ?_⟩⟩
  · exact ContinuousWithinAt.closure_le (hcl hz) (hcont hi z hz).norm.continuousWithinAt
      continuousWithinAt_const fun y hy => heq i hy ▸ (hb i hi).1 y hy
  · refine HolderOnWith.of_subset_closure (fun a ha b hb' => ?_) hcl
      (fun z hz => (hcont hi z hz).continuousWithinAt)
    rw [heq i ha, heq i hb']
    exact (hb i hi).2 a ha b hb'

end TauCeti
