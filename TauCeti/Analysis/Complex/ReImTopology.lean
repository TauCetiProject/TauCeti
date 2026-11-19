/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Sets.Opens

/-!
# Upper halves of open planar sets

The open upper half `W ∩ {0 < im}` of an open set `W ⊆ ℂ` is packaged as an open set,
`TopologicalSpace.Opens.upperHalf`. A relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper
half-plane has interior `Ω ∩ {0 < im}` (`TauCeti.interior_inter_setOf_im_nonneg`), which as an
open set is the upper half of `Ω`
(`TopologicalSpace.Opens.interior_inter_setOf_im_nonneg_eq_upperHalf`). A local property holds on
`Ω ∩ {0 ≤ im}` once it holds on the upper half of `Ω` and on the half-discs centred on the real
axis (`TauCeti.inter_setOf_im_nonneg_induction`).
-/

public noncomputable section

open TopologicalSpace
open scoped Topology

/-- The open upper half `W ∩ {0 < im}` of an open planar set `W`. -/
def TopologicalSpace.Opens.upperHalf (W : Opens ℂ) : Opens ℂ :=
  ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
    W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩

@[simp]
theorem TopologicalSpace.Opens.coe_upperHalf (W : Opens ℂ) :
    (W.upperHalf : Set ℂ) = (W : Set ℂ) ∩ {z : ℂ | 0 < z.im} := (rfl)

@[simp]
theorem TopologicalSpace.Opens.mem_upperHalf {W : Opens ℂ} {z : ℂ} :
    z ∈ W.upperHalf ↔ z ∈ W ∧ 0 < z.im :=
  (Iff.rfl)

/-- Taking upper halves is monotone. -/
theorem TopologicalSpace.Opens.upperHalf_mono {V W : Opens ℂ} (h : V ≤ W) :
    V.upperHalf ≤ W.upperHalf :=
  fun _ hz => Opens.mem_upperHalf.2 ⟨h (Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2⟩

/-- The upper half of an open set with compact closure has compact closure. -/
theorem TopologicalSpace.Opens.isCompact_closure_upperHalf {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) : IsCompact (closure (W.upperHalf : Set ℂ)) :=
  hWc.of_isClosed_subset isClosed_closure
    (closure_mono (by rw [Opens.coe_upperHalf]; exact Set.inter_subset_left))

/-- The upper half of an open planar set lies in its closed upper half. -/
theorem TopologicalSpace.Opens.coe_upperHalf_subset (W : Opens ℂ) :
    (W.upperHalf : Set ℂ) ⊆ (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im} :=
  fun _ hz => ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩

namespace TauCeti

/-- A relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane has interior
`Ω ∩ {0 < im}` in `ℂ`: points on the real axis are not interior, since every neighbourhood meets
`{z | z.im < 0}`. -/
theorem interior_inter_setOf_im_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    interior (Ω ∩ {z : ℂ | 0 ≤ z.im}) = Ω ∩ {z : ℂ | 0 < z.im} := by
  rw [interior_inter, hΩ.interior_eq, Complex.interior_setOfPred_le_im]

/-- **Induction on half-discs.** A property `P` of subsets of `ℂ` holds on `Ω ∩ {0 ≤ im}` if it
can be checked on relative neighbourhoods of each point, and holds on the upper half
`Ω ∩ {0 < im}` and on the half-discs `ball x r ∩ {0 ≤ im}` centred on the real axis inside `Ω`. -/
theorem inter_setOf_im_nonneg_induction {Ω : Opens ℂ} (P : Set ℂ → Prop)
    (hP : (∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im},
      ∃ V ∈ 𝓝[(Ω : Set ℂ) ∩ {z | 0 ≤ z.im}] z, P V) → P ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hint : P Ω.upperHalf)
    (hbd : ∀ x r : ℝ, 0 < r → Metric.ball (x : ℂ) r ⊆ Ω →
      P (Metric.ball (x : ℂ) r ∩ {z | 0 ≤ z.im})) :
    P ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  refine hP fun z hz => ?_
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
  rcases hz.2.lt_or_eq with hz0 | hz0
  · exact ⟨Ω.upperHalf, mem_nhdsWithin_of_mem_nhds (Ω.upperHalf.isOpen.mem_nhds
      (Opens.mem_upperHalf.2 ⟨hz.1, hz0⟩)), hint⟩
  · have hzx : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen _ (hzx.symm ▸ hz.1)
    exact ⟨Metric.ball (z.re : ℂ) r ∩ {z | 0 ≤ z.im}, mem_nhdsWithin.2
      ⟨Metric.ball (z.re : ℂ) r, Metric.isOpen_ball, hzx ▸ Metric.mem_ball_self hr,
        fun w hw => ⟨hw.1, hw.2.2⟩⟩, hbd z.re r hr hrΩ⟩

end TauCeti

/-- The interior of the half-disc `Ω ∩ {0 ≤ im}`, as an open set, is the upper half of `Ω`. -/
theorem TopologicalSpace.Opens.interior_inter_setOf_im_nonneg_eq_upperHalf (Ω : Opens ℂ) :
    Opens.interior ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) = Ω.upperHalf :=
  Opens.ext ((TauCeti.interior_inter_setOf_im_nonneg Ω.isOpen).trans (Opens.coe_upperHalf Ω).symm)
