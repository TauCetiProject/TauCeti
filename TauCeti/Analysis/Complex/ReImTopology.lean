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
(`TopologicalSpace.Opens.interior_inter_setOf_im_nonneg_eq_upperHalf`).
-/

public noncomputable section

open TopologicalSpace

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

namespace TauCeti

/-- A relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane has interior
`Ω ∩ {0 < im}` in `ℂ`: points on the real axis are not interior, since every neighbourhood meets
`{z | z.im < 0}`. -/
theorem interior_inter_setOf_im_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    interior (Ω ∩ {z : ℂ | 0 ≤ z.im}) = Ω ∩ {z : ℂ | 0 < z.im} := by
  rw [interior_inter, hΩ.interior_eq, Complex.interior_setOfPred_le_im]

end TauCeti

/-- The interior of the half-disc `Ω ∩ {0 ≤ im}`, as an open set, is the upper half of `Ω`. -/
theorem TopologicalSpace.Opens.interior_inter_setOf_im_nonneg_eq_upperHalf (Ω : Opens ℂ) :
    Opens.interior ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) = Ω.upperHalf :=
  Opens.ext ((TauCeti.interior_inter_setOf_im_nonneg Ω.isOpen).trans (Opens.coe_upperHalf Ω).symm)
