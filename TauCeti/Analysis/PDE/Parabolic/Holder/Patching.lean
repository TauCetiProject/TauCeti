/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Bilinear
public import TauCeti.Analysis.Holder.Patching

/-!
# Patching local bounds for order-two parabolic Hölder norms

The order-two norm of the bounded parabolic Hölder space `C_b^{2+α,1+α/2}` on a slab
`E × [a, b]` is controlled by local data. Let `r > 0`. If around every point `p` of the slab the
map `u` agrees, on the parabolic ball of radius `r` about `p`, with a map of norm at most `M`,
then

`‖u‖ ≤ (6 + 4 r^(-α)) M`.

The derivative fields are local (`TauCeti.ParabolicC2HolderSpace.eqOn_spatialFDerivL_of_eqOn`
and its companions), so the supremum norms of the four fields are bounded pointwise by the local
pieces, and the parabolic Hölder seminorms of the Hessian and of the time derivative by the
patching estimate for bounded Hölder functions (`TauCeti.HolderSpace.norm_le_of_forall_eqOn_ball`).

The local pieces are usually localizations `χ_p u` by space-time cutoffs `χ_p` equal to one near
`p`, such as the cutoffs in `C_b^{2+α,1+α/2}` centred at every point of the slab given by
`TauCeti.ParabolicC2HolderSpace.exists_cutoff_family`. With them, a bound on `‖χ_p u‖` uniform in
the centre `p` bounds `‖u‖` with a constant depending only on `α` and the cutoff radius. This is
how a global parabolic Schauder estimate is assembled from estimates of localizations, to which a
constant-coefficient estimate applies after freezing the coefficients at `p`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.norm_le_of_forall_eqOn_ball`: the patching estimate.
* `TauCeti.ParabolicC2HolderSpace.norm_le_of_forall_norm_compParabolicC2Holder₂_le`: the patching
  estimate for localizations by cutoffs.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (passing from local to global Schauder estimates).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8 (parabolic Schauder estimates).
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Metric ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- **Patching local bounds for the order-two parabolic Hölder norm.** Let `r > 0`. If around
every point `p` of the slab the map `f` agrees, on the parabolic ball of radius `r` about `p`,
with a map of norm at most `M`, then `‖f‖ ≤ (6 + 4 r^(-α)) M`. -/
theorem norm_le_of_forall_eqOn_ball {f : ParabolicC2HolderSpace α E F hab} {r M : ℝ}
    (hr : 0 < r) (h : ∀ p, ∃ g : ParabolicC2HolderSpace α E F hab, ‖g‖ ≤ M ∧ EqOn f g (ball p r)) :
    ‖f‖ ≤ (6 + 4 * r ^ (-(α : ℝ))) * M := by
  have : Nonempty (slab (E := E) a b) := ⟨slabMk 0 ⟨a, left_mem_Icc.2 hab.le⟩⟩
  have hM : 0 ≤ M := by
    obtain ⟨g, hg, -⟩ := h (Classical.arbitrary _)
    exact (norm_nonneg g).trans hg
  -- At its centre, each field of `f` is the corresponding field of the local piece.
  have hval : ‖valueL f‖ ≤ M := (BoundedContinuousFunction.norm_le hM).2 fun p ↦ by
    obtain ⟨g, hg, hfg⟩ := h p
    rw [valueL_apply, hfg (mem_ball_self hr)]
    exact ((valueL g).norm_coe_le_norm p).trans ((norm_valueL_le g).trans hg)
  have hgrad : ‖spatialFDerivL f‖ ≤ M := (BoundedContinuousFunction.norm_le hM).2 fun p ↦ by
    obtain ⟨g, hg, hfg⟩ := h p
    rw [eqOn_spatialFDerivL_of_eqOn isOpen_ball hfg (mem_ball_self hr)]
    refine ((spatialFDerivL g).norm_coe_le_norm p).trans (le_trans ?_ hg)
    rw [norm_eq g]
    linarith [norm_nonneg (valueL g), norm_nonneg (spatialSecondFDerivL g),
      norm_nonneg (timeDerivL g)]
  -- The two Hölder fields are patched as bounded Hölder functions.
  have hxx : ‖spatialSecondFDerivL f‖ ≤ 2 * (1 + r ^ (-(α : ℝ))) * M :=
    HolderSpace.norm_le_of_forall_eqOn_ball hr fun p ↦ by
      obtain ⟨g, hg, hfg⟩ := h p
      exact ⟨spatialSecondFDerivL g, (norm_spatialSecondFDerivL_le g).trans hg,
        eqOn_spatialSecondFDerivL_of_eqOn isOpen_ball hfg⟩
  have ht : ‖timeDerivL f‖ ≤ 2 * (1 + r ^ (-(α : ℝ))) * M :=
    HolderSpace.norm_le_of_forall_eqOn_ball hr fun p ↦ by
      obtain ⟨g, hg, hfg⟩ := h p
      exact ⟨timeDerivL g, (norm_timeDerivL_le g).trans hg,
        eqOn_timeDerivL_of_eqOn isOpen_ball hfg⟩
  rw [norm_eq]
  linarith

/-- **Patching localizations by cutoffs.** Let `B` be a bilinear map with `B 1 y = y`, such as
scalar multiplication or the multiplication of `ℝ`, and let each scalar map `χ p` be one on the
parabolic ball of radius `r > 0` about `p`. If the localizations `B (χ p) f` all have norm at most
`M`, then `‖f‖ ≤ (6 + 4 r^(-α)) M`. -/
theorem norm_le_of_forall_norm_compParabolicC2Holder₂_le (hα : α ≤ 1)
    (B : ℝ →L[ℝ] F →L[ℝ] F) (hB : ∀ y, B 1 y = y) {r M : ℝ} (hr : 0 < r)
    {χ : slab (E := E) a b → ParabolicC2HolderSpace α E ℝ hab}
    (hχ : ∀ p, ∀ q ∈ ball p r, χ p q = 1) {f : ParabolicC2HolderSpace α E F hab}
    (hM : ∀ p, ‖B.compParabolicC2Holder₂ hα (χ p) f‖ ≤ M) :
    ‖f‖ ≤ (6 + 4 * r ^ (-(α : ℝ))) * M :=
  norm_le_of_forall_eqOn_ball hr fun p ↦
    ⟨_, hM p, fun q hq ↦ by rw [ContinuousLinearMap.compParabolicC2Holder₂_apply, hχ p q hq, hB]⟩

end TauCeti.ParabolicC2HolderSpace
