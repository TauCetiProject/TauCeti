/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
import TauCeti.Analysis.Normed.Algebra.Amenable.Bidual
import TauCeti.Analysis.Normed.Module.Dual.Bilinear
import TauCeti.Analysis.Normed.Module.Dual.Goldstine
import TauCeti.Analysis.Normed.Ring.ApproximateUnit

/-!
# Bounded approximate identities for amenable normed algebras

Every amenable normed algebra `A` over `ℝ` or `ℂ` has a bounded two-sided approximate identity
(`TauCeti.IsAmenable.exists_isApproximateUnit`). Applying universe-polymorphic bidual innerness
(`TauCeti.IsAmenable.exists_eq_bidual_dualAction_sub_dualAction`) to the canonical inclusion
`J_A : A →L[𝕜] A**` for the one-sided actions `(mul, 0)` and `(0, mul.flip)`, bidual norm
approximation (`StrongDual.exists_neBot_eventually_norm_le_and_forall_tendsto`) produces bounded
right and left approximate identities, which combine via Dixon's combination
(`exists_isApproximateUnit_of_left_of_right`).

## Main results

* `TauCeti.IsAmenable.exists_isApproximateUnit`: every amenable normed algebra over `ℝ` or `ℂ` has
  a bounded two-sided approximate identity.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.1 and §2.2.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.8–2.9.
-/

public section

noncomputable section

universe u v

open Filter NormedSpace Topology ContinuousLinearMap

namespace TauCeti

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

section ApproximateUnit

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded right approximate identity. -/
private theorem IsAmenable.exists_tendsto_mul_left (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a) := by
  -- Apply bidual innerness to `J_A : A →L[𝕜] A**` for the one-sided actions `(mul, 0)`.
  have hD (a b : A) : inclusionInDoubleDual 𝕜 A (a * b) =
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a (inclusionInDoubleDual 𝕜 A b) +
        dualAction (dualAction (0 : A →L[𝕜] A →L[𝕜] A)) b (inclusionInDoubleDual 𝕜 A a) := by
    ext f; simp
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_bidual_dualAction_sub_dualAction
    (fun a b x ↦ by simp [mul_assoc]) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (inclusionInDoubleDual 𝕜 A) hD
  obtain ⟨l, hl, hle, ht⟩ := Φ.exists_neBot_eventually_norm_le_and_forall_tendsto
    (fun a ↦ ContinuousLinearMap.mul 𝕜 A a) id (fun a f ↦ by
      have ha := congr($(hΦ a) f)
      simpa only [sub_apply, dualAction_dualAction_apply_apply, zero_apply, comp_zero, map_zero,
        sub_zero, dual_def, id_eq] using ha.symm) le_rfl
  exact ⟨‖Φ‖, l, hl, hle, fun a ↦ (ht a).congr fun e ↦ mul_apply' 𝕜 A a e⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded left approximate identity. -/
private theorem IsAmenable.exists_tendsto_mul_right (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a) := by
  -- Apply bidual innerness to `-J_A : A →L[𝕜] A**` for the one-sided actions `(0, mul.flip)`.
  have hD (a b : A) : (-inclusionInDoubleDual 𝕜 A) (a * b) =
      dualAction (dualAction (0 : A →L[𝕜] A →L[𝕜] A)) a ((-inclusionInDoubleDual 𝕜 A) b) +
        dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) b
          ((-inclusionInDoubleDual 𝕜 A) a) := by
    ext f; simp
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_bidual_dualAction_sub_dualAction
    (fun _ _ _ ↦ by simp) (fun a b x ↦ by simp [mul_assoc]) (fun _ _ _ ↦ by simp)
    (-inclusionInDoubleDual 𝕜 A) hD
  obtain ⟨l, hl, hle, ht⟩ := Φ.exists_neBot_eventually_norm_le_and_forall_tendsto
    (fun a ↦ (ContinuousLinearMap.mul 𝕜 A).flip a) id (fun a f ↦ by
      have ha := congr($(hΦ a) f)
      simpa only [neg_apply, sub_apply, dualAction_dualAction_apply_apply, zero_apply, comp_zero,
        map_zero, zero_sub, neg_inj, dual_def, id_eq] using ha.symm) le_rfl
  exact ⟨‖Φ‖, l, hl, hle, fun a ↦ (ht a).congr fun _ ↦ by simp⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded two-sided approximate identity. -/
theorem IsAmenable.exists_isApproximateUnit (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C := by
  obtain ⟨C, hleft⟩ := h.exists_tendsto_mul_right
  obtain ⟨D, hright⟩ := h.exists_tendsto_mul_left
  exact ⟨C + D + C * D, exists_isApproximateUnit_of_left_of_right hleft hright⟩

end ApproximateUnit

end TauCeti
