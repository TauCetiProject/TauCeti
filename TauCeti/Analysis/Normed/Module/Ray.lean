/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ray

/-!
# Rays chained along a partition

Mathlib's `SameRay.trans` chains two ray relations `SameRay ℝ x y` and `SameRay ℝ y z` into
`SameRay ℝ x z`, provided the middle vector `y` vanishes only when `x` or `z` does. This file
iterates that step along a finite ordered partition of a real interval: if a path `w` in a real
normed space lies, on each piece of the partition, on the ray of its value at the end of that
piece, and the norm of `w` is nondecreasing, then every value of `w` lies on the ray of the final
value. Monotonicity of the norm supplies the side condition of `SameRay.trans`: a partition point
where `w` vanishes is preceded only by zeros.

The explicit-partition induction follows the pattern of the Apache-2.0
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
formalization, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, as used in
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.

## Main results

* `TauCeti.sameRay_of_partition_of_monotoneOn_norm`: rays chain through a partition when the norm
  is nondecreasing.
-/

public section

open Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {w : ℝ → F}

/-- **Rays chain through a partition.** If a path `w` in a real normed space lies, on each piece of
an ordered partition, on the ray of its value at the end of that piece, and its norm is
nondecreasing, then every value lies on the ray of the final value. Monotonicity of the norm rules
out a zero at a partition point preceded by a nonzero value. -/
theorem sameRay_of_partition_of_monotoneOn_norm {k : ℕ} (τ : Fin (k + 2) → ℝ)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hpiece : ∀ i : Fin (k + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ),
      SameRay ℝ (w t) (w (τ i.succ)))
    (hmono : MonotoneOn (fun t ↦ ‖w t‖) (Icc (τ 0) (τ (Fin.last (k + 1)))))
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (k + 1)))) :
    SameRay ℝ (w t) (w (τ (Fin.last (k + 1)))) := by
  induction k generalizing t with
  | zero => simpa using hpiece 0 t (by simpa using ht)
  | succ k ih =>
      have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr hτ
      have hlast : τ (Fin.last (k + 1)).succ = τ (Fin.last (k + 2)) := by rw [Fin.succ_last]
      rcases le_or_gt (τ (Fin.last (k + 1)).castSucc) t with hmt | htm
      · simpa only [hlast] using hpiece (Fin.last (k + 1)) t ⟨hmt, hlast ▸ ht.2⟩
      · have hm : τ (Fin.last (k + 1)).castSucc ∈ Icc (τ 0) (τ (Fin.last (k + 2))) :=
          ⟨hτmono (Fin.zero_le _), hτmono (Fin.le_last _)⟩
        have h₁ : SameRay ℝ (w t) (w (τ (Fin.last (k + 1)).castSucc)) :=
          ih (fun i ↦ τ i.castSucc)
            (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.castSucc)
            (fun i u hu ↦ by simpa only [Fin.succ_castSucc] using hpiece i.castSucc u hu)
            (hmono.mono (Icc_subset_Icc le_rfl (hτmono (Fin.le_last _)))) ⟨ht.1, htm.le⟩
        have h₂ : SameRay ℝ (w (τ (Fin.last (k + 1)).castSucc)) (w (τ (Fin.last (k + 2)))) := by
          simpa only [hlast] using hpiece (Fin.last (k + 1)) _ ⟨le_rfl, hτ _⟩
        refine h₁.trans h₂ fun hm0 ↦ Or.inl ?_
        have hle := hmono ht hm htm.le
        simp only [hm0, norm_zero] at hle
        exact norm_le_zero_iff.1 hle

end TauCeti
