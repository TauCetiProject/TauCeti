/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Ray

/-!
# Rays chained along a partition

Mathlib's `SameRay.trans` chains two ray relations `SameRay R x y` and `SameRay R y z` into
`SameRay R x z`, provided the middle vector `y` vanishes only when `x` or `z` does. This file
iterates that step along a finite ordered partition of an interval in a linear order: if a map
`w` into an ordered scalar module lies, on each piece of the partition, on the ray of its value at
the end of that piece, and `w` vanishes at a point of the interval only if it vanishes at every
earlier point, then every value of `w` lies on the ray of the final value. The vanishing condition
supplies the side condition of `SameRay.trans` at each partition point.

For a map into a normed additive group, the vanishing condition follows from monotonicity of the
norm. No compatibility between the norm and scalar multiplication is needed.

The explicit-partition induction follows the pattern of the Apache-2.0
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
formalization, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, as used in
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.

## Main results

* `TauCeti.sameRay_of_partition`: rays chain through a partition when zeros of the map propagate
  backward.
* `TauCeti.sameRay_of_partition_of_monotoneOn_norm`: rays chain through a partition when the norm
  is nondecreasing.
-/

public section

open Set

namespace TauCeti

variable {R α F : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [LinearOrder α] {w : α → F}

/-- **Rays chain through a partition.** If a map `w` into an ordered scalar module lies, on each
piece of an ordered partition, on the ray of its value at the end of that piece, and `w` vanishes
at a point of the interval only if it vanishes at every earlier point of the interval, then every
value lies on the ray of the final value. -/
theorem sameRay_of_partition [AddCommMonoid F] [Module R F] {k : ℕ} (τ : Fin (k + 2) → α)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hpiece : ∀ i : Fin (k + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ),
      SameRay R (w t) (w (τ i.succ)))
    (hzero : ∀ ⦃s⦄, s ∈ Icc (τ 0) (τ (Fin.last (k + 1))) →
      ∀ ⦃u⦄, u ∈ Icc (τ 0) (τ (Fin.last (k + 1))) → s ≤ u → w u = 0 → w s = 0)
    {t : α} (ht : t ∈ Icc (τ 0) (τ (Fin.last (k + 1)))) :
    SameRay R (w t) (w (τ (Fin.last (k + 1)))) := by
  induction k generalizing t with
  | zero => simpa using hpiece 0 t (by simpa using ht)
  | succ k ih =>
      have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr hτ
      have hlast : τ (Fin.last (k + 1)).succ = τ (Fin.last (k + 2)) := by rw [Fin.succ_last]
      rcases le_or_gt (τ (Fin.last (k + 1)).castSucc) t with hmt | htm
      · simpa only [hlast] using hpiece (Fin.last (k + 1)) t ⟨hmt, hlast ▸ ht.2⟩
      · have hml : τ (Fin.last (k + 1)).castSucc ≤ τ (Fin.last (k + 2)) :=
          hτmono (Fin.le_last _)
        have hm : τ (Fin.last (k + 1)).castSucc ∈ Icc (τ 0) (τ (Fin.last (k + 2))) :=
          ⟨hτmono (Fin.zero_le _), hml⟩
        have h₁ : SameRay R (w t) (w (τ (Fin.last (k + 1)).castSucc)) :=
          ih (fun i ↦ τ i.castSucc)
            (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.castSucc)
            (fun i u hu ↦ by simpa only [Fin.succ_castSucc] using hpiece i.castSucc u hu)
            (fun _ hs _ hu ↦ hzero ⟨hs.1, hs.2.trans hml⟩ ⟨hu.1, hu.2.trans hml⟩)
            ⟨ht.1, htm.le⟩
        have h₂ : SameRay R (w (τ (Fin.last (k + 1)).castSucc)) (w (τ (Fin.last (k + 2)))) := by
          simpa only [hlast] using hpiece (Fin.last (k + 1)) _ ⟨le_rfl, hτ _⟩
        exact h₁.trans h₂ fun hm0 ↦ Or.inl (hzero ht hm htm.le hm0)

/-- **Rays chain through a partition, normed form.** If a map `w` into a normed additive group with
an ordered scalar module structure lies, on each piece of an ordered partition, on the ray of its
value at the end of that piece, and its norm is nondecreasing, then every value lies on the ray of
the final value. -/
theorem sameRay_of_partition_of_monotoneOn_norm [NormedAddCommGroup F] [Module R F] {k : ℕ}
    (τ : Fin (k + 2) → α) (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hpiece : ∀ i : Fin (k + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ),
      SameRay R (w t) (w (τ i.succ)))
    (hmono : MonotoneOn (fun t ↦ ‖w t‖) (Icc (τ 0) (τ (Fin.last (k + 1)))))
    {t : α} (ht : t ∈ Icc (τ 0) (τ (Fin.last (k + 1)))) :
    SameRay R (w t) (w (τ (Fin.last (k + 1)))) :=
  sameRay_of_partition τ hτ hpiece (fun _ hs _ hu hsu hu0 ↦ by simpa [hu0] using hmono hs hu hsu)
    ht

end TauCeti
