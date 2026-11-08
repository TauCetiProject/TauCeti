/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import TauCeti.LinearAlgebra.Ray

/-!
# Rays chained along a partition, normed form

`TauCeti.sameRay_of_partition` chains ray relations along a finite ordered partition of an
interval in a linear order, provided a map `w` vanishes at a point of the interval only if it
vanishes at every earlier point. For a map into a normed additive group, this vanishing condition
follows from monotonicity of the norm. No compatibility between the norm and scalar
multiplication is needed.

## Main results

* `TauCeti.sameRay_of_partition_of_monotoneOn_norm`: rays chain through a partition when the norm
  is nondecreasing.
-/

public section

open Set

namespace TauCeti

variable {R α F : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [LinearOrder α] [NormedAddCommGroup F] [Module R F] {w : α → F}

/-- **Rays chain through a partition, normed form.** If a map `w` into a normed additive group with
an ordered scalar module structure lies, on each piece of an ordered partition, on the ray of its
value at the end of that piece, and its norm is nondecreasing, then every value lies on the ray of
the final value. -/
theorem sameRay_of_partition_of_monotoneOn_norm {k : ℕ} (τ : Fin (k + 2) → α)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hpiece : ∀ i : Fin (k + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ),
      SameRay R (w t) (w (τ i.succ)))
    (hmono : MonotoneOn (fun t ↦ ‖w t‖) (Icc (τ 0) (τ (Fin.last (k + 1)))))
    {t : α} (ht : t ∈ Icc (τ 0) (τ (Fin.last (k + 1)))) :
    SameRay R (w t) (w (τ (Fin.last (k + 1)))) :=
  sameRay_of_partition τ hτ hpiece (fun _ hs _ hu hsu hu0 ↦ by simpa [hu0] using hmono hs hu hsu)
    ht

end TauCeti
