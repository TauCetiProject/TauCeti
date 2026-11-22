/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import Mathlib.Topology.Algebra.InfiniteSum.Order
import TauCeti.Algebra.Order.Star.Basic

/-!
# Trace radicals of strictly positive countable atomic models

For a countable atomic model `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace pos q p hp n` with
strictly positive weights `p : ι → R` over a complete normed `StarOrderedRing` with
`OrderClosedTopology` and no zero divisors, the null space and trace radical coincide with
`RingHom.ker (signedChecked pos q)`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_eq_zero_iff`: null space of a
  strictly positive countable atomic trace.
* `TauCeti.TypeAHeckeAlgebra.traceRadical_countableAtomicTrace_eq_ker_signedChecked`: the trace
  radical of a strictly positive countable atomic trace is `RingHom.ker (signedChecked pos q)`.
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [PartialOrder R] [StarRing R]
  [StarOrderedRing R] [OrderClosedTopology R] [NoZeroDivisors R] {ι : Type*} [LinearOrder ι]
  (pos : ι → Prop) [DecidablePred pos] (q : Rˣ) [Fact (IsSelfAdjoint (q : R))]

/-- **Null space of a strictly positive countable atomic trace** over a complete normed
`StarOrderedRing` with `OrderClosedTopology` and no zero divisors:
`countableAtomicTrace (star x * x) = 0 ↔ signedChecked pos q x = 0`. -/
@[simp]
theorem countableAtomicTrace_star_mul_self_eq_zero_iff {p : ι → R} (hp : Summable fun a ↦ ‖p a‖)
    (hp0 : ∀ a, 0 < p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by
    rw [countableAtomicTrace_apply, map_mul (signedChecked pos q), hx]; simp⟩
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [countableAtomicTrace_apply] at hx
  have hsum : Summable fun w : Fin n → ι ↦
      signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) :=
    (summable_norm_signedChecked_mul_prod pos q hp n (star x * x)).of_norm
  have hnonneg (w : Fin n → ι) :
      0 ≤ signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) :=
    StarOrderedRing.mul_nonneg (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
      (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ (hp0 (w i)).le)
  ext w u
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  have hw : signedChecked pos q (star x * x) (single w 1) w * ∏ i, p (w i) = 0 :=
    le_antisymm ((hsum.le_tsum w fun _ _ ↦ hnonneg _).trans_eq hx) (hnonneg w)
  have hdiag : signedChecked pos q (star x * x) (single w 1) w = 0 :=
    (mul_eq_zero.mp hw).resolve_right (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp0 (w i)).ne')
  exact signedChecked_single_apply_eq_zero_of_star_mul_self pos q x hdiag u

/-- **Trace radical of a strictly positive countable atomic model** equals
`RingHom.ker (signedChecked)`. -/
theorem traceRadical_countableAtomicTrace_eq_ker_signedChecked {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 < p a) (n : ℕ) :
    (countableAtomicTrace pos q p hp n).traceRadical
        (countableAtomicTrace_mul_comm pos q p hp) =
      RingHom.ker (signedChecked pos q) := by
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ (countableAtomicTrace_star_mul_self_eq_zero_iff pos q hp hp0 x).mp
    (by rw [countableAtomicTrace_mul_comm]; exact hx (star x)), fun hx y ↦ ?_⟩
  rw [countableAtomicTrace_apply, map_mul (signedChecked pos q), hx]
  simp

end TauCeti.TypeAHeckeAlgebra
