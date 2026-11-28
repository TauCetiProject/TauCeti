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
`RingHom.ker (signedChecked pos q)`
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_eq_zero_iff`,
`TauCeti.TypeAHeckeAlgebra.traceRadical_countableAtomicTrace_eq_ker_signedChecked`).
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
@[simp] theorem countableAtomicTrace_star_mul_self_eq_zero_iff {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 < p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [countableAtomicTrace_apply, hx]⟩
  nontriviality R; rw [countableAtomicTrace_apply] at hx
  have hnonneg (w : Fin n → ι) : 0 ≤ signedChecked pos q (star x * x) (single w 1) w *
      ∏ i, p (w i) := StarOrderedRing.mul_nonneg
    (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
    (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ (hp0 (w i)).le)
  ext w u; simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  exact signedChecked_single_apply_eq_zero_of_star_mul_self pos q x ((mul_eq_zero.mp (le_antisymm ((
    (summable_norm_signedChecked_mul_prod pos q hp n (star x * x)).of_norm.le_tsum w fun _ _ ↦
      hnonneg _).trans_eq hx) (hnonneg w))).resolve_right (Finset.prod_ne_zero_iff.mpr fun i _ ↦
        (hp0 (w i)).ne')) u

/-- **Trace radical of a strictly positive countable atomic model** equals
`RingHom.ker (signedChecked)`. -/
theorem traceRadical_countableAtomicTrace_eq_ker_signedChecked {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 < p a) (n : ℕ) :
    (countableAtomicTrace pos q p hp n).traceRadical (countableAtomicTrace_mul_comm pos q p hp) =
      RingHom.ker (signedChecked pos q) := by
  ext x; simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  exact ⟨fun hx ↦ (countableAtomicTrace_star_mul_self_eq_zero_iff pos q hp hp0 x).mp (by
      rw [countableAtomicTrace_mul_comm]; exact hx (star x)),
    fun hx y ↦ by simp [countableAtomicTrace_apply, hx]⟩

end TauCeti.TypeAHeckeAlgebra
