/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import TauCeti.Algebra.Order.Star.Basic

/-!
# Trace radicals of strictly positive finite atomic models

For a finite atomic model `TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n` with strictly positive
weights `p : ι → R` over a `StarOrderedRing` without zero divisors, the null space and trace
radical coincide with `RingHom.ker (signedChecked pos q)`
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_star_mul_self_eq_zero_iff`,
`TauCeti.TypeAHeckeAlgebra.traceRadical_atomicTrace_eq_ker_signedChecked`).
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  [NoZeroDivisors R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) [Fact (IsSelfAdjoint (q : R))] {n : ℕ}

/-- **Null space of a strictly positive atomic trace** over a `StarOrderedRing` without zero
divisors: `atomicTrace (star x * x) = 0 ↔ signedChecked pos q x = 0`. -/
@[simp] theorem atomicTrace_star_mul_self_eq_zero_iff [Finite ι] {p : ι → R} (hp : ∀ a, 0 < p a)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n (star x * x) = 0 ↔ signedChecked pos q x = 0 := by
  cases nonempty_fintype ι; refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [atomicTrace_apply, hx]⟩
  nontriviality R; rw [atomicTrace_eq_sum] at hx
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ StarOrderedRing.mul_nonneg
    (signedChecked_star_mul_self_single_apply_nonneg pos q x w)
    (Finset.prod_nonneg_of_starOrderedRing fun i _ ↦ (hp (w i)).le)).mp hx
  ext w u; simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearMap.zero_apply,
    Finsupp.coe_zero, Pi.zero_apply]
  exact signedChecked_single_apply_eq_zero_of_star_mul_self pos q x ((mul_eq_zero.mp (hterm w
    (Finset.mem_univ w))).resolve_right (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hp (w i)).ne')) u

/-- **Trace radical of a strictly positive atomic model** equals `RingHom.ker (signedChecked)`. -/
theorem traceRadical_atomicTrace_eq_ker_signedChecked [Finite ι] {p : ι → R} (hp : ∀ a, 0 < p a)
    (n : ℕ) : (atomicTrace pos q p n).traceRadical (atomicTrace_mul_comm pos q p) =
      RingHom.ker (signedChecked pos q) := by
  ext x; simp only [LinearMap.mem_traceRadical, RingHom.mem_ker]
  exact ⟨fun hx ↦ (atomicTrace_star_mul_self_eq_zero_iff pos q hp x).mp (by
    rw [atomicTrace_mul_comm]; exact hx (star x)), fun hx y ↦ by simp [atomicTrace_apply, hx]⟩

end TauCeti.TypeAHeckeAlgebra
