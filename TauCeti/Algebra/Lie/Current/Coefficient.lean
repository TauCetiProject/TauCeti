/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Basic
public import TauCeti.RingTheory.LaurentSeries.Multiplication

/-!
# Coefficients and finite cutoffs of current brackets

The bracket of formal currents is coefficient convolution. For currents `u` and `v` of orders
at least `M` and `N`, its coefficient at `n` is the finite sum
`∑ i ∈ Finset.Icc M (n - N), ⁅uᵢ, vₙ₋ᵢ⁆`. This works over a commutative ring, without freeness
or finite generation of the coefficient Lie algebra.

Truncating both inputs sufficiently far out preserves the bracket below a prescribed order.
The estimates keep track of the lower orders of both inputs: a fixed output cutoff generally
requires different input cutoffs when negative modes occur. These estimates allow Lie laws
for actions defined by finite truncation to be checked on polynomial currents.

## References

* V. Kac, *Infinite-Dimensional Lie Algebras*, Chapter 7 (current algebras).
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

-- Match the coefficientwise scalar action used to define formal currents.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- The coefficient of a current bracket is a finite convolution over the interval specified
by lower order bounds on its inputs. -/
theorem coeff_lie_eq_sum {M N : ℤ} {u v : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L M) (hv : v ∈ orderSubmodule R L N) (n : ℤ) :
    coeff R L n ⁅u, v⁆ =
      ∑ i ∈ Finset.Icc M (n - N), ⁅coeff R L i u, coeff R L (n - i) v⁆ := by
  classical
  rw [orderSubmodule_def] at hu hv
  induction hu, hv using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
    obtain ⟨f, x, hf, rfl⟩ := hu
    obtain ⟨g, y, hg, rfl⟩ := hv
    simp only [LieAlgebra.ExtendScalars.bracket_tmul, coeff_tmul,
      LaurentSeries.coeff_mul_eq_sum hf hg, Finset.sum_smul, smul_lie, lie_smul, smul_smul,
      mul_comm]
  | zero_left v _ => simp
  | zero_right u _ => simp
  | add_left u u' v _ _ _ hu hu' =>
    simp only [add_lie, map_add, hu, hu', Finset.sum_add_distrib]
  | add_right u v v' _ _ _ hv hv' =>
    simp only [lie_add, map_add, hv, hv', Finset.sum_add_distrib]
  | smul_left r u v _ _ h =>
    simp only [smul_lie, map_smul, h, Finset.smul_sum]
  | smul_right r u v _ _ h =>
    simp only [lie_smul, map_smul, h, Finset.smul_sum]

/-- Truncating both inputs preserves their bracket modulo currents of order at least `T`,
provided the input cutoffs account for the other input's lower order. -/
theorem lie_ofLoop_trunc_sub_mem_orderSubmodule {M N P Q T : ℤ}
    {u v : currentAlgebra R L} (hu : u ∈ orderSubmodule R L M)
    (hv : v ∈ orderSubmodule R L N) (hPN : T ≤ P + N)
    (hMQ : T ≤ M + Q) :
    ⁅ofLoop R L (trunc R L P u), ofLoop R L (trunc R L Q v)⁆ - ⁅u, v⁆ ∈
      orderSubmodule R L T := by
  have hPu := ofLoop_trunc_sub_mem_orderSubmodule R L P u
  have hQv := ofLoop_trunc_sub_mem_orderSubmodule R L Q v
  have huP := ofLoop_trunc_mem_orderSubmodule R L P hu
  have h := (orderSubmodule R L T).add_mem
    (orderSubmodule_antitone R L hMQ (lie_mem_orderSubmodule R L huP hQv))
    (orderSubmodule_antitone R L hPN (lie_mem_orderSubmodule R L hPu hv))
  simpa only [lie_sub, sub_lie, sub_add_sub_cancel] using h

/-- Below the error bound, a current bracket and its polynomial approximation have the same
coefficients. -/
theorem coeff_lie_ofLoop_trunc_eq {M N P Q n : ℤ} {u v : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L M) (hv : v ∈ orderSubmodule R L N)
    (hnP : n < P + N) (hnQ : n < M + Q) :
    coeff R L n ⁅ofLoop R L (trunc R L P u), ofLoop R L (trunc R L Q v)⁆ =
      coeff R L n ⁅u, v⁆ := by
  have h := lie_ofLoop_trunc_sub_mem_orderSubmodule R L hu hv
    (T := min (P + N) (M + Q)) (min_le_left _ _) (min_le_right _ _)
  simpa only [map_sub, sub_eq_zero] using
    coeff_eq_zero_of_mem_orderSubmodule R L h (lt_min hnP hnQ)

end TauCeti.CurrentAlgebra
