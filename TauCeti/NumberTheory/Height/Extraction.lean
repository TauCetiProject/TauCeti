/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.Comparison
import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Estimates

/-!
# Independent tuples of algebraic integers of small height

Let `K` be a number field of degree `D` and let `u` be a family of `D * k` tuples of algebraic
integers in `K ^ ι` whose images under a `ℚ`-linear map `f` are linearly independent. In the
basis form of Siegel's lemma, `f` is the coordinatewise embedding of `K ^ ι` into the real
Minkowski space, which has real dimension `D * #ι`. There the family `u` realizes the successive
minima `c` of the lattice `W ∩ 𝓞_K ^ ι` of a `K`-subspace `W` with respect to a product of
local balls, so `c` is monotone and bounds `u l` at every infinite place.

Since a `K`-span of `j` vectors has `ℚ`-dimension at most `D * j`, one may select `k` members of
`u` that are linearly independent over `K`, the `j`-th of them (counted from zero) at position at
most `D * j`. The heights of the selected tuples are then controlled by the whole family `c`.
For a tuple of algebraic integers the finite places contribute at most one to the height, so a
bound by `c l` at every infinite place bounds the height of `u l` by `c l`. Monotonicity of `c`
bounds each selected term by the `D` terms of its block. Altogether the product of the heights of
the selected tuples is at most `(∏ l, c l) ^ (1 / D)`, both for the absolute sup height
`absoluteProjectiveTupleHeight` and for the absolute Euclidean height `height2`. No minimality of
`c` is needed for this step.

## Main results

* `TauCeti.exists_linearIndependent_prod_absoluteProjectiveTupleHeight_le`: from bounds `c` at
  every infinite place on the coordinates, a `K`-independent selection whose product of absolute
  heights is at most `(∏ l, c l) ^ (1 / D)`.
* `TauCeti.exists_linearIndependent_prod_height2_le`: the same from bounds `c` on the Euclidean
  norms at the infinite places, with the Euclidean height `height2`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §2.9 (2.9.10–2.9.18) and Appendix C, Theorem C.3.8.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. 73 (1983), 11–32.
-/

public section

open Module NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]
  {E M : Type*} [Semiring E] [Nontrivial E] [Algebra ℚ E]
  [AddCommGroup M] [Module E M] [Module ℚ M] [IsScalarTower ℚ E M]
  {k : ℕ} {f : (ι → K) →ₗ[ℚ] M} {u : Fin (finrank ℚ K * k) → ι → 𝓞 K}
  {c : Fin (finrank ℚ K * k) → ℝ}

/-- **Basis form of Siegel's lemma, selection step, sup height.** Let `u` be `[K : ℚ] * k`
tuples of algebraic integers with linearly independent images under a `ℚ`-linear map `f`, and
let `c` be monotone with `|u l i|_w ≤ c l` at every infinite place `w`. Then `k` members of `u`
are linearly independent over `K`, the `j`-th at position at most `[K : ℚ] * j`, and the product
of their absolute heights is at most `(∏ l, c l) ^ (1 / [K : ℚ])`. -/
theorem exists_linearIndependent_prod_absoluteProjectiveTupleHeight_le
    (hu : LinearIndependent E fun l ↦ f fun i ↦ (u l i : K)) (hc : Monotone c)
    (hle : ∀ l i (w : InfinitePlace K), w (u l i) ≤ c l) :
    ∃ s : Fin k → Fin (finrank ℚ K * k),
      LinearIndependent K (fun j i ↦ (u (s j) i : K)) ∧ (∀ j, (s j : ℕ) ≤ finrank ℚ K * j) ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (u (s j) i : K)) ≤
        (∏ l, c l) ^ (finrank ℚ K : ℝ)⁻¹ :=
  exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv (K := K) (u := fun l i ↦ (u l i : K))
    (b := fun l ↦ absoluteProjectiveTupleHeight fun i ↦ (u l i : K)) hu
    (fun _ ↦ (absoluteProjectiveTupleHeight_pos _).le)
    (fun l ↦ absoluteProjectiveTupleHeight_le_of_forall_le
      (fun h ↦ hu.ne_zero l (by simp [RingOfIntegers.coe_tuple_eq_zero_iff.mpr h])) (hle l)) hc

/-- **Basis form of Siegel's lemma, selection step, Euclidean height.** Let `u` be
`[K : ℚ] * k` tuples of algebraic integers with linearly independent images under a `ℚ`-linear
map `f`, and let `c` be monotone such that at every infinite place `w` the embedded tuple
`w (u l)` has Euclidean norm at most `c l`. Then `k` members of `u` are linearly independent
over `K`, the `j`-th at position at most `[K : ℚ] * j`, and the product of their Euclidean
heights is at most `(∏ l, c l) ^ (1 / [K : ℚ])`. -/
theorem exists_linearIndependent_prod_height2_le [Fintype ι]
    (hu : LinearIndependent E fun l ↦ f fun i ↦ (u l i : K)) (hc : Monotone c)
    (hle : ∀ l (w : InfinitePlace K), √(∑ i, ‖w.embedding (u l i)‖ ^ 2) ≤ c l) :
    ∃ s : Fin k → Fin (finrank ℚ K * k),
      LinearIndependent K (fun j i ↦ (u (s j) i : K)) ∧ (∀ j, (s j : ℕ) ≤ finrank ℚ K * j) ∧
      ∏ j, height2 (fun i ↦ (u (s j) i : K)) ≤ (∏ l, c l) ^ (finrank ℚ K : ℝ)⁻¹ :=
  exists_linearIndependent_comp_finrank_mul_prod_le_rpow_inv (K := K) (u := fun l i ↦ (u l i : K))
    (b := fun l ↦ height2 fun i ↦ (u l i : K)) hu (fun _ ↦ height2_nonneg _)
    (fun l ↦ height2_le_of_forall_le (hle l)) hc

end TauCeti
