/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# Alternating maps on linearly dependent families over semirings

An alternating map vanishes on a linearly dependent family. Mathlib's
`AlternatingMap.map_linearDependent` proves this for a domain acting on torsion-free values. Over
a semiring a dependence need not have a nonzero coefficient on one side, so it is a pair of
coefficient families `c ≠ d` with `∑ j ∈ s, c j • v j = ∑ j ∈ s, d j • v j`, differing at some
`i ∈ s`. Putting either sum in place of `v i` multiplies the value by `c i`, respectively `d i`,
since every other term repeats an argument. Hence `c i • f v = d i • f v`, so the conclusion
holds whenever unequal scalars act differently on every nonzero value. That covers, for example,
`ℕ`-modules with values in `ℤ`.

## Main results

* `AlternatingMap.map_linearDependent_of_smul_left_injective`: an alternating map vanishes on a
  linearly dependent family when unequal scalars act differently on every nonzero value.
* `LinearMap.IsAlt.eq_zero_of_not_linearIndependent`: the same for an alternating bilinear map on
  a linearly dependent pair.
-/

public section

namespace AlternatingMap

/-- An alternating map vanishes on a linearly dependent family, provided unequal scalars act
differently on every nonzero value. Over a domain acting on torsion-free values, the latter
hypothesis is `fun _ ↦ smul_left_injective R`. This is `AlternatingMap.map_linearDependent` over
any semiring. -/
theorem map_linearDependent_of_smul_left_injective {R M N ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (f : M [⋀^ι]→ₗ[R] N)
    (hN : ∀ n : N, n ≠ 0 → Function.Injective fun r : R ↦ r • n) {v : ι → M}
    (hv : ¬LinearIndependent R v) : f v = 0 := by
  classical
  obtain ⟨s, c, d, hcd, i, hi, hne⟩ := not_linearIndependent_iffₛ.mp hv
  -- Putting `∑ j ∈ s, e j • v j` in place of `v i` multiplies the value by `e i`.
  have key (e : ι → R) : f (Function.update v i (∑ j ∈ s, e j • v j)) = e i • f v := by
    rw [f.map_update_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji ↦ by
      rw [f.map_update_smul, f.map_update_self _ hji.symm, smul_zero], f.map_update_smul,
      Function.update_eq_self]
  by_contra h0
  exact hne <| hN _ h0 <| by simpa only [key] using congr(f (Function.update v i $hcd))

end AlternatingMap

namespace LinearMap.IsAlt

/-- An alternating bilinear map vanishes on a linearly dependent pair, provided unequal scalars
act differently on every nonzero value. Over a domain acting on torsion-free values, the latter
hypothesis is `fun _ ↦ smul_left_injective R`. This is the case of two arguments of
`AlternatingMap.map_linearDependent_of_smul_left_injective`. -/
theorem eq_zero_of_not_linearIndependent {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt)
    (hN : ∀ n : N, n ≠ 0 → Function.Injective fun r : R ↦ r • n) {v w : M}
    (hvw : ¬LinearIndependent R ![v, w]) : ω v w = 0 := by
  simpa using halt.toAlternatingMap.map_linearDependent_of_smul_left_injective hN hvw

end LinearMap.IsAlt
