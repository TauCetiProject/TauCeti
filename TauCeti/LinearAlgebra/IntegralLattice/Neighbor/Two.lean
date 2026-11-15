/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Isotropic

/-!
# Two-neighbors

For a lattice vector `v` of norm divisible by four, the two-neighbor of `L` along `v` is the
general neighbor `TauCeti.IntegralLattice.neighbor` at `p = 2`. It is obtained by keeping the
vectors pairing evenly with `v` (the neighbor kernel `TauCeti.IntegralLattice.neighborKernel` at
`p = 2`) and adjoining `v / 2`. This file shows that its carrier is the union of the even-pairing
kernel and the translate of that kernel by `v / 2`.

The general results specialise as follows. When `L` is even and the norm of `v` is divisible by
eight, the two-neighbor is even (`TauCeti.IntegralLattice.isEven_neighbor`). When some lattice
vector pairs oddly with `v` (`Int.isCoprime_two_right`), the two-neighbor is a Kneser
two-neighbor (`TauCeti.IntegralLattice.isNeighbor_neighbor`). Then it is unimodular when `L` is
(`TauCeti.IntegralLattice.IsNeighbor.isUnimodular`).

## Main results

* `TauCeti.IntegralLattice.mem_neighbor_two_carrier_iff_mem_or_sub_mem`: the two-neighbor is the
  union of the even-pairing kernel and its translate by `v / 2`.

## References

* G. Nebe, [*Extremal lattices*](https://www.math.rwth-aachen.de/homes/Gabriele.Nebe/talks/OW12.pdf),
  slide 11, for the two-neighbor construction of the Leech lattice.
* R. E. Borcherds, [*The Leech lattice and other lattices*](https://math.berkeley.edu/~reb/papers/thesis/thesis.pdf),
  §0.2, for the even-pairing kernel.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The two-neighbor is the union of the even-pairing kernel and the translate of that kernel by
`v / 2`. -/
@[simp]
theorem mem_neighbor_two_carrier_iff_mem_or_sub_mem {v : L} (hv : (2 : ℤ) ^ 2 ∣ L.integralNorm v)
    (x : V) : x ∈ (L.neighbor 2 v hv).carrier ↔
      x ∈ L.neighborKernel 2 v ∨ x - (2 : ℚ)⁻¹ • (v : V) ∈ L.neighborKernel 2 v := by
  have hv₀ := L.coe_mem_neighborKernel_self 2 (dvd_trans (dvd_pow_self _ two_ne_zero) hv)
  rw [mem_neighbor_carrier_iff]
  simp only [Nat.cast_ofNat]
  set h : V := (2 : ℚ)⁻¹ • (v : V)
  have hh : h + h = (v : V) := by
    rw [← add_smul]
    norm_num
  constructor
  · rintro ⟨y, hy, n, rfl⟩
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      rw [add_smul, ← smul_add, hh]
      exact Submodule.add_mem _ hy (Submodule.smul_mem _ k hv₀)
    · right
      rw [add_smul, one_smul, two_mul, add_smul, ← smul_add, hh, ← add_assoc,
        add_sub_cancel_right]
      exact Submodule.add_mem _ hy (Submodule.smul_mem _ k hv₀)
  · rintro (hx | hx)
    · exact ⟨x, hx, 0, by rw [zero_smul, add_zero]⟩
    · exact ⟨x - h, hx, 1, by rw [one_smul, sub_add_cancel]⟩

end TauCeti.IntegralLattice
