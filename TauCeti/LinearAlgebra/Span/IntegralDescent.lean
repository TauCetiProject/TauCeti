/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Descending a span from a ring of scalars to `ℤ`

Let `b` be a family in an `A`-module `M` that is linearly independent over the ring `A`, let `L` be
the lattice of integer combinations of `b`, and let `V ≤ L` be a sublattice. Enlarging the
coefficients of `V` from `ℤ` to `A` can only add elements outside `L`, provided `ℤ · 1` is a direct
summand of `A`, that is, provided some additive map `t : A → ℤ` has `t 1 = 1`:
`Submodule.span A V ∩ L = V` (`TauCeti.mem_of_mem_span_of_mem_closure`).

The map `t` is applied to coordinates: on the `A`-span of `b` it sends `∑ aᵢ bᵢ` to `∑ t(aᵢ) bᵢ`;
this fixes `L` pointwise and carries `a • v` to `t(a) • v` for `v ∈ L`. Without such a retraction
the conclusion fails, as `A = ℤ[1/2]`, `V = 2L` shows.

The standard source of a retraction is a power basis: the coordinate along `gen ^ 0 = 1` is one
(`PowerBasis.exists_linearMap_apply_one`). In particular it applies to `A = ℤ[ζ]` for a root of
unity `ζ` in a field of characteristic zero, through `Algebra.adjoin.powerBasis'`. This is the
descent step in Brauer's induction theorem, where a virtual character is first written as a
combination of induced characters with coefficients in `ℤ[ζ]`.

## Main statements

* `TauCeti.mem_of_mem_span_of_mem_closure`: an integer combination of `b` that is an
  `A`-combination of elements of `V` is already in `V`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Chapter 10, in
  the proof of Theorem 18, where the case `A = ℤ[ζ]` is argued with a `ℤ`-basis of `A`
  containing `1`.
-/

public section

namespace TauCeti

variable {ι A M : Type*} [Ring A] [AddCommGroup M] [Module A M] {b : ι → M}

/-- **Descent of a span from `A` to `ℤ`.** Let `b` be linearly independent over `A`, and let
`t : A → ℤ` be additive with `t 1 = 1`. If `V` is an additive subgroup of the integer combinations
of `b`, then an integer combination of `b` lying in the `A`-span of `V` already lies in `V`. -/
theorem mem_of_mem_span_of_mem_closure (hb : LinearIndependent A b) (t : A →+ ℤ) (ht : t 1 = 1)
    {V : AddSubgroup M} (hV : V ≤ AddSubgroup.closure (Set.range b)) {f : M}
    (hf : f ∈ AddSubgroup.closure (Set.range b)) (hfA : f ∈ Submodule.span A (V : Set M)) :
    f ∈ V := by
  have ht_int (n : ℤ) : t n = n := by rw [← zsmul_one, map_zsmul, ht, smul_eq_mul, mul_one]
  have ht_mul (n : ℤ) (a : A) : t (n * a) = n * t a := by
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]
  -- An integer combination of `b` has integer `A`-coordinates.
  have hL {v : M} (hv : v ∈ AddSubgroup.closure (Set.range b)) :
      ∃ n : ι →₀ ℤ, Finsupp.linearCombination A b (n.mapRange Int.cast Int.cast_zero) = v := by
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_closure_range_iff.mp hv
    refine ⟨n, ?_⟩
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (h := fun i (a : A) => a • b i) fun i => zero_smul A (b i)]
    exact Finsupp.sum_congr fun i _ => Int.cast_smul_eq_zsmul A (n i) (b i)
  -- `P x`: up to an element of `V`, `x` is a combination of `b` whose coefficients `t` kills.
  let P : M → Prop := fun x => ∃ w ∈ V, ∃ c : ι →₀ A,
    (∀ i, t (c i) = 0) ∧ x = w + Finsupp.linearCombination A b c
  have hP_add {x y : M} (hx : P x) (hy : P y) : P (x + y) := by
    obtain ⟨w, hw, c, hc, rfl⟩ := hx
    obtain ⟨w', hw', c', hc', rfl⟩ := hy
    refine ⟨w + w', V.add_mem hw hw', c + c', fun i => by simp [hc, hc'], ?_⟩
    rw [map_add, add_add_add_comm]
  -- For `v ∈ V ≤ L` with integer coordinates `n`, `a • v = t(a) • v + ∑ (a - t(a)) nᵢ bᵢ`.
  have hP_smul (a : A) {v : M} (hv : v ∈ V) : P (a • v) := by
    obtain ⟨n, hn⟩ := hL (hV hv)
    let m : ι →₀ A := n.mapRange Int.cast Int.cast_zero
    refine ⟨t a • v, V.zsmul_mem hv _, a • m - (t a : A) • m, fun i => ?_, ?_⟩
    · simp only [m, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul, map_sub]
      rw [← Int.cast_comm, ← Int.cast_comm, ht_mul, ht_mul, ht_int, sub_self]
    · rw [map_sub, map_smul, map_smul, hn, Int.cast_smul_eq_zsmul, add_sub_cancel]
  have hP : ∀ x ∈ Submodule.span A (V : Set M), ∀ a : A, P (a • x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun a => hP_smul a hx
    | zero => exact fun _ => ⟨0, V.zero_mem, 0, fun _ => by simp, by simp⟩
    | add x y _ _ hx hy => exact fun a => by rw [smul_add]; exact hP_add (hx a) (hy a)
    | smul r x _ hx => exact fun a => by rw [smul_smul]; exact hx (a * r)
  obtain ⟨w, hw, c, hc, hfw⟩ := one_smul A f ▸ hP f hfA 1
  -- `f - w` has integer coordinates `n`, which must be the coordinates `c`, killed by `t`.
  obtain ⟨n, hn⟩ := hL (AddSubgroup.sub_mem _ hf (hV hw))
  have hcn : n.mapRange Int.cast Int.cast_zero = c :=
    hb.finsuppLinearCombination_injective (by rw [hn, hfw, add_sub_cancel_left])
  have hn0 : n = 0 := by
    ext i
    simpa [← hcn, ht_int] using hc i
  rw [hfw, ← hcn, hn0, Finsupp.mapRange_zero, map_zero, add_zero]
  exact hw

end TauCeti
