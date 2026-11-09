/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Descending a span from an algebra to its ring of scalars

Let `A` be an algebra over a commutative ring `R`, let `b` be a family in an `A`-module `M` that is
linearly independent over `A`, let `L` be the `R`-span of `b`, and let `V ≤ L` be an `R`-submodule.
Enlarging the coefficients of `V` from `R` to `A` can only add elements outside `L`, provided
`R · 1` is a direct summand of `A`, that is, provided some `R`-linear map `t : A → R` has
`t 1 = 1`: `Submodule.span A V ∩ L = V` (`TauCeti.mem_of_mem_span_of_mem_span_range`).

The map `t` is applied to coordinates: on the `A`-span of `b` it sends `∑ aᵢ bᵢ` to `∑ t(aᵢ) bᵢ`;
this fixes `L` pointwise and carries `a • v` to `t(a) • v` for `v ∈ L`. Without such a retraction
the conclusion fails, as `R = ℤ`, `A = ℤ[1/2]`, `V = 2L` shows.

The standard source of a retraction is a power basis: the coordinate along `gen ^ 0 = 1` is one
(`PowerBasis.exists_linearMap_apply_one`). In particular it applies to `R = ℤ` and `A = ℤ[ζ]` for
a root of unity `ζ` in a field of characteristic zero, through `Algebra.adjoin.powerBasis'`. This
is the descent step in Brauer's induction theorem, where a virtual character is first written as a
combination of induced characters with coefficients in `ℤ[ζ]`.

## Main statements

* `TauCeti.mem_of_mem_span_of_mem_span_range`: an `R`-combination of `b` that is an
  `A`-combination of elements of `V` is already in `V`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Chapter 10, in
  the proof of Theorem 18, where the case `R = ℤ`, `A = ℤ[ζ]` is argued with a `ℤ`-basis of `A`
  containing `1`.
-/

public section

namespace TauCeti

variable {ι R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module A M] [IsScalarTower R A M] {b : ι → M}

/-- **Descent of a span from `A` to `R`.** Let `b` be linearly independent over the `R`-algebra
`A`, and let `t : A → R` be `R`-linear with `t 1 = 1`. If `V` is an `R`-submodule of the `R`-span
of `b`, then an element of the `R`-span of `b` lying in the `A`-span of `V` already lies in `V`. -/
theorem mem_of_mem_span_of_mem_span_range (hb : LinearIndependent A b) (t : A →ₗ[R] R)
    (ht : t 1 = 1) {V : Submodule R M} (hV : V ≤ Submodule.span R (Set.range b)) {f : M}
    (hf : f ∈ Submodule.span R (Set.range b)) (hfA : f ∈ Submodule.span A (V : Set M)) :
    f ∈ V := by
  have ht_alg (r : R) : t (algebraMap R A r) = r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ht, smul_eq_mul, mul_one]
  -- An element of the `R`-span of `b` has `A`-coordinates in the image of `R`.
  have hL {v : M} (hv : v ∈ Submodule.span R (Set.range b)) : ∃ n : ι →₀ R,
      Finsupp.linearCombination A b (n.mapRange (algebraMap R A) (map_zero _)) = v := by
    obtain ⟨n, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
    exact ⟨n, by simp [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]⟩
  -- `P x`: up to an element of `V`, `x` is a combination of `b` whose coefficients `t` kills.
  let P : M → Prop := fun x => ∃ w ∈ V, ∃ c : ι →₀ A,
    (∀ i, t (c i) = 0) ∧ x = w + Finsupp.linearCombination A b c
  have hP_add {x y : M} (hx : P x) (hy : P y) : P (x + y) := by
    obtain ⟨w, hw, c, hc, rfl⟩ := hx
    obtain ⟨w', hw', c', hc', rfl⟩ := hy
    refine ⟨w + w', V.add_mem hw hw', c + c', fun i => by simp [hc, hc'], ?_⟩
    rw [map_add, add_add_add_comm]
  -- For `v ∈ V` with coordinates `n` in `R`, `a • v = t(a) • v + ∑ (a - t(a)) nᵢ bᵢ`.
  have hP_smul (a : A) {v : M} (hv : v ∈ V) : P (a • v) := by
    obtain ⟨n, hn⟩ := hL (hV hv)
    refine ⟨t a • v, V.smul_mem _ hv,
      (a - algebraMap R A (t a)) • n.mapRange (algebraMap R A) (map_zero _), fun i => ?_, ?_⟩
    · simp [← Algebra.commutes, ← Algebra.smul_def, ht_alg]
    · rw [map_smul, hn, sub_smul, algebraMap_smul, add_sub_cancel]
  have hP : ∀ x ∈ Submodule.span A (V : Set M), ∀ a : A, P (a • x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact fun a => hP_smul a hx
    | zero => exact fun _ => ⟨0, V.zero_mem, 0, fun _ => by simp, by simp⟩
    | add x y _ _ hx hy => exact fun a => by rw [smul_add]; exact hP_add (hx a) (hy a)
    | smul r x _ hx => exact fun a => by rw [smul_smul]; exact hx (a * r)
  obtain ⟨w, hw, c, hc, hfw⟩ := one_smul A f ▸ hP f hfA 1
  -- `f - w` has coordinates `n` in `R`, which must be the coordinates `c`, killed by `t`.
  obtain ⟨n, hn⟩ := hL (sub_mem hf (hV hw))
  have hcn : n.mapRange (algebraMap R A) (map_zero _) = c :=
    hb.finsuppLinearCombination_injective (by rw [hn, hfw, add_sub_cancel_left])
  have hn0 : n = 0 := by
    ext i
    simpa [← hcn, ht_alg] using hc i
  rw [hfw, ← hcn, hn0, Finsupp.mapRange_zero, map_zero, add_zero]
  exact hw

end TauCeti
