/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Coefficient extraction and cyclic invariance for alternating maps

Putting a linear combination `∑ j ∈ s, e j • v j` in place of the `i`-th argument `v i` of an
alternating map, for `i ∈ s`, multiplies its value on `v` by `e i`: every other term of the sum
repeats an argument, so its contribution vanishes. Over a basis, this reads off the `i`-th
coordinate of a vector put in place of the `i`-th basis vector.

An alternating map is unchanged by a permutation of its arguments of sign `1`; in particular, an
alternating map of four arguments is unchanged by a cyclic permutation of its last three
arguments.

## Main results

* `AlternatingMap.map_update_sum_smul`: putting `∑ j ∈ s, e j • v j` in place of `v i`, for
  `i ∈ s`, multiplies the value of an alternating map by `e i`.
* `AlternatingMap.map_perm_of_sign_eq_one`: an alternating map is invariant under a permutation of
  its arguments of sign `1`.
* `AlternatingMap.map_fin_four_cycle`: an alternating map of four arguments is invariant under a
  cyclic permutation of its last three arguments.
* `AlternatingMap.exists_map_eq_units_smul`: if every vector of an injective family `w` is a vector
  of a family `v` indexed by the same finite type, an alternating map takes the same value on `v`
  and on `w` up to sign.
-/

public section

namespace AlternatingMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- Putting the linear combination `∑ j ∈ s, e j • v j` in place of `v i`, for `i ∈ s`, multiplies
the value of an alternating map by `e i`: every other term repeats an argument. -/
@[simp]
theorem map_update_sum_smul [DecidableEq ι] (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) {s : Finset ι}
    {i : ι} (hi : i ∈ s) (e : ι → R) :
    f (Function.update v i (∑ j ∈ s, e j • v j)) = e i • f v := by
  rw [f.map_update_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji ↦ by
    rw [f.map_update_smul, f.map_update_self _ hji.symm, smul_zero], f.map_update_smul,
    Function.update_eq_self]

/-- An alternating map is invariant under a permutation of its arguments of sign `1`. -/
theorem map_perm_of_sign_eq_one {N : Type*} [AddCommGroup N] [Module R N] [DecidableEq ι]
    [Fintype ι] (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) {σ : Equiv.Perm ι}
    (hσ : Equiv.Perm.sign σ = 1) : f (v ∘ σ) = f v := by
  rw [f.map_perm, hσ, one_smul]

/-- An alternating map of four arguments is invariant under a cyclic permutation of its last three
arguments: `f (a, v, w, u) = f (a, u, v, w)`. This is `map_perm_of_sign_eq_one` for a
three-cycle. -/
theorem map_fin_four_cycle {N : Type*} [AddCommGroup N] [Module R N] (f : M [⋀^Fin 4]→ₗ[R] N)
    (a u v w : M) : f ![a, v, w, u] = f ![a, u, v, w] := by
  have e : ![a, v, w, u] =
      ![a, u, v, w] ∘ (Equiv.swap 1 2 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) := by
    ext j
    fin_cases j <;> rfl
  rw [e, f.map_perm_of_sign_eq_one _ (by decide)]

/-- If every vector of an injective family `w` is a vector of the family `v`, indexed by the same
finite type, then `v` is `w` reordered, so an alternating map takes the same value on `v` and on
`w` up to sign. -/
theorem exists_map_eq_units_smul {N : Type*} [AddCommGroup N] [Module R N] [Finite ι]
    (f : M [⋀^ι]→ₗ[R] N) {v w : ι → M} (hw : Function.Injective w)
    (h : ∀ i, ∃ j, v j = w i) : ∃ ε : ℤˣ, f v = ε • f w := by
  classical
  have := Fintype.ofFinite ι
  choose g hg using h
  have hg' : g.Injective := fun i i' hii' ↦ hw (by rw [← hg, ← hg, hii'])
  let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg')
  have hvw : v = w ∘ σ.symm := funext fun j ↦ by
    obtain ⟨i, rfl⟩ := σ.surjective j
    rw [Function.comp_apply, Equiv.symm_apply_apply]
    exact hg i
  exact ⟨Equiv.Perm.sign σ.symm, by rw [hvw, f.map_perm]⟩

end AlternatingMap
