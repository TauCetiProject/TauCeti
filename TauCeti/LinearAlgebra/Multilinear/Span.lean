/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Values of a multilinear map on spans

A multilinear map is linear in each argument separately, so its value at a family of arguments
drawn from the spans of sets `s i` is a linear combination of its values at families drawn from
the sets `s i` themselves. This needs finitely many arguments: either the index type is finite, or
all but finitely many arguments already lie in the sets `s i`. This is the multilinear analogue of
`Submodule.map₂_span_span` for bilinear maps. It reduces statements about all values of a
determinant-like expression to its values on generators.

For an alternating map, over any semiring and with any index type, this shows that the value
vanishes when more than `k` of the arguments lie in the span of `k` vectors. No domain or
torsion-freeness assumption is needed. Over a commutative domain and with a torsion-free codomain
this also follows from `AlternatingMap.map_linearDependent`, but over a general semiring no
cancellation is available.

## Main results

* `MultilinearMap.map_mem_span_image_pi_of_finset`: if `m i ∈ span R (s i)` for `i` in a finset
  `t` and `m i ∈ s i` for `i ∉ t`, then `f m` lies in the span of the values of `f` on
  `Set.univ.pi s`.
* `MultilinearMap.map_mem_span_image_pi`: for a finite index type, if `m i ∈ span R (s i)` for
  every `i`, then `f m` lies in the span of the values of `f` on `Set.univ.pi s`.
* `AlternatingMap.map_eq_zero_of_mem_span`: an alternating map vanishes when more than `k` of
  its arguments lie in the span of `k` vectors, over any semiring.
-/

public section

namespace MultilinearMap

variable {R S ι N : Type*} {M : ι → Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module S N]

/-- The value of a `σ`-multisemilinear map at a family whose arguments indexed by a finset `t` lie
in the `R`-spans of sets `s i`, and whose other arguments lie in the sets `s i` themselves, lies in
the `S`-span of its values at arguments drawn from the sets `s i`. The index type may be
infinite. -/
theorem map_mem_span_image_pi_of_finset (f : (Π i, M i) →ₘₛₗ[σ] N) (s : ∀ i, Set (M i))
    (t : Finset ι) {m : ∀ i, M i} (hm : ∀ i ∈ t, m i ∈ Submodule.span R (s i))
    (hmt : ∀ i ∉ t, m i ∈ s i) : f m ∈ Submodule.span S (f '' Set.univ.pi s) := by
  classical
  induction t using Finset.induction_on generalizing m with
  | empty => exact Submodule.subset_span ⟨m, fun i _ ↦ hmt i (Finset.notMem_empty i), rfl⟩
  | insert a t ha ih =>
    -- The argument `a` ranges over `span R (s a)` linearly; on generators, use induction on `t`.
    have key : f.toLinearMap m a '' Submodule.span R (s a) ⊆
        Submodule.span S (f '' Set.univ.pi s) := by
      refine (Submodule.image_span_subset _ _ _).2 fun x hx ↦ ?_
      rw [toLinearMap_apply]
      refine ih (fun i hi ↦ ?_) fun i hi ↦ ?_
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
        exact hm i (Finset.mem_insert_of_mem hi)
      · rcases eq_or_ne i a with rfl | hia
        · simpa using hx
        · simpa [hia] using hmt i (by simp [hia, hi])
    simpa using key ⟨m a, hm a (Finset.mem_insert_self a t), rfl⟩

/-- The value of a `σ`-multisemilinear map in finitely many arguments drawn from the `R`-spans of
sets `s i` lies in the `S`-span of its values at arguments drawn from the sets `s i`. -/
theorem map_mem_span_image_pi [Finite ι] (f : (Π i, M i) →ₘₛₗ[σ] N)
    (s : ∀ i, Set (M i)) {m : ∀ i, M i} (hm : ∀ i, m i ∈ Submodule.span R (s i)) :
    f m ∈ Submodule.span S (f '' Set.univ.pi s) := by
  cases nonempty_fintype ι
  exact f.map_mem_span_image_pi_of_finset s Finset.univ (fun i _ ↦ hm i) fun i hi ↦
    absurd (Finset.mem_univ i) hi

end MultilinearMap

namespace AlternatingMap

variable {ι R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- **An alternating map vanishes when too many arguments lie in a small span.** If more than `k`
of the arguments lie in the span of `k` vectors, then the value is zero. This holds over any
semiring, without a domain or torsion-freeness assumption, and the index type may be infinite. Over
a commutative domain and with a torsion-free codomain it also follows from
`AlternatingMap.map_linearDependent`. -/
theorem map_eq_zero_of_mem_span (f : M [⋀^ι]→ₗ[R] N) {v : ι → M} {t : Finset ι}
    {k : ℕ} (c : Fin k → M) (ht : k < t.card)
    (hv : ∀ i ∈ t, v i ∈ Submodule.span R (Set.range c)) : f v = 0 := by
  classical
  -- Expand the arguments indexed by `t` along `c`; the other arguments stay fixed.
  let s : ι → Set M := fun i ↦ if i ∈ t then Set.range c else {v i}
  refine (Submodule.mem_bot R).1 <| Submodule.span_le.2 ?_ <|
    f.toMultilinearMap.map_mem_span_image_pi_of_finset s t
      (fun i hi ↦ by simpa [s, hi] using hv i hi) fun i hi ↦ by simp [s, hi]
  rintro _ ⟨w, hw, rfl⟩
  -- Each expanded family maps `t` into the at most `k` values of `c`, so two coincide.
  obtain ⟨i, -, j, -, hij, hwij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t := Finset.univ.image c) (Finset.card_image_le.trans_lt (by simpa using ht))
    fun i (hi : i ∈ t) ↦ mem_image_univ_iff_mem_range.2 (by simpa [s, hi] using hw i trivial)
  exact f.map_eq_zero_of_eq w hwij hij

end AlternatingMap
