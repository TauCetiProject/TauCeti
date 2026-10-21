/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Values of a multilinear map on spans

A multilinear map is linear in each argument separately, so its value at a family of arguments
drawn from the spans of sets `s i` is a linear combination of its values at families drawn from
the sets `s i` themselves. This is the multilinear analogue of `Submodule.map₂_span_span` for
bilinear maps. It reduces statements about all values of a determinant-like expression to its
values on generators.

For an alternating map, this shows that the value vanishes when more than `k` of the arguments
lie in the span of `k` vectors. Over a domain this is `AlternatingMap.map_linearDependent`, but
over an arbitrary ring no cancellation is available.

## Main results

* `MultilinearMap.map_mem_span_image_pi`: if `m i ∈ span R (s i)` for every `i`, then `f m` lies
  in the span of the values of `f` on `Set.univ.pi s`.
* `AlternatingMap.map_eq_zero_of_mem_span`: an alternating map vanishes when more than `k` of
  its arguments lie in the span of `k` vectors, over any semiring.
-/

public section

namespace MultilinearMap

variable {R ι N : Type*} {M : ι → Type*} [Semiring R] [Finite ι]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- The value of a multilinear map at arguments drawn from the spans of sets `s i` lies in the
span of its values at arguments drawn from the sets `s i`. -/
theorem map_mem_span_image_pi (f : MultilinearMap R M N) (s : ∀ i, Set (M i)) {m : ∀ i, M i}
    (hm : ∀ i, m i ∈ Submodule.span R (s i)) :
    f m ∈ Submodule.span R (f '' Set.univ.pi s) := by
  classical
  cases nonempty_fintype ι
  -- Replace the arguments indexed by `t` by elements of the spans, one coordinate at a time.
  suffices key : ∀ t : Finset ι, ∀ m : ∀ i, M i, (∀ i, m i ∈ Submodule.span R (s i)) →
      (∀ i ∉ t, m i ∈ s i) → f m ∈ Submodule.span R (f '' Set.univ.pi s) from
    key Finset.univ m hm (by simp)
  intro t
  induction t using Finset.induction_on with
  | empty => exact fun m _ h ↦ Submodule.subset_span ⟨m, fun i _ ↦ h i (by simp), rfl⟩
  | insert a t ha ih =>
    intro m hm h
    have hupdate : ∀ x ∈ Submodule.span R (s a),
        f (Function.update m a x) ∈ Submodule.span R (f '' Set.univ.pi s) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun i ↦ ?_) (fun i hi ↦ ?_)
        · rcases eq_or_ne i a with rfl | hia
          · simpa using Submodule.subset_span hx
          · simpa [hia] using hm i
        · rcases eq_or_ne i a with rfl | hia
          · simpa using hx
          · simpa [hia] using h i (by simp [hia, hi])
      | zero => simp
      | add x y _ _ hx hy => rw [f.map_update_add]; exact add_mem hx hy
      | smul c x _ hx => rw [f.map_update_smul]; exact Submodule.smul_mem _ c hx
    simpa using hupdate (m a) (hm a)

end MultilinearMap

namespace AlternatingMap

variable {ι R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- **An alternating map vanishes when too many arguments lie in a small span.** If more than `k`
of the arguments lie in the span of `k` vectors, then the value is zero. Over a domain this
follows from `AlternatingMap.map_linearDependent`; here the ring is arbitrary. -/
theorem map_eq_zero_of_mem_span [Finite ι] (f : M [⋀^ι]→ₗ[R] N) {v : ι → M} {t : Finset ι}
    {k : ℕ} (c : Fin k → M) (ht : k < t.card)
    (hv : ∀ i ∈ t, v i ∈ Submodule.span R (Set.range c)) : f v = 0 := by
  classical
  cases nonempty_fintype ι
  -- Expand the arguments indexed by `t` along `c`; the other arguments stay fixed.
  let s : ι → Set M := fun i ↦ if i ∈ t then Set.range c else {v i}
  have hs (i : ι) : v i ∈ Submodule.span R (s i) := by
    by_cases hi : i ∈ t
    · simpa [s, hi] using hv i hi
    · simp [s, hi]
  refine (Submodule.mem_bot R).1 <| Submodule.span_le.2 ?_ <|
    f.toMultilinearMap.map_mem_span_image_pi s hs
  rintro _ ⟨w, hw, rfl⟩
  -- Each expanded family takes more than `k` values in `range c` on `t`, so two coincide.
  have hwc (i : t) : w i ∈ Set.range c := by simpa [s, i.2] using hw i trivial
  choose g hg using hwc
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simpa using ht)
  simpa using f.map_eq_zero_of_eq w (by rw [← hg i, ← hg j, hgij]) (Subtype.coe_ne_coe.2 hij)

end AlternatingMap
