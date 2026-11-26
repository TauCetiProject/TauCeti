/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Star.Orthogonal
public import TauCeti.Algebra.Star.Basic
public import TauCeti.RingTheory.Semisimple.CenterDimension

/-!
# Proper involutions preserve the simple factors of a semisimple ring

Let `R` be a semisimple ring with a proper involution: a `StarRing` structure with `star x * x = 0`
only for `x = 0` (Mathlib's `IsProperStar`). The involution preserves every isotypic component `c`
of `R` as a left module over itself (the simple factors of `R`). The preimage of `c` under the
involution is a two-sided ideal, hence a sum of isotypic components; for an isotypic component
`c' ≠ c` contained in it and `y ∈ c'`, the product `y* y` lies in `c c' = 0`, so `y = 0`.

Consequently `x x*` splits along the simple factors: writing `x = ∑_c x_c` with `x_c ∈ c`
(`TauCeti.exists_sum_eq_of_isotypicComponents`), `x x* = ∑_c x_c x_c*`, and an additive map `t`
with values in an ordered monoid is positive on all nonzero `x x*` exactly when it is positive on
the nonzero `y y*` with `y` in one simple factor.

## Main results

* `TauCeti.star_mem_of_mem_isotypicComponents`: on a semisimple ring, a proper involution preserves
  every isotypic component of the regular module.
* `TauCeti.sum_mul_star_sum_of_isotypicComponents`: `(∑_c x_c)(∑_c x_c)* = ∑_c x_c x_c*`.
* `TauCeti.forall_pos_mul_star_iff_of_isotypicComponents`: positivity on all `x x*` is positivity
  on the `y y*` with `y` in one isotypic component.
* `TauCeti.forall_pos_mul_star_of_isotypicComponents`: positivity on all `x x*` transfers from one
  additive map to another that is positive wherever the first is, on each isotypic component.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] [StarRing R]

section IsProperStar

variable [IsProperStar R] [IsSemisimpleRing R]

/-- **A proper involution preserves the simple factors.** On a semisimple ring with a proper
involution, the involution maps every isotypic component `c` of the regular module into itself. -/
theorem star_mem_of_mem_isotypicComponents {c : Ideal R} (hc : c ∈ isotypicComponents R R)
    {b : R} (hb : b ∈ c) : star b ∈ c := by
  have := isTwoSided_of_mem_isotypicComponents hc
  -- The preimage `J = {y | y* ∈ c}` is a two-sided ideal.
  let J : Ideal R :=
    { carrier := {y | star y ∈ c}
      add_mem' := fun hx hy ↦ by simpa [star_add] using c.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := fun r y hy ↦ by
        simpa [star_mul] using Ideal.mul_mem_right (star r) c hy }
  have hmemJ : ∀ y, y ∈ J ↔ star y ∈ c := fun _ ↦ Iff.rfl
  have hJ : J.IsTwoSided := ⟨fun r hy ↦ by
    rw [hmemJ, star_mul]
    exact c.smul_mem (star r) ((hmemJ _).mp hy)⟩
  obtain ⟨s, hs, hJs⟩ :=
    isFullyInvariant_iff_sSup_isotypicComponents.mp (isFullyInvariant_iff_isTwoSided.mpr hJ)
  have hJc : J ≤ c := by
    rw [hJs]
    refine sSup_le fun c' hc' ↦ ?_
    by_cases hne : c' = c
    · exact hne.le
    · intro y hy
      have hyJ : star y ∈ c := (hmemJ y).mp (hJs.ge (le_sSup hc' hy))
      have h0 : star y * y = 0 :=
        mul_eq_zero_of_mem_isotypicComponents hc (hs hc') hne hyJ hy
      rw [star_mul_self_eq_zero.mp h0]
      exact c.zero_mem
  exact hJc ((hmemJ _).mpr (by rwa [star_star]))

/-- **`x x*` splits along the simple factors**: if `x = ∑_{c ∈ s} x_c` with `x_c` in the
isotypic component `c` and `s` a set of isotypic components, then `x x* = ∑_{c ∈ s} x_c x_c*`. -/
theorem sum_mul_star_sum_of_isotypicComponents {s : Finset (Ideal R)}
    (hs : ∀ c ∈ s, c ∈ isotypicComponents R R) {μ : Ideal R → R} (hμ : ∀ c ∈ s, μ c ∈ c) :
    (∑ c ∈ s, μ c) * star (∑ c ∈ s, μ c) = ∑ c ∈ s, μ c * star (μ c) := by
  refine Set.Pairwise.sum_mul_star_sum_of_isStarOrtho fun c hc c' hc' hne ↦ ?_
  have hy := star_mem_of_mem_isotypicComponents (hs c' hc') (hμ c' hc')
  exact ⟨mul_eq_zero_of_mem_isotypicComponents (hs c hc) (hs c' hc') (Ne.symm hne) (hμ c hc) hy,
    mul_eq_zero_of_mem_isotypicComponents (hs c' hc') (hs c hc) hne hy (hμ c hc)⟩

/-- **Positivity of `x x*` can be checked on the simple factors.** For an additive map `t` from a
semisimple ring with a proper involution to an ordered cancellative monoid, `t (x x*) > 0` for
every `x ≠ 0` exactly when `t (y y*) > 0` for every nonzero `y` in an isotypic component of the
regular module. -/
theorem forall_pos_mul_star_iff_of_isotypicComponents {M : Type*} [AddCommMonoid M]
    [PartialOrder M] [IsOrderedCancelAddMonoid M] (t : R →+ M) :
    (∀ x : R, x ≠ 0 → 0 < t (x * star x)) ↔
      ∀ c ∈ isotypicComponents R R, ∀ y ∈ c, y ≠ 0 → 0 < t (y * star y) := by
  refine ⟨fun h _ _ y _ hy ↦ h y hy, fun h x hx ↦ ?_⟩
  obtain ⟨μ, hμ, rfl⟩ := exists_sum_eq_of_isotypicComponents x
  have hs : ∀ c ∈ (isotypicComponents R R).toFinite.toFinset, c ∈ isotypicComponents R R :=
    fun c hc ↦ (Set.Finite.mem_toFinset _).mp hc
  rw [sum_mul_star_sum_of_isotypicComponents hs fun c _ ↦ hμ c, map_sum]
  obtain ⟨c, hc, hμc⟩ : ∃ c ∈ (isotypicComponents R R).toFinite.toFinset, μ c ≠ 0 := by
    by_contra! h0
    exact hx (Finset.sum_eq_zero h0)
  refine Finset.sum_pos' (fun c' hc' ↦ ?_) ⟨c, hc, h c (hs c hc) _ (hμ c) hμc⟩
  obtain h0 | hne := eq_or_ne (μ c') 0
  · simp [h0]
  · exact (h c' (hs c' hc') _ (hμ c') hne).le

end IsProperStar

variable [IsSemisimpleRing R]

/-- **Positivity of `x x*` transfers along the simple factors.** Let `t` be an additive map that is
positive on every nonzero `x x*`, so that the involution is proper. If on each isotypic component
`c` of the regular module `t (y y*) > 0` implies `u (y y*) > 0` for `y ∈ c`, then the additive map
`u` to an ordered cancellative monoid is positive on every nonzero `x x*`. -/
theorem forall_pos_mul_star_of_isotypicComponents {M N : Type*} [AddMonoid M] [Preorder M]
    [AddCommMonoid N] [PartialOrder N] [IsOrderedCancelAddMonoid N] (t : R →+ M) (u : R →+ N)
    (ht : ∀ x : R, x ≠ 0 → 0 < t (x * star x))
    (h : ∀ c ∈ isotypicComponents R R, ∀ y ∈ c, 0 < t (y * star y) → 0 < u (y * star y)) :
    ∀ x : R, x ≠ 0 → 0 < u (x * star x) := by
  have := isProperStar_of_forall_pos_mul_star t ht
  exact (forall_pos_mul_star_iff_of_isotypicComponents u).mpr
    fun c hc y hy hy0 ↦ h c hc y hy (ht y hy0)

end TauCeti
