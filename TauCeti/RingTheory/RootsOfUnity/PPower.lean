/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.Torsion

/-!
# Roots of unity of `p`-power order

For a commutative monoid, the `p`-power roots of unity form the primary component of its unit
group. In a reduced ring of exponential characteristic `p` this subgroup is trivial. When finite
in a domain, it is cyclic by Mathlib's instance `isCyclic_subgroup_units`. If a commutative monoid
has no primitive `p ^ (k + 1)`-th root of unity, for a prime `p`, then each of its roots of unity of
`p`-power order is a `p ^ k`-th root of unity.
-/

public section

namespace TauCeti

variable (p : ℕ) (K : Type*) [CommMonoid K]

/-- The subgroup of `Kˣ` consisting of roots of unity of `p`-power order. -/
abbrev pPowerRootsOfUnity : Subgroup Kˣ := CommGroup.primaryComponent Kˣ p

/-- A unit is a `p`-power root of unity exactly when some power of `p` kills it. -/
theorem mem_pPowerRootsOfUnity_iff (x : Kˣ) :
    x ∈ pPowerRootsOfUnity p K ↔ ∃ n : ℕ, x ^ (p ^ n) = 1 :=
  CommGroup.mem_primaryComponent

/-- The `p`-power roots of unity are the union of the finite-level root groups. -/
theorem pPowerRootsOfUnity_eq_iSup_rootsOfUnity :
    pPowerRootsOfUnity p K = ⨆ n : ℕ, rootsOfUnity (p ^ n) K := by
  ext x
  simp only [mem_pPowerRootsOfUnity_iff, mem_rootsOfUnity, Subgroup.mem_iSup_of_directed
    (Monotone.directed_le fun _ _ h ↦ rootsOfUnity_le_of_dvd (pow_dvd_pow p h))]

/-- In a reduced ring of exponential characteristic `p`, the only root of unity of `p`-power
order is `1`, since the Frobenius is injective. -/
@[simp]
theorem pPowerRootsOfUnity_eq_bot (R : Type*) [CommRing R] [IsReduced R] [ExpChar R p] :
    pPowerRootsOfUnity p R = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := (mem_pPowerRootsOfUnity_iff p R x).1 hx
  simpa using (mem_rootsOfUnity_prime_pow_mul_iff' R p n 1).1 (by rwa [mul_one])

/-- If a commutative monoid has no primitive `p ^ (k + 1)`-th root of unity, for a prime `p`, then
every root of unity of `p`-power order in it is a `p ^ k`-th root of unity. -/
theorem pow_prime_pow_eq_one_of_forall_not_isPrimitiveRoot {M : Type*} [CommMonoid M]
    {p k n : ℕ} (hp : p.Prime) (h : ∀ ζ : M, ¬IsPrimitiveRoot ζ (p ^ (k + 1))) {ζ : M}
    (hζ : ζ ^ p ^ n = 1) : ζ ^ p ^ k = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hζ)
  rcases le_or_gt j k with hjk | hkj
  · rw [← orderOf_dvd_iff_pow_eq_one, hj]
    exact pow_dvd_pow p hjk
  · -- otherwise `ζ ^ p ^ (j - (k + 1))` is a primitive `p ^ (k + 1)`-th root of unity
    have hdvd : p ^ (j - (k + 1)) ∣ orderOf ζ := hj ▸ pow_dvd_pow p (by omega)
    have := (IsPrimitiveRoot.orderOf ζ).pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd
    rw [hj, Nat.pow_div (by omega) hp.pos, show j - (j - (k + 1)) = k + 1 by omega] at this
    exact (h _ this).elim

end TauCeti
