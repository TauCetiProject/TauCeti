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
in a domain, it is cyclic by Mathlib's instance `isCyclic_subgroup_units`. For `m ≤ n`, the power
`ζ ^ p ^ (n - m)` of a primitive `p ^ n`-th root of unity `ζ` is a primitive `p ^ m`-th root of
unity. If a commutative monoid has no primitive `p ^ (k + 1)`-th root of unity, for a prime `p`,
then each of its roots of unity of `p`-power order is a `p ^ k`-th root of unity.
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

/-- If `ζ` is a primitive `p ^ n`-th root of unity and `m ≤ n`, then `ζ ^ p ^ (n - m)` is a
primitive `p ^ m`-th root of unity. -/
theorem _root_.IsPrimitiveRoot.pow_pow_sub {M : Type*} [CommMonoid M] {ζ : M} {p n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (hp : p ≠ 0) {m : ℕ} (hm : m ≤ n) :
    IsPrimitiveRoot (ζ ^ p ^ (n - m)) (p ^ m) :=
  hζ.pow (pow_pos (Nat.pos_of_ne_zero hp) n) (by rw [← pow_add, Nat.sub_add_cancel hm])

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
    exact (h _ ((hj ▸ IsPrimitiveRoot.orderOf ζ).pow_pow_sub hp.ne_zero hkj)).elim

end TauCeti
