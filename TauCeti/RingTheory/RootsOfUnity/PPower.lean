/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.IntegralDomain

/-!
# Roots of unity of `p`-power order

For a commutative monoid, the `p`-power roots of unity form the primary component of its unit
group. When this subgroup is finite, its order is a power of `p`. In a domain, the subgroup is
cyclic, so primitive `p`-power roots are characterized by divisibility of its order.
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
  have hdir : Directed (· ≤ ·) (fun n : ℕ ↦ rootsOfUnity (p ^ n) K) := by
    intro m n
    refine ⟨max m n, rootsOfUnity_le_of_dvd (pow_dvd_pow p (le_max_left m n)),
      rootsOfUnity_le_of_dvd (pow_dvd_pow p (le_max_right m n))⟩
  simp only [mem_pPowerRootsOfUnity_iff, Subgroup.mem_iSup_of_directed hdir,
    mem_rootsOfUnity]

/-- The order of the `p`-power roots of unity, with finiteness made explicit. In local-field
applications the witness is `finite_pPowerRootsOfUnity`. -/
@[expose] noncomputable def localRootOfUnityOrder
    (_h : Finite (pPowerRootsOfUnity p K)) : ℕ :=
  Nat.card (pPowerRootsOfUnity p K)

/-- The order of the `p`-power roots of unity is the cardinality of its subgroup. -/
@[simp] theorem localRootOfUnityOrder_def (h : Finite (pPowerRootsOfUnity p K)) :
    localRootOfUnityOrder p K h = Nat.card (pPowerRootsOfUnity p K) := rfl

/-- The order of a finite `p`-power root group is positive. -/
theorem localRootOfUnityOrder_pos (h : Finite (pPowerRootsOfUnity p K)) :
    0 < localRootOfUnityOrder p K h := by
  rw [localRootOfUnityOrder_def]
  let _ := h
  exact Nat.card_pos

variable [Fact p.Prime]

/-- The order of the `p`-power roots of unity is a power of `p`. -/
theorem localRootOfUnityOrder_isPow (h : Finite (pPowerRootsOfUnity p K)) :
    ∃ n : ℕ, localRootOfUnityOrder p K h = p ^ n := by
  rw [localRootOfUnityOrder_def]
  let _ := h
  exact IsPGroup.iff_card.mp CommGroup.primaryComponent.isPGroup

/-- If the `p`-power roots of unity have order two, then `p = 2`. -/
theorem prime_eq_two_of_localRootOfUnityOrder_eq_two
    (h : Finite (pPowerRootsOfUnity p K))
    (horder : localRootOfUnityOrder p K h = 2) : p = 2 := by
  obtain ⟨n, hn⟩ := localRootOfUnityOrder_isPow p K h
  have hpow : p ^ n = 2 := hn.symm.trans horder
  cases n with
  | zero => simp at hpow
  | succ n =>
    have hdiv : p ∣ 2 := by
      rw [← hpow]
      exact dvd_pow_self p (by omega)
    exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (Fact.out : p.Prime).ne_one

/-- Once the `p`-power roots of unity are finite, a single level of the root tower contains
them all: that level is their order. -/
theorem pPowerRootsOfUnity_eq_rootsOfUnity_order
    (h : Finite (pPowerRootsOfUnity p K)) :
    pPowerRootsOfUnity p K = rootsOfUnity (localRootOfUnityOrder p K h) K := by
  let _ := h
  obtain ⟨n, hn⟩ := localRootOfUnityOrder_isPow p K h
  ext x
  constructor
  · intro hx
    rw [mem_rootsOfUnity]
    rw [localRootOfUnityOrder_def]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : pPowerRootsOfUnity p K)))
  · intro hx
    apply (mem_pPowerRootsOfUnity_iff p K x).mpr
    exact ⟨n, by simpa only [← hn, mem_rootsOfUnity] using hx⟩

end TauCeti

namespace TauCeti

variable (p : ℕ) (K : Type*) [CommRing K] [IsDomain K]

/-- A finite group of `p`-power roots of unity in a domain is cyclic. -/
theorem isCyclic_pPowerRootsOfUnity (h : Finite (pPowerRootsOfUnity p K)) :
    IsCyclic (pPowerRootsOfUnity p K) := by
  let _ := h
  exact isCyclic_subgroup_units (pPowerRootsOfUnity p K)

/-- A domain with finitely many `p`-power roots of unity contains a primitive `p^n`-th root
precisely when `p^n` divides the order of their group. -/
theorem primitiveRoot_pow_iff_dvd_localRootOfUnityOrder_of_finite
    [NeZero p] (hfinite : Finite (pPowerRootsOfUnity p K)) (n : ℕ) :
    (∃ ζ : K, IsPrimitiveRoot ζ (p ^ n)) ↔
      p ^ n ∣ localRootOfUnityOrder p K hfinite := by
  let _ := hfinite
  constructor
  · rintro ⟨ζ, hζ⟩
    have hpn : p ^ n ≠ 0 := pow_ne_zero n (NeZero.ne p)
    let u := (hζ.isUnit hpn).unit
    have hu : IsPrimitiveRoot u (p ^ n) := hζ.isUnit_unit hpn
    have hmem : u ∈ pPowerRootsOfUnity p K :=
      (mem_pPowerRootsOfUnity_iff p K u).mpr ⟨n, hu.pow_eq_one⟩
    have hord : orderOf (⟨u, hmem⟩ : pPowerRootsOfUnity p K) = p ^ n := by
      calc
        orderOf (⟨u, hmem⟩ : pPowerRootsOfUnity p K) = orderOf u :=
          (Subgroup.orderOf_coe _).symm
        _ = p ^ n := hu.eq_orderOf.symm
    simpa only [localRootOfUnityOrder_def, hord] using
      (orderOf_dvd_natCard (⟨u, hmem⟩ : pPowerRootsOfUnity p K))
  · intro hdvd
    let _ := isCyclic_pPowerRootsOfUnity p K hfinite
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
      (α := pPowerRootsOfUnity p K)
    have hdiv : p ^ n ∣ orderOf g := by
      simpa only [hg, localRootOfUnityOrder_def] using hdvd
    have hg0 : orderOf g ≠ 0 := by
      rw [hg]
      exact Nat.ne_of_gt Nat.card_pos
    let u := g ^ (orderOf g / p ^ n)
    have hu : orderOf u = p ^ n := orderOf_pow_orderOf_div hg0 hdiv
    refine ⟨((u : Kˣ) : K), ?_⟩
    apply IsPrimitiveRoot.iff_orderOf.mpr
    simpa only [orderOf_units, Subgroup.orderOf_coe] using hu

end TauCeti
