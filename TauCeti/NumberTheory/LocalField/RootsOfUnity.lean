/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.RingTheory.RootsOfUnity.PPower

/-!
# The `p`-power roots of unity in a local field

The `p`-power roots of unity form the `p`-primary component of the multiplicative group.
In a nonarchimedean local field of characteristic different from `p`, this group is finite:
every root has valuation zero, and sufficiently deep principal units have no `p`-power
torsion. The resulting injection into a finite unit-filtration quotient proves finiteness.
A finite subgroup of a field's unit group is cyclic. These facts make its order an arithmetic
invariant of finite extensions of `ℚ_p`.

The finiteness argument uses the unit-filtration results in this library. For the standard
structure theorem see Serre, *Local Fields*, Chapter II, §§4–5.
-/

public section

namespace TauCeti

section

variable (p : ℕ) (K : Type*) [CommMonoid K]

/-- The order of the `p`-power roots of unity, with finiteness made explicit. In local-field
applications the witness is `finite_pPowerRootsOfUnity`. -/
noncomputable def localRootOfUnityOrder
    (_h : Finite (pPowerRootsOfUnity p K)) : ℕ :=
  Nat.card (pPowerRootsOfUnity p K)

/-- The order of the `p`-power roots of unity is the cardinality of its subgroup. -/
@[simp] theorem localRootOfUnityOrder_def (h : Finite (pPowerRootsOfUnity p K)) :
    localRootOfUnityOrder p K h = Nat.card (pPowerRootsOfUnity p K) := (rfl)

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

end

section

variable (p : ℕ) (K : Type*) [CommRing K] [IsDomain K]

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

end

open IsNonarchimedeanLocalField

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [Fact p.Prime] in
/-- Every `p`-power root of unity has valuation zero. -/
theorem pPowerRootsOfUnity_le_unitFiltration_zero (hp : p ≠ 0) :
    pPowerRootsOfUnity p K ≤ unitFiltration K 0 := by
  rw [pPowerRootsOfUnity_eq_iSup_rootsOfUnity]
  exact iSup_le fun n ↦ rootsOfUnity_le_unitFiltration_zero K (pow_ne_zero n hp)

/-- A sufficiently deep principal-unit group contains no nontrivial `p`-power root of unity. -/
theorem disjoint_pPowerRootsOfUnity_unitFiltration {i : ℕ} (hpK : (p : K) ≠ 0)
    (hi : natCastValuation K p hpK < (p - 1) * i) :
    Disjoint (pPowerRootsOfUnity p K) (unitFiltration K i) := by
  have hp : p.Prime := Fact.out
  have hprime := disjoint_rootsOfUnity_unitFiltration_of_prime hp hpK hi
  have hpow (n : ℕ) (x : Kˣ) (hx : x ∈ unitFiltration K i)
      (hxn : x ^ (p ^ n) = 1) : x = 1 := by
    induction n generalizing x with
    | zero => simpa using hxn
    | succ n ih =>
      have hxp : x ^ p = 1 := ih (x ^ p) (Subgroup.pow_mem _ hx _) (by
        simpa only [pow_succ', pow_mul] using hxn)
      exact Subgroup.disjoint_def.mp hprime ((mem_rootsOfUnity p x).mpr hxp) hx
  exact Subgroup.disjoint_def.mpr fun {x} hx hxi ↦
    let ⟨n, hn⟩ := (mem_pPowerRootsOfUnity_iff p K x).mp hx
    hpow n x hxi hn

/-- The `p`-power roots of unity in a local field of characteristic different from `p` form a
finite group. -/
theorem finite_pPowerRootsOfUnity (hpK : (p : K) ≠ 0) :
    Finite (pPowerRootsOfUnity p K) := by
  let i := natCastValuation K p hpK + 1
  have hi : natCastValuation K p hpK < (p - 1) * i := by
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    dsimp [i]
    calc
      natCastValuation K p hpK < natCastValuation K p hpK + 1 := Nat.lt_succ_self _
      _ = 1 * (natCastValuation K p hpK + 1) := by simp
      _ ≤ (p - 1) * (natCastValuation K p hpK + 1) :=
        Nat.mul_le_mul_right _ (by omega)
  have hdisjoint := disjoint_pPowerRootsOfUnity_unitFiltration hpK hi
  have hle : unitFiltration K i ≤ unitFiltration K 0 :=
    unitFiltration_antitone (Nat.zero_le _)
  have hindex : (unitFiltration K i).IsFiniteRelIndex (unitFiltration K 0) := by
    have hsucc : (unitFiltration K i).IsFiniteRelIndex (unitFiltration K 1) :=
      inferInstance
    exact hsucc.trans (unitFiltration_one_isFiniteRelIndex_zero (K := K))
  have hfinite : Finite (unitFiltration K 0 ⧸ (unitFiltration K i).subgroupOf
      (unitFiltration K 0)) := by
    exact (Subgroup.finiteIndex_iff_finite_quotient).mp
      ((Subgroup.isFiniteRelIndex_iff_finiteIndex).mp hindex)
  let f : pPowerRootsOfUnity p K →
      unitFiltration K 0 ⧸ (unitFiltration K i).subgroupOf (unitFiltration K 0) :=
    fun x ↦ QuotientGroup.mk
      ⟨x.1, pPowerRootsOfUnity_le_unitFiltration_zero (Fact.out : p.Prime).ne_zero x.2⟩
  apply @Finite.of_injective _ _ hfinite f
  intro x y hxy
  have hmem : (x.1 * y.1⁻¹) ∈ unitFiltration K i := by
    have hq := QuotientGroup.eq.mp hxy
    have hq' : x.1⁻¹ * y.1 ∈ unitFiltration K i := by
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hq
    simpa only [mul_inv_rev, inv_inv, mul_comm] using (unitFiltration K i).inv_mem hq'
  have hroot : x.1 * y.1⁻¹ ∈ pPowerRootsOfUnity p K :=
    mul_mem x.2 (inv_mem y.2)
  have h1 : x.1 * y.1⁻¹ = 1 := Subgroup.disjoint_def.mp hdisjoint hroot hmem
  exact Subtype.ext (mul_inv_eq_one.mp h1)

/-- A local field contains a primitive `p^n`-th root of unity precisely when `p^n` divides
the order of its `p`-power root group. -/
theorem primitiveRoot_pow_iff_dvd_localRootOfUnityOrder (hpK : (p : K) ≠ 0)
    (n : ℕ) :
    (∃ ζ : K, IsPrimitiveRoot ζ (p ^ n)) ↔
      p ^ n ∣ localRootOfUnityOrder p K (finite_pPowerRootsOfUnity hpK) :=
  primitiveRoot_pow_iff_dvd_localRootOfUnityOrder_of_finite
    p K (finite_pPowerRootsOfUnity hpK) n

/-- A local field contains a primitive `p`-th root of unity exactly when `p` divides the
order of its `p`-power root group. -/
theorem primitiveRoot_iff_dvd_localRootOfUnityOrder (hpK : (p : K) ≠ 0) :
    (∃ ζ : K, IsPrimitiveRoot ζ p) ↔
      p ∣ localRootOfUnityOrder p K (finite_pPowerRootsOfUnity hpK) := by
  simpa only [pow_one] using primitiveRoot_pow_iff_dvd_localRootOfUnityOrder hpK 1

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- In a dyadic local field, the `2`-power root group has order greater than two exactly when
there is a primitive fourth root of unity. This distinguishes the two dyadic presentation
branches. -/
theorem localRootOfUnityOrder_ne_two_iff (h2 : (2 : K) ≠ 0) :
    localRootOfUnityOrder 2 K (finite_pPowerRootsOfUnity h2) ≠ 2 ↔
      ∃ ζ : K, IsPrimitiveRoot ζ 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := localRootOfUnityOrder 2 K (finite_pPowerRootsOfUnity h2)
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    exact (ringChar.spec K 2).mpr (by simp [h])
  have hprimitive : IsPrimitiveRoot (-1 : K) 2 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    simp [orderOf_neg_one, hchar]
  have htwo : 2 ∣ q := by
    exact (primitiveRoot_iff_dvd_localRootOfUnityOrder h2).mp ⟨-1, hprimitive⟩
  have hpow : ∃ n : ℕ, q = 2 ^ n := localRootOfUnityOrder_isPow 2 K _
  have hfour : (∃ ζ : K, IsPrimitiveRoot ζ 4) ↔ 4 ∣ q := by
    simpa [q] using (primitiveRoot_pow_iff_dvd_localRootOfUnityOrder h2 2)
  rw [hfour]
  obtain ⟨n, hn⟩ := hpow
  constructor
  · intro hne
    cases n with
    | zero => simp [hn] at htwo
    | succ n =>
      cases n with
      | zero => exact (hne (by simpa [hn])).elim
      | succ n =>
        rw [hn]
        simpa using (pow_dvd_pow (2 : ℕ) (by omega : 2 ≤ n.succ.succ))
  · intro hdvd heq
    have hq : q = 2 := heq
    rw [hq] at hdvd
    norm_num at hdvd

end TauCeti
