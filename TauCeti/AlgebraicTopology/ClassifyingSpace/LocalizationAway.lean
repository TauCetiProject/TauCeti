/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicTopology.ClassifyingSpace.WedgeCircles
public import TauCeti.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.Tactic.LinearCombination

/-!
# The homology of the classifying space of `ℤ[1/m]`

For a nonzero integer `m`, the additive group of `ℤ[1/m] = Localization.Away m` is the directed
union of its infinite cyclic subgroups `m⁻ʳ ℤ`. Each of these is a free group, whose group homology
with trivial coefficients vanishes in degrees `n ≥ 2` (`TauCeti.isZero_groupHomology_freeGroup`).
Every class of a directed union of subgroups comes from a member, so its homology vanishes if it
vanishes on each member (`TauCeti.groupHomology.isZero_groupHomology_of_directed`); for directed
unions of infinite cyclic subgroups this is `TauCeti.isZero_groupHomology_of_directed_zpowers`.
Hence

* `Hₙ(ℤ[1/m], k) = 0` for `n ≥ 2` and every commutative ring `k`
  (`TauCeti.isZero_groupHomology_localizationAway`);
* `H₁(ℤ[1/m], k) = ℤ[1/m] ⊗ k` vanishes when `m = 0` in `k`, since `ℤ[1/m]` is `m`-divisible
  (`TauCeti.isZero_groupHomology_one_localizationAway`, an instance of
  `TauCeti.groupHomology.isZero_H1_of_forall_exists_zpow_eq`).

Through the identification of the singular homology of Milnor's classifying space `BG` with the
group homology of `G`, the classifying space `K(ℤ[1/m], 1)` has the homology of a point with
coefficients in any ring `k` in which `m = 0`
(`TauCeti.isZero_classifyingSpace_singularHomology_localizationAway`). For `m = 2` and
`k = 𝔽₂` this is the mod-two acyclicity of `K(ℤ[1/2], 1)`, the basic case of the vanishing of
the reduced mod-two homology of `K(A, 1)` for every uniquely two-divisible abelian group `A`.

## Main results

* `TauCeti.isZero_groupHomology_localizationAway`: `Hₙ(ℤ[1/m], k) = 0` for `n ≥ 2`.
* `TauCeti.isZero_groupHomology_one_localizationAway`: `H₁(ℤ[1/m], k) = 0` when `m = 0` in `k`.
* `TauCeti.isZero_classifyingSpace_singularHomology_localizationAway`: the classifying space
  of `ℤ[1/m]` has no homology in positive degrees with coefficients in which `m = 0`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer, 1982,
  Chapter V, Proposition 5.3.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

open CategoryTheory Limits groupHomology

namespace TauCeti

variable (k : Type) [CommRing k]

section LocalizationAway

open IsLocalization.Away

variable {m : ℤ}

/-- The generator `m⁻ʳ` of the subgroup `m⁻ʳ ℤ` of `ℤ[1/m]`, in multiplicative notation. -/
private noncomputable abbrev invPowGen (m : ℤ) (r : ℕ) : Multiplicative (Localization.Away m) :=
  Multiplicative.ofAdd (invSelf m ^ r)

/-- The `a`-th power of the generator `m⁻ʳ` is `a m⁻ʳ`, in additive notation. -/
private theorem toAdd_invPowGen_zpow (r : ℕ) (a : ℤ) :
    (invPowGen m r ^ a).toAdd = algebraMap ℤ (Localization.Away m) a * invSelf m ^ r := by
  rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, eq_intCast]

private theorem invPowGen_mem_zpowers_succ (r : ℕ) :
    invPowGen m r ∈ Subgroup.zpowers (invPowGen m (r + 1)) := by
  refine Subgroup.mem_zpowers_iff.2 ⟨m, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_invPowGen_zpow, toAdd_ofAdd]
  linear_combination invSelf m ^ r * mul_invSelf (S := Localization.Away m) m

private theorem directed_zpowers_invPowGen :
    Directed (· ≤ ·) fun r ↦ Subgroup.zpowers (invPowGen m r) :=
  Monotone.directed_le <| monotone_nat_of_le_succ fun r ↦
    Subgroup.zpowers_le.2 (invPowGen_mem_zpowers_succ r)

private theorem iSup_zpowers_invPowGen : ⨆ r, Subgroup.zpowers (invPowGen m r) = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ (Subgroup.mem_iSup_of_directed directed_zpowers_invPowGen).2 ?_
  -- every element of `ℤ[1/m]` is `a / mʳ` for some integer `a` and some `r`
  obtain ⟨r, a, h⟩ := surj m y.toAdd
  refine ⟨r, Subgroup.mem_zpowers_iff.2 ⟨a, Multiplicative.toAdd.injective ?_⟩⟩
  have hr : (algebraMap ℤ (Localization.Away m) m * invSelf m) ^ r = 1 := by
    rw [mul_invSelf, one_pow]
  rw [toAdd_invPowGen_zpow]
  linear_combination -(invSelf m ^ r) * h + y.toAdd * hr

private theorem not_isOfFinOrder_invPowGen (hm : m ≠ 0) (r : ℕ) :
    ¬IsOfFinOrder (invPowGen m r) := by
  intro h
  obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_zpow_eq_one.1 h
  replace hn1 := congrArg Multiplicative.toAdd hn1
  rw [toAdd_invPowGen_zpow, toAdd_one] at hn1
  -- clearing the denominator `mʳ`, the integer `n` vanishes in `ℤ[1/m]`
  have hr : (algebraMap ℤ (Localization.Away m) m * invSelf m) ^ r = 1 := by
    rw [mul_invSelf, one_pow]
  have hn0 : algebraMap ℤ (Localization.Away m) n = 0 := by
    linear_combination algebraMap ℤ (Localization.Away m) m ^ r * hn1 -
      algebraMap ℤ (Localization.Away m) n * hr
  obtain ⟨⟨c, j, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers m) _ n).1 hn0
  exact hn ((mul_eq_zero.1 hc).resolve_left (pow_ne_zero _ hm))

/-- **The homology of `ℤ[1/m]` in degrees at least two.** For a nonzero integer `m`, the group
homology of the additive group of `ℤ[1/m]` with trivial coefficients vanishes in degrees `n ≥ 2`. -/
theorem isZero_groupHomology_localizationAway (hm : m ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (groupHomology (Rep.trivial k (Multiplicative (Localization.Away m)) k) n) :=
  isZero_groupHomology_of_directed_zpowers k (not_isOfFinOrder_invPowGen hm)
    directed_zpowers_invPowGen iSup_zpowers_invPowGen hn

/-- **The first homology of `ℤ[1/m]`.** If `m = 0` in `k`, the first group homology of the
additive group of `ℤ[1/m]` with trivial coefficients `k` vanishes: it is `ℤ[1/m] ⊗ k`, and
`ℤ[1/m]` is divisible by `m`. -/
theorem isZero_groupHomology_one_localizationAway (hmk : (m : k) = 0) :
    IsZero (groupHomology (Rep.trivial k (Multiplicative (Localization.Away m)) k) 1) :=
  TauCeti.groupHomology.isZero_H1_of_forall_exists_zpow_eq _ m
    (fun g ↦ ⟨Multiplicative.ofAdd (invSelf m * g.toAdd), Multiplicative.toAdd.injective <| by
      rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, ← eq_intCast (algebraMap ℤ (Localization.Away m))]
      linear_combination g.toAdd * mul_invSelf (S := Localization.Away m) m⟩)
    fun c ↦ by rw [zsmul_eq_mul, hmk, zero_mul]

/-- **The classifying space of `ℤ[1/m]` is acyclic modulo `m`.** For a nonzero integer `m` and a
commutative ring `k` in which `m = 0`, the singular homology of the classifying space of the
additive group of `ℤ[1/m]` with coefficients in `k` vanishes in every positive degree. For
`m = 2` and `k = ZMod 2`, the space `K(ℤ[1/2], 1)` has the mod-two homology of a point. -/
theorem isZero_classifyingSpace_singularHomology_localizationAway (hm : m ≠ 0)
    (hmk : (m : k) = 0) {n : ℕ} (hn : 1 ≤ n) :
    IsZero (((singularChains k).obj
      (TopCat.of (classifyingSpace (Multiplicative (Localization.Away m))))).homology n) := by
  refine IsZero.of_iso ?_ (classifyingSpaceSingularHomologyIsoGroupHomology k _ n)
  obtain rfl | hn := hn.eq_or_lt
  · exact isZero_groupHomology_one_localizationAway k hmk
  · exact isZero_groupHomology_localizationAway k hm hn

end LocalizationAway

end TauCeti
