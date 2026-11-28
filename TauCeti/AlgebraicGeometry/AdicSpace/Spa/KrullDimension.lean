/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.KrullDimension
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Pair
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Topology.Sober
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.NormedField
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Spectral
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.VerticalGeneralization
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The Krull dimension of the adic spectrum of a nontrivially normed field

Let `K` be a nontrivially normed field with a nonarchimedean topology and `K⁺` a ring of integral
elements of `K`. A point of `Spv K` is the class of the valuation of a valuation subring `O` of
`K`, and it lies in `Spa(K, K⁺)` exactly when `K⁺ ⊆ O ≠ K`
(`TauCeti.ValuationSpectrum.ofValuation_valuation_mem_spa_iff`). The trivial valuation is
excluded because `K` has topologically nilpotent units, and every other `O` containing `K⁺`
gives a continuous valuation: an element of norm less than one has `O`-valuation less than one,
for otherwise the powers of its inverse would carry all of `K` into `O`.

One point specializes to another exactly when the valuation subring of the second is contained in
that of the first (`TauCeti.ValuationSpectrum.ofValuation_valuation_specializes_iff`). When `K⁺` is
a valuation ring, its overrings `O` correspond to the primes of `K⁺`, with `O = K` corresponding
to the zero ideal (`ValuationSubring.primeSpectrumOrderEquiv`). For an ultrametric norm,
`Spa(K, K⁺)` is a spectral space, so its irreducible closed subsets are the closures of its
points, and these form a chain indexed by the nonzero primes of `K⁺`. Hence

```text
dim Spa(K, K⁺) + 1 = dim K⁺,
```

the right side being the Krull dimension of `K⁺`, that is, its rank as a valuation ring
(`TauCeti.ValuationSpectrum.topologicalKrullDim_spa_field`). Both sides may be infinite. For the
largest plus ring `K⁺ = K°` the spectrum is a single point, of dimension zero
(`TauCeti.ValuationSpectrum.topologicalKrullDim_spa_powerBoundedSubring`); for a valuation ring
`K⁺ ⊊ K°` of rank two there are two points, the rank-one generization and the closed point, and
the dimension is one. The dimension is that of the topological space, which differs from the
Krull dimension `0` of the ring `K`.

## Main results

* `TauCeti.ValuationSpectrum.topologicalKrullDim_spa_field`: for a valuation ring `K⁺`,
  `dim Spa(K, K⁺) + 1 = dim K⁺`.
* `TauCeti.ValuationSpectrum.topologicalKrullDim_spa_powerBoundedSubring`: `Spa(K, K°)` has
  dimension zero.

## References

* K. Hübner, *The adic tame site*, §2, p. 5, for the dimension of the adic spectrum of a field.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.8, Definition 1.8.1,
  for the dimension of an adic space.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Chapter 4, for specializations
  of valuations as coarsenings.
-/

public section

open Filter Topology TopologicalSpace Order

namespace TauCeti.ValuationSpectrum

open Huber

variable {K : Type*} [NontriviallyNormedField K] {Kplus : Subring K}

section Nonarchimedean

variable [NonarchimedeanRing K]

/-- In a ring of integral elements `K⁺` of `K` that is a valuation ring, every element of `K` or
its inverse lies in `K⁺`. An element `x` of `K` is the quotient of `cⁿ x` by `cⁿ`, both in `K⁺` for
some `c` of norm less than one and `n` large, and one of these divides the other in `K⁺`. -/
private theorem mem_or_inv_mem (hK : IsRingOfIntegralElements Kplus) [ValuationRing Kplus]
    (x : K) : x ∈ Kplus ∨ x⁻¹ ∈ Kplus := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  have hc (n : ℕ) : c ^ n ≠ 0 := pow_ne_zero n (norm_pos_iff.mp hc0)
  obtain ⟨n, hn⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc1).mul_const
    ‖x‖).eventually (gt_mem_nhds (by simp : 0 * ‖x‖ < 1))).exists
  have hcn : c ^ n ∈ Kplus :=
    pow_mem (hK.mem_of_isTopologicallyNilpotent (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)) n
  have hxn : c ^ n * x ∈ Kplus := hK.mem_of_isTopologicallyNilpotent
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rwa [norm_mul, norm_pow]))
  rcases ValuationRing.dvd_total (⟨c ^ n * x, hxn⟩ : Kplus) ⟨c ^ n, hcn⟩ with ⟨d, hd⟩ | ⟨d, hd⟩
  · -- `cⁿ = cⁿ x d`, so `x⁻¹ = d`
    right
    have hd' : c ^ n * 1 = c ^ n * (x * d) := by
      rw [mul_one, ← mul_assoc]
      exact congrArg Subtype.val hd
    rw [inv_eq_of_mul_eq_one_right (mul_left_cancel₀ (hc n) hd').symm]
    exact d.property
  · -- `cⁿ x = cⁿ d`, so `x = d`
    left
    rw [mul_left_cancel₀ (hc n) (congrArg Subtype.val hd)]
    exact d.property

end Nonarchimedean

/-! ### Valuation rings of integral elements -/

section ValuationRing

variable [IsUltrametricDist K] (V : ValuationSubring K)

/-- `K` is the largest overring of a valuation subring `V`. -/
local instance : OrderTop {S : ValuationSubring K // V ≤ S} := Subtype.orderTop le_top

/-- The valuation subring of a point of `Spa(K, V)` is an overring of `V` other than `K`. -/
private theorem le_valuationSubring_and_ne_top (hV : IsRingOfIntegralElements V.toSubring)
    (x : spa V.toSubring) :
    V ≤ (x : Spv K).valuation.valuationSubring ∧ (x : Spv K).valuation.valuationSubring ≠ ⊤ := by
  have h := (ofValuation_valuation_mem_spa_iff hV (x : Spv K).valuation.valuationSubring).mp
    ((ofValuation_valuationSubring_valuation x.val).symm ▸ x.property)
  exact ⟨fun a ha ↦ h.1 ha, h.2⟩

/-- The points of `Spa(K, V)` are the overrings of `V` other than `K`. -/
private noncomputable def overringEquivSpa (hV : IsRingOfIntegralElements V.toSubring) :
    {S : {S : ValuationSubring K // V ≤ S} // S ≠ ⊤} ≃ spa V.toSubring where
  toFun S := ⟨ofValuation S.val.val.valuation, (ofValuation_valuation_mem_spa_iff hV _).mpr
    ⟨fun _ ha ↦ S.val.property ha, fun h ↦ S.property (Subtype.ext h)⟩⟩
  invFun x := ⟨⟨_, (le_valuationSubring_and_ne_top V hV x).1⟩,
    fun h ↦ (le_valuationSubring_and_ne_top V hV x).2 (congrArg Subtype.val h)⟩
  left_inv S := Subtype.ext (Subtype.ext S.val.val.valuationSubring_valuation_ofValuation)
  right_inv x := Subtype.ext (ofValuation_valuationSubring_valuation x.val)

/-- The irreducible closed subsets of `Spa(K, V)`, ordered by inclusion, are the overrings of `V`
other than `K`: the closure of a point corresponds to its valuation subring. -/
private noncomputable def overringOrderIsoIrreducibleCloseds
    (hV : IsRingOfIntegralElements V.toSubring) :
    {S : {S : ValuationSubring K // V ≤ S} // S ≠ ⊤} ≃o IrreducibleCloseds (spa V.toSubring) where
  toEquiv := (overringEquivSpa V hV).trans irreducibleSetEquivPoints.toEquiv.symm
  map_rel_iff' := (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
    ((subtype_specializes_iff _ _).trans ofValuation_valuation_specializes_iff)

/-- **The dimension of the adic spectrum of a field.** Let `K` be a nontrivially normed field
with an ultrametric norm and `K⁺` a ring of integral elements of `K` that is a valuation ring.
Then `dim Spa(K, K⁺) + 1 = dim K⁺`: the points of `Spa(K, K⁺)` form a chain indexed by the
nonzero primes of `K⁺`. Both sides may be infinite. -/
theorem topologicalKrullDim_spa_field (hK : IsRingOfIntegralElements Kplus)
    [ValuationRing Kplus] : topologicalKrullDim (spa Kplus) + 1 = ringKrullDim Kplus := by
  classical
  let V := ValuationSubring.ofSubring Kplus (mem_or_inv_mem hK)
  -- `V ≠ K`, since `K⁺` consists of power-bounded elements
  have hV : (⟨V, le_rfl⟩ : {S : ValuationSubring K // V ≤ S}) ≠ ⊤ := by
    intro h
    obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
    have hV' : V = ⊤ := congrArg Subtype.val h
    have hc : c⁻¹ ∈ V := by
      rw [hV']
      exact ValuationSubring.mem_top c⁻¹
    have := isPowerBounded_iff_norm_le_one.mp (hK.isPowerBounded_of_mem hc)
    rw [norm_inv] at this
    exact (one_lt_inv₀ hc0 |>.mpr hc1).not_ge this
  have : Nonempty {S : {S : ValuationSubring K // V ≤ S} // S ≠ ⊤} := ⟨⟨_, hV⟩⟩
  calc topologicalKrullDim (spa Kplus) + 1
      = krullDim {S : {S : ValuationSubring K // V ≤ S} // S ≠ ⊤} + 1 :=
        congrArg (· + 1) (krullDim_eq_of_orderIso (overringOrderIsoIrreducibleCloseds V hK)).symm
    _ = krullDim (WithTop {S : {S : ValuationSubring K // V ≤ S} // S ≠ ⊤}) :=
        krullDim_WithTop.symm
    _ = krullDim {S : ValuationSubring K // V ≤ S} :=
        krullDim_eq_of_orderIso WithTop.subtypeOrderIso
    _ = krullDim (PrimeSpectrum V)ᵒᵈ := (krullDim_eq_of_orderIso V.primeSpectrumOrderEquiv).symm
    _ = ringKrullDim Kplus := krullDim_orderDual

end ValuationRing

/-! ### The power-bounded plus ring -/

section PowerBounded

variable [IsUltrametricDist K]

/-- **`Spa(K, K°)` has dimension zero.** For a nontrivially normed field `K` with an ultrametric
norm, `Spa(K, K°)` is a single point: every point compares elements of `K` by their norms
(`TauCeti.ValuationSpectrum.vle_iff_norm_le_of_mem_spa`), and the closed unit ball `K°` is a
valuation subring of `K` other than `K`. -/
theorem topologicalKrullDim_spa_powerBoundedSubring :
    topologicalKrullDim (spa (powerBoundedSubring K)) = 0 := by
  have hmem (x : K) : x ∈ powerBoundedSubring K ↔ ‖x‖ ≤ 1 := by
    rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
  let O := ValuationSubring.ofSubring (powerBoundedSubring K) fun x ↦ by
    rcases le_total ‖x‖ 1 with h | h
    · exact .inl ((hmem x).mpr h)
    · exact .inr ((hmem _).mpr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h))
  have hO : O ≠ ⊤ := by
    intro h
    obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
    have hc : c⁻¹ ∈ O := by
      rw [h]
      exact ValuationSubring.mem_top c⁻¹
    have := (hmem _).mp hc
    rw [norm_inv] at this
    exact (one_lt_inv₀ hc0 |>.mpr hc1).not_ge this
  have hpt : ofValuation O.valuation ∈ spa (powerBoundedSubring K) :=
    (ofValuation_valuation_mem_spa_iff (isRingOfIntegralElements_powerBoundedSubring K) O).mpr
      ⟨le_rfl, hO⟩
  have : Subsingleton (spa (powerBoundedSubring K)) := ⟨fun x y ↦ Subtype.ext (ext' fun a b ↦
    (vle_iff_norm_le_of_mem_spa x.property a b).trans
      (vle_iff_norm_le_of_mem_spa y.property a b).symm)⟩
  have : Nonempty (IrreducibleCloseds (spa (powerBoundedSubring K))) :=
    ⟨⟨closure {⟨_, hpt⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact (topologicalKrullDim_zero_of_discreteTopology _).antisymm krullDim_nonneg

end PowerBounded

end TauCeti.ValuationSpectrum
