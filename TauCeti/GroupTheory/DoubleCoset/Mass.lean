/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.Field.Rat
public import TauCeti.GroupTheory.DoubleCoset.WeightedPairing
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup
import TauCeti.GroupTheory.GroupAction.CardCommute

/-!
# The mass of an orbit space and of a class set

Let a group `G` act on a type `α`. The **mass** of the orbit space is the rational number

`mass(G, α) = ∑_{x ∈ G \ α} 1 / c(x)`,

where `c(x)` is the order of the stabiliser of the orbit `x` (`TauCeti.cardStabilizerOnOrbit`).
It is the stabiliser-weighted pairing `⟨1, 1⟩` of `TauCeti.stabilizerWeightedPairing`, and it is a
function of the orbit space, so no choice of representatives enters its definition.

For a subgroup `V` of finite index in `U`, the **index formula** `mass(V, α) = [U : V] mass(U, α)`
holds with no further hypothesis. Above a `U`-orbit `p` with finite stabiliser, the `V`-orbits
carry mass `[U : V] / c_U(p)`: this is the multiplicity count behind the adjunction
`⟨f, tr h⟩_U = ⟨f|_V, h⟩_V` between pullback and the level trace, applied to the constant function
`1`, whose trace is the constant `[U : V]`. Above an orbit with infinite stabiliser all the
stabilisers are infinite and contribute nothing.

The main application is to the **class set** `Γ \ G / J` of a group `G` with subgroups `Γ` and `J`.
The double coset `Γ g J` corresponds to the `J`-orbit of the coset `g⁻¹ Γ` in `G ⧸ Γ`
(`TauCeti.doubleCosetQuotientEquivOrbitRelQuotient`), and the stabiliser of `g⁻¹ Γ` in `J` is
`J ∩ g⁻¹ Γ g`, which conjugation by `g` identifies with `Γ_g = Γ ∩ g J g⁻¹`. So the mass of the
orbit space of `J` acting on `G ⧸ Γ` is the mass of the class set,

`mass J = ∑_i 1 / |Γ_i|`, `Γ_i = Γ ∩ t_i J t_i⁻¹`,

for any representatives `t_i` of `Γ \ G / J` (`TauCeti.orbitMass_eq_finsum_doubleCoset`). For
algebraic modular forms `G` is the group of finite-adelic points of a reductive group compact at
infinity, `Γ` its rational points and `J` a compact open subgroup; the stabilisers `Γ_i` are then
finite, and for `J' ≤ J` of finite index the index formula reads `mass J' = [J : J'] · mass J`.

## Main definitions

* `TauCeti.orbitMass G α`: the mass `∑_x 1 / c(x)` of the orbit space of `G` acting on `α`.
* `TauCeti.orbitSum G α F`: the weighted orbit sum `∑_x c(x)⁻¹ F(x)` of a function on the orbit
  space with values in a `ℚ`-vector space; `TauCeti.orbitSum_one` identifies it with the mass for
  `F = 1`.

## Main results

* `TauCeti.orbitMass_eq_stabilizerWeightedPairing`: the mass is the pairing `⟨1, 1⟩`.
* `TauCeti.orbitMass_eq_natCard_of_cardStabilizerOnOrbit_eq_one`: with trivial stabilisers the
  mass counts the orbits.
* `TauCeti.natCard_mul_orbitMass`: for a finite group, `|G| · mass = |α|`.
* `TauCeti.finsum_mem_inv_cardStabilizerOnOrbit_preimage`: the orbits above one orbit carry
  `[U : V]` times its mass.
* `TauCeti.orbitSum_comp_map_of_le`: the index formula for weighted orbit sums,
  `∑_{V \ α} c_V⁻¹ F = [U : V] ∑_{U \ α} c_U⁻¹ F` for `F` pulled back from the `U`-orbits.
* `TauCeti.orbitMass_eq_relIndex_mul_of_le`: **the index formula**
  `mass(V, α) = [U : V] mass(U, α)`.
* `TauCeti.orbitMass_eq_natCard_of_mackeySubgroup_eq_bot`: with trivial stabilisers `Γ_i` the
  mass counts the classes.
* `TauCeti.orbitMass_eq_finsum_doubleCoset`: the mass of the class set as `∑_i 1 / |Γ_i|`, for
  any representatives; `TauCeti.orbitMass_eq_finsum_doubleCoset_stabilizer` is the same sum with
  the stabilisers `J ∩ t_i⁻¹ Γ t_i` of the cosets read inside `J`.

## References

* B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§4–8.
* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, ch. 3.

The index formula and the independence of the class-set mass from the representatives are
adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/Adelic/Hecke/ClassSums.lean`, declarations
`New.classSum_one_of_le` and `New.classSum_eq_relIndex_smul`, and file
`src/Lib/Adelic/Hecke/Basic.lean`, declarations `New.classSum_eq_finsum_of_rep` and
`New.card_classAut_mul_mul`.
-/

public section

open MulAction

namespace TauCeti

section Orbit

variable (G α : Type*) [Group G] [MulAction G α]

/-- **The mass of an orbit space**: the sum `∑_x 1 / c(x)` over the orbits `x` of `G` acting on
`α`, where `c(x)` is the order of the stabiliser of `x` (`cardStabilizerOnOrbit`). An orbit with
infinite stabiliser contributes `0`, since `Nat.card` of an infinite type is `0` and `0⁻¹ = 0`;
the sum is a `finsum`, so the mass is `0` when the summand has infinite support. -/
noncomputable def orbitMass : ℚ :=
  ∑ᶠ x : orbitRel.Quotient G α, (cardStabilizerOnOrbit x : ℚ)⁻¹

theorem orbitMass_def :
    orbitMass G α = ∑ᶠ x : orbitRel.Quotient G α, (cardStabilizerOnOrbit x : ℚ)⁻¹ :=
  (rfl)

variable {G α}

/-- The mass is the stabiliser-weighted pairing of the constant function `1` with itself. -/
theorem orbitMass_eq_stabilizerWeightedPairing :
    orbitMass G α = stabilizerWeightedPairing (1 : orbitRel.Quotient G α → ℚ) 1 := by
  simp [orbitMass_def, stabilizerWeightedPairing_def]

/-- The mass is nonnegative. -/
theorem orbitMass_nonneg : 0 ≤ orbitMass G α :=
  finsum_nonneg fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- **With trivial stabilisers, the mass counts the orbits.** When there are infinitely many
orbits both sides are `0`. -/
theorem orbitMass_eq_natCard_of_cardStabilizerOnOrbit_eq_one
    (h : ∀ x : orbitRel.Quotient G α, cardStabilizerOnOrbit x = 1) :
    orbitMass G α = Nat.card (orbitRel.Quotient G α) := by
  simp only [orbitMass_def, h, Nat.cast_one, inv_one]
  cases finite_or_infinite (orbitRel.Quotient G α) with
  | inl _ =>
    have := Fintype.ofFinite (orbitRel.Quotient G α)
    simp [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  | inr _ =>
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
    exact finsum_of_infinite_support (by
      rw [Function.support_const one_ne_zero]
      exact Set.infinite_univ)

/-- **The mass is invariant under an equivariant equivalence.** An equivalence `e : α ≃ β`
carrying the action of `G` to that of `H` along `φ : G ≃* H` preserves the mass. -/
theorem orbitMass_congr {H β : Type*} [Group H] [MulAction H β] (φ : G ≃* H) (e : α ≃ β)
    (he : ∀ (g : G) (a : α), e (g • a) = φ g • e a) :
    orbitMass G α = orbitMass H β := by
  rw [orbitMass_def, orbitMass_def, ← finsum_comp_equiv (MulAction.orbitRelQuotientCongr φ e he)]
  simp only [cardStabilizerOnOrbit_orbitRelQuotientCongr]

/-- **The mass of a finite group action**: for a finite group `G` acting on `α`,
`|G| · mass(G, α) = |α|`. This is the class formula `|α| = ∑_x |G| / c(x)`; when `α` is infinite
both sides are `0`. -/
theorem natCard_mul_orbitMass [Finite G] : (Nat.card G : ℚ) * orbitMass G α = Nat.card α := by
  rw [card_eq_finsum_card_group_div_cardStabilizerOnOrbit G α ℚ, orbitMass_def, mul_finsum]
  simp only [div_eq_mul_inv]

variable (G α) in
/-- **The weighted orbit sum** of a function `F` on the orbit space of `G` acting on `α`, with
values in a `ℚ`-vector space: `∑_x c(x)⁻¹ F(x)`, where `c(x)` is the order of the stabiliser of
the orbit `x` (`cardStabilizerOnOrbit`). An orbit with infinite stabiliser has weight `0`, and the
sum is `0` when its summand has infinite support. For `F = 1` it is the mass
(`TauCeti.orbitSum_one`). -/
noncomputable def orbitSum {W : Type*} [AddCommGroup W] [Module ℚ W]
    (F : orbitRel.Quotient G α → W) : W :=
  ∑ᶠ x, (cardStabilizerOnOrbit x : ℚ)⁻¹ • F x

variable (G α) in
theorem orbitSum_def {W : Type*} [AddCommGroup W] [Module ℚ W] (F : orbitRel.Quotient G α → W) :
    orbitSum G α F = ∑ᶠ x, (cardStabilizerOnOrbit x : ℚ)⁻¹ • F x :=
  (rfl)

/-- The weighted orbit sum of the constant function `1` is the mass. -/
theorem orbitSum_one : orbitSum G α (fun _ ↦ (1 : ℚ)) = orbitMass G α := by
  simp [orbitSum_def, orbitMass_def]

/-- **The weighted orbit sum is invariant under an equivariant equivalence.** An equivalence
`e : α ≃ β` carrying the action of `G` to that of `H` along `φ : G ≃* H` preserves weighted orbit
sums. -/
theorem orbitSum_congr {H β W : Type*} [Group H] [MulAction H β] [AddCommGroup W] [Module ℚ W]
    (φ : G ≃* H) (e : α ≃ β) (he : ∀ (g : G) (a : α), e (g • a) = φ g • e a)
    (F : orbitRel.Quotient H β → W) :
    orbitSum G α (F ∘ MulAction.orbitRelQuotientCongr φ e he) = orbitSum H β F := by
  rw [orbitSum_def, orbitSum_def, ← finsum_comp_equiv (MulAction.orbitRelQuotientCongr φ e he)]
  simp only [Function.comp_apply, cardStabilizerOnOrbit_orbitRelQuotientCongr]

end Orbit

section LevelTrace

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The mass above one orbit.** For `V ≤ U` of finite index, the `V`-orbits lying over a
`U`-orbit `p` carry mass `[U : V] / c_U(p)`. When the stabiliser of `p` is infinite both sides
are `0`. -/
theorem finsum_mem_inv_cardStabilizerOnOrbit_preimage {V U : Subgroup G} (hle : V ≤ U)
    [V.IsFiniteRelIndex U] (p : orbitRel.Quotient U α) :
    ∑ᶠ q ∈ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hle) ⁻¹' {p},
        (cardStabilizerOnOrbit q : ℚ)⁻¹ =
      V.relIndex U * (cardStabilizerOnOrbit p : ℚ)⁻¹ := by
  by_cases hp : cardStabilizerOnOrbit p = 0
  · -- the stabilisers of the orbits above `p` are infinite too
    rw [hp, Nat.cast_zero, inv_zero, mul_zero]
    refine finsum_mem_of_eqOn_zero fun q hq ↦ ?_
    induction q using Quotient.inductionOn' with | h x => ?_
    rw [Set.mem_preimage, TauCeti.Setoid.map_of_le_mk, Set.mem_singleton_iff] at hq
    rw [← hq, cardStabilizerOnOrbit_mk] at hp
    rw [cardStabilizerOnOrbit_mk, Pi.zero_apply, inv_eq_zero, Nat.cast_eq_zero]
    exact not_not.mp fun h ↦ (natCard_stabilizer_ne_zero_iff_of_le hle x).mp h hp
  · -- the multiplicity count for the level trace of `1`, which is the constant `[U : V]`
    have h := inverse_cardStabilizerOnOrbit_smul_levelTrace (R := ℚ) hle
      (1 : orbitRel.Quotient V α → ℚ) p
      (Nat.cast_ne_zero.mpr hp).isUnit
    rw [levelTrace_one] at h
    simpa [mul_comm] using h.symm

/-- **The index formula for weighted orbit sums.** For `V ≤ U` of finite index and a function `F`
on the `U`-orbits with values in a `ℚ`-vector space, the weighted sum over the `V`-orbits of `F`
pulled back is `[U : V]` times the weighted sum over the `U`-orbits:
`∑_{y ∈ V \ α} c_V(y)⁻¹ F(U y) = [U : V] ∑_{x ∈ U \ α} c_U(x)⁻¹ F(x)`. No finiteness of the orbit
spaces or of the stabilisers is assumed. -/
theorem orbitSum_comp_map_of_le {W : Type*} [AddCommGroup W] [Module ℚ W] {V U : Subgroup G}
    (hle : V ≤ U) [V.IsFiniteRelIndex U] (F : orbitRel.Quotient U α → W) :
    orbitSum V α (F ∘ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hle)) =
      V.relIndex U • orbitSum U α F := by
  -- Orbit by orbit this is `finsum_mem_inv_cardStabilizerOnOrbit_preimage`. The `V`-orbits in the
  -- support are the orbits lying over the `U`-orbits in the support, finitely many above each, so
  -- when there are infinitely many of either kind both sums are `0`.
  set π := Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (X := α) hle)
  simp only [orbitSum_def, Function.comp_apply]
  set fV : orbitRel.Quotient V α → W := fun q ↦ (cardStabilizerOnOrbit q : ℚ)⁻¹ • F (π q)
  set fU : orbitRel.Quotient U α → W := fun p ↦ (cardStabilizerOnOrbit p : ℚ)⁻¹ • F p
  -- a `V`-orbit has finite stabiliser exactly when the `U`-orbit below it has
  have hsupp : Function.support fV = π ⁻¹' Function.support fU := by
    ext q
    induction q using Quotient.inductionOn' with | h x => ?_
    simp only [Function.mem_support, Set.mem_preimage, fV, fU, π, TauCeti.Setoid.map_of_le_mk,
      cardStabilizerOnOrbit_mk, ne_eq, smul_eq_zero, inv_eq_zero, Nat.cast_eq_zero, not_or]
    exact and_congr_left' (natCard_stabilizer_ne_zero_iff_of_le hle x)
  have hπ : Function.Surjective π := fun p ↦ by
    induction p using Quotient.inductionOn' with | h x => exact ⟨Quotient.mk'' x, rfl⟩
  have hfib (p : orbitRel.Quotient U α) : (π ⁻¹' {p}).Finite :=
    Set.finite_coe_iff.mp (finite_fiber_orbitRel_map_of_isFiniteRelIndex (X := α) hle p)
  by_cases hfin : (Function.support fU).Finite
  · rw [← finsum_mem_support fV, ← finsum_mem_support fU, hsupp,
      ← Set.biUnion_preimage_singleton,
      finsum_mem_biUnion (Set.pairwiseDisjoint_fiber π _) hfin fun p _ ↦ hfib p,
      smul_finsum_mem hfin]
    refine finsum_mem_congr rfl fun p _ ↦ ?_
    have h_fib : ∑ᶠ q ∈ π ⁻¹' {p}, fV q =
        (∑ᶠ q ∈ π ⁻¹' {p}, (cardStabilizerOnOrbit q : ℚ)⁻¹) • F p := by
      rw [finsum_mem_def, finsum_mem_def, finsum_smul]
      refine finsum_congr fun q ↦ ?_
      by_cases hq : q ∈ π ⁻¹' {p}
      · have hπq : π q = p := by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hq
        simp only [Set.indicator_of_mem hq, fV, hπq]
      · simp only [Set.indicator_of_notMem hq, zero_smul]
    rw [h_fib, finsum_mem_inv_cardStabilizerOnOrbit_preimage hle p, mul_smul,
      Nat.cast_smul_eq_nsmul]
  · -- infinitely many `U`-orbits in the support, hence infinitely many `V`-orbits
    have hinf : (Function.support fV).Infinite := fun h ↦ hfin (by
      rw [← Set.image_preimage_eq (Function.support fU) hπ, ← hsupp]
      exact h.image π)
    rw [finsum_of_infinite_support hinf, finsum_of_infinite_support hfin, smul_zero]

/-- **The index formula for the mass.** For `V ≤ U` of finite index,
`mass(V, α) = [U : V] · mass(U, α)`. No finiteness of the orbit spaces or of the stabilisers is
assumed. -/
theorem orbitMass_eq_relIndex_mul_of_le {V U : Subgroup G} (hle : V ≤ U) [V.IsFiniteRelIndex U] :
    orbitMass V α = V.relIndex U * orbitMass U α := by
  simpa [orbitSum_one, nsmul_eq_mul, Function.comp_def] using
    orbitSum_comp_map_of_le (α := α) hle fun _ ↦ (1 : ℚ)

end LevelTrace

section ClassSet

variable {G : Type*} [Group G] (Γ J : Subgroup G)

/-- The stabiliser order of the orbit of `g⁻¹ Γ` is the order of `J ∩ g⁻¹ Γ g`, the stabiliser of
the class `Γ g J` read inside `J` (`TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`). -/
theorem cardStabilizerOnOrbit_doubleCosetQuotientEquivOrbitRelQuotient_mk (g : G) :
    cardStabilizerOnOrbit (doubleCosetQuotientEquivOrbitRelQuotient Γ J (DoubleCoset.mk Γ J g)) =
      Nat.card ((mackeySubgroup g⁻¹ Γ J).subgroupOf J) := by
  rw [doubleCosetQuotientEquivOrbitRelQuotient_mk, cardStabilizerOnOrbit_mk,
    stabilizer_eq_mackeySubgroup_subgroupOf]

variable {Γ J}

/-- **The mass of the class set**, with the stabilisers read inside `J`: for any representatives
`c q` of the double cosets `q ∈ Γ \ G / J`, the mass of `J` acting on `G ⧸ Γ` is
`∑_q 1 / |J ∩ (c q)⁻¹ Γ (c q)|`. These are the stabilisers indexing the evaluation equivalence
`Representation.levelFormsEquivPi` of level forms. -/
theorem orbitMass_eq_finsum_doubleCoset_stabilizer (c : DoubleCoset.Quotient (Γ : Set G) J → G)
    (hc : ∀ q, DoubleCoset.mk Γ J (c q) = q) :
    orbitMass J (G ⧸ Γ) =
      ∑ᶠ q, (Nat.card ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) : ℚ)⁻¹ := by
  rw [orbitMass_def, ← finsum_comp_equiv (doubleCosetQuotientEquivOrbitRelQuotient Γ J)]
  refine finsum_congr fun q ↦ ?_
  conv_lhs => rw [← hc q]
  rw [cardStabilizerOnOrbit_doubleCosetQuotientEquivOrbitRelQuotient_mk]

/-- **The mass of the class set** `mass J = ∑_i 1 / |Γ_i|`, `Γ_i = Γ ∩ t_i J t_i⁻¹`, for any
representatives `t_i = c q` of the double cosets `q ∈ Γ \ G / J`. The left side does not mention
the representatives, so neither does the sum. -/
theorem orbitMass_eq_finsum_doubleCoset (c : DoubleCoset.Quotient (Γ : Set G) J → G)
    (hc : ∀ q, DoubleCoset.mk Γ J (c q) = q) :
    orbitMass J (G ⧸ Γ) = ∑ᶠ q, (Nat.card (mackeySubgroup (c q) J Γ) : ℚ)⁻¹ := by
  simp only [orbitMass_eq_finsum_doubleCoset_stabilizer c hc,
    natCard_mackeySubgroup_inv_subgroupOf]

/-- Every orbit of `J` on `G ⧸ Γ` has the stabiliser order `|Γ ∩ g J g⁻¹|` of some `g`. -/
private theorem forall_cardStabilizerOnOrbit {P : ℕ → Prop}
    (h : ∀ g : G, P (Nat.card (mackeySubgroup g J Γ))) (p : orbitRel.Quotient J (G ⧸ Γ)) :
    P (cardStabilizerOnOrbit p) := by
  obtain ⟨q, rfl⟩ := (doubleCosetQuotientEquivOrbitRelQuotient Γ J).surjective p
  rw [← DoubleCoset.out_eq' q, cardStabilizerOnOrbit_doubleCosetQuotientEquivOrbitRelQuotient_mk,
    natCard_mackeySubgroup_inv_subgroupOf]
  exact h _

/-- If `Γ ∩ g J g⁻¹` is trivial for every `g`, every orbit of `J` on `G ⧸ Γ` has trivial
stabiliser. -/
theorem cardStabilizerOnOrbit_eq_one_of_mackeySubgroup_eq_bot
    (h : ∀ g : G, mackeySubgroup g J Γ = ⊥) (p : orbitRel.Quotient J (G ⧸ Γ)) :
    cardStabilizerOnOrbit p = 1 :=
  forall_cardStabilizerOnOrbit (P := (· = 1)) (fun g ↦ by rw [h g, Subgroup.card_bot]) p

/-- **The mass of a class set with trivial stabilisers** is the number of classes: if
`Γ ∩ g J g⁻¹` is trivial for every `g`, then `mass J = #(Γ \ G / J)`. -/
theorem orbitMass_eq_natCard_of_mackeySubgroup_eq_bot (h : ∀ g : G, mackeySubgroup g J Γ = ⊥) :
    orbitMass J (G ⧸ Γ) = Nat.card (DoubleCoset.Quotient (Γ : Set G) J) := by
  rw [orbitMass_eq_natCard_of_cardStabilizerOnOrbit_eq_one
      (cardStabilizerOnOrbit_eq_one_of_mackeySubgroup_eq_bot h),
    Nat.card_congr (doubleCosetQuotientEquivOrbitRelQuotient Γ J)]

end ClassSet

end TauCeti
