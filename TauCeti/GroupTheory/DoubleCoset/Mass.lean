/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import TauCeti.GroupTheory.DoubleCoset.WeightedPairing
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup
import Mathlib.Tactic.Group
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
* `TauCeti.doubleCosetQuotientEquivOrbitRelQuotient Γ J`: the class set `Γ \ G / J` as the orbit
  space of `J` acting on `G ⧸ Γ`.

## Main results

* `TauCeti.orbitMass_eq_stabilizerWeightedPairing`: the mass is the pairing `⟨1, 1⟩`.
* `TauCeti.orbitMass_eq_natCard_of_cardStabilizerOnOrbit_eq_one`: with trivial stabilisers the
  mass counts the orbits.
* `TauCeti.natCard_mul_orbitMass`: for a finite group, `|G| · mass = |α|`.
* `TauCeti.levelTrace_one`: the level trace of `1` is the constant index `[U : V]`.
* `TauCeti.finsum_mem_inv_cardStabilizerOnOrbit_preimage`: the orbits above one orbit carry
  `[U : V]` times its mass.
* `TauCeti.orbitMass_of_le`: **the index formula** `mass(V, α) = [U : V] mass(U, α)`.
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
`New.card_classAut_mul_mul`. There the class sum is defined through chosen representatives of
`Γ \ G / J` and the index formula is proved by double counting; here the mass is a function of the
orbit space and the index formula is the multiplicity count
`TauCeti.inverse_cardStabilizerOnOrbit_smul_levelTrace` of the level trace, orbit by orbit.
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

end Orbit

section LevelTrace

variable {G α : Type*} [Group G] [MulAction G α]

/-- **The level trace of `1` is the index**: for `V` of finite relative index in `U`, the trace
from `V`-orbits to `U`-orbits of the constant function `1` is the constant `[U : V]`. -/
theorem levelTrace_one {R : Type*} [AddCommMonoidWithOne R] (V U : Subgroup G)
    [V.IsFiniteRelIndex U] :
    levelTrace V U (1 : orbitRel.Quotient V α → R) = fun _ ↦ (V.relIndex U : R) := by
  funext p
  induction p using Quotient.inductionOn' with
  | h x =>
    have := Fintype.ofFinite (U ⧸ V.subgroupOf U)
    rw [levelTrace_mk, finsum_eq_sum_of_fintype]
    simp [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

/-- **Stabilisers are finite in a subgroup of finite index exactly when they are finite in the
larger group.** For `V ≤ U` of finite index, the stabiliser of `x` in `V` is the intersection of
its stabiliser in `U` with `V`, which has finite index in it. Finiteness is stated as
`Nat.card ≠ 0`. -/
theorem natCard_stabilizer_ne_zero_iff_of_le {V U : Subgroup G} (hle : V ≤ U)
    [V.IsFiniteRelIndex U] (x : α) :
    Nat.card (stabilizer V x) ≠ 0 ↔ Nat.card (stabilizer U x) ≠ 0 := by
  set H : Subgroup U := V.subgroupOf U
  -- `H ⊓ stabilizer U x` is the stabiliser of `x` in `V`, read inside `U`
  have he : (H ⊓ stabilizer U x : Subgroup U) ≃ stabilizer V x :=
    { toFun u := ⟨⟨u.val.val, Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp u.property).1⟩,
        (Subgroup.mem_inf.mp u.property).2⟩
      invFun v := ⟨⟨v.val.val, hle v.val.property⟩, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mpr v.val.property, v.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have := Subgroup.isFiniteRelIndex_of_finiteIndex (H := H) (K := stabilizer U x)
  rw [← Subgroup.relIndex_mul_card (H := H) (K := stabilizer U x), Nat.card_congr he]
  exact ⟨mul_ne_zero Subgroup.relIndex_ne_zero, right_ne_zero_of_mul⟩

/-- **The mass above one orbit.** For `V ≤ U` of finite index, the `V`-orbits lying over a
`U`-orbit `p` carry mass `[U : V] / c_U(p)`. When the stabiliser of `p` is finite this is the
multiplicity count `inverse_cardStabilizerOnOrbit_smul_levelTrace` for the trace of `1`; when it
is infinite, so are the stabilisers of the orbits above `p`, and both sides are `0`. -/
theorem finsum_mem_inv_cardStabilizerOnOrbit_preimage {V U : Subgroup G} (hle : V ≤ U)
    [V.IsFiniteRelIndex U] (p : orbitRel.Quotient U α) :
    ∑ᶠ q ∈ Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le hle) ⁻¹' {p},
        (cardStabilizerOnOrbit q : ℚ)⁻¹ =
      V.relIndex U * (cardStabilizerOnOrbit p : ℚ)⁻¹ := by
  by_cases hp : cardStabilizerOnOrbit p = 0
  · rw [hp, Nat.cast_zero, inv_zero, mul_zero]
    refine finsum_mem_of_eqOn_zero fun q hq ↦ ?_
    induction q using Quotient.inductionOn' with | h x => ?_
    rw [Set.mem_preimage, TauCeti.Setoid.map_of_le_mk, Set.mem_singleton_iff] at hq
    rw [← hq, cardStabilizerOnOrbit_mk] at hp
    rw [cardStabilizerOnOrbit_mk, Pi.zero_apply, inv_eq_zero, Nat.cast_eq_zero]
    exact not_not.mp fun h ↦ (natCard_stabilizer_ne_zero_iff_of_le hle x).mp h hp
  · have h := inverse_cardStabilizerOnOrbit_smul_levelTrace (R := ℚ) hle
      (1 : orbitRel.Quotient V α → ℚ) p
      (Nat.cast_ne_zero.mpr hp).isUnit
    rw [levelTrace_one] at h
    simpa [mul_comm] using h.symm

/-- **The index formula for the mass.** For `V ≤ U` of finite index,
`mass(V, α) = [U : V] · mass(U, α)`. Orbit by orbit this is
`finsum_mem_inv_cardStabilizerOnOrbit_preimage`. No finiteness of the orbit spaces or of the
stabilisers is needed: the `V`-orbits with finite stabiliser are the orbits lying over the
`U`-orbits with finite stabiliser, finitely many above each, so when there are infinitely many of
either kind both masses are `0`. -/
theorem orbitMass_of_le {V U : Subgroup G} (hle : V ≤ U) [V.IsFiniteRelIndex U] :
    orbitMass V α = V.relIndex U * orbitMass U α := by
  set π := Setoid.map_of_le (MulAction.orbitRel_le_of_subgroup_le (X := α) hle)
  set fV : orbitRel.Quotient V α → ℚ := fun q ↦ (cardStabilizerOnOrbit q : ℚ)⁻¹
  set fU : orbitRel.Quotient U α → ℚ := fun p ↦ (cardStabilizerOnOrbit p : ℚ)⁻¹
  -- a `V`-orbit has finite stabiliser exactly when the `U`-orbit below it has
  have hsupp : Function.support fV = π ⁻¹' Function.support fU := by
    ext q
    induction q using Quotient.inductionOn' with | h x => ?_
    simp only [Function.mem_support, Set.mem_preimage, fV, fU, π, TauCeti.Setoid.map_of_le_mk,
      cardStabilizerOnOrbit_mk, ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    exact natCard_stabilizer_ne_zero_iff_of_le hle x
  have hπ : Function.Surjective π := fun p ↦ by
    induction p using Quotient.inductionOn' with | h x => exact ⟨Quotient.mk'' x, rfl⟩
  have hfib (p : orbitRel.Quotient U α) : (π ⁻¹' {p}).Finite :=
    Set.finite_coe_iff.mp (finite_fiber_orbitRel_map_of_isFiniteRelIndex (X := α) hle p)
  change ∑ᶠ q, fV q = V.relIndex U * ∑ᶠ p, fU p
  by_cases hfin : (Function.support fU).Finite
  · rw [← finsum_mem_support fV, ← finsum_mem_support fU, hsupp,
      ← Set.biUnion_preimage_singleton,
      finsum_mem_biUnion (Set.pairwiseDisjoint_fiber π _) hfin fun p _ ↦ hfib p, mul_finsum_mem]
    exact finsum_mem_congr rfl fun p _ ↦ finsum_mem_inv_cardStabilizerOnOrbit_preimage hle p
  · -- infinitely many `U`-orbits with finite stabiliser, hence infinitely many such `V`-orbits
    have hinf : (Function.support fV).Infinite := fun h ↦ hfin (by
      rw [← Set.image_preimage_eq (Function.support fU) hπ, ← hsupp]
      exact h.image π)
    rw [finsum_of_infinite_support hinf, finsum_of_infinite_support hfin, mul_zero]

end LevelTrace

section ClassSet

variable {G : Type*} [Group G] (Γ J : Subgroup G)

/-- Two cosets `g⁻¹ Γ` and `h⁻¹ Γ` lie in one `J`-orbit exactly when `g` and `h` lie in one
double coset `Γ g J`. -/
theorem mk_inv_eq_mk_inv_iff {g h : G} :
    (Quotient.mk'' ((g⁻¹ : G) : G ⧸ Γ) : orbitRel.Quotient J (G ⧸ Γ)) =
        Quotient.mk'' ((h⁻¹ : G) : G ⧸ Γ) ↔
      DoubleCoset.mk Γ J g = DoubleCoset.mk Γ J h := by
  rw [Quotient.eq'', orbitRel_apply, ← mem_doubleCoset_iff_mk_mem_orbit,
    DoubleCoset.mem_doubleCoset, DoubleCoset.eq]
  constructor
  · rintro ⟨u, hu, γ, hγ, h'⟩
    exact ⟨γ, hγ, u, hu, by rw [← inv_inv g, h']; group⟩
  · rintro ⟨γ, hγ, u, hu, h'⟩
    exact ⟨u, hu, γ, hγ, by rw [h']; group⟩

/-- **The class set as an orbit space.** The double coset space `Γ \ G / J` is the orbit space of
`J` acting on the left cosets `G ⧸ Γ`, by `Γ g J ↦ J • g⁻¹ Γ`. -/
noncomputable def doubleCosetQuotientEquivOrbitRelQuotient :
    DoubleCoset.Quotient (Γ : Set G) J ≃ orbitRel.Quotient J (G ⧸ Γ) :=
  Equiv.ofBijective
    (Quotient.lift (fun g ↦ Quotient.mk'' ((g⁻¹ : G) : G ⧸ Γ)) fun _ _ h ↦
      (mk_inv_eq_mk_inv_iff Γ J).mpr (Quotient.sound h))
    ⟨fun p q ↦ by
      induction p using Quotient.inductionOn' with | h g => ?_
      induction q using Quotient.inductionOn' with | h h => ?_
      exact (mk_inv_eq_mk_inv_iff Γ J).mp,
    fun p ↦ by
      induction p using Quotient.inductionOn' with | h x => ?_
      induction x using QuotientGroup.induction_on with | H g => ?_
      exact ⟨DoubleCoset.mk Γ J g⁻¹, by simp [DoubleCoset.mk]⟩⟩

@[simp]
theorem doubleCosetQuotientEquivOrbitRelQuotient_mk (g : G) :
    doubleCosetQuotientEquivOrbitRelQuotient Γ J (DoubleCoset.mk Γ J g) =
      Quotient.mk'' ((g⁻¹ : G) : G ⧸ Γ) :=
  (rfl)

/-- The stabiliser order of the orbit of `g⁻¹ Γ` is the order of `J ∩ g⁻¹ Γ g`, the stabiliser of
the class `Γ g J` read inside `J` (`TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`). -/
theorem cardStabilizerOnOrbit_doubleCosetQuotientEquivOrbitRelQuotient_mk (g : G) :
    cardStabilizerOnOrbit (doubleCosetQuotientEquivOrbitRelQuotient Γ J (DoubleCoset.mk Γ J g)) =
      Nat.card ((mackeySubgroup g⁻¹ Γ J).subgroupOf J) := by
  rw [doubleCosetQuotientEquivOrbitRelQuotient_mk, cardStabilizerOnOrbit_mk,
    stabilizer_eq_mackeySubgroup_subgroupOf]

/-- Conjugation by `g` identifies the stabiliser `J ∩ g⁻¹ Γ g` of the coset `g⁻¹ Γ` with
`Γ ∩ g J g⁻¹`, the stabiliser of the coset `g J` in `Γ`. -/
theorem natCard_mackeySubgroup_inv_subgroupOf (g : G) :
    Nat.card ((mackeySubgroup g⁻¹ Γ J).subgroupOf J) = Nat.card (mackeySubgroup g J Γ) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe mackeySubgroup_le_right).toEquiv]
  refine Nat.card_congr ((MulAut.conj g).toEquiv.subtypeEquiv fun x ↦ ?_)
  simp only [mem_mackeySubgroup_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨hx, hΓ⟩
    exact ⟨by simpa [mul_assoc] using hΓ, by simpa [mul_assoc] using hx⟩
  · rintro ⟨hΓ, hx⟩
    exact ⟨by simpa [mul_assoc] using hx, by simpa [mul_assoc] using hΓ⟩

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
