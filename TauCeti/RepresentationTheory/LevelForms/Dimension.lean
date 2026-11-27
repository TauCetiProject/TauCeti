/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.GroupTheory.DoubleCoset.Mass
public import TauCeti.RepresentationTheory.LevelForms
import Mathlib.RingTheory.IntegralDomain
import TauCeti.RepresentationTheory.Character.Basic

/-!
# Dimensions of spaces of level forms

Let `G` be a group with subgroups `Γ` and `J`, and `M` a finite-dimensional vector space over a
field `K` with a right action `m ∣ u = ρ (op u) m` of `J`. The space of level forms
`S_Γ(J, M) = Representation.levelForms ρ Γ` is identified, by evaluation at representatives
`c q` of the classes `q ∈ Γ \ G / J`, with the product of the invariants of the stabilisers
`S_q = J ∩ (c q)⁻¹ Γ (c q)` (`Representation.levelFormsEquivPi`). For finitely many classes this
gives the dimension formulas of algebraic modular forms on a group compact at infinity:

* `dim S_Γ(J, M) = ∑_q dim M^{S_q}`;
* when the stabilisers are finite of order invertible in `K`, the averaging projector gives
  `dim S_Γ(J, M) = ∑_q |S_q|⁻¹ ∑_{u ∈ S_q} tr(u | M)`;
* the terms `u = 1` add up to `mass J · dim M`, where `mass J = ∑_q |S_q|⁻¹` is the mass of the
  class set (`TauCeti.orbitMass J (G ⧸ Γ)`, see `TauCeti.orbitMass_eq_finsum_doubleCoset`); more
  generally, if a central subgroup `Z ≤ Γ ∩ J` acts on `M` through a character `ω`, the terms
  `u ∈ Z` add up to `|Z| · mass J · dim M` when `ω = 1` and to `0` otherwise;
* when every stabiliser is trivial, `dim S_Γ(J, M) = #(Γ \ G / J) · dim M = mass J · dim M`, and
  for `J' ≤ J` of finite index all of whose stabilisers are trivial,
  `dim S_Γ(J', M) = [J : J'] · mass J · dim M` by the index formula
  `TauCeti.orbitMass_eq_relIndex_mul_of_le`.

In Gross's convention the stabilisers are `Γ_i = Γ ∩ t_i J t_i⁻¹`, acting on `M` through
`γ ↦ ρ(t_i⁻¹ γ t_i)`; conjugation by `t_i = c q` identifies `Γ_i` with `S_q`
(`TauCeti.natCard_mackeySubgroup_inv_subgroupOf`). Here the stabilisers are taken inside `J`,
where `M` is a representation, as in `Representation.levelFormsEquivPi`.

## Main results

* `Representation.finrank_levelForms`: `dim S_Γ(J, M) = ∑_q dim M^{S_q}`.
* `Representation.natCast_finrank_levelForms`: the character form
  `dim S_Γ(J, M) = ∑_q |S_q|⁻¹ ∑_{u ∈ S_q} tr(u | M)`.
* `Representation.natCast_finrank_levelForms_eq_central`: the central-term form.
* `Representation.natCast_finrank_levelForms_eq_orbitMass_mul_add`: the mass form
  `dim S_Γ(J, M) = mass J · dim M + ∑_q |S_q|⁻¹ ∑_{u ∈ S_q, u ≠ 1} tr(u | M)`.
* `Representation.finrank_levelForms_of_mackeySubgroup_eq_bot`,
  `Representation.finrank_levelForms_eq_orbitMass_mul_of_mackeySubgroup_eq_bot`: the free case.
* `Representation.finrank_levelForms_eq_relIndex_mul_orbitMass_mul`: the dimension at a level
  `J' ≤ J` of finite index with trivial stabilisers.

## References

* B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), §§4–8.

The free case is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean`,
declaration `New.finrank_levelSpace_smoothFormRep`, and file `src/Lib/Adelic/Hecke/ClassSums.lean`,
declaration `New.card_classes_eq_classSum`.
-/

public section

open MulOpposite Module TauCeti

namespace Representation

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

variable {G : Type*} [Group G] {J : Subgroup G} (ρ : Representation K Jᵐᵒᵖ M) (Γ : Subgroup G)
variable (c : DoubleCoset.Quotient (Γ : Set G) J → G) (hc : ∀ q, DoubleCoset.mk Γ J (c q) = q)

include hc in
/-- **The dimension of the level forms** is the sum over the classes `q ∈ Γ \ G / J` of the
dimensions of the invariants of the stabilisers `J ∩ (c q)⁻¹ Γ (c q)`, for any representatives
`c q`. -/
theorem finrank_levelForms [Finite (DoubleCoset.Quotient (Γ : Set G) J)] [FiniteDimensional K M] :
    finrank K (ρ.levelForms Γ) = ∑ᶠ q, finrank K
      (invariants (ρ.comp (MonoidHom.op ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J).subtype))) := by
  have := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) J)
  rw [(levelFormsEquivPi ρ Γ c hc).finrank_eq, finrank_pi_fintype, finsum_eq_sum_of_fintype]

include hc in
/-- **The dimension of the level forms as a sum of character averages.** With finitely many
classes and stabilisers `S_q = J ∩ (c q)⁻¹ Γ (c q)` whose orders are finite and nonzero in `K`
(for instance finite stabilisers in characteristic zero),
`dim S_Γ(J, M) = ∑_q |S_q|⁻¹ ∑_{u ∈ S_q} tr(u | M)`. -/
theorem natCast_finrank_levelForms [Finite (DoubleCoset.Quotient (Γ : Set G) J)]
    [FiniteDimensional K M]
    (hS : ∀ q, (Nat.card ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) : K) ≠ 0) :
    (finrank K (ρ.levelForms Γ) : K) = ∑ᶠ q,
      (Nat.card ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) : K)⁻¹ *
        ∑ᶠ u : (mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J, ρ.character (op (u : J)) := by
  rw [finrank_levelForms ρ Γ c hc, Nat.cast_finsum]
  exact finsum_congr fun q ↦ natCast_finrank_invariants_comp_op_subtype ρ _ (hS q)

include hc in
/-- The class-set mass, read in a field of characteristic zero, is `∑_q |S_q|⁻¹`. -/
private theorem ratCast_orbitMass [CharZero K] [Finite (DoubleCoset.Quotient (Γ : Set G) J)] :
    ((orbitMass J (G ⧸ Γ) : ℚ) : K) =
      ∑ᶠ q, (Nat.card ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) : K)⁻¹ := by
  have := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) J)
  rw [orbitMass_eq_finsum_doubleCoset_stabilizer c hc, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- **Splitting off a central subgroup from a trace sum.** If `Z ≤ Γ ∩ J` is central in `G` and
acts on `M` through a character `ω`, it lies in every stabiliser `S_q = J ∩ (c q)⁻¹ Γ (c q)`, and
its elements contribute `[ω = 1] · |Z| · dim M` to the trace sum over `S_q`. -/
private theorem finsum_character_eq_central (q : DoubleCoset.Quotient (Γ : Set G) J)
    [Finite ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J)]
    {Z : Subgroup G} (hZJ : Z ≤ J) (hZΓ : Z ≤ Γ) (hZ : Z ≤ Subgroup.center G) (ω : Z →* K)
    [Decidable (ω = 1)] (hω : ∀ (z : Z) (m : M), ρ (op ⟨z, hZJ z.property⟩) m = ω z • m) :
    ∑ᶠ u : (mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J, ρ.character (op (u : J)) =
      (if ω = 1 then (Nat.card Z : K) else 0) * finrank K M +
        ∑ᶠ (u : (mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) (_ : ((u : J) : G) ∉ Z),
          ρ.character (op (u : J)) := by
  set S := (mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J
  -- a central element of `Γ ∩ J` fixes every coset `(c q)⁻¹ Γ`
  have hZS (z : G) (hz : z ∈ Z) : (⟨z, hZJ hz⟩ : J) ∈ S := by
    rw [Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff, inv_inv]
    refine ⟨hZJ hz, ?_⟩
    rw [Subgroup.coe_mk, Subgroup.mem_center_iff.mp (hZ hz) (c q), mul_inv_cancel_right]
    exact hZΓ hz
  let e : {u : S // ((u : J) : G) ∈ Z} ≃ Z :=
    { toFun u := ⟨u.val.val.val, u.property⟩
      invFun z := ⟨⟨⟨z.val, hZJ z.property⟩, hZS z.val z.property⟩, z.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have := Finite.of_equiv _ e
  have := Fintype.ofFinite Z
  rw [← finsum_mem_univ, ← Set.union_compl_self {u : S | ((u : J) : G) ∈ Z},
    finsum_mem_union disjoint_compl_right (Set.toFinite _) (Set.toFinite _)]
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the elements of `Z` act by scalars, and `∑_{z ∈ Z} ω z` is `|Z|` or `0`
    simp only [Set.mem_ofPred_eq]
    rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv e.symm]
    simp only [Equiv.coe_fn_symm_mk, e, character_eq_finrank_mul_of_apply_eq_smul ρ (hω _)]
    rw [← mul_finsum, finsum_eq_sum_of_fintype, sum_hom_units, mul_comm]
    split_ifs <;> simp [Nat.card_eq_fintype_card]
  · -- membership in the complement is the `∉` condition
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]

include hc in
/-- **The dimension of the level forms, central-term form.** Let `Z ≤ Γ ∩ J` be central in `G`
and act on `M` through a character `ω`, as the centre `Z_G(F) ∩ J` does on an irreducible
coefficient module. Over a field of characteristic zero, with finitely many classes and finite
stabilisers `S_q = J ∩ (c q)⁻¹ Γ (c q)`,
`dim S_Γ(J, M) = [ω = 1] · |Z| · mass J · dim M + ∑_q |S_q|⁻¹ ∑_{u ∈ S_q ∖ Z} tr(u | M)`. -/
theorem natCast_finrank_levelForms_eq_central [CharZero K]
    [Finite (DoubleCoset.Quotient (Γ : Set G) J)] [FiniteDimensional K M]
    (hfin : ∀ q, Finite ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J))
    {Z : Subgroup G} (hZJ : Z ≤ J) (hZΓ : Z ≤ Γ) (hZ : Z ≤ Subgroup.center G) (ω : Z →* K)
    [Decidable (ω = 1)] (hω : ∀ (z : Z) (m : M), ρ (op ⟨z, hZJ z.property⟩) m = ω z • m) :
    (finrank K (ρ.levelForms Γ) : K) =
      (if ω = 1 then (Nat.card Z : K) else 0) * (orbitMass J (G ⧸ Γ) : K) * finrank K M +
        ∑ᶠ q, (Nat.card ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) : K)⁻¹ *
          ∑ᶠ (u : (mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) (_ : ((u : J) : G) ∉ Z),
            ρ.character (op (u : J)) := by
  rw [natCast_finrank_levelForms ρ Γ c hc fun q ↦
      have := hfin q
      Nat.cast_ne_zero.mpr Nat.card_pos.ne',
    ratCast_orbitMass Γ c hc,
    mul_comm (if ω = 1 then _ else _), mul_assoc, finsum_mul, ← finsum_add_distrib
      (Set.toFinite _) (Set.toFinite _)]
  refine finsum_congr fun q ↦ ?_
  have := hfin q
  rw [finsum_character_eq_central ρ Γ c q hZJ hZΓ hZ ω hω, mul_add]

include hc in
/-- **The dimension of the level forms, mass form.** Over a field of characteristic zero, with
finitely many classes and finite stabilisers `S_q = J ∩ (c q)⁻¹ Γ (c q)`,
`dim S_Γ(J, M) = mass J · dim M + ∑_q |S_q|⁻¹ ∑_{u ∈ S_q, u ≠ 1} tr(u | M)`: the identity
elements contribute the mass times the dimension. -/
theorem natCast_finrank_levelForms_eq_orbitMass_mul_add [CharZero K]
    [Finite (DoubleCoset.Quotient (Γ : Set G) J)] [FiniteDimensional K M]
    (hfin : ∀ q, Finite ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J)) :
    (finrank K (ρ.levelForms Γ) : K) =
      (orbitMass J (G ⧸ Γ) : K) * finrank K M +
        ∑ᶠ q, (Nat.card ((mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) : K)⁻¹ *
          ∑ᶠ (u : (mackeySubgroup (c q)⁻¹ Γ J).subgroupOf J) (_ : u ≠ 1),
            ρ.character (op (u : J)) := by
  classical
  -- the central-term form for the trivial subgroup and the trivial character
  have hω (z : (⊥ : Subgroup G)) (m : M) :
      ρ (op ⟨z, bot_le (a := J) z.property⟩) m = (1 : (⊥ : Subgroup G) →* K) z • m := by
    obtain ⟨z, hz⟩ := z
    obtain rfl := Subgroup.mem_bot.mp hz
    simp only [MonoidHom.one_apply, one_smul]
    exact LinearMap.congr_fun ρ.map_one m
  rw [natCast_finrank_levelForms_eq_central ρ Γ c hc hfin bot_le bot_le bot_le 1 hω,
    Subgroup.card_bot]
  simp only [↓reduceIte, Nat.cast_one, one_mul, Subgroup.mem_bot, OneMemClass.coe_eq_one, ne_eq]

/-- With trivial stabilisers the invariants are everything. -/
private theorem finrank_invariants_of_mackeySubgroup_eq_bot {g : G}
    (h : mackeySubgroup g J Γ = ⊥) :
    finrank K (invariants (ρ.comp (MonoidHom.op ((mackeySubgroup g⁻¹ Γ J).subgroupOf J).subtype))) =
      finrank K M := by
  have hS : (mackeySubgroup g⁻¹ Γ J).subgroupOf J = ⊥ := Subgroup.card_eq_one.mp (by
    rw [natCard_mackeySubgroup_inv_subgroupOf, h, Subgroup.card_bot])
  rw [show invariants (ρ.comp (MonoidHom.op ((mackeySubgroup g⁻¹ Γ J).subgroupOf J).subtype)) = ⊤
    from eq_top_iff.mpr fun m _ u ↦ by
      have hu : (u.unop : J) = 1 := Subgroup.mem_bot.mp (hS ▸ u.unop.property)
      simp [hu], finrank_top]

/-- **The dimension of the level forms with trivial stabilisers.** If `Γ ∩ g J g⁻¹` is trivial
for every `g` and there are finitely many classes, `dim S_Γ(J, M) = #(Γ \ G / J) · dim M`. No
assumption on the field is needed. -/
theorem finrank_levelForms_of_mackeySubgroup_eq_bot [Finite (DoubleCoset.Quotient (Γ : Set G) J)]
    [FiniteDimensional K M] (h : ∀ g : G, mackeySubgroup g J Γ = ⊥) :
    finrank K (ρ.levelForms Γ) = Nat.card (DoubleCoset.Quotient (Γ : Set G) J) * finrank K M := by
  have := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) J)
  rw [finrank_levelForms ρ Γ (fun q ↦ q.out) DoubleCoset.out_eq', finsum_eq_sum_of_fintype]
  simp [finrank_invariants_of_mackeySubgroup_eq_bot ρ Γ (h _), Nat.card_eq_fintype_card]

/-- **The dimension of the level forms with trivial stabilisers is the mass times the dimension of
the coefficients**: `dim S_Γ(J, M) = mass J · dim M`. -/
theorem finrank_levelForms_eq_orbitMass_mul_of_mackeySubgroup_eq_bot
    [Finite (DoubleCoset.Quotient (Γ : Set G) J)] [FiniteDimensional K M]
    (h : ∀ g : G, mackeySubgroup g J Γ = ⊥) :
    (finrank K (ρ.levelForms Γ) : ℚ) = orbitMass J (G ⧸ Γ) * finrank K M := by
  rw [finrank_levelForms_of_mackeySubgroup_eq_bot ρ Γ h,
    orbitMass_eq_natCard_of_mackeySubgroup_eq_bot h, Nat.cast_mul]

/-- **The dimension at a smaller level with trivial stabilisers.** For `J' ≤ J` of finite index,
finitely many classes in `Γ \ G / J`, and `Γ ∩ g J' g⁻¹` trivial for every `g`, the level forms
of level `J'` with coefficients `M` restricted to `J'` have dimension `[J : J'] · mass J · dim M`.
The stabilisers `Γ ∩ g J g⁻¹` need not be trivial; they are finite because `J'` has finite index
in `J`. -/
theorem finrank_levelForms_eq_relIndex_mul_orbitMass_mul {J' : Subgroup G} (hle : J' ≤ J)
    [J'.IsFiniteRelIndex J] [Finite (DoubleCoset.Quotient (Γ : Set G) J)] [FiniteDimensional K M]
    (h : ∀ g : G, mackeySubgroup g J' Γ = ⊥) :
    (finrank K (levelForms (ρ.comp (MonoidHom.op (Subgroup.inclusion hle))) Γ) : ℚ) =
      J'.relIndex J * orbitMass J (G ⧸ Γ) * finrank K M := by
  have := Finite.of_equiv _ (doubleCosetQuotientEquivOrbitRelQuotient Γ J)
  have := finite_orbitRelQuotient_of_le (X := G ⧸ Γ) hle
  have := Finite.of_equiv _ (doubleCosetQuotientEquivOrbitRelQuotient Γ J').symm
  have h' := orbitMass_eq_natCard_of_mackeySubgroup_eq_bot h
  rw [finrank_levelForms_of_mackeySubgroup_eq_bot _ Γ h, Nat.cast_mul, ← h',
    orbitMass_eq_relIndex_mul_of_le hle]

end Representation
