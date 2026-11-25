/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.WildInertia
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Graded

/-!
# The tame quotient of a place

Let `F' / F` be an extension of fields, `k` a subfield of `F`, and `P` a place of `F' / k`.  The
inertia group `G_0(P)` acts on the valuation ring `𝒪_P`, a discrete valuation ring, and the
ramification groups of `P` are the generic local-ring ramification groups of this action
(`TauCeti.Place.ramificationGroup_def`).  So the **tame character** of `P` is the generic
`TauCeti.IsLocalRing.tameCharacter (P.integers.decompositionSubgroup F) P.integers`, which sends
`σ` to the value at `P` of the unit `σ t / t` for any uniformizer `t`, and its kernel contains
`G_1(P)`.

The decomposition group fixes the valuation ring `𝒪_{P ∩ F}` of the place below `P`
(`TauCeti.Place.instSMulCommClassIntegers`).  When the residue extension
`F'_P / F_{P ∩ F}` is separable, the generic uniformizer criterion therefore applies: an element of
`G_0(P)` lies in `G_1(P)` exactly when it fixes a uniformizer modulo `𝔪_P²`, the kernel of the tame
character is exactly `G_1(P)`, and `G_0(P) / G_1(P)` embeds in the multiplicative group of the
residue field.  When the inertia group is finite, `G_0(P) / G_1(P)` is then **cyclic of order prime
to the residue characteristic** `p`.  Since `G_1(P)` is a `p`-group
(`TauCeti.Place.isPGroup_ramificationGroup_succ`), the place has no wild inertia exactly when `p`
does not divide `|G_0(P)|`, which in a finite Galois extension is the ramification index.

This is part of Stichtenoth, Proposition 3.8.5, which is stated over a perfect constant field, so
that all residue fields are perfect; here the only hypothesis is that the residue extension is
separable.  Without it the kernel of the tame character can be strictly larger than `G_1(P)`.

## Main results

* `TauCeti.Place.mem_ramificationGroup_one_iff`: for a separable residue extension, an element of
  `G_0(P)` lies in `G_1(P)` exactly when it fixes a uniformizer modulo `𝔪_P²`.
* `TauCeti.Place.isCyclic_quotient_ramificationGroup_one` and
  `TauCeti.Place.not_dvd_index_ramificationGroup_one`: for finite inertia and a separable residue
  extension, **`G_0(P) / G_1(P)` is cyclic of order prime to the residue characteristic**.
* `TauCeti.Place.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: for finite
  inertia and a separable residue extension, the first
  ramification group is trivial exactly when the residue characteristic does not divide the order
  of the inertia group, and `TauCeti.Place.ramificationGroup_one_eq_bot_iff_not_dvd_ramificationIdx`
  its form for a finite Galois extension: **no wild inertia exactly in the tame case**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.8.5.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section Separable

variable (F) [Algebra.IsIntegral F F'] (P : Place k F') {t : F'}

/-- **Membership in the first ramification group is decided at a uniformizer**, when the residue
extension is separable (Stichtenoth, Proposition 3.8.5): an element of `G_0(P)` lies in `G_1(P)`
exactly when it fixes `t` modulo `𝔪_P²`. This is the case of the valuation ring `𝒪_P` of
`TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`. -/
theorem mem_ramificationGroup_one_iff
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] (ht : P.ord t = 1)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P 0) :
    g ∈ ramificationGroup F P 1 ↔ (g : F' ≃ₐ[F] F') t - t ∈ P.filtration 2 := by
  have htP : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hπ := (P.irreducible_of_isUniformizer (t := ⟨t, htP⟩)
    (P.isUniformizer_iff_ord_eq_one.mpr ht)).maximalIdeal_eq
  rw [ramificationGroup_def] at hg ⊢
  rw [IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem (P.restrict k F).integers hπ hg,
    P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
    ValuationSubring.coe_decompositionSubgroup_smul]
  norm_num

/-- **The tame quotient `G_0(P) / G_1(P)` is cyclic** when the inertia group is finite and the
residue extension is separable (Stichtenoth, Proposition 3.8.5): it embeds in the multiplicative
group of the residue field, whose finite subgroups are cyclic. This is the case of the valuation
ring `𝒪_P` of `TauCeti.IsLocalRing.isCyclic_ramificationGroupGraded_zero`. -/
theorem isCyclic_quotient_ramificationGroup_one
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    IsCyclic (ramificationGroup F P 0 ⧸
      (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)) := by
  -- Transport along `ramificationGroup_def`, generalizing the subgroups so that the normality
  -- instance of the quotient is not in the way.
  have key : ∀ A B : Subgroup (P.integers.decompositionSubgroup F),
      A = IsLocalRing.ramificationGroup _ P.integers 0 →
      B = IsLocalRing.ramificationGroup _ P.integers 1 → ∀ [Finite A] [(B.subgroupOf A).Normal],
      IsCyclic (A ⧸ B.subgroupOf A) := by
    rintro A B rfl rfl _ _
    exact IsLocalRing.isCyclic_ramificationGroupGraded_zero (P.restrict k F).integers
  exact key _ _ (ramificationGroup_def F P 0) (ramificationGroup_def F P 1)

/-- **The index of `G_1(P)` in `G_0(P)` is prime to the residue characteristic `p`**, when the
inertia group is finite and the residue extension is separable (Stichtenoth, Proposition 3.8.5).
This is the case of the valuation ring `𝒪_P` of
`TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    ¬ p ∣ ((ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)).index := by
  have hfin := ‹Finite (ramificationGroup F P 0)›
  rw [ramificationGroup_def] at hfin
  rw [ramificationGroup_def, ramificationGroup_def]
  exact IsLocalRing.not_dvd_index_ramificationGroup_one (P.restrict k F).integers p

/-- **A place has no wild inertia exactly when the residue characteristic `p` does not divide the
order of its inertia group**, when that group is finite and the residue extension is separable:
`G_1(P)` is a `p`-group (`TauCeti.Place.isPGroup_ramificationGroup_succ`) of index prime to `p`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    ramificationGroup F P 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup F P 0) := by
  refine ⟨fun h ↦ ?_, ramificationGroup_succ_eq_bot_of_not_dvd_card_inertia F P p 0⟩
  have hindex := not_dvd_index_ramificationGroup_one F P p
  rwa [h, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hindex

end Separable

section Galois

variable (F) [FiniteDimensional F F'] [IsGalois F F'] (P : Place k F')

/-- **A place of a finite Galois extension is tamely ramified exactly when it has no wild
inertia**, when the residue extension is separable: the first ramification group is trivial if and
only if the residue characteristic `p` does not divide the ramification index. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_ramificationIdx (p : ℕ) [Fact p.Prime]
    [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] :
    ramificationGroup F P 1 = ⊥ ↔ ¬ p ∣ ramificationIdx F P := by
  have : Finite (ramificationGroup F P 0) :=
    Finite.of_injective (fun g : ramificationGroup F P 0 ↦ (g : F' ≃ₐ[F] F'))
      (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
  rw [ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero F P p,
    ramificationGroup_zero, card_inertiaSubgroup F P]

end Galois

end Place

end TauCeti
