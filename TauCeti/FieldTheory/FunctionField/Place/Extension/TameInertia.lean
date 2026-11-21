/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.WildInertia
public import TauCeti.RingTheory.DiscreteValuationRing.RamificationGroup

/-!
# The tame character of a place

Let `F' / F` be an extension of fields, `k` a subfield of `F`, and `P` a place of `F' / k`, and fix
a uniformizer `t` at `P`.  An automorphism `σ` in the inertia group `G_0(P)` moves `t` by a unit,
`σ t = u_σ t`, and the value of `u_σ` at `P` is the **tame character**
`TauCeti.Place.tameCharacter : G_0(P) →* (F'_P)ˣ`.  Because `σ` acts trivially on the residue field,
`σ ↦ u_σ(P)` is a homomorphism, and it does not depend on `t`.  Its kernel consists of the
automorphisms with `σ t ≡ t` modulo `𝔪_P²`, so it contains the first ramification group `G_1(P)`.

When the residue extension `F'_P / F_{P ∩ F}` is separable, the kernel is exactly `G_1(P)`: the
value at `P` of a function `z` integral at `P` is a simple root of a polynomial over `𝒪_{P ∩ F}`,
and Taylor expansion of that polynomial at `z` shows that `σ z ≡ z` modulo `𝔪_P²` as soon as
`σ t ≡ t`.  Then `G_0(P) / G_1(P)` embeds in the multiplicative group of the residue field, so when
the inertia group is finite it is **cyclic of order prime to the residue characteristic** `p`.
Since `G_1(P)` is a `p`-group (`TauCeti.Place.isPGroup_ramificationGroup_succ`), the place has no
wild inertia exactly when `p` does not divide `|G_0(P)|`, which in a finite Galois extension is the
ramification index.

This is part of Stichtenoth, Proposition 3.8.5, which is stated over a perfect constant field, so
that all residue fields are perfect; here the only hypothesis is that the residue extension is
separable.  Without it the kernel of the tame character can be strictly larger than `G_1(P)`.  The
general discrete-valuation-ring theory lives in
`TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean`, and the analogous statements for
nonarchimedean local fields are in
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`.

## Main definitions

* `TauCeti.Place.tameCharacter`: for a uniformizer `t` at `P`, the homomorphism
  `σ ↦ (σ t / t)(P)` from `G_0(P)` to the units of the residue field.
* `TauCeti.Place.tameCharacterGraded`: the induced homomorphism on `G_0(P) / G_1(P)`.

## Main results

* `TauCeti.Place.tameCharacter_eq_of_ord_eq_one`: the tame character does not depend on the
  uniformizer.
* `TauCeti.Place.tameCharacter_eq_one_iff`: `σ` lies in the kernel exactly when `σ t ≡ t` modulo
  `𝔪_P²`.
* `TauCeti.Place.mem_ramificationGroup_one_iff`: for a separable residue extension, an element of
  `G_0(P)` lies in `G_1(P)` exactly when it fixes a uniformizer modulo `𝔪_P²`.
* `TauCeti.Place.ker_tameCharacter`: for a separable residue extension, the kernel of the tame
  character is `G_1(P)`.
* `TauCeti.Place.tameCharacterGraded_injective`: for a separable residue extension, the induced
  tame character on `G_0(P) / G_1(P)` is injective.
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

section Character

variable (F) (P : Place k F') {t : F'}

private theorem ne_zero_of_ord_eq_one (ht : P.ord t = 1) : t ≠ 0 := fun h0 ↦ by
  simp [h0, ord_zero] at ht

private theorem mem_integers_of_ord_eq_one (ht : P.ord t = 1) : t ∈ P.integers := by
  rw [mem_integers_iff_ord_nonneg, ht]
  norm_num

private theorem irreducible_of_ord_eq_one (ht : P.ord t = 1) :
    Irreducible (⟨t, mem_integers_of_ord_eq_one P ht⟩ : P.integers) :=
  P.irreducible_of_isUniformizer (P.isUniformizer_iff_ord_eq_one.mpr ht)

private noncomputable def ramificationGroupZeroEquiv :
    ramificationGroup F P 0 ≃*
      IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers 0 :=
  MulEquiv.subgroupCongr ((ramificationGroup_def F P 0).trans (by norm_num))

omit [Algebra k F] [IsScalarTower k F F'] in
private theorem ramificationGroupZeroEquiv_apply (g : ramificationGroup F P 0) :
    (ramificationGroupZeroEquiv F P g : P.integers.decompositionSubgroup F) = g :=
  rfl

private noncomputable def ramificationGroupGradedZeroEquiv :
    (ramificationGroup F P 0 ⧸ (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)) ≃*
      IsLocalRing.RamificationGroupGraded (P.integers.decompositionSubgroup F) P.integers 0 :=
  QuotientGroup.congr
    ((ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0))
    ((IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers
        (0 + 1)).subgroupOf
      (IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers 0))
    (ramificationGroupZeroEquiv F P)
    (by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, zero_add]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rwa [← Nat.cast_one, ← ramificationGroup_def]
      · intro hg
        refine ⟨⟨(g : P.integers.decompositionSubgroup F),
          by rw [ramificationGroup_def, Nat.cast_zero]; exact g.property⟩, ?_, Subtype.ext rfl⟩
        rwa [ramificationGroup_def, Nat.cast_one])

/-- **The tame character** (Stichtenoth, Proposition 3.8.5): for a uniformizer `t` at `P`, the
homomorphism from the inertia group `G_0(P)` to the units of the residue field sending `σ` to the
value at `P` of the unit `σ t / t`.  It does not depend on `t`
(`TauCeti.Place.tameCharacter_eq_of_ord_eq_one`), and its kernel contains `G_1(P)`, with equality
when the residue extension is separable (`TauCeti.Place.ker_tameCharacter`). -/
noncomputable def tameCharacter (ht : P.ord t = 1) :
    ramificationGroup F P 0 →* P.ResidueFieldˣ :=
  (TauCeti.IsDiscreteValuationRing.tameCharacter (irreducible_of_ord_eq_one P ht)).comp
    (ramificationGroupZeroEquiv F P).toMonoidHom

omit [Algebra k F] [IsScalarTower k F F'] in
/-- The value of the tame character at `σ`, computed on any representative `y` of `σ t / t`
in `𝒪_P`. -/
theorem coe_tameCharacter_of_eq (ht : P.ord t = 1) (g : ramificationGroup F P 0)
    {y : P.integers}
    (hy : (y : F') = ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') t * t⁻¹) :
    (tameCharacter F P ht g : P.ResidueField) = IsLocalRing.residue P.integers y := by
  have ht0 := ne_zero_of_ord_eq_one P ht
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  refine TauCeti.IsDiscreteValuationRing.coe_tameCharacter_of_mul_eq
    (irreducible_of_ord_eq_one P ht) (ramificationGroupZeroEquiv F P g) (Subtype.ext ?_)
  change (y : F') * t = ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') t
  rw [hy, inv_mul_cancel_right₀ ht0]

omit [Algebra k F] [IsScalarTower k F F'] in
/-- **The kernel of the tame character** (Stichtenoth, Proposition 3.8.5): `σ` has trivial tame
character exactly when it fixes the uniformizer `t` modulo `𝔪_P²`. -/
theorem tameCharacter_eq_one_iff (ht : P.ord t = 1) (g : ramificationGroup F P 0) :
    tameCharacter F P ht g = 1 ↔
      ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') t - t ∈ P.filtration 2 := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    TauCeti.IsDiscreteValuationRing.tameCharacter_eq_one_iff,
    P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
    ramificationGroupZeroEquiv_apply, ValuationSubring.coe_decompositionSubgroup_smul]
  norm_num

omit [Algebra k F] [IsScalarTower k F F'] in
/-- **The tame character does not depend on the uniformizer.** -/
theorem tameCharacter_eq_of_ord_eq_one {t' : F'} (ht : P.ord t = 1) (ht' : P.ord t' = 1) :
    tameCharacter F P ht = tameCharacter F P ht' := by
  rw [tameCharacter, tameCharacter,
    TauCeti.IsDiscreteValuationRing.tameCharacter_eq_of_irreducible
      (irreducible_of_ord_eq_one P ht) (irreducible_of_ord_eq_one P ht')]

omit [Algebra k F] [IsScalarTower k F F'] in
/-- The tame character is trivial on the first ramification group: an automorphism moving every
function integral at `P` by an element of `𝔪_P²` in particular fixes `t` modulo `𝔪_P²`. -/
theorem ramificationGroup_one_subgroupOf_le_ker_tameCharacter (ht : P.ord t = 1) :
    (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0) ≤
      (tameCharacter F P ht).ker := by
  intro g hg
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff]
  rw [Subgroup.mem_subgroupOf] at hg
  simpa using (mem_ramificationGroup_iff F P).mp hg t (mem_integers_of_ord_eq_one P ht)

/-- The tame character induced on `G_0(P) / G_1(P)`. It is injective when the residue extension
is separable (`TauCeti.Place.tameCharacterGraded_injective`). -/
noncomputable def tameCharacterGraded (ht : P.ord t = 1) :
    ramificationGroup F P 0 ⧸ (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)
      →* P.ResidueFieldˣ :=
  (TauCeti.IsDiscreteValuationRing.tameCharacterGraded (irreducible_of_ord_eq_one P ht)).comp
    (ramificationGroupGradedZeroEquiv F P).toMonoidHom

omit [Algebra k F] [IsScalarTower k F F'] in
/-- The induced tame character evaluated on the class of an inertia automorphism. -/
@[simp]
theorem tameCharacterGraded_mk (ht : P.ord t = 1) (g : ramificationGroup F P 0) :
    tameCharacterGraded F P ht (QuotientGroup.mk g) = tameCharacter F P ht g := by
  rw [tameCharacterGraded, tameCharacter, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, ramificationGroupGradedZeroEquiv,
    QuotientGroup.congr_mk, TauCeti.IsDiscreteValuationRing.tameCharacterGraded_mk]

omit [Algebra k F] [IsScalarTower k F F'] in
/-- The induced tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_ord_eq_one {t' : F'} (ht : P.ord t = 1)
    (ht' : P.ord t' = 1) :
    tameCharacterGraded F P ht = tameCharacterGraded F P ht' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    TauCeti.IsDiscreteValuationRing.tameCharacterGraded_eq_of_irreducible
      (irreducible_of_ord_eq_one P ht) (irreducible_of_ord_eq_one P ht')]

end Character

section Separable

variable (F) [Algebra.IsIntegral F F'] (P : Place k F') {t : F'}

/-- **Membership in the first ramification group is decided at a uniformizer**, when the residue
extension is separable (Stichtenoth, Proposition 3.8.5): an element of `G_0(P)` lies in `G_1(P)`
exactly when it fixes `t` modulo `𝔪_P²`. -/
theorem mem_ramificationGroup_one_iff
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] (ht : P.ord t = 1)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P 0) :
    g ∈ ramificationGroup F P 1 ↔ (g : F' ≃ₐ[F] F') t - t ∈ P.filtration 2 := by
  have hg0 : g ∈ IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers 0 :=
    by rwa [ramificationGroup_def, Nat.cast_zero] at hg
  rw [ramificationGroup_def, Nat.cast_one, ← Nat.cast_one,
    TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_natCast_iff_smul_sub_mem
      (P.restrict k F).integers (irreducible_of_ord_eq_one P ht) hg0,
    P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
    ValuationSubring.coe_decompositionSubgroup_smul]
  norm_num

/-- **The kernel of the tame character is the first ramification group**, when the residue
extension is separable (Stichtenoth, Proposition 3.8.5): so `G_0(P) / G_1(P)` embeds in the
multiplicative group of the residue field. -/
theorem ker_tameCharacter [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    (ht : P.ord t = 1) :
    (tameCharacter F P ht).ker =
      (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0) := by
  ext g
  rw [tameCharacter, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← MonoidHom.mem_ker,
    TauCeti.IsDiscreteValuationRing.ker_tameCharacter (P.restrict k F).integers
      (irreducible_of_ord_eq_one P ht),
    Subgroup.mem_subgroupOf, ramificationGroupZeroEquiv_apply, Subgroup.mem_subgroupOf,
    ramificationGroup_def F P 1, Nat.cast_one]

/-- The induced tame character is injective when the residue extension is separable. -/
theorem tameCharacterGraded_injective
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField] (ht : P.ord t = 1) :
    Function.Injective (tameCharacterGraded F P ht) :=
  (TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective (P.restrict k F).integers
    (irreducible_of_ord_eq_one P ht)).comp (ramificationGroupGradedZeroEquiv F P).injective

/-- **The tame quotient `G_0(P) / G_1(P)` is cyclic** when the inertia group is finite and the
residue extension is separable (Stichtenoth, Proposition 3.8.5): it embeds in the multiplicative
group of the residue field, whose finite subgroups are cyclic. -/
theorem isCyclic_quotient_ramificationGroup_one
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    IsCyclic (ramificationGroup F P 0 ⧸
      (ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)) := by
  have : Finite
      (IsLocalRing.RamificationGroupGraded (P.integers.decompositionSubgroup F) P.integers 0) :=
    Finite.of_equiv _ (ramificationGroupGradedZeroEquiv F P).toEquiv
  let : IsCyclic
      (IsLocalRing.RamificationGroupGraded (P.integers.decompositionSubgroup F) P.integers 0) :=
    TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero
      (P.integers.decompositionSubgroup F) (P.restrict k F).integers P.integers
  exact isCyclic_of_surjective _ (ramificationGroupGradedZeroEquiv F P).symm.surjective

/-- **The index of `G_1(P)` in `G_0(P)` is prime to the residue characteristic `p`**, when the
inertia group is finite and the residue extension is separable (Stichtenoth, Proposition 3.8.5):
`G_0(P) / G_1(P)` embeds in the multiplicative group of a field of characteristic `p`, which has
no element of order `p`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    ¬ p ∣ ((ramificationGroup F P 1).subgroupOf (ramificationGroup F P 0)).index := by
  have : Finite
      (IsLocalRing.RamificationGroupGraded (P.integers.decompositionSubgroup F) P.integers 0) :=
    Finite.of_equiv _ (ramificationGroupGradedZeroEquiv F P).toEquiv
  rw [Subgroup.index_eq_card, Nat.card_congr (ramificationGroupGradedZeroEquiv F P).toEquiv,
    ← Subgroup.index_eq_card]
  exact TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one
    (P.integers.decompositionSubgroup F) (P.restrict k F).integers P.integers p

/-- **A place has no wild inertia exactly when the residue characteristic `p` does not divide the
order of its inertia group**, when that group is finite and the residue extension is separable:
`G_1(P)` is a `p`-group (`TauCeti.Place.isPGroup_ramificationGroup_succ`) of index prime to `p`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP P.ResidueField p]
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    [Finite (ramificationGroup F P 0)] :
    ramificationGroup F P 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup F P 0) := by
  have : Finite
      (IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers 0) :=
    Finite.of_equiv _ (ramificationGroupZeroEquiv F P).toEquiv
  rw [ramificationGroup_def, Nat.card_congr (ramificationGroupZeroEquiv F P).toEquiv, Nat.cast_one]
  exact TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_card
    (P.integers.decompositionSubgroup F) (P.restrict k F).integers P.integers p

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
