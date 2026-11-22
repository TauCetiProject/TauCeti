/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.Algebra.Group.Subgroup.FiniteFiltration
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer

/-!
# The higher ramification groups of a place

Let `F' / F` be an extension of fields, `k` a subfield of `F`, and `P` a place of `F' / k`.  An
automorphism of `F'` over `F` fixing `P` acts on the valuation ring `𝒪_P`, and the **`i`-th
ramification group** of `P` collects those automorphisms whose action on `𝒪_P` is the identity to
order `i + 1`:

`G_i(P) = {σ ∈ G_Z(P) | ord_P (σ z - z) ≥ i + 1 for every z ∈ 𝒪_P}`.

At `i = 0` this is the condition that `σ` act trivially on the residue field, so `G_0(P)` is the
inertia group; the groups then decrease, are normal in the decomposition group, and meet in the
trivial group.  This is the lower numbering, and no completion is taken.  The groups are the
generic ramification filtration `TauCeti.IsLocalRing.ramificationGroup` of the decomposition group
acting on the valuation ring `𝒪_P`; the condition above reads it off the order filtration of `F'`
at `P` built in `TauCeti/FieldTheory/FunctionField/Place/Filtration.lean`.

The structure of the successive quotients comes from a single map.  Fix a uniformizer `t` at `P`.
For `σ ∈ G_{i+1}(P)` the function `z ↦ (σ z - z) / t^{i+2}` takes values in `𝒪_P`, and reducing it
at `P` gives a function `𝒪_P → F'_P`; the resulting
`TauCeti.Place.ramificationResidueHom` is a group homomorphism from `G_{i+1}(P)` to the *additive*
group of such functions, and its kernel is exactly `G_{i+2}(P)`.  Its being a homomorphism is
where the hypothesis `i + 1 ≥ 1` enters: an automorphism in `G_1(P)` moves `t` by a unit
congruent to `1` at `P`, and one in `G_0(P)` does not move residues at all, so the two error terms
produced by expanding `(στ) z - z` disappear on reduction.

Consequently every quotient `G_{i+1}(P) / G_{i+2}(P)` embeds in the additive group of functions
from `𝒪_P` to the residue field: it is abelian, and in characteristic `p` it is killed by `p`, while
in characteristic zero it is torsion-free.  When `G_1(P)` is finite the last statement forces
`G_{i+1}(P) = G_{i+2}(P)` for every `i`, and hence — the groups meeting in `1` — `G_1(P)` is
trivial.

This is Stichtenoth, Definition 3.8.4 and Proposition 3.8.5.  Nothing here consumes perfectness of
the residue fields; the complementary statement that `G_0(P) / G_1(P)` is cyclic of order prime to
the characteristic needs the residue extension to be separable, and is proved in
`TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`.

## Main definitions

* `TauCeti.Place.ramificationGroup`: the `i`-th ramification group of a place, a subgroup of the
  decomposition group; `TauCeti.Place.ramificationGroup_def` is its definition as a local-ring
  ramification group, and `TauCeti.Place.mem_ramificationGroup_iff` its membership in terms of the
  order filtration.
* `TauCeti.Place.ramificationResidueHom`: for a uniformizer `t` at `P`, the homomorphism
  `σ ↦ (z ↦ ((σ z - z) / t^{i+2})(P))` from `G_{i+1}(P)` to the additive group of functions
  `𝒪_P → F'_P`.

## Main results

* `TauCeti.Place.ramificationGroup_zero`: the `0`-th ramification group is the inertia group.
* `TauCeti.Place.ramificationGroup_antitone`, `TauCeti.Place.normal_ramificationGroup`: the
  ramification groups decrease and are normal in the decomposition group.
* `TauCeti.Place.iInf_ramificationGroup_eq_bot` and
  `TauCeti.Place.exists_forall_ramificationGroup_eq_bot`: the ramification groups meet in the
  trivial group, and, when `G_0(P)` is finite, are trivial from some index on.
* `TauCeti.Place.ker_ramificationResidueHom`: **the kernel of the ramification residue is the next
  ramification group**, so `G_{i+1}(P) / G_{i+2}(P)` embeds in an additive group of functions to
  the residue field.
* `TauCeti.Place.commutator_ramificationGroup_le` and
  `TauCeti.Place.pow_mem_ramificationGroup_of_charP`: the quotient `G_{i+1}(P) / G_{i+2}(P)` is
  abelian, and elementary abelian of exponent `p` in characteristic `p`.
* `TauCeti.Place.ramificationGroup_one_eq_bot`: **in characteristic zero the first ramification
  group of a place is trivial when it is finite**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.8.4 and Proposition 3.8.5.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F'] [Algebra F F']

section Transport

variable (F) (P : Place k F') (g : P.integers.decompositionSubgroup F)

/-- An automorphism fixing `P` preserves every step of the order filtration at `P`. -/
theorem mem_filtration_decompositionSubgroup_apply {a : ℤ} {x : F'} :
    (g : F' ≃ₐ[F] F') x ∈ P.filtration a ↔ x ∈ P.filtration a := by
  simp only [mem_filtration_iff, valuation_decompositionSubgroup_apply]

end Transport

section Defs

variable (F) (P : Place k F')

/-- **The `i`-th ramification group of a place** (Stichtenoth, Definition 3.8.4): the
automorphisms in the decomposition group of `P` that move every function integral at `P` by
something of order at least `i + 1`.  This is the lower numbering: the generic ramification
filtration `TauCeti.IsLocalRing.ramificationGroup` of the decomposition group acting on the
valuation ring `𝒪_P`, whose membership `TauCeti.Place.mem_ramificationGroup_iff` reads the order
condition on the order filtration of `F'` at `P`. -/
def ramificationGroup (i : ℕ) : Subgroup (P.integers.decompositionSubgroup F) :=
  IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers i

/-- The ramification groups of a place are the local-ring ramification groups of its valuation
ring under the decomposition group. -/
theorem ramificationGroup_def (i : ℕ) :
    ramificationGroup F P i =
      IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers i :=
  (rfl)

/-- **Membership in the `i`-th ramification group** (Stichtenoth, Definition 3.8.4): an
automorphism lies in `G_i(P)` exactly when it moves every function integral at `P` by something of
order at least `i + 1`. -/
@[simp]
theorem mem_ramificationGroup_iff {i : ℕ} {g : P.integers.decompositionSubgroup F} :
    g ∈ ramificationGroup F P i ↔
      ∀ x ∈ P.integers, (g : F' ≃ₐ[F] F') x - x ∈ P.filtration (i + 1) := by
  rw [ramificationGroup_def, IsLocalRing.mem_ramificationGroup_natCast_iff]
  constructor
  · intro h x hx
    have h' := (P.mem_maximalIdeal_pow_iff_coe_mem_filtration (i + 1) _).mp (h ⟨x, hx⟩)
    rwa [AddSubgroupClass.coe_sub, ValuationSubring.coe_decompositionSubgroup_smul,
      Nat.cast_add, Nat.cast_one] at h'
  · intro h x
    rw [P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
      ValuationSubring.coe_decompositionSubgroup_smul, Nat.cast_add, Nat.cast_one]
    exact h x x.property

/-- **The `0`-th ramification group is the inertia group** (Stichtenoth, Definition 3.8.4): acting
trivially on the residue field is acting trivially to order `1` on the valuation ring. -/
@[simp]
theorem ramificationGroup_zero : ramificationGroup F P 0 = P.integers.inertiaSubgroup F :=
  IsLocalRing.ramificationGroup_zero_eq_inertiaSubgroup F P.integers

/-- The ramification groups decrease: vanishing to higher order is a stronger condition. -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup F P) := fun _ _ hij ↦
  IsLocalRing.ramificationGroup_antitone _ _ (Int.ofNat_le.mpr hij)

/-- Every ramification group sits inside the inertia group. -/
theorem ramificationGroup_le_inertiaSubgroup (i : ℕ) :
    ramificationGroup F P i ≤ P.integers.inertiaSubgroup F := by
  rw [← ramificationGroup_zero]
  exact ramificationGroup_antitone F P (Nat.zero_le i)

/-- **The ramification groups are normal in the decomposition group**
(Stichtenoth, Proposition 3.8.5). -/
instance normal_ramificationGroup (i : ℕ) : (ramificationGroup F P i).Normal :=
  IsLocalRing.instNormalRamificationGroup _ _ _

/-- **The ramification groups meet in the trivial group** (Stichtenoth, Proposition 3.8.5): an
automorphism fixing every function integral at `P` to every order is the identity, because the
valuation ring of `P` has `F'` for its field of fractions. -/
theorem iInf_ramificationGroup_eq_bot : ⨅ i, ramificationGroup F P i = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_iInf] at hg
  have hfix : ∀ x ∈ P.integers, (g : F' ≃ₐ[F] F') x = x := by
    intro x hx
    by_contra hne
    have h0 : (g : F' ≃ₐ[F] F') x - x ≠ 0 := sub_ne_zero.mpr hne
    have hmem := (mem_ramificationGroup_iff F P).mp
      (hg (P.ord ((g : F' ≃ₐ[F] F') x - x)).toNat) x hx
    have := (P.mem_filtration_iff_le_ord h0).mp hmem
    omega
  rw [Subgroup.mem_bot]
  exact ValuationSubring.decompositionSubgroup.ext P.integers fun x ↦
    hfix x x.property

/-- **The ramification groups of a place whose inertia group is finite are trivial from some index
on** (Stichtenoth, Proposition 3.8.5). -/
theorem exists_forall_ramificationGroup_eq_bot [Finite (ramificationGroup F P 0)] :
    ∃ N : ℕ, ∀ i, N ≤ i → ramificationGroup F P i = ⊥ := by
  exact TauCeti.Subgroup.exists_forall_eq_bot_of_antitone_iInf_eq_bot
    (ramificationGroup F P) (ramificationGroup_antitone F P)
    (iInf_ramificationGroup_eq_bot F P)

end Defs

section Residue

variable (F) (P : Place k F') {t : F'}

/-- **The ramification residue** (Stichtenoth, Proposition 3.8.5): for a uniformizer `t` at `P`,
the map sending an automorphism `σ` of `G_{i+1}(P)` to the function `z ↦ ((σ z - z)/t^{i+2})(P)`
on `𝒪_P`.  It is a homomorphism into the *additive* group of functions `𝒪_P → F'_P`, which is
therefore written multiplicatively here.  The map depends on the choice of `t`; its kernel,
`TauCeti.Place.ker_ramificationResidueHom`, does not. -/
noncomputable def ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    ramificationGroup F P (i + 1) →* Multiplicative (P.integers → P.ResidueField) :=
  ((AddEquiv.piCongrRight fun _ ↦
    (residueFieldEquivMaximalIdealGradedOfUniformizer
      ⟨t, P.mem_integers_iff_ord_nonneg.mpr (ht ▸ zero_le_one)⟩
      (P.irreducible_of_isUniformizer (P.isUniformizer_iff_ord_eq_one.mpr ht))
      (i + 2)).symm.toAddEquiv).toAddMonoidHom.toMultiplicative.comp
    (IsLocalRing.displacementHom (P.integers.decompositionSubgroup F) P.integers i)).comp
    (MulEquiv.subgroupCongr (ramificationGroup_def F P (i + 1))).toMonoidHom

/-- The value of the ramification residue at a function `x` integral at `P`, computed on any
representative `y` of `(σ x - x)/t^{i+2}` in `𝒪_P`. -/
theorem toAdd_ramificationResidueHom_apply (ht : P.ord t = 1) (i : ℕ)
    (g : ramificationGroup F P (i + 1)) (x y : P.integers)
    (hy : (y : F') = (t ^ (i + 2))⁻¹ *
      (((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') (x : F') - (x : F'))) :
    Multiplicative.toAdd (ramificationResidueHom F P ht i g) x =
      IsLocalRing.residue P.integers y := by
  have ht0 : t ≠ 0 := fun h0 ↦ by simp [h0, ord_zero] at ht
  rw [ramificationResidueHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, AddEquiv.coe_toAddMonoidHom,
    toAdd_ofAdd, AddEquiv.piCongrRight_apply, LinearEquiv.coe_toAddEquiv]
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer
    ⟨t, P.mem_integers_iff_ord_nonneg.mpr (ht ▸ zero_le_one)⟩
    (P.irreducible_of_isUniformizer (P.isUniformizer_iff_ord_eq_one.mpr ht)) (i + 2)).injective
  rw [LinearEquiv.coe_addEquiv_apply, LinearEquiv.apply_symm_apply,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk,
    IsLocalRing.toAdd_displacementHom_apply]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  apply Subtype.ext
  change ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') (x : F') - (x : F') =
    (y : F') * t ^ (i + 2)
  rw [hy, mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), one_mul]

/-- **The kernel of the ramification residue is the next ramification group** (Stichtenoth,
Proposition 3.8.5): so `G_{i+1}(P) / G_{i+2}(P)` embeds into the additive group of functions from
`𝒪_P` to the residue field at `P`. -/
theorem ker_ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    (ramificationResidueHom F P ht i).ker =
      (ramificationGroup F P (i + 2)).subgroupOf (ramificationGroup F P (i + 1)) := by
  ext g
  have hidx : ((i + 2 : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ) + 1 := by omega
  rw [ramificationResidueHom, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, ← toAdd_eq_zero, toAdd_ofAdd,
    AddEquiv.coe_toAddMonoidHom, map_eq_zero_iff _ (AddEquiv.injective _), toAdd_eq_zero,
    ← MonoidHom.mem_ker, IsLocalRing.ker_displacementHom, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_apply,
    ramificationGroup_def F P (i + 2), hidx]

end Residue

section Structure

variable (F) (P : Place k F')

/-- **The successive quotients of the ramification filtration are abelian**
(Stichtenoth, Proposition 3.8.5): a commutator of `G_{i+1}(P)` lies in `G_{i+2}(P)`. -/
theorem commutator_ramificationGroup_le (i : ℕ) :
    ⁅ramificationGroup F P (i + 1), ramificationGroup F P (i + 1)⁆ ≤
      ramificationGroup F P (i + 2) := by
  rw [ramificationGroup_def, ramificationGroup_def]
  have h : ((i + 2 : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ) + 1 := by omega
  rw [h]
  exact IsLocalRing.commutator_ramificationGroup_le
    (P.integers.decompositionSubgroup F) P.integers (by omega)

/-- **In characteristic `p` the successive quotients of the ramification filtration are killed by
`p`** (Stichtenoth, Proposition 3.8.5): the `p`-th power of an element of `G_{i+1}(P)` lies in
`G_{i+2}(P)`, so `G_{i+1}(P) / G_{i+2}(P)` is elementary abelian. -/
theorem pow_mem_ramificationGroup_of_charP (p : ℕ) [CharP P.ResidueField p] (i : ℕ)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P (i + 1)) :
    g ^ p ∈ ramificationGroup F P (i + 2) := by
  rw [ramificationGroup_def] at hg ⊢
  have h : ((i + 2 : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ) + 1 := by omega
  rw [h]
  exact IsLocalRing.pow_mem_ramificationGroup_of_charP p (by omega) hg

/-- **In characteristic zero a finite first ramification group is trivial** (Stichtenoth,
Proposition 3.8.5): each successive quotient embeds in a
torsion-free additive group, so the filtration is constant from `1` on and meets in `1`. -/
theorem ramificationGroup_one_eq_bot [Finite (ramificationGroup F P 1)]
    [CharZero P.ResidueField] :
    ramificationGroup F P 1 = ⊥ := by
  have hstep : ∀ i : ℕ, ramificationGroup F P (i + 1) ≤ ramificationGroup F P (i + 2) := by
    intro i
    have : Finite (IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F)
        P.integers ((i + 1 : ℕ) : ℤ)) := by
      rw [← ramificationGroup_def]
      exact Finite.of_injective _ (Subgroup.inclusion_injective
        (ramificationGroup_antitone F P (Nat.succ_le_succ (Nat.zero_le i))))
    have hsub := IsLocalRing.subsingleton_ramificationGroupGraded_of_charZero
      (P.integers.decompositionSubgroup F) P.integers (i := ((i + 1 : ℕ) : ℤ)) (by omega)
    rw [IsLocalRing.RamificationGroupGraded, QuotientGroup.subsingleton_iff,
      Subgroup.subgroupOf_eq_top] at hsub
    rwa [ramificationGroup_def, ramificationGroup_def, Nat.cast_succ (R := ℤ) (i + 1)]
  have hle : ∀ i : ℕ, ramificationGroup F P 1 ≤ ramificationGroup F P i := by
    intro i
    induction i with
    | zero => exact ramificationGroup_antitone F P (Nat.zero_le 1)
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact le_rfl
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact le_trans ih (hstep j)
  refine le_antisymm ?_ bot_le
  rw [← iInf_ramificationGroup_eq_bot F P]
  exact le_iInf hle

end Structure

end Place

end TauCeti
