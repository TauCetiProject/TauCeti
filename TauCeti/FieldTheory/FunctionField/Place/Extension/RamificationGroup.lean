/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup

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
at `P` gives a function `𝒪_P → F'_P`; the resulting `TauCeti.Place.ramificationResidueHom` is
obtained by composing `TauCeti.IsLocalRing.ramificationGroupToMaximalIdealGraded` with the
uniformizer identification `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`, and its
kernel is exactly `G_{i+2}(P)`.

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
  have : Finite (IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers 0) :=
    by rw [← Nat.cast_zero, ← ramificationGroup_def]; infer_instance
  obtain ⟨N, hN⟩ := IsLocalRing.exists_forall_ramificationGroup_eq_bot_of_finite
    (P.integers.decompositionSubgroup F) P.integers 0
  exact ⟨N.toNat, fun i hi ↦ by rw [ramificationGroup_def]; exact hN i (by omega)⟩

end Defs

section Residue

variable (F) (P : Place k F') {t : F'}

/-- **The ramification residue** (Stichtenoth, Proposition 3.8.5): for a uniformizer `t` at `P`,
the map sending an automorphism `σ` of `G_{i+1}(P)` to the function `z ↦ ((σ z - z)/t^{i+2})(P)`
on `𝒪_P`, obtained by composing `TauCeti.IsLocalRing.ramificationGroupToMaximalIdealGraded` with
the uniformizer coordinate `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`.  The map
depends on the choice of `t`; its kernel, `TauCeti.Place.ker_ramificationResidueHom`, does not. -/
noncomputable def ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    ramificationGroup F P (i + 1) →* Multiplicative (P.integers → P.ResidueField) :=
  let π : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (ht ▸ zero_le_one)⟩
  let hπ : Irreducible π :=
    P.irreducible_of_isUniformizer (P.isUniformizer_iff_ord_eq_one.mpr ht)
  let e :
      (↥(IsLocalRing.maximalIdeal P.integers ^ (i + 2)) ⧸
        (IsLocalRing.maximalIdeal P.integers • ⊤ :
          Submodule P.integers ↥(IsLocalRing.maximalIdeal P.integers ^ (i + 2)))) →+
        P.ResidueField :=
    (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm.toAddMonoidHom
  let post :
      Multiplicative (P.integers →
        ↥(IsLocalRing.maximalIdeal P.integers ^ (i + 2)) ⧸
          (IsLocalRing.maximalIdeal P.integers • ⊤ :
            Submodule P.integers ↥(IsLocalRing.maximalIdeal P.integers ^ (i + 2)))) →*
        Multiplicative (P.integers → P.ResidueField) :=
    (e.compLeft P.integers).toMultiplicative
  post.comp
    ((IsLocalRing.ramificationGroupToMaximalIdealGraded
        (P.integers.decompositionSubgroup F) P.integers i).comp
      (MulEquiv.subgroupCongr (by rw [ramificationGroup_def, Nat.cast_succ])).toMonoidHom)

/-- The value of the ramification residue at a function `x` integral at `P`, computed on any
representative `y` of `(σ x - x)/t^{i+2}` in `𝒪_P`. -/
theorem toAdd_ramificationResidueHom_apply (ht : P.ord t = 1) (i : ℕ)
    (g : ramificationGroup F P (i + 1)) (x y : P.integers)
    (hy : (y : F') = (t ^ (i + 2))⁻¹ *
      (((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') (x : F') - (x : F'))) :
    Multiplicative.toAdd (ramificationResidueHom F P ht i g) x =
      IsLocalRing.residue P.integers y := by
  have ht0 : t ≠ 0 := fun h0 ↦ by simp [h0, ord_zero] at ht
  let π : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (ht ▸ zero_le_one)⟩
  let hπ : Irreducible π :=
    P.irreducible_of_isUniformizer (P.isUniformizer_iff_ord_eq_one.mpr ht)
  let g' : IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers
      ((i : ℤ) + 1) :=
    ⟨(g : P.integers.decompositionSubgroup F), (Nat.cast_succ (R := ℤ) i).symm ▸ g.property⟩
  have heval : Multiplicative.toAdd (ramificationResidueHom F P ht i g) x =
      (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm
        (Submodule.Quotient.mk ⟨(g' : P.integers.decompositionSubgroup F) • x - x,
          IsLocalRing.mem_ramificationGroup_add_one_iff.mp g'.property x⟩) := by
    have hg' : (MulEquiv.subgroupCongr (by rw [ramificationGroup_def, Nat.cast_succ])) g = g' :=
      Subtype.ext (MulEquiv.subgroupCongr_apply _ _)
    rw [ramificationResidueHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hg']
    exact congrArg
      (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm
      (IsLocalRing.toAdd_ramificationGroupToMaximalIdealGraded_apply
        (P.integers.decompositionSubgroup F) P.integers i g' x)
  have hsub : (g' : P.integers.decompositionSubgroup F) • x - x = y * π ^ (i + 2) :=
    Subtype.ext <| by
      rw [AddSubgroupClass.coe_sub, ValuationSubring.coe_decompositionSubgroup_smul,
        MulMemClass.coe_mul, SubmonoidClass.coe_pow, hy]
      change ((g : F' ≃ₐ[F] F') (x : F') - (x : F')) =
        (t ^ (i + 2))⁻¹ * ((g : F' ≃ₐ[F] F') (x : F') - (x : F')) * t ^ (i + 2)
      rw [mul_assoc, mul_comm _ (t ^ (i + 2)), ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ ht0), one_mul]
  rw [heval]
  have hmk := congrArg (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm
    (residueFieldEquivMaximalIdealGradedOfUniformizer_mk π hπ (i + 2) y)
  rw [LinearEquiv.symm_apply_apply] at hmk
  rw [hmk]
  exact congrArg (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm
    (congrArg Submodule.Quotient.mk (Subtype.ext hsub))

/-- **The kernel of the ramification residue is the next ramification group** (Stichtenoth,
Proposition 3.8.5): so `G_{i+1}(P) / G_{i+2}(P)` embeds into the additive group of functions from
`𝒪_P` to the residue field at `P`. -/
theorem ker_ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    (ramificationResidueHom F P ht i).ker =
      (ramificationGroup F P (i + 2)).subgroupOf (ramificationGroup F P (i + 1)) := by
  let π : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.mpr (ht ▸ zero_le_one)⟩
  let hπ : Irreducible π :=
    P.irreducible_of_isUniformizer (P.isUniformizer_iff_ord_eq_one.mpr ht)
  let e :
      (↥(IsLocalRing.maximalIdeal P.integers ^ (i + 2)) ⧸
        (IsLocalRing.maximalIdeal P.integers • ⊤ :
          Submodule P.integers ↥(IsLocalRing.maximalIdeal P.integers ^ (i + 2)))) →+
        P.ResidueField :=
    (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm.toAddMonoidHom
  have hpost_inj : Function.Injective ((e.compLeft P.integers).toMultiplicative) := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    funext x
    exact (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (i + 2)).symm.injective
      (congrFun (congrArg Multiplicative.toAdd hab) x)
  have hker := IsLocalRing.ker_ramificationGroupToMaximalIdealGraded
    (P.integers.decompositionSubgroup F) P.integers i
  ext g
  rw [ramificationResidueHom, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
    map_eq_one_iff _ hpost_inj, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
    MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_apply, Subgroup.mem_subgroupOf]
  simp [ramificationGroup_def, Nat.cast_succ]

end Residue

section Structure

variable (F) (P : Place k F')

/-- **The successive quotients of the ramification filtration are abelian**
(Stichtenoth, Proposition 3.8.5): a commutator of `G_{i+1}(P)` lies in `G_{i+2}(P)`. -/
theorem commutator_ramificationGroup_le (i : ℕ) :
    ⁅ramificationGroup F P (i + 1), ramificationGroup F P (i + 1)⁆ ≤
      ramificationGroup F P (i + 2) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  let a' : IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers
      ((i : ℤ) + 1) := ⟨a, (Nat.cast_succ (R := ℤ) i).symm ▸ ha⟩
  let b' : IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers
      ((i : ℤ) + 1) := ⟨b, (Nat.cast_succ (R := ℤ) i).symm ▸ hb⟩
  have hcomm : (QuotientGroup.mk (a' * b' * a'⁻¹ * b'⁻¹) :
      IsLocalRing.RamificationGroupGraded (P.integers.decompositionSubgroup F) P.integers
        ((i : ℤ) + 1)) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm' (QuotientGroup.mk a'), mul_inv_cancel_right, mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hcomm
  simpa [ramificationGroup_def, Nat.cast_succ, commutatorElement_def, a', b'] using hcomm

/-- **In characteristic `p` the successive quotients of the ramification filtration are killed by
`p`** (Stichtenoth, Proposition 3.8.5): the `p`-th power of an element of `G_{i+1}(P)` lies in
`G_{i+2}(P)`, so `G_{i+1}(P) / G_{i+2}(P)` is elementary abelian. -/
theorem pow_mem_ramificationGroup_of_charP (p : ℕ) [CharP P.ResidueField p] (i : ℕ)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P (i + 1)) :
    g ^ p ∈ ramificationGroup F P (i + 2) := by
  let g' : IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers
      ((i : ℤ) + 1) := ⟨g, (Nat.cast_succ (R := ℤ) i).symm ▸ hg⟩
  have hpow : (QuotientGroup.mk g' :
      IsLocalRing.RamificationGroupGraded (P.integers.decompositionSubgroup F) P.integers
        ((i : ℤ) + 1)) ^ p = 1 :=
    IsLocalRing.ramificationGroupGraded_natCast_succ_pow_char_eq_one p i _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hpow
  exact_mod_cast hpow

/-- **In characteristic zero a finite first ramification group is trivial** (Stichtenoth,
Proposition 3.8.5): each successive quotient embeds in a
torsion-free additive group, so the filtration is constant from `1` on and meets in `1`. -/
theorem ramificationGroup_one_eq_bot [Finite (ramificationGroup F P 1)]
    [CharZero P.ResidueField] :
    ramificationGroup F P 1 = ⊥ := by
  have : Finite (IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers 1) :=
    ‹_›
  simpa only [ramificationGroup_def, Nat.cast_one] using
    IsLocalRing.ramificationGroup_one_eq_bot_of_charZero
      (P.integers.decompositionSubgroup F) P.integers

end Structure

end Place

end TauCeti
