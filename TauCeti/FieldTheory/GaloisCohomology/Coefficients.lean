/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import TauCeti.RingTheory.RootsOfUnity.Action
-- Non-public: the roots of unity of a separably closed field are used only inside a proof.
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
-- Non-public: lifting a unit of `Kˢ` lying in `K` to a unit of `K` is used only inside a proof.
import TauCeti.Algebra.GroupWithZero.Units.Basic

/-!
# The multiplicative coefficient modules of Galois cohomology

Galois cohomology takes its coefficients in discrete modules over `G_K = AbsoluteGaloisGroup K`,
the automorphism group of a separable closure `Kˢ`. This file fixes the two multiplicative
coefficient modules once and for all, written additively through `Additive` as Mathlib's
`Representation.ofMulDistribMulAction` does:

```text
UnitsCoeff K = Additive (Kˢ)ˣ,      KummerCoeff K n = Additive μₙ,
```

with `μₙ = rootsOfUnity n Kˢ`. Both are **discrete** `G_K`-modules: their point stabilizers are
open because every element of `Kˢ` is separable over `K`, hence lies in a finite subextension
(`TauCeti.stabilizer_isOpen_units`). The action on `μₙ` is in general nontrivial, and the Kummer
isomorphism is false for the trivial action, so it is the module and not the abstract group that
is named here.

The two maps between them assemble the **Kummer sequence**

```text
1 ⟶ μₙ ⟶ (Kˢ)ˣ ⟶ (Kˢ)ˣ ⟶ 1
```

as a `TauCeti.ContCohomology.DiscreteShortExact`, so that the long exact sequence of continuous
cohomology applies to it verbatim. Exactness in the middle holds over any field and for any `n`;
surjectivity on the right is where `IsUnit (n : K)` enters, through the separability of `Xⁿ - a`
and the separable closedness of `Kˢ`.

Finally `TauCeti.baseUnitsEquivInvariants` identifies `H⁰(G_K, (Kˢ)ˣ)` with `Kˣ`. These are not
the same Lean type — the invariants are an additive subgroup of `Additive (Kˢ)ˣ` — so what is
supplied is the canonical isomorphism and not an equality. Using the **separable** closure is
essential: for imperfect `K` the fixed field of the automorphism group of an algebraic closure is
the purely inseparable closure of `K` and not `K` itself
(`TauCeti.mem_perfectClosure_iff_fixed`), so the invariants of the units of an algebraic closure
are strictly larger than `Kˣ`.

## Main definitions

* `TauCeti.UnitsCoeff`, `TauCeti.KummerCoeff`: the two coefficient modules, with their discrete
  topologies.
* `TauCeti.kummerCoeffAddEquivZMod`: an additive isomorphism `μₙ ≃ ℤ/nℤ`, for `n` invertible in
  `K`.
* `TauCeti.kummerCoeffIncl`, `TauCeti.unitsCoeffPow`: the inclusion `μₙ ↪ (Kˢ)ˣ` and the `n`-th
  power map, the two maps of the Kummer sequence.
* `TauCeti.kummerShortExact`: the Kummer sequence as a short exact sequence of discrete
  `G_K`-modules.
* `TauCeti.baseUnitsEquivInvariants`: the isomorphism `Kˣ ≅ H⁰(G_K, (Kˢ)ˣ)`.
* `TauCeti.embeddedUnitsInvariants`: for a `K`-embedding `σ : L →ₐ[K] Kˢ`, a unit `b` of `L` as
  the invariant `σ b` of `(Kˢ)ˣ` under the subgroup of `G_K` fixing `σ(L)`.
* `TauCeti.embeddedUnitsEquivInvariants`: the isomorphism `Lˣ ≅ H⁰(Gal(Kˢ/σ(L)), (Kˢ)ˣ)`.
  For normal `L/K` it intertwines the action of `σ.restrictNormalHom g` with that of `g`
  (`TauCeti.embeddedUnitsEquivInvariants_restrictNormalHom_smul`, with the `simp` form
  `TauCeti.coe_embeddedUnitsInvariants_map_restrictNormalHom`).

## Main results

* `TauCeti.unitsCoeff_continuousSMul`, `TauCeti.kummerCoeff_continuousSMul`: the coefficients are
  discrete modules, that is, the action is continuous.
* `TauCeti.natCard_kummerCoeff`: `μₙ` has `n` elements, for `n` invertible in `K`.
* `TauCeti.smul_kummerCoeff_eq_self`: the action on `μₙ` is trivial when `K` contains a primitive
  `n`th root of unity.
* `TauCeti.mem_H0_unitsCoeff_iff`: a unit of `Kˢ` fixed by `G_K` comes from `Kˣ`.
* `TauCeti.mem_H0_fixingSubgroup_unitsCoeff_iff`: a unit of `Kˢ` fixed by the subgroup fixing
  `σ(L)` comes from `Lˣ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it, for the Kummer sequence and the invariants of `(Kˢ)ˣ`.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

variable (K : Type*) [Field K]

/-! ### The units of the separable closure -/

/-- The multiplicative coefficient module of Galois cohomology: the units of a separable closure
of `K`, written additively. This is the module Hilbert 90 and the cohomological Brauer group are
stated at, and `KummerCoeff K n` is its `n`-torsion submodule. -/
abbrev UnitsCoeff : Type _ := Additive (SeparableClosure K)ˣ

instance : TopologicalSpace (UnitsCoeff K) := ⊥

instance : DiscreteTopology (UnitsCoeff K) := ⟨rfl⟩

/-- **`(Kˢ)ˣ` is a discrete `G_K`-module**: every unit of `Kˢ` is separable over `K`, so it lies
in a finite subextension and its stabilizer is open. -/
instance unitsCoeff_continuousSMul : ContinuousSMul (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  continuousSMul_iff_stabilizer_isOpen.2 fun x => stabilizer_isOpen_units (K := K) x.toMul

/-! ### The roots of unity -/

/-- The Kummer coefficient module: the `n`-th roots of unity in a separable closure of `K`,
written additively. The `G_K`-action on `μₙ` is in general nontrivial and the Kummer isomorphism
depends on it, so the coefficients are fixed as this module rather than as an abstract cyclic
group. -/
abbrev KummerCoeff (n : ℕ) : Type _ := Additive (rootsOfUnity n (SeparableClosure K))

variable (n : ℕ)

instance : TopologicalSpace (KummerCoeff K n) := ⊥

instance : DiscreteTopology (KummerCoeff K n) := ⟨rfl⟩

/-- **`μₙ` is a discrete `G_K`-module**: the stabilizer of a root of unity is the stabilizer of
the underlying unit of `Kˢ`, which is open. -/
instance kummerCoeff_continuousSMul :
    ContinuousSMul (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
  continuousSMul_iff_stabilizer_isOpen.2 fun x => by
    convert stabilizer_isOpen_units (K := K) (x.toMul : (SeparableClosure K)ˣ) using 2
    ext σ
    refine ⟨fun h => ?_, fun h => Additive.toMul.injective (Subtype.ext (by simpa using h))⟩
    simpa using
      congrArg (fun v : KummerCoeff K n => (v.toMul : (SeparableClosure K)ˣ)) h

variable {K n} in
/-- **`G_K` acts trivially on `μₙ` when `K` contains a primitive `n`th root of unity `ζ`**: every
`n`th root of unity of `Kˢ` is then a power of `ζ`, which `G_K` fixes. -/
theorem smul_kummerCoeff_eq_self [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (g : AbsoluteGaloisGroup K) (x : KummerCoeff K n) : g • x = x := by
  have hζs := (hζ.map_of_injective (algebraMap K (SeparableClosure K)).injective).isUnit_unit
    (NeZero.ne n)
  obtain ⟨i, -, hi⟩ := hζs.eq_pow_of_mem_rootsOfUnity x.toMul.2
  have hx : (((x.toMul : rootsOfUnity n (SeparableClosure K)) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = algebraMap K _ ζ ^ i := by
    rw [← hi, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  simp only [Additive.toMul_smul, rootsOfUnity.coe_smul, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_ofClass]
  rw [hx, map_pow, AlgEquiv.commutes]

variable {K n} in
/-- **`μₙ` has `n` elements** for `n` invertible in `K`. -/
theorem natCard_kummerCoeff (hn : IsUnit (n : K)) : Nat.card (KummerCoeff K n) = n := by
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  have : NeZero n := NeZero.of_neZero_natCast K
  exact (Nat.card_congr Additive.toMul).trans
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (SeparableClosure K) n)

variable {K n} in
/-- **`μₙ` is cyclic of order `n`** for `n` invertible in `K`: the `n`th roots of unity of `Kˢ`
are additively isomorphic to `ℤ/nℤ`. The isomorphism is not canonical; it amounts to a choice of
primitive `n`th root of unity in `Kˢ`. -/
def kummerCoeffAddEquivZMod (hn : IsUnit (n : K)) : KummerCoeff K n ≃+ ZMod n :=
  have : NeZero (n : K) := ⟨hn.ne_zero⟩
  have : NeZero n := NeZero.of_neZero_natCast K
  addEquivOfAddCyclicCardEq <| by rw [Nat.card_zmod, natCard_kummerCoeff hn]

/-! ### The two maps of the Kummer sequence -/

/-- The inclusion `μₙ ↪ (Kˢ)ˣ`, the left-hand map of the Kummer sequence. -/
def kummerCoeffIncl : KummerCoeff K n →+ UnitsCoeff K :=
  MonoidHom.toAdditive (rootsOfUnity n (SeparableClosure K)).subtype

@[simp]
theorem toMul_kummerCoeffIncl (x : KummerCoeff K n) :
    (kummerCoeffIncl K n x).toMul = (x.toMul : (SeparableClosure K)ˣ) :=
  (rfl)

@[simp]
theorem kummerCoeffIncl_equivariant (g : AbsoluteGaloisGroup K) (x : KummerCoeff K n) :
    kummerCoeffIncl K n (g • x) = g • kummerCoeffIncl K n x :=
  Additive.toMul.injective (by simp)

theorem kummerCoeffIncl_injective : Function.Injective (kummerCoeffIncl K n) := fun x y h =>
  Additive.toMul.injective <| Subtype.ext <| by
    simpa only [toMul_kummerCoeffIncl] using congrArg Additive.toMul h

/-- The `n`-th power map on `(Kˢ)ˣ`, the right-hand map of the Kummer sequence. In additive
notation it is multiplication by `n`, which is `TauCeti.unitsCoeffPow_eq_nsmul`. -/
def unitsCoeffPow : UnitsCoeff K →+ UnitsCoeff K :=
  MonoidHom.toAdditive (powMonoidHom n)

@[simp]
theorem toMul_unitsCoeffPow (x : UnitsCoeff K) :
    (unitsCoeffPow K n x).toMul = x.toMul ^ n :=
  (rfl)

theorem unitsCoeffPow_eq_nsmul (x : UnitsCoeff K) : unitsCoeffPow K n x = n • x :=
  Additive.toMul.injective <| by simp [toMul_nsmul]

@[simp]
theorem unitsCoeffPow_equivariant (g : AbsoluteGaloisGroup K) (x : UnitsCoeff K) :
    unitsCoeffPow K n (g • x) = g • unitsCoeffPow K n x :=
  Additive.toMul.injective <| by simp [smul_pow']

/-- **Exactness of the Kummer sequence in the middle**: a unit of `Kˢ` has trivial `n`-th power
exactly when it is an `n`-th root of unity. This holds over any field and for every `n`. -/
theorem kummerSequence_exact : Function.Exact (kummerCoeffIncl K n) (unitsCoeffPow K n) := by
  intro x
  refine ⟨fun hx => ⟨Additive.ofMul ⟨x.toMul, ?_⟩, Additive.toMul.injective (by simp)⟩, ?_⟩
  · simpa only [mem_rootsOfUnity, toMul_unitsCoeffPow, toMul_zero] using
      congrArg Additive.toMul hx
  · rintro ⟨y, rfl⟩
    exact Additive.toMul.injective <| by
      simpa only [toMul_unitsCoeffPow, toMul_kummerCoeffIncl, toMul_zero] using
        (mem_rootsOfUnity n _).1 y.toMul.2

/-- **The `n`-th power map on the units of a separable closure is surjective** when `n` is
invertible in `K`: `Xⁿ - a` is then separable, and `Kˢ` is separably closed. -/
theorem unitsCoeffPow_surjective (hn : IsUnit (n : K)) :
    Function.Surjective (unitsCoeffPow K n) := by
  have hn0 : (n : SeparableClosure K) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (SeparableClosure K))).2 hn.ne_zero
    rwa [map_natCast] at h
  have hn' : n ≠ 0 := by rintro rfl; simp at hn0
  have : NeZero (n : SeparableClosure K) := ⟨hn0⟩
  intro x
  obtain ⟨z, hz⟩ :=
    IsSepClosed.exists_pow_nat_eq ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) n
  have hz0 : z ≠ 0 := fun h => x.toMul.ne_zero (by rw [← hz, h, zero_pow hn'])
  refine ⟨Additive.ofMul (Units.mk0 z hz0), Additive.toMul.injective (Units.ext ?_)⟩
  simpa using hz

/-- **The Kummer sequence** `1 → μₙ → (Kˢ)ˣ → (Kˢ)ˣ → 1` of discrete `G_K`-modules, for `n`
invertible in `K` (NSW (6.2.1)). It is the datum the long exact sequence of continuous cohomology
is applied to, and its degree-zero connecting map is the Kummer map. -/
def kummerShortExact (hn : IsUnit (n : K)) :
    DiscreteShortExact (AbsoluteGaloisGroup K) (KummerCoeff K n) (UnitsCoeff K)
      (UnitsCoeff K) where
  incl := kummerCoeffIncl K n
  proj := unitsCoeffPow K n
  incl_equivariant := kummerCoeffIncl_equivariant K n
  proj_equivariant := unitsCoeffPow_equivariant K n
  incl_injective := kummerCoeffIncl_injective K n
  proj_surjective := unitsCoeffPow_surjective K n hn
  exact := kummerSequence_exact K n

@[simp]
theorem kummerShortExact_incl (hn : IsUnit (n : K)) :
    (kummerShortExact K n hn).incl = kummerCoeffIncl K n :=
  (rfl)

@[simp]
theorem kummerShortExact_proj (hn : IsUnit (n : K)) :
    (kummerShortExact K n hn).proj = unitsCoeffPow K n :=
  (rfl)

/-! ### The invariants of the units -/

variable {K}

/-- A unit of the base field is fixed by the absolute Galois group after mapping into the
separable closure. -/
theorem smul_units_map_algebraMap (g : AbsoluteGaloisGroup K) (a : Kˣ) :
    g • Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a :=
  Units.ext (AlgEquiv.commutes g (a : K))

/-- **A unit of `Kˢ` fixed by the whole Galois group comes from `Kˣ`.** This is the fixed-field
theorem for the separable closure read on units: `InfiniteGalois.mem_range_algebraMap_iff_fixed`
supplies a base-field preimage of the unit, and `TauCeti.mem_range_iff_exists_units_map_eq`
promotes it to a unit of `K`. -/
theorem mem_H0_unitsCoeff_iff {u : UnitsCoeff K} :
    u ∈ H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) ↔
      ∃ a : Kˣ, Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a = u.toMul := by
  rw [FixedPoints.mem_addSubgroup]
  refine ⟨fun hu => ?_, ?_⟩
  · -- The unit is fixed, so it comes from the base field.
    have hfixU : ∀ σ : AbsoluteGaloisGroup K,
        Units.map (σ : SeparableClosure K →* SeparableClosure K) u.toMul = u.toMul :=
      fun σ => by simpa using congrArg Additive.toMul (hu σ)
    have hfix : ∀ σ : AbsoluteGaloisGroup K,
        σ ((u.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) =
          ((u.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) :=
      fun σ => congrArg Units.val (hfixU σ)
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    exact (mem_range_iff_exists_units_map_eq (algebraMap K (SeparableClosure K)) u.toMul).mp
      ⟨a, ha⟩
  · rintro ⟨a, ha⟩ σ
    refine Additive.toMul.injective ?_
    rw [Additive.toMul_smul, ← ha]
    exact smul_units_map_algebraMap σ a

variable (K)

/-- **The invariants of `(Kˢ)ˣ` are the units of `K`**, that is `H⁰(G_K, (Kˢ)ˣ) ≅ Kˣ`. The two
sides are different Lean types, so this canonical isomorphism — and not an equality — is what a
cohomological construction starting from `Kˣ` goes through, the Kummer map among them. -/
def baseUnitsEquivInvariants :
    Additive Kˣ ≃+ H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) :=
  AddEquiv.ofBijective
    ((MonoidHom.toAdditive
      (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom)).codRestrict _
        fun a => mem_H0_unitsCoeff_iff.2 ⟨a.toMul, rfl⟩)
    ⟨fun x y h => Additive.toMul.injective <| Units.ext <|
        (algebraMap K (SeparableClosure K)).injective <|
          congrArg (fun v : H0 (AbsoluteGaloisGroup K) (UnitsCoeff K) =>
            (((v : UnitsCoeff K).toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) h,
      fun u => by
        obtain ⟨a, ha⟩ := mem_H0_unitsCoeff_iff.1 u.2
        exact ⟨Additive.ofMul a, Subtype.ext (Additive.toMul.injective ha)⟩⟩

@[simp]
theorem toMul_coe_baseUnitsEquivInvariants (a : Additive Kˣ) :
    ((baseUnitsEquivInvariants K a : UnitsCoeff K).toMul : (SeparableClosure K)ˣ) =
      Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a.toMul :=
  (rfl)

section Embedded

variable (L : Type*) [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)

/-- **A unit of `L` as an invariant of `(Kˢ)ˣ` under `Gal(Kˢ/σ(L))`**: every automorphism of `Kˢ`
fixing `σ(L)` fixes `σ b`. For the subgroup cut out by `σ` this is what
`TauCeti.baseUnitsEquivInvariants` is for the whole of `G_K`. -/
def embeddedUnitsInvariants (b : Lˣ) : H0 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K) :=
  ⟨Additive.ofMul (Units.map σ.toRingHom.toMonoidHom b), by
    refine (FixedPoints.mem_addSubgroup _ _ _).2 fun h => ?_
    rw [Subgroup.smul_def (α := UnitsCoeff K), ← Additive.ofMul_smul]
    exact congrArg Additive.ofMul (Units.ext
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 (σ b) ⟨b, rfl⟩))⟩

/-- The invariant attached to a unit of `L` is the image of that unit in `(Kˢ)ˣ`. -/
@[simp]
theorem toMul_coe_embeddedUnitsInvariants (b : Lˣ) :
    ((embeddedUnitsInvariants K L σ b : UnitsCoeff K).toMul : (SeparableClosure K)ˣ) =
      Units.map σ.toRingHom.toMonoidHom b :=
  (rfl)

/-- The unit `1` of `L` is the zero invariant. -/
@[simp]
theorem embeddedUnitsInvariants_one : embeddedUnitsInvariants K L σ 1 = 0 :=
  Subtype.ext <| Additive.toMul.injective <| map_one (Units.map σ.toRingHom.toMonoidHom)

/-- Multiplication of units of `L` becomes addition of invariants. -/
@[simp]
theorem embeddedUnitsInvariants_mul (a b : Lˣ) :
    embeddedUnitsInvariants K L σ (a * b) =
      embeddedUnitsInvariants K L σ a + embeddedUnitsInvariants K L σ b :=
  Subtype.ext <| Additive.toMul.injective <| map_mul (Units.map σ.toRingHom.toMonoidHom) a b

variable {K L σ} in
/-- **A unit of `Kˢ` fixed by `Gal(Kˢ/σ(L))` comes from `Lˣ`.** This is the fixed-field theorem
`InfiniteGalois.fixedField_fixingSubgroup` for the intermediate field `σ(L)`, read on units. -/
theorem mem_H0_fixingSubgroup_unitsCoeff_iff {u : UnitsCoeff K} :
    u ∈ H0 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K) ↔
      ∃ b : Lˣ, Units.map σ.toRingHom.toMonoidHom b = u.toMul := by
  refine ⟨fun hu => ?_, ?_⟩
  · have hfix : ((u.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) ∈
        IntermediateField.fixedField σ.fieldRange.fixingSubgroup :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun g hg => by
        have h := (FixedPoints.mem_addSubgroup _ _ _).1 hu ⟨g, hg⟩
        rw [Subgroup.smul_def (α := UnitsCoeff K)] at h
        have h' := congrArg (fun v : UnitsCoeff K =>
          ((v.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) h
        simp only [Additive.toMul_smul] at h'
        simpa [AlgEquiv.smul_units_def] using h'
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hfix
    obtain ⟨b, hb⟩ := hfix
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact u.toMul.ne_zero (by simpa using hb.symm)
    exact ⟨Units.mk0 b hb0, Units.ext hb⟩
  · rintro ⟨b, hb⟩
    have hu : u = embeddedUnitsInvariants K L σ b :=
      Additive.toMul.injective (hb.symm.trans (toMul_coe_embeddedUnitsInvariants K L σ b).symm)
    rw [hu]
    exact (embeddedUnitsInvariants K L σ b).2

/-- **The invariants of `(Kˢ)ˣ` under `Gal(Kˢ/σ(L))` are the units of `L`**, that is
`H⁰(Gal(Kˢ/σ(L)), (Kˢ)ˣ) ≅ Lˣ`: the additive equivalence whose forward map is
`embeddedUnitsInvariants`. For `σ(L) = K` this is `TauCeti.baseUnitsEquivInvariants`. -/
def embeddedUnitsEquivInvariants :
    Additive Lˣ ≃+ H0 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K) :=
  AddEquiv.ofBijective
    ({ toFun := fun b => embeddedUnitsInvariants K L σ b.toMul
       map_zero' := embeddedUnitsInvariants_one K L σ
       map_add' := fun a b => embeddedUnitsInvariants_mul K L σ a.toMul b.toMul } :
      Additive Lˣ →+ H0 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K))
    ⟨fun a b h => Additive.toMul.injective <| Units.map_injective σ.toRingHom.injective <| by
        simpa using congrArg (fun v : H0 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K) =>
          ((v : UnitsCoeff K).toMul : (SeparableClosure K)ˣ)) h,
      fun u => by
        obtain ⟨b, hb⟩ := mem_H0_fixingSubgroup_unitsCoeff_iff.1 u.2
        exact ⟨Additive.ofMul b, Subtype.ext (Additive.toMul.injective
          ((toMul_coe_embeddedUnitsInvariants K L σ b).trans hb))⟩⟩

/-- `embeddedUnitsEquivInvariants` sends a unit of `L` to its invariant `embeddedUnitsInvariants`.
-/
@[simp]
theorem embeddedUnitsEquivInvariants_apply (b : Additive Lˣ) :
    embeddedUnitsEquivInvariants K L σ b = embeddedUnitsInvariants K L σ b.toMul :=
  (rfl)

/-- **`embeddedUnitsInvariants` is Galois-equivariant**, in `simp`-normal form: for normal `L/K`,
embedding by `σ` turns the restriction `σ.restrictNormalHom g` acting on `Lˣ` into the action of
`g` on `(Kˢ)ˣ`. -/
@[simp]
theorem coe_embeddedUnitsInvariants_map_restrictNormalHom [Normal K L]
    (g : AbsoluteGaloisGroup K) (b : Lˣ) :
    (embeddedUnitsInvariants K L σ (Units.map (σ.restrictNormalHom g : L →* L) b) :
        UnitsCoeff K) =
      g • (embeddedUnitsInvariants K L σ b : UnitsCoeff K) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [Additive.toMul_smul, toMul_coe_embeddedUnitsInvariants, toMul_coe_embeddedUnitsInvariants,
    AlgEquiv.smul_units_def]
  simp only [Units.coe_map]
  exact σ.restrictNormalHom_commutes g b

/-- **`embeddedUnitsEquivInvariants` is Galois-equivariant**: for normal `L/K`, embedding by `σ`
turns the action of the restriction `σ.restrictNormalHom g` on `Lˣ` into the action of `g` on
`(Kˢ)ˣ`. -/
theorem embeddedUnitsEquivInvariants_restrictNormalHom_smul [Normal K L]
    (g : AbsoluteGaloisGroup K) (b : Additive Lˣ) :
    (embeddedUnitsEquivInvariants K L σ (Additive.ofMul (σ.restrictNormalHom g • b.toMul)) :
        UnitsCoeff K) =
      g • (embeddedUnitsEquivInvariants K L σ b : UnitsCoeff K) := by
  simp

end Embedded

end TauCeti
