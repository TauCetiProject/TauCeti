/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Elementary
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Root-subgroup maps of the Chevalley exceptional isogenies

Over a commutative ring `A` of characteristic `2` for types `B₂` and `F₄`, and of characteristic
`3` for type `G₂`, Steinberg's exceptional endomorphism `τ` of a Chevalley group acts on the
root subgroup of a root `α` by

```text
x_α(u) ↦ x_{f(α)}(ε_α u ^ q(α)),
```

where `f` is the root-index involution of the special root-datum isogeny
(`TauCeti.DynkinType.b2SpecialIsogeny`, `TauCeti.DynkinType.f4SpecialIsogeny`, or
`TauCeti.DynkinType.g2SpecialIsogeny`), the exponent `q(α) = f.exponent (f.indexEquiv α)` is `1`
when `α` is long and the defining characteristic `p` when `α` is short, and `ε_α = ±1` is a sign
determined by the pinned Chevalley system (`1` in characteristic `2`, and
`TauCeti.DynkinType.g2SpecialIsogenySign` in type `G₂`).

Because `u ↦ u ^ q(α)` is either the identity or the Frobenius endomorphism of `A`, these formulas
already define genuine group homomorphisms `Multiplicative A →* D.points A` into the points of
every Chevalley datum `D` of the corresponding Dynkin type, valued in `D.elementarySubgroup A`.
This file constructs those three families of root-subgroup homomorphisms and establishes their
pinned simple-root equations, Steinberg Weyl-element equations, and square equations `τ² = Frob_p`
on all root subgroups; the preservation of the Chevalley commutator relations in characteristics
`2` and `3` is proved in `DoublyLaced.lean` and `G2.lean`.

## Main definitions

* `TauCeti.DynkinType.g2SpecialIsogenySign`: the twelve signs `ε_α ∈ ℤˣ` of the `G₂` exceptional
  isogeny in the pinned Chevalley basis (`+1` on the four signed simple roots and on the positive
  and negative roots `2α₁ + α₂` and `3α₁ + 2α₂`, `-1` on `±(α₁ + α₂)` and `±(3α₁ + α₂)`).
* `TauCeti.DynkinType.ChevalleyDatum.b2SpecialIsogenyRootSubgroup`,
  `TauCeti.DynkinType.ChevalleyDatum.f4SpecialIsogenyRootSubgroup`, and
  `TauCeti.DynkinType.ChevalleyDatum.g2SpecialIsogenyRootSubgroup`: the transformed root-subgroup
  homomorphisms `Multiplicative A →* D.points A` over `[ExpChar A 2]` and `[ExpChar A 3]`.

## Main results

* `b2SpecialIsogenyRootSubgroup_simpleIndex`, `f4SpecialIsogenyRootSubgroup_simpleIndex`,
  `g2SpecialIsogenyRootSubgroup_simpleIndex`, and their `reflectionPerm_simpleIndex` counterparts:
  on the positive and negative simple roots, the maps permute nodes by the pinned length
  permutation with exponent `(t.rootLength (σ i)).toNat` and unit sign `1`.
* `b2SpecialIsogenyRootSubgroup_weylElement`, `f4SpecialIsogenyRootSubgroup_weylElement`, and
  `g2SpecialIsogenyRootSubgroup_weylElement`: Steinberg's Weyl word `x'_α(s) x'_{-α}(-s⁻¹) x'_α(s)`
  evaluates to `D.weylElement` at the partner root.
* `b2SpecialIsogenyRootSubgroup_comp_self`, `f4SpecialIsogenyRootSubgroup_comp_self`, and
  `g2SpecialIsogenyRootSubgroup_comp_self`: applying the root-subgroup map twice equals
  `D.frobenius p 1 A` on every root subgroup.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Lemma 53 and Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3–12.4.
-/

public section

namespace TauCeti.DynkinType

/-- **The root-subgroup sign table of the `G₂` exceptional isogeny** in characteristic three,
indexed by the twelve roots of `TauCeti.DynkinType.g2Root`. With unit sign `+1` on the positive and
negative simple roots `0, 1, 6, 7`, the pinned Chevalley structure constants
`TauCeti.DynkinType.g2StructureConstant` force `-1` on `±(α₁ + α₂)` (`2, 8`) and `±(3α₁ + α₂)`
(`4, 10`) and `+1` on `±(2α₁ + α₂)` (`3, 9`) and `±(3α₁ + 2α₂)` (`5, 11`). -/
def g2SpecialIsogenySign : Fin 12 → ℤˣ :=
  ![1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1]

/-- The explicit entries of `TauCeti.DynkinType.g2SpecialIsogenySign`. -/
theorem g2SpecialIsogenySign_def :
    g2SpecialIsogenySign = ![1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1] :=
  (rfl)

/-- Every root of `G₂` and its negative carry the same exceptional-isogeny sign. -/
@[simp] theorem g2SpecialIsogenySign_add_six (i : Fin 12) :
    g2SpecialIsogenySign (i + 6) = g2SpecialIsogenySign i := by
  decide +revert

/-- The `G₂` exceptional-isogeny sign is invariant under the special root permutation. -/
@[simp] theorem g2SpecialIsogenySign_g2SpecialIsogenyIndex (i : Fin 12) :
    g2SpecialIsogenySign (g2SpecialIsogenyIndex i) = g2SpecialIsogenySign i := by
  rw [g2SpecialIsogenyIndex_def]
  decide +revert

/-- On the two positive simple roots of `G₂`, the exceptional-isogeny sign is `1`. -/
@[simp] theorem g2SpecialIsogenySign_castLE (i : Fin 2) :
    g2SpecialIsogenySign (Fin.castLE (by omega) i) = 1 := by
  fin_cases i <;> decide

namespace ChevalleyDatum

open Multiplicative

universe v

private def congrIsogeny {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P Q : RootPairing ι R M N} (h : P = Q)
    (f : RootPairingIsogeny Q Q) : RootPairingIsogeny P P where
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  exponent := f.exponent
  exponent_pos := f.exponent_pos
  weightMap_injective := f.weightMap_injective
  coweightMap_injective := f.coweightMap_injective
  weightMap_finiteIndex := f.weightMap_finiteIndex
  coweightMap_finiteIndex := f.coweightMap_finiteIndex
  weight_coweight_transpose := by subst h; exact f.weight_coweight_transpose
  root_weightMap := by subst h; exact f.root_weightMap
  coroot_coweightMap := by subst h; exact f.coroot_coweightMap

private theorem congrIsogeny_mul_self {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    {P Q : RootDatum ι M N} (h : P = Q) (f : RootPairingIsogeny Q Q) (c : ℕ+)
    (hf : f * f = RootPairingIsogeny.smulId Q c) :
    congrIsogeny h f * congrIsogeny h f = RootPairingIsogeny.smulId P c := by
  subst h
  exact hf

private def specialExpRingHom (p : ℕ) (A : Type v) [CommRing A] [ExpChar A p] (q : ℕ)
    (hq : q = 1 ∨ q = p) : A →+* A :=
  (if q = 1 then RingHom.id A else _root_.frobenius A p).copy (fun u => u ^ q) (by
    ext u
    rcases hq with rfl | rfl
    · simp
    · by_cases h1 : q = 1 <;> simp [h1, _root_.frobenius_def])

private noncomputable def specialRootSubgroupAux {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht) (p : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hq : ∀ α, (f.exponent α).toNat = 1 ∨ (f.exponent α).toNat = p)
    (ε : Fin t.numRoots → ℤˣ) (α : Fin t.numRoots) : Multiplicative A →* D.points A where
  toFun u := D.rootSubgroupPoints (f.indexEquiv α) A
    (ofAdd (((ε α : ℤ) : A) * toAdd u ^ (f.exponent (f.indexEquiv α)).toNat))
  map_one' := by
    -- Express `0 ^ q` as `specialExpRingHom` applied to `0`.
    change D.rootSubgroupPoints (f.indexEquiv α) A
      (ofAdd (((ε α : ℤ) : A) * specialExpRingHom p A _ (hq _) 0)) = 1
    simp
  map_mul' u v := by
    simp only [toAdd_mul, ← map_mul, ← ofAdd_add]
    congr 2
    -- Express `(toAdd u + toAdd v) ^ q` via `specialExpRingHom` to apply `map_add`.
    change ((ε α : ℤ) : A) * specialExpRingHom p A _ (hq _) (toAdd u + toAdd v) = _
    rw [map_add, mul_add]
    rfl

private theorem specialRootSubgroupAux_weylElement {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht) (p : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hq : ∀ α, (f.exponent α).toNat = 1 ∨ (f.exponent α).toNat = p)
    (ε : Fin t.numRoots → ℤˣ)
    (hε : ∀ α, ε ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = ε α)
    (α : Fin t.numRoots) (s : Aˣ) :
    specialRootSubgroupAux D p A f hq ε α (ofAdd (s : A)) *
        specialRootSubgroupAux D p A f hq ε
          ((t.simplyConnectedRootDatum ht).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        specialRootSubgroupAux D p A f hq ε α (ofAdd (s : A)) =
      D.weylElement (f.indexEquiv α) A
        (Units.map (Int.castRingHom A).toMonoidHom (ε α) *
          s ^ (f.exponent (f.indexEquiv α)).toNat) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  set q := (f.exponent (f.indexEquiv α)).toNat
  simp only [specialRootSubgroupAux, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hε,
    f.indexEquiv_reflectionPerm, f.exponent_reflectionPerm, weylElement_def,
    mul_inv_rev, ← inv_pow, ← map_inv, Int.units_inv_eq_self,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map]
  congr 4
  -- Express `(-s⁻¹) ^ q` via `specialExpRingHom` so `map_neg` extracts the minus sign.
  change ((ε α : ℤ) : A) * specialExpRingHom p A q (hq _) (-((s⁻¹ : Aˣ) : A)) = _
  rw [map_neg]
  -- Unfold `specialExpRingHom` back to `q`-th power before `ring`.
  change ((ε α : ℤ) : A) * -(((s⁻¹ : Aˣ) : A) ^ q) = -(((s⁻¹ : Aˣ) : A) ^ q * ((ε α : ℤ) : A))
  ring

private theorem specialRootSubgroupAux_comp_self {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht) (p : ℕ) (c : ℕ+) (hc : (c : ℕ) = p)
    (A : Type v) [CommRing A] [ExpChar A p]
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) c)
    (hq : ∀ α, (f.exponent α).toNat = 1 ∨ (f.exponent α).toNat = p)
    (ε : Fin t.numRoots → ℤˣ) (hε : ∀ α, ε (f.indexEquiv α) = ε α)
    (α : Fin t.numRoots) (u : A) :
    specialRootSubgroupAux D p A f hq ε (f.indexEquiv α)
        (ofAdd (((ε α : ℤ) : A) * u ^ (f.exponent (f.indexEquiv α)).toNat)) =
      D.frobenius p 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have hinv := RootPairingIsogeny.indexEquiv_apply_apply (t.simplyConnectedRootDatum ht) hf α
  have hprod : (f.exponent (f.indexEquiv α)).toNat * (f.exponent α).toNat = p := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_mul, Int.toNat_of_nonneg (f.exponent_pos _).le,
      Int.toNat_of_nonneg (f.exponent_pos _).le, mul_comm,
      RootPairingIsogeny.exponent_mul_exponent_indexEquiv (t.simplyConnectedRootDatum ht) hf α,
      ← hc]
  have hcast : (((ε α : ℤ) : A) * u ^ (f.exponent (f.indexEquiv α)).toNat) ^
      (f.exponent α).toNat = ((ε α : ℤ) : A) * u ^ p := by
    -- Express the outer power via `specialExpRingHom` to distribute over `*` and `Int.cast`.
    change specialExpRingHom p A (f.exponent α).toNat (hq α) _ = _
    rw [map_mul, map_intCast]
    -- Unfold `specialExpRingHom` back to exponentiation.
    change ((ε α : ℤ) : A) * (u ^ (f.exponent (f.indexEquiv α)).toNat) ^ (f.exponent α).toNat = _
    rw [← pow_mul, hprod]
  have hsq : ((ε α : ℤ) : A) * ((ε α : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  simp only [specialRootSubgroupAux, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hinv, hε,
    D.frobenius_rootSubgroupPoints, pow_one]
  rw [hcast, ← mul_assoc, hsq, one_mul]

/-! ## `B₂` in characteristic two -/

section B2

variable {ht : (B 2).Valid} (D : ChevalleyDatum (B 2) ht)
variable (A : Type v) [CommRing A] [ExpChar A 2]

private noncomputable def b2Iso (ht : (B 2).Valid) :
    RootPairingIsogeny ((B 2).simplyConnectedRootDatum ht) ((B 2).simplyConnectedRootDatum ht) :=
  congrIsogeny (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny

private theorem b2_toNat_exponent (α : Fin (B 2).numRoots) :
    ((b2Iso ht).exponent α).toNat = 1 ∨ ((b2Iso ht).exponent α).toNat = 2 := by
  have h : ∀ k : Fin (2 * 2 ^ 2), (b2SpecialIsogeny.exponent k).toNat = 1 ∨
      (b2SpecialIsogeny.exponent k).toNat = 2 := fun k => by
    rcases b2SpecialIsogenyExponent_eq_one_or_eq_two k with hk | hk <;>
      simp [b2SpecialIsogeny_exponent, hk]
  exact h α

/-- **The exceptional-isogeny root-subgroup map on a Chevalley datum of type `B₂`** over a
commutative ring of exponential characteristic `2`: sends `x_α(u)` to `x_{f(α)}(u ^ q(α))` where
`f` is `TauCeti.DynkinType.b2SpecialIsogeny`. -/
noncomputable def b2SpecialIsogenyRootSubgroup (α : Fin (B 2).numRoots) :
    Multiplicative A →* D.points A :=
  specialRootSubgroupAux D 2 A (b2Iso ht) b2_toNat_exponent (fun _ => 1) α

@[simp] theorem b2SpecialIsogenyRootSubgroup_ofAdd (α : Fin (B 2).numRoots) (u : A) :
    D.b2SpecialIsogenyRootSubgroup A α (ofAdd u) =
      D.rootSubgroupPoints (b2SpecialIsogeny.indexEquiv α) A
        (ofAdd (u ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat)) := by
  -- Unfold `b2SpecialIsogenyRootSubgroup` and `specialRootSubgroupAux` at `ε = 1`.
  change D.rootSubgroupPoints (b2SpecialIsogeny.indexEquiv α) A
    (ofAdd ((((1 : ℤˣ) : ℤ) : A) *
      u ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat)) = _
  rw [Units.val_one, Int.cast_one, one_mul]

@[simp] theorem b2SpecialIsogenyRootSubgroup_mem_elementarySubgroup
    (α : Fin (B 2).numRoots) (u : Multiplicative A) :
    D.b2SpecialIsogenyRootSubgroup A α u ∈ D.elementarySubgroup A := by
  rw [← ofAdd_toAdd u, b2SpecialIsogenyRootSubgroup_ofAdd]
  exact D.rootSubgroupPoints_mem_elementarySubgroup A _ _

private theorem b2_indexEquiv_simpleIndex (i : Fin (B 2).rank) :
    b2SpecialIsogeny.indexEquiv ((B 2).simpleIndex ht i) =
      (B 2).simpleIndex ht (lengthPermRankTwo i) :=
  (congrArg (⇑b2SpecialIsogeny.indexEquiv) (simpleIndex_B 2 ht i)).trans
    (((b2SpecialIsogeny_indexEquiv_apply _).trans
        (b2SpecialIsogenyIndexEquiv_typeBSimpleIndex i)).trans
      (simpleIndex_B 2 ht (lengthPermRankTwo i)).symm)

private theorem b2_exponent_simpleIndex (i : Fin (B 2).rank) :
    b2SpecialIsogeny.exponent ((B 2).simpleIndex ht i) = (B 2).rootLength i :=
  (congrArg b2SpecialIsogeny.exponent (simpleIndex_B 2 ht i)).trans
    ((b2SpecialIsogeny_exponent _).trans (b2SpecialIsogenyExponent_typeBSimpleIndex i))

/-- On a positive simple root of `B₂`, the exceptional-isogeny map exchanges the two nodes and
raises the parameter to `((B 2).rootLength (lengthPermRankTwo i)).toNat`. -/
theorem b2SpecialIsogenyRootSubgroup_simpleIndex (i : Fin (B 2).rank) (u : A) :
    D.b2SpecialIsogenyRootSubgroup A ((B 2).simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints ((B 2).simpleIndex ht (lengthPermRankTwo i)) A
        (ofAdd (u ^ ((B 2).rootLength (lengthPermRankTwo i)).toNat)) := by
  rw [b2SpecialIsogenyRootSubgroup_ofAdd, b2_indexEquiv_simpleIndex (ht := ht) i,
    b2_exponent_simpleIndex (ht := ht) (lengthPermRankTwo i)]

/-- On a negative simple root of `B₂`, the exceptional-isogeny map exchanges the two negative
simple roots with the same exponent `((B 2).rootLength (lengthPermRankTwo i)).toNat`. -/
theorem b2SpecialIsogenyRootSubgroup_reflectionPerm_simpleIndex (i : Fin (B 2).rank) (u : A) :
    D.b2SpecialIsogenyRootSubgroup A
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht (lengthPermRankTwo i))
          ((B 2).simpleIndex ht (lengthPermRankTwo i))) A
        (ofAdd (u ^ ((B 2).rootLength (lengthPermRankTwo i)).toNat)) := by
  have := (B 2).isReduced_simplyConnectedRootDatum ht
  have href := (b2Iso ht).indexEquiv_reflectionPerm
    ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)
  have hexp' := (b2Iso ht).exponent_reflectionPerm
    ((b2Iso ht).indexEquiv ((B 2).simpleIndex ht i))
    ((b2Iso ht).indexEquiv ((B 2).simpleIndex ht i))
  rw [b2SpecialIsogenyRootSubgroup_ofAdd]
  -- Fold `b2SpecialIsogeny` fields into `b2Iso ht` so `rw` matches the uniform root datum.
  change D.rootSubgroupPoints
      ((b2Iso ht).indexEquiv (((B 2).simplyConnectedRootDatum ht).reflectionPerm
        ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i))) A
      (ofAdd (u ^ ((b2Iso ht).exponent ((b2Iso ht).indexEquiv
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)))).toNat)) = _
  have hidx : (b2Iso ht).indexEquiv ((B 2).simpleIndex ht i) =
      (B 2).simpleIndex ht (lengthPermRankTwo i) := b2_indexEquiv_simpleIndex (ht := ht) i
  have hexp : (b2Iso ht).exponent ((B 2).simpleIndex ht (lengthPermRankTwo i)) =
      (B 2).rootLength (lengthPermRankTwo i) :=
    b2_exponent_simpleIndex (ht := ht) (lengthPermRankTwo i)
  rw [href, hexp', hidx, hexp]

/-- Steinberg's Weyl word in `b2SpecialIsogenyRootSubgroup` evaluates to `D.weylElement` at the
partner root. -/
theorem b2SpecialIsogenyRootSubgroup_weylElement (α : Fin (B 2).numRoots) (s : Aˣ) :
    D.b2SpecialIsogenyRootSubgroup A α (ofAdd (s : A)) *
        D.b2SpecialIsogenyRootSubgroup A
          (((B 2).simplyConnectedRootDatum ht).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        D.b2SpecialIsogenyRootSubgroup A α (ofAdd (s : A)) =
      D.weylElement (b2SpecialIsogeny.indexEquiv α) A
        (s ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat) := by
  have h := specialRootSubgroupAux_weylElement D 2 A (b2Iso ht) b2_toNat_exponent
    (fun _ => 1) (fun _ => rfl) α s
  rw [map_one, one_mul] at h
  exact h

/-- Applying `b2SpecialIsogenyRootSubgroup` twice gives the prime Frobenius endomorphism on every
root subgroup. -/
theorem b2SpecialIsogenyRootSubgroup_comp_self (α : Fin (B 2).numRoots) (u : A) :
    D.b2SpecialIsogenyRootSubgroup A (b2SpecialIsogeny.indexEquiv α)
        (ofAdd (u ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat)) =
      D.frobenius 2 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have h := specialRootSubgroupAux_comp_self D 2 2 rfl A (b2Iso ht)
    (congrIsogeny_mul_self (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny 2
      b2SpecialIsogeny_mul_self)
    b2_toNat_exponent (fun _ => 1) (fun _ => rfl) α u
  rw [Units.val_one, Int.cast_one, one_mul] at h
  exact h

end B2

/-! ## `F₄` in characteristic two -/

section F4

variable {ht : F4.Valid} (D : ChevalleyDatum F4 ht)
variable (A : Type v) [CommRing A] [ExpChar A 2]

private noncomputable def f4Iso (ht : F4.Valid) :
    RootPairingIsogeny (F4.simplyConnectedRootDatum ht) (F4.simplyConnectedRootDatum ht) :=
  congrIsogeny (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny

private theorem f4_toNat_exponent (α : Fin F4.numRoots) :
    ((f4Iso ht).exponent α).toNat = 1 ∨ ((f4Iso ht).exponent α).toNat = 2 := by
  have h : ∀ k : Fin 48, (f4SpecialIsogeny.exponent k).toNat = 1 ∨
      (f4SpecialIsogeny.exponent k).toNat = 2 := fun k => by
    rcases f4Length_eq_one_or_eq_two k with hk | hk <;> simp [f4SpecialIsogeny_exponent, hk]
  exact h α

/-- **The exceptional-isogeny root-subgroup map on a Chevalley datum of type `F₄`** over a
commutative ring of exponential characteristic `2`: sends `x_α(u)` to `x_{f(α)}(u ^ q(α))` where
`f` is `TauCeti.DynkinType.f4SpecialIsogeny`. -/
noncomputable def f4SpecialIsogenyRootSubgroup (α : Fin F4.numRoots) :
    Multiplicative A →* D.points A :=
  specialRootSubgroupAux D 2 A (f4Iso ht) f4_toNat_exponent (fun _ => 1) α

@[simp] theorem f4SpecialIsogenyRootSubgroup_ofAdd (α : Fin F4.numRoots) (u : A) :
    D.f4SpecialIsogenyRootSubgroup A α (ofAdd u) =
      D.rootSubgroupPoints (f4SpecialIsogeny.indexEquiv α) A
        (ofAdd (u ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat)) := by
  -- Unfold `f4SpecialIsogenyRootSubgroup` and `specialRootSubgroupAux` at `ε = 1`.
  change D.rootSubgroupPoints (f4SpecialIsogeny.indexEquiv α) A
    (ofAdd ((((1 : ℤˣ) : ℤ) : A) *
      u ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat)) = _
  rw [Units.val_one, Int.cast_one, one_mul]

@[simp] theorem f4SpecialIsogenyRootSubgroup_mem_elementarySubgroup
    (α : Fin F4.numRoots) (u : Multiplicative A) :
    D.f4SpecialIsogenyRootSubgroup A α u ∈ D.elementarySubgroup A := by
  rw [← ofAdd_toAdd u, f4SpecialIsogenyRootSubgroup_ofAdd]
  exact D.rootSubgroupPoints_mem_elementarySubgroup A _ _

private theorem f4_indexEquiv_simpleIndex (i : Fin F4.rank) :
    f4SpecialIsogeny.indexEquiv (F4.simpleIndex ht i) =
      F4.simpleIndex ht (lengthPermF4 i) :=
  (congrArg (⇑f4SpecialIsogeny.indexEquiv) (simpleIndex_F4 ht i)).trans
    (((f4SpecialIsogeny_indexEquiv_apply _).trans (f4SpecialIsogenyIndex_castAdd i)).trans
      (simpleIndex_F4 ht (lengthPermF4 i)).symm)

private theorem f4_exponent_simpleIndex (i : Fin F4.rank) :
    f4SpecialIsogeny.exponent (F4.simpleIndex ht i) = F4.rootLength i :=
  (congrArg f4SpecialIsogeny.exponent (simpleIndex_F4 ht i)).trans
    ((f4SpecialIsogeny_exponent _).trans (f4Length_castAdd i))

/-- On a positive simple root of `F₄`, the exceptional-isogeny map reverses the four Bourbaki
nodes and raises the parameter to `(F4.rootLength (lengthPermF4 i)).toNat`. -/
theorem f4SpecialIsogenyRootSubgroup_simpleIndex (i : Fin F4.rank) (u : A) :
    D.f4SpecialIsogenyRootSubgroup A (F4.simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints (F4.simpleIndex ht (lengthPermF4 i)) A
        (ofAdd (u ^ (F4.rootLength (lengthPermF4 i)).toNat)) := by
  rw [f4SpecialIsogenyRootSubgroup_ofAdd, f4_indexEquiv_simpleIndex (ht := ht) i,
    f4_exponent_simpleIndex (ht := ht) (lengthPermF4 i)]

/-- On a negative simple root of `F₄`, the exceptional-isogeny map reverses the four negative
simple roots with exponent `(F4.rootLength (lengthPermF4 i)).toNat`. -/
theorem f4SpecialIsogenyRootSubgroup_reflectionPerm_simpleIndex (i : Fin F4.rank) (u : A) :
    D.f4SpecialIsogenyRootSubgroup A
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht i) (F4.simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht (lengthPermF4 i)) (F4.simpleIndex ht (lengthPermF4 i))) A
        (ofAdd (u ^ (F4.rootLength (lengthPermF4 i)).toNat)) := by
  have := F4.isReduced_simplyConnectedRootDatum ht
  have href := (f4Iso ht).indexEquiv_reflectionPerm
    (F4.simpleIndex ht i) (F4.simpleIndex ht i)
  have hexp' := (f4Iso ht).exponent_reflectionPerm
    ((f4Iso ht).indexEquiv (F4.simpleIndex ht i))
    ((f4Iso ht).indexEquiv (F4.simpleIndex ht i))
  rw [f4SpecialIsogenyRootSubgroup_ofAdd]
  -- Fold `f4SpecialIsogeny` fields into `f4Iso ht` so `rw` matches `F4.simplyConnectedRootDatum`.
  change D.rootSubgroupPoints
      ((f4Iso ht).indexEquiv ((F4.simplyConnectedRootDatum ht).reflectionPerm
        (F4.simpleIndex ht i) (F4.simpleIndex ht i))) A
      (ofAdd (u ^ ((f4Iso ht).exponent ((f4Iso ht).indexEquiv
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht i) (F4.simpleIndex ht i)))).toNat)) = _
  have hidx : (f4Iso ht).indexEquiv (F4.simpleIndex ht i) =
      F4.simpleIndex ht (lengthPermF4 i) := f4_indexEquiv_simpleIndex (ht := ht) i
  have hexp : (f4Iso ht).exponent (F4.simpleIndex ht (lengthPermF4 i)) =
      F4.rootLength (lengthPermF4 i) := f4_exponent_simpleIndex (ht := ht) (lengthPermF4 i)
  rw [href, hexp', hidx, hexp]

/-- Steinberg's Weyl word in `f4SpecialIsogenyRootSubgroup` evaluates to `D.weylElement` at the
partner root. -/
theorem f4SpecialIsogenyRootSubgroup_weylElement (α : Fin F4.numRoots) (s : Aˣ) :
    D.f4SpecialIsogenyRootSubgroup A α (ofAdd (s : A)) *
        D.f4SpecialIsogenyRootSubgroup A
          ((F4.simplyConnectedRootDatum ht).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        D.f4SpecialIsogenyRootSubgroup A α (ofAdd (s : A)) =
      D.weylElement (f4SpecialIsogeny.indexEquiv α) A
        (s ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat) := by
  have h := specialRootSubgroupAux_weylElement D 2 A (f4Iso ht) f4_toNat_exponent
    (fun _ => 1) (fun _ => rfl) α s
  rw [map_one, one_mul] at h
  exact h

/-- Applying `f4SpecialIsogenyRootSubgroup` twice gives the prime Frobenius endomorphism on every
root subgroup. -/
theorem f4SpecialIsogenyRootSubgroup_comp_self (α : Fin F4.numRoots) (u : A) :
    D.f4SpecialIsogenyRootSubgroup A (f4SpecialIsogeny.indexEquiv α)
        (ofAdd (u ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat)) =
      D.frobenius 2 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have h := specialRootSubgroupAux_comp_self D 2 2 rfl A (f4Iso ht)
    (congrIsogeny_mul_self (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny 2
      f4SpecialIsogeny_mul_self)
    f4_toNat_exponent (fun _ => 1) (fun _ => rfl) α u
  rw [Units.val_one, Int.cast_one, one_mul] at h
  exact h

end F4

/-! ## `G₂` in characteristic three -/

section G2

variable {ht : G2.Valid} (D : ChevalleyDatum G2 ht)
variable (A : Type v) [CommRing A] [ExpChar A 3]

private noncomputable def g2Iso (ht : G2.Valid) :
    RootPairingIsogeny (G2.simplyConnectedRootDatum ht) (G2.simplyConnectedRootDatum ht) :=
  congrIsogeny (simplyConnectedRootDatum_G2 ht) g2SpecialIsogeny

private theorem g2_toNat_exponent (α : Fin G2.numRoots) :
    ((g2Iso ht).exponent α).toNat = 1 ∨ ((g2Iso ht).exponent α).toNat = 3 := by
  have h : ∀ k : Fin 12, (g2SpecialIsogeny.exponent k).toNat = 1 ∨
      (g2SpecialIsogeny.exponent k).toNat = 3 := fun k => by
    rcases g2Length_eq_one_or_eq_three k with hk | hk <;> simp [g2SpecialIsogeny_exponent, hk]
  exact h α

private theorem g2SpecialIsogenySign_reflectionPerm_self (α : Fin G2.numRoots) :
    g2SpecialIsogenySign ((G2.simplyConnectedRootDatum ht).reflectionPerm α α) =
      g2SpecialIsogenySign α := by
  have h : ∀ β : Fin 12, g2SimplyConnectedRootDatum.reflectionPerm β β = β + 6 := by
    intro β
    apply g2SimplyConnectedRootDatum.root.injective
    have hr := g2SimplyConnectedRootDatum.root_reflectionPerm β β
    rw [g2SimplyConnectedRootDatum.reflection_apply_self] at hr
    rw [hr, g2SimplyConnectedRootDatum_root, g2Root_eq_smul_add_smul β,
      g2Root_eq_smul_add_smul (β + 6), g2Coeff_add_six]
    simp [add_comm]
  rw [simplyConnectedRootDatum_G2]
  let β : Fin 12 := α
  exact (congrArg g2SpecialIsogenySign (h β)).trans (g2SpecialIsogenySign_add_six β)

private theorem g2_indexEquiv_simpleIndex (i : Fin G2.rank) :
    g2SpecialIsogeny.indexEquiv (G2.simpleIndex ht i) =
      G2.simpleIndex ht (lengthPermRankTwo i) := by
  have hcast (j : Fin 2) : (Fin.castAdd 10 j : Fin 12) = Fin.castLE (by omega) j := rfl
  exact (congrArg (⇑g2SpecialIsogeny.indexEquiv)
      ((simpleIndex_G2 ht i).trans (hcast i))).trans
    (((g2SpecialIsogeny_indexEquiv_apply _).trans (g2SpecialIsogenyIndex_castLE i)).trans
      (((hcast (lengthPermRankTwo i)).symm).trans
        (simpleIndex_G2 ht (lengthPermRankTwo i)).symm))

private theorem g2_exponent_simpleIndex (i : Fin G2.rank) :
    g2SpecialIsogeny.exponent (G2.simpleIndex ht i) = G2.rootLength i := by
  have hcast (j : Fin 2) : (Fin.castAdd 10 j : Fin 12) = Fin.castLE (by omega) j := rfl
  exact (congrArg g2SpecialIsogeny.exponent
      ((simpleIndex_G2 ht i).trans (hcast i))).trans
    ((g2SpecialIsogeny_exponent _).trans (g2Length_castLE i))

private theorem g2_sign_simpleIndex (i : Fin G2.rank) :
    g2SpecialIsogenySign (G2.simpleIndex ht i) = 1 := by
  have hcast (j : Fin 2) : (Fin.castAdd 10 j : Fin 12) = Fin.castLE (by omega) j := rfl
  exact (congrArg g2SpecialIsogenySign ((simpleIndex_G2 ht i).trans (hcast i))).trans
    (g2SpecialIsogenySign_castLE i)

/-- **The exceptional-isogeny root-subgroup map on a Chevalley datum of type `G₂`** over a
commutative ring of exponential characteristic `3`: sends `x_α(u)` to `x_{f(α)}(ε_α u ^ q(α))`
where `f` is `TauCeti.DynkinType.g2SpecialIsogeny` and `ε` is
`TauCeti.DynkinType.g2SpecialIsogenySign`. -/
noncomputable def g2SpecialIsogenyRootSubgroup (α : Fin G2.numRoots) :
    Multiplicative A →* D.points A :=
  specialRootSubgroupAux D 3 A (g2Iso ht) g2_toNat_exponent g2SpecialIsogenySign α

@[simp] theorem g2SpecialIsogenyRootSubgroup_ofAdd (α : Fin G2.numRoots) (u : A) :
    D.g2SpecialIsogenyRootSubgroup A α (ofAdd u) =
      D.rootSubgroupPoints (g2SpecialIsogeny.indexEquiv α) A
        (ofAdd (((g2SpecialIsogenySign α : ℤ) : A) *
          u ^ (g2SpecialIsogeny.exponent (g2SpecialIsogeny.indexEquiv α)).toNat)) := by
  rfl

@[simp] theorem g2SpecialIsogenyRootSubgroup_mem_elementarySubgroup
    (α : Fin G2.numRoots) (u : Multiplicative A) :
    D.g2SpecialIsogenyRootSubgroup A α u ∈ D.elementarySubgroup A := by
  rw [← ofAdd_toAdd u, g2SpecialIsogenyRootSubgroup_ofAdd]
  exact D.rootSubgroupPoints_mem_elementarySubgroup A _ _

/-- On a positive simple root of `G₂`, the exceptional-isogeny map exchanges the two Bourbaki
nodes with unit sign `1` and exponent `(G2.rootLength (lengthPermRankTwo i)).toNat`. -/
theorem g2SpecialIsogenyRootSubgroup_simpleIndex (i : Fin G2.rank) (u : A) :
    D.g2SpecialIsogenyRootSubgroup A (G2.simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints (G2.simpleIndex ht (lengthPermRankTwo i)) A
        (ofAdd (u ^ (G2.rootLength (lengthPermRankTwo i)).toNat)) := by
  rw [g2SpecialIsogenyRootSubgroup_ofAdd, g2_indexEquiv_simpleIndex (ht := ht) i,
    g2_exponent_simpleIndex (ht := ht) (lengthPermRankTwo i), g2_sign_simpleIndex (ht := ht) i]
  simp

/-- On a negative simple root of `G₂`, the exceptional-isogeny map exchanges the two negative
simple roots with unit sign `1` and exponent `(G2.rootLength (lengthPermRankTwo i)).toNat`. -/
theorem g2SpecialIsogenyRootSubgroup_reflectionPerm_simpleIndex (i : Fin G2.rank) (u : A) :
    D.g2SpecialIsogenyRootSubgroup A
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht i) (G2.simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht (lengthPermRankTwo i))
          (G2.simpleIndex ht (lengthPermRankTwo i))) A
        (ofAdd (u ^ (G2.rootLength (lengthPermRankTwo i)).toNat)) := by
  have := G2.isReduced_simplyConnectedRootDatum ht
  have href := (g2Iso ht).indexEquiv_reflectionPerm
    (G2.simpleIndex ht i) (G2.simpleIndex ht i)
  have hexp' := (g2Iso ht).exponent_reflectionPerm
    ((g2Iso ht).indexEquiv (G2.simpleIndex ht i))
    ((g2Iso ht).indexEquiv (G2.simpleIndex ht i))
  have hidx : (g2Iso ht).indexEquiv (G2.simpleIndex ht i) =
      G2.simpleIndex ht (lengthPermRankTwo i) := g2_indexEquiv_simpleIndex (ht := ht) i
  have hexp : (g2Iso ht).exponent (G2.simpleIndex ht (lengthPermRankTwo i)) =
      G2.rootLength (lengthPermRankTwo i) :=
    g2_exponent_simpleIndex (ht := ht) (lengthPermRankTwo i)
  rw [g2SpecialIsogenyRootSubgroup_ofAdd, g2SpecialIsogenySign_reflectionPerm_self (ht := ht),
    g2_sign_simpleIndex (ht := ht) i, Units.val_one, Int.cast_one, one_mul]
  -- Fold `g2SpecialIsogeny` fields into `g2Iso ht` so `rw` matches `G2.simplyConnectedRootDatum`.
  change D.rootSubgroupPoints
      ((g2Iso ht).indexEquiv ((G2.simplyConnectedRootDatum ht).reflectionPerm
        (G2.simpleIndex ht i) (G2.simpleIndex ht i))) A
      (ofAdd (u ^ ((g2Iso ht).exponent ((g2Iso ht).indexEquiv
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht i) (G2.simpleIndex ht i)))).toNat)) = _
  rw [href, hexp', hidx, hexp]

/-- Steinberg's Weyl word in `g2SpecialIsogenyRootSubgroup` evaluates to `D.weylElement` at the
partner root, with unit parameter signed by `TauCeti.DynkinType.g2SpecialIsogenySign`. -/
theorem g2SpecialIsogenyRootSubgroup_weylElement (α : Fin G2.numRoots) (s : Aˣ) :
    D.g2SpecialIsogenyRootSubgroup A α (ofAdd (s : A)) *
        D.g2SpecialIsogenyRootSubgroup A
          ((G2.simplyConnectedRootDatum ht).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        D.g2SpecialIsogenyRootSubgroup A α (ofAdd (s : A)) =
      D.weylElement (g2SpecialIsogeny.indexEquiv α) A
        (Units.map (Int.castRingHom A).toMonoidHom (g2SpecialIsogenySign α) *
          s ^ (g2SpecialIsogeny.exponent (g2SpecialIsogeny.indexEquiv α)).toNat) :=
  specialRootSubgroupAux_weylElement D 3 A (g2Iso ht) g2_toNat_exponent
    g2SpecialIsogenySign (g2SpecialIsogenySign_reflectionPerm_self (ht := ht)) α s

/-- Applying `g2SpecialIsogenyRootSubgroup` twice gives the prime Frobenius endomorphism on every
root subgroup: the two `G₂` signs on each special-isogeny orbit coincide and cancel. -/
theorem g2SpecialIsogenyRootSubgroup_comp_self (α : Fin G2.numRoots) (u : A) :
    D.g2SpecialIsogenyRootSubgroup A (g2SpecialIsogeny.indexEquiv α)
        (ofAdd (((g2SpecialIsogenySign α : ℤ) : A) *
          u ^ (g2SpecialIsogeny.exponent (g2SpecialIsogeny.indexEquiv α)).toNat)) =
      D.frobenius 3 1 A (D.rootSubgroupPoints α A (ofAdd u)) :=
  specialRootSubgroupAux_comp_self D 3 3 rfl A (g2Iso ht)
    (congrIsogeny_mul_self (simplyConnectedRootDatum_G2 ht) g2SpecialIsogeny 3
      g2SpecialIsogeny_mul_self)
    g2_toNat_exponent g2SpecialIsogenySign (fun β => by
      have h : ∀ k : Fin 12, g2SpecialIsogenySign (g2SpecialIsogeny.indexEquiv k) =
          g2SpecialIsogenySign k := fun k => by
        rw [g2SpecialIsogeny_indexEquiv_apply, g2SpecialIsogenySign_g2SpecialIsogenyIndex]
      exact h β) α u

end G2

end ChevalleyDatum

end TauCeti.DynkinType
