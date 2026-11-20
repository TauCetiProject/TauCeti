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

Over `[ExpChar A 2]` (`B₂`, `F₄`) and `[ExpChar A 3]` (`G₂`), Steinberg's exceptional endomorphism
maps `x_α(u) ↦ x_{f(α)}(ε_α u ^ q(α))` (`b2SpecialIsogenyRootSubgroup`,
`f4SpecialIsogenyRootSubgroup`, `g2SpecialIsogenyRootSubgroup`, with signs `g2SpecialIsogenySign`),
intertwining signed simple roots and Weyl words and squaring to `D.frobenius p 1 A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Ch. 10; R. W. Carter, *Simple Groups*, §§12.3–12.4.
-/

public section

namespace TauCeti.DynkinType

/-- **The root-subgroup sign table of the `G₂` exceptional isogeny** in characteristic three,
indexed by `g2Root`: `+1` on `0, 1, 3, 5, 6, 7, 9, 11` and `-1` on `2, 4, 8, 10`. -/
def g2SpecialIsogenySign : Fin 12 → ℤˣ := ![1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1]

/-- The explicit entries of `TauCeti.DynkinType.g2SpecialIsogenySign`. -/
theorem g2SpecialIsogenySign_def :
    g2SpecialIsogenySign = ![1, 1, -1, 1, -1, 1, 1, 1, -1, 1, -1, 1] := (rfl)

/-- Every root of `G₂` and its negative carry the same exceptional-isogeny sign. -/
@[simp] theorem g2SpecialIsogenySign_add_six (i : Fin 12) :
    g2SpecialIsogenySign (i + 6) = g2SpecialIsogenySign i := by decide +revert

/-- The `G₂` exceptional-isogeny sign is invariant under the special root permutation. -/
@[simp] theorem g2SpecialIsogenySign_g2SpecialIsogenyIndex (i : Fin 12) :
    g2SpecialIsogenySign (g2SpecialIsogenyIndex i) = g2SpecialIsogenySign i := by
  rw [g2SpecialIsogenyIndex_def]; decide +revert

/-- On the two positive simple roots of `G₂`, the exceptional-isogeny sign is `1`. -/
@[simp] theorem g2SpecialIsogenySign_castLE (i : Fin 2) :
    g2SpecialIsogenySign (Fin.castLE (by omega) i) = 1 := by fin_cases i <;> decide

namespace ChevalleyDatum

open Multiplicative

universe v

private structure SpecialPkg (t : DynkinType) (ht : t.Valid) (p : ℕ) where
  iso : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht)
  scale : ℕ+
  scale_eq : (scale : ℕ) = p
  mul_self : iso * iso = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) scale
  hq : ∀ α, (iso.exponent α).toNat = 1 ∨ (iso.exponent α).toNat = p
  ε : Fin t.numRoots → ℤˣ
  ε_refl : ∀ α, ε ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = ε α
  ε_idx : ∀ α, ε (iso.indexEquiv α) = ε α
  σ : Equiv.Perm (Fin t.rank)
  idx_simple : ∀ i, iso.indexEquiv (t.simpleIndex ht i) = t.simpleIndex ht (σ i)
  exp_simple : ∀ i, iso.exponent (t.simpleIndex ht i) = t.rootLength i
  ε_simple : ∀ i, ε (t.simpleIndex ht i) = 1

section PkgAPI

variable {t : DynkinType} {ht : t.Valid} {p : ℕ}
  (D : ChevalleyDatum t ht) (A : Type v) [CommRing A] [ExpChar A p]

local notation "Φt" => t.simplyConnectedRootDatum ht

private noncomputable def SpecialPkg.hom (S : SpecialPkg t ht p) (α : Fin t.numRoots) :
    Multiplicative A →* D.points A where
  toFun u := D.rootSubgroupPoints (S.iso.indexEquiv α) A
    (ofAdd (((S.ε α : ℤ) : A) * toAdd u ^ (S.iso.exponent (S.iso.indexEquiv α)).toNat))
  map_one' := by
    have hpos : (S.iso.exponent (S.iso.indexEquiv α)).toNat ≠ 0 := by
      have := S.iso.exponent_pos (S.iso.indexEquiv α); omega
    rw [toAdd_one, zero_pow hpos, mul_zero, ofAdd_zero, map_one]
  map_mul' u v := by
    simp only [toAdd_mul, ← map_mul, ← ofAdd_add]
    congr 2
    rcases S.hq (S.iso.indexEquiv α) with h | h <;> rw [h]
    · rw [pow_one, pow_one, pow_one, mul_add]
    · rw [← _root_.frobenius_def, map_add, _root_.frobenius_def, _root_.frobenius_def, mul_add]

private theorem SpecialPkg.simpleIndex (S : SpecialPkg t ht p) (i : Fin t.rank) (u : A) :
    S.hom D A (t.simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints (t.simpleIndex ht (S.σ i)) A
        (ofAdd (u ^ (t.rootLength (S.σ i)).toNat)) := by
  simp [SpecialPkg.hom, S.idx_simple, S.exp_simple, S.ε_simple]

private theorem SpecialPkg.reflectionPerm_simpleIndex (S : SpecialPkg t ht p) (i : Fin t.rank)
    (u : A) :
    S.hom D A ((Φt).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints
        ((Φt).reflectionPerm (t.simpleIndex ht (S.σ i)) (t.simpleIndex ht (S.σ i))) A
        (ofAdd (u ^ (t.rootLength (S.σ i)).toNat)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  simp [SpecialPkg.hom, S.ε_refl, S.ε_simple, S.iso.indexEquiv_reflectionPerm,
    S.iso.exponent_reflectionPerm, S.idx_simple, S.exp_simple]

private theorem SpecialPkg.weylElement (S : SpecialPkg t ht p) (α : Fin t.numRoots) (s : Aˣ) :
    S.hom D A α (ofAdd (s : A)) * S.hom D A ((Φt).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        S.hom D A α (ofAdd (s : A)) =
      D.weylElement (S.iso.indexEquiv α) A
        (Units.map (Int.castRingHom A).toMonoidHom (S.ε α) *
          s ^ (S.iso.exponent (S.iso.indexEquiv α)).toNat) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hε : ((Units.map (Int.castRingHom A).toMonoidHom (S.ε α) : Aˣ) : A) = (S.ε α : ℤ) := rfl
  simp only [SpecialPkg.hom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, S.ε_refl,
    S.iso.indexEquiv_reflectionPerm, S.iso.exponent_reflectionPerm, weylElement_def,
    mul_inv_rev, ← inv_pow, ← map_inv, Int.units_inv_eq_self, Units.val_mul,
    Units.val_pow_eq_pow_val, hε]
  congr 4
  rcases S.hq (S.iso.indexEquiv α) with h | h <;> rw [h]
  · ring
  · rw [← _root_.frobenius_def, map_neg, _root_.frobenius_def]; ring

private theorem SpecialPkg.comp_self (S : SpecialPkg t ht p) (α : Fin t.numRoots) (u : A) :
    S.hom D A (S.iso.indexEquiv α)
        (ofAdd (((S.ε α : ℤ) : A) * u ^ (S.iso.exponent (S.iso.indexEquiv α)).toNat)) =
      D.frobenius p 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have hinv := RootPairingIsogeny.indexEquiv_apply_apply _ S.mul_self α
  have hprod : (S.iso.exponent (S.iso.indexEquiv α)).toNat * (S.iso.exponent α).toNat = p :=
    Int.ofNat_inj.mp <| by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (S.iso.exponent_pos _).le,
        Int.toNat_of_nonneg (S.iso.exponent_pos _).le, mul_comm,
        RootPairingIsogeny.exponent_mul_exponent_indexEquiv _ S.mul_self α, S.scale_eq]
  have hcast : (((S.ε α : ℤ) : A) * u ^ (S.iso.exponent (S.iso.indexEquiv α)).toNat) ^
      (S.iso.exponent α).toNat = ((S.ε α : ℤ) : A) * u ^ p := by
    rcases S.hq α with h | h
    · rw [h, pow_one]; rw [h, mul_one] at hprod; rw [hprod]
    · rw [h] at hprod ⊢
      rw [← _root_.frobenius_def, map_mul, map_intCast, _root_.frobenius_def, ← pow_mul, hprod]
  have hsq : ((S.ε α : ℤ) : A) * ((S.ε α : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  simp only [SpecialPkg.hom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hinv, S.ε_idx,
    D.frobenius_rootSubgroupPoints, pow_one]
  rw [hcast, ← mul_assoc, hsq, one_mul]

private theorem SpecialPkg.mem_elementarySubgroup (S : SpecialPkg t ht p) (α : Fin t.numRoots)
    (u : Multiplicative A) : S.hom D A α u ∈ D.elementarySubgroup A := by
  rw [← ofAdd_toAdd u]; exact D.rootSubgroupPoints_mem_elementarySubgroup A _ _

end PkgAPI

/-! ## `B₂` in characteristic two -/

section B2

private noncomputable def b2Pkg (ht : (B 2).Valid) : SpecialPkg (B 2) ht 2 where
  iso := b2SpecialIsogeny.ofEq (simplyConnectedRootDatum_B 2 ht)
  scale := 2; scale_eq := rfl
  mul_self := RootPairingIsogeny.ofEq_mul_self _ (simplyConnectedRootDatum_B 2 ht)
    b2SpecialIsogeny_mul_self
  hq α :=
    (RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny α).symm ▸
      by rcases b2SpecialIsogeny_exponent_eq_one_or_eq_two α with hk | hk <;> simp [hk]
  ε _ := 1; ε_refl _ := rfl; ε_idx _ := rfl; σ := lengthPermRankTwo; ε_simple _ := rfl
  idx_simple i :=
    (congrArg (· ((B 2).simpleIndex ht i))
      (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_B 2 ht)
        b2SpecialIsogeny)).trans (b2SpecialIsogeny_indexEquiv_simpleIndex ht i)
  exp_simple i :=
    (RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny _).trans
      ((congrArg b2SpecialIsogeny.exponent (simpleIndex_B 2 ht i)).trans
        ((b2SpecialIsogeny_exponent _).trans (b2SpecialIsogenyExponent_typeBSimpleIndex i)))

private theorem b2Pkg_indexEquiv (ht : (B 2).Valid) (α : Fin (B 2).numRoots) :
    (b2Pkg ht).iso.indexEquiv α = b2SpecialIsogeny.indexEquiv α :=
  congrArg (· α) (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_B 2 ht)
    b2SpecialIsogeny)

private theorem b2Pkg_exponent (ht : (B 2).Valid) (α : Fin (B 2).numRoots) :
    (b2Pkg ht).iso.exponent α = b2SpecialIsogeny.exponent α :=
  RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny α

private theorem b2Pkg_ε (ht : (B 2).Valid) (α : Fin (B 2).numRoots) : (b2Pkg ht).ε α = 1 := rfl

variable {ht : (B 2).Valid} (D : ChevalleyDatum (B 2) ht) (A : Type v) [CommRing A] [ExpChar A 2]

local notation "ΦB2" => DynkinType.simplyConnectedRootDatum (B 2) ht

/-- **The exceptional-isogeny root-subgroup map on a Chevalley datum of type `B₂`**, sending
`α ↦ (u ↦ x_{indexEquiv α}(u ^ exponent (indexEquiv α)))` (with sign `ε = 1`). -/
noncomputable def b2SpecialIsogenyRootSubgroup (α : Fin (B 2).numRoots) :
    Multiplicative A →* D.points A := (b2Pkg ht).hom D A α

local notation "xB2" => D.b2SpecialIsogenyRootSubgroup A

/-- Explicit root-subgroup formula for `b2SpecialIsogenyRootSubgroup` on additive parameters. -/
@[simp] theorem b2SpecialIsogenyRootSubgroup_ofAdd (α : Fin (B 2).numRoots) (u : A) :
    xB2 α (ofAdd u) = D.rootSubgroupPoints (b2SpecialIsogeny.indexEquiv α) A
      (ofAdd (u ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat)) := by
  dsimp only [b2SpecialIsogenyRootSubgroup, SpecialPkg.hom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [toAdd_ofAdd, b2Pkg_exponent, b2Pkg_indexEquiv, b2Pkg_ε, Units.val_one, Int.cast_one, one_mul]

/-- Every image of `b2SpecialIsogenyRootSubgroup` lies in the elementary subgroup. -/
@[simp] theorem b2SpecialIsogenyRootSubgroup_mem_elementarySubgroup
    (α : Fin (B 2).numRoots) (u : Multiplicative A) : xB2 α u ∈ D.elementarySubgroup A :=
  (b2Pkg ht).mem_elementarySubgroup D A α u

/-- On a positive simple root of `B₂`, the exceptional-isogeny map exchanges the two nodes. -/
theorem b2SpecialIsogenyRootSubgroup_simpleIndex (i : Fin (B 2).rank) (u : A) :
    xB2 ((B 2).simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints ((B 2).simpleIndex ht (lengthPermRankTwo i)) A
        (ofAdd (u ^ ((B 2).rootLength (lengthPermRankTwo i)).toNat)) :=
  (b2Pkg ht).simpleIndex D A i u

/-- On a negative simple root of `B₂`, the exceptional-isogeny map swaps the negative nodes. -/
theorem b2SpecialIsogenyRootSubgroup_reflectionPerm_simpleIndex (i : Fin (B 2).rank) (u : A) :
    xB2 ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints ((ΦB2).reflectionPerm ((B 2).simpleIndex ht (lengthPermRankTwo i))
        ((B 2).simpleIndex ht (lengthPermRankTwo i))) A
        (ofAdd (u ^ ((B 2).rootLength (lengthPermRankTwo i)).toNat)) :=
  (b2Pkg ht).reflectionPerm_simpleIndex D A i u

/-- Steinberg's Weyl word in `b2SpecialIsogenyRootSubgroup` gives `D.weylElement` at the partner. -/
theorem b2SpecialIsogenyRootSubgroup_weylElement (α : Fin (B 2).numRoots) (s : Aˣ) :
    xB2 α (ofAdd (s : A)) * xB2 ((ΦB2).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        xB2 α (ofAdd (s : A)) =
      D.weylElement (b2SpecialIsogeny.indexEquiv α) A
        (s ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat) := by
  have h := (b2Pkg ht).weylElement D A α s
  rw [b2Pkg_exponent, b2Pkg_indexEquiv, b2Pkg_ε, map_one, one_mul] at h
  exact h

/-- Applying `b2SpecialIsogenyRootSubgroup` twice gives `D.frobenius 2 1 A` on root subgroups. -/
theorem b2SpecialIsogenyRootSubgroup_comp_self (α : Fin (B 2).numRoots) (u : A) :
    xB2 (b2SpecialIsogeny.indexEquiv α)
        (ofAdd (u ^ (b2SpecialIsogeny.exponent (b2SpecialIsogeny.indexEquiv α)).toNat)) =
      D.frobenius 2 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have h := (b2Pkg ht).comp_self D A α u
  rw [b2Pkg_exponent, b2Pkg_indexEquiv, b2Pkg_ε, Units.val_one, Int.cast_one, one_mul] at h
  exact h

end B2

/-! ## `F₄` in characteristic two -/

section F4

private noncomputable def f4Pkg (ht : F4.Valid) : SpecialPkg F4 ht 2 where
  iso := f4SpecialIsogeny.ofEq (simplyConnectedRootDatum_F4 ht)
  scale := 2; scale_eq := rfl
  mul_self := RootPairingIsogeny.ofEq_mul_self _ (simplyConnectedRootDatum_F4 ht)
    f4SpecialIsogeny_mul_self
  hq α :=
    (RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny α).symm ▸
      by rcases f4SpecialIsogeny_exponent_eq_one_or_eq_two α with hk | hk <;> simp [hk]
  ε _ := 1; ε_refl _ := rfl; ε_idx _ := rfl; σ := lengthPermF4; ε_simple _ := rfl
  idx_simple i :=
    (congrArg (· (F4.simpleIndex ht i))
      (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_F4 ht)
        f4SpecialIsogeny)).trans (f4SpecialIsogeny_indexEquiv_simpleIndex ht i)
  exp_simple i :=
    (RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny _).trans
      ((congrArg f4SpecialIsogeny.exponent (simpleIndex_F4 ht i)).trans
        ((f4SpecialIsogeny_exponent _).trans (f4Length_castAdd i)))

private theorem f4Pkg_indexEquiv (ht : F4.Valid) (α : Fin F4.numRoots) :
    (f4Pkg ht).iso.indexEquiv α = f4SpecialIsogeny.indexEquiv α :=
  congrArg (· α) (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_F4 ht)
    f4SpecialIsogeny)

private theorem f4Pkg_exponent (ht : F4.Valid) (α : Fin F4.numRoots) :
    (f4Pkg ht).iso.exponent α = f4SpecialIsogeny.exponent α :=
  RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny α

private theorem f4Pkg_ε (ht : F4.Valid) (α : Fin F4.numRoots) : (f4Pkg ht).ε α = 1 := rfl

variable {ht : F4.Valid} (D : ChevalleyDatum F4 ht) (A : Type v) [CommRing A] [ExpChar A 2]

local notation "ΦF4" => F4.simplyConnectedRootDatum ht

/-- **The exceptional-isogeny root-subgroup map on a Chevalley datum of type `F₄`**, sending
`α ↦ (u ↦ x_{indexEquiv α}(u ^ exponent (indexEquiv α)))` (with sign `ε = 1`). -/
noncomputable def f4SpecialIsogenyRootSubgroup (α : Fin F4.numRoots) :
    Multiplicative A →* D.points A := (f4Pkg ht).hom D A α

local notation "xF4" => D.f4SpecialIsogenyRootSubgroup A

/-- Explicit root-subgroup formula for `f4SpecialIsogenyRootSubgroup` on additive parameters. -/
@[simp] theorem f4SpecialIsogenyRootSubgroup_ofAdd (α : Fin F4.numRoots) (u : A) :
    xF4 α (ofAdd u) = D.rootSubgroupPoints (f4SpecialIsogeny.indexEquiv α) A
      (ofAdd (u ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat)) := by
  dsimp only [f4SpecialIsogenyRootSubgroup, SpecialPkg.hom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [toAdd_ofAdd, f4Pkg_exponent, f4Pkg_indexEquiv, f4Pkg_ε, Units.val_one, Int.cast_one, one_mul]

/-- Every image of `f4SpecialIsogenyRootSubgroup` lies in the elementary subgroup. -/
@[simp] theorem f4SpecialIsogenyRootSubgroup_mem_elementarySubgroup
    (α : Fin F4.numRoots) (u : Multiplicative A) : xF4 α u ∈ D.elementarySubgroup A :=
  (f4Pkg ht).mem_elementarySubgroup D A α u

/-- On a positive simple root of `F₄`, the exceptional-isogeny map reverses the four nodes. -/
theorem f4SpecialIsogenyRootSubgroup_simpleIndex (i : Fin F4.rank) (u : A) :
    xF4 (F4.simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints (F4.simpleIndex ht (lengthPermF4 i)) A
        (ofAdd (u ^ (F4.rootLength (lengthPermF4 i)).toNat)) :=
  (f4Pkg ht).simpleIndex D A i u

/-- On a negative simple root of `F₄`, the exceptional-isogeny map reverses the negative nodes. -/
theorem f4SpecialIsogenyRootSubgroup_reflectionPerm_simpleIndex (i : Fin F4.rank) (u : A) :
    xF4 ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints ((ΦF4).reflectionPerm (F4.simpleIndex ht (lengthPermF4 i))
        (F4.simpleIndex ht (lengthPermF4 i))) A
        (ofAdd (u ^ (F4.rootLength (lengthPermF4 i)).toNat)) :=
  (f4Pkg ht).reflectionPerm_simpleIndex D A i u

/-- Steinberg's Weyl word in `f4SpecialIsogenyRootSubgroup` gives `D.weylElement` at the partner. -/
theorem f4SpecialIsogenyRootSubgroup_weylElement (α : Fin F4.numRoots) (s : Aˣ) :
    xF4 α (ofAdd (s : A)) * xF4 ((ΦF4).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        xF4 α (ofAdd (s : A)) =
      D.weylElement (f4SpecialIsogeny.indexEquiv α) A
        (s ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat) := by
  have h := (f4Pkg ht).weylElement D A α s
  rw [f4Pkg_exponent, f4Pkg_indexEquiv, f4Pkg_ε, map_one, one_mul] at h
  exact h

/-- Applying `f4SpecialIsogenyRootSubgroup` twice gives `D.frobenius 2 1 A` on root subgroups. -/
theorem f4SpecialIsogenyRootSubgroup_comp_self (α : Fin F4.numRoots) (u : A) :
    xF4 (f4SpecialIsogeny.indexEquiv α)
        (ofAdd (u ^ (f4SpecialIsogeny.exponent (f4SpecialIsogeny.indexEquiv α)).toNat)) =
      D.frobenius 2 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have h := (f4Pkg ht).comp_self D A α u
  rw [f4Pkg_exponent, f4Pkg_indexEquiv, f4Pkg_ε, Units.val_one, Int.cast_one, one_mul] at h
  exact h

end F4

/-! ## `G₂` in characteristic three -/

section G2

private noncomputable def g2Pkg (ht : G2.Valid) : SpecialPkg G2 ht 3 where
  iso := g2SpecialIsogeny.ofEq (simplyConnectedRootDatum_G2 ht)
  scale := 3; scale_eq := rfl
  mul_self := RootPairingIsogeny.ofEq_mul_self _ (simplyConnectedRootDatum_G2 ht)
    g2SpecialIsogeny_mul_self
  hq α :=
    (RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_G2 ht) g2SpecialIsogeny α).symm ▸
      by rcases g2SpecialIsogeny_exponent_eq_one_or_eq_three α with hk | hk <;> simp [hk]
  ε := g2SpecialIsogenySign; σ := lengthPermRankTwo
  ε_refl α := (congrArg g2SpecialIsogenySign (reflectionPerm_self_G2 ht α)).trans
    (g2SpecialIsogenySign_add_six α)
  ε_idx α :=
    (congrArg g2SpecialIsogenySign
      ((congrArg (· α) (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_G2 ht)
        g2SpecialIsogeny)).trans (g2SpecialIsogeny_indexEquiv_apply α))).trans
      (g2SpecialIsogenySign_g2SpecialIsogenyIndex α)
  idx_simple i :=
    (congrArg (· (G2.simpleIndex ht i))
      (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_G2 ht)
        g2SpecialIsogeny)).trans (g2SpecialIsogeny_indexEquiv_simpleIndex ht i)
  exp_simple i :=
    (RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_G2 ht) g2SpecialIsogeny _).trans
      ((congrArg g2SpecialIsogeny.exponent (simpleIndex_G2 ht i)).trans
        ((g2SpecialIsogeny_exponent _).trans (g2Length_castLE i)))
  ε_simple i := (congrArg g2SpecialIsogenySign (simpleIndex_G2 ht i)).trans
    (g2SpecialIsogenySign_castLE i)

private theorem g2Pkg_indexEquiv (ht : G2.Valid) (α : Fin G2.numRoots) :
    (g2Pkg ht).iso.indexEquiv α = g2SpecialIsogeny.indexEquiv α :=
  congrArg (· α) (RootPairingIsogeny.ofEq_indexEquiv (simplyConnectedRootDatum_G2 ht)
    g2SpecialIsogeny)

private theorem g2Pkg_exponent (ht : G2.Valid) (α : Fin G2.numRoots) :
    (g2Pkg ht).iso.exponent α = g2SpecialIsogeny.exponent α :=
  RootPairingIsogeny.ofEq_exponent (simplyConnectedRootDatum_G2 ht) g2SpecialIsogeny α

private theorem g2Pkg_ε (ht : G2.Valid) (α : Fin G2.numRoots) :
    (g2Pkg ht).ε α = g2SpecialIsogenySign α := rfl

variable {ht : G2.Valid} (D : ChevalleyDatum G2 ht) (A : Type v) [CommRing A] [ExpChar A 3]

local notation "ΦG2" => G2.simplyConnectedRootDatum ht

/-- **The exceptional-isogeny root-subgroup map on a Chevalley datum of type `G₂`**, sending
`α ↦ (u ↦ x_{indexEquiv α}(g2SpecialIsogenySign α · u ^ exponent (indexEquiv α)))`. -/
noncomputable def g2SpecialIsogenyRootSubgroup (α : Fin G2.numRoots) :
    Multiplicative A →* D.points A := (g2Pkg ht).hom D A α

local notation "xG2" => D.g2SpecialIsogenyRootSubgroup A

/-- Explicit signed root-subgroup formula for `g2SpecialIsogenyRootSubgroup` on additive
parameters. -/
@[simp] theorem g2SpecialIsogenyRootSubgroup_ofAdd (α : Fin G2.numRoots) (u : A) :
    xG2 α (ofAdd u) = D.rootSubgroupPoints (g2SpecialIsogeny.indexEquiv α) A
      (ofAdd (((g2SpecialIsogenySign α : ℤ) : A) *
        u ^ (g2SpecialIsogeny.exponent (g2SpecialIsogeny.indexEquiv α)).toNat)) := by
  dsimp only [g2SpecialIsogenyRootSubgroup, SpecialPkg.hom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [toAdd_ofAdd, g2Pkg_exponent, g2Pkg_indexEquiv, g2Pkg_ε]

/-- Every image of `g2SpecialIsogenyRootSubgroup` lies in the elementary subgroup. -/
@[simp] theorem g2SpecialIsogenyRootSubgroup_mem_elementarySubgroup
    (α : Fin G2.numRoots) (u : Multiplicative A) : xG2 α u ∈ D.elementarySubgroup A :=
  (g2Pkg ht).mem_elementarySubgroup D A α u

/-- On a positive simple root of `G₂`, the exceptional-isogeny map exchanges the two nodes. -/
theorem g2SpecialIsogenyRootSubgroup_simpleIndex (i : Fin G2.rank) (u : A) :
    xG2 (G2.simpleIndex ht i) (ofAdd u) =
      D.rootSubgroupPoints (G2.simpleIndex ht (lengthPermRankTwo i)) A
        (ofAdd (u ^ (G2.rootLength (lengthPermRankTwo i)).toNat)) :=
  (g2Pkg ht).simpleIndex D A i u

/-- On a negative simple root of `G₂`, the exceptional-isogeny map swaps the negative nodes. -/
theorem g2SpecialIsogenyRootSubgroup_reflectionPerm_simpleIndex (i : Fin G2.rank) (u : A) :
    xG2 ((ΦG2).reflectionPerm (G2.simpleIndex ht i) (G2.simpleIndex ht i)) (ofAdd u) =
      D.rootSubgroupPoints ((ΦG2).reflectionPerm (G2.simpleIndex ht (lengthPermRankTwo i))
        (G2.simpleIndex ht (lengthPermRankTwo i))) A
        (ofAdd (u ^ (G2.rootLength (lengthPermRankTwo i)).toNat)) :=
  (g2Pkg ht).reflectionPerm_simpleIndex D A i u

/-- Steinberg's Weyl word in `g2SpecialIsogenyRootSubgroup` gives the signed `D.weylElement`. -/
theorem g2SpecialIsogenyRootSubgroup_weylElement (α : Fin G2.numRoots) (s : Aˣ) :
    xG2 α (ofAdd (s : A)) * xG2 ((ΦG2).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        xG2 α (ofAdd (s : A)) =
      D.weylElement (g2SpecialIsogeny.indexEquiv α) A
        (Units.map (Int.castRingHom A).toMonoidHom (g2SpecialIsogenySign α) *
          s ^ (g2SpecialIsogeny.exponent (g2SpecialIsogeny.indexEquiv α)).toNat) := by
  have h := (g2Pkg ht).weylElement D A α s
  rw [g2Pkg_exponent, g2Pkg_indexEquiv, g2Pkg_ε] at h
  exact h

/-- Applying `g2SpecialIsogenyRootSubgroup` twice gives `D.frobenius 3 1 A` on root subgroups. -/
theorem g2SpecialIsogenyRootSubgroup_comp_self (α : Fin G2.numRoots) (u : A) :
    xG2 (g2SpecialIsogeny.indexEquiv α) (ofAdd (((g2SpecialIsogenySign α : ℤ) : A) *
        u ^ (g2SpecialIsogeny.exponent (g2SpecialIsogeny.indexEquiv α)).toNat)) =
      D.frobenius 3 1 A (D.rootSubgroupPoints α A (ofAdd u)) := by
  have h := (g2Pkg ht).comp_self D A α u
  rw [g2Pkg_exponent, g2Pkg_indexEquiv, g2Pkg_ε] at h
  exact h

end G2

end ChevalleyDatum

end TauCeti.DynkinType
