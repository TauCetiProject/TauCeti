/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.Transfer
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Conjugation
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Refinement
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
import TauCeti.GroupTheory.Transfer

/-!
# Maps between abelianized Galois groups of finite normal layers

The functoriality of the Artin map compares operations on formation levels with three canonical
homomorphisms between the abelianizations of finite-layer Galois groups, and with the equivalence
induced directly by conjugation. This file constructs the homomorphisms and proves coherence laws
for the conjugation equivalence obtained from Mathlib's `MulEquiv.abelianizationCongr`.

For a restriction of layers `K/E` inside `K/F`, the inclusion

```text
Gal(K/E) ↪ Gal(K/F)
```

induces `LayerRestriction.inclusionHom` on abelianizations. In the other direction,
`LayerRestriction.transferHom` is the group-theoretic transfer (Verlagerung). It is formed by
identifying `Gal(K/E)` with the range of the inclusion, applying Mathlib's `MonoidHom.transfer`,
and then using the universal property of the abelianization. The index of that range is the
relative degree `[E : F]`. Like the inclusion, the transfer is functorial along a tower of
restrictions, because the group-theoretic transfer is transitive (`MonoidHom.transfer_transfer`).

For a refinement `L/F` of `K/F`, the quotient map

```text
Gal(L/F) → Gal(K/F)
```

induces `LayerRefinement.quotientHom`. The inclusion and quotient maps inherit identity and tower
laws from `Abelianization.map`; these laws make the maps usable without unfolding their bodies.
Conjugation of a layer similarly induces an equivalence on abelianizations from
`NormalLayer.conjugateGalEquiv` and Mathlib's `MulEquiv.abelianizationCongr`.

## Main definitions and results

* `TauCeti.ClassFieldTheory.LayerRestriction.inclusionHom`: the map on abelianizations induced by
  inclusion of Galois groups.
* `TauCeti.ClassFieldTheory.LayerRestriction.transferHom`: group-theoretic transfer between the
  same abelianizations, in the opposite direction.
* `TauCeti.ClassFieldTheory.LayerRestriction.transferHom_trans`: the transfer is functorial along
  a tower of restrictions.
* `TauCeti.ClassFieldTheory.LayerRefinement.quotientHom`: the map on abelianizations induced by a
  quotient of Galois groups.
* `NormalLayer.conjugateGalEquiv_abelianizationCongr_one`: conjugation by one is the identity on
  abelianized Galois groups.
* `NormalLayer.conjugateGalEquiv_abelianizationCongr_trans`: conjugation on abelianized Galois
  groups composes.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace LayerRestriction

variable {small big : NormalLayer G}

/-- The index of the image of `Gal(K/E)` in `Gal(K/F)` is the relative degree `[E : F]`. -/
theorem index_range_galHom (T : LayerRestriction small big) :
    T.galHom.range.index = T.relativeDegree := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := small.Gal))
  calc
    Nat.card small.Gal * T.galHom.range.index =
        Nat.card T.galHom.range * T.galHom.range.index := by
          rw [Nat.card_congr (MonoidHom.ofInjective T.galHom_injective).toEquiv]
    _ = Nat.card big.Gal := T.galHom.range.card_mul_index
    _ = big.degree := big.degree_eq_natCard_gal.symm
    _ = small.degree * T.relativeDegree := T.degree_mul_relativeDegree.symm
    _ = Nat.card small.Gal * T.relativeDegree := by rw [small.degree_eq_natCard_gal]

/-- The map `(U'/V)^ab → (U/V)^ab` induced by the inclusion `U'/V → U/V` attached to a
restriction of layers. The additive type tags match the additive convention of Tate cohomology. -/
def inclusionHom (T : LayerRestriction small big) :
    Additive (Abelianization small.Gal) →+ Additive (Abelianization big.Gal) :=
  (Abelianization.map T.galHom).toAdditive

/-- The inclusion map sends the abelianization class of `x` to the class of its image in the
larger Galois group. -/
@[simp]
theorem inclusionHom_of (T : LayerRestriction small big) (x : small.Gal) :
    T.inclusionHom (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (T.galHom x)) :=
  (rfl)

/-- Inclusion on abelianized Galois groups is the identity for the trivial restriction. -/
@[simp]
theorem inclusionHom_self {L : NormalLayer G} (T : LayerRestriction L L) :
    T.inclusionHom = AddMonoidHom.id (Additive (Abelianization L.Gal)) := by
  rw [inclusionHom, T.galHom_self, Abelianization.map_id]
  rfl

variable {a b c : NormalLayer G}

/-- Inclusion on abelianized Galois groups is functorial along a tower of restrictions. -/
theorem inclusionHom_trans (T : LayerRestriction a b) (T' : LayerRestriction b c) :
    (T.trans T').inclusionHom = T'.inclusionHom.comp T.inclusionHom := by
  rw [inclusionHom, inclusionHom, inclusionHom, galHom_trans, ← Abelianization.map_comp]
  rfl

variable {small big : NormalLayer G}

/-- The group-theoretic transfer `(U/V)^ab → (U'/V)^ab` attached to a restriction of layers.
Mathlib's transfer first gives a homomorphism from `U/V` to the abelianization of `U'/V`; the
universal property of the source abelianization then supplies the displayed map. -/
noncomputable def transferHom (T : LayerRestriction small big) :
    Additive (Abelianization big.Gal) →+ Additive (Abelianization small.Gal) :=
  (Abelianization.lift (MonoidHom.transfer
    (Abelianization.of.comp
      (MonoidHom.ofInjective T.galHom_injective).symm.toMonoidHom))).toAdditive

/-- On the class of an element, `transferHom` is Mathlib's group-theoretic transfer to the image
of the smaller Galois group, transported back along the equivalence induced by `galHom`. -/
@[simp]
theorem transferHom_of (T : LayerRestriction small big) (x : big.Gal) :
    T.transferHom (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (MonoidHom.transfer
        (Abelianization.of.comp
          (MonoidHom.ofInjective T.galHom_injective).symm.toMonoidHom) x) :=
  (rfl)

/-- Transfer on abelianized Galois groups is functorial along a tower of restrictions: for
`F ⊆ E ⊆ E' ⊆ K`, the transfer `Gal(K/F)^ab → Gal(K/E')^ab` is the transfer
`Gal(K/F)^ab → Gal(K/E)^ab` followed by the transfer `Gal(K/E)^ab → Gal(K/E')^ab`. -/
theorem transferHom_trans (T : LayerRestriction a b) (T' : LayerRestriction b c) :
    (T.trans T').transferHom = T.transferHom.comp T'.transferHom := by
  have hle := galHom_range_trans_le T T'
  -- Transported along `T'.galHom`, the transfer from `Gal(K/E)` to the image of `Gal(K/E')` is
  -- the transfer from the image of `Gal(K/E)` to that of `Gal(K/E')`, both inside `Gal(K/F)`.
  -- The identification `subgroupOfEquivOfLe` enters as a coercion, the form `transfer_transfer`
  -- is stated in.
  have htransport : (MonoidHom.transfer (Abelianization.of.comp
        (MonoidHom.ofInjective T.galHom_injective).symm.toMonoidHom)).comp
        (MonoidHom.ofInjective T'.galHom_injective).symm.toMonoidHom =
      MonoidHom.transfer ((Abelianization.of.comp
        (MonoidHom.ofInjective (T.trans T').galHom_injective).symm.toMonoidHom).comp
        (MonoidHomClass.toMonoidHom (Subgroup.subgroupOfEquivOfLe hle))) := by
    ext z
    obtain ⟨m, rfl⟩ := (MonoidHom.ofInjective T'.galHom_injective).surjective z
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    refine (MonoidHom.transfer_apply_of_mulEquiv _ _ (galHom_range_map_ofInjective T T') _
      (fun h ↦ congrArg Abelianization.of ((T.trans T').galHom_injective ?_)) m).symm
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.apply_ofInjective_symm]
    simp [galHom_trans T T', MonoidHom.ofInjective_apply]
  refine AddMonoidHom.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨y, rfl⟩ : ∃ y, Abelianization.of y = x := QuotientGroup.mk_surjective x
  rw [AddMonoidHom.comp_apply, transferHom_of, transferHom_of, transferHom,
    MonoidHom.toAdditive_apply_apply, toMul_ofMul]
  -- Naturality in the target (`transfer_comp`) moves the outer `Abelianization.lift` inside the
  -- transfer to `Gal(K/E)`, where it becomes the inner transfer transported along `T'.galHom`;
  -- `htransport` and the tower law `transfer_transfer` then give the transfer of `T.trans T'`.
  rw [← MonoidHom.comp_apply (Abelianization.lift _), ← MonoidHom.transfer_comp,
    ← MonoidHom.comp_assoc, ← Abelianization.lift_symm_apply, Equiv.symm_apply_apply, htransport,
    MonoidHom.transfer_transfer]

end LayerRestriction

namespace LayerRefinement

variable {old new : NormalLayer G}

/-- The quotient map `(U/V')^ab → (U/V)^ab` induced by the quotient homomorphism `U/V' → U/V`
attached to a refinement of layers. -/
def quotientHom (T : LayerRefinement old new) :
    Additive (Abelianization new.Gal) →+ Additive (Abelianization old.Gal) :=
  (Abelianization.map T.galHom).toAdditive

/-- The quotient map sends the abelianization class of `x` to the class of its image in the
quotient Galois group. -/
@[simp]
theorem quotientHom_of (T : LayerRefinement old new) (x : new.Gal) :
    T.quotientHom (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (T.galHom x)) :=
  (rfl)

/-- The quotient map on abelianized Galois groups is surjective. -/
theorem quotientHom_surjective (T : LayerRefinement old new) :
    Function.Surjective T.quotientHom := by
  rintro ⟨x⟩
  induction x using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨y, hy⟩ := T.galHom_surjective x
    refine ⟨Additive.ofMul (Abelianization.of y), ?_⟩
    rw [quotientHom_of, hy]
    rfl

/-- The quotient map on abelianized Galois groups is the identity for the trivial refinement. -/
@[simp]
theorem quotientHom_self {L : NormalLayer G} (T : LayerRefinement L L) :
    T.quotientHom = AddMonoidHom.id (Additive (Abelianization L.Gal)) := by
  rw [quotientHom, T.galHom_self, Abelianization.map_id]
  rfl

variable {a b c : NormalLayer G}

/-- Quotient maps on abelianized Galois groups are functorial along a tower of refinements. -/
theorem quotientHom_trans (T : LayerRefinement a b) (T' : LayerRefinement b c) :
    (T.trans T').quotientHom = T.quotientHom.comp T'.quotientHom := by
  rw [quotientHom, quotientHom, quotientHom, galHom_trans, ← Abelianization.map_comp]
  rfl

end LayerRefinement

namespace NormalLayer

variable (L : NormalLayer G) (g h : G)

/-- Conjugation by `1` is the identity on abelianized Galois groups, after transporting along
`conjugate_one`. -/
@[simp]
theorem conjugateGalEquiv_abelianizationCongr_one :
    ((L.conjugateGalEquiv 1).abelianizationCongr.toAdditive).trans
        ((MulEquiv.abelianizationCongr
          (MulEquiv.cast (M := fun K : NormalLayer G ↦ K.Gal) L.conjugate_one)).toAdditive) =
      AddEquiv.refl (Additive (Abelianization L.Gal)) := by
  apply AddEquiv.ext
  intro x
  have he :
      (L.conjugateGalEquiv 1).abelianizationCongr.trans
          (MulEquiv.cast (M := fun K : NormalLayer G ↦ K.Gal)
            L.conjugate_one).abelianizationCongr =
        MulEquiv.refl (Abelianization L.Gal) := by
    rw [abelianizationCongr_trans, L.conjugateGalEquiv_one, abelianizationCongr_refl]
  simpa only [AddEquiv.trans_apply,
    MulEquiv.toAdditive_apply_apply, MonoidHom.toAdditive_apply_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.refl_apply, AddEquiv.refl_apply,
    toMul_ofMul, ofMul_toMul] using
      congrArg Additive.ofMul (DFunLike.congr_fun he x.toMul)

/-- Conjugation on abelianized Galois groups composes: conjugating by `h` and then by `g` is
conjugating by `g * h`, up to transport along `conjugate_conjugate`. -/
theorem conjugateGalEquiv_abelianizationCongr_trans :
    ((L.conjugateGalEquiv h).abelianizationCongr.toAdditive).trans
        (((L.conjugate h).conjugateGalEquiv g).abelianizationCongr.toAdditive) =
      ((L.conjugateGalEquiv (g * h)).abelianizationCongr.toAdditive).trans
        ((MulEquiv.abelianizationCongr
          (MulEquiv.cast (M := fun K : NormalLayer G ↦ K.Gal)
            (L.conjugate_conjugate g h).symm)).toAdditive) := by
  apply AddEquiv.ext
  intro x
  have he :
      (L.conjugateGalEquiv h).abelianizationCongr.trans
          ((L.conjugate h).conjugateGalEquiv g).abelianizationCongr =
        (L.conjugateGalEquiv (g * h)).abelianizationCongr.trans
          (MulEquiv.cast (M := fun K : NormalLayer G ↦ K.Gal)
            (L.conjugate_conjugate g h).symm).abelianizationCongr := by
    simpa only [abelianizationCongr_trans] using congrArg MulEquiv.abelianizationCongr
      (L.conjugateGalEquiv_trans_conjugateGalEquiv g h)
  simpa only [AddEquiv.trans_apply,
    MulEquiv.toAdditive_apply_apply, MonoidHom.toAdditive_apply_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, toMul_ofMul, ofMul_toMul] using
      congrArg Additive.ofMul (DFunLike.congr_fun he x.toMul)

end NormalLayer

end TauCeti.ClassFieldTheory
