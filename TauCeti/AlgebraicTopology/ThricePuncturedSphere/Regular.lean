/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Deck
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Regular
public import TauCeti.GroupTheory.TriangleGroup.Regular

/-!
# Regular covers of the thrice-punctured sphere

Let `c` be a connected cover of the thrice-punctured sphere `U = ℂ ∖ {0, 1}` whose fibre over the
basepoint `b = 1/2` is numbered by `Fin n`, and let `t` be its monodromy triple. This file proves
that the following are equivalent:

* the deck group acts transitively on the fibre over `b`, or equivalently on every fibre
  (`TauCeti.Deck.IsRegular`);
* the triple `t` is regular (`TauCeti.PermutationTriple.IsRegular`);
* the subgroup of `π₁(U, b)` recovered from any point of the fibre over `b` is normal;
* the monodromy group of the cover, the image of `π₁(U, b)` in the permutations of the fibre,
  acts freely on the fibre;
* the deck group has order `n`, and likewise the monodromy group has order `n`.

The group `π₁(U, b)` is free on the peripheral loops
(`TauCeti.ThricePuncturedSphere.fundamentalGroupMulEquivFreeGroup`), so the third condition is
normality of the corresponding subgroup of `FreeGroup (Fin 2)`. For a regular cover the deck group
is isomorphic to the opposite of the monodromy group of `t`
(`TauCeti.ConnectedFiberNumberedCover.deckMulEquivMonodromyGroupMulOpposite`).

The correspondence with normal subgroups of triangle groups goes through the quotient map
`TauCeti.ThricePuncturedSphere.toTriangleGroup a b c : π₁(U, b) →* Δ(a, b, c)` sending the
peripheral loops at `0` and `1` to the generators `x` and `y`. When the components of `t` have
orders dividing `a`, `b`, `c`, the monodromy representation of the cover factors through it and
the permutation representation `TauCeti.TriangleGroup.toPerm t` of `Δ(a, b, c)`, so the subgroup of
`π₁(U, b)` recovered from the point labelled `i` is the preimage of the stabiliser of `i` in
`Δ(a, b, c)`. For a regular cover this is the preimage of the kernel of `toPerm t`, which is the
normal subgroup that `TauCeti.TriangleGroup.regularIsoClassEquiv` attaches to the class of `t`.

## Main declarations

* `TauCeti.ConnectedFiberNumberedCover.isRegular_proj_iff`: a numbered cover of `U` is regular
  exactly when its triple is.
* `TauCeti.ConnectedFiberNumberedCover.normal_range_mapOfEq_iff`: the recovered subgroup is normal
  exactly when the triple is regular.
* `TauCeti.ConnectedFiberNumberedCover.isRegular_iff_isCancelSMul`: the triple is regular exactly
  when the monodromy group acts freely on the fibre.
* `TauCeti.ConnectedFiberNumberedCover.isRegular_iff_card_deck`,
  `TauCeti.ConnectedFiberNumberedCover.isRegular_iff_card_range_monodromyPerm`: the triple is
  regular exactly when the deck group, respectively the monodromy group, has order the degree.
* `TauCeti.ConnectedFiberNumberedCover.deckMulEquivMonodromyGroupMulOpposite`: the deck group of a
  regular cover is the opposite of the monodromy group of its triple.
* `TauCeti.ThricePuncturedSphere.toTriangleGroup`: the quotient map `π₁(U, b) →* Δ(a, b, c)`.
* `TauCeti.ConnectedFiberNumberedCover.range_mapOfEq_eq_comap_regularIsoClassEquiv`: the
  recovered subgroup of a regular cover is the preimage of the normal subgroup of `Δ(a, b, c)`
  attached to its triple.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Definition 2.64 and Proposition 2.66 (normal coverings, and normality as `deg f = |Mon(f)|`).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.39 (normal
  covering spaces and normal subgroups).
-/

public section

open Equiv FundamentalGroup

namespace TauCeti

open ThricePuncturedSphere PermutationTriple TriangleGroup

variable {n : ℕ}

/-! ### The quotient map to a triangle group -/

namespace ThricePuncturedSphere

variable (a b c : ℕ)

/-- The quotient map `π₁(ℂ ∖ {0, 1}, 1/2) →* Δ(a, b, c)` sending the peripheral loops `periph0` and
`periph1` to the generators `x` and `y`. It is defined through the free basis
`TauCeti.ThricePuncturedSphere.peripheralBasis`. -/
noncomputable def toTriangleGroup :
    FundamentalGroup ThricePuncturedSphere basePt →* TriangleGroup a b c :=
  peripheralBasis.lift ![x a b c, y a b c]

/-- `TauCeti.ThricePuncturedSphere.toTriangleGroup` sends the loop around `0` to `x`. -/
@[simp]
theorem toTriangleGroup_periph0 : toTriangleGroup a b c periph0 = x a b c := by
  simp [toTriangleGroup, ← peripheralBasis_zero]

/-- `TauCeti.ThricePuncturedSphere.toTriangleGroup` sends the loop around `1` to `y`. -/
@[simp]
theorem toTriangleGroup_periph1 : toTriangleGroup a b c periph1 = y a b c := by
  simp [toTriangleGroup, ← peripheralBasis_one]

/-- `TauCeti.ThricePuncturedSphere.toTriangleGroup` sends the loop around `∞` to `z`. -/
@[simp]
theorem toTriangleGroup_periphInf : toTriangleGroup a b c periphInf = z a b c := by
  rw [periphInf_def, map_inv, map_mul, toTriangleGroup_periph0, toTriangleGroup_periph1, z_eq]

/-- `TauCeti.ThricePuncturedSphere.toTriangleGroup` is surjective: `x` and `y` generate
`Δ(a, b, c)`. -/
theorem toTriangleGroup_surjective : Function.Surjective (toTriangleGroup a b c) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_x_y, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  exacts [⟨periph0, toTriangleGroup_periph0 a b c⟩, ⟨periph1, toTriangleGroup_periph1 a b c⟩]

variable {a b c}

/-- **A representation of `π₁(ℂ ∖ {0, 1}, 1/2)` factors through the triangle group** `Δ(a, b, c)`
whenever the components of its triple have orders dividing `a`, `b` and `c`: it is the permutation
representation of the triple composed with `TauCeti.ThricePuncturedSphere.toTriangleGroup`. -/
theorem toPerm_permutationTriple_comp_toTriangleGroup
    (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Perm (Fin n))
    (ha : (permutationTriple ρ).σ0 ^ a = 1) (hb : (permutationTriple ρ).σ1 ^ b = 1)
    (hc : (permutationTriple ρ).σinf ^ c = 1) :
    (toPerm _ ha hb hc).comp (toTriangleGroup a b c) = ρ :=
  fundamentalGroup_hom_ext (by simp) (by simp)

end ThricePuncturedSphere

namespace ConnectedFiberNumberedCover

variable (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

/-! ### Regularity of the deck action -/

/-- **The deck group of a numbered cover of `ℂ ∖ {0, 1}` acts transitively on the fibre over `1/2`
exactly when the triple of the cover is regular.** -/
theorem isPretransitive_deck_iff_isRegular :
    MulAction.IsPretransitive (deck ⇑c.cover.proj) (⇑c.cover.proj ⁻¹' {basePt}) ↔
      (c.connectedTriple : PermutationTriple n).IsRegular := by
  rw [← isPretransitive_range_deckPerm_iff, range_deckPerm_eq_automorphismGroup, isRegular_iff,
    and_iff_right c.connectedTriple.2]

/-- **A numbered cover of `ℂ ∖ {0, 1}` is regular exactly when its triple is regular**: the deck
group acts transitively on every fibre exactly when the triple is regular. -/
theorem isRegular_proj_iff :
    Deck.IsRegular ⇑c.cover.proj ↔ (c.connectedTriple : PermutationTriple n).IsRegular := by
  rw [Deck.isRegular_iff_fiber_isPretransitive c.cover.isCoveringMap_proj
    (c.ν.symm ⟨0, Nat.pos_of_ne_zero c.forgetNumbering.ne_zero⟩),
    isPretransitive_deck_iff_isRegular]

/-- **A numbered cover of `ℂ ∖ {0, 1}` is regular exactly when its deck group has order the
degree.** -/
theorem isRegular_iff_card_deck :
    (c.connectedTriple : PermutationTriple n).IsRegular ↔ Nat.card (deck ⇑c.cover.proj) = n := by
  rw [isRegular_iff_card_automorphismGroup, and_iff_right c.connectedTriple.2,
    Nat.card_congr c.deckMulEquiv.toEquiv]

/-- **A numbered cover of `ℂ ∖ {0, 1}` is regular exactly when its monodromy group, the image of
`π₁(ℂ ∖ {0, 1}, 1/2)` in the permutations of the fibre over `1/2`, has order the degree.** -/
theorem isRegular_iff_card_range_monodromyPerm :
    (c.connectedTriple : PermutationTriple n).IsRegular ↔
      Nat.card (c.cover.isCoveringMap_proj.monodromyPerm basePt).range = n := by
  rw [isRegular_iff_card_monodromyGroup, and_iff_right c.connectedTriple.2, coe_connectedTriple,
    IsCoveringMap.monodromyGroup_monodromyTriple,
    Subgroup.card_map_of_injective c.ν.permCongrHom.injective]

/-! ### The recovered subgroup and the monodromy action -/

/-- **The subgroup of `π₁(ℂ ∖ {0, 1}, 1/2)` recovered from a point of the fibre over `1/2` is
normal exactly when the triple of the cover is regular.** Through the isomorphism
`TauCeti.ThricePuncturedSphere.fundamentalGroupMulEquivFreeGroup` this is normality of the
corresponding subgroup of `FreeGroup (Fin 2)`. -/
theorem normal_range_mapOfEq_iff (e : ⇑c.cover.proj ⁻¹' {basePt}) :
    (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ e.2).range.Normal ↔
      (c.connectedTriple : PermutationTriple n).IsRegular := by
  have := c.cover.isCoveringMap_proj.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (c.cover : TopCat) := PathConnectedSpace.of_locallyPathConnectedSpace
  rw [← IsCoveringMap.isRegular_iff_normal_range c.cover.isCoveringMap_proj e, isRegular_proj_iff]

/-- **A numbered cover of `ℂ ∖ {0, 1}` is regular exactly when its monodromy group acts freely on
the fibre over `1/2`.** -/
theorem isRegular_iff_isCancelSMul :
    (c.connectedTriple : PermutationTriple n).IsRegular ↔
      IsCancelSMul (c.cover.isCoveringMap_proj.monodromyPerm basePt).range
        (⇑c.cover.proj ⁻¹' {basePt}) := by
  have := c.cover.isCoveringMap_proj.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (c.cover : TopCat) := PathConnectedSpace.of_locallyPathConnectedSpace
  let e := c.ν.symm ⟨0, Nat.pos_of_ne_zero c.forgetNumbering.ne_zero⟩
  have htrans : MulAction.IsPretransitive (c.cover.isCoveringMap_proj.monodromyPerm basePt).range
      (⇑c.cover.proj ⁻¹' {basePt}) := by
    let := c.cover.isCoveringMap_proj.fundamentalGroupMulAction basePt
    have := c.cover.isCoveringMap_proj.monodromy_isPretransitive (x := basePt)
    rw [← IsCoveringMap.toPermHom_eq_monodromyPerm, MulAction.isPretransitive_range_toPermHom_iff]
    infer_instance
  rw [← MonoidHom.normal_comap_stabilizer_iff_isCancelSMul _ htrans e,
    c.cover.isCoveringMap_proj.comap_stabilizer_monodromyPerm, normal_range_mapOfEq_iff]

/-- **The deck group of a regular numbered cover of `ℂ ∖ {0, 1}` is the opposite of the monodromy
group of its triple.** A deck transformation `φ` goes to the unique element of the monodromy group
moving the label `i` to the label of the image under `φ` of the point labelled `i`
(`unop_deckMulEquivMonodromyGroupMulOpposite_smul`). -/
noncomputable def deckMulEquivMonodromyGroupMulOpposite
    (h : (c.connectedTriple : PermutationTriple n).IsRegular) (i : Fin n) :
    deck ⇑c.cover.proj ≃* (c.connectedTriple : PermutationTriple n).monodromyGroupᵐᵒᵖ :=
  c.deckMulEquiv.trans (automorphismGroupMulEquivMonodromyGroupMulOpposite h i)

/-- The element of the monodromy group attached to a deck transformation `φ` moves the label `i`
as `φ` does. -/
@[simp]
theorem unop_deckMulEquivMonodromyGroupMulOpposite_smul
    (h : (c.connectedTriple : PermutationTriple n).IsRegular) (i : Fin n)
    (φ : deck ⇑c.cover.proj) :
    (c.deckMulEquivMonodromyGroupMulOpposite h i φ).unop • i = c.deckPerm φ i := by
  rw [deckMulEquivMonodromyGroupMulOpposite, MulEquiv.trans_apply,
    unop_automorphismGroupMulEquivMonodromyGroupMulOpposite_smul, Subgroup.smul_def, Perm.smul_def,
    coe_deckMulEquiv_apply]

/-! ### Comparison with normal subgroups of triangle groups -/

section TriangleGroup

variable {a b k : ℕ} (ha : (c.connectedTriple : PermutationTriple n).σ0 ^ a = 1)
  (hb : (c.connectedTriple : PermutationTriple n).σ1 ^ b = 1)
  (hk : (c.connectedTriple : PermutationTriple n).σinf ^ k = 1)

/-- **The monodromy representation of a numbered cover of `ℂ ∖ {0, 1}` factors through the
triangle group** `Δ(a, b, k)`, whenever the components of its triple have orders dividing `a`, `b`
and `k`: it is the permutation representation of the triple composed with the quotient map
`TauCeti.ThricePuncturedSphere.toTriangleGroup`. -/
theorem toPerm_comp_toTriangleGroup :
    (toPerm _ ha hb hk).comp (toTriangleGroup a b k) =
      c.ν.permCongrHom.toMonoidHom.comp (c.cover.isCoveringMap_proj.monodromyPerm basePt) := by
  generalize ht : (c.connectedTriple : PermutationTriple n) = t at ha hb hk
  rw [coe_connectedTriple, IsCoveringMap.monodromyTriple_def] at ht
  subst ht
  exact toPerm_permutationTriple_comp_toTriangleGroup _ ha hb hk

/-- **The subgroup recovered from the point labelled `i` is the preimage of the stabiliser of `i`
under the action of the triangle group** `Δ(a, b, k)` on the labels. -/
theorem range_mapOfEq_eq_comap_comap_stabilizer (i : Fin n) :
    (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ (c.ν.symm i).2).range =
      ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm _ ha hb hk)).comap
        (toTriangleGroup a b k) := by
  rw [Subgroup.comap_comap, toPerm_comp_toTriangleGroup, ← Subgroup.comap_comap,
    ← c.cover.isCoveringMap_proj.comap_stabilizer_monodromyPerm]
  congr 1
  ext σ
  simp [MulAction.mem_stabilizer_iff, permCongr_apply, Equiv.eq_symm_apply]

/-- **The subgroup recovered from any point of the fibre of a regular cover is the preimage of the
kernel of the action of the triangle group** `Δ(a, b, k)` on the labels. -/
theorem range_mapOfEq_eq_comap_ker (h : (c.connectedTriple : PermutationTriple n).IsRegular)
    (e : ⇑c.cover.proj ⁻¹' {basePt}) :
    (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ e.2).range =
      (toPerm _ ha hb hk).ker.comap (toTriangleGroup a b k) := by
  rw [← c.ν.symm_apply_apply e, range_mapOfEq_eq_comap_comap_stabilizer c ha hb hk,
    comap_stabilizer_toPerm_eq_ker _ _ _ _ _
      (isCancelSMul_iff_stabilizer_eq_bot.mp h.isCancelSMul _)]

/-- **A regular cover of `ℂ ∖ {0, 1}` matches the normal subgroup of the triangle group attached to
its triple.** The subgroup recovered from any point of the fibre is the preimage under
`TauCeti.ThricePuncturedSphere.toTriangleGroup` of the normal subgroup of index `n` of
`Δ(a, b, k)` that `TauCeti.TriangleGroup.regularIsoClassEquiv` attaches to the class of the
triple. -/
theorem range_mapOfEq_eq_comap_regularIsoClassEquiv [NeZero n]
    (h : (c.connectedTriple : PermutationTriple n).IsRegular) (e : ⇑c.cover.proj ⁻¹' {basePt}) :
    (mapOfEq ⟨c.cover.proj, c.cover.isCoveringMap_proj.continuous⟩ e.2).range =
      (regularIsoClassEquiv ⟨IsoClass.mk (c.connectedTriple : PermutationTriple n),
        mk_mem_regularIsoClasses_iff.mpr ⟨h, (hasDividingOrders_iff _).mpr ⟨ha, hb, hk⟩⟩⟩ :
          Subgroup (TriangleGroup a b k)).comap (toTriangleGroup a b k) := by
  rw [coe_regularIsoClassEquiv_mk _ ha hb hk, range_mapOfEq_eq_comap_ker c ha hb hk h e]

end TriangleGroup

/-! ### The threaded examples -/

/-- The cover of `ℂ ∖ {0, 1}` with the triple of `z ↦ zⁿ` is regular. -/
theorem isRegular_proj_of_connectedTriple_eq_cyclicTriple
    (hc : (c.connectedTriple : PermutationTriple n) = cyclicTriple n) :
    Deck.IsRegular ⇑c.cover.proj := by
  rw [isRegular_proj_iff, hc]
  exact isRegular_cyclicTriple c.forgetNumbering.ne_zero

/-- The degree-four cover of `ℂ ∖ {0, 1}` with the torus triple is regular. -/
theorem isRegular_proj_of_connectedTriple_eq_torusTriple
    (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt 4)
    (hc : (c.connectedTriple : PermutationTriple 4) = torusTriple) :
    Deck.IsRegular ⇑c.cover.proj := by
  rw [isRegular_proj_iff, hc]
  exact isRegular_torusTriple

end ConnectedFiberNumberedCover

end TauCeti
