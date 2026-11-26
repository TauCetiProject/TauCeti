/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
public import TauCeti.LinearAlgebra.RootSystem.Weyl.CartanType
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm

/-!
# Weyl groups of type D

The classical roots of type `Dₙ` are the vectors `±eᵢ ± eⱼ` (`i ≠ j`) of `ℤⁿ`, the integral
vectors of squared length two (`TauCeti.DynkinType.TypeDRoot`). The hyperoctahedral group
`ℤˣ ≀ Sym(n)` of signed permutations of the coordinates preserves the dot product, so it permutes
these roots, and for `n ≥ 2` it acts on them faithfully. The reflection in `eᵢ - eⱼ` is the
transposition of the coordinates `i` and `j`, and the reflection in `±(eᵢ + eⱼ)` is that
transposition followed by the sign change of both coordinates. Transpositions and double sign
changes generate the signed permutations with an even number of sign changes, the kernel of the
product of the signs. So the classical reflections generate exactly the image of that kernel, of
order `2ⁿ⁻¹ · n!`.

The pinned datum of type `Dₙ` permutes its root indices as the classical reflections permute the
classical roots (`TauCeti.DynkinType.typeDRootEquiv_reflectionPerm`), and its Weyl group acts
faithfully on its root indices. This identifies its Weyl group with the even-sign subgroup; the
pinned rational root system has the same reflection permutations. Since the Weyl group of a root
system over `ℚ` depends only on its Cartan type
(`TauCeti.nonempty_weylGroup_mulEquiv_of_hasCartanType`), every root system over `ℚ` with a base
of Cartan type `Dₙ` has Weyl group of order `2ⁿ⁻¹ · n!`.

## Main definitions

* `TauCeti.DynkinType.typeDWeylSubgroup`: the signed permutations of `n` coordinates with an even
  number of sign changes.
* `TauCeti.DynkinType.negSwap`: the signed permutation exchanging two distinct coordinates and
  changing both their signs.
* `TauCeti.DynkinType.typeDRootPermHom`: the action of signed permutations on the pinned root
  indices of type `Dₙ`.
* `TauCeti.DynkinType.typeDWeylGroupEquiv`: the Weyl group of the pinned integral datum of type
  `Dₙ` is the even-sign subgroup.
* `TauCeti.DynkinType.typeDRationalWeylGroupEquiv`: the same for the pinned rational root system.

## Main results

* `TauCeti.DynkinType.closure_range_typeDRootReflectionEquiv`: the classical reflections generate
  the image of the even-sign subgroup in the permutations of the classical roots.
* `TauCeti.DynkinType.coe_typeDWeylGroupEquiv_ofIdx_typeDRootSub` and
  `TauCeti.DynkinType.coe_typeDWeylGroupEquiv_ofIdx_typeDRootAdd`: the reflection in `eᵢ - eⱼ` is
  the transposition of `i` and `j`, and the reflection in `eᵢ + eⱼ` is `negSwap i j`; similarly
  for the pinned rational root system.
* `TauCeti.DynkinType.card_weylGroup_typeDSimplyConnectedRootDatum`: the Weyl group of the pinned
  datum of type `Dₙ` has order `2ⁿ⁻¹ · n!`.
* `RootPairing.card_weylGroup_of_hasCartanType_D`: so does the Weyl group of every finite reduced
  crystallographic root system over `ℚ` with a base of Cartan type `Dₙ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Section 2.10.
* S. Fomin and N. Reading, *Root systems and generalized associahedra*, Lecture 2, §2.5.
-/

public section

open Function Set

namespace TauCeti

namespace DynkinType

open RootPairing

noncomputable section

variable {n : ℕ}

/-! ## The even-sign subgroup -/

/-- The Weyl group of type `Dₙ` in its classical model: the signed permutations of the `n`
coordinates with an even number of sign changes, the kernel of the product of the signs on the
hyperoctahedral group `ℤˣ ≀ Sym(n)`. -/
def typeDWeylSubgroup (n : ℕ) : Subgroup (WreathProduct ℤˣ (Fin n)) :=
  (WreathProduct.baseProd ℤˣ (Fin n)).ker

/-- A signed permutation lies in the even-sign subgroup when the product of its signs is `1`. -/
@[simp]
theorem mem_typeDWeylSubgroup_iff {w : WreathProduct ℤˣ (Fin n)} :
    w ∈ typeDWeylSubgroup n ↔ ∏ i, w.left i = 1 := by
  rw [typeDWeylSubgroup, MonoidHom.mem_ker, WreathProduct.baseProd_apply]

/-- In positive rank the even-sign subgroup has order `2ⁿ⁻¹ · n!`, half the order of the
hyperoctahedral group. -/
theorem card_typeDWeylSubgroup (hn : 1 ≤ n) :
    Nat.card (typeDWeylSubgroup n) = 2 ^ (n - 1) * n.factorial := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := WreathProduct.card_ker_baseProd_mul_card (C := ℤˣ) (κ := Fin n)
  rw [WreathProduct.card, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int,
    Nat.card_fin] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
  rw [typeDWeylSubgroup, h, Nat.add_sub_cancel, pow_succ]
  ring

/-! ## The action on the classical roots -/

/-- Signed permutations of the coordinates permute the classical roots of type `Dₙ`, the integral
vectors of squared length two. -/
instance : MulAction (WreathProduct ℤˣ (Fin n)) (TypeDRoot n) where
  smul w x := ⟨w • x.val, by rw [WreathProduct.smul_dotProduct_smul, x.property]⟩
  one_smul x := Subtype.ext (one_smul _ x.val)
  mul_smul w z x := Subtype.ext (mul_smul w z x.val)

/-- A signed permutation acts on a classical root by acting on its coordinates. -/
@[simp]
theorem coe_smul_typeDRoot (w : WreathProduct ℤˣ (Fin n)) (x : TypeDRoot n) :
    ((w • x : TypeDRoot n) : Fin n → ℤ) = w • (x : Fin n → ℤ) :=
  (rfl)

/-- A signed permutation fixing the roots `eᵢ + eⱼ` and `eᵢ - eⱼ` fixes the coordinate `i` with
sign `1`. -/
private theorem right_apply_eq_and_left_eq_one {w : WreathProduct ℤˣ (Fin n)} {i j : Fin n}
    (hij : i ≠ j) (hadd : w • typeDRootAdd hij = typeDRootAdd hij)
    (hsub : w • typeDRootSub hij = typeDRootSub hij) :
    w.right i = i ∧ w.left i = 1 := by
  -- Evaluate both fixed roots at the coordinate `w.right i`, where the sign `w.left (w.right i)`
  -- of the signed permutation appears.
  have hp := congrFun (congrArg Subtype.val hadd) (w.right i)
  have hm := congrFun (congrArg Subtype.val hsub) (w.right i)
  simp only [coe_smul_typeDRoot, WreathProduct.product_smul, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply, coe_typeDRootAdd, coe_typeDRootSub, Pi.add_apply, Pi.sub_apply,
    Pi.single_eq_same, Units.smul_def] at hp hm
  rcases Int.units_eq_one_or (w.left (w.right i)) with hu | hu <;>
    by_cases hk : w.right i = i <;> by_cases hj : w.right i = j <;>
    simp_all

/-- For `n ≥ 2` a signed permutation fixing every classical root of type `Dₙ` is the identity. -/
theorem eq_one_of_forall_smul_typeDRoot_eq (hn : 2 ≤ n) {w : WreathProduct ℤˣ (Fin n)}
    (hw : ∀ x : TypeDRoot n, w • x = x) : w = 1 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have key (i : Fin n) : w.right i = i ∧ w.left i = 1 := by
    obtain ⟨j, hji⟩ := exists_ne i
    exact right_apply_eq_and_left_eq_one hji.symm (hw _) (hw _)
  exact SemidirectProduct.ext (funext fun i ↦ (key i).2) (Equiv.ext fun i ↦ (key i).1)

/-- A signed permutation acting on coordinate vectors as the reflection in a classical root acts
on the classical roots as that reflection. -/
private theorem typeDRootReflectionEquiv_eq_toPerm {u : TypeDRoot n}
    {w : WreathProduct ℤˣ (Fin n)} (h : ∀ v : Fin n → ℤ, w • v = v - (v ⬝ᵥ u.val) • u.val) :
    typeDRootReflectionEquiv u = MulAction.toPerm w :=
  Equiv.ext fun v ↦ Subtype.ext <| by
    rw [typeDRootReflectionEquiv_apply, typeDRootReflection_val, MulAction.toPerm_apply,
      coe_smul_typeDRoot, h]

/-- For `i ≠ j`, the signed permutation exchanging the coordinates `i` and `j` and changing both
their signs. For `i = j` the two sign changes cancel and `negSwap i i = 1`. -/
def negSwap (i j : Fin n) : WreathProduct ℤˣ (Fin n) :=
  SemidirectProduct.inl (Pi.mulSingle i (-1) * Pi.mulSingle j (-1)) *
    SemidirectProduct.inr (Equiv.swap i j)

/-- The signs of `negSwap i j`: for `i ≠ j`, `-1` at the coordinates `i` and `j` and `1`
elsewhere (for `i = j` the two factors cancel). -/
@[simp]
theorem left_negSwap (i j : Fin n) :
    (negSwap i j).left = Pi.mulSingle i (-1) * Pi.mulSingle j (-1) := by
  simp [negSwap]

/-- The underlying permutation of `negSwap i j` is the transposition of `i` and `j`. -/
@[simp]
theorem right_negSwap (i j : Fin n) : (negSwap i j).right = Equiv.swap i j := by
  simp [negSwap]

/-- The reflection in `eᵢ - eⱼ` is the transposition of the coordinates `i` and `j`. -/
private theorem typeDRootReflectionEquiv_typeDRootSub {i j : Fin n} (hij : i ≠ j) :
    typeDRootReflectionEquiv (typeDRootSub hij) =
      MulAction.toPerm (SemidirectProduct.inr (Equiv.swap i j) : WreathProduct ℤˣ (Fin n)) := by
  refine typeDRootReflectionEquiv_eq_toPerm fun v ↦ funext fun k ↦ ?_
  rcases eq_or_ne k i with rfl | hki
  · simp [coe_typeDRootSub, hij]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [coe_typeDRootSub, hki]
    · simp [coe_typeDRootSub, Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

/-- The reflection in a root `u` with `u = eᵢ + eⱼ` or `u = -(eᵢ + eⱼ)` exchanges the coordinates
`i` and `j` and changes both their signs. -/
private theorem typeDRootReflectionEquiv_eq_negSwap {i j : Fin n} (hij : i ≠ j) {u : TypeDRoot n}
    (hu : u.val = Pi.single i 1 + Pi.single j 1 ∨ u.val = -(Pi.single i 1 + Pi.single j 1)) :
    typeDRootReflectionEquiv u = MulAction.toPerm (negSwap i j) := by
  refine typeDRootReflectionEquiv_eq_toPerm fun v ↦ ?_
  -- The reflection only sees `u` through `(v ⬝ᵥ u) • u`, which does not change when `u` is negated.
  have hrefl : (v ⬝ᵥ u.val) • u.val =
      (v ⬝ᵥ (Pi.single i 1 + Pi.single j 1)) • (Pi.single i 1 + Pi.single j 1) := by
    rcases hu with hu | hu <;> rw [hu]
    rw [dotProduct_neg, neg_smul_neg]
  rw [hrefl]
  funext k
  rcases eq_or_ne k i with rfl | hki
  · simp [negSwap, hij]
  · rcases eq_or_ne k j with rfl | hkj
    · simp [negSwap, hki]
    · simp [negSwap, Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

private theorem inr_swap_mem_typeDWeylSubgroup (i j : Fin n) :
    (SemidirectProduct.inr (Equiv.swap i j) : WreathProduct ℤˣ (Fin n)) ∈ typeDWeylSubgroup n := by
  simp [mem_typeDWeylSubgroup_iff]

private theorem negSwap_mem_typeDWeylSubgroup (i j : Fin n) :
    negSwap i j ∈ typeDWeylSubgroup n := by
  simp [mem_typeDWeylSubgroup_iff, negSwap, Finset.prod_mul_distrib]

/-- **The classical reflections of type `Dₙ` generate the even-sign subgroup**: the subgroup of
permutations of the classical roots generated by the reflections is the image of the signed
permutations with an even number of sign changes. -/
theorem closure_range_typeDRootReflectionEquiv :
    Subgroup.closure (range (typeDRootReflectionEquiv (n := n))) =
      (typeDWeylSubgroup n).map (MulAction.toPermHom (WreathProduct ℤˣ (Fin n)) (TypeDRoot n)) := by
  apply le_antisymm
  · -- Every reflection is a transposition, or a transposition with a double sign change.
    rw [Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    obtain ⟨i, j, hij, hu | hu⟩ := u.exists_eq_single_sub_or_add_or_neg_add
    · obtain rfl : u = typeDRootSub hij := Subtype.ext (hu.trans (coe_typeDRootSub hij).symm)
      exact ⟨_, inr_swap_mem_typeDWeylSubgroup i j,
        (typeDRootReflectionEquiv_typeDRootSub hij).symm⟩
    · exact ⟨_, negSwap_mem_typeDWeylSubgroup i j,
        (typeDRootReflectionEquiv_eq_negSwap hij hu).symm⟩
  · -- Conversely, transpositions and double sign changes generate the even-sign subgroup.
    rw [Subgroup.map_le_iff_le_comap]
    set H := (Subgroup.closure (range (typeDRootReflectionEquiv (n := n)))).comap
      (MulAction.toPermHom (WreathProduct ℤˣ (Fin n)) (TypeDRoot n))
    have hswap (i j : Fin n) (hij : i ≠ j) : SemidirectProduct.inr (Equiv.swap i j) ∈ H :=
      Subgroup.subset_closure ⟨typeDRootSub hij, typeDRootReflectionEquiv_typeDRootSub hij⟩
    have hnegSwap (i j : Fin n) (hij : i ≠ j) : negSwap i j ∈ H :=
      Subgroup.subset_closure ⟨typeDRootAdd hij,
        typeDRootReflectionEquiv_eq_negSwap hij (Or.inl (coe_typeDRootAdd hij))⟩
    -- A double sign change is a signed transposition followed by the transposition.
    rw [typeDWeylSubgroup]
    refine WreathProduct.ker_baseProd_le_of_inl_mulSingle_mul_mulSingle_mem_of_inr_swap_mem hswap
      fun i j hij ↦ ?_
    rw [show SemidirectProduct.inl (Pi.mulSingle i (-1) * Pi.mulSingle j (-1)) =
        negSwap i j * SemidirectProduct.inr (Equiv.swap i j) by
      rw [negSwap, mul_assoc, ← map_mul SemidirectProduct.inr, Equiv.swap_mul_self, map_one,
        mul_one]]
    exact H.mul_mem (hnegSwap i j hij) (hswap i j hij)

/-! ## The pinned root indices -/

/-- The action of signed permutations on the pinned root indices of type `Dₙ`, transported from
the classical roots along the enumeration `TauCeti.DynkinType.typeDRootEquiv`. -/
def typeDRootPermHom (n : ℕ) (hn : 4 ≤ n) :
    WreathProduct ℤˣ (Fin n) →* Equiv.Perm (Fin (2 * n * (n - 1))) :=
  (typeDRootEquiv n hn).symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom _ _)

/-- A signed permutation moves the root index `k` to the index of its image of the `k`-th
classical root. -/
@[simp]
theorem typeDRootEquiv_typeDRootPermHom_apply (hn : 4 ≤ n) (w : WreathProduct ℤˣ (Fin n))
    (k : Fin (2 * n * (n - 1))) :
    typeDRootEquiv n hn (typeDRootPermHom n hn w k) = w • typeDRootEquiv n hn k := by
  simp [typeDRootPermHom, Equiv.permCongrHom, Equiv.permCongr_apply]

/-- The action of signed permutations on the pinned root indices of type `Dₙ` is faithful. -/
theorem typeDRootPermHom_injective (hn : 4 ≤ n) : Injective (typeDRootPermHom n hn) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ eq_one_of_forall_smul_typeDRoot_eq (by omega)
    fun x ↦ ?_
  obtain ⟨k, rfl⟩ := (typeDRootEquiv n hn).surjective x
  rw [← typeDRootEquiv_typeDRootPermHom_apply, hw, Equiv.Perm.one_apply]

/-- The pinned reflection permutations of type `Dₙ` are the classical reflections, transported to
the root indices. -/
private theorem reflectionPerm_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).reflectionPerm =
      (typeDRootEquiv n hn).symm.permCongrHom.toMonoidHom ∘ typeDRootReflectionEquiv ∘
        typeDRootEquiv n hn := by
  funext k
  refine Equiv.ext fun l ↦ (typeDRootEquiv n hn).injective ?_
  simp [Equiv.permCongrHom, Equiv.permCongr_apply]

/-- The pinned Weyl group of type `Dₙ` permutes the root indices exactly as the even-sign subgroup
does. -/
private theorem range_weylGroupToPerm_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).weylGroupToPerm.range =
      ((typeDRootPermHom n hn).domRestrict (typeDWeylSubgroup n)).range := by
  rw [range_weylGroupToPerm, reflectionPerm_typeDSimplyConnectedRootDatum,
    range_comp, (typeDRootEquiv n hn).surjective.range_comp, ← MonoidHom.map_closure,
    closure_range_typeDRootReflectionEquiv, Subgroup.map_map, MonoidHom.domRestrict_range,
    typeDRootPermHom]

private theorem typeDRootPermHom_domRestrict_injective (hn : 4 ≤ n) :
    Injective ((typeDRootPermHom n hn).domRestrict (typeDWeylSubgroup n)) :=
  fun _ _ h ↦ Subtype.ext (typeDRootPermHom_injective hn h)

/-- **The Weyl group of the pinned integral datum of type `Dₙ` is the group of signed permutations
of `n` coordinates with an even number of sign changes**, acting on the root indices as on the
classical roots `±eᵢ ± eⱼ`; see `TauCeti.DynkinType.typeDRootPermHom_typeDWeylGroupEquiv`. -/
noncomputable def typeDWeylGroupEquiv (n : ℕ) (hn : 4 ≤ n) :
    (typeDSimplyConnectedRootDatum n hn).weylGroup ≃* typeDWeylSubgroup n :=
  (MonoidHom.ofInjective (weylGroupToPerm_injective_of_corootSpan_eq_top _
      (corootSpan_typeDSimplyConnectedRootDatum_eq_top n hn))).trans <|
    (MulEquiv.subgroupCongr (range_weylGroupToPerm_typeDSimplyConnectedRootDatum hn)).trans
      (MonoidHom.ofInjective (typeDRootPermHom_domRestrict_injective hn)).symm

/-- The signed permutation attached to a Weyl-group element of the pinned datum of type `Dₙ`
induces its permutation of the root indices. -/
@[simp]
theorem typeDRootPermHom_typeDWeylGroupEquiv (hn : 4 ≤ n)
    (w : (typeDSimplyConnectedRootDatum n hn).weylGroup) :
    typeDRootPermHom n hn (typeDWeylGroupEquiv n hn w) =
      (typeDSimplyConnectedRootDatum n hn).weylGroupToPerm w := by
  rw [typeDWeylGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← MonoidHom.domRestrict_apply, MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

/-- The reflection in a classical root `u` goes to a signed permutation acting on the classical
roots as the reflection in `u`. -/
private theorem coe_typeDWeylGroupEquiv_ofIdx_symm (hn : 4 ≤ n) {u : TypeDRoot n}
    {w : WreathProduct ℤˣ (Fin n)} (h : typeDRootReflectionEquiv u = MulAction.toPerm w) :
    (typeDWeylGroupEquiv n hn (weylGroup.ofIdx (typeDSimplyConnectedRootDatum n hn)
      ((typeDRootEquiv n hn).symm u)) : WreathProduct ℤˣ (Fin n)) = w := by
  refine typeDRootPermHom_injective hn ?_
  rw [typeDRootPermHom_typeDWeylGroupEquiv]
  refine Equiv.ext fun l ↦ (typeDRootEquiv n hn).injective ?_
  rw [weylGroupToPerm_ofIdx_apply, typeDRootEquiv_reflectionPerm,
    typeDRootEquiv_typeDRootPermHom_apply, Equiv.apply_symm_apply, ← typeDRootReflectionEquiv_apply,
    h, MulAction.toPerm_apply]

/-- Under the type-`Dₙ` Weyl-group equivalence, the reflection in the root `eᵢ - eⱼ` is the
transposition of the coordinates `i` and `j`. -/
@[simp]
theorem coe_typeDWeylGroupEquiv_ofIdx_typeDRootSub (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    (typeDWeylGroupEquiv n hn (weylGroup.ofIdx (typeDSimplyConnectedRootDatum n hn)
      ((typeDRootEquiv n hn).symm (typeDRootSub hij))) : WreathProduct ℤˣ (Fin n)) =
      SemidirectProduct.inr (Equiv.swap i j) :=
  coe_typeDWeylGroupEquiv_ofIdx_symm hn (typeDRootReflectionEquiv_typeDRootSub hij)

/-- Under the type-`Dₙ` Weyl-group equivalence, the reflection in the root `eᵢ + eⱼ` exchanges
the coordinates `i` and `j` and changes both their signs. The reflection in `-(eᵢ + eⱼ)` is the
same Weyl-group element (`RootPairing.weylGroup.ofIdx_neg`). -/
@[simp]
theorem coe_typeDWeylGroupEquiv_ofIdx_typeDRootAdd (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    (typeDWeylGroupEquiv n hn (weylGroup.ofIdx (typeDSimplyConnectedRootDatum n hn)
      ((typeDRootEquiv n hn).symm (typeDRootAdd hij))) : WreathProduct ℤˣ (Fin n)) =
      negSwap i j :=
  coe_typeDWeylGroupEquiv_ofIdx_symm hn
    (typeDRootReflectionEquiv_eq_negSwap hij (Or.inl (coe_typeDRootAdd hij)))

section Realization

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (hn : 4 ≤ n) (Q : RootPairing (Fin (2 * n * (n - 1))) R M N)
  (hQ : Q.reflectionPerm = (typeDSimplyConnectedRootDatum n hn).reflectionPerm)
  (hinj : Injective Q.weylGroupToPerm)

include hQ hinj

/-- Compare a root pairing whose Weyl group acts faithfully on the root indices, with the pinned
reflection permutations of type `Dₙ`, with the even-sign subgroup. -/
private noncomputable def typeDWeylGroupEquivOf : Q.weylGroup ≃* typeDWeylSubgroup n :=
  (weylGroupEquivOfReflectionPermEq Q (typeDSimplyConnectedRootDatum n hn) hQ hinj
    (weylGroupToPerm_injective_of_corootSpan_eq_top _
      (corootSpan_typeDSimplyConnectedRootDatum_eq_top n hn))).trans (typeDWeylGroupEquiv n hn)

private theorem typeDRootPermHom_typeDWeylGroupEquivOf (w : Q.weylGroup) :
    typeDRootPermHom n hn (typeDWeylGroupEquivOf hn Q hQ hinj w) = Q.weylGroupToPerm w := by
  rw [typeDWeylGroupEquivOf, MulEquiv.trans_apply, typeDRootPermHom_typeDWeylGroupEquiv,
    weylGroupToPerm_weylGroupEquivOfReflectionPermEq]

private theorem typeDWeylGroupEquivOf_ofIdx (k : Fin (2 * n * (n - 1))) :
    typeDWeylGroupEquivOf hn Q hQ hinj (weylGroup.ofIdx Q k) =
      typeDWeylGroupEquiv n hn (weylGroup.ofIdx (typeDSimplyConnectedRootDatum n hn) k) := by
  rw [typeDWeylGroupEquivOf, MulEquiv.trans_apply, weylGroupEquivOfReflectionPermEq_ofIdx]

end Realization

/-- **The Weyl group of the pinned integral datum of type `Dₙ` has order `2ⁿ⁻¹ · n!`.** -/
theorem card_weylGroup_typeDSimplyConnectedRootDatum (hn : 4 ≤ n) :
    Nat.card (typeDSimplyConnectedRootDatum n hn).weylGroup = 2 ^ (n - 1) * n.factorial := by
  rw [Nat.card_congr (typeDWeylGroupEquiv n hn).toEquiv, card_typeDWeylSubgroup (by omega)]

private theorem reflectionPerm_rationalRootSystem_D (hn : 4 ≤ n) :
    ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn)).reflectionPerm =
      (typeDSimplyConnectedRootDatum n hn).reflectionPerm := by
  rw [reflectionPerm_rationalRootSystem, simplyConnectedRootDatum_D]

/-- The pinned rational root system of type `Dₙ` has as Weyl group the signed permutations of `n`
coordinates with an even number of sign changes. It has the same reflection permutations as the
integral datum, so the same comparison applies. -/
noncomputable def typeDRationalWeylGroupEquiv (n : ℕ) (hn : 4 ≤ n) :
    ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn)).weylGroup ≃*
      typeDWeylSubgroup n :=
  typeDWeylGroupEquivOf hn _ (reflectionPerm_rationalRootSystem_D hn)
    (weylGroupToPerm_injective ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn)))

/-- The signed permutation attached to a Weyl-group element of the pinned rational root system of
type `Dₙ` induces its permutation of the root indices. -/
@[simp]
theorem typeDRootPermHom_typeDRationalWeylGroupEquiv (hn : 4 ≤ n)
    (w : ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn)).weylGroup) :
    typeDRootPermHom n hn (typeDRationalWeylGroupEquiv n hn w) =
      ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn)).weylGroupToPerm w :=
  typeDRootPermHom_typeDWeylGroupEquivOf hn _ _ _ w

/-- Under the rational type-`Dₙ` Weyl-group equivalence, the reflection in the root `eᵢ - eⱼ` is
the transposition of the coordinates `i` and `j`. -/
@[simp]
theorem coe_typeDRationalWeylGroupEquiv_ofIdx_typeDRootSub (hn : 4 ≤ n) {i j : Fin n}
    (hij : i ≠ j) :
    (typeDRationalWeylGroupEquiv n hn
      (weylGroup.ofIdx ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn))
        ((typeDRootEquiv n hn).symm (typeDRootSub hij))) : WreathProduct ℤˣ (Fin n)) =
      SemidirectProduct.inr (Equiv.swap i j) :=
  (congrArg Subtype.val (typeDWeylGroupEquivOf_ofIdx hn _ _ _ _)).trans
    (coe_typeDWeylGroupEquiv_ofIdx_typeDRootSub hn hij)

/-- Under the rational type-`Dₙ` Weyl-group equivalence, the reflection in the root `eᵢ + eⱼ`
exchanges the coordinates `i` and `j` and changes both their signs. -/
@[simp]
theorem coe_typeDRationalWeylGroupEquiv_ofIdx_typeDRootAdd (hn : 4 ≤ n) {i j : Fin n}
    (hij : i ≠ j) :
    (typeDRationalWeylGroupEquiv n hn
      (weylGroup.ofIdx ((DynkinType.D n).rationalRootSystem (DynkinType.valid_D.mpr hn))
        ((typeDRootEquiv n hn).symm (typeDRootAdd hij))) : WreathProduct ℤˣ (Fin n)) =
      negSwap i j :=
  (congrArg Subtype.val (typeDWeylGroupEquivOf_ofIdx hn _ _ _ _)).trans
    (coe_typeDWeylGroupEquiv_ofIdx_typeDRootAdd hn hij)

end

end DynkinType

end TauCeti

namespace RootPairing

open TauCeti

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N] [Finite ι]
  {P : RootPairing ι ℚ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] {n : ℕ}

/-- **The Weyl group of type `Dₙ` has order `2ⁿ⁻¹ · n!`**, for every finite reduced
crystallographic root system over `ℚ` with a base of Cartan type `Dₙ`, `n ≥ 4`. -/
theorem card_weylGroup_of_hasCartanType_D (hn : 4 ≤ n) {b : P.Base}
    (h : HasCartanType P b (.D n)) :
    Nat.card P.weylGroup = 2 ^ (n - 1) * n.factorial := by
  obtain ⟨e⟩ := nonempty_weylGroup_mulEquiv_of_hasCartanType b
    ((DynkinType.D n).rationalBase (DynkinType.valid_D.mpr hn)) (.D n) h
    ((DynkinType.D n).hasCartanType_rationalRootSystem (DynkinType.valid_D.mpr hn))
  rw [Nat.card_congr (e.trans (DynkinType.typeDRationalWeylGroupEquiv n hn)).toEquiv,
    DynkinType.card_typeDWeylSubgroup (by omega)]

end RootPairing
