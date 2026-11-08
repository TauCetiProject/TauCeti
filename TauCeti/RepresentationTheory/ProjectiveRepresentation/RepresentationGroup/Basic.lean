/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.ProjectiveRepresentation.Finite
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.RootsOfUnity
import TauCeti.RepresentationTheory.ProjectiveRepresentation.Torsion
import TauCeti.RingTheory.RootsOfUnity.Basic
public import TauCeti.GroupTheory.GroupExtension.Character.Basic
import TauCeti.FieldTheory.IsAlgClosed.Units
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Finite stem extensions with bijective character transgression

For a finite group over an algebraically closed field of arbitrary characteristic, construct a
finite central extension whose kernel lies in the commutator subgroup and whose character
transgression is bijective onto `H²(G, kˣ)`. Thus the character dual of the kernel is exactly
second cohomology, with no surplus kernel characters invisible to projective representations.

Decompose second cohomology into finite cyclic summands. Represent each cyclic generator
by a factor set taking values in roots of unity of its own order, and take their product.
Coordinate characters make transgression surjective; the kernel and second cohomology have
matching cardinalities, so transgression is also injective. The stem criterion then places
the kernel in the commutator subgroup. This supplies the finite extension underlying a
representation group; the universal lifting criterion applies to its surjective transgression.

The cyclic summands have orders nonzero in the field because second cohomology has no
torsion at the characteristic. Thus the kernel also has order prime to the characteristic,
even when the characteristic divides the order of the original group.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
* Mathlib's finite abelian structure theorem:
  `AddCommGroup.equiv_directSum_zmod_of_finite'`.
* The torsion representative theorem:
  `TauCeti.FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one`.
* The stem criterion:
  `TauCeti.FactorSet.characterTransgression_injective_iff_range_inl_le_commutator_of_rootableBy`.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

open scoped BigOperators

variable (k G : Type) [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- The second cohomology `H²(G, kˣ)` of a finite group has cyclic generators `x i` whose orders
`n i` are nonzero in `k`, and its cardinality is the product of the orders. -/
private theorem exists_cyclic_generators_schurMultiplier :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ)
      (x : ι → groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)),
      (∀ i, (n i : k) ≠ 0) ∧ (∀ i, n i • x i = 0) ∧
      (∀ y, ∃ c : ι → ℕ, y = ∑ i, c i • x i) ∧
      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) = ∏ i, n i := by
  classical
  -- Choose cyclic generators of second cohomology, each with its own annihilating order.
  let : Finite (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) :=
    inferInstanceAs (Finite (schurMultiplier k G))
  obtain ⟨ι, hι, n, hn, ⟨e₀⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite'
      (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ))
  let e := e₀.trans (DirectSum.addEquivProd (fun i ↦ ZMod (n i)))
  let x (i : ι) : groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ) := e.symm (Pi.single i 1)
  have hne : ∀ i, NeZero (n i) := fun i ↦ ⟨by have := hn i; omega⟩
  have horder (i : ι) : addOrderOf (x i) = n i := by
    dsimp only [x]
    rw [e.symm.addOrderOf_eq]
    simpa only [AddMonoidHom.single_apply, ZMod.addOrderOf_one] using
      addOrderOf_injective (AddMonoidHom.single (fun j ↦ ZMod (n j)) i)
        (by simpa only [AddMonoidHom.coe_single] using
          Pi.single_injective (M := fun j ↦ ZMod (n j)) i) (1 : ZMod (n i))
  have hx (i : ι) : n i • x i = 0 := horder i ▸ addOrderOf_nsmul_eq_zero (x i)
  refine ⟨ι, hι, n, x, fun i ↦ ?_, hx, fun y ↦ ⟨fun i ↦ (e y i).val, ?_⟩, ?_⟩
  · rw [← horder i]
    exact schurMultiplier_natCast_addOrderOf_ne_zero (x i) (horder i ▸ (hne i).out)
  · apply e.injective
    simp only [x]
    rw [map_sum e]
    simp_rw [map_nsmul e, AddEquiv.apply_symm_apply]
    simp only [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact (Finset.univ_sum_single (e y)).symm
  · rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    simp only [Nat.card_zmod]

omit [Finite G] in
/-- If elements `x i` killed by `n i`, with `n i` nonzero in `k`, generate `H²(G, kˣ)`, then some
factor set with values in `∏ i, μ_{n i}` has surjective character transgression. -/
private theorem exists_factorSet_surjective_characterTransgression {ι : Type} [Fintype ι]
    (n : ι → ℕ)
    (x : ι → groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) (hx : ∀ i, n i • x i = 0)
    (hgen : ∀ y, ∃ c : ι → ℕ, y = ∑ i, c i • x i) :
    ∃ α : FactorSet G (∀ i, rootsOfUnity (n i) k),
      Function.Surjective (α.characterTransgression (A := kˣ)) := by
  classical
  choose β hβ hpow using fun i ↦
    (FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one (x i)).mp (hx i)
  let γ (i : ι) : FactorSet G (rootsOfUnity (n i) k) :=
    ((β i).isFactorSet_curry trivialMulDistribMulAction_smul).toRootsOfUnityFactorSet
      (fun g h ↦ hpow i (g, h))
  -- Assemble their root-valued representatives into one central extension.
  let M := ∀ i, rootsOfUnity (n i) k
  let : MulDistribMulAction G M := trivialMulDistribMulAction G M
  -- Use the same action for characters and transgression: otherwise bare scalar-action
  -- inference on the function type M can select the pointwise Pi instance.
  let : SMul G M := (inferInstance : MulDistribMulAction G M).toMulAction.toSMul
  let α : FactorSet G M :=
    { toFun p i := γ i p
      isMulCocycle₂' g h j := by
        funext i
        exact (γ i).isMulCocycle₂ g h j
      map_one_one' := by
        funext i
        exact (γ i).map_one_one }
  have hα (p : G × G) (i : ι) : α p i = γ i p := rfl
  have hγ (i : ι) (p : G × G) : (γ i p : kˣ) = β i p :=
    IsFactorSet.coe_toRootsOfUnityFactorSet_apply _ _ p
  let ev (i : ι) : M →*[G] kˣ :=
    { (rootsOfUnity (n i) k).subtype.comp (Pi.evalMonoidHom _ i) with
      map_smul' _ _ := rfl }
  have hev (i : ι) (a : M) : ev i a = (a i : kˣ) := rfl
  let χ (i : ι) : Additive (equivariantCharacterSubgroup G M kˣ) :=
    Additive.ofMul ((equivariantCharacterEquiv G M kˣ).symm (ev i))
  have hχ (i : ι) : α.characterTransgression (χ i) = x i := by
    rw [FactorSet.characterTransgression_apply]
    have heq : α.map (equivariantCharacterEquiv G M kˣ (χ i).toMul) = β i := by
      ext p
      simp only [χ, toMul_ofMul, Equiv.apply_symm_apply, FactorSet.map_apply]
      simp only [hev, hα, hγ]
    rw [heq]
    exact hβ i
  -- Every cyclic generator is the transgression of its coordinate character.
  refine ⟨α, fun y ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hgen y
  exact ⟨∑ i, c i • χ i, by simp only [map_sum, map_nsmul, hχ]⟩

omit [Finite G] in
/-- When each `n i` is nonzero in `k`, the group of equivariant `kˣ`-valued characters of
`∏ i, μ_{n i}` has `∏ i, n i` elements. -/
private theorem natCard_additive_equivariantCharacterSubgroup_rootsOfUnity {ι : Type} [Fintype ι]
    (n : ι → ℕ) (hncast : ∀ i, (n i : k) ≠ 0) :
    Nat.card (Additive (equivariantCharacterSubgroup G (∀ i, rootsOfUnity (n i) k) kˣ)) =
      ∏ i, n i := by
  classical
  let hnroot (i : ι) : NeZero (n i : k) := ⟨hncast i⟩
  let M := ∀ i, rootsOfUnity (n i) k
  have hne (i : ι) : NeZero (n i) := .of_neZero_natCast k
  have : NeZero (Monoid.exponent M : k) := ⟨exponent_pi_rootsOfUnity_cast_ne_zero n hncast⟩
  let : MulDistribMulAction G M := trivialMulDistribMulAction G M
  have hcardM : Nat.card M = ∏ i, n i := by
    rw [Nat.card_pi]
    simp only [HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  let forget : equivariantCharacterSubgroup G M kˣ ≃ (M →* kˣ) :=
    Equiv.subtypeUnivEquiv fun f ↦
      (mem_equivariantCharacterSubgroup G M kˣ f).mpr fun _ _ ↦ rfl
  rw [Nat.card_congr Additive.toMul, Nat.card_congr forget,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, hcardM]

/-- Every finite group over an algebraically closed field has a finite
central stem extension with bijective character transgression. In particular, the character
dual of its kernel is `H²(G, kˣ)`. -/
theorem exists_finite_stem_factorSet_bijective_characterTransgression :
    ∃ (M : Type) (_ : CommGroup M) (_ : Finite M) (α : FactorSet G M),
      (FactorSet.rightHom α).ker ≤ Subgroup.center α.Extension ∧
      (FactorSet.rightHom α).ker ≤ commutator α.Extension ∧
      Function.Bijective (α.characterTransgression (A := kˣ)) := by
  classical
  obtain ⟨ι, hι, n, x, hncast, hx, hgen, hcardH⟩ := exists_cyclic_generators_schurMultiplier k G
  have hnroot (i : ι) : NeZero (n i : k) := ⟨hncast i⟩
  have hne (i : ι) : NeZero (n i) := .of_neZero_natCast k
  have : NeZero (Monoid.exponent (∀ i, rootsOfUnity (n i) k) : k) :=
    ⟨exponent_pi_rootsOfUnity_cast_ne_zero n hncast⟩
  obtain ⟨α, hsurj⟩ := exists_factorSet_surjective_characterTransgression k G n x hx hgen
  have hcard := natCard_additive_equivariantCharacterSubgroup_rootsOfUnity k G n hncast
  have hbij : Function.Bijective (α.characterTransgression (A := kˣ)) :=
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard.trans hcardH.symm⟩
  -- Injectivity of transgression forces the central kernel into the commutator subgroup.
  refine ⟨_, inferInstance, inferInstance, α, ?_, ?_, hbij⟩
  · rw [← FactorSet.range_inl_eq_ker_rightHom]
    exact α.inl_range_le_center trivialMulDistribMulAction_smul
  · rw [← FactorSet.range_inl_eq_ker_rightHom]
    exact (α.characterTransgression_injective_iff_range_inl_le_commutator_of_rootableBy
      trivialMulDistribMulAction_smul).mp hbij.injective

end TauCeti
