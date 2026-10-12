/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.ProjectiveRepresentation.Finite
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.RootsOfUnity
public import TauCeti.GroupTheory.GroupExtension.Character.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Finite stem extensions with bijective character transgression

For a finite group over an algebraically closed field of characteristic zero, construct a
finite central extension whose kernel lies in the commutator subgroup and whose character
transgression is bijective onto `H²(G, kˣ)`. Thus the character dual of the kernel is exactly
second cohomology, with no surplus kernel characters invisible to projective representations.

Decompose second cohomology into finite cyclic summands. Represent each cyclic generator
by a factor set taking values in roots of unity of its own order, and take their product.
Coordinate characters make transgression surjective; the kernel and second cohomology have
matching cardinalities, so transgression is also injective. The stem criterion then places
the kernel in the commutator subgroup. This supplies the finite extension underlying a
representation group; the universal lifting criterion applies to its surjective transgression.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
* Mathlib's finite abelian structure theorem:
  `AddCommGroup.equiv_directSum_zmod_of_finite'`.
* The torsion representative theorem:
  `TauCeti.FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one`.
* The stem criterion:
  `TauCeti.FactorSet.characterTransgression_injective_iff_range_inl_le_commutator_of_isAlgClosed`.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

open scoped BigOperators

variable (k G : Type) [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Finite G]

/-- Every finite group over an algebraically closed characteristic-zero field has a finite
central stem extension with bijective character transgression. In particular, the character
dual of its kernel is `H²(G, kˣ)`. -/
theorem exists_finite_stem_factorSet_bijective_characterTransgression :
    ∃ (M : Type) (_ : CommGroup M) (_ : Finite M) (α : FactorSet G M),
      (FactorSet.rightHom α).ker ≤ Subgroup.center α.Extension ∧
      (FactorSet.rightHom α).ker ≤ commutator α.Extension ∧
      Function.Bijective (α.characterTransgression (A := kˣ)) := by
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
  have hx (i : ι) : n i • x i = 0 := by
    apply e.injective
    simp [x, ← Pi.single_smul, nsmul_eq_mul]
  choose β hβ hpow using fun i ↦
    (FactorSet.nsmul_eq_zero_iff_exists_factorSet_pow_eq_one (x i)).mp (hx i)
  let γ (i : ι) : FactorSet G (rootsOfUnity (n i) k) :=
    ((β i).isFactorSet_curry trivialMulDistribMulAction_smul).toRootsOfUnityFactorSet
      (fun g h ↦ hpow i (g, h))
  -- Assemble their root-valued representatives into one central extension.
  let M := ∀ i, rootsOfUnity (n i) k
  let : MulDistribMulAction G M := trivialMulDistribMulAction G M
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
  have hsurj : Function.Surjective (α.characterTransgression (A := kˣ)) := by
    intro y
    refine ⟨∑ i, (e y i).val • χ i, ?_⟩
    simp only [map_sum, map_nsmul, hχ]
    apply e.injective
    simp only [x]
    rw [map_sum e]
    simp_rw [map_nsmul e, AddEquiv.apply_symm_apply]
    simp only [← Pi.single_smul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact Finset.univ_sum_single (e y)
  -- There are exactly as many kernel characters as cohomology classes.
  have hcardM : Nat.card M = Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi, Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card, ZMod.card]
  let forget : equivariantCharacterSubgroup G M kˣ ≃ (M →* kˣ) :=
    { toFun := Subtype.val
      invFun f := ⟨f, (mem_equivariantCharacterSubgroup G M kˣ f).mpr (fun _ _ ↦ rfl)⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hcard : Nat.card (Additive (equivariantCharacterSubgroup G M kˣ)) =
      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)) := by
    rw [Nat.card_congr Additive.toMul, Nat.card_congr forget,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, hcardM]
  have hbij : Function.Bijective (α.characterTransgression (A := kˣ)) :=
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩
  -- Injectivity of transgression forces the central kernel into the commutator subgroup.
  refine ⟨M, inferInstance, inferInstance, α, ?_, ?_, hbij⟩
  · rw [← FactorSet.range_inl_eq_ker_rightHom]
    exact α.inl_range_le_center trivialMulDistribMulAction_smul
  · rw [← FactorSet.range_inl_eq_ker_rightHom]
    exact (α.characterTransgression_injective_iff_range_inl_le_commutator_of_isAlgClosed).mp
      hbij.injective

end TauCeti
