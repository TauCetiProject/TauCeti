/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator

/-!
# Weyl representatives at every root

On a Kostant-stable lattice, Steinberg's word
`n_α(s) = x_α(s) x_{-α}(-s⁻¹) x_α(s)` is defined for every numbered root and every
unit of the coefficient ring. Its value at one acts on all root subgroups by the
root reflection, with the sign of the pinned Chevalley system. These representatives
supply the root-reflection action needed to construct the Weyl group from root words.

The construction uses `chevalleyRootSubgroup` and the existing generic Kostant Weyl
conjugation theorem. Integrality of divided powers at every root permits applying
that theorem to the root generators alone; no additional lattice-stability assumption
is imposed. The argument is the all-root version of
`kostantWeylGL_conj_chevalleyRootSubgroup`, which concerns simple Weyl representatives.
All statements hold over arbitrary commutative rings, including characteristics two
and three and nonreduced rings.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19–20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra TensorProduct TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable {t : DynkinType} {ht : t.Valid}
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

-- Match the integral module structure used by the scalar-extension point API.
attribute [local instance high] Algebra.toModule

/-- Steinberg's root word at any numbered root, with the negative root given by
reflection of the root in itself. -/
def chevalleyWeylElement (α : Fin t.numRoots) (A : CommAlgCat ℤ) (s : Aˣ) :
    LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd (s : A)) *
    chevalleyRootSubgroup ρ M hM hnil ((t.simplyConnectedRootDatum ht).reflectionPerm α α)
      A (Multiplicative.ofAdd (-((s⁻¹ : Aˣ) : A))) *
    chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd (s : A))

/-- The three root factors of Steinberg's word. -/
theorem chevalleyWeylElement_def (α : Fin t.numRoots) (A : CommAlgCat ℤ) (s : Aˣ) :
    chevalleyWeylElement ρ M hM hnil α A s =
      chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd (s : A)) *
        chevalleyRootSubgroup ρ M hM hnil ((t.simplyConnectedRootDatum ht).reflectionPerm α α)
          A (Multiplicative.ofAdd (-((s⁻¹ : Aˣ) : A))) *
        chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd (s : A)) :=
  (rfl)

/-- At a simple root, this is the existing numbered Kostant root word. -/
@[simp]
theorem chevalleyWeylElement_simpleIndex (i : Fin t.rank) (A : CommAlgCat ℤ) (s : Aˣ) :
    chevalleyWeylElement ρ M hM hnil (t.simpleIndex ht i) A s =
      kostantWeylParam (t.lieBasis ht).rootGenerator (t.lieBasis ht).h ρ M hM
        (hnil (.inl i)) (hnil (.inr i)) A s := by
  simp only [chevalleyWeylElement_def, chevalleyRootSubgroup_simpleIndex,
    chevalleyRootSubgroup_reflectionPerm_simpleIndex, kostantWeylParam_def]

-- Only root divided powers are needed to apply the generic Weyl-conjugation theorem.
include hM hnil in
private theorem rootKostantStable :
    ∀ u ∈ kostantForm (t.chevalleySystem ht) (fun i : Empty => nomatch i),
      ∀ v ∈ M, ρ u v ∈ M := by
  intro u hu v hv
  exact kostantForm_apply_mem _ _ ρ (AddSubgroup.toIntSubmodule M)
    (fun α n v hv => by
      simpa only [Associative.map_dividedPower, Module.End.smul_def,
        ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule] using
        dividedPower_chevalleySystem_smul_mem ρ M hM hnil α n v hv)
    (fun i => nomatch i) u hu hv

private theorem rootKostantParam_eq (α : Fin t.numRoots) (A : CommAlgCat ℤ) :
    kostantRootSubgroupParam (t.chevalleySystem ht) (fun i : Empty => nomatch i)
        ρ M (rootKostantStable ρ M hM hnil) α
        (isNilpotent_apply_ι_chevalleySystem ρ hnil α) A =
      chevalleyRootSubgroup ρ M hM hnil α A := by
  refine MonoidHom.ext fun u => Units.ext <| LinearMap.ext fun z => ?_
  rw [kostantRootSubgroupParam_val_apply, chevalleyRootSubgroup_val]

private theorem chevalleyWeylElement_eq (α : Fin t.numRoots) (A : CommAlgCat ℤ) (s : Aˣ) :
    chevalleyWeylElement ρ M hM hnil α A s =
      kostantWeylParam (t.chevalleySystem ht) (fun i : Empty => nomatch i)
        ρ M (rootKostantStable ρ M hM hnil)
        (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
        (isNilpotent_apply_ι_chevalleySystem ρ hnil
          ((t.simplyConnectedRootDatum ht).reflectionPerm α α)) A s := by
  rw [kostantWeylParam_def, rootKostantParam_eq ρ M hM hnil,
    rootKostantParam_eq ρ M hM hnil, chevalleyWeylElement_def]

/-- Inversion negates the unit parameter of Steinberg's word. -/
@[simp]
theorem chevalleyWeylElement_inv (α : Fin t.numRoots) (A : CommAlgCat ℤ) (s : Aˣ) :
    (chevalleyWeylElement ρ M hM hnil α A s)⁻¹ =
      chevalleyWeylElement ρ M hM hnil α A (-s) := by
  simp only [chevalleyWeylElement_eq, kostantWeylParam_inv]

/-- Every root word lies in the elementary group generated by the numbered simple roots
and their negatives. -/
theorem chevalleyWeylElement_mem_kostantElementarySubgroup (α : Fin t.numRoots)
    (A : CommAlgCat ℤ) (s : Aˣ) :
    chevalleyWeylElement ρ M hM hnil α A s ∈
      kostantElementarySubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h ρ M hM hnil A := by
  exact mul_mem (mul_mem (chevalleyRootSubgroup_mem_kostantElementarySubgroup _ _ _ _ _ _ _)
    (chevalleyRootSubgroup_mem_kostantElementarySubgroup _ _ _ _ _ _ _))
    (chevalleyRootSubgroup_mem_kostantElementarySubgroup _ _ _ _ _ _ _)

/-- Root words commute with extension of the coefficient ring. -/
theorem mapScalarExtensionAutomorphisms_chevalleyWeylElement (α : Fin t.numRoots)
    {A B : CommAlgCat ℤ} (φ : A ⟶ B) (s : Aˣ) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := M) φ
        (chevalleyWeylElement ρ M hM hnil α A s) =
      chevalleyWeylElement ρ M hM hnil α B (Units.map (φ.hom : A →* B) s) := by
  rw [chevalleyWeylElement_eq, chevalleyWeylElement_eq]
  exact mapScalarExtensionAutomorphisms_kostantWeylParam _ _ ρ M
    (rootKostantStable ρ M hM hnil) _ _ φ s

/-- The Weyl representative at any root acts on every root subgroup by reflection, with
exactly the sign determined by the pinned Chevalley system. -/
theorem chevalleyWeylElement_conj_chevalleyRootSubgroup (α β : Fin t.numRoots)
    (A : CommAlgCat ℤ) (u : A) :
    chevalleyWeylElement ρ M hM hnil α A 1 *
        chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd u) *
        (chevalleyWeylElement ρ M hM hnil α A 1)⁻¹ =
      chevalleyRootSubgroup ρ M hM hnil
        ((t.simplyConnectedRootDatum ht).reflectionPerm α β) A
        (Multiplicative.ofAdd (((t.chevalleyWeylSign ht α β : ℤ) : A) * u)) := by
  rw [chevalleyWeylElement_eq, kostantWeylParam_one]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, kostantWeylGL_val, kostantWeylGL_inv_val,
    chevalleyRootSubgroup_val, chevalleyRootSubgroup_val,
    toAdd_ofAdd, toAdd_ofAdd,
    kostantWeylPoints_conj_baseChangeExp_weylAut _ _ ρ M (rootKostantStable ρ M hM hnil)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil _)
      (t.isSl2Triple_chevalleySystem ht α)
      (t.isNilpotent_ad_chevalleySystem ht α).exists_pow_apply_eq_zero
      (t.isNilpotent_ad_chevalleySystem ht _).exists_pow_apply_eq_zero
      (dividedPower_chevalleySystem_smul_mem ρ M hM hnil β)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil β)]
  have hw := congrArg (fun z => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z))
    (t.weylAut_chevalleySystem ht α β)
  simp only [map_zsmul] at hw
  have hsign : ∀ n, ∀ v ∈ M, Associative.dividedPower n
      ((t.chevalleyWeylSign ht α β : ℤ) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm α β)))) • v ∈ M := by
    intro n v hv
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (dividedPower_chevalleySystem_smul_mem ρ M hM hnil _ n v hv) _
  exact (baseChangeExp_congr hw M _ hsign u).trans
    (baseChangeExp_zsmul _ M (dividedPower_chevalleySystem_smul_mem ρ M hM hnil _) hsign
      (isNilpotent_apply_ι_chevalleySystem ρ hnil _) u)

end

end TauCeti.DynkinType
