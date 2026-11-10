/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Reconstruction
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basis
public import TauCeti.RepresentationTheory.Finsupp
public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# The normal restriction of reconstructed Clifford representations

A basis of a right commutant module identifies its reconstructed representation,
restricted to the normal subgroup, with a direct sum of copies of the original
representation. In particular, when the original representation is simple, this
restriction is semisimple and isotypic, even for an infinite inertia quotient and
in modular characteristic. No averaging or scalar-Schur hypothesis is used.

The coefficient ring is the full categorical endomorphism ring. Its opposite acts
on the multiplicity module, as required by the inverse-factor crossed system.
The direct-sum coordinates are those of `Module.Basis.balancedTensorProductEquiv`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension
open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  {M : Type w} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

local notation "R" => forget₂ (FDRep k N) (Rep k N)
local notation "F" => (R) ⋙ forget₂ (Rep k N) (ModuleCat k)
local notation "V" => (Functor.obj (R) A : Rep k N)
local notation "recRep" => MonoidHom.comp (cliffordReconstructionRepresentation A s hs U)
  (Subgroup.inclusion (le_inertia A))

attribute [local instance] endModule

local instance : IsScalarTower k (End A) V := (F).endModule_isScalarTower A

/-- On restriction to the normal subgroup, a basis of the right commutant module
expresses reconstruction as the direct sum of copies of the original representation. -/
def cliffordReconstructionRestrictEquiv {ι : Type*} (b : Module.Basis ι (End A)ᵐᵒᵖ M) :
    Representation.Equiv recRep (Representation.finsupp (V).ρ ι) where
  toLinearEquiv := b.balancedTensorProductEquiv
  isIntertwining' n := by
    apply BalancedTensorProduct.hom_ext
    intro m x
    ext i
    simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
    erw [cliffordReconstructionRepresentation_inclusion_tmul,
      Module.Basis.balancedTensorProductEquiv_tmul_apply]
    rw [Representation.finsupp_apply_apply]
    erw [Module.Basis.balancedTensorProductEquiv_tmul_apply]
    -- The commutation equation uses the original FDRep carrier, whereas the tensor
    -- uses its forgotten carrier. `erw` applies the named equations across this view.
    erw [(F).endModule_smul A, (F).endModule_smul A]
    exact LinearMap.congr_fun (hom_hom_hom_comm (unop (b.repr m i)).asHom n) x

/-- The restriction comparison on pure tensors is given by right-module coordinates. -/
@[simp]
theorem cliffordReconstructionRestrictEquiv_tmul_apply {ι : Type*}
    (b : Module.Basis ι (End A)ᵐᵒᵖ M) (m : M) (x : V) (i : ι) :
    cliffordReconstructionRestrictEquiv A s hs U b
      (BalancedTensorProduct.tmul k (End A) m x) i = unop (b.repr m i) • x :=
  b.balancedTensorProductEquiv_tmul_apply m x i

/-- A vector supported at a single coordinate reconstructs its basis tensor. -/
@[simp]
theorem cliffordReconstructionRestrictEquiv_symm_single {ι : Type*}
    (b : Module.Basis ι (End A)ᵐᵒᵖ M) (i : ι) (x : V) :
    (cliffordReconstructionRestrictEquiv A s hs U b).symm (Finsupp.single i x) =
      BalancedTensorProduct.tmul k (End A) (b i) x :=
  b.balancedTensorProductEquiv_symm_single i x

/-- The group-algebra module of the normal restriction is a direct sum of copies of
`A`, with one copy for each right-commutant basis vector. -/
def cliffordReconstructionRestrictModuleEquiv {ι : Type*}
    (b : Module.Basis ι (End A)ᵐᵒᵖ M) :
    Representation.asModule recRep ≃ₗ[k[N]] (ι →₀ Representation.asModule A.ρ) := by
  simpa only [FDRep.forget₂_ρ] using!
    (TauCeti.Representation.asModuleLinearEquivOfEquiv
      (cliffordReconstructionRestrictEquiv A s hs U b)).trans
        (Representation.finsuppAsModuleEquiv (V).ρ ι)

/-- The module comparison evaluates by the same direct-sum coordinates. -/
@[simp]
theorem cliffordReconstructionRestrictModuleEquiv_apply {ι : Type*}
    (b : Module.Basis ι (End A)ᵐᵒᵖ M) (z : Representation.asModule recRep) (i : ι) :
    cliffordReconstructionRestrictModuleEquiv A s hs U b z i =
      (Representation.asModuleEquiv A.ρ).symm
        (cliffordReconstructionRestrictEquiv A s hs U b
          (Representation.asModuleEquiv recRep z) i) := by
  unfold cliffordReconstructionRestrictModuleEquiv
  -- Apply the coordinate lemmas across the FDRep/forgotten-carrier comparison.
  erw [LinearEquiv.trans_apply, Representation.finsuppAsModuleEquiv_apply,
    TauCeti.Representation.asModuleLinearEquivOfEquiv_apply, LinearEquiv.apply_symm_apply]

/-- A single module coordinate reconstructs the corresponding basis tensor. -/
@[simp]
theorem cliffordReconstructionRestrictModuleEquiv_symm_single {ι : Type*}
    (b : Module.Basis ι (End A)ᵐᵒᵖ M) (i : ι) (x : Representation.asModule A.ρ) :
    (cliffordReconstructionRestrictModuleEquiv A s hs U b).symm (Finsupp.single i x) =
      (Representation.asModuleEquiv recRep).symm
        (BalancedTensorProduct.tmul k (End A) (b i) (Representation.asModuleEquiv A.ρ x)) := by
  apply (cliffordReconstructionRestrictModuleEquiv A s hs U b).injective
  ext j
  rw [LinearEquiv.apply_symm_apply, cliffordReconstructionRestrictModuleEquiv_apply,
    LinearEquiv.apply_symm_apply]
  erw [← cliffordReconstructionRestrictEquiv_symm_single A s hs U b i,
    Representation.Equiv.apply_symm_apply]
  rfl

/-- Reconstruction of a simple normal-subgroup representation has semisimple
normal restriction. The multiplicity module may be infinite-dimensional. -/
theorem isSemisimpleModule_cliffordReconstruction_restrict [Simple A] :
    IsSemisimpleModule k[N] (Representation.asModule recRep) := by
  let b := Module.Free.chooseBasis (End A)ᵐᵒᵖ M
  exact .congr (cliffordReconstructionRestrictModuleEquiv A s hs U b)

/-- Reconstruction has only the prescribed simple normal-subgroup type. This also
includes the zero multiplicity module, whose reconstructed representation is zero. -/
theorem isIsotypicOfType_cliffordReconstruction_restrict [Simple A] :
    IsIsotypicOfType k[N] (Representation.asModule recRep)
      (Representation.asModule A.ρ) := by
  let b := Module.Free.chooseBasis (End A)ᵐᵒᵖ M
  exact (cliffordReconstructionRestrictModuleEquiv A s hs U b).isIsotypicOfType_iff.mpr
    ((IsIsotypicOfType.of_isSimpleModule k[N] (Representation.asModule A.ρ)).finsupp _)

end FDRep
