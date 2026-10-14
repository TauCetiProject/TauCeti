/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Associator

/-!
# Associativity of balanced DG tensor products

For a right DG `B`-module `M`, a DG `(B,C)`-bimodule `N`, and a left DG `C`-module `P`,
reassociation identifies `(M ⊗_B N) ⊗_C P` with `M ⊗_B (N ⊗_C P)` as cochain complexes.
The carrier map is the balanced associator and has degree zero. It commutes with the
three-term tensor differential: the last term has sign `(-1)^(|m|+|n|)` in either
parenthesization. No flatness is needed for these underived tensor products.

Both the algebraic statements and the complex isomorphism permit independent carrier universes.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open CategoryTheory MulOpposite DirectSum

namespace TauCeti.BalancedTensorProduct

section Algebraic

variable {R B C M N P : Type*} [CommRing R] [Ring B] [Ring C]
  [Algebra R B] [Algebra R C]
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module B N] [Module Cᵐᵒᵖ N]
  [IsScalarTower R B N] [IsScalarTower R Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module C P] [IsScalarTower R C P]
  {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [Decomposition ℳ] [Decomposition 𝒩] [Decomposition ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul ℬ 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece 𝒩]
  [SetLike.GradedSMul 𝒞 ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  (hM : IsDGRightModule hB ℳ dM) (hN : IsDGBimodule hB hC 𝒩 dN)
  (hP : IsDGLeftModule hC ℳP dP)

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower

local notation "G" => InternalGrading.ofDecomposition ℳ
local notation "H" => InternalGrading.ofDecomposition 𝒩
local notation "GMN" => grading (𝒜 := ℬ) G H

attribute [local instance] tensorGradedRight tensorGradedLeft
  tensorGradedOuterLeft tensorGradedOuterRight

local notation "DL" => differential (isDGRightModule_tensorProduct hM hN) hP
local notation "DR" => differential hM (isDGLeftModule_tensorProduct hN hP)

/-- The balanced associator commutes with the signed tensor differentials. -/
@[simp]
theorem assoc_comp_differential :
    assoc.toLinearMap ∘ₗ DL = DR ∘ₗ assoc.toLinearMap := by
  apply hom_ext
  intro x p
  induction x using induction_on with
  | ht m n =>
    induction m using Decomposition.inductionOn ℳ with
    | zero => simp
    | add m m' hm hm' => simp [add_tmul, map_add, hm, hm']
    | @homogeneous q m =>
      induction n using Decomposition.inductionOn 𝒩 with
      | zero => simp
      | add n n' hn hn' => simp [tmul_add, add_tmul, map_add, hn, hn']
      | @homogeneous r n =>
        have hmn : tmul R B (m : M) (n : N) ∈ (GMN).piece (q + r) :=
          tmul_mem_grading G H (by simpa only [InternalGrading.ofDecomposition_piece] using m.2)
            (by simpa only [InternalGrading.ofDecomposition_piece] using n.2)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [differential_tmul_of_mem _ hP hmn,
          differential_tmul_of_mem hM hN.toIsDGLeftModule m.2,
          assoc_tmul, differential_tmul_of_mem hM _ m.2,
          differential_tmul_of_mem hN.isDGRightModule hP n.2]
        simp only [add_tmul, tmul_add, smul_tmul, tmul_smul, map_add, map_smul,
          assoc_tmul, Int.negOnePow_add, Units.val_mul, Int.cast_mul, smul_add, smul_smul]
        module
  | ha x y hx hy => simp [add_tmul, map_add, hx, hy]

/-- Reassociating a tensor and then differentiating gives the same result as differentiating
before reassociation. -/
@[simp]
theorem assoc_differential (x : BalancedTensorProduct R C (BalancedTensorProduct R B M N) P) :
    assoc (DL x) = DR (assoc x) :=
  LinearMap.congr_fun (assoc_comp_differential hM hN hP) x

/-- Inverse reassociation also commutes with the tensor differentials. -/
@[simp]
theorem assoc_symm_comp_differential :
    assoc.symm.toLinearMap ∘ₗ DR = DL ∘ₗ assoc.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply assoc.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [assoc_differential hM hN hP, LinearEquiv.apply_symm_apply]

/-- Inverse reassociation intertwines differentiation on individual tensors. -/
@[simp]
theorem assoc_symm_differential (x : BalancedTensorProduct R B M
    (BalancedTensorProduct R C N P)) :
    assoc.symm (DR x) = DL (assoc.symm x) :=
  LinearMap.congr_fun (assoc_symm_comp_differential hM hN hP) x

end Algebraic

section Complex

universe uM uN uP

variable {R B C : Type*} [CommRing R] [Ring B] [Ring C]
  [Algebra R B] [Algebra R C]
  {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module B N] [Module Cᵐᵒᵖ N]
  [IsScalarTower R B N] [IsScalarTower R Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module C P] [IsScalarTower R C P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [Decomposition ℳ] [Decomposition 𝒩] [Decomposition ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul ℬ 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece 𝒩]
  [SetLike.GradedSMul 𝒞 ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  (hM : IsDGRightModule hB ℳ dM) (hN : IsDGBimodule hB hC 𝒩 dN)
  (hP : IsDGLeftModule hC ℳP dP)

local notation "G" => InternalGrading.ofDecomposition ℳ
local notation "H" => InternalGrading.ofDecomposition 𝒩
local notation "I" => InternalGrading.ofDecomposition ℳP
local notation "GMN" => grading (𝒜 := ℬ) G H
local notation "GNP" => grading (𝒜 := 𝒞) H I
attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
attribute [local instance] tensorGradedRight tensorGradedLeft
  tensorGradedOuterLeft tensorGradedOuterRight

local notation "GL" => grading (𝒜 := 𝒞)
  (InternalGrading.ofDecomposition (InternalGrading.piece GMN)) I
local notation "GR" => grading (𝒜 := ℬ) G
  (InternalGrading.ofDecomposition (InternalGrading.piece GNP))
local notation "KL" => cochainComplex (isDGRightModule_tensorProduct hM hN) hP
local notation "KR" => cochainComplex hM (isDGLeftModule_tensorProduct hN hP)

omit [IsScalarTower R Bᵐᵒᵖ M] [IsScalarTower R C P] in
private theorem assoc_map_piece (p : ℤ) :
    ((GL).piece p).map assoc.toLinearMap = (GR).piece p := by
  have hMN : InternalGrading.ofDecomposition (GMN).piece = GMN :=
    InternalGrading.ext fun p ↦ congrFun (InternalGrading.ofDecomposition_piece _) p
  have hNP : InternalGrading.ofDecomposition (GNP).piece = GNP :=
    InternalGrading.ext fun p ↦ congrFun (InternalGrading.ofDecomposition_piece _) p
  simpa only [hMN, hNP] using map_assoc_grading_piece G H I p

private noncomputable def assocDegreeIso (p : ℤ) : (KL).X p ≅ (KR).X p :=
  eqToIso (cochainComplex_X _ _ p) ≪≫
    (LinearEquiv.ofSubmodules assoc ((GL).piece p) ((GR).piece p)
      (assoc_map_piece p)).toModuleIso ≪≫ (eqToIso (cochainComplex_X _ _ p)).symm

-- Cancel the degree-piece transports here, keeping their implementation out of the
-- complex-level evaluation formulas.
private theorem assocDegreeIso_hom_apply (p : ℤ) (x : (GL).piece p) :
    (eqToHom (cochainComplex_X hM (isDGLeftModule_tensorProduct hN hP) p)
      ((assocDegreeIso hM hN hP p).hom
        ((eqToHom (cochainComplex_X (isDGRightModule_tensorProduct hM hN) hP p).symm) x)) :
      BalancedTensorProduct R B M (BalancedTensorProduct R C N P)) = assoc x := by
  simp only [assocDegreeIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
    ← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.ofSubmodules_apply]

private theorem assocDegreeIso_inv_apply (p : ℤ) (x : (GR).piece p) :
    (eqToHom (cochainComplex_X (isDGRightModule_tensorProduct hM hN) hP p)
      ((assocDegreeIso hM hN hP p).inv
        ((eqToHom (cochainComplex_X hM (isDGLeftModule_tensorProduct hN hP) p).symm) x)) :
      BalancedTensorProduct R C (BalancedTensorProduct R B M N) P) = assoc.symm x := by
  simp only [assocDegreeIso, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, eqToIso.hom,
    ← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.ofSubmodules_symm_apply]

/-- The balanced associator identifies the two parenthesizations of the ordinary DG tensor
product as cochain complexes. On every degree piece it is the carrier reassociation map. -/
noncomputable def cochainComplexAssoc : KL ≅ KR :=
  HomologicalComplex.Hom.isoOfComponents (assocDegreeIso hM hN hP) (by
    intro p q hpq
    rw [ComplexShape.up_Rel] at hpq
    subst q
    simp only [assocDegreeIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
      cochainComplex_d, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    simp only [← Category.assoc, cancel_mono]
    simp only [Category.assoc, cancel_epi]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.coe_restrict_apply, LinearEquiv.toModuleIso_hom,
      LinearEquiv.coe_coe, LinearEquiv.ofSubmodules_apply] using
        (assoc_differential hM hN hP x).symm)

/-- Under the canonical degree-piece identifications, forward reassociation changes only
parentheses. -/
@[simp]
theorem cochainComplexAssoc_hom_f_apply (p : ℤ) (x : (GL).piece p) :
    (eqToHom (cochainComplex_X hM (isDGLeftModule_tensorProduct hN hP) p)
      ((cochainComplexAssoc hM hN hP).hom.f p
        ((eqToHom (cochainComplex_X (isDGRightModule_tensorProduct hM hN) hP p).symm) x)) :
      BalancedTensorProduct R B M (BalancedTensorProduct R C N P)) = assoc x := by
  simpa only [cochainComplexAssoc, HomologicalComplex.Hom.isoOfComponents_hom_f] using
    assocDegreeIso_hom_apply hM hN hP p x

/-- Under the canonical degree-piece identifications, inverse reassociation restores the
original parentheses. -/
@[simp]
theorem cochainComplexAssoc_inv_f_apply (p : ℤ) (x : (GR).piece p) :
    (eqToHom (cochainComplex_X (isDGRightModule_tensorProduct hM hN) hP p)
      ((cochainComplexAssoc hM hN hP).inv.f p
        ((eqToHom (cochainComplex_X hM (isDGLeftModule_tensorProduct hN hP) p).symm) x)) :
      BalancedTensorProduct R C (BalancedTensorProduct R B M N) P) = assoc.symm x := by
  simpa only [cochainComplexAssoc, HomologicalComplex.Hom.isoOfComponents_inv_f] using
    assocDegreeIso_inv_apply hM hN hP p x

end Complex

end TauCeti.BalancedTensorProduct
