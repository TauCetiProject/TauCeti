/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Unit

/-!
# Unit isomorphisms for balanced DG tensor complexes

The regular DG bimodule is a unit for the ordinary balanced tensor product. The action maps
`A ⊗_A N → N` and `M ⊗_A A → M` preserve degree and commute with differentials, so they
identify the tensor complexes with the underlying module complexes. The inverse maps insert
`1`, whose degree is zero and whose differential vanishes.

The algebra and module carriers may have independent universes. The target complex is lifted
to the universe of the tensor product. This is only a universe lift: the forward components
are the action maps and the inverse components are insertion of `1`. These are underived
isomorphisms and require no flatness hypothesis.

## Main definitions

* `cochainComplexLid`: tensoring the regular right DG module with a left DG module returns it.
* `cochainComplexRid`: tensoring a right DG module with the regular left module returns it.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti.BalancedTensorProduct

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA}

section Left

variable {N : Type uM} [AddCommGroup N] [Module R N] [Module A N]
  [IsScalarTower R A N] {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
  {dN : N →ₗ[R] N} (hN : IsDGLeftModule hA 𝒩 dN)

local notation "G" => InternalGrading.ofDecomposition 𝒩
local notation "T" => grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition 𝒜) G
local notation "K" => cochainComplex hA.isDGRightModule hN

attribute [local instance] tensorGradedRight tensorGradedLeft

-- The degree-piece isomorphisms and differential compatibility proofs below adapt the
-- formalization pattern of `cochainComplexAssoc` in
-- `TauCeti/Algebra/Homology/DG/Module/TensorProduct/Associator.lean`.
private noncomputable def lidDegreeIso (p : ℤ) :
    (K).X p ≅ (gradedCochainComplexLift.{uR, uM, uA} 𝒩 dN
      hN.isHomogeneous (fun _ x ↦ hN.sq_zero x)).X p :=
  eqToIso (cochainComplex_X _ _ p) ≪≫
    ((LinearEquiv.ofSubmodules (lid R A N) ((T).piece p) (𝒩 p)
      (by simpa only [InternalGrading.ofDecomposition_piece] using
        map_lid_grading_piece (𝒜 := 𝒜) G p)).trans
          ULift.moduleEquiv.symm).toModuleIso ≪≫
    (eqToIso (gradedCochainComplexLift_X.{uR, uM, uA}
      (hdeg := hN.isHomogeneous) (hsq := fun _ x ↦ hN.sq_zero x) p)).symm

/-- The left regular-module action is an isomorphism from the balanced tensor complex
onto the underlying module complex, lifted to the tensor product's universe. -/
noncomputable def cochainComplexLid : K ≅
    gradedCochainComplexLift.{uR, uM, uA} 𝒩 dN
      hN.isHomogeneous (fun _ x ↦ hN.sq_zero x) :=
  HomologicalComplex.Hom.isoOfComponents (lidDegreeIso hN) (by
    intro p q hpq
    rw [ComplexShape.up_Rel] at hpq
    subst q
    simp only [lidDegreeIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
      cochainComplex_d, gradedCochainComplexLift_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simp only [← Category.assoc, cancel_mono]
    simp only [Category.assoc, cancel_epi]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.toModuleIso_hom, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply]
    -- Evaluate the universe-lift equivalence; the remaining maps are restricted actions.
    simp only [ULift.moduleEquiv, LinearEquiv.symm, LinearMap.inverse,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, ULift.down_up]
    simp only [LinearMap.coe_restrict_apply, LinearEquiv.ofSubmodules_apply]
    exact (LinearMap.congr_fun (lid_comp_differential hA hN) x).symm)

/-- On a homogeneous tensor, the forward unit isomorphism is the left action map. -/
-- Use `rw`: simplification of concrete-category coercions prevents `simp` matching this formula.
theorem cochainComplexLid_hom_f_apply (p : ℤ) (x : (T).piece p) :
    (eqToHom (gradedCochainComplexLift_X.{uR, uM, uA}
      (hdeg := hN.isHomogeneous) (hsq := fun _ x ↦ hN.sq_zero x) p)
      ((cochainComplexLid hN).hom.f p
        ((eqToHom (cochainComplex_X hA.isDGRightModule hN p).symm) x))).down.val =
      lid R A N x := by
  simp only [cochainComplexLid, HomologicalComplex.Hom.isoOfComponents_hom_f,
    lidDegreeIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
    ← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  -- The universe lift inserts `ULift.up`, which is cancelled by `down`.
  simp only [ULift.moduleEquiv, LinearEquiv.symm, LinearMap.inverse,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, ULift.down_up]
  exact LinearEquiv.ofSubmodules_apply _ _ _

/-- On a homogeneous module element, the inverse unit isomorphism inserts the algebra unit. -/
-- Use `rw`: simplification of concrete-category coercions prevents `simp` matching this formula.
theorem cochainComplexLid_inv_f_apply (p : ℤ) (x : 𝒩 p) :
    (eqToHom (cochainComplex_X hA.isDGRightModule hN p)
      ((cochainComplexLid hN).inv.f p
        ((eqToHom (gradedCochainComplexLift_X.{uR, uM, uA}
          (hdeg := hN.isHomogeneous) (hsq := fun _ x ↦ hN.sq_zero x) p).symm) (ULift.up x))) :
      BalancedTensorProduct R A A N) =
        tmul R A 1 (x : N) := by
  simp only [cochainComplexLid, HomologicalComplex.Hom.isoOfComponents_inv_f,
    lidDegreeIso, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, eqToIso.hom,
    ← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofSubmodules_symm_apply, lid_symm_apply, LinearEquiv.symm_symm]
  -- The inverse lift removes `ULift.up`; both sides are then the same pure tensor.
  rfl

end Left

section Right

variable {M : Type uM} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
  [IsScalarTower R Aᵐᵒᵖ M] {ℳ : ℤ → Submodule R M}
  [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {dM : M →ₗ[R] M} (hM : IsDGRightModule hA ℳ dM)

local notation "G" => InternalGrading.ofDecomposition ℳ
local notation "T" => grading (𝒜 := 𝒜) G (InternalGrading.ofDecomposition 𝒜)
local notation "K" => cochainComplex hM hA.isDGLeftModule

attribute [local instance] tensorGradedRight tensorGradedLeft

private noncomputable def ridDegreeIso (p : ℤ) :
    (K).X p ≅ (gradedCochainComplexLift.{uR, uM, uA} ℳ dM
      hM.isHomogeneous (fun _ x ↦ hM.sq_zero x)).X p :=
  eqToIso (cochainComplex_X _ _ p) ≪≫
    ((LinearEquiv.ofSubmodules (rid R A M) ((T).piece p) (ℳ p)
      (by simpa only [InternalGrading.ofDecomposition_piece] using
        map_rid_grading_piece (𝒜 := 𝒜) G p)).trans
          ULift.moduleEquiv.symm).toModuleIso ≪≫
    (eqToIso (gradedCochainComplexLift_X.{uR, uM, uA}
      (hdeg := hM.isHomogeneous) (hsq := fun _ x ↦ hM.sq_zero x) p)).symm

/-- The right regular-module action is an isomorphism from the balanced tensor complex
onto the underlying module complex, lifted to the tensor product's universe. -/
noncomputable def cochainComplexRid : K ≅
    gradedCochainComplexLift.{uR, uM, uA} ℳ dM
      hM.isHomogeneous (fun _ x ↦ hM.sq_zero x) :=
  HomologicalComplex.Hom.isoOfComponents (ridDegreeIso hM) (by
    intro p q hpq
    rw [ComplexShape.up_Rel] at hpq
    subst q
    simp only [ridDegreeIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
      cochainComplex_d, gradedCochainComplexLift_d, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simp only [← Category.assoc, cancel_mono]
    simp only [Category.assoc, cancel_epi]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.toModuleIso_hom, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply]
    -- Evaluate the universe-lift equivalence; the remaining maps are restricted actions.
    simp only [ULift.moduleEquiv, LinearEquiv.symm, LinearMap.inverse,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, ULift.down_up]
    simp only [LinearMap.coe_restrict_apply, LinearEquiv.ofSubmodules_apply]
    exact (LinearMap.congr_fun (rid_comp_differential hA hM) x).symm)

/-- On a homogeneous tensor, the forward unit isomorphism is the right action map. -/
-- Use `rw`: simplification of concrete-category coercions prevents `simp` matching this formula.
theorem cochainComplexRid_hom_f_apply (p : ℤ) (x : (T).piece p) :
    (eqToHom (gradedCochainComplexLift_X.{uR, uM, uA}
      (hdeg := hM.isHomogeneous) (hsq := fun _ x ↦ hM.sq_zero x) p)
      ((cochainComplexRid hM).hom.f p
        ((eqToHom (cochainComplex_X hM hA.isDGLeftModule p).symm) x))).down.val =
      rid R A M x := by
  simp only [cochainComplexRid, HomologicalComplex.Hom.isoOfComponents_hom_f,
    ridDegreeIso, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv,
    ← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  -- The universe lift inserts `ULift.up`, which is cancelled by `down`.
  simp only [ULift.moduleEquiv, LinearEquiv.symm, LinearMap.inverse,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, ULift.down_up]
  exact LinearEquiv.ofSubmodules_apply _ _ _

/-- On a homogeneous module element, the inverse unit isomorphism inserts the algebra unit. -/
-- Use `rw`: simplification of concrete-category coercions prevents `simp` matching this formula.
theorem cochainComplexRid_inv_f_apply (p : ℤ) (x : ℳ p) :
    (eqToHom (cochainComplex_X hM hA.isDGLeftModule p)
      ((cochainComplexRid hM).inv.f p
        ((eqToHom (gradedCochainComplexLift_X.{uR, uM, uA}
          (hdeg := hM.isHomogeneous) (hsq := fun _ x ↦ hM.sq_zero x) p).symm) (ULift.up x))) :
      BalancedTensorProduct R A M A) =
        tmul R A (x : M) 1 := by
  simp only [cochainComplexRid, HomologicalComplex.Hom.isoOfComponents_inv_f,
    ridDegreeIso, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, eqToIso.hom,
    ← CategoryTheory.comp_apply, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofSubmodules_symm_apply, rid_symm_apply, LinearEquiv.symm_symm]
  -- The inverse lift removes `ULift.up`; both sides are then the same pure tensor.
  rfl

end Right

end TauCeti.BalancedTensorProduct
