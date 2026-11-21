/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Closed

/-!
# Internal Hom in classical and degenerate almost setups

Internal Hom recovers the scalar ring on a classical rank-one module. For a
proper setup ideal, the residue module is nonzero before almostification but
has zero internal Hom into or out of its almostification. These checks also
exercise the tensor–Hom adjunction for modules that need not be finitely
generated or projective.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct
  TauCeti.Almost TauCeti.Almost.BasicSetup TauCeti.Almost.Module

universe u

variable {V : Type u} [CommRing V]

-- Classically, almost elements of the rank-one internal endomorphism object
-- recover the scalar ring, sending the identity almost element to `1`.
-- This fixes the comparison on a nonzero element whenever `V` is nontrivial.
-- Transport the identity along the public internal-Hom object equation.
example :
    ∃ e : (elements (classical V)).obj
        ((alHom (classical V) ((toAlmost (classical V)).obj (ModuleCat.of V V))).obj
          ((toAlmost (classical V)).obj (ModuleCat.of V V))) ≅ ModuleCat.of V V,
      ((elements (classical V)).map (eqToHom (alHom_obj (classical V)
        ((toAlmost (classical V)).obj (ModuleCat.of V V))
        ((toAlmost (classical V)).obj (ModuleCat.of V V))).symm) ≫ e.hom).hom
        (((adjElements (classical V)).unit.app
          (ModuleCat.of V ((toAlmost (classical V)).obj (ModuleCat.of V V) ⟶
            (toAlmost (classical V)).obj (ModuleCat.of V V)))).hom (𝟙 _)) = 1 := by
  let F := toAlmost (classical V)
  let e₀ : (ModuleCat.of V V ⟶ ModuleCat.of V V) ≃ₗ[V]
      (F.obj (ModuleCat.of V V) ⟶ F.obj (ModuleCat.of V V)) :=
    LinearEquiv.ofBijective (F.mapLinearMap V) ⟨F.map_injective, F.map_surjective⟩
  let e : (F.obj (ModuleCat.of V V) ⟶ F.obj (ModuleCat.of V V)) ≃ₗ[V] V :=
    e₀.symm ≪≫ₗ ModuleCat.homLinearEquiv (S := V) ≪≫ₗ LinearMap.ringLmapEquivSelf V V V
  let k := (asIso ((adjElements (classical V)).unit.app
    (ModuleCat.of V (F.obj (ModuleCat.of V V) ⟶ F.obj (ModuleCat.of V V))))).symm ≪≫
      e.toModuleIso
  let t := (elements (classical V)).mapIso
    (eqToIso (alHom_obj (classical V) (F.obj (ModuleCat.of V V))
      (F.obj (ModuleCat.of V V))))
  refine ⟨t ≪≫ k, ?_⟩
  change (t.inv ≫ (t.hom ≫ k.hom)).hom _ = 1
  rw [← Category.assoc, t.inv_hom_id, Category.id_comp]
  have h : e (F.map (𝟙 (ModuleCat.of V V))) = 1 := by
    -- Express the almost identity through the map defining the linear equivalence.
    change (LinearMap.ringLmapEquivSelf V V V)
      (ModuleCat.homLinearEquiv (S := V) (e₀.symm (e₀ (𝟙 (ModuleCat.of V V))))) = 1
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [F.map_id] at h
  exact (congrArg e (ModuleCat.inv_hom_apply
    (asIso ((adjElements (classical V)).unit.app
      (ModuleCat.of V (F.obj (ModuleCat.of V V) ⟶ F.obj (ModuleCat.of V V))))) (𝟙 _))).trans h

-- Internal Hom out of a zero object vanishes.
example (S : BasicSetup V) (M N : Module S) (hM : IsZero M) :
    IsZero ((alHom S M).obj N) := by
  have : Subsingleton (M ⟶ N) := ⟨fun f g ↦ hM.eq_of_src f g⟩
  rw [alHom_obj]
  exact (isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_of_subsingleton

-- The residue target is killed, even when the original residue module is nonzero.
example (S : BasicSetup V) (M : Module S) :
    IsZero ((alHom S M).obj ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal)))) :=
  (alHom S M).map_isZero ((isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_quotient)

-- The residue source is killed as well; this does not identify ordinary Hom
-- with almost Hom before almostification.
example (S : BasicSetup V) (N : Module S) :
    IsZero ((alHom S ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal)))).obj N) := by
  have h := (isZero_toAlmost_obj_iff S (ModuleCat.of V (V ⧸ S.ideal))).mpr
    S.isAlmostZero_quotient
  have : Subsingleton ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal)) ⟶ N) :=
    ⟨fun f g ↦ h.eq_of_src f g⟩
  rw [alHom_obj]
  exact (isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_of_subsingleton

-- Over the zero setup the entire internal Hom, including its almost elements,
-- vanishes, even over a nonzero base ring.
example (M N : Module (zero V)) :
    IsZero ((elements (zero V)).obj ((alHom (zero V) M).obj N)) := by
  rw [elements_obj]
  have : Subsingleton ((toAlmost (zero V)).obj (ModuleCat.of V V) ⟶
      (alHom (zero V) M).obj N) :=
    ⟨fun f g ↦ (isZero_of_ideal_eq_bot _ zero_ideal _).eq_of_tgt f g⟩
  exact ModuleCat.isZero_of_subsingleton _

-- Currying works for arbitrary almost modules, including infinite modules.
noncomputable example (S : BasicSetup V) (M N P : Module S) :
    (M ⊗ N ⟶ P) ≃ (N ⟶ (alHom S M).obj P) :=
  (alHomAdj S M).homEquiv N P

-- The right adjoint preserves products and all other limits; tensoring preserves
-- arbitrary colimits on both sides.
example (S : BasicSetup V) (M : Module S) :
    PreservesLimits (alHom S M) ∧ PreservesColimits (tensorLeft M) ∧
      PreservesColimits (tensorRight M) :=
  ⟨inferInstance, inferInstance,
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)⟩

-- This exercises the public almostification comparison on infinite free modules.
noncomputable example (S : BasicSetup V) :
    (alHom S ((toAlmost S).obj (ModuleCat.of V (ℕ →₀ V)))).obj
        ((toAlmost S).obj (ModuleCat.of V V)) ≅
      (toAlmost S).obj (ModuleCat.of V (S.tilde ⊗[V] (ℕ →₀ V) →ₗ[V] V)) :=
  alHomToAlmost S _ _
