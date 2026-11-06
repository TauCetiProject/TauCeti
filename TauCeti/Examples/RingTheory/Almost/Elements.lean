/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Elements

/-!
# Examples of almost elements and the left adjoint `(−)_!`

The unit `V → (V^a)_*` sends a scalar to the corresponding multiple of the identity of `V^a`.
For the classical setup the unit is an isomorphism, while for a proper ideal it is not even
injective on the almost zero residue module `V ⧸ m`. For the zero setup every module of almost
elements vanishes. The left adjoint sends `V^a` to `m~`, not to `V`, and its counit is the
action map.
-/

open CategoryTheory Limits TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup
  TauCeti.Almost.Module

universe u

variable {V : Type u} [CommRing V]

-- The unit `V → (V^a)_* = Hom(V^a, V^a)` sends `r` to `r • 𝟙`.
example (S : BasicSetup V) (r : V) :
    dsimp% only [Functor.id_obj, Functor.comp_obj]
      ((adjElements S).unit.app (ModuleCat.of V V)).hom r =
      (r • 𝟙 _ : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj (ModuleCat.of V V)) := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton V V r) = r • 𝟙 (ModuleCat.of V V) := by
    ext
    simp
  rw [adjElements_unit_app_apply, h, Functor.map_smul, CategoryTheory.Functor.map_id]

-- For the classical setup `(V, V)`, the unit `N → (N^a)_*` is an isomorphism.
example (N : ModuleCat.{u} V) : IsIso ((adjElements (classical V)).unit.app N) :=
  inferInstance

-- For a proper ideal, the unit is not injective on the almost zero module `V ⧸ m`.
example (S : BasicSetup V) (hS : S.ideal ≠ ⊤) :
    ¬ Function.Injective ((adjElements S).unit.app (ModuleCat.of V (V ⧸ S.ideal))).hom := by
  intro h
  have hz : IsZero ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal))) :=
    (isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_quotient
  have h1 : Ideal.Quotient.mk S.ideal 1 = 0 :=
    h (hz.eq_of_tgt _ _)
  exact hS ((Ideal.eq_top_iff_one S.ideal).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1))

-- For the zero setup `(V, 0)`, every module of almost elements is zero.
example (M : Module (zero V)) : Subsingleton ((elements (zero V)).obj M) :=
  ⟨fun f g ↦ (isZero_of_ideal_eq_bot (zero V) zero_ideal M).eq_of_tgt f g⟩

-- The left adjoint sends `V^a` to `m~ ⊗[V] V ≅ m~`.
noncomputable example (S : BasicSetup V) :
    (shriek S).obj ((toAlmost S).obj (ModuleCat.of V V)) ≅ ModuleCat.of V S.tilde :=
  (toAlmostCompShriekIso S).app _ ≪≫ (TensorProduct.rid V S.tilde).toModuleIso

-- Over the zero setup on a nontrivial ring, `(V^a)_!` is zero although `V` is not, so the
-- counit `(V^a)_! → V` is not an isomorphism.
example [Nontrivial V] : ¬ IsIso ((adjShriek (zero V)).counit.app (ModuleCat.of V V)) := by
  intro h
  have hz : IsZero ((shriek (zero V)).obj ((toAlmost (zero V)).obj (ModuleCat.of V V))) :=
    (shriek (zero V)).map_isZero (isZero_of_ideal_eq_bot (zero V) zero_ideal _)
  have := congrArg (fun f : ModuleCat.of V V ⟶ ModuleCat.of V V ↦ f.hom 1)
    ((hz.of_iso (asIso ((adjShriek (zero V)).counit.app (ModuleCat.of V V))).symm).eq_of_src
      (𝟙 _) 0)
  simp at this

-- Under `(N^a)_! ≅ m~ ⊗[V] N`, the counit is the action map: over the classical setup on `ℤ`,
-- it sends `(2 ⊗ 3) ⊗ 5` to `30`.
example : ((toAlmostCompShriekIso (classical ℤ)).inv.app (ModuleCat.of ℤ ℤ) ≫
    (adjShriek (classical ℤ)).counit.app (ModuleCat.of ℤ ℤ)).hom
      (((⟨2, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨3, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ
        (5 : ℤ)) = (30 : ℤ) := by
  rw [adjShriek_counit_app, Iso.inv_hom_id_app_assoc, ModuleCat.hom_ofHom, tildeAct_tmul,
    tildeMul_tmul, smul_eq_mul]
  norm_num
