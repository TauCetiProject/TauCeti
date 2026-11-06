/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Elements

/-!
# Examples of almost elements and of the left adjoint `M ↦ M_!`

These examples test the functor of almost elements `TauCeti.Almost.Module.elements S`, the functor
`TauCeti.Almost.Module.shriek S` and their adjunctions with almostification:

* the unit `x ↦ (1 ↦ x)^a` sends `1 : ℤ` to the identity of `ℤ^a` for the classical setup, and the
  unit of `adjElements` is a natural isomorphism for the classical setup;
* for every setup with `m ≠ V`, the unit `V ⧸ m → ((V ⧸ m)^a)_*` is not injective, although it is an
  almost isomorphism: almost elements of `N^a` are not elements of `N`;
* for the zero setup every module of almost elements and every `M_!` is zero, so `(ℤ^a)_!` is not
  isomorphic to `ℤ`, while for the classical setup the counit `(N^a)_! → N` is an isomorphism;
* `(N^a)_! ≅ m~ ⊗[V] N`, and the category of almost modules is complete, cocomplete and has enough
  injectives.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2.
-/

open CategoryTheory Limits TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup
  TauCeti.Almost.Module

variable {V : Type*} [CommRing V]

/-! ### Almost elements -/

-- For the classical setup on `ℤ`, the unit sends `1` to the identity of `ℤ^a`, which is nonzero.
example : ((adjElements (classical ℤ)).unit.app (ModuleCat.of ℤ ℤ)).hom (1 : ℤ) =
    𝟙 ((toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  rw [adjElements_unit_app_hom_apply, ← (toAlmost _).map_id]
  congr 1
  ext
  simp

example : 𝟙 ((toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ)) ≠ 0 := by
  intro h
  refine (isZero_toAlmost_obj_iff _ _).not.mpr ?_ ((IsZero.iff_id_eq_zero _).mpr h)
  rw [isAlmostZero_classical_iff]
  intro h
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

-- For the classical setup, the unit `N → (N^a)_*` is an isomorphism.
example : IsIso (adjElements (classical V)).unit :=
  inferInstance

-- For the zero setup, every module of almost elements is zero.
example (M : Module (zero V)) : IsZero ((elements (zero V)).obj M) := by
  have : Subsingleton ((elements (zero V)).obj M) :=
    ⟨fun f g ↦ (isZero_of_ideal_eq_bot _ zero_ideal M).eq_of_tgt f g⟩
  exact ModuleCat.isZero_of_subsingleton _

-- If `m ≠ V`, the unit `V ⧸ m → ((V ⧸ m)^a)_*` is not injective, although it is an almost
-- isomorphism.
example (S : BasicSetup V) (hS : S.ideal ≠ ⊤) :
    ¬ Function.Injective ((adjElements S).unit.app (ModuleCat.of V (V ⧸ S.ideal))).hom := by
  have hzero : IsZero ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal))) :=
    (isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_quotient
  have : Nontrivial (V ⧸ S.ideal) := Ideal.Quotient.nontrivial_iff.mpr hS
  intro h
  exact one_ne_zero (α := V ⧸ S.ideal) (h (hzero.eq_of_tgt
    (((adjElements S).unit.app _).hom (1 : V ⧸ S.ideal)) (((adjElements S).unit.app _).hom 0)))

example (S : BasicSetup V) :
    S.IsAlmostIso ((adjElements S).unit.app (ModuleCat.of V (V ⧸ S.ideal))).hom :=
  isAlmostIso_adjElements_unit_app S _

-- Almost elements form a fully faithful right adjoint, so the counit `(M_*)^a → M` is an
-- isomorphism.
example (S : BasicSetup V) : IsIso (adjElements S).counit :=
  inferInstance

/-! ### The left adjoint `M ↦ M_!` -/

-- `(N^a)_! ≅ m~ ⊗[V] N`.
noncomputable example (S : BasicSetup V) (N : ModuleCat V) :
    (shriek S).obj ((toAlmost S).obj N) ≅ ModuleCat.of V (S.tilde ⊗[V] N) :=
  (toAlmostCompShriekIso S).app N

-- For the zero setup, `M_!` is zero for every almost module `M`.
example (M : Module (zero V)) : IsZero ((shriek (zero V)).obj M) :=
  (shriek (zero V)).map_isZero (isZero_of_ideal_eq_bot _ zero_ideal M)

-- So for the zero setup, `(ℤ^a)_!` is not isomorphic to `ℤ`: the functor `M ↦ M_!` is not unital.
example : IsEmpty ((shriek (zero ℤ)).obj ((toAlmost (zero ℤ)).obj (ModuleCat.of ℤ ℤ)) ≅
    ModuleCat.of ℤ ℤ) := by
  refine ⟨fun e ↦ ?_⟩
  have := ModuleCat.subsingleton_of_isZero
    (((shriek (zero ℤ)).map_isZero (isZero_of_ideal_eq_bot _ zero_ideal _)).of_iso e.symm)
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

-- For the classical setup, the counit `(N^a)_! → N` is an isomorphism.
example : IsIso (adjShriek (classical V)).counit :=
  inferInstance

-- `M ↦ M_!` is exact.
example (S : BasicSetup V) :
    PreservesFiniteLimits (shriek S) ∧ PreservesFiniteColimits (shriek S) :=
  ⟨inferInstance, inferInstance⟩

/-! ### Limits, colimits and injectives -/

example (S : BasicSetup V) : HasLimits (Module S) ∧ HasColimits (Module S) :=
  ⟨inferInstance, inferInstance⟩

example (S : BasicSetup V) : PreservesLimits (toAlmost S) ∧ PreservesColimits (toAlmost S) :=
  ⟨inferInstance, inferInstance⟩

example (S : BasicSetup V) : EnoughInjectives (Module S) :=
  inferInstance
