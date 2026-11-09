/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Monoidal

/-!
# Examples of the monoidal structure on almost modules

These examples test the localized symmetric monoidal structure on `TauCeti.Almost.Module S`:

* the inclusion `m ⊆ V` stays an almost isomorphism after tensoring with any module; for `m ≠ V`,
  tensoring it with `V ⧸ m` gives the zero map `V ⧸ m ⊗ m → V ⧸ m ⊗ V ≅ V ⧸ m`, which is not an
  isomorphism of `V`-modules but becomes one after almostification;
* the tensor unit is `V^a`, isomorphic to `m^a`, and `M^a ⊗ N^a ≅ (M ⊗[V] N)^a`;
* `(V ⧸ m)^a ⊗ X` is zero for every almost module `X`, while `ℤ^a ⊗ ℤ^a` is not zero for the
  classical setup `(ℤ, ℤ)`;
* the tensor product of almost modules is `V`-linear and right exact;
* almost elements are lax monoidal with almost-isomorphic comparisons, `M ↦ M_!` preserves tensor
  products, and its unit comparison `(V^a)_! → V` is an isomorphism for the classical setup but
  not for the zero setup over `ℤ`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.5).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Proposition 4.5.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup
  TauCeti.Almost.Module

variable {V : Type*} [CommRing V]

/-! ### Tensoring almost isomorphisms -/

-- Tensoring the almost isomorphism `m → V` with any module gives an almost isomorphism.
example (S : BasicSetup V) (X : Type*) [AddCommGroup X] [Module V X] :
    S.IsAlmostIso (S.ideal.subtype.lTensor X) ∧ S.IsAlmostIso (S.ideal.subtype.rTensor X) :=
  ⟨S.isAlmostIso_subtype.lTensor X, S.isAlmostIso_subtype.rTensor X⟩

-- For `m ≠ V`, the map `V ⧸ m ⊗ m → V ⧸ m ⊗ V` is not an isomorphism of `V`-modules: it is zero,
-- and its target `V ⧸ m ⊗ V ≅ V ⧸ m` is not.
example (S : BasicSetup V) (hS : S.ideal ≠ ⊤) :
    ¬ IsIso (ModuleCat.of V (V ⧸ S.ideal) ◁ ModuleCat.ofHom S.ideal.subtype) := by
  intro h
  have hzero : (TensorProduct.rid V (V ⧸ S.ideal)).toLinearMap ∘ₗ
      S.ideal.subtype.lTensor (V ⧸ S.ideal) = 0 := by
    refine TensorProduct.ext' fun x i ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.lTensor_tmul, Submodule.subtype_apply, TensorProduct.rid_tmul, LinearMap.zero_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact S.ideal.mul_mem_right x i.2
  have hbij : Function.Bijective (S.ideal.subtype.lTensor (V ⧸ S.ideal)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp h
  have hsurj : Function.Surjective ((TensorProduct.rid V (V ⧸ S.ideal)).toLinearMap ∘ₗ
      S.ideal.subtype.lTensor (V ⧸ S.ideal)) :=
    (TensorProduct.rid V (V ⧸ S.ideal)).surjective.comp hbij.2
  rw [hzero] at hsurj
  obtain ⟨y, hy⟩ := hsurj 1
  exact hS (Ideal.Quotient.subsingleton_iff.mp ⟨fun a b ↦ by
    rw [← one_mul a, ← one_mul b, ← hy, LinearMap.zero_apply, zero_mul, zero_mul]⟩)

-- After almostification it becomes an isomorphism.
example (S : BasicSetup V) :
    IsIso ((toAlmost S).map (ModuleCat.of V (V ⧸ S.ideal) ◁ ModuleCat.ofHom S.ideal.subtype)) := by
  rw [isIso_toAlmost_map_iff, isAlmostIso_iff_isoModSerre]
  exact S.almostZero.isoModSerre.whiskerLeft_mem _ _
    ((S.isAlmostIso_iff_isoModSerre _).mp S.isAlmostIso_subtype)

/-! ### The tensor unit and the tensor product of almostified modules -/

-- The tensor unit is `V^a`.
example (S : BasicSetup V) : 𝟙_ (Module S) = (toAlmost S).obj (ModuleCat.of V V) :=
  rfl

-- The tensor unit is isomorphic to `m^a`.
noncomputable example (S : BasicSetup V) :
    𝟙_ (Module S) ≅ (toAlmost S).obj (ModuleCat.of V S.ideal) :=
  Functor.Monoidal.εIso (toAlmost S) ≪≫
    (asIso ((toAlmost S).map (ModuleCat.ofHom S.ideal.subtype))).symm

-- `M^a ⊗ N^a ≅ (M ⊗[V] N)^a`.
noncomputable example (S : BasicSetup V) (M N : ModuleCat V) :
    (toAlmost S).obj M ⊗ (toAlmost S).obj N ≅ (toAlmost S).obj (M ⊗ N) :=
  Functor.Monoidal.μIso (toAlmost S) M N

/-! ### Zero and nonzero tensor products -/

-- `(V ⧸ m)^a ⊗ X` is zero for every almost module `X`.
example (S : BasicSetup V) (X : Module S) :
    IsZero ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal)) ⊗ X) := by
  have h := (isZero_toAlmost_obj_iff S (ModuleCat.of V (V ⧸ S.ideal))).mpr S.isAlmostZero_quotient
  rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, h.eq_of_src (𝟙 _) 0,
    MonoidalPreadditive.zero_whiskerRight]

-- For the zero setup, every tensor product of almost modules is zero.
example (X Y : Module (zero V)) : IsZero (X ⊗ Y) :=
  isZero_of_ideal_eq_bot _ zero_ideal _

-- For the classical setup, `ℤ^a ⊗ ℤ^a ≅ (ℤ ⊗[ℤ] ℤ)^a` is not zero.
example : ¬ IsZero ((toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ) ⊗
    (toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  intro h
  have h' := (isZero_toAlmost_obj_iff _ _).mp (h.of_iso (Functor.Monoidal.μIso _ _ _).symm)
  rw [isAlmostZero_classical_iff] at h'
  have := congrArg (TensorProduct.lid ℤ ℤ) (Subsingleton.elim ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) 0)
  simp at this

/-! ### Linearity and right exactness -/

-- The tensor product of almost modules is `V`-linear in each variable.
example (S : BasicSetup V) (X : Module S) {Y Z : Module S} (ε : V) (f : Y ⟶ Z) :
    X ◁ (ε • f) = ε • (X ◁ f) ∧ (ε • f) ▷ X = ε • (f ▷ X) := by
  simp

-- The tensor product of almost modules is right exact in each variable.
example (S : BasicSetup V) (X : Module S) :
    PreservesFiniteColimits (tensorLeft X) ∧ PreservesFiniteColimits (tensorRight X) :=
  ⟨inferInstance, inferInstance⟩

/-! ### Almost elements and the left adjoint `M ↦ M_!` -/

open Functor.LaxMonoidal Functor.OplaxMonoidal in
-- The unit comparison `V → (𝟙_)_*` of almost elements is an almost isomorphism, but for the zero
-- setup over `ℤ` it is not injective: its target is zero.
example : (zero ℤ).IsAlmostIso (ε (elements (zero ℤ))).hom ∧
    ¬ Function.Injective (ε (elements (zero ℤ))).hom := by
  refine ⟨isAlmostIso_elements_ε _, fun h ↦ one_ne_zero (α := ℤ) (@h 1 0 ?_)⟩
  exact (isZero_of_ideal_eq_bot _ zero_ideal _).eq_of_tgt _ _

-- The tensor comparison `(M ⊗ N)_! → M_! ⊗[V] N_!` of `M ↦ M_!` is an isomorphism for every
-- setup, even though its unit comparison need not be.
example (S : BasicSetup V) (M N : Module S) : IsIso (Functor.OplaxMonoidal.δ (shriek S) M N) :=
  inferInstance

-- Positive control: for the classical setup the unit comparison `(V^a)_! → V` is an isomorphism.
example : IsIso (Functor.OplaxMonoidal.η (shriek (classical V))) :=
  (isIso_shriek_η_iff _).mpr classical_ideal

-- Negative control: for the zero setup over `ℤ`, `(ℤ^a)_! = 0`, so the unit comparison
-- `(ℤ^a)_! → ℤ` is not an isomorphism.
example : ¬ IsIso (Functor.OplaxMonoidal.η (shriek (zero ℤ))) := by
  rw [isIso_shriek_η_iff, zero_ideal]
  exact bot_ne_top

-- The same holds for every setup with a proper ideal, for instance the maximal ideal of a
-- valuation ring that is not finitely generated.
example (S : BasicSetup V) (hS : S.ideal ≠ ⊤) :
    ¬ IsIso (Functor.OplaxMonoidal.η (shriek S)) :=
  fun h ↦ hS ((isIso_shriek_η_iff S).mp h)

-- A tensor product with a firm module is firm, whatever the other factor.
example (S : BasicSetup V) (P : Type*) [AddCommGroup P] [Module V P] :
    S.IsFirm (P ⊗[V] S.tilde) :=
  S.isFirm_tilde.tensorProduct P
