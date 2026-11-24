/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Schubert.AffineFlag.Basic
public import TauCeti.AlgebraicGeometry.Grassmannian.BaseChange

/-!
# Base change of affine-base flag schemes

The flag scheme of a module commutes with extension of its base ring. The comparison
transports each step through the canonical tensor-product equivalence, preserving all
containments, and agrees with the Grassmannian comparison on every projection.
-/

public section

universe u

open CategoryTheory Limits _root_.AlgebraicGeometry TensorProduct Module.Grassmannian

namespace TauCeti.AlgebraicGeometry

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
  (M : Type u) [AddCommGroup M] [Module R M] {n : ℕ} (q : Fin n → ℕ)

private noncomputable def flagPointBaseChangeEquiv (A : Type u) [CommRing A] [Algebra R' A]
    [Algebra R A] [IsScalarTower R R' A] :
    {N : ∀ i, G(q i, A ⊗[R'] (R' ⊗[R] M); A) //
      ∀ ⦃i j⦄, i < j → (N i).toSubmodule ≤ (N j).toSubmodule} ≃
    {N : ∀ i, G(q i, A ⊗[R] M; A) //
      ∀ ⦃i j⦄, i < j → (N i).toSubmodule ≤ (N j).toSubmodule} :=
  (Equiv.piCongrRight fun i ↦ baseChangeEquiv R' (k := q i)).subtypeEquiv fun N ↦ by
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, toSubmodule_baseChangeEquiv,
      Submodule.map_le_map_iff_of_injective
        (AlgebraTensorModule.cancelBaseChange R R' A A M).injective]

private theorem flagPointBaseChangeEquiv_apply (A : Type u) [CommRing A] [Algebra R' A]
    [Algebra R A] [IsScalarTower R R' A]
    (N : {N : ∀ i, G(q i, A ⊗[R'] (R' ⊗[R] M); A) //
      ∀ ⦃i j⦄, i < j → (N i).toSubmodule ≤ (N j).toSubmodule}) (i : Fin n) :
    (flagPointBaseChangeEquiv R R' M q A N).val i = baseChangeEquiv R' (N.val i) :=
  (rfl)

private noncomputable def flagBaseChangePoint {A : CommRingCat.{u}}
    (a : Spec A ⟶ (flagScheme R' (R' ⊗[R] M) q).left) :
    Spec A ⟶ (flagScheme R M q).left :=
  let φ := (Spec.preimage (a ≫ (flagScheme R' (R' ⊗[R] M) q).hom)).hom
  letI := φ.toAlgebra
  letI : Algebra R A := (φ.comp (algebraMap R R')).toAlgebra
  letI : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  (flagSchemeHomEquiv.symm (flagPointBaseChangeEquiv R R' M q A
    (flagSchemeHomEquiv (Over.homMk a (Spec.map_preimage _).symm)))).left

private lemma flagBaseChangePoint_π {A : CommRingCat.{u}}
    (a : Spec A ⟶ (flagScheme R' (R' ⊗[R] M) q).left) (i : Fin n) :
    flagBaseChangePoint R R' M q a ≫ flagSchemeπ R M q i =
      a ≫ flagSchemeπ R' (R' ⊗[R] M) q i ≫ baseChangeHom R R' M (q i) := by
  let φ := (Spec.preimage (a ≫ (flagScheme R' (R' ⊗[R] M) q).hom)).hom
  let _ := φ.toAlgebra
  let _ : Algebra R A := (φ.comp (algebraMap R R')).toAlgebra
  let _ : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  dsimp only [flagBaseChangePoint]
  rw [flagSchemeHomEquiv_symm_apply_π]
  rw [flagPointBaseChangeEquiv_apply]
  rw [← toSchemeHom_comp_baseChangeHom, toSchemeHom_flagSchemeHomEquiv_apply]
  simp only [Over.Hom.left, Over.homMk_left, Category.assoc]

private lemma flagBaseChangePoint_toSpec {A : CommRingCat.{u}}
    (a : Spec A ⟶ (flagScheme R' (R' ⊗[R] M) q).left) :
    flagBaseChangePoint R R' M q a ≫ (flagScheme R M q).hom =
      a ≫ (flagScheme R' (R' ⊗[R] M) q).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  let φ := (Spec.preimage (a ≫ (flagScheme R' (R' ⊗[R] M) q).hom)).hom
  let _ := φ.toAlgebra
  let _ : Algebra R A := (φ.comp (algebraMap R R')).toAlgebra
  let _ : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  dsimp only [flagBaseChangePoint]
  rw [Over.w]
  rw [← Category.assoc,
    ← Spec.map_preimage (a ≫ (flagScheme R' (R' ⊗[R] M) q).hom), ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra,
    Spec.preimage_map]

private lemma flagBaseChangePoint_comp {A B : CommRingCat.{u}} (f : Spec B ⟶ Spec A)
    (a : Spec A ⟶ (flagScheme R' (R' ⊗[R] M) q).left) :
    flagBaseChangePoint R R' M q (f ≫ a) = f ≫ flagBaseChangePoint R R' M q a := by
  apply flagScheme_hom_ext
  · simp only [flagBaseChangePoint_toSpec, Category.assoc]
  · intro i
    simp only [flagBaseChangePoint_π, Category.assoc]

/-- The projection from the flag scheme after extending the base ring, induced by the canonical
identification of the tensor products in each step. -/
noncomputable def flagBaseChangeHom :
    (flagScheme R' (R' ⊗[R] M) q).left ⟶ (flagScheme R M q).left :=
  Scheme.homOfAffinePoints (flagBaseChangePoint R R' M q)
    (flagBaseChangePoint_comp R R' M q)

/-- Base change of flags agrees with base change of each Grassmannian step. -/
@[reassoc (attr := simp)]
theorem flagBaseChangeHom_π (i : Fin n) :
    flagBaseChangeHom R R' M q ≫ flagSchemeπ R M q i =
      flagSchemeπ R' (R' ⊗[R] M) q i ≫ baseChangeHom R R' M (q i) := by
  apply Scheme.hom_ext_of_forall_spec
  intro A a
  rw [← Category.assoc, flagBaseChangeHom, Scheme.comp_homOfAffinePoints,
    flagBaseChangePoint_π]

/-- The flag base-change projection lies over the map of affine base schemes. -/
@[reassoc (attr := simp)]
theorem flagBaseChangeHom_toSpec :
    flagBaseChangeHom R R' M q ≫ (flagScheme R M q).hom =
      (flagScheme R' (R' ⊗[R] M) q).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  apply Scheme.hom_ext_of_forall_spec
  intro A a
  rw [← Category.assoc, flagBaseChangeHom, Scheme.comp_homOfAffinePoints,
    flagBaseChangePoint_toSpec]

/-- Formation of the flag scheme commutes with arbitrary extension of the affine base ring. -/
theorem isPullback_flagBaseChangeHom :
    IsPullback (flagBaseChangeHom R R' M q) (flagScheme R' (R' ⊗[R] M) q).hom
      (flagScheme R M q).hom (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  refine Scheme.isPullback_of_forall_spec (flagBaseChangeHom_toSpec R R' M q)
    fun B a b hab ↦ ?_
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  let _ : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  let a' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ flagScheme R M q :=
    Over.homMk a (hab.trans (Spec.map_comp _ _).symm)
  let N := (flagPointBaseChangeEquiv R R' M q B).symm (flagSchemeHomEquiv a')
  let c := (flagSchemeHomEquiv.symm N).left
  have hc₂ : c ≫ (flagScheme R' (R' ⊗[R] M) q).hom = Spec.map φ :=
    Over.w (flagSchemeHomEquiv.symm N)
  have hc₁ : c ≫ flagBaseChangeHom R R' M q = a := by
    apply flagScheme_hom_ext
    · rw [Category.assoc, flagBaseChangeHom_toSpec, ← Category.assoc, hc₂, hab]
    · intro i
      rw [Category.assoc, flagBaseChangeHom_π, ← Category.assoc,
        flagSchemeHomEquiv_symm_apply_π, toSchemeHom_comp_baseChangeHom]
      have h := congrArg (fun p ↦ p.val i)
        ((flagPointBaseChangeEquiv R R' M q B).apply_symm_apply (flagSchemeHomEquiv a'))
      exact (congrArg toSchemeHom h).trans (toSchemeHom_flagSchemeHomEquiv_apply a' i)
  refine ⟨c, ⟨hc₁, hc₂⟩, ?_⟩
  rintro d ⟨hd₁, hd₂⟩
  apply flagScheme_hom_ext (hd₂.trans hc₂.symm)
  intro i
  apply (Module.Grassmannian.isPullback_baseChangeHom R R' M (q i)).hom_ext
  · rw [Category.assoc, ← flagBaseChangeHom_π, ← Category.assoc, hd₁,
      Category.assoc, ← flagBaseChangeHom_π, ← Category.assoc, hc₁]
  · simp only [Category.assoc, flagSchemeπ_toSpec, hd₂, hc₂]

end TauCeti.AlgebraicGeometry
