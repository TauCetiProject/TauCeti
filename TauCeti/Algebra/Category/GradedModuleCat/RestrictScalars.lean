/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Restriction of scalars of graded modules

Let `f : A →ₐ[k] B` be an algebra map sending each homogeneous piece `𝒜ᵢ` into `ℬᵢ`. A graded
`ℬ`-module `M` becomes a graded `𝒜`-module by letting `a` act as `f a`, keeping the underlying
`k`-module and its grading. Morphisms of degree zero stay morphisms of degree zero, so this is a
functor `GradedModuleCat ℬ ⥤ GradedModuleCat 𝒜`, and it commutes with the grading shift: both
composites keep the underlying module and shift its grading.

When `e : A ≃ₐ[k] B` is an algebra isomorphism with `e a ∈ ℬᵢ ↔ a ∈ 𝒜ᵢ`, restricting along `e`
and along `e.symm` are mutually inverse, giving an equivalence of graded module categories.
Restriction of scalars along a surjective map preserves and reflects finite generation of the
underlying module, and restriction along a graded isomorphism preserves and reflects
projectivity.

Along any scalar tower `k₀ → k → A`, viewing the pieces of `𝒜` as `k₀`-submodules restricts the
base ring without changing the `A`-action; when `1 ∈ 𝒜₀`, the `k`-action is recovered via
`algebraMap k A : k → 𝒜₀`, giving an equivalence of categories.

## Main definitions

* `TauCeti.GradedModuleCat.restrictScalars`: restriction of scalars along a grading-preserving
  algebra map.
* `TauCeti.GradedModuleCat.restrictScalarsShiftIso`: restriction of scalars commutes with the
  grading shift.
* `TauCeti.GradedModuleCat.restrictScalarsObjLinearEquiv`: a restricted graded module is, as an
  ungraded module, the ungraded restriction of scalars of the original module.
* `TauCeti.GradedModuleCat.restrictScalarsEquivalenceOfAlgEquiv`: the equivalence of graded module
  categories induced by a graded algebra isomorphism.
* `TauCeti.GradedModuleCat.restrictBase`, `TauCeti.GradedModuleCat.extendBase`, and
  `TauCeti.GradedModuleCat.restrictBaseEquivalence`: base-ring change and equivalence along
  `k₀ → k → A`.

## Main results

* `TauCeti.GradedModuleCat.finite_restrictScalarsObj_iff`: along a surjective map, the
  restricted module is finitely generated exactly when the original one is.
* `TauCeti.GradedModuleCat.projective_restrictScalarsObj_iff`: along a graded isomorphism, the
  restricted module is projective exactly when the original one is.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Section 2.2, for change of rings between categories of graded modules.
-/

public section

namespace TauCeti

open CategoryTheory

universe v uk uA uB

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]

namespace GradedModuleCat

section ChangeOfRings

variable {B : Type uB} [Ring B] [Algebra k B] {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}

section RestrictScalars

variable (f : A →ₐ[k] B) (hf : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, a ∈ 𝒜 i → f a ∈ ℬ i)

/-- The graded `𝒜`-module obtained from a graded `ℬ`-module by letting `a : A` act as `f a`. The
underlying `k`-module and the grading are unchanged. -/
abbrev restrictScalarsObj (M : GradedModuleCat.{v} ℬ) : GradedModuleCat.{v} 𝒜 :=
  letI : Module A M := Module.compHom M f.toRingHom
  haveI : IsScalarTower k A M :=
    ⟨fun c a m ↦ (congrArg (· • m) (map_smul f c a)).trans (smul_assoc c (f a) m)⟩
  { carrier := M
    grading := M.grading
    gradedSMul := ⟨fun _ _ _ _ ha hm ↦ M.gradedSMul.smul_mem (hf ha) hm⟩ }

/-- In the restricted module, `a : A` acts as `f a`. -/
@[simp]
theorem restrictScalarsObj_smul_def (M : GradedModuleCat.{v} ℬ) (a : A)
    (m : restrictScalarsObj f hf M) : a • m = (f a • (m : M) : M) :=
  rfl

/-- **Restriction of scalars** of graded modules along an algebra map `f` sending each `𝒜ᵢ` into
`ℬᵢ`: a graded `ℬ`-module becomes a graded `𝒜`-module with `a` acting as `f a`. -/
@[expose]
def restrictScalars : GradedModuleCat.{v} ℬ ⥤ GradedModuleCat.{v} 𝒜 where
  obj := restrictScalarsObj f hf
  map {M N} g := ofHom (M := restrictScalarsObj f hf M) (N := restrictScalarsObj f hf N)
    { toFun := g.hom
      map_add' := g.hom.map_add
      map_smul' := fun a x ↦ g.hom.map_smul (f a) x }
    (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by rw [add_zero]; exact map_mem g hx)

/-- The objects of the restriction functor are the restricted modules. -/
theorem restrictScalars_obj (M : GradedModuleCat.{v} ℬ) :
    (restrictScalars f hf).obj M = restrictScalarsObj f hf M :=
  rfl

/-- Restriction of scalars does not change the underlying function of a morphism. -/
@[simp]
theorem restrictScalars_map_hom_apply {M N : GradedModuleCat.{v} ℬ} (g : M ⟶ N)
    (x : restrictScalarsObj f hf M) : ((restrictScalars f hf).map g).hom x = g.hom x :=
  rfl

instance : (restrictScalars.{v} f hf).Additive where
  map_add := by intros; ext; rfl

instance : (restrictScalars.{v} f hf).Linear k where
  map_smul := by intros; ext; rfl

/-- Restriction of scalars commutes with the grading shift: both composites keep the underlying
module and shift its grading, so the components are identities. -/
def restrictScalarsShiftIso :
    (shift ℬ).functor ⋙ restrictScalars.{v} f hf ≅ restrictScalars.{v} f hf ⋙ (shift 𝒜).functor :=
  NatIso.ofComponents (fun _ ↦ isoMk (LinearEquiv.refl A _) fun _ _ ↦ Iff.rfl) fun _ ↦ rfl

/-- The components of `TauCeti.GradedModuleCat.restrictScalarsShiftIso` are identities. -/
@[simp]
theorem restrictScalarsShiftIso_hom_app_hom (M : GradedModuleCat.{v} ℬ) :
    ((restrictScalarsShiftIso f hf).hom.app M).hom = LinearMap.id :=
  (rfl)

/-- The inverse components of `TauCeti.GradedModuleCat.restrictScalarsShiftIso` are identities. -/
@[simp]
theorem restrictScalarsShiftIso_inv_app_hom (M : GradedModuleCat.{v} ℬ) :
    ((restrictScalarsShiftIso f hf).inv.app M).hom = LinearMap.id :=
  (rfl)

/-- Forgetting the grading of a restricted graded module gives the ungraded restriction of
scalars of the underlying module: the identity map is an `A`-linear equivalence between them. -/
def restrictScalarsObjLinearEquiv (M : GradedModuleCat.{v} ℬ) :
    restrictScalarsObj f hf M ≃ₗ[A] (ModuleCat.restrictScalars (f : A →+* B)).obj (ModuleCat.of B M)
    where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' a m := (restrictScalarsObj_smul_def f hf M a m).trans
    (ModuleCat.restrictScalars.smul_def' (f : A →+* B) (M := ModuleCat.of B M) a m).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- `TauCeti.GradedModuleCat.restrictScalarsObjLinearEquiv` is the identity on elements. -/
@[simp]
theorem restrictScalarsObjLinearEquiv_apply (M : GradedModuleCat.{v} ℬ)
    (m : restrictScalarsObj f hf M) : (restrictScalarsObjLinearEquiv f hf M m : M) = m :=
  (rfl)

/-- The inverse of `TauCeti.GradedModuleCat.restrictScalarsObjLinearEquiv` is the identity on
elements. -/
@[simp]
theorem restrictScalarsObjLinearEquiv_symm_apply (M : GradedModuleCat.{v} ℬ)
    (m : (ModuleCat.restrictScalars (f : A →+* B)).obj (ModuleCat.of B M)) :
    ((restrictScalarsObjLinearEquiv f hf M).symm m : M) = m :=
  (rfl)

/-- Restriction of scalars along a surjective grading-preserving algebra map preserves and
reflects finite generation of the underlying module: every scalar of `B` is the image of a scalar
of `A`, so the two spans of a set agree. -/
theorem finite_restrictScalarsObj_iff (hsurj : Function.Surjective f)
    (M : GradedModuleCat.{v} ℬ) :
    Module.Finite A (restrictScalarsObj f hf M) ↔ Module.Finite B M :=
  (Module.Finite.equiv_iff (restrictScalarsObjLinearEquiv f hf M)).trans
    (f.toRingHom.finite_restrictScalars_iff hsurj (ModuleCat.of B M))

end RestrictScalars

section AlgEquiv

/-- An algebra isomorphism `e` with `e a ∈ ℬᵢ ↔ a ∈ 𝒜ᵢ` sends each `𝒜ᵢ` into `ℬᵢ`. -/
theorem map_mem_of_algEquiv {e : A ≃ₐ[k] B} (he : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, e a ∈ ℬ i ↔ a ∈ 𝒜 i)
    ⦃i : ℤ⦄ ⦃a : A⦄ (ha : a ∈ 𝒜 i) : e.toAlgHom a ∈ ℬ i :=
  he.2 ha

/-- The inverse of an algebra isomorphism `e` with `e a ∈ ℬᵢ ↔ a ∈ 𝒜ᵢ` sends each `ℬᵢ` into
`𝒜ᵢ`. -/
theorem symm_map_mem_of_algEquiv {e : A ≃ₐ[k] B} (he : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, e a ∈ ℬ i ↔ a ∈ 𝒜 i)
    ⦃i : ℤ⦄ ⦃b : B⦄ (hb : b ∈ ℬ i) : e.symm.toAlgHom b ∈ 𝒜 i :=
  he.1 ((e.apply_symm_apply b).symm ▸ hb)

variable (e : A ≃ₐ[k] B) (he : ∀ ⦃i : ℤ⦄ ⦃a : A⦄, e a ∈ ℬ i ↔ a ∈ 𝒜 i)

/-- **Restriction of scalars along a graded algebra isomorphism** `e : A ≃ₐ[k] B`, one with
`e a ∈ ℬᵢ ↔ a ∈ 𝒜ᵢ`, is an equivalence of graded module categories, with inverse the
restriction of scalars along `e.symm`. -/
def restrictScalarsEquivalenceOfAlgEquiv : GradedModuleCat.{v} ℬ ≌ GradedModuleCat.{v} 𝒜 where
  functor := restrictScalars e.toAlgHom (map_mem_of_algEquiv he)
  inverse := restrictScalars e.symm.toAlgHom (symm_map_mem_of_algEquiv he)
  unitIso := NatIso.ofComponents (fun _ ↦ isoMk
    { toFun := id
      invFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun b x ↦ (congrArg (· • x) (e.apply_symm_apply b)).symm
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl } fun _ _ ↦ Iff.rfl) fun _ ↦ rfl
  counitIso := NatIso.ofComponents (fun N ↦ isoMk
    { toFun := id
      invFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a (x : N) ↦ congrArg (· • x) (e.symm_apply_apply a)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl } fun _ _ ↦ Iff.rfl) fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

/-- The functor of the equivalence is restriction of scalars along `e`. -/
@[simp]
theorem restrictScalarsEquivalenceOfAlgEquiv_functor :
    (restrictScalarsEquivalenceOfAlgEquiv.{v} e he).functor =
      restrictScalars e.toAlgHom (map_mem_of_algEquiv he) :=
  (rfl)

/-- The inverse of the equivalence is restriction of scalars along `e.symm`. -/
@[simp]
theorem restrictScalarsEquivalenceOfAlgEquiv_inverse :
    (restrictScalarsEquivalenceOfAlgEquiv.{v} e he).inverse =
      restrictScalars e.symm.toAlgHom (symm_map_mem_of_algEquiv he) :=
  (rfl)

/-- Restriction of scalars along a graded algebra isomorphism preserves and reflects projectivity
of the underlying module. -/
theorem projective_restrictScalarsObj_iff (M : GradedModuleCat.{v} ℬ) :
    Module.Projective A (restrictScalarsObj e.toAlgHom (map_mem_of_algEquiv he) M) ↔
      Module.Projective B M :=
  let φ := restrictScalarsObjLinearEquiv e.toAlgHom (map_mem_of_algEquiv he) M
  Iff.trans ⟨fun _ ↦ Module.Projective.of_equiv φ, fun _ ↦ Module.Projective.of_equiv φ.symm⟩
    (e.toRingEquiv.projective_restrictScalars_iff (ModuleCat.of B M))

end AlgEquiv

end ChangeOfRings

section RestrictBase

variable (k₀ : Type*) [CommRing k₀] [Algebra k₀ k] [Algebra k₀ A] [IsScalarTower k₀ k A]

/-- **Restriction of the base ring** along a scalar tower `k₀ → k → A`: a graded `𝒜`-module becomes
a graded module over `(𝒜 · |>.restrictScalars k₀)` with the same underlying `A`-module. -/
@[expose]
def restrictBase (𝒜 : ℤ → Submodule k A) :
    GradedModuleCat.{v} 𝒜 ⥤ GradedModuleCat.{v} (fun i ↦ (𝒜 i).restrictScalars k₀) where
  obj M :=
    letI : Module k₀ M := Module.compHom M (algebraMap k₀ k)
    haveI : IsScalarTower k₀ k M :=
      ⟨fun c₀ c m ↦ (congrArg (· • m) (Algebra.smul_def c₀ c)).trans (mul_smul _ c m)⟩
    haveI : IsScalarTower k₀ A M :=
      ⟨fun c₀ a m ↦ by rw [← IsScalarTower.algebraMap_smul k c₀ a, smul_assoc]; rfl⟩
    { carrier := M
      grading := { piece := fun p ↦ (M.grading.piece p).restrictScalars k₀
                   isInternal := M.grading.isInternal }
      gradedSMul := ⟨fun _ _ _ _ ha hm ↦ M.gradedSMul.smul_mem ha hm⟩ }
  map g := ofHom g.hom (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    rw [add_zero]; exact map_mem g hx)

/-- Restricting the base ring leaves the underlying `A`-linear map of a morphism unchanged. -/
@[simp]
theorem restrictBase_map_hom {𝒜 : ℤ → Submodule k A} {M N : GradedModuleCat.{v} 𝒜} (g : M ⟶ N) :
    ((restrictBase k₀ 𝒜).map g).hom = g.hom := rfl

instance (𝒜 : ℤ → Submodule k A) : (restrictBase.{v} k₀ 𝒜).Additive where
  map_add := by intros; ext; rfl

/-- **Extension of the base ring** along `k₀ → k → A` when `1 ∈ 𝒜₀`: every graded module over
`(𝒜 · |>.restrictScalars k₀)` is a graded `𝒜`-module with `k` acting via `algebraMap k A`. -/
@[expose]
def extendBase (𝒜 : ℤ → Submodule k A) [SetLike.GradedOne 𝒜] :
    GradedModuleCat.{v} (fun i ↦ (𝒜 i).restrictScalars k₀) ⥤ GradedModuleCat.{v} 𝒜 where
  obj N :=
    letI : Module k N := Module.compHom N (algebraMap k A)
    haveI : IsScalarTower k A N :=
      ⟨fun c a x ↦ (congrArg (· • x) (Algebra.smul_def c a)).trans (mul_smul _ a x)⟩
    { carrier := N
      grading :=
        { piece := fun p ↦
            { carrier := N.grading.piece p
              zero_mem' := (N.grading.piece p).zero_mem
              add_mem' := (N.grading.piece p).add_mem
              smul_mem' := fun c x hx ↦ by
                have hc : algebraMap k A c ∈ 𝒜 0 := Algebra.algebraMap_eq_smul_one (A := A) c ▸
                  (𝒜 0).smul_mem c (SetLike.GradedOne.one_mem (A := 𝒜))
                exact zero_vadd ℤ p ▸ N.gradedSMul.smul_mem hc hx }
          isInternal := N.grading.isInternal }
      gradedSMul := ⟨fun _ _ _ _ ha hx ↦ N.gradedSMul.smul_mem ha hx⟩ }
  map g := ofHom g.hom (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    rw [add_zero]; exact map_mem g hx)

/-- Extending the base ring leaves the underlying `A`-linear map of a morphism unchanged. -/
@[simp]
theorem extendBase_map_hom {𝒜 : ℤ → Submodule k A} [SetLike.GradedOne 𝒜]
    {M N : GradedModuleCat.{v} (fun i ↦ (𝒜 i).restrictScalars k₀)} (g : M ⟶ N) :
    ((extendBase k₀ 𝒜).map g).hom = g.hom := rfl

instance (𝒜 : ℤ → Submodule k A) [SetLike.GradedOne 𝒜] : (extendBase.{v} k₀ 𝒜).Additive where
  map_add := by intros; ext; rfl

/-- **Base-ring independence of graded modules.** When `1 ∈ 𝒜₀`, restricting the base ring of `𝒜`
along a scalar tower `k₀ → k → A` is an equivalence of graded module categories. -/
@[expose]
def restrictBaseEquivalence (𝒜 : ℤ → Submodule k A) [SetLike.GradedOne 𝒜] :
    GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} (fun i ↦ (𝒜 i).restrictScalars k₀) where
  functor := restrictBase k₀ 𝒜
  inverse := extendBase k₀ 𝒜
  unitIso := NatIso.ofComponents (fun _ ↦ isoMk (.refl A _) fun _ _ ↦ Iff.rfl) fun _ ↦ rfl
  counitIso := NatIso.ofComponents (fun _ ↦ isoMk (.refl A _) fun _ _ ↦ Iff.rfl) fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

/-- The forward functor of `TauCeti.GradedModuleCat.restrictBaseEquivalence` is `restrictBase`. -/
@[simp]
theorem restrictBaseEquivalence_functor (𝒜 : ℤ → Submodule k A) [SetLike.GradedOne 𝒜] :
    (restrictBaseEquivalence.{v} k₀ 𝒜).functor = restrictBase k₀ 𝒜 := (rfl)

/-- The inverse functor of `TauCeti.GradedModuleCat.restrictBaseEquivalence` is `extendBase`. -/
@[simp]
theorem restrictBaseEquivalence_inverse (𝒜 : ℤ → Submodule k A) [SetLike.GradedOne 𝒜] :
    (restrictBaseEquivalence.{v} k₀ 𝒜).inverse = extendBase k₀ 𝒜 := (rfl)

end RestrictBase

end GradedModuleCat

end TauCeti
