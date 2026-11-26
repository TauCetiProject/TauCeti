/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import TauCeti.Algebra.DirectSum.HomogeneousExtend
import TauCeti.Algebra.DirectSum.Internal

/-!
# Coinduced graded modules and enough injectives

For a `ℤ`-graded `k`-algebra `A` decomposed by `𝒜` and an ungraded left `A`-module `N`, the
**coinduced** graded module has underlying `k`-module `⨁ p : ℤ, N`, with degree-`p` piece given by
the `p`-th summand and homogeneous scalar multiplication shifting summands: an element `a ∈ 𝒜 q`
sends `(p, y)` to `(q + p, a • y)`.

Summing the homogeneous coordinates defines an `A`-linear counit `toModuleCat (coind N) ⟶ N`.
Conversely, since every element `m` of an internally graded `𝒜`-module `M` has only finitely many
nonzero homogeneous components `m_p`, any `A`-linear map `f : M ⟶ N` lifts uniquely to a degree-zero
graded morphism `M ⟶ coind N` whose `p`-th coordinate on `m` is `f (m_p)`. This exhibits
`coindFunctor 𝒜` as right adjoint to the forgetful functor `toModuleCat`.

Because `toModuleCat` preserves and reflects monomorphisms and `ModuleCat A` has enough injectives,
the adjunction transfers injective objects and enough injectives to `GradedModuleCat 𝒜`.

## Main definitions

* `TauCeti.GradedModuleCat.coindFunctor`: the right adjoint `ModuleCat A ⥤ GradedModuleCat 𝒜` to
  forgetting the grading.
* `TauCeti.GradedModuleCat.coindCounit` and `TauCeti.GradedModuleCat.coindLift`: the `A`-linear
  counit `toModuleCat ((coindFunctor 𝒜).obj N) ⟶ N` and the graded lift
  `M ⟶ (coindFunctor 𝒜).obj N` of an ungraded map `toModuleCat.obj M ⟶ N`.
* `TauCeti.GradedModuleCat.toModuleCatCoindAdj`: the adjunction `toModuleCat ⊣ coindFunctor 𝒜`.

## Main results

* `TauCeti.GradedModuleCat.coind_hom_ext`: graded morphisms into `(coindFunctor 𝒜).obj N` are
  determined by their ungraded composites with `coindCounit`.
* `TauCeti.GradedModuleCat.injective_coindFunctor_obj`: `coindFunctor 𝒜` preserves injective
  objects.
* `TauCeti.GradedModuleCat.enoughInjectives` and the `[Small.{v} A]` instance
  `EnoughInjectives (GradedModuleCat.{v} 𝒜)`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  **1836**, Springer (2004), Section 2.2 (the right adjoint to forgetting a group grading) and
  Section 2.3 (enough injectives in categories of graded modules).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe v uk uA

attribute [local implicit_reducible] toModuleCat

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Homogeneous action of `a ∈ 𝒜 q` on `⨁ p : ℤ, N`, shifting summand `p` to `q + p`. -/
private def coindHomogeneousEnd (N : ModuleCat.{v} A) (q : ℤ) :
    𝒜 q →ₗ[k] Module.End k (⨁ _ : ℤ, RestrictScalars k A N) where
  toFun a := DirectSum.toModule k ℤ (⨁ _ : ℤ, RestrictScalars k A N) fun p ↦
    (DirectSum.lof k ℤ (fun _ ↦ RestrictScalars k A N) (q + p)).comp
      (RestrictScalars.lsmul k A N (a : A))
  map_add' a b := by
    apply DirectSum.linearMap_ext k
    intro p
    ext y
    simp [map_add]
  map_smul' c a := by
    apply DirectSum.linearMap_ext k
    intro p
    ext y
    simp [map_smul]

/-- The `k`-algebra homomorphism `A →ₐ[k] End_k(⨁ p : ℤ, N)` defining the graded `A`-action. -/
private def coindEndAlgHom (N : ModuleCat.{v} A) :
    A →ₐ[k] Module.End k (⨁ _ : ℤ, RestrictScalars k A N) :=
  (DirectSum.toAlgebra k (fun q ↦ 𝒜 q) (coindHomogeneousEnd 𝒜 N)
    (by
      apply DirectSum.linearMap_ext k
      intro p
      refine LinearMap.ext fun y ↦ ?_
      simp [coindHomogeneousEnd, SetLike.coe_gOne])
    (fun {q r} a b ↦ by
      apply DirectSum.linearMap_ext k
      intro p
      refine LinearMap.ext fun y ↦ ?_
      simp [coindHomogeneousEnd, SetLike.coe_gMul, add_assoc, map_mul])).comp
    (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom

private theorem coindEndAlgHom_of_mem (N : ModuleCat.{v} A) {q : ℤ} {a : A} (ha : a ∈ 𝒜 q)
    (p : ℤ) (y : RestrictScalars k A N) :
    coindEndAlgHom 𝒜 N a (DirectSum.lof k ℤ (fun _ ↦ RestrictScalars k A N) p y) =
      DirectSum.lof k ℤ (fun _ ↦ RestrictScalars k A N) (q + p)
        (RestrictScalars.lsmul k A N a y) := by
  have h : coindEndAlgHom 𝒜 N a = coindHomogeneousEnd 𝒜 N q ⟨a, ha⟩ := by
    rw [coindEndAlgHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      DirectSum.decomposeAlgEquiv_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAlgebra_apply]
    exact DirectSum.toSemiring_of _ _ _ _ _
  rw [h]
  simp [coindHomogeneousEnd]

private instance (N : ModuleCat.{v} A) : AddCommGroup (⨁ _ : ℤ, RestrictScalars k A N) :=
  DirectSum.instAddCommGroup

/-- Construct the coinduced graded `𝒜`-module of an `A`-module `N`. -/
@[implicit_reducible]
private def coindObj (N : ModuleCat.{v} A) : GradedModuleCat.{v} 𝒜 :=
  letI : Module A (⨁ _ : ℤ, RestrictScalars k A N) :=
    Module.compHom (⨁ _ : ℤ, RestrictScalars k A N) (coindEndAlgHom 𝒜 N).toRingHom
  haveI : IsScalarTower k A (⨁ _ : ℤ, RestrictScalars k A N) :=
    IsScalarTower.of_algebraMap_smul fun c z ↦
      congrArg (fun f : Module.End k _ ↦ f z) ((coindEndAlgHom 𝒜 N).commutes c)
  let G : InternalGrading k (⨁ _ : ℤ, RestrictScalars k A N) ℤ :=
    InternalGrading.ofDecomposition
      (_root_.DirectSum.summand k (fun _ : ℤ ↦ RestrictScalars k A N))
  haveI : SetLike.GradedSMul 𝒜 G.piece := ⟨fun {q p} a z ha hz ↦ by
    have hsmul (b : A) (w : ⨁ _ : ℤ, RestrictScalars k A N) :
        b • w = coindEndAlgHom 𝒜 N b w := rfl
    rw [InternalGrading.ofDecomposition_piece] at hz ⊢
    obtain ⟨y, rfl⟩ := _root_.DirectSum.mem_summand.mp hz
    rw [← DirectSum.lof_eq_of k, hsmul, coindEndAlgHom_of_mem 𝒜 N ha]
    exact _root_.DirectSum.lof_mem_summand (q + p) _⟩
  { carrier := ⨁ _ : ℤ, RestrictScalars k A N
    grading := G }

@[simp]
private theorem coindObj_smul (N : ModuleCat.{v} A) (a : A) (z : coindObj 𝒜 N) :
    a • z = coindEndAlgHom 𝒜 N a z :=
  rfl

private theorem coindObj_piece (N : ModuleCat.{v} A) (p : ℤ) :
    (coindObj 𝒜 N).grading.piece p =
      _root_.DirectSum.summand k (fun _ : ℤ ↦ RestrictScalars k A N) p :=
  congrFun
    (InternalGrading.ofDecomposition_piece
      (_root_.DirectSum.summand k (fun _ : ℤ ↦ RestrictScalars k A N))) p

private def restrictScalarsLinear (k : Type uk) [CommRing k] [Algebra k A]
    {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) :
    RestrictScalars k A N₁ →ₗ[k] RestrictScalars k A N₂ where
  toFun y := (RestrictScalars.addEquiv k A N₂).symm (g.hom (RestrictScalars.addEquiv k A N₁ y))
  map_add' x y := by simp
  map_smul' c y := by
    rw [RestrictScalars.addEquiv_map_smul, g.hom.map_smul,
      RestrictScalars.addEquiv_symm_map_algebraMap_smul, RingHom.id_apply]

@[simp]
private theorem restrictScalarsLinear_apply {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂)
    (y : RestrictScalars k A N₁) :
    restrictScalarsLinear k g y =
      (RestrictScalars.addEquiv k A N₂).symm (g.hom (RestrictScalars.addEquiv k A N₁ y)) :=
  rfl

@[simp]
private theorem restrictScalarsLinear_id (N : ModuleCat.{v} A) :
    restrictScalarsLinear k (𝟙 N) = LinearMap.id := by
  ext y
  simp

@[simp]
private theorem restrictScalarsLinear_comp {N₁ N₂ N₃ : ModuleCat.{v} A}
    (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    restrictScalarsLinear k (f ≫ g) =
      (restrictScalarsLinear k g).comp (restrictScalarsLinear k f) := by
  ext y
  simp

private def coindMapLinear (k : Type uk) [CommRing k] [Algebra k A]
    {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) :
    (⨁ _ : ℤ, RestrictScalars k A N₁) →ₗ[k] ⨁ _ : ℤ, RestrictScalars k A N₂ :=
  DirectSum.lmap fun _ : ℤ ↦ restrictScalarsLinear k g

private theorem coindMapLinear_endAlgHom {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) (a : A)
    (z : ⨁ _ : ℤ, RestrictScalars k A N₁) :
    coindMapLinear k g (coindEndAlgHom 𝒜 N₁ a z) =
      coindEndAlgHom 𝒜 N₂ a (coindMapLinear k g z) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    induction z using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      rw [← DirectSum.lof_eq_of k, coindEndAlgHom_of_mem 𝒜 N₁ a.property, coindMapLinear,
        DirectSum.lmap_lof, DirectSum.lmap_lof, coindEndAlgHom_of_mem 𝒜 N₂ a.property]
      simp [RestrictScalars.lsmul_apply_apply]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | add a₁ a₂ ha₁ ha₂ => simp [ha₁, ha₂]

/-- Map an `A`-linear map `g : N₁ ⟶ N₂` componentwise across `coindObj`. -/
private def coindMap {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂) :
    coindObj 𝒜 N₁ ⟶ coindObj 𝒜 N₂ :=
  ofHom (M := coindObj 𝒜 N₁) (N := coindObj 𝒜 N₂)
    { toFun := fun z ↦ coindMapLinear k g z
      map_add' := fun x y ↦ (coindMapLinear k g).map_add x y
      map_smul' := fun a z ↦ by
        dsimp only [RingHom.id_apply]
        rw [coindObj_smul, coindObj_smul]
        exact coindMapLinear_endAlgHom 𝒜 g a z }
    (LinearMap.isHomogeneous_def.mpr fun p z hz ↦ by
      rw [add_zero]
      rw [coindObj_piece] at hz ⊢
      obtain ⟨y, rfl⟩ := _root_.DirectSum.mem_summand.mp hz
      simp only [← DirectSum.lof_eq_of k, LinearMap.coe_mk, AddHom.coe_mk, coindMapLinear,
        DirectSum.lmap_lof]
      exact _root_.DirectSum.lof_mem_summand p _)

@[simp]
private theorem coindMap_hom_apply {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂)
    (z : coindObj 𝒜 N₁) :
    (coindMap 𝒜 g).hom z = coindMapLinear k g z :=
  rfl

private def coindCounitAddHom (k : Type uk) (N : ModuleCat.{v} A) :
    (⨁ _ : ℤ, RestrictScalars k A N) →+ N :=
  DirectSum.toAddMonoid fun _ ↦ (RestrictScalars.addEquiv k A N).toAddMonoidHom

private theorem coindCounitAddHom_endAlgHom (N : ModuleCat.{v} A) (a : A)
    (z : ⨁ _ : ℤ, RestrictScalars k A N) :
    coindCounitAddHom k N (coindEndAlgHom 𝒜 N a z) = a • coindCounitAddHom k N z := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    induction z using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      rw [← DirectSum.lof_eq_of k, coindEndAlgHom_of_mem 𝒜 N a.property]
      simp [coindCounitAddHom, RestrictScalars.lsmul_apply_apply, DirectSum.lof_eq_of]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | add a₁ a₂ ha₁ ha₂ => simp [add_smul, ha₁, ha₂]

private def coindCounitObj (N : ModuleCat.{v} A) :
    toModuleCat.obj (coindObj 𝒜 N) ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun z : coindObj 𝒜 N ↦ coindCounitAddHom k N z
      map_add' := fun x y ↦ (coindCounitAddHom k N).map_add x y
      map_smul' := fun a z ↦ by
        dsimp only [RingHom.id_apply]
        rw [coindObj_smul]
        exact coindCounitAddHom_endAlgHom 𝒜 N a z }

@[simp]
private theorem coindCounitObj_apply (N : ModuleCat.{v} A)
    (z : toModuleCat.obj (coindObj 𝒜 N)) :
    (coindCounitObj 𝒜 N).hom z = coindCounitAddHom k N z :=
  rfl

private theorem coindCounitAddHom_mapLinear {N₁ N₂ : ModuleCat.{v} A} (g : N₁ ⟶ N₂)
    (z : ⨁ _ : ℤ, RestrictScalars k A N₁) :
    coindCounitAddHom k N₂ (coindMapLinear k g z) = g.hom (coindCounitAddHom k N₁ z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    rw [← DirectSum.lof_eq_of k, coindMapLinear, DirectSum.lmap_lof]
    simp [coindCounitAddHom, DirectSum.lof_eq_of]
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]

omit [GradedAlgebra 𝒜] in
private def toRestrictScalarsLinear
    {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A} (f : toModuleCat.obj M ⟶ N) :
    M →ₗ[k] RestrictScalars k A N where
  toFun m := (RestrictScalars.addEquiv k A N).symm (f.hom m)
  map_add' x y := by simp
  map_smul' c m := by
    rw [← algebraMap_smul A c m, f.hom.map_smul,
      RestrictScalars.addEquiv_symm_map_algebraMap_smul, RingHom.id_apply]

omit [GradedAlgebra 𝒜] in
@[simp]
private theorem toRestrictScalarsLinear_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) (m : M) :
    toRestrictScalarsLinear 𝒜 f m = (RestrictScalars.addEquiv k A N).symm (f.hom m) :=
  rfl

private def coindLiftLinear {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) : M →ₗ[k] ⨁ _ : ℤ, RestrictScalars k A N :=
  DirectSum.homogeneousExtend M.grading.piece fun p ↦
    (DirectSum.lof k ℤ (fun _ ↦ RestrictScalars k A N) p).comp
      ((toRestrictScalarsLinear 𝒜 f).comp (M.grading.piece p).subtype)

omit [GradedAlgebra 𝒜] in
private theorem coindLiftLinear_of_mem {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) {p : ℤ} {x : M} (hx : x ∈ M.grading.piece p) :
    coindLiftLinear 𝒜 f x =
      DirectSum.lof k ℤ (fun _ ↦ RestrictScalars k A N) p
        ((RestrictScalars.addEquiv k A N).symm (f.hom x)) := by
  rw [coindLiftLinear, DirectSum.homogeneousExtend_of_mem M.grading.piece _ hx]
  simp

private theorem coindLiftLinear_smul {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) (a : A) (m : M) :
    coindLiftLinear 𝒜 f (a • m) = coindEndAlgHom 𝒜 N a (coindLiftLinear 𝒜 f m) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous q a =>
    induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
    | zero => simp
    | @homogeneous p x =>
      have hax : (a : A) • (x : M) ∈ M.grading.piece (q + p) :=
        SetLike.GradedSMul.smul_mem a.property x.property
      rw [coindLiftLinear_of_mem 𝒜 f hax, coindLiftLinear_of_mem 𝒜 f x.property,
        coindEndAlgHom_of_mem 𝒜 N a.property, RestrictScalars.lsmul_apply_apply,
        AddEquiv.apply_symm_apply]
      exact congrArg
        (fun y ↦ DirectSum.lof k ℤ (fun _ ↦ RestrictScalars k A N) (q + p)
          ((RestrictScalars.addEquiv k A N).symm y))
        (f.hom.map_smul (a : A) ((x : M) : toModuleCat.obj M))
    | add m₁ m₂ hm₁ hm₂ => simp [smul_add, hm₁, hm₂]
  | add a₁ a₂ ha₁ ha₂ => simp [add_smul, ha₁, ha₂]

private def coindLiftObj {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) : M ⟶ coindObj 𝒜 N :=
  ofHom (M := M) (N := coindObj 𝒜 N)
    { toFun := fun m ↦ coindLiftLinear 𝒜 f m
      map_add' := fun x y ↦ (coindLiftLinear 𝒜 f).map_add x y
      map_smul' := fun a m ↦ by
        dsimp only [RingHom.id_apply]
        rw [coindObj_smul]
        exact coindLiftLinear_smul 𝒜 f a m }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      simp only [add_zero, coindObj_piece, LinearMap.coe_mk, AddHom.coe_mk]
      rw [coindLiftLinear_of_mem 𝒜 f hx]
      exact _root_.DirectSum.lof_mem_summand p _)

@[simp]
private theorem coindLiftObj_hom_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) (m : M) :
    (coindLiftObj 𝒜 f).hom m = coindLiftLinear 𝒜 f m :=
  rfl

private theorem coindLiftLinear_comp_coindCounitObj {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (g : M ⟶ coindObj 𝒜 N) (m : M) :
    coindLiftLinear 𝒜 (toModuleCat.map g ≫ coindCounitObj 𝒜 N) m = g.hom m := by
  induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
  | zero => simp only [map_zero]
  | @homogeneous p x =>
    have hgx : g.hom x ∈ (coindObj 𝒜 N).grading.piece p := map_mem g x.property
    rw [coindObj_piece] at hgx
    obtain ⟨y, hy⟩ := _root_.DirectSum.mem_summand.mp hgx
    have hgx_eq : (g.hom x : ⨁ _ : ℤ, RestrictScalars k A N) =
        DirectSum.of (fun _ ↦ RestrictScalars k A N) p y := hy.symm
    rw [coindLiftLinear_of_mem 𝒜 _ x.property, toModuleCat_map, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, coindCounitObj_apply, hgx_eq, coindCounitAddHom,
      DirectSum.toAddMonoid_of, DirectSum.lof_eq_of]
    simp
  | add m₁ m₂ hm₁ hm₂ => simp only [map_add, hm₁, hm₂]

/-- The **coinduction functor** `ModuleCat A ⥤ GradedModuleCat 𝒜`, right adjoint to forgetting
the internal grading. -/
def coindFunctor : ModuleCat.{v} A ⥤ GradedModuleCat.{v} 𝒜 where
  obj := coindObj 𝒜
  map := coindMap 𝒜
  map_id N := hom_ext <| by
    have h : coindMapLinear k (𝟙 N) = LinearMap.id := by
      simp only [coindMapLinear, restrictScalarsLinear_id, DirectSum.lmap_id]
    exact LinearMap.ext fun z ↦ LinearMap.congr_fun h z
  map_comp f g := hom_ext <| by
    have h : coindMapLinear k (f ≫ g) = (coindMapLinear k g).comp (coindMapLinear k f) := by
      simp only [coindMapLinear, restrictScalarsLinear_comp, ← DirectSum.lmap_comp]
    exact LinearMap.ext fun z ↦ LinearMap.congr_fun h z

attribute [local implicit_reducible] coindFunctor

/-- The ungraded `A`-linear counit `toModuleCat ((coindFunctor 𝒜).obj N) ⟶ N`, summing homogeneous
coordinates in `N`. -/
def coindCounit (N : ModuleCat.{v} A) :
    toModuleCat.obj ((coindFunctor 𝒜).obj N) ⟶ N :=
  coindCounitObj 𝒜 N

/-- The counit `coindCounit 𝒜 N` is surjective, hence an epimorphism in `ModuleCat A`. -/
instance epi_coindCounit (N : ModuleCat.{v} A) : Epi (coindCounit 𝒜 N) := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  refine ⟨DirectSum.of (fun _ : ℤ ↦ RestrictScalars k A N) (0 : ℤ)
    ((RestrictScalars.addEquiv k A N).symm y), ?_⟩
  rw [coindCounit, coindCounitObj, ModuleCat.ofHom_apply]
  simp [coindCounitAddHom]

/-- Naturality of `coindCounit` with respect to morphisms in `ModuleCat A`. -/
@[reassoc]
theorem toModuleCat_map_coindFunctor_comp_coindCounit {N₁ N₂ : ModuleCat.{v} A}
    (g : N₁ ⟶ N₂) :
    toModuleCat.map ((coindFunctor 𝒜).map g) ≫ coindCounit 𝒜 N₂ = coindCounit 𝒜 N₁ ≫ g :=
  ModuleCat.hom_ext (LinearMap.ext fun z ↦ coindCounitAddHom_mapLinear (k := k) g z)

/-- The `simp`-normal form of `toModuleCat_map_coindFunctor_comp_coindCounit` after
`toModuleCat_map`. -/
@[reassoc (attr := simp)]
theorem ofHom_hom_coindFunctor_map_comp_coindCounit {N₁ N₂ : ModuleCat.{v} A}
    (g : N₁ ⟶ N₂) :
    ModuleCat.ofHom ((coindFunctor 𝒜).map g).hom ≫ coindCounit 𝒜 N₂ = coindCounit 𝒜 N₁ ≫ g := by
  rw [← toModuleCat_map]
  exact toModuleCat_map_coindFunctor_comp_coindCounit 𝒜 g

/-- Lift an ungraded `A`-linear morphism `toModuleCat.obj M ⟶ N` to a degree-zero graded morphism
`M ⟶ (coindFunctor 𝒜).obj N`. -/
def coindLift {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) : M ⟶ (coindFunctor 𝒜).obj N :=
  coindLiftObj 𝒜 f

/-- Composing `coindLift 𝒜 f` with the counit recovers `f`. -/
@[reassoc]
theorem toModuleCat_map_coindLift_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (f : toModuleCat.obj M ⟶ N) :
    toModuleCat.map (coindLift 𝒜 f) ≫ coindCounit 𝒜 N = f := by
  refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  rw [toModuleCat_map, coindLift, coindCounit, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, coindLiftObj_hom_apply, coindCounitObj_apply]
  induction m using DirectSum.Decomposition.inductionOn M.grading.piece with
  | zero => simp
  | @homogeneous p x =>
    rw [coindLiftLinear_of_mem 𝒜 f x.property]
    simp [coindCounitAddHom, DirectSum.lof_eq_of]
  | add m₁ m₂ hm₁ hm₂ => simp [hm₁, hm₂]

/-- The `simp`-normal form of `toModuleCat_map_coindLift_comp_coindCounit` after
`toModuleCat_map`. -/
@[reassoc (attr := simp)]
theorem ofHom_hom_coindLift_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (f : toModuleCat.obj M ⟶ N) :
    ModuleCat.ofHom (coindLift 𝒜 f).hom ≫ coindCounit 𝒜 N = f := by
  rw [← toModuleCat_map]
  exact toModuleCat_map_coindLift_comp_coindCounit 𝒜 f

/-- Lifting a monomorphism `f : toModuleCat.obj M ⟶ N` yields a monomorphism in
`GradedModuleCat 𝒜`. -/
instance {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) [Mono f] : Mono (coindLift 𝒜 f) := by
  have : Mono (toModuleCat.map (coindLift 𝒜 f) ≫ coindCounit 𝒜 N) := by
    rw [toModuleCat_map_coindLift_comp_coindCounit]
    infer_instance
  exact toModuleCat.mono_of_mono_map (mono_of_mono _ (coindCounit 𝒜 N))

/-- Lifting the counit composite of a graded morphism `g : M ⟶ (coindFunctor 𝒜).obj N` recovers
`g`. -/
theorem coindLift_toModuleCat_map_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (g : M ⟶ (coindFunctor 𝒜).obj N) :
    coindLift 𝒜 (toModuleCat.map g ≫ coindCounit 𝒜 N) = g :=
  hom_ext (LinearMap.ext fun m ↦ coindLiftLinear_comp_coindCounitObj 𝒜 g m)

/-- The `simp`-normal form of `coindLift_toModuleCat_map_comp_coindCounit` after
`toModuleCat_map`. -/
@[simp]
theorem coindLift_ofHom_hom_comp_coindCounit {M : GradedModuleCat.{v} 𝒜}
    {N : ModuleCat.{v} A} (g : M ⟶ (coindFunctor 𝒜).obj N) :
    coindLift 𝒜 (ModuleCat.ofHom g.hom ≫ coindCounit 𝒜 N) = g := by
  rw [← toModuleCat_map]
  exact coindLift_toModuleCat_map_comp_coindCounit 𝒜 g

/-- Lifting `coindCounit 𝒜 N` itself yields the identity on `(coindFunctor 𝒜).obj N`. -/
@[simp]
theorem coindLift_coindCounit (N : ModuleCat.{v} A) :
    coindLift 𝒜 (coindCounit 𝒜 N) = 𝟙 ((coindFunctor 𝒜).obj N) := by
  rw [← Category.id_comp (coindCounit 𝒜 N), ← toModuleCat.map_id,
    coindLift_toModuleCat_map_comp_coindCounit]

/-- Morphisms into `(coindFunctor 𝒜).obj N` are uniquely determined by their ungraded composites
with `coindCounit 𝒜 N`. -/
@[ext]
theorem coind_hom_ext {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    {f g : M ⟶ (coindFunctor 𝒜).obj N}
    (h : toModuleCat.map f ≫ coindCounit 𝒜 N = toModuleCat.map g ≫ coindCounit 𝒜 N) :
    f = g := by
  rw [← coindLift_toModuleCat_map_comp_coindCounit 𝒜 f, h,
    coindLift_toModuleCat_map_comp_coindCounit]

/-- Precomposing `coindLift 𝒜 f` with a graded morphism `u` lifts `toModuleCat.map u ≫ f`. -/
@[reassoc (attr := simp)]
theorem comp_coindLift {M₁ M₂ : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (u : M₁ ⟶ M₂) (f : toModuleCat.obj M₂ ⟶ N) :
    u ≫ coindLift 𝒜 f = coindLift 𝒜 (toModuleCat.map u ≫ f) := by
  apply coind_hom_ext
  rw [Functor.map_comp, Category.assoc, toModuleCat_map_coindLift_comp_coindCounit,
    toModuleCat_map_coindLift_comp_coindCounit]

/-- Postcomposing `coindLift 𝒜 f` with `(coindFunctor 𝒜).map g` lifts `f ≫ g`. -/
@[reassoc (attr := simp)]
theorem coindLift_comp_map {M : GradedModuleCat.{v} 𝒜} {N₁ N₂ : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N₁) (g : N₁ ⟶ N₂) :
    coindLift 𝒜 f ≫ (coindFunctor 𝒜).map g = coindLift 𝒜 (f ≫ g) := by
  apply coind_hom_ext
  rw [Functor.map_comp, Category.assoc, toModuleCat_map_coindFunctor_comp_coindCounit,
    ← Category.assoc, toModuleCat_map_coindLift_comp_coindCounit,
    toModuleCat_map_coindLift_comp_coindCounit]

/-- **Forgetting the grading is left adjoint to coinduction.** -/
def toModuleCatCoindAdj : toModuleCat.{v} (𝒜 := 𝒜) ⊣ coindFunctor.{v} 𝒜 :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        { toFun := coindLift 𝒜
          invFun := fun g ↦ toModuleCat.map g ≫ coindCounit 𝒜 N
          left_inv := toModuleCat_map_coindLift_comp_coindCounit 𝒜
          right_inv := coindLift_toModuleCat_map_comp_coindCounit 𝒜 }
      homEquiv_naturality_left_symm := fun _ _ ↦ by
        simp only [Equiv.coe_fn_symm_mk, Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := fun f g ↦
        (coindLift_comp_map 𝒜 f g).symm }

/-- The forward hom-equivalence of `toModuleCatCoindAdj` is `coindLift`. -/
@[simp]
theorem toModuleCatCoindAdj_homEquiv_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (f : toModuleCat.obj M ⟶ N) :
    (toModuleCatCoindAdj 𝒜).homEquiv M N f = coindLift 𝒜 f := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse hom-equivalence of `toModuleCatCoindAdj` composes with `coindCounit`. -/
@[simp]
theorem toModuleCatCoindAdj_homEquiv_symm_apply {M : GradedModuleCat.{v} 𝒜} {N : ModuleCat.{v} A}
    (g : M ⟶ (coindFunctor 𝒜).obj N) :
    ((toModuleCatCoindAdj 𝒜).homEquiv M N).symm g = toModuleCat.map g ≫ coindCounit 𝒜 N := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit of `toModuleCatCoindAdj` at `M` is `coindLift 𝒜 (𝟙 (toModuleCat.obj M))`. -/
@[simp]
theorem toModuleCatCoindAdj_unit_app (M : GradedModuleCat.{v} 𝒜) :
    (toModuleCatCoindAdj 𝒜).unit.app M = coindLift 𝒜 (𝟙 (toModuleCat.obj M)) := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_unit_app]
  rfl

/-- The counit of `toModuleCatCoindAdj` at `N` is `coindCounit 𝒜 N`. -/
@[simp]
theorem toModuleCatCoindAdj_counit_app (N : ModuleCat.{v} A) :
    (toModuleCatCoindAdj 𝒜).counit.app N = coindCounit 𝒜 N := by
  rw [toModuleCatCoindAdj, Adjunction.mkOfHomEquiv_counit_app, Equiv.coe_fn_symm_mk,
    CategoryTheory.Functor.map_id, Category.id_comp]

instance : (toModuleCat.{v} (𝒜 := 𝒜)).IsLeftAdjoint :=
  (toModuleCatCoindAdj 𝒜).isLeftAdjoint

instance : (coindFunctor.{v} 𝒜).IsRightAdjoint :=
  (toModuleCatCoindAdj 𝒜).isRightAdjoint

/-- Coinduction is an additive functor, as a right adjoint to `toModuleCat`. -/
instance : (coindFunctor.{v} 𝒜).Additive :=
  (toModuleCatCoindAdj 𝒜).right_adjoint_additive

/-- Coinduction is faithful, since every counit component `coindCounit 𝒜 N` is an epimorphism. -/
instance : (coindFunctor.{v} 𝒜).Faithful := by
  have : ∀ N, Epi ((toModuleCatCoindAdj 𝒜).counit.app N) := fun N ↦ by
    rw [toModuleCatCoindAdj_counit_app]
    exact epi_coindCounit 𝒜 N
  exact (toModuleCatCoindAdj 𝒜).faithful_R_of_epi_counit_app

/-- Coinduction preserves injective objects, since `toModuleCat` preserves monomorphisms. -/
instance injective_coindFunctor_obj (N : ModuleCat.{v} A) [Injective N] :
    Injective ((coindFunctor 𝒜).obj N) :=
  Injective.injective_of_adjoint (toModuleCatCoindAdj 𝒜) N

/-- Every category of graded `𝒜`-modules in universe `max v uA` has enough injectives. -/
theorem enoughInjectives : EnoughInjectives (GradedModuleCat.{max v uA} 𝒜) :=
  letI := ModuleCat.enoughInjectives.{v, uA} A
  EnoughInjectives.of_adjunction (toModuleCatCoindAdj 𝒜)

/-- When `A` is small in universe `v` (in particular for `v = uA`), `GradedModuleCat.{v} 𝒜` has
enough injectives. -/
instance [Small.{v} A] : EnoughInjectives (GradedModuleCat.{v} 𝒜) :=
  EnoughInjectives.of_adjunction (toModuleCatCoindAdj 𝒜)

end TauCeti.GradedModuleCat
