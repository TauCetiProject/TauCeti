/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Basic

/-!
# Banach representations

A *Banach representation* of a topological monoid `G` over a nontrivially normed field `𝕜` is a
Banach space over `𝕜` with a linear action of `G` whose action map `G × V → V` is jointly
continuous. For `𝕜 = ℚ_p` and `G` the absolute Galois group of a `p`-adic field these are the
objects of Fontaine's category of Banach Galois representations, the ambient category in which
almost `C`-representations live. Morphisms are the continuous equivariant linear maps; the norm is
part of the data of an object only up to the isomorphisms of the category, which are the
equivariant continuous linear equivalences, so objects are Banach spaces up to equivalent norms.

This file builds the category `TauCeti.BanachRep 𝕜 G`, with its additive structure, a zero object
and binary biproducts, and the objects used to build its exact structure: closed invariant
subspaces and quotients by them, with their universal properties. The quotient by the zero
subspace is isomorphic to the representation itself, and the quotient by the whole space is
zero. By the open mapping theorem, a morphism is an isomorphism as soon as it is bijective, and a
surjective morphism induces an isomorphism from the quotient by its kernel. The action is a
`TauCeti.ContinuousRep`, so joint continuity is part of every object, as for Galois
representations.

## Main definitions

* `TauCeti.BanachRep 𝕜 G`: the category of Banach representations; a morphism `f` has an
  underlying continuous linear map `f.hom`.
* `TauCeti.BanachRep.toTopModuleCat`: the faithful forgetful functor to topological modules.
* `TauCeti.BanachRep.prod`: the product of two Banach representations, a biproduct.
* `TauCeti.BanachRep.subrepresentation`, `TauCeti.BanachRep.subrepresentationι`,
  `TauCeti.BanachRep.subrepresentationLift`: a closed invariant subspace, its inclusion, and the
  factorization of a morphism with values in it.
* `TauCeti.BanachRep.quotient`, `TauCeti.BanachRep.quotientπ`, `TauCeti.BanachRep.quotientDesc`:
  the quotient by a closed invariant subspace, its projection, and the factorization of a
  morphism killing the subspace.
* `TauCeti.BanachRep.quotientFactor`: the projection `X ⧸ W ⟶ X ⧸ W'` between quotients by
  closed invariant subspaces `W ≤ W'`.

## Main results

* `TauCeti.BanachRep.isIso_iff_bijective`: a morphism is an isomorphism exactly when it is
  bijective.
* `TauCeti.BanachRep.isIso_quotientDesc_ker`: the first isomorphism theorem, a surjective morphism
  induces an isomorphism from the quotient by its kernel.
* `TauCeti.BanachRep.isZero_iff_subsingleton`: the zero objects are the zero spaces.
* `TauCeti.BanachRep` has a zero object and binary biproducts, and the forgetful functor to
  topological modules reflects isomorphisms.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Documenta Mathematica, Extra Volume Kato
  (2003), 285–385, §1.2.
* P. Colmez and W. Nizioł, *On the cohomology of `p`-adic analytic spaces, II: The
  `C_st`-conjecture* (2025), §2.1.
-/

public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

/-- **A Banach representation** of the topological monoid `G` over `𝕜`: a Banach space `V` over
`𝕜` together with a linear action of `G` whose action map `G × V → V` is jointly continuous. -/
structure BanachRep (𝕜 : Type u) [NontriviallyNormedField 𝕜] (G : Type v) [Monoid G]
    [TopologicalSpace G] where
  /-- The underlying Banach space. -/
  V : Type w
  [isNormedAddCommGroup : NormedAddCommGroup V]
  [isNormedSpace : NormedSpace 𝕜 V]
  [isCompleteSpace : CompleteSpace V]
  /-- The jointly continuous action of `G`. -/
  ρ : ContinuousRep G 𝕜 V

namespace BanachRep

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {G : Type v} [Monoid G] [TopologicalSpace G]

attribute [instance] isNormedAddCommGroup isNormedSpace isCompleteSpace

instance : CoeSort (BanachRep.{w} 𝕜 G) (Type w) := ⟨V⟩

attribute [coe] V

/-- The Banach representation given by a jointly continuous action on a Banach space. -/
abbrev of {V : Type w} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    (ρ : ContinuousRep G 𝕜 V) : BanachRep.{w} 𝕜 G :=
  ⟨V, ρ⟩

variable {X Y Z : BanachRep.{w} 𝕜 G}

/-- A morphism of Banach representations: a continuous linear map commuting with the actions. -/
@[ext]
structure Hom (X Y : BanachRep.{w} 𝕜 G) where
  /-- The underlying continuous linear map. -/
  hom : X →L[𝕜] Y
  /-- The underlying map is equivariant. -/
  hom_comm_apply : ∀ (g : G) (x : X), hom (X.ρ g x) = Y.ρ g (hom x)

attribute [simp] Hom.hom_comm_apply

instance : Category (BanachRep.{w} 𝕜 G) where
  Hom := Hom
  id X := ⟨ContinuousLinearMap.id 𝕜 X, fun _ _ => rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun _ _ => by simp⟩

@[simp]
theorem hom_id : (𝟙 X : X ⟶ X).hom = ContinuousLinearMap.id 𝕜 X :=
  (rfl)

@[simp]
theorem hom_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.comp f.hom :=
  (rfl)

/-- Two morphisms of Banach representations with the same underlying map are equal. -/
@[ext]
theorem hom_ext {f f' : X ⟶ Y} (h : f.hom = f'.hom) : f = f' :=
  Hom.ext h

theorem hom_injective : Function.Injective (Hom.hom : (X ⟶ Y) → (X →L[𝕜] Y)) :=
  fun _ _ => hom_ext

/-! ### The additive structure -/

instance : Zero (X ⟶ Y) := ⟨⟨0, fun _ _ => by simp⟩⟩

instance : Add (X ⟶ Y) := ⟨fun f f' => ⟨f.hom + f'.hom, fun _ _ => by simp⟩⟩

instance : Neg (X ⟶ Y) := ⟨fun f => ⟨-f.hom, fun _ _ => by simp⟩⟩

instance : Sub (X ⟶ Y) := ⟨fun f f' => ⟨f.hom - f'.hom, fun _ _ => by simp⟩⟩

instance : SMul ℕ (X ⟶ Y) := ⟨fun n f => ⟨n • f.hom, fun _ _ => by simp⟩⟩

instance : SMul ℤ (X ⟶ Y) := ⟨fun n f => ⟨n • f.hom, fun _ _ => by simp⟩⟩

@[simp]
theorem hom_zero : (0 : X ⟶ Y).hom = 0 :=
  (rfl)

@[simp]
theorem hom_add (f f' : X ⟶ Y) : (f + f').hom = f.hom + f'.hom :=
  (rfl)

@[simp]
theorem hom_neg (f : X ⟶ Y) : (-f).hom = -f.hom :=
  (rfl)

@[simp]
theorem hom_sub (f f' : X ⟶ Y) : (f - f').hom = f.hom - f'.hom :=
  (rfl)

@[simp]
theorem hom_nsmul (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom :=
  (rfl)

@[simp]
theorem hom_zsmul (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom :=
  (rfl)

instance : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup (Hom.hom : (X ⟶ Y) → (X →L[𝕜] Y)) hom_injective
    (rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Preadditive (BanachRep.{w} 𝕜 G) where

/-- A morphism of Banach representations that is injective on vectors is a monomorphism. -/
theorem mono_of_injective (f : X ⟶ Y) (hf : Function.Injective f.hom) : Mono f :=
  ⟨fun _ _ w => hom_ext (ContinuousLinearMap.ext fun x => hf congr(($w).hom x))⟩

/-- A morphism of Banach representations that is surjective on vectors is an epimorphism. -/
theorem epi_of_surjective (f : X ⟶ Y) (hf : Function.Surjective f.hom) : Epi f :=
  ⟨fun _ _ w => hom_ext (ContinuousLinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := hf y
    exact congr(($w).hom x))⟩

/-! ### Isomorphisms -/

/-- **A bijective morphism of Banach representations is an isomorphism**: by the open mapping
theorem its inverse is continuous, and the inverse of an equivariant bijection is equivariant. -/
theorem isIso_of_bijective (f : X ⟶ Y) (hf : Function.Bijective f.hom) : IsIso f := by
  let e := ContinuousLinearEquiv.ofBijective f.hom (LinearMap.ker_eq_bot.mpr hf.1)
    (LinearMap.range_eq_top.mpr hf.2)
  have he : ∀ (g : G) (y : Y), e.symm (Y.ρ g y) = X.ρ g (e.symm y) := fun g y =>
    e.injective (by simp [e, ContinuousLinearEquiv.ofBijective_apply_symm_apply])
  refine ⟨⟨e.symm.toContinuousLinearMap, he⟩, hom_ext ?_, hom_ext ?_⟩
  · ext x
    exact e.symm_apply_apply x
  · ext y
    exact e.apply_symm_apply y

/-- An isomorphism of Banach representations is bijective on vectors. -/
theorem bijective_of_isIso (f : X ⟶ Y) [IsIso f] : Function.Bijective f.hom := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(inv f).hom, fun x => ?_, fun y => ?_⟩
  · have h := congr($(IsIso.hom_inv_id f).hom x)
    rwa [hom_comp, hom_id] at h
  · have h := congr($(IsIso.inv_hom_id f).hom y)
    rwa [hom_comp, hom_id] at h

/-- **A morphism of Banach representations is an isomorphism exactly when it is bijective.** -/
theorem isIso_iff_bijective (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f.hom :=
  ⟨fun _ => bijective_of_isIso f, isIso_of_bijective f⟩

/-! ### Invariant subspaces attached to a morphism -/

/-- The range of a morphism of Banach representations is invariant: it is the subrepresentation
`Representation.IntertwiningMap.range` of the underlying intertwining map. -/
theorem range_invariant (f : X ⟶ Y) :
    ∀ (g : G), ∀ y ∈ LinearMap.range (f.hom : X →ₗ[𝕜] Y), Y.ρ g y ∈ LinearMap.range
      (f.hom : X →ₗ[𝕜] Y) :=
  ((f.hom : X →ₗ[𝕜] Y).intertwiningMap_of_isIntertwiningMap (ρ := X.ρ.toRepresentation)
    (σ := Y.ρ.toRepresentation) f.hom_comm_apply).range.apply_mem_toSubmodule

/-- The kernel of a morphism of Banach representations is invariant: it is the subrepresentation
`Representation.IntertwiningMap.ker` of the underlying intertwining map. -/
theorem ker_invariant (f : X ⟶ Y) :
    ∀ (g : G), ∀ x ∈ LinearMap.ker (f.hom : X →ₗ[𝕜] Y), X.ρ g x ∈ LinearMap.ker
      (f.hom : X →ₗ[𝕜] Y) :=
  ((f.hom : X →ₗ[𝕜] Y).intertwiningMap_of_isIntertwiningMap (ρ := X.ρ.toRepresentation)
    (σ := Y.ρ.toRepresentation) f.hom_comm_apply).ker.apply_mem_toSubmodule

/-! ### Lattice operations on invariant subspaces -/

variable (X) in
/-- The zero subspace of a Banach representation is invariant. -/
theorem bot_invariant : ∀ (g : G), ∀ x ∈ (⊥ : Submodule 𝕜 X), X.ρ g x ∈ (⊥ : Submodule 𝕜 X) := by
  simp

variable (X) in
/-- The whole space of a Banach representation is invariant. -/
theorem top_invariant : ∀ (g : G), ∀ x ∈ (⊤ : Submodule 𝕜 X), X.ρ g x ∈ (⊤ : Submodule 𝕜 X) := by
  simp

/-- The sum of two invariant subspaces of a Banach representation is invariant: it is the
supremum of the two subrepresentations. -/
theorem sup_invariant {B B' : Submodule 𝕜 Y} (hB : ∀ (g : G), ∀ y ∈ B, Y.ρ g y ∈ B)
    (hB' : ∀ (g : G), ∀ y ∈ B', Y.ρ g y ∈ B') : ∀ (g : G), ∀ y ∈ B ⊔ B', Y.ρ g y ∈ B ⊔ B' :=
  (⟨B, hB⟩ ⊔ ⟨B', hB'⟩ : Subrepresentation Y.ρ.toRepresentation).apply_mem_toSubmodule

/-! ### The forgetful functor to topological modules -/

/-- The forgetful functor from Banach representations to topological `𝕜`-modules. -/
@[expose]
def toTopModuleCat : BanachRep.{w} 𝕜 G ⥤ TopModuleCat.{w} 𝕜 where
  obj X := TopModuleCat.of 𝕜 X
  map f := TopModuleCat.ofHom f.hom

@[simp]
theorem toTopModuleCat_obj (X : BanachRep.{w} 𝕜 G) : toTopModuleCat.obj X = TopModuleCat.of 𝕜 X :=
  (rfl)

@[simp]
theorem toTopModuleCat_map_hom (f : X ⟶ Y) : (toTopModuleCat.map f).hom = f.hom :=
  (rfl)

instance : (toTopModuleCat (𝕜 := 𝕜) (G := G)).Faithful where
  map_injective h := hom_ext congr(($h).hom)

/-- The forgetful functor to topological modules reflects isomorphisms: a morphism whose
underlying continuous linear map is invertible is bijective. -/
instance : (toTopModuleCat (𝕜 := 𝕜) (G := G)).ReflectsIsomorphisms where
  reflects f _ :=
    isIso_of_bijective f (ConcreteCategory.bijective_of_isIso (toTopModuleCat.map f))

/-! ### The zero object -/

/-- **The zero objects are the zero spaces.** -/
theorem isZero_iff_subsingleton : IsZero X ↔ Subsingleton X := by
  rw [IsZero.iff_id_eq_zero]
  refine ⟨fun h => ⟨fun x y => ?_⟩, fun _ => hom_ext (ContinuousLinearMap.ext
    fun _ => Subsingleton.elim _ _)⟩
  have hx : x = 0 := by simpa using congr(($h).hom x)
  have hy : y = 0 := by simpa using congr(($h).hom y)
  rw [hx, hy]

instance : HasZeroObject (BanachRep.{w} 𝕜 G) :=
  ⟨⟨of (ContinuousRep.trivial G 𝕜 PUnit.{w + 1}),
    isZero_iff_subsingleton.mpr inferInstanceAs (Subsingleton PUnit)⟩⟩

/-! ### Products -/

/-- **The product of two Banach representations**: `G` acts componentwise on `X × Y`. -/
noncomputable abbrev prod (X Y : BanachRep.{w} 𝕜 G) : BanachRep.{w} 𝕜 G :=
  of (X.ρ.prod Y.ρ)

/-- `G` acts componentwise on a product. -/
theorem prod_ρ_apply (g : G) (x : prod X Y) : (prod X Y).ρ g x = (X.ρ g x.1, Y.ρ g x.2) :=
  ContinuousRep.prod_apply X.ρ Y.ρ g x

/-- The first projection out of a product. -/
noncomputable def prodFst (X Y : BanachRep.{w} 𝕜 G) : prod X Y ⟶ X :=
  ⟨ContinuousLinearMap.fst 𝕜 X Y, fun _ _ => by simp⟩

/-- The second projection out of a product. -/
noncomputable def prodSnd (X Y : BanachRep.{w} 𝕜 G) : prod X Y ⟶ Y :=
  ⟨ContinuousLinearMap.snd 𝕜 X Y, fun _ _ => by simp⟩

/-- The first inclusion into a product. -/
noncomputable def prodInl (X Y : BanachRep.{w} 𝕜 G) : X ⟶ prod X Y :=
  ⟨ContinuousLinearMap.inl 𝕜 X Y, fun _ _ => by simp⟩

/-- The second inclusion into a product. -/
noncomputable def prodInr (X Y : BanachRep.{w} 𝕜 G) : Y ⟶ prod X Y :=
  ⟨ContinuousLinearMap.inr 𝕜 X Y, fun _ _ => by simp⟩

@[simp]
theorem prodFst_hom : (prodFst X Y).hom = ContinuousLinearMap.fst 𝕜 X Y :=
  (rfl)

@[simp]
theorem prodSnd_hom : (prodSnd X Y).hom = ContinuousLinearMap.snd 𝕜 X Y :=
  (rfl)

@[simp]
theorem prodInl_hom : (prodInl X Y).hom = ContinuousLinearMap.inl 𝕜 X Y :=
  (rfl)

@[simp]
theorem prodInr_hom : (prodInr X Y).hom = ContinuousLinearMap.inr 𝕜 X Y :=
  (rfl)

theorem prodFst_hom_apply (x : prod X Y) : (prodFst X Y).hom x = x.1 :=
  (rfl)

theorem prodSnd_hom_apply (x : prod X Y) : (prodSnd X Y).hom x = x.2 :=
  (rfl)

theorem prodInl_hom_apply (x : X) : (prodInl X Y).hom x = (x, 0) :=
  (rfl)

theorem prodInr_hom_apply (y : Y) : (prodInr X Y).hom y = (0, y) :=
  (rfl)

@[reassoc (attr := simp)]
theorem prodInl_prodFst : prodInl X Y ≫ prodFst X Y = 𝟙 X :=
  (rfl)

@[reassoc (attr := simp)]
theorem prodInl_prodSnd : prodInl X Y ≫ prodSnd X Y = 0 :=
  (rfl)

@[reassoc (attr := simp)]
theorem prodInr_prodFst : prodInr X Y ≫ prodFst X Y = 0 :=
  (rfl)

@[reassoc (attr := simp)]
theorem prodInr_prodSnd : prodInr X Y ≫ prodSnd X Y = 𝟙 Y :=
  (rfl)

theorem prodFst_prodInl_add_prodSnd_prodInr :
    prodFst X Y ≫ prodInl X Y + prodSnd X Y ≫ prodInr X Y = 𝟙 (prod X Y) :=
  -- The total map sends `(a, b)` to `(a, 0) + (0, b)`.
  hom_ext (ContinuousLinearMap.ext fun ⟨a, b⟩ => Prod.ext (add_zero a) (zero_add b))

/-- The product `X × Y` with its projections and inclusions, as a binary bicone. -/
@[expose, simps]
noncomputable def prodBicone (X Y : BanachRep.{w} 𝕜 G) : BinaryBicone X Y where
  pt := prod X Y
  fst := prodFst X Y
  snd := prodSnd X Y
  inl := prodInl X Y
  inr := prodInr X Y

/-- **The product is a biproduct.** -/
noncomputable def prodBiconeIsBilimit (X Y : BanachRep.{w} 𝕜 G) : (prodBicone X Y).IsBilimit :=
  isBinaryBilimitOfTotal _ prodFst_prodInl_add_prodSnd_prodInr

instance : HasBinaryBiproducts (BanachRep.{w} 𝕜 G) where
  has_binary_biproduct X Y := .mk ⟨prodBicone X Y, prodBiconeIsBilimit X Y⟩

/-! ### Closed invariant subspaces and quotients -/

section Subquotient

variable (X) (W : Submodule 𝕜 X) (hW : ∀ (g : G), ∀ x ∈ W, X.ρ g x ∈ W)
  (hWc : IsClosed (W : Set X))

/-- **A closed invariant subspace** of a Banach representation, with the restricted action. -/
noncomputable abbrev subrepresentation : BanachRep.{w} 𝕜 G :=
  haveI := hWc.completeSpace_coe
  of (X.ρ.subrepresentation W hW)

/-- `G` acts on a closed invariant subspace by restriction. -/
theorem subrepresentation_ρ_apply (g : G) (x : subrepresentation X W hW hWc) :
    ((subrepresentation X W hW hWc).ρ g x : X) = X.ρ g (x : W) :=
  ContinuousRep.coe_subrepresentation_apply X.ρ W hW g x

/-- The inclusion of a closed invariant subspace. -/
noncomputable def subrepresentationι : subrepresentation X W hW hWc ⟶ X :=
  ⟨W.subtypeL, fun g x => subrepresentation_ρ_apply X W hW hWc g x⟩

@[simp]
theorem subrepresentationι_hom : (subrepresentationι X W hW hWc).hom = W.subtypeL :=
  (rfl)

theorem subrepresentationι_hom_apply (x : subrepresentation X W hW hWc) :
    (subrepresentationι X W hW hWc).hom x = (x : X) :=
  (rfl)

theorem subrepresentationι_injective : Function.Injective (subrepresentationι X W hW hWc).hom :=
  Subtype.val_injective

instance : Mono (subrepresentationι X W hW hWc) :=
  mono_of_injective _ (subrepresentationι_injective X W hW hWc)

/-- **The universal property of a closed invariant subspace**: a morphism with values in `W`
factors through it. -/
noncomputable def subrepresentationLift {T : BanachRep.{w} 𝕜 G} (k : T ⟶ X)
    (hk : ∀ t, k.hom t ∈ W) : T ⟶ subrepresentation X W hW hWc :=
  ⟨k.hom.codRestrict W hk, fun g t =>
    Subtype.ext ((k.hom_comm_apply g t).trans
      (subrepresentation_ρ_apply X W hW hWc g (k.hom.codRestrict W hk t)).symm)⟩

@[simp]
theorem subrepresentationLift_hom {T : BanachRep.{w} 𝕜 G} (k : T ⟶ X) (hk : ∀ t, k.hom t ∈ W) :
    (subrepresentationLift X W hW hWc k hk).hom = k.hom.codRestrict W hk :=
  (rfl)

theorem subrepresentationLift_hom_apply {T : BanachRep.{w} 𝕜 G} (k : T ⟶ X)
    (hk : ∀ t, k.hom t ∈ W) (t : T) :
    ((subrepresentationLift X W hW hWc k hk).hom t : X) = k.hom t :=
  (rfl)

@[reassoc (attr := simp)]
theorem subrepresentationLift_comp_ι {T : BanachRep.{w} 𝕜 G} (k : T ⟶ X) (hk : ∀ t, k.hom t ∈ W) :
    subrepresentationLift X W hW hWc k hk ≫ subrepresentationι X W hW hWc = k :=
  hom_ext (ContinuousLinearMap.ext fun _ => rfl)

/-- **The quotient** of a Banach representation by a closed invariant subspace, with the quotient
norm and the descended action. -/
noncomputable abbrev quotient : BanachRep.{w} 𝕜 G :=
  haveI : IsClosed (W : Set X) := hWc
  of (X.ρ.quotient W hW)

/-- `G` acts on the quotient by acting on representatives. -/
theorem quotient_ρ_apply_mk (g : G) (x : X) :
    (quotient X W hW hWc).ρ g (Submodule.Quotient.mk x : X ⧸ W) =
      Submodule.Quotient.mk (X.ρ g x) :=
  ContinuousRep.quotient_apply_mk X.ρ W hW g x

/-- The projection onto the quotient by a closed invariant subspace. -/
noncomputable def quotientπ : X ⟶ quotient X W hW hWc :=
  ⟨W.mkQL, fun g x => (quotient_ρ_apply_mk X W hW hWc g x).symm⟩

/-- The projection onto the quotient is `Submodule.mkQL`. -/
@[simp]
theorem quotientπ_hom : (quotientπ X W hW hWc).hom = W.mkQL :=
  (rfl)

theorem quotientπ_hom_apply (x : X) :
    (quotientπ X W hW hWc).hom x = (Submodule.Quotient.mk x : X ⧸ W) :=
  (rfl)

theorem quotientπ_surjective : Function.Surjective (quotientπ X W hW hWc).hom :=
  Submodule.Quotient.mk_surjective W

instance : Epi (quotientπ X W hW hWc) :=
  epi_of_surjective _ (quotientπ_surjective X W hW hWc)

theorem quotientπ_hom_apply_eq_iff (x y : X) :
    (quotientπ X W hW hWc).hom x = (quotientπ X W hW hWc).hom y ↔ x - y ∈ W :=
  Submodule.Quotient.eq W

theorem quotientπ_hom_apply_eq_zero_iff (x : X) : (quotientπ X W hW hWc).hom x = 0 ↔ x ∈ W :=
  Submodule.Quotient.mk_eq_zero W

/-- The projection onto the quotient by the zero subspace is an isomorphism. -/
instance isIso_quotientπ_bot (hW : ∀ (g : G), ∀ x ∈ (⊥ : Submodule 𝕜 X), X.ρ g x ∈ ⊥)
    (hWc : IsClosed ((⊥ : Submodule 𝕜 X) : Set X)) : IsIso (quotientπ X ⊥ hW hWc) :=
  isIso_of_bijective _ ⟨fun x y h => by
    simpa [sub_eq_zero] using (quotientπ_hom_apply_eq_iff X ⊥ hW hWc x y).mp h,
    quotientπ_surjective X ⊥ hW hWc⟩

/-- The quotient by the whole space is a zero object. -/
theorem isZero_quotient_top (hW : ∀ (g : G), ∀ x ∈ (⊤ : Submodule 𝕜 X), X.ρ g x ∈ ⊤)
    (hWc : IsClosed ((⊤ : Submodule 𝕜 X) : Set X)) : IsZero (quotient X ⊤ hW hWc) :=
  isZero_iff_subsingleton.mpr inferInstanceAs (Subsingleton (X ⧸ (⊤ : Submodule 𝕜 X)))

/-- **The universal property of the quotient**: a morphism killing `W` factors through the
quotient by `W`. -/
noncomputable def quotientDesc {T : BanachRep.{w} 𝕜 G} (k : X ⟶ T)
    (hk : ∀ x ∈ W, k.hom x = 0) : quotient X W hW hWc ⟶ T :=
  ⟨W.liftQL k.hom hk, fun g q => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W q
    rw [quotient_ρ_apply_mk]
    exact k.hom_comm_apply g x⟩

@[simp]
theorem quotientDesc_hom {T : BanachRep.{w} 𝕜 G} (k : X ⟶ T) (hk : ∀ x ∈ W, k.hom x = 0) :
    (quotientDesc X W hW hWc k hk).hom = W.liftQL k.hom hk :=
  (rfl)

theorem quotientDesc_hom_quotientπ_hom {T : BanachRep.{w} 𝕜 G} (k : X ⟶ T)
    (hk : ∀ x ∈ W, k.hom x = 0) (x : X) :
    (quotientDesc X W hW hWc k hk).hom ((quotientπ X W hW hWc).hom x) = k.hom x :=
  (rfl)

@[reassoc (attr := simp)]
theorem quotientπ_comp_quotientDesc {T : BanachRep.{w} 𝕜 G} (k : X ⟶ T)
    (hk : ∀ x ∈ W, k.hom x = 0) :
    quotientπ X W hW hWc ≫ quotientDesc X W hW hWc k hk = k :=
  hom_ext (ContinuousLinearMap.ext fun _ => rfl)

end Subquotient

/-- **The first isomorphism theorem**: a surjective morphism of Banach representations induces
an isomorphism from the quotient by its kernel. -/
theorem isIso_quotientDesc_ker {T : BanachRep.{w} 𝕜 G} (k : X ⟶ T)
    (hk : Function.Surjective k.hom) :
    IsIso (quotientDesc X _ (ker_invariant k) k.hom.isClosed_ker k fun _ hx => hx) := by
  have hkc := k.hom.isClosed_ker
  refine isIso_of_bijective _ ⟨fun x y hxy => ?_, fun t => ?_⟩
  · obtain ⟨x, rfl⟩ := quotientπ_surjective X _ (ker_invariant k) hkc x
    obtain ⟨y, rfl⟩ := quotientπ_surjective X _ (ker_invariant k) hkc y
    rw [quotientDesc_hom_quotientπ_hom X _ (ker_invariant k) hkc k (fun _ hx => hx) x,
      quotientDesc_hom_quotientπ_hom X _ (ker_invariant k) hkc k (fun _ hx => hx) y] at hxy
    rw [quotientπ_hom_apply_eq_iff]
    simp [hxy]
  · obtain ⟨x, rfl⟩ := hk t
    exact ⟨_, quotientDesc_hom_quotientπ_hom X _ (ker_invariant k) hkc k (fun _ hx => hx) x⟩

/-! ### Projections between quotients -/

section QuotientFactor

variable (X) {W W' : Submodule 𝕜 X} (hW : ∀ (g : G), ∀ x ∈ W, X.ρ g x ∈ W)
  (hWc : IsClosed (W : Set X)) (hW' : ∀ (g : G), ∀ x ∈ W', X.ρ g x ∈ W')
  (hWc' : IsClosed (W' : Set X)) (h : W ≤ W')

/-- **The projection between quotients** `X ⧸ W ⟶ X ⧸ W'` by closed invariant subspaces
`W ≤ W'`: the morphism induced by `Submodule.factor`. -/
noncomputable def quotientFactor : quotient X W hW hWc ⟶ quotient X W' hW' hWc' :=
  quotientDesc X W hW hWc (quotientπ X W' hW' hWc') fun x hx =>
    (quotientπ_hom_apply_eq_zero_iff X W' hW' hWc' x).mpr (h hx)

/-- The projection between quotients is `Submodule.factor`. -/
@[simp]
theorem quotientFactor_hom_toLinearMap :
    (quotientFactor X hW hWc hW' hWc' h).hom.toLinearMap = Submodule.factor h :=
  Submodule.linearMap_qext _ rfl

theorem quotientFactor_hom_quotientπ_hom (x : X) :
    (quotientFactor X hW hWc hW' hWc' h).hom ((quotientπ X W hW hWc).hom x) =
      (quotientπ X W' hW' hWc').hom x :=
  (rfl)

@[reassoc (attr := simp)]
theorem quotientπ_comp_quotientFactor :
    quotientπ X W hW hWc ≫ quotientFactor X hW hWc hW' hWc' h = quotientπ X W' hW' hWc' :=
  quotientπ_comp_quotientDesc X W hW hWc _ _

theorem quotientFactor_surjective :
    Function.Surjective (quotientFactor X hW hWc hW' hWc' h).hom :=
  Submodule.factor_surjective h

/-- The kernel of the projection `X ⧸ W ⟶ X ⧸ W'` is the image of `W'` in `X ⧸ W`. -/
theorem ker_quotientFactor :
    LinearMap.ker (quotientFactor X hW hWc hW' hWc' h).hom.toLinearMap = W'.map W.mkQ := by
  rw [quotientFactor_hom_toLinearMap, Submodule.ker_mapQ, Submodule.comap_id]

end QuotientFactor

end BanachRep

end TauCeti
