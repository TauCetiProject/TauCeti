/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Ring.Opposite
public import TauCeti.RingTheory.Patching.Projective

/-!
# Patching triples and the patching functor of a fibre product of rings

Let `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` be ring homomorphisms between possibly noncommutative
rings, and let `D = A₁ ×_Q A₂` be their fibre product, Mathlib's `RingHom.pullback π₁ π₂`, with
projections `p₁` and `p₂`. A **patching triple** `(P₁, P₂, α)` consists of finitely generated
projective right modules `P₁` over `A₁` and `P₂` over `A₂` and an isomorphism
`α : P₁ ⊗ Q ≅ P₂ ⊗ Q` of right `Q`-modules; a morphism of patching triples is a pair of module
maps compatible with the isomorphisms. The category of patching triples is the categorical
pullback of the two extension-of-scalars functors on finitely generated projective right modules.

Every finitely generated projective right `D`-module `P` gives the patching triple
`(P ⊗_D A₁, P ⊗_D A₂, α_P)`, whose isomorphism `α_P` is the canonical one through `P ⊗_D Q`
(`RingHom.finiteProjectiveModulesExtendScalarsCompIso` for the square `π₁ ∘ p₁ = π₂ ∘ p₂`). It
sends `(p ⊗ a) ⊗ q` to `(p ⊗ 1) ⊗ (π₁ a * q)`, in particular `(p ⊗ 1) ⊗ 1` to `(p ⊗ 1) ⊗ 1`
(`RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_tmul`); on underlying modules
it is the gluing isomorphism `TauCeti.BalancedExtension.commSqEquiv`. This is the **patching
functor**. Milnor's patching theorem says that it is an equivalence of categories as soon
as `π₁` or `π₂` is surjective; the inverse sends `(P₁, P₂, α)` to the fibre product module
`{(x, y) ∈ P₁ × P₂ | α (x ⊗ 1) = y ⊗ 1}`.

The patching functor is fully faithful for all `π₁` and `π₂`. On underlying modules this is
`TauCeti.BalancedExtension.existsUnique_map_eq_and_map_eq` over the square of opposite rings: a
compatible pair of maps `P ⊗_D Aⱼ → P' ⊗_D Aⱼ` comes from exactly one map `P → P'`, because a
finitely generated projective module over `D` is the patched module of its triple.

When `π₁` or `π₂` is surjective, the patched module `M(P₁, P₂, α)` of every patching triple is
finitely generated projective and its triple is isomorphic to `(P₁, P₂, α)` through the comparison
maps `M ⊗_D Aⱼ → Pⱼ` (`TauCeti.finite_patchedModule`, `TauCeti.projective_patchedModule`,
`TauCeti.PatchedModule.bijective_compareFst`, `TauCeti.PatchedModule.bijective_compareSnd`). This
file packages these module-level statements as the patched module functor and the counit of an
equivalence of categories whose functor is the patching functor: this is **Milnor's patching
theorem** (`RingHom.milnor_patching`). The unit is the isomorphism `p ↦ (p ⊗ 1, p ⊗ 1)` of a
module with the patched module of its triple. Essential surjectivity needs the surjective leg: for
the inclusions `ℤ → ℚ ← ℤ` the fibre product is `ℤ`, and the triple `(ℤ, ℤ, 2)` is not isomorphic
to the image `(ℤ, ℤ, 1)` of any module.

## Main definitions

* `RingHom.PatchingTriples π₁ π₂`: the category of patching triples, with the gluing isomorphism
  `RingHom.PatchingTriples.gluing` of a triple.
* `RingHom.patchingFunctor π₁ π₂`: the functor `P ↦ (P ⊗_D A₁, P ⊗_D A₂, α_P)` from finitely
  generated projective right `D`-modules to patching triples.
* `RingHom.patchedModuleFunctor π₁ π₂ hπ`: with a surjective leg, the functor
  `(P₁, P₂, α) ↦ M(P₁, P₂, α)` from patching triples to finitely generated projective right
  `D`-modules.
* `RingHom.patchingCounitIso hπ T`: the isomorphism of the patching triple of `M(T)` with `T`.
* `RingHom.patchingEquivalence π₁ π₂ hπ`: the equivalence of categories formed by these two
  functors.

## Main results

* `RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_eq_commSqEquiv`: for every
  commuting square, the isomorphism `RingHom.finiteProjectiveModulesExtendScalarsCompIso` is the
  gluing isomorphism `TauCeti.BalancedExtension.commSqEquiv` on underlying modules.
* `RingHom.faithful_patchingFunctor`, `RingHom.full_patchingFunctor`: the patching functor is
  faithful and full.
* `RingHom.milnor_patching`: with a surjective leg, the patching functor is an equivalence.
* `RingHom.fst_patchingEquivalence_unitIso_hom_app`,
  `RingHom.snd_patchingEquivalence_unitIso_hom_app`: the unit sends `p` to `(p ⊗ 1, p ⊗ 1)`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2
  (projective modules over a fibre product of rings).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, Milnor Patching
  Theorem 2.7, p. 12.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti BalancedExtension

namespace RingHom

universe u

section Square

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D] (f₁ : A →+* B) (g₁ : B →+* D)
  (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂)

/-- For every commuting square `g₁ ∘ f₁ = g₂ ∘ f₂`, the component at `P` of
`RingHom.finiteProjectiveModulesExtendScalarsCompIso` is, on underlying modules, the gluing
isomorphism `TauCeti.BalancedExtension.commSqEquiv h P : D ⊗_B (B ⊗_A P) ≃ D ⊗_C (C ⊗_A P)`. -/
theorem finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_eq_commSqEquiv
    (P : (finiteProjectiveModules A).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).hom.app P).hom.hom =
      (commSqEquiv h P.obj).toLinearMap :=
  LinearMap.ext fun x ↦
    (finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_apply f₁ g₁ f₂ g₂ h P x).trans <|
      (LinearEquiv.symm_apply_eq _).2 (cancelBaseChange_commSqEquiv h x).symm

end Square

variable {A₁ A₂ Q : Type u} [Ring A₁] [Ring A₂] [Ring Q] (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)

/-- The category of **patching triples** of ring homomorphisms `π₁ : A₁ →+* Q` and
`π₂ : A₂ →+* Q`: the categorical pullback of the extension-of-scalars functors along `π₁` and `π₂`
on finitely generated projective right modules. An object is a triple `(P₁, P₂, α)` with `Pⱼ` a
finitely generated projective right `Aⱼ`-module and `α : P₁ ⊗ Q ≅ P₂ ⊗ Q` an isomorphism of right
`Q`-modules; a morphism is a pair of module maps compatible with the isomorphisms. -/
abbrev PatchingTriples : Type (u + 1) :=
  CategoricalPullback (RingHom.op π₁).finiteProjectiveModulesExtendScalars
    (RingHom.op π₂).finiteProjectiveModulesExtendScalars

/-- The **patching functor** of the fibre product `D = A₁ ×_Q A₂` of `π₁ : A₁ →+* Q` and
`π₂ : A₂ →+* Q`: it sends a finitely generated projective right `D`-module `P` to the patching
triple `(P ⊗_D A₁, P ⊗_D A₂, α_P)`, where `α_P : (P ⊗_D A₁) ⊗ Q ≅ (P ⊗_D A₂) ⊗ Q` is the
canonical isomorphism through `P ⊗_D Q`, and a map to the pair of its extensions. -/
-- Exposed so that the components of the image of a module or map are definitionally its
-- extensions, as recorded by the `simps` lemmas.
@[expose, simps! obj_fst obj_snd obj_iso map_fst map_snd]
def patchingFunctor : FiniteProjectiveRight (π₁.pullback π₂) ⥤ π₁.PatchingTriples π₂ :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := (RingHom.op (π₁.pullbackFst π₂)).finiteProjectiveModulesExtendScalars
      snd := (RingHom.op (π₁.pullbackSnd π₂)).finiteProjectiveModulesExtendScalars
      iso := finiteProjectiveModulesExtendScalarsCompIso _ _ _ _ (op_pullback_comm_sq π₁ π₂) }

/-- The first component of the image of a map `f` under the patching functor is, on underlying
modules, the extension `TauCeti.BalancedExtension.map` of `f` along the first projection. -/
private theorem patchingFunctor_map_fst_hom_hom {P P' : FiniteProjectiveRight (π₁.pullback π₂)}
    (f : P ⟶ P') :
    ((patchingFunctor π₁ π₂).map f).fst.hom.hom = map (RingHom.op (π₁.pullbackFst π₂)) f.hom.hom :=
  -- The `eqToHom`s of `finiteProjectiveModulesExtendScalars_map_hom` are identities.
  congr($(patchingFunctor_map_fst π₁ π₂ f).hom.hom).trans
    congr($(finiteProjectiveModulesExtendScalars_map_hom _ f).hom)

/-- The second component of the image of a map `f` under the patching functor is, on underlying
modules, the extension `TauCeti.BalancedExtension.map` of `f` along the second projection. -/
private theorem patchingFunctor_map_snd_hom_hom {P P' : FiniteProjectiveRight (π₁.pullback π₂)}
    (f : P ⟶ P') :
    ((patchingFunctor π₁ π₂).map f).snd.hom.hom = map (RingHom.op (π₁.pullbackSnd π₂)) f.hom.hom :=
  -- The `eqToHom`s of `finiteProjectiveModulesExtendScalars_map_hom` are identities.
  congr($(patchingFunctor_map_snd π₁ π₂ f).hom.hom).trans
    congr($(finiteProjectiveModulesExtendScalars_map_hom _ f).hom)

/-- A map `P → P'` of finitely generated projective right modules over `A₁ ×_Q A₂` is determined
by a compatible pair of maps of their extensions to `A₁` and `A₂`. -/
private theorem existsUnique_patchingFunctor {P P' : FiniteProjectiveRight (π₁.pullback π₂)}
    (g₁ : BalancedExtension (RingHom.op (π₁.pullbackFst π₂)) P.obj →ₗ[A₁ᵐᵒᵖ]
      BalancedExtension (RingHom.op (π₁.pullbackFst π₂)) P'.obj)
    (g₂ : BalancedExtension (RingHom.op (π₁.pullbackSnd π₂)) P.obj →ₗ[A₂ᵐᵒᵖ]
      BalancedExtension (RingHom.op (π₁.pullbackSnd π₂)) P'.obj)
    (hg : ∀ x, commSqEquiv (op_pullback_comm_sq π₁ π₂) P'.obj (map (RingHom.op π₁) g₁ x) =
      map (RingHom.op π₂) g₂ (commSqEquiv (op_pullback_comm_sq π₁ π₂) P.obj x)) :
    ∃! g : P.obj →ₗ[(π₁.pullback π₂)ᵐᵒᵖ] P'.obj,
      map (RingHom.op (π₁.pullbackFst π₂)) g = g₁ ∧ map (RingHom.op (π₁.pullbackSnd π₂)) g = g₂ :=
  existsUnique_map_eq_and_map_eq (op_pullback_comm_sq π₁ π₂)
    (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂) g₁ g₂ hg

/-- The extensions to `Q` of the two components of a morphism of patching triples between images
of the patching functor are intertwined by the gluing isomorphisms `commSqEquiv`. -/
private theorem commSqEquiv_map_hom_fst {P P' : FiniteProjectiveRight (π₁.pullback π₂)}
    (φ : (patchingFunctor π₁ π₂).obj P ⟶ (patchingFunctor π₁ π₂).obj P')
    (x : BalancedExtension (RingHom.op π₁)
      (BalancedExtension (RingHom.op (π₁.pullbackFst π₂)) P.obj)) :
    commSqEquiv (op_pullback_comm_sq π₁ π₂) P'.obj (map (RingHom.op π₁) φ.fst.hom.hom x) =
      map (RingHom.op π₂) φ.snd.hom.hom (commSqEquiv (op_pullback_comm_sq π₁ π₂) P.obj x) :=
  -- The components of `φ.w` are these maps up to the definitional identification of the extended
  -- modules with balanced extensions.
  (LinearMap.congr_fun (finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_eq_commSqEquiv
      _ _ _ _ (op_pullback_comm_sq π₁ π₂) P') _).symm.trans
    ((congr($(φ.w).hom x)).trans (congrArg _ (LinearMap.congr_fun
      (finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_eq_commSqEquiv
        _ _ _ _ (op_pullback_comm_sq π₁ π₂) P) x)))

/-- **The patching functor is faithful**: a map of finitely generated projective right modules over
`A₁ ×_Q A₂` is determined by its extensions to `A₁` and `A₂`. -/
instance faithful_patchingFunctor : (patchingFunctor π₁ π₂).Faithful where
  map_injective {_ _} φ ψ hφψ :=
    ObjectProperty.hom_ext _ <| ModuleCat.hom_ext <|
      (existsUnique_patchingFunctor π₁ π₂ _ _ (commSqEquiv_map _ φ.hom.hom)).unique ⟨rfl, rfl⟩
        ⟨(patchingFunctor_map_fst_hom_hom π₁ π₂ ψ).symm.trans
            (congr($(congrArg CategoricalPullback.Hom.fst hφψ).hom.hom).symm.trans
              (patchingFunctor_map_fst_hom_hom π₁ π₂ φ)),
          (patchingFunctor_map_snd_hom_hom π₁ π₂ ψ).symm.trans
            (congr($(congrArg CategoricalPullback.Hom.snd hφψ).hom.hom).symm.trans
              (patchingFunctor_map_snd_hom_hom π₁ π₂ φ))⟩

/-- **The patching functor is full**: a morphism of patching triples between the images of
finitely generated projective right modules `P` and `P'` over `A₁ ×_Q A₂` is the image of a map
`P → P'`. -/
instance full_patchingFunctor : (patchingFunctor π₁ π₂).Full where
  map_surjective {P P'} φ := by
    obtain ⟨g, hg, -⟩ := existsUnique_patchingFunctor π₁ π₂ _ _ (commSqEquiv_map_hom_fst π₁ π₂ φ)
    exact ⟨ObjectProperty.homMk (ModuleCat.ofHom g), CategoricalPullback.hom_ext
      (ObjectProperty.hom_ext _ (ModuleCat.hom_ext
        ((patchingFunctor_map_fst_hom_hom π₁ π₂ _).trans hg.1)))
      (ObjectProperty.hom_ext _ (ModuleCat.hom_ext
        ((patchingFunctor_map_snd_hom_hom π₁ π₂ _).trans hg.2)))⟩

section Equivalence

variable {π₁ π₂}

/-- The gluing isomorphism `α : P₁ ⊗ Q ≃ P₂ ⊗ Q` of a patching triple `(P₁, P₂, α)`, as a linear
equivalence of balanced extensions. -/
def PatchingTriples.gluing (T : π₁.PatchingTriples π₂) :
    BalancedExtension (RingHom.op π₁) T.fst.obj ≃ₗ[Qᵐᵒᵖ]
      BalancedExtension (RingHom.op π₂) T.snd.obj :=
  ((finiteProjectiveModules Qᵐᵒᵖ).ι.mapIso T.iso).toLinearEquiv

@[simp]
theorem PatchingTriples.gluing_apply (T : π₁.PatchingTriples π₂)
    (x : BalancedExtension (RingHom.op π₁) T.fst.obj) :
    T.gluing x = T.iso.hom.hom x :=
  (rfl)

/-- The two components of a morphism of patching triples are intertwined by the gluing
isomorphisms. -/
theorem PatchingTriples.gluing_map {T T' : π₁.PatchingTriples π₂} (φ : T ⟶ T')
    (x : BalancedExtension (RingHom.op π₁) T.fst.obj) :
    T'.gluing (map (RingHom.op π₁) φ.fst.hom.hom x) =
      map (RingHom.op π₂) φ.snd.hom.hom (T.gluing x) :=
  congr($(φ.w).hom x)

/-- **Milnor patching**: with a surjective leg, the patched module of a patching triple
`(P₁, P₂, α)` is a finitely generated projective right module over `A₁ ×_Q A₂`. -/
theorem finiteProjectiveModules_patchedModule
    (hπ : Function.Surjective π₁ ∨ Function.Surjective π₂) (T : π₁.PatchingTriples π₂) :
    finiteProjectiveModules (π₁.pullback π₂)ᵐᵒᵖ
      (ModuleCat.of _ (PatchedModule (op_pullback_comm_sq π₁ π₂) T.gluing.toLinearMap)) :=
  finiteProjectiveModules_iff.2
    ⟨finite_patchedModule _ T.gluing
        (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂)
        (hπ.imp op_surjective_iff.2 op_surjective_iff.2),
      projective_patchedModule _ T.gluing
        (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂)
        (hπ.imp op_surjective_iff.2 op_surjective_iff.2)⟩

variable (π₁ π₂) in
/-- The **patched module functor** of a fibre product `D = A₁ ×_Q A₂` with a surjective leg: it
sends a patching triple `(P₁, P₂, α)` to the patched module
`M(P₁, P₂, α) = {(x, y) ∈ P₁ × P₂ | α (x ⊗ 1) = y ⊗ 1}`, a finitely generated projective right
`D`-module by Milnor's theorem (`TauCeti.finite_patchedModule`,
`TauCeti.projective_patchedModule`), and a morphism `(g₁, g₂)` to `(x, y) ↦ (g₁ x, g₂ y)`. It is
the inverse of the patching functor (`RingHom.patchingEquivalence`). -/
-- Exposed so that the underlying module of the image of a triple is definitionally its patched
-- module, as recorded by `RingHom.patchedModuleFunctor_obj_obj`.
@[expose, simps! obj_obj]
def patchedModuleFunctor (hπ : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    π₁.PatchingTriples π₂ ⥤ FiniteProjectiveRight (π₁.pullback π₂) where
  obj T := ⟨ModuleCat.of _ (PatchedModule (op_pullback_comm_sq π₁ π₂) T.gluing.toLinearMap),
    finiteProjectiveModules_patchedModule hπ T⟩
  map φ := ObjectProperty.homMk (ModuleCat.ofHom
    (PatchedModule.map φ.fst.hom.hom φ.snd.hom.hom (PatchingTriples.gluing_map φ)))

@[simp]
theorem patchedModuleFunctor_map_hom_hom (hπ : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {T T' : π₁.PatchingTriples π₂} (φ : T ⟶ T') :
    ((patchedModuleFunctor π₁ π₂ hπ).map φ).hom.hom =
      PatchedModule.map φ.fst.hom.hom φ.snd.hom.hom (PatchingTriples.gluing_map φ) :=
  (rfl)

variable (hπ : Function.Surjective π₁ ∨ Function.Surjective π₂)

/-- The morphism from the patching triple of `M(P₁, P₂, α)` to `T = (P₁, P₂, α)` given by the
comparison maps `M ⊗ A₁ → P₁` and `M ⊗ A₂ → P₂`. -/
private def patchingCounit (T : π₁.PatchingTriples π₂) :
    (patchingFunctor π₁ π₂).obj ((patchedModuleFunctor π₁ π₂ hπ).obj T) ⟶ T where
  fst := ObjectProperty.homMk (ModuleCat.ofHom (PatchedModule.compareFst _ T.gluing.toLinearMap))
  snd := ObjectProperty.homMk (ModuleCat.ofHom (PatchedModule.compareSnd _ T.gluing.toLinearMap))
  w := ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦
    -- The structure isomorphism of the patching triple of `M` is `commSqEquiv`, and the
    -- comparison maps intertwine it with the gluing isomorphism of `T`; the two sides of `w` are
    -- these maps up to the definitional identification of the extended modules with balanced
    -- extensions, as in `commSqEquiv_map_hom_fst`.
    (PatchedModule.map_compareSnd_commSqEquiv _ T.gluing.toLinearMap x).symm.trans
      (congrArg _ (LinearMap.congr_fun
        (finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_eq_commSqEquiv _ _ _ _ _ _)
        x).symm)))

/-- **Milnor patching: every patching triple is patched from a module.** With a surjective leg,
the patching triple of the patched module `M(P₁, P₂, α)` is isomorphic to `T = (P₁, P₂, α)`,
through the comparison maps `M ⊗_D A₁ → P₁` and `M ⊗_D A₂ → P₂`, which are bijective by Milnor's
theorem. This is the counit of the patching equivalence (`RingHom.patchingEquivalence`). -/
def patchingCounitIso (T : π₁.PatchingTriples π₂) :
    (patchingFunctor π₁ π₂).obj ((patchedModuleFunctor π₁ π₂ hπ).obj T) ≅ T :=
  CategoricalPullback.mkIso
    (ObjectProperty.isoMk _ (LinearEquiv.ofBijective _ (PatchedModule.bijective_compareFst _
      T.gluing (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂)
      (hπ.imp op_surjective_iff.2 op_surjective_iff.2))).toModuleIso)
    (ObjectProperty.isoMk _ (LinearEquiv.ofBijective _ (PatchedModule.bijective_compareSnd _
      T.gluing (fun _ _ ↦ existsUnique_op_pullbackFst_eq_and_op_pullbackSnd_eq π₁ π₂)
      (hπ.imp op_surjective_iff.2 op_surjective_iff.2))).toModuleIso)
    (patchingCounit hπ T).w

/-- The first component of `RingHom.patchingCounitIso` is the comparison map `M ⊗_D A₁ → P₁`,
`(x, y) ⊗ a ↦ x a`. -/
@[simp]
theorem patchingCounitIso_hom_fst_hom_hom (T : π₁.PatchingTriples π₂) :
    (patchingCounitIso hπ T).hom.fst.hom.hom = PatchedModule.compareFst _ T.gluing.toLinearMap :=
  (rfl)

/-- The second component of `RingHom.patchingCounitIso` is the comparison map `M ⊗_D A₂ → P₂`,
`(x, y) ⊗ a ↦ y a`. -/
@[simp]
theorem patchingCounitIso_hom_snd_hom_hom (T : π₁.PatchingTriples π₂) :
    (patchingCounitIso hπ T).hom.snd.hom.hom = PatchedModule.compareSnd _ T.gluing.toLinearMap :=
  (rfl)

/-- `RingHom.patchingCounitIso` is natural in morphisms of patching triples. -/
@[reassoc]
theorem patchingCounitIso_hom_naturality {T T' : π₁.PatchingTriples π₂} (φ : T ⟶ T') :
    (patchingFunctor π₁ π₂).map ((patchedModuleFunctor π₁ π₂ hπ).map φ) ≫
        (patchingCounitIso hπ T').hom = (patchingCounitIso hπ T).hom ≫ φ :=
  CategoricalPullback.hom_ext
    (ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦
      PatchedModule.compareFst_map_map _ _ _ _ _ x)))
    (ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦
      PatchedModule.compareSnd_map_map _ _ _ _ _ x)))

variable (π₁ π₂) in
/-- **Milnor's patching theorem**, as an equivalence of categories. Let `D = A₁ ×_Q A₂` be the
fibre product of ring homomorphisms `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q`, one of which is
surjective. The patching functor `P ↦ (P ⊗_D A₁, P ⊗_D A₂, α_P)` from finitely generated projective
right `D`-modules to patching triples is an equivalence, with inverse the patched module functor
`(P₁, P₂, α) ↦ M(P₁, P₂, α) = {(x, y) ∈ P₁ × P₂ | α (x ⊗ 1) = y ⊗ 1}`. Its counit is
`RingHom.patchingCounitIso`, and its unit sends `p` to `(p ⊗ 1, p ⊗ 1)`
(`RingHom.fst_patchingEquivalence_unitIso_hom_app`). -/
-- Exposed so that its functor and inverse are definitionally the patching and patched module
-- functors, which the statements about its unit and counit need to typecheck.
@[expose, simps! functor inverse counitIso_hom_app counitIso_inv_app]
def patchingEquivalence :
    FiniteProjectiveRight (π₁.pullback π₂) ≌ π₁.PatchingTriples π₂ :=
  letI hF := Functor.FullyFaithful.ofFullyFaithful (patchingFunctor π₁ π₂)
  { functor := patchingFunctor π₁ π₂
    inverse := patchedModuleFunctor π₁ π₂ hπ
    unitIso := NatIso.ofComponents
      (fun P ↦ hF.preimageIso (patchingCounitIso hπ ((patchingFunctor π₁ π₂).obj P)).symm)
      fun f ↦ hF.map_injective (by simp [← cancel_mono (patchingCounitIso hπ _).hom,
        patchingCounitIso_hom_naturality])
    counitIso := NatIso.ofComponents (patchingCounitIso hπ) (patchingCounitIso_hom_naturality hπ)
    functor_unitIso_comp P := by simp }

/-- The unit of the patching equivalence sends `p` to `(p ⊗ 1, p ⊗ 1)`: its first component. -/
-- The source and target of the linear map are given as `P` and `e.inverse.obj (e.functor.obj P)`,
-- the simp normal forms of `(𝟭 _).obj P` and `(e.functor ⋙ e.inverse).obj P`.
@[simp]
theorem fst_patchingEquivalence_unitIso_hom_app (P : FiniteProjectiveRight (π₁.pullback π₂))
    (x : P.obj) :
    ((ModuleCat.Hom.hom (A := P.obj)
      (B := ((patchingEquivalence π₁ π₂ hπ).inverse.obj
        ((patchingEquivalence π₁ π₂ hπ).functor.obj P)).obj)
      ((patchingEquivalence π₁ π₂ hπ).unitIso.hom.app P).hom) x).fst =
      tmul (RingHom.op (π₁.pullbackFst π₂)) 1 x := by
  -- The first component of the image of the unit, followed by the counit, is the identity.
  set u := ((patchingEquivalence π₁ π₂ hπ).unitIso.hom.app P).hom.hom
  calc _ = (1 : A₁ᵐᵒᵖ) • (u x).fst := (one_smul _ _).symm
    _ = PatchedModule.compareFst _ _ (tmul _ 1 (u x)) :=
      (PatchedModule.compareFst_tmul _ _ 1 _).symm
    _ = PatchedModule.compareFst _ _ (map _ u (tmul _ 1 x)) := congrArg _ (map_tmul _ _ _).symm
    _ = ((patchingEquivalence π₁ π₂ hπ).counitIso.hom.app _).fst.hom.hom
          (((patchingFunctor π₁ π₂).map
            ((patchingEquivalence π₁ π₂ hπ).unitIso.hom.app P)).fst.hom.hom (tmul _ 1 x)) := by
      rw [patchingFunctor_map_fst_hom_hom, patchingEquivalence_counitIso_hom_app]
      exact (LinearMap.congr_fun (patchingCounitIso_hom_fst_hom_hom hπ _) _).symm
    -- The triangle identity, whose composite has this component by `CategoricalPullback.comp_fst`.
    _ = _ := congr($(((patchingEquivalence π₁ π₂ hπ).functor_unitIso_comp P)).fst.hom.hom
      (tmul (RingHom.op (π₁.pullbackFst π₂)) 1 x))

/-- The unit of the patching equivalence sends `p` to `(p ⊗ 1, p ⊗ 1)`: its second component. -/
-- The source and target of the linear map are given as `P` and `e.inverse.obj (e.functor.obj P)`,
-- the simp normal forms of `(𝟭 _).obj P` and `(e.functor ⋙ e.inverse).obj P`.
@[simp]
theorem snd_patchingEquivalence_unitIso_hom_app (P : FiniteProjectiveRight (π₁.pullback π₂))
    (x : P.obj) :
    ((ModuleCat.Hom.hom (A := P.obj)
      (B := ((patchingEquivalence π₁ π₂ hπ).inverse.obj
        ((patchingEquivalence π₁ π₂ hπ).functor.obj P)).obj)
      ((patchingEquivalence π₁ π₂ hπ).unitIso.hom.app P).hom) x).snd =
      tmul (RingHom.op (π₁.pullbackSnd π₂)) 1 x := by
  -- The second component of the image of the unit, followed by the counit, is the identity.
  set u := ((patchingEquivalence π₁ π₂ hπ).unitIso.hom.app P).hom.hom
  calc _ = (1 : A₂ᵐᵒᵖ) • (u x).snd := (one_smul _ _).symm
    _ = PatchedModule.compareSnd _ _ (tmul _ 1 (u x)) :=
      (PatchedModule.compareSnd_tmul _ _ 1 _).symm
    _ = PatchedModule.compareSnd _ _ (map _ u (tmul _ 1 x)) := congrArg _ (map_tmul _ _ _).symm
    _ = ((patchingEquivalence π₁ π₂ hπ).counitIso.hom.app _).snd.hom.hom
          (((patchingFunctor π₁ π₂).map
            ((patchingEquivalence π₁ π₂ hπ).unitIso.hom.app P)).snd.hom.hom (tmul _ 1 x)) := by
      rw [patchingFunctor_map_snd_hom_hom, patchingEquivalence_counitIso_hom_app]
      exact (LinearMap.congr_fun (patchingCounitIso_hom_snd_hom_hom hπ _) _).symm
    -- The triangle identity, whose composite has this component by `CategoricalPullback.comp_snd`.
    _ = _ := congr($(((patchingEquivalence π₁ π₂ hπ).functor_unitIso_comp P)).snd.hom.hom
      (tmul (RingHom.op (π₁.pullbackSnd π₂)) 1 x))

variable (π₁ π₂) in
include hπ in
/-- **Milnor's patching theorem.** For ring homomorphisms `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q`, one
of which is surjective, the patching functor `P ↦ (P ⊗_D A₁, P ⊗_D A₂, α_P)` from finitely
generated projective right modules over `D = A₁ ×_Q A₂` to patching triples is an equivalence of
categories; its inverse is the patched module functor (`RingHom.patchingEquivalence`). -/
theorem milnor_patching : (patchingFunctor π₁ π₂).IsEquivalence :=
  (patchingEquivalence π₁ π₂ hπ).isEquivalence_functor

end Equivalence

end RingHom
