/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Basic

/-!
# Inner comparisons and their central ambiguity

The comparison between derivation self-extensions indexed by an element `b` of the algebra
remembers more than the inner derivation `ad b`. Replacing `b` by `b + c` for a central `c`
composes it with the automorphism `(u, v) ↦ (u + c • v, v)`. These automorphisms form an action
of the additive center. On a module with strict central character `χ`, they are precisely
`1 + εχ(c)`, where `ε(u, v) = (v, 0)`. In particular they cannot generally be discarded when
comparing representatives of outer derivations.

This file also lifts the inner comparisons to isomorphisms of the actual short complexes in
the category of discrete modules, with identity, composition and inverse laws. No topology on
the center or continuity of the map `c ↦ ad c` is required for these comparisons: continuity
is required only of the derivations indexing the discrete self-extensions.

The constructions use `DerivationExtension.innerEquiv`, `innerEquiv_trans` and
`functorInnerIso` from `DerivationExtension.Basic`.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups* (2007), for inner derivations
  and infinitesimal comparisons of local representation categories.
-/

public section

namespace TauCeti.DerivationExtension

open CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {δ δ' δ'' : derivationLieAlgebra R A} {b b' : A}

section Comparisons

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- Two inner comparisons agree exactly when their indexing elements act identically on the
original module. Equality of the inner derivations alone does not suffice. -/
theorem innerEquiv_eq_iff (h : δ' = δ + innerDerivation R b)
    (h' : δ' = δ + innerDerivation R b') :
    innerEquiv M h = innerEquiv M h' ↔ ∀ v : M, b • v = b' • v := by
  constructor
  · intro he v
    have := congrArg (fun e => (e (⟨0, v⟩ : DerivationExtension δ M)).fst) he
    simpa using this
  · intro he
    ext x <;> simp [he]

/-- For a faithful module, the comparison remembers its actual indexing element. -/
theorem innerEquiv_eq_iff_of_faithfulSMul [FaithfulSMul A M]
    (h : δ' = δ + innerDerivation R b) (h' : δ' = δ + innerDerivation R b') :
    innerEquiv M h = innerEquiv M h' ↔ b = b' := by
  rw [innerEquiv_eq_iff M h h']
  exact ⟨fun he => eq_of_smul_eq_smul he, fun he v => he ▸ rfl⟩

/-- The square-zero endomorphism `ε(u, v) = (v, 0)` of a derivation self-extension. -/
def epsilon (δ : derivationLieAlgebra R A) : Module.End A (DerivationExtension δ M) :=
  inlHom δ M ∘ₗ sndHom δ M

@[simp]
theorem epsilon_apply (x : DerivationExtension δ M) : epsilon M δ x = ⟨x.snd, 0⟩ := by
  ext <;> simp [epsilon]

/-- The endomorphism denoted by `ε` has square zero. -/
@[simp]
theorem epsilon_mul_self : epsilon M δ * epsilon M δ = 0 := by
  ext x <;> simp

/-- The additive center acts on a self-extension by the automorphisms
`(u, v) ↦ (u + c • v, v)`. The action retains central changes of inner representatives. -/
def centralInnerHom (δ : derivationLieAlgebra R A) :
    Multiplicative (Subalgebra.center R A) →* (DerivationExtension δ M ≃ₗ[A]
      DerivationExtension δ M) where
  toFun c := innerEquiv M (b := (c.toAdd : A)) (by
    simp [innerDerivation_eq_zero_of_mem_center R c.toAdd.property])
  map_one' := by
    apply innerEquiv_zero
  map_mul' c d := by
    ext x <;> simp [add_smul, add_comm, add_left_comm]

@[simp]
theorem fst_centralInnerHom (c : Multiplicative (Subalgebra.center R A))
    (x : DerivationExtension δ M) :
    (centralInnerHom M δ c x).fst = x.fst + (c.toAdd : A) • x.snd := by
  simp [centralInnerHom]

@[simp]
theorem snd_centralInnerHom (c : Multiplicative (Subalgebra.center R A))
    (x : DerivationExtension δ M) : (centralInnerHom M δ c x).snd = x.snd := by
  simp [centralInnerHom]

/-- As an endomorphism, the central comparison is `1 + cε`. The scalar acts on the
self-extension through its given `A`-module structure. -/
theorem centralInnerHom_toLinearMap (c : Multiplicative (Subalgebra.center R A)) :
    (centralInnerHom M δ c).toLinearMap =
      1 + Module.End.smulLeft (c.toAdd : A) c.toAdd.property ∘ₗ epsilon M δ := by
  ext x <;> simp [Module.End.smulLeft]

/-- Adding a central element to an inner representative composes its comparison with the
corresponding central automorphism on the target self-extension. -/
theorem innerEquiv_trans_centralInnerHom (h : δ' = δ + innerDerivation R b)
    (c : Multiplicative (Subalgebra.center R A))
    (h' : δ' = δ + innerDerivation R (b + (c.toAdd : A))) :
    (innerEquiv M h).trans (centralInnerHom M δ' c) = innerEquiv M h' := by
  ext x <;> simp [add_smul, add_assoc]

/-- Central comparisons commute with every inner comparison. -/
theorem centralInnerHom_trans_innerEquiv (h : δ' = δ + innerDerivation R b)
    (c : Multiplicative (Subalgebra.center R A)) :
    (centralInnerHom M δ c).trans (innerEquiv M h) =
      (innerEquiv M h).trans (centralInnerHom M δ' c) := by
  ext x <;> simp [add_right_comm]

/-- Central comparisons are natural in the module. -/
theorem map_comp_centralInnerHom {N : Type*} [AddCommGroup N] [Module A N]
    (c : Multiplicative (Subalgebra.center R A)) (f : M →ₗ[A] N) :
    map (δ := δ) f ∘ₗ (centralInnerHom M δ c).toLinearMap =
      (centralInnerHom N δ c).toLinearMap ∘ₗ map f := by
  exact map_comp_innerEquiv M (b := (c.toAdd : A))
    (by simp [innerDerivation_eq_zero_of_mem_center R c.toAdd.property]) f

variable [Module R M] (χ : Subalgebra.center R A →ₐ[R] R)
  (hχ : ∀ (z : Subalgebra.center R A) (v : M), (z : A) • v = χ z • v)

include hχ

/-- On a strict-character module the central comparison is `1 + εχ(c)`. This does not
require the self-extension itself to have the original strict character. -/
theorem centralInnerHom_apply (c : Multiplicative (Subalgebra.center R A))
    (x : DerivationExtension δ M) :
    centralInnerHom M δ c x = ⟨x.fst + χ c.toAdd • x.snd, x.snd⟩ := by
  ext <;> simp [hχ]

/-- The central comparison is the identity exactly when its character value annihilates the
module; this formulation also includes the zero module. -/
theorem centralInnerHom_eq_one_iff (c : Multiplicative (Subalgebra.center R A)) :
    centralInnerHom M δ c = 1 ↔ ∀ v : M, χ c.toAdd • v = 0 := by
  constructor
  · intro he v
    have := congrArg (fun e => (e (⟨0, v⟩ : DerivationExtension δ M)).fst) he
    simpa [centralInnerHom_apply M χ hχ] using this
  · intro he
    ext x <;> simp [centralInnerHom_apply M χ hχ, he]

/-- With faithful scalar action, a central comparison is the identity precisely when its
central-character value is zero. Thus nonzero values give actual comparison automorphisms. -/
theorem centralInnerHom_eq_one_iff_of_faithfulSMul [FaithfulSMul R M]
    (c : Multiplicative (Subalgebra.center R A)) :
    centralInnerHom M δ c = 1 ↔ χ c.toAdd = 0 := by
  rw [centralInnerHom_eq_one_iff M χ hχ]
  exact ⟨fun he => eq_of_smul_eq_smul (α := M) fun v => by simpa using he v,
    fun he v => by simp [he]⟩

end Comparisons

section Discrete

variable [TopologicalSpace A]
  (hδ : Continuous (δ : Module.End R A)) (hδ' : Continuous (δ' : Module.End R A))
  (h : δ' = δ + innerDerivation R b) (M : (discreteModules.{v} A).FullSubcategory)

/-- An actual inner change gives an isomorphism of short complexes in the category of
discrete modules, fixing both endpoints. Its middle map is the specified inner comparison. -/
def discreteInnerIso : discreteShortComplex hδ M ≅ discreteShortComplex hδ' M :=
  ShortComplex.isoMk (Iso.refl _)
    (ObjectProperty.isoMk (discreteModules A) (innerEquiv M.obj h).toModuleIso) (Iso.refl _)
    (by
      apply InducedCategory.hom_ext
      simpa using ModuleCat.hom_ext (innerEquiv_comp_inlHom M.obj h).symm)
    (by
      apply InducedCategory.hom_ext
      simpa using ModuleCat.hom_ext (sndHom_comp_innerEquiv M.obj h))

@[simp]
theorem discreteInnerIso_hom_τ₁ : (discreteInnerIso hδ hδ' h M).hom.τ₁ = 𝟙 M := by
  rfl

@[simp]
theorem discreteInnerIso_hom_τ₂ : (discreteInnerIso hδ hδ' h M).hom.τ₂ =
    ObjectProperty.homMk (ModuleCat.ofHom (innerEquiv M.obj h).toLinearMap) := by
  rfl

@[simp]
theorem discreteInnerIso_hom_τ₃ : (discreteInnerIso hδ hδ' h M).hom.τ₃ = 𝟙 M := by
  rfl

@[simp]
theorem discreteInnerIso_inv_τ₁ : (discreteInnerIso hδ hδ' h M).inv.τ₁ = 𝟙 M := by
  rfl

@[simp]
theorem discreteInnerIso_inv_τ₂ : (discreteInnerIso hδ hδ' h M).inv.τ₂ =
    ObjectProperty.homMk (ModuleCat.ofHom (innerEquiv M.obj h).symm.toLinearMap) := by
  rfl

@[simp]
theorem discreteInnerIso_inv_τ₃ : (discreteInnerIso hδ hδ' h M).inv.τ₃ = 𝟙 M := by
  rfl

/-- The inclusion into all modules recovers the specified natural inner comparison, including
both endpoint maps. -/
@[simp]
theorem mapShortComplex_discreteInnerIso :
    (discreteModules A).ι.mapShortComplex.mapIso (discreteInnerIso hδ hδ' h M) =
      (functorInnerIso h).app M.obj := by
  -- The inclusion forgets the homMk wrappers. Its endpoint maps are identities, and its
  -- middle map is the same innerEquiv.toLinearMap as in functorInnerIso. The final rfl
  -- identifies these maps after reducing the short-complex object projections and wrappers.
  ext : 2 <;> simp <;> rfl

/-- The discrete inner comparison for zero is the identity of the whole short complex. -/
@[simp]
theorem discreteInnerIso_zero (h : δ = δ + innerDerivation R (0 : A)) :
    discreteInnerIso hδ hδ h M = Iso.refl _ := by
  ext : 2
  · simp [discreteShortComplex]
  · rw [discreteInnerIso_hom_τ₂, innerEquiv_zero, Iso.refl_hom, ShortComplex.id_τ₂]
    -- Normalize the middle object so the underlying ModuleCat identity lemma applies.
    dsimp only [discreteShortComplex]
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    simp only [LinearEquiv.refl_toLinearMap, ObjectProperty.FullSubcategory.id_hom,
      ModuleCat.hom_id]
    exact ConcreteCategory.hom_ofHom (C := ModuleCat A) _
  · simp [discreteShortComplex]

/-- Successive inner changes compose by adding their actual indexing elements. -/
theorem discreteInnerIso_trans (hδ'' : Continuous (δ'' : Module.End R A))
    (h' : δ'' = δ' + innerDerivation R b') :
    discreteInnerIso hδ hδ' h M ≪≫ discreteInnerIso hδ' hδ'' h' M =
      discreteInnerIso hδ hδ'' (b := b + b') (by rw [h', h, map_add, add_assoc]) M := by
  ext : 2
  · simp only [Iso.trans_hom, ShortComplex.comp_τ₁, discreteInnerIso_hom_τ₁]
    exact Category.id_comp _
  · apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    exact congrArg LinearEquiv.toLinearMap (innerEquiv_trans M.obj h h')
  · simp only [Iso.trans_hom, ShortComplex.comp_τ₃, discreteInnerIso_hom_τ₃]
    exact Category.id_comp _

/-- The inverse discrete comparison is indexed by the negative element. -/
theorem discreteInnerIso_symm :
    (discreteInnerIso hδ hδ' h M).symm =
      discreteInnerIso hδ' hδ (b := -b) (by rw [h, map_neg, add_neg_cancel_right]) M := by
  ext : 2
  · rw [Iso.symm_hom, discreteInnerIso_inv_τ₁, discreteInnerIso_hom_τ₁]
  · apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    exact congrArg LinearEquiv.toLinearMap (innerEquiv_symm M.obj h)
  · rw [Iso.symm_hom, discreteInnerIso_inv_τ₃, discreteInnerIso_hom_τ₃]

end Discrete

end TauCeti.DerivationExtension
