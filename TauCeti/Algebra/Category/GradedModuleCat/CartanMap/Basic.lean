/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.CategoryTheory.Exact.Projective
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.FullSubcategory

/-!
# The graded Cartan map

Let `A` be a `k`-algebra with homogeneous pieces `𝒜 : ℤ → Submodule k A`. The finitely generated
graded `A`-modules and the finitely generated graded modules whose underlying `A`-modules are
projective are shift-stable full subcategories of `TauCeti.GradedModuleCat 𝒜`. This file equips
them with their induced graded exact structures and constructs the Laurent-linear Cartan map

```text
c_A^gr : K₀^gr(proj A) ⟶ G₀^gr(mod A).
```

Both subcategories are extension closed for any grading data: a short exact sequence with
projective quotient splits on underlying modules. When `𝒜` is a decomposition of `A`, the exact
structure on the graded projectives is moreover split: a conflation with projective quotient
splits in the graded module category. The inclusion into the finite graded modules is compatible
with the grading shift, so its map on Grothendieck groups is linear over `ℤ[q,q⁻¹]`.

The map is constructed for arbitrary grading data, since its construction uses only extension
closure and shift stability. Its source is `K₀^gr(proj A)` in the textbook sense when `𝒜` is a
decomposition of `A`: then finite graded modules with projective underlying module are projective
objects of the graded module category (`TauCeti.GradedModuleCat.projective_of_module_projective`),
and their induced exact structure is the split one
(`TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_split`).

The smallness argument uses an explicit small model. A finite graded module is transported to a
quotient of a finite-rank free `A`-module using Mathlib's `FGModuleRepr`; the grading and its
compatibility with `𝒜` transport across the resulting linear equivalence. Thus both graded
Grothendieck groups live in the same universe as the coefficient data.

## Main definitions

* `TauCeti.gradedFiniteModules` and `TauCeti.gradedFiniteProjectiveModules`: the two object
  properties.
* `TauCeti.gradedFiniteModulesExactStructure` and
  `TauCeti.gradedFiniteProjectiveModulesExactStructure`: their induced graded exact structures.
* `TauCeti.gradedCartanMap`: the Laurent-linear graded Cartan map.

## Main results

* `TauCeti.isExtensionClosed_gradedFiniteModules` and
  `TauCeti.isExtensionClosed_gradedFiniteProjectiveModules`: both properties are extension closed
  in the abelian category of graded modules.
* `TauCeti.gradedFiniteModules_shift` and `TauCeti.gradedFiniteProjectiveModules_shift`: both
  properties are stable under the grading shift.
* `TauCeti.gradedFiniteModulesExactStructure_conflation_iff` and
  `TauCeti.gradedFiniteProjectiveModulesExactStructure_conflation_iff`: the conflations of the two
  structures are the short exact sequences of graded modules with terms in the subcategory.
* `TauCeti.gradedFiniteModulesExactStructureShiftFunctorCompιIso` and
  `TauCeti.gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso`: the restricted shifts
  agree with the ambient grading shift after inclusion.
* `TauCeti.laurentK0_of_shiftObj`: `[M{d}] = qᵈ [M]` in the graded Grothendieck group of finite
  graded modules.
* `TauCeti.laurentK0_projective_of_shiftObj`: `[P{d}] = qᵈ [P]` in the graded Grothendieck group
  of finite graded projectives.
* `TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_split`: the underlying exact structure
  on finite graded projectives is split when `𝒜` is a decomposition of `A`.
* `TauCeti.gradedCartanMap_of`: the graded Cartan map sends the class of a projective to the class
  of the same graded module in the finite-module category.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and grading shifts.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan map over the Laurent coefficient ring.

The construction adapts the ungraded Cartan map of
`TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic` (`TauCeti.cartanMap`) to graded modules and
the Laurent-linear Grothendieck group.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty ZeroObject

universe uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

/-! ### Finite graded modules -/

/-- The object property of having a finitely generated underlying module. -/
def gradedFiniteModules : ObjectProperty (GradedModuleCat.{uA} 𝒜) :=
  fun M => Module.Finite A M

/-- The object property of having a finitely generated projective underlying module. -/
def gradedFiniteProjectiveModules : ObjectProperty (GradedModuleCat.{uA} 𝒜) :=
  fun M => Module.Finite A M ∧ Module.Projective A M

variable {𝒜}

@[simp]
theorem gradedFiniteModules_iff {M : GradedModuleCat.{uA} 𝒜} :
    gradedFiniteModules 𝒜 M ↔ Module.Finite A M :=
  Iff.rfl

@[simp]
theorem gradedFiniteProjectiveModules_iff {M : GradedModuleCat.{uA} 𝒜} :
    gradedFiniteProjectiveModules 𝒜 M ↔ Module.Finite A M ∧ Module.Projective A M :=
  Iff.rfl

/-- A finite graded projective is, in particular, a finite graded module. -/
theorem gradedFiniteProjectiveModules_le_finiteModules :
    gradedFiniteProjectiveModules 𝒜 ≤ gradedFiniteModules 𝒜 :=
  fun _ h => h.1

instance (M : (gradedFiniteModules 𝒜).FullSubcategory) : Module.Finite A M.obj :=
  M.property

/-- Over an algebra finite as a module over its base ring, a finite graded module is finite over
the base ring. -/
instance [Module.Finite k A] (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    Module.Finite k M.obj :=
  Module.Finite.trans A M.obj

instance (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) : Module.Finite A M.obj :=
  M.property.1

instance (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) : Module.Projective A M.obj :=
  M.property.2

instance : (gradedFiniteModules 𝒜).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    let _ : Module.Finite A ↑((GradedModuleCat.toModuleCat (𝒜 := 𝒜)).obj M) := hM
    exact Module.Finite.equiv
      (((GradedModuleCat.toModuleCat (𝒜 := 𝒜)).mapIso e).toLinearEquiv)

instance : (gradedFiniteProjectiveModules 𝒜).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    let _ : Module.Finite A ↑((GradedModuleCat.toModuleCat (𝒜 := 𝒜)).obj M) := hM.1
    let _ : Module.Projective A ↑((GradedModuleCat.toModuleCat (𝒜 := 𝒜)).obj M) := hM.2
    let e' := ((GradedModuleCat.toModuleCat (𝒜 := 𝒜)).mapIso e).toLinearEquiv
    exact ⟨Module.Finite.equiv e', Module.Projective.of_equiv e'⟩

/-- A retract of a finite graded projective is a finite graded projective: its underlying module is
a direct summand of a finitely generated projective module. -/
instance : (gradedFiniteProjectiveModules 𝒜).IsStableUnderRetracts where
  of_retract {M N} h hN := by
    let _ : Module.Finite A N := hN.1
    let _ : Module.Projective A N := hN.2
    have hri : h.r.hom ∘ₗ h.i.hom = LinearMap.id := by
      rw [← GradedModuleCat.hom_comp, h.retract, GradedModuleCat.hom_id]
    exact ⟨Module.Finite.of_surjective h.r.hom fun x ↦ ⟨h.i.hom x, LinearMap.congr_fun hri x⟩,
      Module.Projective.of_split h.i.hom h.r.hom hri⟩

/-! ### A small model -/

namespace GradedFGModuleRepr

/-- The canonical scalar-restricted module structure on a finite-module representative. -/
private noncomputable instance moduleBase (M : FGModuleRepr A) : Module k M :=
  Module.compHom _ (algebraMap k A)

/-- Scalar restriction along `k → A` is compatible with the original `A`-module structure. -/
private instance scalarTower (M : FGModuleRepr A) : IsScalarTower k A M :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

end GradedFGModuleRepr

/-- A small representative of a finitely generated graded module. Its underlying module is one
of Mathlib's quotients of a finite-rank free module. -/
private structure GradedFGModuleRepr where
  /-- The small representative of the underlying finitely generated module. -/
  moduleRepr : FGModuleRepr A
  /-- The internal grading on the representative. -/
  grading : InternalGrading k moduleRepr
  /-- Multiplication by a homogeneous algebra element shifts the degree as prescribed. -/
  [gradedSMul : SetLike.GradedSMul 𝒜 grading.piece]

namespace GradedFGModuleRepr

attribute [instance] gradedSMul

/-- A small graded representative as an object of the graded module category. -/
private abbrev toGradedModuleCat (M : GradedFGModuleRepr (𝒜 := 𝒜)) :
    GradedModuleCat.{uA} 𝒜 where
  carrier := M.moduleRepr
  grading := M.grading

private instance : Category (GradedFGModuleRepr (𝒜 := 𝒜)) :=
  inferInstanceAs (Category (InducedCategory _ toGradedModuleCat))

private instance : SmallCategory (GradedFGModuleRepr (𝒜 := 𝒜)) where

/-- The small representatives embed in the category of finite graded modules. -/
private def embed (𝒜 : ℤ → Submodule k A) :
    GradedFGModuleRepr (𝒜 := 𝒜) ⥤ (gradedFiniteModules 𝒜).FullSubcategory :=
  (gradedFiniteModules 𝒜).lift (inducedFunctor toGradedModuleCat)
    (fun M => (inferInstance : Module.Finite A (toGradedModuleCat M)))

private instance : (embed 𝒜).Faithful :=
  by
    let _ : (inducedFunctor (toGradedModuleCat (𝒜 := 𝒜))).Faithful :=
      (fullyFaithfulInducedFunctor (toGradedModuleCat (𝒜 := 𝒜))).faithful
    exact Functor.Faithful.of_comp_iso
      ((gradedFiniteModules 𝒜).liftCompιIso
        (inducedFunctor (toGradedModuleCat (𝒜 := 𝒜))) _)

private instance : (embed 𝒜).Full :=
  by
    let _ : (inducedFunctor (toGradedModuleCat (𝒜 := 𝒜))).Full :=
      (fullyFaithfulInducedFunctor (toGradedModuleCat (𝒜 := 𝒜))).full
    exact Functor.Full.of_comp_faithful_iso
      ((gradedFiniteModules 𝒜).liftCompιIso
        (inducedFunctor (toGradedModuleCat (𝒜 := 𝒜))) _)

variable (M : GradedModuleCat.{uA} 𝒜) [Module.Finite A M]

private noncomputable def moduleEquiv :
    FGModuleRepr.ofFinite A M ≃ₗ[A] M :=
  FGModuleRepr.ofFiniteEquiv A M

private noncomputable def smallGrading :
    InternalGrading k (FGModuleRepr.ofFinite A M) :=
  M.grading.map ((moduleEquiv M).symm.restrictScalars k)

private noncomputable instance smallGradedSMul :
    SetLike.GradedSMul 𝒜 (smallGrading M).piece where
  smul_mem := fun {i j} a x ha hx => by
    have hx' := (M.grading.mem_map_piece_iff
      ((moduleEquiv M).symm.restrictScalars k) j x).1 hx
    apply (M.grading.mem_map_piece_iff
      ((moduleEquiv M).symm.restrictScalars k) (i + j) (a • x)).2
    simpa using SetLike.GradedSMul.smul_mem (B := M.grading.piece) ha hx'

/-- A chosen small representative of a finite graded module. -/
private noncomputable abbrev ofFinite : GradedFGModuleRepr (𝒜 := 𝒜) where
  moduleRepr := FGModuleRepr.ofFinite A M
  grading := smallGrading M

/-- A finite graded module is isomorphic to its chosen small representative. -/
private noncomputable def ofFiniteIso : toGradedModuleCat (ofFinite M) ≅ M :=
  GradedModuleCat.isoMk (moduleEquiv M) fun p x =>
    M.grading.mem_map_piece_iff ((moduleEquiv M).symm.restrictScalars k) p x

private instance : (embed 𝒜).EssSurj where
  mem_essImage M := ⟨ofFinite M.obj,
    ⟨ObjectProperty.isoMk (P := gradedFiniteModules 𝒜) (ofFiniteIso M.obj)⟩⟩

private instance : (embed 𝒜).IsEquivalence where

end GradedFGModuleRepr

/-- Finite graded modules form an essentially small category. -/
instance : ObjectProperty.EssentiallySmall.{uA} (gradedFiniteModules 𝒜) :=
  (ObjectProperty.exists_equivalence_iff.{uA, uA} _).1
    ⟨_, _, ⟨(GradedFGModuleRepr.embed 𝒜).asEquivalence.symm⟩⟩

/-- Finite graded projective modules form an essentially small category. -/
instance : ObjectProperty.EssentiallySmall.{uA}
    (gradedFiniteProjectiveModules 𝒜) :=
  ObjectProperty.EssentiallySmall.of_le gradedFiniteProjectiveModules_le_finiteModules

/-! ### Induced graded exact structures -/

private abbrev finiteZero : GradedModuleCat.{uA} 𝒜 where
  carrier := PUnit
  grading :=
    { piece := fun _ => ⊥
      isInternal :=
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩ }
  gradedSMul := ⟨fun _ _ => by simp⟩

private theorem isZero_finiteZero : IsZero (finiteZero (𝒜 := 𝒜)) :=
  (IsZero.iff_id_eq_zero _).2 (by
    apply GradedModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim (α := PUnit) _ _)

private theorem finite_finiteZero : Module.Finite A (finiteZero (𝒜 := 𝒜)) :=
  inferInstance

private theorem projective_finiteZero : Module.Projective A (finiteZero (𝒜 := 𝒜)) :=
  inferInstance

instance : (gradedFiniteModules 𝒜).ContainsZero where
  exists_zero := ⟨finiteZero, isZero_finiteZero, finite_finiteZero⟩

instance : (gradedFiniteProjectiveModules 𝒜).ContainsZero where
  exists_zero := ⟨finiteZero, isZero_finiteZero,
    ⟨finite_finiteZero, projective_finiteZero⟩⟩

/-- Finite graded modules are extension closed in the abelian category of graded modules. -/
theorem isExtensionClosed_gradedFiniteModules :
    (ExactStructure.abelian (GradedModuleCat.{uA} 𝒜)).IsExtensionClosed
      (gradedFiniteModules 𝒜) where
  prop_X₂ {S} hS h₁ h₃ := by
    rw [ExactStructure.abelian_conflation] at hS
    have hS' : (S.map (GradedModuleCat.toModuleCat (𝒜 := 𝒜))).Exact :=
      hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
    let _ : Module.Finite A S.X₁ := h₁
    let _ : Module.Finite A S.X₃ := h₃
    exact Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS')
      ((GradedModuleCat.epi_iff_surjective S.g).1
        hS.epi_g)

/-- Finite graded modules with projective underlying module are extension closed in the abelian
category of graded modules: a short exact sequence with projective quotient splits on the
underlying modules. -/
theorem isExtensionClosed_gradedFiniteProjectiveModules :
    (ExactStructure.abelian (GradedModuleCat.{uA} 𝒜)).IsExtensionClosed
      (gradedFiniteProjectiveModules 𝒜) where
  prop_X₂ {S} hS h₁ h₃ := by
    refine ⟨isExtensionClosed_gradedFiniteModules.prop_X₂ hS h₁.1 h₃.1, ?_⟩
    rw [ExactStructure.abelian_conflation] at hS
    have hS' : (S.map (GradedModuleCat.toModuleCat (𝒜 := 𝒜))).Exact :=
      hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'
    have hf : Function.Injective S.f.hom := (GradedModuleCat.mono_iff_injective S.f).1 hS.mono_f
    let _ : Module.Projective A S.X₁ := h₁.2
    let _ : Module.Projective A S.X₃ := h₃.2
    obtain ⟨l, hl⟩ := Module.projective_lifting_property S.g.hom LinearMap.id
      ((GradedModuleCat.epi_iff_surjective S.g).1 hS.epi_g)
    exact Module.Projective.of_equiv (hex.splitSurjectiveEquiv hf ⟨l, hl⟩).1.symm

instance : (gradedFiniteModules 𝒜).IsClosedUnderBinaryProducts :=
  (isExtensionClosed_gradedFiniteModules (𝒜 := 𝒜)).isClosedUnderBinaryProducts

instance : (gradedFiniteProjectiveModules 𝒜).IsClosedUnderBinaryProducts :=
  (isExtensionClosed_gradedFiniteProjectiveModules (𝒜 := 𝒜)).isClosedUnderBinaryProducts

private noncomputable abbrev gradedModuleExactStructure (𝒜 : ℤ → Submodule k A) :
    GradedExactStructure (GradedModuleCat.{uA} 𝒜) :=
  GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)

/-- Finite graded modules are extension closed for the graded abelian exact structure of the
grading shift. -/
theorem isExtensionClosed_gradedFiniteModules_gradedAbelian :
    (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).toExactStructure.IsExtensionClosed
      (gradedFiniteModules 𝒜) := by
  rw [GradedExactStructure.abelian_toExactStructure]
  exact isExtensionClosed_gradedFiniteModules

/-- Finite graded modules with projective underlying module are extension closed for the graded
abelian exact structure of the grading shift. -/
theorem isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian :
    (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).toExactStructure.IsExtensionClosed
      (gradedFiniteProjectiveModules 𝒜) := by
  rw [GradedExactStructure.abelian_toExactStructure]
  exact isExtensionClosed_gradedFiniteProjectiveModules

/-- Finite graded modules are stable under the grading shift. -/
theorem gradedFiniteModules_shift :
    (gradedFiniteModules 𝒜).inverseImage (GradedModuleCat.shift 𝒜).functor =
      gradedFiniteModules 𝒜 := by
  ext M
  rfl

/-- Finite graded modules with projective underlying module are stable under the grading
shift. -/
theorem gradedFiniteProjectiveModules_shift :
    (gradedFiniteProjectiveModules 𝒜).inverseImage (GradedModuleCat.shift 𝒜).functor =
      gradedFiniteProjectiveModules 𝒜 := by
  ext M
  rfl

/-- Finite graded modules are stable under the shift of the graded abelian exact structure. -/
theorem gradedFiniteModules_gradedAbelian_shift :
    (gradedFiniteModules 𝒜).inverseImage
        (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).shift.functor =
      gradedFiniteModules 𝒜 := by
  rw [GradedExactStructure.abelian_shift]
  exact gradedFiniteModules_shift

/-- Finite graded modules with projective underlying module are stable under the shift of the
graded abelian exact structure. -/
theorem gradedFiniteProjectiveModules_gradedAbelian_shift :
    (gradedFiniteProjectiveModules 𝒜).inverseImage
        (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).shift.functor =
      gradedFiniteProjectiveModules 𝒜 := by
  rw [GradedExactStructure.abelian_shift]
  exact gradedFiniteProjectiveModules_shift

/-- The induced graded exact structure on finite graded modules: the full-subcategory exact
structure of the graded abelian exact structure for the grading shift. Its Laurent Grothendieck
group is the graded Grothendieck group `G₀^gr(mod A)` of finite graded modules. -/
@[expose] noncomputable def gradedFiniteModulesExactStructure (𝒜 : ℤ → Submodule k A) :
    GradedExactStructure (gradedFiniteModules 𝒜).FullSubcategory :=
  (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).fullSubcategory _
    isExtensionClosed_gradedFiniteModules_gradedAbelian
      gradedFiniteModules_gradedAbelian_shift

/-- The induced graded exact structure on finite graded modules with projective underlying
module. When `𝒜` is a decomposition of `A`, it is the split exact structure, by
`TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_split`. -/
@[expose] noncomputable def gradedFiniteProjectiveModulesExactStructure (𝒜 : ℤ → Submodule k A) :
    GradedExactStructure (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).fullSubcategory _
    isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
      gradedFiniteProjectiveModules_gradedAbelian_shift

/-- The graded exact structure on finite graded modules is the one induced from the canonical
graded exact structure on all graded modules, for any proofs of the side conditions. -/
theorem gradedFiniteModulesExactStructure_eq_fullSubcategory
    (hP : (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).toExactStructure
      |>.IsExtensionClosed (gradedFiniteModules 𝒜))
    (hshift : (gradedFiniteModules 𝒜).inverseImage
        (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).shift.functor =
      gradedFiniteModules 𝒜) :
    gradedFiniteModulesExactStructure 𝒜 =
      (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).fullSubcategory _ hP hshift := by
  rw [gradedFiniteModulesExactStructure]

/-- The graded exact structure on finite graded modules with projective underlying module is the
one induced from the canonical graded exact structure on all graded modules, for any proofs of
the side conditions. -/
theorem gradedFiniteProjectiveModulesExactStructure_eq_fullSubcategory
    (hP : (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).toExactStructure
      |>.IsExtensionClosed (gradedFiniteProjectiveModules 𝒜))
    (hshift : (gradedFiniteProjectiveModules 𝒜).inverseImage
        (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).shift.functor =
      gradedFiniteProjectiveModules 𝒜) :
    gradedFiniteProjectiveModulesExactStructure 𝒜 =
      (GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)).fullSubcategory _ hP hshift := by
  rw [gradedFiniteProjectiveModulesExactStructure]

/-- The shift on finite graded modules agrees with the ambient grading shift after applying the
full-subcategory inclusion. -/
noncomputable def gradedFiniteModulesExactStructureShiftFunctorCompιIso :
  (gradedFiniteModulesExactStructure 𝒜).shift.functor ⋙ (gradedFiniteModules 𝒜).ι ≅
      (gradedFiniteModules 𝒜).ι ⋙ (GradedModuleCat.shift 𝒜).functor := by
  rw [gradedFiniteModulesExactStructure, GradedExactStructure.fullSubcategory_shift]
  let e := (gradedModuleExactStructure 𝒜).fullSubcategoryShiftFunctorCompιIso
    (gradedFiniteModules 𝒜) gradedFiniteModules_gradedAbelian_shift
  rw [GradedExactStructure.abelian_shift] at e
  exact e

/-- The shift on finite graded projective modules agrees with the ambient grading shift after
applying the full-subcategory inclusion. -/
noncomputable def gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).shift.functor ⋙
        (gradedFiniteProjectiveModules 𝒜).ι ≅
      (gradedFiniteProjectiveModules 𝒜).ι ⋙ (GradedModuleCat.shift 𝒜).functor := by
  rw [gradedFiniteProjectiveModulesExactStructure, GradedExactStructure.fullSubcategory_shift]
  let e := (gradedModuleExactStructure 𝒜).fullSubcategoryShiftFunctorCompιIso
    (gradedFiniteProjectiveModules 𝒜) gradedFiniteProjectiveModules_gradedAbelian_shift
  rw [GradedExactStructure.abelian_shift] at e
  exact e

/-- The conflations of finite graded modules are the short exact sequences of graded modules
whose three terms are finitely generated. -/
@[simp]
theorem gradedFiniteModulesExactStructure_conflation_iff
    (S : ShortComplex (gradedFiniteModules 𝒜).FullSubcategory) :
    (gradedFiniteModulesExactStructure 𝒜).Conflation S ↔
      (S.map (gradedFiniteModules 𝒜).ι).ShortExact := by
  rw [gradedFiniteModulesExactStructure, GradedExactStructure.fullSubcategory_conflation_iff,
    GradedExactStructure.abelian_toExactStructure, ExactStructure.abelian_conflation]

/-- The conflations of finite graded modules with projective underlying module are the short
exact sequences of graded modules whose three terms are of this kind. -/
@[simp]
theorem gradedFiniteProjectiveModulesExactStructure_conflation_iff
    (S : ShortComplex (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).Conflation S ↔
      (S.map (gradedFiniteProjectiveModules 𝒜).ι).ShortExact := by
  rw [gradedFiniteProjectiveModulesExactStructure,
    GradedExactStructure.fullSubcategory_conflation_iff,
    GradedExactStructure.abelian_toExactStructure, ExactStructure.abelian_conflation]

/-! ### Classes of shifted modules -/

/-- An internal shift of a finite graded module is finite: it has the same underlying module. -/
theorem gradedFiniteModules_shiftObj {M : GradedModuleCat.{uA} 𝒜} (hM : gradedFiniteModules 𝒜 M)
    (d : ℤ) : gradedFiniteModules 𝒜 (M.shiftObj d) :=
  gradedFiniteModules_iff.2 (gradedFiniteModules_iff.1 hM)

/-- In a full subcategory stable under internal shifts, whose exact-structure shift agrees with
the ambient grading shift, the class of the explicit `d`-shift is `T d` times the original class. -/
private theorem laurentK0_of_shiftObj_aux {P : ObjectProperty (GradedModuleCat.{uA} 𝒜)}
    [HasZeroObject P.FullSubcategory] [HasBinaryBiproducts P.FullSubcategory]
    [ObjectProperty.EssentiallySmall.{uA} P]
    (E : GradedExactStructure P.FullSubcategory)
    (hP : ∀ {M}, P M → ∀ d : ℤ, P (M.shiftObj d))
    (hshift : E.shift.functor ⋙ P.ι ≅ P.ι ⋙ (GradedModuleCat.shift 𝒜).functor)
    (M : P.FullSubcategory) (d : ℤ) :
    LaurentK0.of.{uA} E ⟨M.obj.shiftObj d, hP M.property d⟩ =
      (LaurentPolynomial.T d : LaurentPolynomial ℤ) • LaurentK0.of.{uA} E M := by
  -- One application of the shift of the full subcategory is the explicit shift by one.
  have step : ∀ X : P.FullSubcategory,
      (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) •
          LaurentK0.of.{uA} E X =
        LaurentK0.of.{uA} E
          ⟨X.obj.shiftObj 1, hP X.property 1⟩ := fun X => by
    rw [LaurentK0.T_one_smul_of]
    exact LaurentK0.of_congr _
      (ObjectProperty.isoMk _ (hshift.app X))
  -- Shifting by `d` and then by one is shifting by `d + 1`.
  have hadd : ∀ d : ℤ,
      LaurentK0.of.{uA} E
          ⟨M.obj.shiftObj (d + 1), hP M.property _⟩ =
        (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) •
          LaurentK0.of.{uA} E
            ⟨M.obj.shiftObj d, hP M.property d⟩ := fun d => by
    rw [step]
    exact LaurentK0.of_congr _
      (ObjectProperty.isoMk _ ((GradedModuleCat.shiftFunctorAddIso 𝒜 d 1).app M.obj).symm)
  induction d using Int.induction_on with
  | zero =>
    rw [LaurentPolynomial.T_zero, one_smul]
    exact LaurentK0.of_congr _
      (ObjectProperty.isoMk _ ((GradedModuleCat.shiftFunctorZeroIso 𝒜).app M.obj))
  | succ d ih => rw [hadd, ih, smul_smul, ← LaurentPolynomial.T_add, add_comm]
  | pred d ih =>
    have h := hadd (-(d : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    calc _ = (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) •
          (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) •
            LaurentK0.of.{uA} E
              ⟨M.obj.shiftObj (-(d : ℤ) - 1), hP M.property _⟩ := by
          rw [smul_smul, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
            one_smul]
      _ = _ := by rw [← h, smul_smul, ← LaurentPolynomial.T_add, neg_add_eq_sub]

/-- **`[M{d}] = qᵈ [M]`** in the graded Grothendieck group of finite graded modules, for the
explicit internal shift `M{d}` with `(M{d})ₚ = M_{p-d}`. -/
theorem laurentK0_of_shiftObj (M : (gradedFiniteModules 𝒜).FullSubcategory) (d : ℤ) :
    LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨M.obj.shiftObj d, gradedFiniteModules_shiftObj M.property d⟩ =
      (LaurentPolynomial.T d : LaurentPolynomial ℤ) •
        LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) M :=
  laurentK0_of_shiftObj_aux (P := gradedFiniteModules 𝒜)
    (gradedFiniteModulesExactStructure 𝒜) (fun hM d => gradedFiniteModules_shiftObj hM d)
    gradedFiniteModulesExactStructureShiftFunctorCompιIso M d

/-- An internal shift of a finite graded projective has the same underlying finite projective
module. -/
theorem gradedFiniteProjectiveModules_shiftObj {M : GradedModuleCat.{uA} 𝒜}
    (hM : gradedFiniteProjectiveModules 𝒜 M) (d : ℤ) :
    gradedFiniteProjectiveModules 𝒜 (M.shiftObj d) :=
  gradedFiniteProjectiveModules_iff.2 (gradedFiniteProjectiveModules_iff.1 hM)

/-- **`[P{d}] = qᵈ [P]`** in the Laurent Grothendieck group of finite graded projectives, for the
explicit internal shift with `(P{d})ₚ = P_{p-d}`. -/
theorem laurentK0_projective_of_shiftObj
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (d : ℤ) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        ⟨P.obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj P.property d⟩ =
      (LaurentPolynomial.T d : LaurentPolynomial ℤ) •
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) P :=
  laurentK0_of_shiftObj_aux (P := gradedFiniteProjectiveModules 𝒜)
    (gradedFiniteProjectiveModulesExactStructure 𝒜)
    (fun hM d => gradedFiniteProjectiveModules_shiftObj hM d)
    gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso P d

/-! ### The graded Cartan map -/

/-- **The graded Cartan map** `c_A^gr : K₀^gr(proj A) ⟶ G₀^gr(mod A)`, induced by inclusion of
finite graded modules with projective underlying module into all finite graded modules.

It is defined for arbitrary grading data. Its source is the Grothendieck group of the induced
exact structure on finite graded modules with projective underlying module; when `𝒜` is a
decomposition of `A`, these are the finite graded projectives and that structure is split
(`TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_split`), so the source is
`K₀^gr(proj A)`. -/
noncomputable def gradedCartanMap (𝒜 : ℤ → Submodule k A) :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) :=
  by
    let h : GradedConflationExact
        (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (gradedFiniteModulesExactStructure 𝒜)
        (ObjectProperty.ιOfLE gradedFiniteProjectiveModules_le_finiteModules) := by
      rw [gradedFiniteProjectiveModulesExactStructure,
        gradedFiniteModulesExactStructure]
      exact GradedConflationExact.ιOfLE (gradedModuleExactStructure 𝒜)
        (gradedFiniteProjectiveModules 𝒜)
        isExtensionClosed_gradedFiniteProjectiveModules_gradedAbelian
        isExtensionClosed_gradedFiniteModules_gradedAbelian
        gradedFiniteProjectiveModules_gradedAbelian_shift
        gradedFiniteModules_gradedAbelian_shift
        gradedFiniteProjectiveModules_le_finiteModules
    exact LaurentK0.map.{uA, uA} h

/-- The graded Cartan map sends the class of a finite graded projective to the class of the same
graded module in the finite-module category. -/
@[simp]
theorem gradedCartanMap_of {M : GradedModuleCat.{uA} 𝒜}
    (hM : gradedFiniteProjectiveModules 𝒜 M) :
    gradedCartanMap 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) ⟨M, hM⟩) =
      LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨M, gradedFiniteProjectiveModules_le_finiteModules M hM⟩ := by
  rw [gradedCartanMap, LaurentK0.map_of]
  congr 1

/-! ### Splitting over a decomposition -/

variable [DirectSum.Decomposition 𝒜]

/-- A finite graded module with projective underlying module is relatively projective for the
canonical exact structure on graded modules. -/
theorem gradedFiniteProjectiveModules_le_isProjective :
    gradedFiniteProjectiveModules 𝒜 ≤
      (ExactStructure.abelian (GradedModuleCat.{uA} 𝒜)).isProjective := by
  intro M hM
  let _ : Module.Projective A M := hM.2
  exact (ExactStructure.abelian_isProjective_iff M).2 inferInstance

private theorem gradedFiniteProjectiveModules_le_isProjective' :
    gradedFiniteProjectiveModules 𝒜 ≤
      (gradedModuleExactStructure 𝒜).toExactStructure.isProjective := by
  rw [gradedModuleExactStructure, GradedExactStructure.abelian_toExactStructure]
  exact gradedFiniteProjectiveModules_le_isProjective

/-- The underlying exact structure on finite graded projectives is the split exact structure. -/
theorem gradedFiniteProjectiveModulesExactStructure_eq_split :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure =
      ExactStructure.split (gradedFiniteProjectiveModules 𝒜).FullSubcategory := by
  rw [gradedFiniteProjectiveModulesExactStructure,
    GradedExactStructure.fullSubcategory_toExactStructure]
  exact ExactStructure.fullSubcategory_eq_split
    (gradedFiniteProjectiveModules_le_isProjective' (𝒜 := 𝒜))

end TauCeti
