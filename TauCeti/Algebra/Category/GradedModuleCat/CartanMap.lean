/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.FullSubcategory

/-!
# The graded Cartan map

Let `A` be a `k`-algebra with a decomposition `𝒜` into homogeneous pieces. The finitely generated
graded `A`-modules and the finitely generated graded modules whose underlying `A`-modules are
projective are shift-stable full subcategories of `TauCeti.GradedModuleCat 𝒜`. This file equips
them with their induced graded exact structures and constructs the Laurent-linear Cartan map

```text
c_A^gr : K₀^gr(proj A) ⟶ G₀^gr(mod A).
```

The exact structure on the graded projectives is split: a conflation with projective quotient
splits in the graded module category. The inclusion into the finite graded modules is compatible
with the grading shift, so its map on Grothendieck groups is linear over `ℤ[q,q⁻¹]`.

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

* `TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_split`: the underlying exact structure
  on finite graded projectives is split.
* `TauCeti.gradedCartanMap_of`: the graded Cartan map sends the class of a projective to the class
  of the same graded module in the finite-module category.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and grading shifts.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", Section 2.2, for the graded
  Cartan map over the Laurent coefficient ring.
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
  GradedModuleCat.isoMk (moduleEquiv M) fun p x => by
    change x ∈ (smallGrading M).piece p ↔ moduleEquiv M x ∈ M.grading.piece p
    exact M.grading.mem_map_piece_iff ((moduleEquiv M).symm.restrictScalars k) p x

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
    change x = (0 : PUnit)
    exact Subsingleton.elim _ _)

instance : (gradedFiniteModules 𝒜).ContainsZero where
  exists_zero := ⟨finiteZero, isZero_finiteZero,
    show Module.Finite A PUnit from inferInstance⟩

instance : (gradedFiniteProjectiveModules 𝒜).ContainsZero where
  exists_zero := ⟨finiteZero, isZero_finiteZero,
    ⟨show Module.Finite A PUnit from inferInstance,
      show Module.Projective A PUnit from inferInstance⟩⟩

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

variable [DirectSum.Decomposition 𝒜]

/-- A finite graded module with projective underlying module is relatively projective for the
canonical exact structure on graded modules. -/
theorem gradedFiniteProjectiveModules_le_isProjective :
    gradedFiniteProjectiveModules 𝒜 ≤
      (ExactStructure.abelian (GradedModuleCat.{uA} 𝒜)).isProjective := by
  intro M hM
  let _ : Module.Projective A M := hM.2
  exact (ExactStructure.abelian_isProjective_iff M).2 inferInstance

instance : (gradedFiniteModules 𝒜).IsClosedUnderBinaryProducts :=
  (isExtensionClosed_gradedFiniteModules (𝒜 := 𝒜)).isClosedUnderBinaryProducts

private noncomputable def biprodLinearEquiv (M N : GradedModuleCat.{uA} 𝒜) :
    ((M ⊞ N : GradedModuleCat 𝒜) : Type uA) ≃ₗ[A] (M × N) := by
  let B : GradedModuleCat 𝒜 := M ⊞ N
  let f : B →ₗ[A] (M × N) := LinearMap.prod
    ((biprod.fst : B ⟶ M).hom) ((biprod.snd : B ⟶ N).hom)
  let g : (M × N) →ₗ[A] B := LinearMap.coprod
    ((biprod.inl : M ⟶ B).hom) ((biprod.inr : N ⟶ B).hom)
  exact LinearEquiv.ofLinearMap f g
    (by
      apply LinearMap.ext
      rintro ⟨x, y⟩
      dsimp [f, g]
      simp only [LinearMap.prod_apply, map_add, Function.prod_apply]
      ext
      · change (((biprod.inl : M ⟶ B) ≫ biprod.fst).hom) x +
            (((biprod.inr : N ⟶ B) ≫ biprod.fst).hom) y = ((𝟙 M : M ⟶ M).hom) x
        simp
      · change (((biprod.inl : M ⟶ B) ≫ biprod.snd).hom) x +
            (((biprod.inr : N ⟶ B) ≫ biprod.snd).hom) y = ((𝟙 N : N ⟶ N).hom) y
        simp)
    (by
      apply LinearMap.ext
      intro x
      change (((biprod.fst : B ⟶ M) ≫ biprod.inl +
        (biprod.snd : B ⟶ N) ≫ biprod.inr).hom) x = ((𝟙 B : B ⟶ B).hom) x
      rw [biprod.total])

instance : (gradedFiniteProjectiveModules 𝒜).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN => by
    let _ : Module.Finite A M := hM.1
    let _ : Module.Projective A M := hM.2
    let _ : Module.Finite A N := hN.1
    let _ : Module.Projective A N := hN.2
    exact ⟨(gradedFiniteModules 𝒜).prop_biprod_of_isClosedUnderBinaryProducts hM.1 hN.1,
      Module.Projective.of_equiv (biprodLinearEquiv M N).symm⟩

omit [DirectSum.Decomposition 𝒜] in
private noncomputable abbrev gradedModuleExactStructure (𝒜 : ℤ → Submodule k A) :
    GradedExactStructure (GradedModuleCat.{uA} 𝒜) :=
  GradedExactStructure.abelian _ (GradedModuleCat.shift 𝒜)

omit [DirectSum.Decomposition 𝒜] in
private theorem isExtensionClosed_gradedFiniteModules' :
    (gradedModuleExactStructure 𝒜).toExactStructure.IsExtensionClosed
      (gradedFiniteModules 𝒜) := by
  rw [gradedModuleExactStructure, GradedExactStructure.abelian_toExactStructure]
  exact isExtensionClosed_gradedFiniteModules

private theorem gradedFiniteProjectiveModules_le_isProjective' :
    gradedFiniteProjectiveModules 𝒜 ≤
      (gradedModuleExactStructure 𝒜).toExactStructure.isProjective := by
  rw [gradedModuleExactStructure, GradedExactStructure.abelian_toExactStructure]
  exact gradedFiniteProjectiveModules_le_isProjective

omit [DirectSum.Decomposition 𝒜] in
private theorem gradedFiniteModules_shift :
    (gradedFiniteModules 𝒜).inverseImage (GradedModuleCat.shift 𝒜).functor =
      gradedFiniteModules 𝒜 :=
  rfl

omit [DirectSum.Decomposition 𝒜] in
private theorem gradedFiniteProjectiveModules_shift :
    (gradedFiniteProjectiveModules 𝒜).inverseImage (GradedModuleCat.shift 𝒜).functor =
      gradedFiniteProjectiveModules 𝒜 :=
  rfl

omit [DirectSum.Decomposition 𝒜] in
private theorem gradedFiniteModules_shift' :
    (gradedFiniteModules 𝒜).inverseImage (gradedModuleExactStructure 𝒜).shift.functor =
      gradedFiniteModules 𝒜 := by
  rw [gradedModuleExactStructure, GradedExactStructure.abelian_shift]
  exact gradedFiniteModules_shift

omit [DirectSum.Decomposition 𝒜] in
private theorem gradedFiniteProjectiveModules_shift' :
    (gradedFiniteProjectiveModules 𝒜).inverseImage
        (gradedModuleExactStructure 𝒜).shift.functor =
      gradedFiniteProjectiveModules 𝒜 := by
  rw [gradedModuleExactStructure, GradedExactStructure.abelian_shift]
  exact gradedFiniteProjectiveModules_shift

/-- The induced graded exact structure on finite graded modules. -/
noncomputable def gradedFiniteModulesExactStructure (𝒜 : ℤ → Submodule k A) :
    GradedExactStructure (gradedFiniteModules 𝒜).FullSubcategory :=
  (gradedModuleExactStructure 𝒜).fullSubcategory _
    isExtensionClosed_gradedFiniteModules' gradedFiniteModules_shift'

/-- The induced graded exact structure on finite graded modules with projective underlying
module. -/
noncomputable def gradedFiniteProjectiveModulesExactStructure (𝒜 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝒜] :
    GradedExactStructure (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
  (gradedModuleExactStructure 𝒜).fullSubcategory _
    (ExactStructure.isExtensionClosed_of_le_isProjective
      gradedFiniteProjectiveModules_le_isProjective')
    gradedFiniteProjectiveModules_shift'

/-- The underlying exact structure on finite graded projectives is the split exact structure. -/
theorem gradedFiniteProjectiveModulesExactStructure_eq_split :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure =
      ExactStructure.split (gradedFiniteProjectiveModules 𝒜).FullSubcategory := by
  rw [gradedFiniteProjectiveModulesExactStructure,
    GradedExactStructure.fullSubcategory_toExactStructure]
  exact ExactStructure.fullSubcategory_eq_split
    (gradedFiniteProjectiveModules_le_isProjective' (𝒜 := 𝒜))

/-! ### The graded Cartan map -/

/-- **The graded Cartan map** `c_A^gr : K₀^gr(proj A) ⟶ G₀^gr(mod A)`, induced by inclusion of
finite graded modules with projective underlying module into all finite graded modules. -/
noncomputable def gradedCartanMap (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜] :
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
        (ExactStructure.isExtensionClosed_of_le_isProjective
          gradedFiniteProjectiveModules_le_isProjective')
        isExtensionClosed_gradedFiniteModules'
        gradedFiniteProjectiveModules_shift' gradedFiniteModules_shift'
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

end TauCeti
