/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Subcomplexes of a complex of modules cut out by submodules

Let `K` be a homological complex of `R`-modules and `N i ≤ K.X i` a family of submodules carried
into each other by the differentials.  The terms `N i` with the restricted differentials form a
complex `K.ofSubmodules N hN`, whose inclusion into `K` is a monomorphism, hence a subcomplex
`K.subobjectOfSubmodules N hN` of `K`.  A family of submodules is the natural way to describe a
filtration of a complex of chains on elements, for instance by the cubes satisfying a condition,
and this file turns such a family into a subobject, the form in which filtered complexes enter
the spectral sequence of a filtered complex.

## Main definitions

* `HomologicalComplex.ofSubmodules K N hN`: the complex with terms `N i`.
* `HomologicalComplex.ofSubmodulesι K N hN`: its inclusion into `K`, and
  `HomologicalComplex.ofSubmodulesMap`: the restriction of a chain map.
* `HomologicalComplex.subobjectOfSubmodules K N hN`: the corresponding subcomplex of `K`.

## Main results

* `HomologicalComplex.mem_range_subobjectOfSubmodules_arrow_f_iff`: in degree `i` the subcomplex
  consists of the elements of `N i`.
* `HomologicalComplex.subobjectOfSubmodules_factors`: a chain map carrying the submodules of one
  family into those of another restricts to the subcomplexes; in particular
  (`HomologicalComplex.subobjectOfSubmodules_mono`) the construction is monotone.
* `HomologicalComplex.subobjectOfSubmodules_eq_bot`,
  `HomologicalComplex.epi_subobjectOfSubmodules_arrow_f`: the subcomplex is `⊥` when every `N i`
  is, and is everything in degree `i` when `N i` is.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}

section Construction

variable (K : HomologicalComplex (ModuleCat.{v} R) c) (N : ∀ i, Submodule R (K.X i))
  (hN : ∀ i j, ∀ x ∈ N i, K.d i j x ∈ N j)

/-- The complex with terms the submodules `N i ≤ K.X i` and the restricted differentials. -/
def ofSubmodules : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (N i)
  d i j := ModuleCat.ofHom ((K.d i j).hom.restrict (hN i j))
  shape i j h := by
    ext x
    -- The terms are `ModuleCat.of R (N i)` and the differential is `LinearMap.restrict`, whose
    -- value on `x` has underlying element `K.d i j x` by definition.
    change K.d i j (x : N i).1 = 0
    rw [K.shape i j h]
    rfl
  d_comp_d' i j k _ _ := by
    ext x
    -- As for `shape`: the restricted differentials act on underlying elements by definition.
    change K.d j k (K.d i j (x : N i).1) = 0
    rw [← ModuleCat.comp_apply, K.d_comp_d]
    rfl

/-- The inclusion of the complex with terms `N i` into `K`. -/
def ofSubmodulesι : K.ofSubmodules N hN ⟶ K where
  f i := ModuleCat.ofHom (N i).subtype
  comm' _ _ _ := rfl

/-- The inclusion of the complex with terms `N i` is a monomorphism. -/
instance : Mono (K.ofSubmodulesι N hN) :=
  mono_of_mono_f _ fun _ ↦
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective

/-- The subcomplex of `K` with terms the submodules `N i`. -/
def subobjectOfSubmodules : Subobject K :=
  Subobject.mk (K.ofSubmodulesι N hN)

private theorem subobjectOfSubmodules_eq_mk :
    K.subobjectOfSubmodules N hN = Subobject.mk (K.ofSubmodulesι N hN) :=
  (rfl)

/-- In degree `i`, the subcomplex cut out by `N` consists of the elements of `N i`. -/
theorem mem_range_subobjectOfSubmodules_arrow_f_iff (i : ι) (x : K.X i) :
    x ∈ LinearMap.range ((K.subobjectOfSubmodules N hN).arrow.f i).hom ↔ x ∈ N i := by
  rw [subobjectOfSubmodules_eq_mk, ← Subobject.underlyingIso_hom_comp_eq_mk, comp_f,
    ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance)),
    ofSubmodulesι]
  -- The component of the inclusion is `ModuleCat.ofHom (N i).subtype` by definition.
  exact Iff.of_eq (congrArg (x ∈ ·) (Submodule.range_subtype (N i)))

/-- In a degree where `N i` is everything, the subcomplex is everything. -/
theorem epi_subobjectOfSubmodules_arrow_f {i : ι} (h : N i = ⊤) :
    Epi ((K.subobjectOfSubmodules N hN).arrow.f i) := by
  rw [ModuleCat.epi_iff_surjective, ← LinearMap.range_eq_top, eq_top_iff]
  intro x _
  rw [mem_range_subobjectOfSubmodules_arrow_f_iff, h]
  exact Submodule.mem_top

/-- When every `N i` is zero, the subcomplex is zero. -/
theorem subobjectOfSubmodules_eq_bot (h : ∀ i, N i = ⊥) : K.subobjectOfSubmodules N hN = ⊥ := by
  rw [subobjectOfSubmodules_eq_mk, Subobject.mk_eq_bot_iff_zero]
  ext i x
  have hx : (x : N i).1 = 0 := by simpa [h i] using (x : N i).2
  rw [zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
  exact hx

end Construction

section Map

variable {K L : HomologicalComplex (ModuleCat.{v} R) c} {N : ∀ i, Submodule R (K.X i)}
  {hN : ∀ i j, ∀ x ∈ N i, K.d i j x ∈ N j} {N' : ∀ i, Submodule R (L.X i)}
  {hN' : ∀ i j, ∀ x ∈ N' i, L.d i j x ∈ N' j}

variable (hN hN') in
/-- The restriction of a chain map carrying each `N i` into `N' i`. -/
def ofSubmodulesMap (φ : K ⟶ L) (h : ∀ i, ∀ x ∈ N i, φ.f i x ∈ N' i) :
    K.ofSubmodules N hN ⟶ L.ofSubmodules N' hN' where
  f i := ModuleCat.ofHom ((φ.f i).hom.restrict (h i))
  comm' i j _ := by
    ext x
    exact Subtype.ext (by
      -- As in `ofSubmodules`: restricted maps act on underlying elements by definition.
      change L.d i j (φ.f i (x : N i).1) = φ.f j (K.d i j (x : N i).1)
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.comm])

/-- The restriction of a chain map commutes with the inclusions. -/
@[reassoc (attr := simp)]
theorem ofSubmodulesMap_comp_ofSubmodulesι (φ : K ⟶ L) (h : ∀ i, ∀ x ∈ N i, φ.f i x ∈ N' i) :
    ofSubmodulesMap hN hN' φ h ≫ L.ofSubmodulesι N' hN' = K.ofSubmodulesι N hN ≫ φ := by
  ext i x
  rfl

/-- A chain map carrying each `N i` into `N' i` restricts to the subcomplexes: the composite of
the inclusion of the subcomplex cut out by `N` with the chain map factors through the subcomplex
cut out by `N'`. -/
theorem subobjectOfSubmodules_factors (φ : K ⟶ L) (h : ∀ i, ∀ x ∈ N i, φ.f i x ∈ N' i) :
    (L.subobjectOfSubmodules N' hN').Factors ((K.subobjectOfSubmodules N hN).arrow ≫ φ) := by
  rw [subobjectOfSubmodules_eq_mk L, Subobject.mk_factors_iff, subobjectOfSubmodules_eq_mk K,
    ← Subobject.underlyingIso_hom_comp_eq_mk (K.ofSubmodulesι N hN)]
  refine ⟨(Subobject.underlyingIso _).hom ≫ ofSubmodulesMap hN hN' φ h,
    (Category.assoc _ _ _).trans ((congrArg (fun k ↦ (Subobject.underlyingIso _).hom ≫ k)
      ?_).trans (Category.assoc _ _ _).symm)⟩
  exact ofSubmodulesMap_comp_ofSubmodulesι φ h

/-- The subcomplex cut out by a family of submodules is monotone in the family. -/
theorem subobjectOfSubmodules_mono {N₁ : ∀ i, Submodule R (K.X i)}
    {hN₁ : ∀ i j, ∀ x ∈ N₁ i, K.d i j x ∈ N₁ j} (h : ∀ i, N i ≤ N₁ i) :
    K.subobjectOfSubmodules N hN ≤ K.subobjectOfSubmodules N₁ hN₁ :=
  Subobject.mk_le_mk_of_comm (ofSubmodulesMap hN hN₁ (𝟙 K) fun i _ hx ↦ h i hx) (by
    rw [ofSubmodulesMap_comp_ofSubmodulesι, Category.comp_id])

end Map

end HomologicalComplex
