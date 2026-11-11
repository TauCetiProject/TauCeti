/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The sheaf of smooth vector-valued functions as a sheaf of modules

Let `M` be a real manifold with model `I`, and let `V` be a normed space over a normed field `𝕜`
which is a normed algebra over `ℝ`, compatibly with the real structure of `V`. The smooth
functions `U → V` on the opens `U` of `M` form a sheaf of `𝕜`-modules,
`TauCeti.smoothSheafModule I M 𝕜 V`. Mathlib's `smoothSheafCommRing` and
`smoothSheafCommGroup` carry the same sections with ring and group structures; the module
structure is what Čech cohomology with coefficients in modules needs. The scalars `𝕜` may be
larger than `ℝ`: for `𝕜 = V = ℂ` on a Riemann surface, viewed as a real surface, this is the sheaf
`ℰ` of smooth complex-valued functions, a sheaf of complex vector spaces containing the structure
sheaf `𝒪` as the kernel of the Cauchy-Riemann operator.

## Main definitions

* `TauCeti.smoothSections I 𝕜 V U`: the `𝕜`-submodule of smooth functions in `U → V`.
* `TauCeti.smoothSheafModule I M 𝕜 V`: the sheaf of `𝕜`-modules of smooth `V`-valued functions.
* `TauCeti.smoothSheafModule.sectionsEquiv`: its sections over `U` are `smoothSections I 𝕜 V U`.

## References

* The sheaf is assembled from Mathlib's sheaf of smooth functions,
  `StructureGroupoid.LocalInvariantProp.sheaf`, as in `smoothSheafCommRing` in
  `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather Macbeth and Adam Topaz.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (the sheaf `ℰ` of smooth functions).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  (V : Type v) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]

/-- The smooth functions `U → V` on an open set `U` of `M`, as a `𝕜`-submodule of all functions.
Multiplication by a scalar of `𝕜` is a continuous real-linear map of `V`, so it preserves
smoothness. -/
def smoothSections (U : Opens M) : Submodule 𝕜 (U → V) where
  carrier := {f | ContMDiff I 𝓘(ℝ, V) ∞ f}
  zero_mem' := contMDiff_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf :=
    (((c • ContinuousLinearMap.id 𝕜 V).restrictScalars ℝ).contMDiff).comp hf

variable {I 𝕜 V}

/-- A function belongs to `smoothSections I 𝕜 V U` exactly when it is smooth. -/
@[simp]
theorem mem_smoothSections_iff {U : Opens M} {f : U → V} :
    f ∈ smoothSections I 𝕜 V U ↔ ContMDiff I 𝓘(ℝ, V) ∞ f :=
  Iff.rfl

/-- Restricting a smooth function to a smaller open set gives a smooth function. -/
theorem comp_inclusion_mem_smoothSections {U W : Opens M} (h : W ≤ U) {f : U → V}
    (hf : f ∈ smoothSections I 𝕜 V U) : f ∘ Opens.inclusion h ∈ smoothSections I 𝕜 V W :=
  ContMDiff.comp (I' := I) hf (contMDiff_inclusion h)

variable (I 𝕜 V)

/-- Restriction of smooth functions to a smaller open set. -/
private def smoothRestrict {U W : Opens M} (i : W ⟶ U) :
    smoothSections I 𝕜 V U →ₗ[𝕜] smoothSections I 𝕜 V W where
  toFun f := ⟨f.1 ∘ Opens.inclusion i.le, comp_inclusion_mem_smoothSections i.le f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Smoothness, as a local predicate on functions. -/
private def smoothLocalPredicate : TopCat.LocalPredicate fun _ : TopCat.of M ↦ V where
  pred {U} f := f ∈ smoothSections I 𝕜 V U
  res i _ hf := comp_inclusion_mem_smoothSections i.le hf
  locality {W} f h x := by
    obtain ⟨U, hxU, i, hU⟩ := h x
    -- smoothness of `f` at `x` is smoothness of its restriction to `U` at `x`
    exact ((contDiffWithinAt_localInvariantProp ∞).liftPropAt_iff_comp_inclusion i.le f
      ⟨x, hxU⟩).2 (hU ⟨x, hxU⟩)

/-- The presheaf of `𝕜`-modules of smooth `V`-valued functions. -/
private def smoothPresheafModule : TopCat.Presheaf (ModuleCat.{max u v} 𝕜) (TopCat.of M) where
  obj U := ModuleCat.of 𝕜 (smoothSections I 𝕜 V U.unop)
  map h := ModuleCat.ofHom (smoothRestrict I 𝕜 V h.unop)
  map_id _ := by
    apply ModuleCat.hom_ext
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    rfl

variable (M) in
/-- **The sheaf of smooth `V`-valued functions**, as a sheaf of `𝕜`-modules on `M`. Its sections
over `U` are the smooth functions `U → V` (`smoothSheafModule.sectionsEquiv`), and its restriction
maps restrict functions. -/
def smoothSheafModule : TopCat.Sheaf (ModuleCat.{max u v} 𝕜) (TopCat.of M) where
  obj := smoothPresheafModule I 𝕜 V
  property := by
    have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{max u v} 𝕜) :=
      ModuleCat.hasLimitsOfSize.{u, u, max u v}
    have : Limits.ReflectsLimitsOfSize.{u, u} (forget (ModuleCat.{max u v} 𝕜)) :=
      Limits.reflectsLimits_of_reflectsIsomorphisms
    refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{max u v} 𝕜)) ?_
    -- the underlying presheaf of sets is the subsheaf of smooth functions
    exact TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso)
      fun _ ↦ rfl) (TopCat.subsheafToTypes (smoothLocalPredicate I 𝕜 V)).property

namespace smoothSheafModule

/-- The sections of `smoothSheafModule I M 𝕜 V` over `U` are the smooth functions `U → V`. -/
def sectionsEquiv (U : Opens M) :
    (smoothSheafModule I M 𝕜 V).obj.obj (op U) ≃ₗ[𝕜] smoothSections I 𝕜 V U :=
  LinearEquiv.refl 𝕜 _

variable {I 𝕜 V}

/-- Restriction of sections is restriction of functions. -/
@[simp]
theorem sectionsEquiv_map {U W : Opens M} (h : W ⟶ U)
    (f : (smoothSheafModule I M 𝕜 V).obj.obj (op U)) :
    (sectionsEquiv I 𝕜 V W ((smoothSheafModule I M 𝕜 V).obj.map h.op f)).1 =
      (sectionsEquiv I 𝕜 V U f).1 ∘ Opens.inclusion h.le := (rfl)

/-- Two sections of `smoothSheafModule I M 𝕜 V` are equal when they are equal as functions. -/
theorem ext {U : Opens M} {f g : (smoothSheafModule I M 𝕜 V).obj.obj (op U)}
    (h : ∀ x, (sectionsEquiv I 𝕜 V U f).1 x = (sectionsEquiv I 𝕜 V U g).1 x) : f = g :=
  (sectionsEquiv I 𝕜 V U).injective (Subtype.ext (funext h))

end smoothSheafModule

end TauCeti
