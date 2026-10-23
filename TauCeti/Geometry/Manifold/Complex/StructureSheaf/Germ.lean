/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Holomorphic germs as germs of functions

An element of the stalk at `x` of the holomorphic structure sheaf is represented by a holomorphic
function on some open neighbourhood of `x`. Forgetting everything but its values near `x` gives a
germ of functions in Mathlib's sense, along `𝓝 x` or along any finer filter, for instance the
punctured neighbourhood filter `𝓝[≠] x`. This file constructs that comparison as a ring
homomorphism `TauCeti.holomorphicStructureSheaf.toFilterGerm I X x l hl` and proves:

* `toFilterGerm_germ`: the germ of a section is the germ of any function agreeing with it on
  the domain of the section;
* `toFilterGerm_nhds_injective`: a holomorphic germ is determined by its germ along `𝓝 x`;
* `toFilterGerm_nhdsNE_injective`: when `x` is not isolated, it is even determined by its
  germ along the punctured neighbourhoods `𝓝[≠] x`, by continuity;
* `exists_toFilterGerm_nhds_eq_iff`: the image of the comparison along `𝓝 x` consists of the
  germs of the functions which are complex analytic (`ContMDiffAt` at order `ω`) near `x`.

This is the bridge between the categorical stalk and concrete function germs, used to compare
holomorphic germs with meromorphic germs on punctured neighbourhoods.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter Function Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (X : Type) [TopologicalSpace X] [ChartedSpace H X]

/-- The germ along `l ≤ 𝓝 x` of a function agreeing on `U ∋ x` with a section on `U` does not
depend on the values of the function off `U`. -/
private theorem coe_extend_eq {U : Opens X} {x : X} (hx : x ∈ U) {l : Filter X} (hl : l ≤ 𝓝 x)
    (f : (holomorphicStructureSheaf I X).obj.obj (op U)) (g : X → ℂ)
    (hfg : ∀ y : U, toFun I X (op U) f y = g y) :
    ((Subtype.val.extend (toFun I X (op U) f) 0 : X → ℂ) : Germ l ℂ) = g :=
  Germ.coe_eq.2 <| (Eventually.filter_mono hl (U.isOpen.mem_nhds hx)).mono fun y hy ↦
    (Subtype.val_injective.extend_apply _ (0 : X → ℂ) (⟨y, hy⟩ : U)).trans (hfg ⟨y, hy⟩)

/-- The germ along `l ≤ 𝓝 x` of a section on a neighbourhood `U` of `x`, as a ring
homomorphism. -/
private def sectionToFilterGerm {U : Opens X} {x : X} (hx : x ∈ U) {l : Filter X}
    (hl : l ≤ 𝓝 x) : (holomorphicStructureSheaf I X).obj.obj (op U) →+* Germ l ℂ where
  toFun f := (Subtype.val.extend (toFun I X (op U) f) 0 : X → ℂ)
  map_one' := coe_extend_eq I X hx hl 1 1 fun _ ↦ one_apply _
  map_mul' f g := coe_extend_eq I X hx hl (f * g) _ fun y ↦ by
    simp only [Subtype.val_injective.extend_apply]
    exact mul_apply f g y
  map_zero' := coe_extend_eq I X hx hl 0 0 fun _ ↦ zero_apply _
  map_add' f g := coe_extend_eq I X hx hl (f + g) _ fun y ↦ by
    simp only [Subtype.val_injective.extend_apply]
    exact add_apply f g y

/-- The comparison of holomorphic germs with germs of functions, as a morphism in
`CommRingCat`. -/
private def toFilterGermHom (x : X) (l : Filter X) (hl : l ≤ 𝓝 x) :
    (holomorphicStructureSheaf I X).presheaf.stalk x ⟶ CommRingCat.of (Germ l ℂ) :=
  colimit.desc ((OpenNhds.inclusion (X := TopCat.of X) x).op ⋙
      (holomorphicStructureSheaf I X).presheaf)
    { pt := CommRingCat.of (Germ l ℂ)
      ι :=
        { app := fun U ↦ CommRingCat.ofHom (sectionToFilterGerm I X (unop U).2 hl)
          naturality := by
            intro U V h
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro f
            -- Both composites send `f` to the germ of its extension by zero.
            exact coe_extend_eq I X (unop V).2 hl _ _ fun y ↦
              (map_apply (I := I) (X := X)
                (U := op (α := Opens X) (unop U).1) (V := op (α := Opens X) (unop V).1)
                ((OpenNhds.inclusion (X := TopCat.of X) x).map h.unop).op f y).trans
                (Subtype.val_injective.extend_apply _ (0 : X → ℂ) _).symm } }

/-- The comparison of holomorphic germs at `x` with germs of functions along a filter `l` finer
than `𝓝 x`: the germ of a section is the germ along `l` of any function agreeing with the section
on its domain (`toFilterGerm_germ`). -/
def toFilterGerm (x : X) (l : Filter X) (hl : l ≤ 𝓝 x) :
    (holomorphicStructureSheaf I X).presheaf.stalk x →+* Germ l ℂ :=
  (toFilterGermHom I X x l hl).hom

private theorem germ_toFilterGermHom {x : X} {l : Filter X} (hl : l ≤ 𝓝 x) {U : Opens X}
    (hx : x ∈ U) :
    (holomorphicStructureSheaf I X).presheaf.germ U x hx ≫ toFilterGermHom I X x l hl =
      CommRingCat.ofHom (sectionToFilterGerm I X hx hl) :=
  colimit.ι_desc _ _

variable {I X}

/-- The germ of a section is the germ of any function agreeing with the section on its
domain. -/
theorem toFilterGerm_germ {x : X} {l : Filter X} (hl : l ≤ 𝓝 x) {U : Opens X} (hx : x ∈ U)
    (f : (holomorphicStructureSheaf I X).obj.obj (op U)) (g : X → ℂ)
    (hfg : ∀ y : U, toFun I X (op U) f y = g y) :
    toFilterGerm I X x l hl
      (ConcreteCategory.hom ((holomorphicStructureSheaf I X).presheaf.germ U x hx) f) = g := by
  rw [toFilterGerm, ← CommRingCat.comp_apply, germ_toFilterGermHom]
  exact coe_extend_eq I X hx hl f g hfg

/-- Every holomorphic germ at `x` is represented by a function which is complex analytic near
`x`, simultaneously along every filter finer than `𝓝 x`. -/
theorem exists_toFilterGerm_eq (x : X)
    (s : (holomorphicStructureSheaf I X).presheaf.stalk x) :
    ∃ f : X → ℂ, (∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℂ) ω f y) ∧
      ∀ (l : Filter X) (hl : l ≤ 𝓝 x), toFilterGerm I X x l hl s = f := by
  obtain ⟨U, hx, f, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq s
  refine ⟨Subtype.val.extend (toFun I X (op U) f) 0, ?_, fun l hl ↦
    toFilterGerm_germ hl hx f _ fun y ↦ (Subtype.val_injective.extend_apply _ (0 : X → ℂ) y).symm⟩
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  rw [← contMDiffAt_subtype_iff (x := (⟨y, hy⟩ : U))]
  simpa only [Subtype.val_injective.extend_apply] using (contMDiff f).contMDiffAt

/-- A function which is complex analytic near `x` has a holomorphic germ at `x`, with the same
germ as the function along every filter finer than `𝓝 x`. -/
theorem exists_toFilterGerm_eq_of_eventually_contMDiffAt {x : X} {f : X → ℂ}
    (hf : ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℂ) ω f y) :
    ∃ s : (holomorphicStructureSheaf I X).presheaf.stalk x,
      ∀ (l : Filter X) (hl : l ≤ 𝓝 x), toFilterGerm I X x l hl s = f := by
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hf
  let U : Opens X := ⟨t, hto⟩
  let fU : (holomorphicStructureSheaf I X).obj.obj (op U) :=
    ofContMDiff (fun y : U ↦ f y) fun y ↦ contMDiffAt_subtype_iff.2 (ht y y.2)
  exact ⟨ConcreteCategory.hom ((holomorphicStructureSheaf I X).presheaf.germ U x hxt) fU,
    fun l hl ↦ toFilterGerm_germ hl hxt fU f fun y ↦ ofContMDiff_apply _ _ y⟩

/-- A holomorphic germ is determined by its germ along `𝓝 x`. -/
theorem toFilterGerm_nhds_injective (x : X) :
    Injective (toFilterGerm I X x (𝓝 x) le_rfl) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨U, hx, f, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq s
  rw [toFilterGerm_germ le_rfl hx f _ fun y ↦
    (Subtype.val_injective.extend_apply _ (0 : X → ℂ) y).symm, ← Germ.coe_zero, Germ.coe_eq] at hs
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 (hs.and (U.isOpen.mem_nhds hx))
  let W : Opens X := ⟨t, hto⟩
  have hWU : W ≤ U := fun y hy ↦ (ht y hy).2
  rw [← map_zero (ConcreteCategory.hom ((holomorphicStructureSheaf I X).presheaf.germ U x hx))]
  refine TopCat.Presheaf.germ_ext _ W hxt (homOfLE hWU) (homOfLE hWU) (ext fun y ↦ ?_)
  rw [map_apply, map_apply, zero_apply]
  exact (Subtype.val_injective.extend_apply _ (0 : X → ℂ) (Opens.inclusion hWU y)).symm.trans
    (ht y y.2).1

/-- At a point which is not isolated, a holomorphic germ is determined by its germ on the
punctured neighbourhoods of the point, by continuity. -/
theorem toFilterGerm_nhdsNE_injective (x : X) [(𝓝[≠] x).NeBot] :
    Injective (toFilterGerm I X x (𝓝[≠] x) nhdsWithin_le_nhds) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq x s
  have hc : ContinuousAt f x := hf.self_of_nhds.continuousAt
  rw [hfs, ← Germ.coe_zero, Germ.coe_eq] at hs
  apply toFilterGerm_nhds_injective x
  rw [hfs, map_zero, ← Germ.coe_zero, Germ.coe_eq]
  exact (hc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (g := fun _ ↦ 0) continuousAt_const).1 hs

/-- A function has a holomorphic germ at `x` with the same germ along `𝓝 x` exactly when it is
complex analytic near `x`. -/
theorem exists_toFilterGerm_nhds_eq_iff {x : X} {f : X → ℂ} :
    (∃ s, toFilterGerm I X x (𝓝 x) le_rfl s = f) ↔ ∀ᶠ y in 𝓝 x, ContMDiffAt I 𝓘(ℂ) ω f y := by
  refine ⟨fun ⟨s, hs⟩ ↦ ?_, fun hf ↦
    (exists_toFilterGerm_eq_of_eventually_contMDiffAt hf).imp fun _ h ↦ h _ le_rfl⟩
  obtain ⟨g, hg, hgs⟩ := exists_toFilterGerm_eq x s
  rw [hgs, Germ.coe_eq] at hs
  filter_upwards [hg, hs.eventuallyEq_nhds] with y hy hgf
  exact hy.congr_of_eventuallyEq hgf.symm

end TauCeti.holomorphicStructureSheaf
