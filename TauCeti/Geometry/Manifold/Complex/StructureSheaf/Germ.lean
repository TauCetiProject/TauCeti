/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import TauCeti.Geometry.Manifold.ContMDiff.Analytic

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
  germs of the functions which are complex analytic (`ContMDiffAt` at order `ω`) near `x` (and on a
  complex normed space, `exists_analyticAt_toFilterGerm_eq`, `exists_toFilterGerm_eq_of_analyticAt`,
  and `exists_toFilterGerm_nhds_eq_iff_analyticAt` express this directly via `AnalyticAt`);
* `eval_eq_of_toFilterGerm_eq`: the value of a holomorphic germ is the value of any function
  with the same germ;
* `toFilterGerm_stalkPrecomp`: pulling a holomorphic germ back along a complex analytic map `f`
  is composition of germs with `f`;
* `quotientMk_comp_stalkPrecomp_bijective`: if an ideal of germs at `p` on a normed space consists
  of the germs vanishing along a local holomorphic section `σ` of a holomorphic map
  `π`, then pulling back along `π` identifies the germs at `π p` with the quotient by that ideal.
  This computes local rings of analytic subsets that are locally graphs.
  The inverse is composition with `σ` (`toFilterGerm_eq_comp_of_quotientMk_stalkPrecomp_eq`).

The holomorphic germ of a globally analytic function is `germOfContMDiff`.

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

/-- The holomorphic germ at `x` of a function which is complex analytic on all of `X`. -/
def germOfContMDiff (f : X → ℂ) (hf : ContMDiff I 𝓘(ℂ) ω f) (x : X) :
    (holomorphicStructureSheaf I X).presheaf.stalk x :=
  ConcreteCategory.hom ((holomorphicStructureSheaf I X).presheaf.germ ⊤ x trivial)
    (ofContMDiff (fun y : (⊤ : Opens X) ↦ f y) (hf.comp contMDiff_subtype_val))

/-- The holomorphic germ of a globally analytic function `f` is the germ of `f`. -/
@[simp]
theorem toFilterGerm_germOfContMDiff (f : X → ℂ) (hf : ContMDiff I 𝓘(ℂ) ω f) {x : X}
    {l : Filter X} (hl : l ≤ 𝓝 x) : toFilterGerm I X x l hl (germOfContMDiff f hf x) = f :=
  toFilterGerm_germ hl trivial _ f fun y ↦ ofContMDiff_apply _ _ y

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

/-- Every holomorphic germ on the complex line has an analytic representative, simultaneously
along every filter finer than the neighbourhood filter. -/
theorem exists_toFilterGerm_eq_analyticAt (a : ℂ)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f a ∧
      ∀ (l : Filter ℂ) (hl : l ≤ 𝓝 a), toFilterGerm 𝓘(ℂ) ℂ a l hl s = f := by
  obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq a s
  exact ⟨f, (contMDiffAt_iff_contDiffAt.mp hf.self_of_nhds).analyticAt, hfs⟩

/-- A function analytic at a point of the complex line is manifold analytic near that point. -/
theorem eventually_contMDiffAt_of_analyticAt {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    ∀ᶠ z in 𝓝 a, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f z :=
  hf.eventually_analyticAt.mono fun _ hz ↦ contMDiffAt_iff_contDiffAt.mpr hz.contDiffAt

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

/-- The value of a holomorphic germ is the value at the base point of any function with the same
germ along `𝓝 x`. -/
theorem eval_eq_of_toFilterGerm_eq {x : X} {s : (holomorphicStructureSheaf I X).presheaf.stalk x}
    {f : X → ℂ} (h : toFilterGerm I X x (𝓝 x) le_rfl s = f) : eval I X x s = f x := by
  obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf I X).presheaf.exists_germ_eq s
  rw [toFilterGerm_germ le_rfl hx g _ fun y ↦
    (Subtype.val_injective.extend_apply _ (0 : X → ℂ) y).symm, Germ.coe_eq] at h
  rw [eval_germ, ← h.eq_of_nhds]
  exact (Subtype.val_injective.extend_apply _ (0 : X → ℂ) (⟨x, hx⟩ : U)).symm

/-- The value of the holomorphic germ of a globally analytic function `f` at `x` is `f x`. -/
@[simp]
theorem eval_germOfContMDiff (f : X → ℂ) (hf : ContMDiff I 𝓘(ℂ) ω f) (x : X) :
    eval I X x (germOfContMDiff f hf x) = f x :=
  eval_eq_of_toFilterGerm_eq (toFilterGerm_germOfContMDiff f hf le_rfl)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- The germ of the pullback of a holomorphic germ along a complex analytic map `f` is the
composition with `f` of the germ. -/
theorem toFilterGerm_stalkPrecomp (f : X → Y) (hf : ContMDiff I J ω f) (x : X)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk (f x)) :
    toFilterGerm I X x (𝓝 x) le_rfl (stalkPrecomp I X f hf x s) =
      (toFilterGerm J Y (f x) (𝓝 (f x)) le_rfl s).compTendsto f (hf.continuous.tendsto x) := by
  obtain ⟨U, hx, g, rfl⟩ := (holomorphicStructureSheaf J Y).presheaf.exists_germ_eq s
  have hg : ∀ y : U, toFun J Y (op U) g y = (Subtype.val.extend (toFun J Y (op U) g) 0 : Y → ℂ) y :=
    fun y ↦ (Subtype.val_injective.extend_apply _ (0 : Y → ℂ) y).symm
  rw [stalkPrecomp_germ, toFilterGerm_germ le_rfl hx g _ hg]
  exact (toFilterGerm_germ (U := (Opens.map (TopCat.ofHom ⟨f, hf.continuous⟩)).obj U) le_rfl hx _
    _ fun y ↦ (precomp_apply I X f hf (op U) g y).trans (hg ⟨f y.1, y.2⟩)).trans
    (Germ.coe_compTendsto _ _).symm

/-- Pulling back the holomorphic germ of a globally analytic function `g` along a complex analytic
map `f` gives the holomorphic germ of `g ∘ f`. -/
@[simp]
theorem stalkPrecomp_germOfContMDiff (f : X → Y) (hf : ContMDiff I J ω f) (g : Y → ℂ)
    (hg : ContMDiff J 𝓘(ℂ) ω g) (x : X) :
    stalkPrecomp I X f hf x (germOfContMDiff g hg (f x)) =
      germOfContMDiff (g ∘ f) (hg.comp hf) x :=
  toFilterGerm_nhds_injective x <| by
    rw [toFilterGerm_stalkPrecomp, toFilterGerm_germOfContMDiff, toFilterGerm_germOfContMDiff,
      Germ.coe_compTendsto]

section NormedSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- On a complex normed space, every holomorphic germ at `p` is represented by a function
analytic at `p`, simultaneously along every filter finer than `𝓝 p`. -/
theorem exists_analyticAt_toFilterGerm_eq (p : V)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) :
    ∃ φ : V → ℂ, AnalyticAt ℂ φ p ∧
      ∀ (l : Filter V) (hl : l ≤ 𝓝 p), toFilterGerm 𝓘(ℂ, V) V p l hl s = φ := by
  obtain ⟨φ, hφ_cm, hφ⟩ := exists_toFilterGerm_eq p s
  exact ⟨φ, contMDiffAt_modelSpace_omega_iff_analyticAt.1 hφ_cm.self_of_nhds, hφ⟩

/-- On a complex normed space, a function analytic at `p` has a holomorphic germ at `p`, with
the same germ along every filter finer than `𝓝 p`. -/
theorem exists_toFilterGerm_eq_of_analyticAt {p : V} {φ : V → ℂ} (hφ : AnalyticAt ℂ φ p) :
    ∃ s : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p,
      ∀ (l : Filter V) (hl : l ≤ 𝓝 p), toFilterGerm 𝓘(ℂ, V) V p l hl s = φ :=
  exists_toFilterGerm_eq_of_eventually_contMDiffAt
    (hφ.eventually_analyticAt.mono fun _ ↦ contMDiffAt_modelSpace_omega_iff_analyticAt.2)

/-- On a complex normed space, a function has a holomorphic germ at `p` with the same germ
along `𝓝 p` exactly when it is analytic at `p`. -/
theorem exists_toFilterGerm_nhds_eq_iff_analyticAt {p : V} {φ : V → ℂ} :
    (∃ s, toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl s = φ) ↔ AnalyticAt ℂ φ p :=
  exists_toFilterGerm_nhds_eq_iff.trans
    ⟨fun h ↦ contMDiffAt_modelSpace_omega_iff_analyticAt.1 h.self_of_nhds,
      fun h ↦ h.eventually_analyticAt.mono fun _ ↦ contMDiffAt_modelSpace_omega_iff_analyticAt.2⟩

end NormedSpace

/-! ### Germs along a holomorphic section -/

section HolomorphicSection

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Inverting pullback along a holomorphic section.** Let `σ` be a local section of `π : V → W`
near `π p`, and `J` an ideal of the holomorphic germs at `p` consisting exactly of the germs
vanishing along `σ`. If the pullback along `π` of a germ `h` at `π p` agrees modulo `J` with a
germ represented by `G`, then `h` is represented by `G ∘ σ`. -/
theorem toFilterGerm_eq_comp_of_quotientMk_stalkPrecomp_eq {π : V → W}
    (hπ : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, W) ω π) {σ : W → V} {p : V}
    (hπσ : ∀ᶠ w in 𝓝 (π p), π (σ w) = w)
    (J : Ideal ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p))
    (hJ : ∀ (g : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) (G : V → ℂ),
      toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl g = G →
        (g ∈ J ↔ ∀ᶠ w in 𝓝 (π p), G (σ w) = 0))
    {h : (holomorphicStructureSheaf 𝓘(ℂ, W) W).presheaf.stalk (π p)}
    {g : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p} {G : V → ℂ}
    (hgG : toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl g = G)
    (hhg : Ideal.Quotient.mk J (stalkPrecomp 𝓘(ℂ, V) V π hπ p h) = Ideal.Quotient.mk J g) :
    toFilterGerm 𝓘(ℂ, W) W (π p) (𝓝 (π p)) le_rfl h = G ∘ σ := by
  obtain ⟨H, -, hH⟩ := exists_toFilterGerm_eq (π p) h
  rw [Ideal.Quotient.eq] at hhg
  have hHG := (hJ _ (H ∘ π - G) (by
    rw [map_sub, toFilterGerm_stalkPrecomp, hH, hgG, Germ.coe_compTendsto, ← Germ.coe_sub])).1 hhg
  rw [hH, Germ.coe_eq]
  filter_upwards [hHG, hπσ] with w hw hπw
  rwa [Pi.sub_apply, Function.comp_apply, hπw, sub_eq_zero] at hw

/-- **Germs on the image of a holomorphic section.** Let `π : V → W` be holomorphic and `σ` a
local holomorphic section of `π` near `π p`. If an ideal `J` of the holomorphic germs
at `p` consists exactly of the germs vanishing along `σ`, then pulling back along `π` identifies
the holomorphic germs at `π p` with the germs at `p` modulo `J`. -/
theorem quotientMk_comp_stalkPrecomp_bijective {π : V → W} (hπ : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, W) ω π)
    {σ : W → V} {p : V} (hσ : ContDiffAt ℂ ω σ (π p))
    (hπσ : ∀ᶠ w in 𝓝 (π p), π (σ w) = w)
    (J : Ideal ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p))
    (hJ : ∀ (g : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p) (G : V → ℂ),
      toFilterGerm 𝓘(ℂ, V) V p (𝓝 p) le_rfl g = G →
        (g ∈ J ↔ ∀ᶠ w in 𝓝 (π p), G (σ w) = 0)) :
    Bijective ((Ideal.Quotient.mk J).comp (stalkPrecomp 𝓘(ℂ, V) V π hπ p)) := by
  -- The section passes through `p`: otherwise the indicator of a neighbourhood of `σ (π p)`
  -- away from `p` is a germ at `p` vanishing along `σ`, yet equal to `1` along `σ` near `π p`.
  have hσp : σ (π p) = p := by
    by_contra hne
    obtain ⟨U, U', hU, hU', hpU, hqU', hdisj⟩ := t2_separation (Ne.symm hne)
    classical
    have h0 := (hJ 0 (U'.indicator fun _ ↦ 1) (by
      rw [map_zero, ← Germ.coe_zero]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hU.mem_nhds hpU] with x hx
      exact (Set.indicator_of_notMem (fun h ↦ hdisj.le_bot ⟨hx, h⟩) _).symm)).1 (zero_mem J)
    have h1 : ∀ᶠ w in 𝓝 (π p), σ w ∈ U' := hσ.continuousAt.eventually (hU'.mem_nhds hqU')
    obtain ⟨w, hw0, hw1⟩ := (h0.and h1).exists
    simp [hw1] at hw0
  constructor
  · -- A germ at `π p` whose pullback vanishes along `σ` vanishes, since `π ∘ σ = id`.
    rw [injective_iff_map_eq_zero]
    intro h hh
    apply toFilterGerm_nhds_injective (π p)
    rw [toFilterGerm_eq_comp_of_quotientMk_stalkPrecomp_eq hπ hπσ J hJ (G := 0)
      (by rw [map_zero, Germ.coe_zero]) (hh.trans (map_zero _).symm), map_zero]
    rfl
  · -- A germ `G` at `p` agrees along `σ` with the pullback of `G ∘ σ`.
    intro z
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨G, hG, hGg⟩ := exists_toFilterGerm_eq p g
    have hσt : Tendsto σ (𝓝 (π p)) (𝓝 p) := by
      simpa only [hσp] using hσ.continuousAt.tendsto
    have hGσ : ∀ᶠ w in 𝓝 (π p), ContMDiffAt 𝓘(ℂ, W) 𝓘(ℂ) ω (G ∘ σ) w := by
      filter_upwards [hσt.eventually hG, hσ.eventually (by simp)] with w hGw hσw
      rw [contMDiffAt_iff_contDiffAt] at hGw ⊢
      exact hGw.comp w hσw
    obtain ⟨h, hh⟩ := exists_toFilterGerm_eq_of_eventually_contMDiffAt hGσ
    refine ⟨h, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    refine (hJ _ (G ∘ σ ∘ π - G) ?_).2 ?_
    · rw [map_sub, toFilterGerm_stalkPrecomp, hh, hGg, Germ.coe_compTendsto, ← Germ.coe_sub]
      rfl
    · filter_upwards [hπσ] with w hw
      simp [hw]

end HolomorphicSection

end TauCeti.holomorphicStructureSheaf
