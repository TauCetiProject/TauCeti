/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Meromorphic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Basic
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# The sheaf `𝒪_D` of a divisor on a Riemann surface

Let `X` be a Riemann surface and `D` a divisor on `X`, a finite formal integer sum of points
(`TauCeti.AlgebraicGeometry.WeilDivisor`). The sheaf `𝒪_D` assigns to an open set `U` the
meromorphic functions `f` on `U` with `ord_x f ≥ -D x` at every `x ∈ U`: poles of order at most
`D x` are allowed where `D x > 0`, and zeros of order at least `-D x` are required where
`D x < 0`. These are the sheaves whose cohomology enters the Riemann–Roch theorem; `𝒪_0` is the
structure sheaf, and for `D ≤ E` there is an inclusion `𝒪_D ⟶ 𝒪_E`.

## Representing sections by functions

A meromorphic function has no value at a pole. A section of `𝒪_D` over `U` is therefore
represented by an honest function `U → ℂ`, normalized as follows
(`TauCeti.RiemannSurface.IsDivisorSectionAt`): near each point it is meromorphic with order at
least `-D x`, at the points where `D x ≤ 0` it is holomorphic, and at the finitely many points
where `D x > 0` its value is `0`. Values are pinned at every point, so a section is determined by
the meromorphic function it represents: two sections agreeing outside a closed discrete set are
equal (`TauCeti.RiemannSurface.eq_of_eventuallyEq_codiscrete`). (That every meromorphic function
with divisor at least `-D` on `U` has such a normalized representative is not proved in this
file.) The normalization does not depend
on the function, so these functions form a complex vector space under the pointwise operations, and
a sheaf: the defining condition is local, and the sheaf is Mathlib's sheaf of functions satisfying
a local predicate (`TopCat.subsheafToTypes`).

With this normalization the inclusion `𝒪_D ⟶ 𝒪_E` for `D ≤ E` is not literally the identity of
functions: it sets to `0` the values at the new poles allowed by `E`, where a section of `𝒪_D`
may be holomorphic with a nonzero value (`TauCeti.RiemannSurface.divisorSheafMapOfLE_app`). It is
injective on sections, and functorial in the divisor.

## Main definitions

* `TauCeti.RiemannSurface.IsDivisorSectionAt D f x`: `f : X → ℂ` is a local section of `𝒪_D`
  at `x`.
* `TauCeti.RiemannSurface.divisorSections D U`: the complex vector space of sections of `𝒪_D` over
  an open set `U`, as functions on `U`.
* `TauCeti.RiemannSurface.divisorSheaf D`: the sheaf `𝒪_D` of complex vector spaces.
* `TauCeti.RiemannSurface.divisorSheafZeroIso`: `𝒪_0` is the holomorphic structure sheaf
  `TauCeti.holomorphicStructureSheafModules`.
* `TauCeti.RiemannSurface.divisorSheafMapOfLE`: the inclusion `𝒪_D ⟶ 𝒪_E` for `D ≤ E`, a
  monomorphism.

## Main results

* `TauCeti.RiemannSurface.isDivisorSectionAt_iff_of_eq_zero` and
  `TauCeti.RiemannSurface.mem_divisorSections_iff_contMDiff`: away from the support of `D`, the
  sections of `𝒪_D` are the holomorphic functions.
* `TauCeti.RiemannSurface.eq_of_eventuallyEq_codiscrete`: sections of `𝒪_D` are determined by
  their values outside a closed discrete set.
* `TauCeti.RiemannSurface.divisorSheafMapOfLE_app_injective`, `divisorSheafMapOfLE_refl` and
  `divisorSheafMapOfLE_comp`: the inclusions are injective and functorial.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (divisors, the sheaves `𝒪_D` and their inclusions).
* The sheaf of vector spaces is assembled from a sheaf of types of functions as in
  `smoothSheafCommRing` in `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather Macbeth and
  Adam Topaz.
-/

public noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open _root_.TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A function `f : X → ℂ` is a *local section of `𝒪_D` at `x`* when it is meromorphic at `x`
with order at least `-D x`, it is holomorphic at `x` when `D x ≤ 0`, and it takes the value `0`
at `x` when `0 < D x`. -/
structure IsDivisorSectionAt (D : WeilDivisor X) (f : X → ℂ) (x : X) : Prop where
  /-- The function is meromorphic at `x`. -/
  meromorphicAt : MeromorphicAt f x
  /-- The order at `x` is at least `-D x`: a pole of order at most `D x` when `0 < D x`, a zero
  of order at least `-D x` when `D x < 0`. -/
  neg_le_meromorphicOrderAt : ((-D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f x
  /-- Where `D` allows no pole, the function is holomorphic at `x`. -/
  contMDiffAt : D x ≤ 0 → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x
  /-- Where `D` allows a pole, the value at `x` is the normalized value `0`. -/
  apply_eq_zero : 0 < D x → f x = 0

namespace IsDivisorSectionAt

variable {D : WeilDivisor X} {f g : X → ℂ} {x : X}

/-- Being a local section of `𝒪_D` at `x` only depends on the germ at `x`. -/
theorem congr (hf : IsDivisorSectionAt D f x) (h : f =ᶠ[𝓝 x] g) : IsDivisorSectionAt D g x where
  meromorphicAt := hf.meromorphicAt.congr (h.filter_mono nhdsWithin_le_nhds)
  neg_le_meromorphicOrderAt :=
    meromorphicOrderAt_congr (h.filter_mono nhdsWithin_le_nhds) ▸ hf.neg_le_meromorphicOrderAt
  contMDiffAt hD := (hf.contMDiffAt hD).congr_of_eventuallyEq h.symm
  apply_eq_zero hD := h.self_of_nhds ▸ hf.apply_eq_zero hD

variable (D x) in
/-- The zero function is a local section of `𝒪_D`. -/
theorem zero : IsDivisorSectionAt D 0 x where
  meromorphicAt := meromorphicAt_const 0 x
  neg_le_meromorphicOrderAt := by
    classical
    have h := meromorphicOrderAt_const (0 : ℂ) x
    simp only [↓reduceIte] at h
    rw [Pi.zero_def, h]
    exact le_top
  contMDiffAt _ := contMDiffAt_const
  apply_eq_zero _ := rfl

/-- Local sections of `𝒪_D` are closed under addition. -/
theorem add (hf : IsDivisorSectionAt D f x) (hg : IsDivisorSectionAt D g x) :
    IsDivisorSectionAt D (f + g) x where
  meromorphicAt := hf.meromorphicAt.add hg.meromorphicAt
  neg_le_meromorphicOrderAt := (le_min hf.neg_le_meromorphicOrderAt
    hg.neg_le_meromorphicOrderAt).trans (meromorphicOrderAt_add hf.meromorphicAt hg.meromorphicAt)
  contMDiffAt hD := (hf.contMDiffAt hD).add (hg.contMDiffAt hD)
  apply_eq_zero hD := by simp [hf.apply_eq_zero hD, hg.apply_eq_zero hD]

/-- Local sections of `𝒪_D` are closed under multiplication by constants. -/
theorem const_smul (hf : IsDivisorSectionAt D f x) (c : ℂ) : IsDivisorSectionAt D (c • f) x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using zero D x
  exact
  { meromorphicAt := hf.meromorphicAt.const_smul c
    neg_le_meromorphicOrderAt := by
      simpa [meromorphicOrderAt_def, Pi.smul_comp,
        meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc] using hf.neg_le_meromorphicOrderAt
    contMDiffAt := fun hD ↦
      (contMDiffAt_const (c := c) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω _ x).smul (hf.contMDiffAt hD)
    apply_eq_zero := fun hD ↦ by simp [hf.apply_eq_zero hD] }

/-- **Increasing the divisor.** For `D ≤ E`, a local section of `𝒪_D` gives a local section of
`𝒪_E` after its values at the poles allowed by `E` are set to `0`. -/
theorem indicator (hf : IsDivisorSectionAt D f x) {E : WeilDivisor X} (h : D ≤ E) :
    IsDivisorSectionAt E ({y | E y ≤ 0}.indicator f) x := by
  have hev : {y | E y ≤ 0}.indicator f =ᶠ[𝓝[≠] x] f := by
    have := ChartedSpace.t1Space ℂ X
    filter_upwards [E.eventually_eq_zero_nhdsNE x] with y hy
    exact Set.indicator_of_mem (show y ∈ {y | E y ≤ 0} from hy.le) f
  exact
  { meromorphicAt := hf.meromorphicAt.congr hev.symm
    neg_le_meromorphicOrderAt := by
      rw [meromorphicOrderAt_congr hev]
      exact le_trans (by exact_mod_cast neg_le_neg (h x)) hf.neg_le_meromorphicOrderAt
    contMDiffAt := fun hE ↦ (hf.contMDiffAt ((h x).trans hE)).congr_of_eventuallyEq
      (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hev
        (Set.indicator_of_mem (show x ∈ {y | E y ≤ 0} from hE) f))
    apply_eq_zero := fun hE ↦
      Set.indicator_of_notMem (show x ∉ {y | E y ≤ 0} from not_le.2 hE) f }

end IsDivisorSectionAt

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Away from the support of `D`, the local sections of `𝒪_D` are the holomorphic germs. -/
theorem isDivisorSectionAt_iff_of_eq_zero {D : WeilDivisor X} {f : X → ℂ} {x : X}
    (hD : D x = 0) :
    IsDivisorSectionAt D f x ↔ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  refine ⟨fun hf ↦ hf.contMDiffAt hD.le, fun hf ↦ ?_⟩
  have hev := (contMDiffAt_iff_eventually_mdifferentiableAt (by simp)).1 hf
  exact
  { meromorphicAt := meromorphicAt_of_eventually_mdifferentiableAt hev
    neg_le_meromorphicOrderAt := by
      simpa [hD] using meromorphicOrderAt_nonneg_of_eventually_mdifferentiableAt hev
    contMDiffAt := fun _ ↦ hf
    apply_eq_zero := fun h ↦ absurd hD h.ne' }

end IsManifold

/-- The sections of `𝒪_D` over an open set `U`, as functions on `U`: near each point of `U` they
agree with a local section of `𝒪_D` in the sense of `IsDivisorSectionAt`. -/
def divisorSections (D : WeilDivisor X) (U : Opens X) : Submodule ℂ (U → ℂ) where
  carrier := {f | ∀ x : U, ∃ g : X → ℂ, IsDivisorSectionAt D g x ∧ f =ᶠ[𝓝 x] g ∘ Subtype.val}
  zero_mem' x := ⟨0, .zero D x, EventuallyEq.rfl⟩
  add_mem' {f₁ f₂} hf₁ hf₂ x := by
    obtain ⟨g₁, h₁, e₁⟩ := hf₁ x
    obtain ⟨g₂, h₂, e₂⟩ := hf₂ x
    exact ⟨g₁ + g₂, h₁.add h₂, e₁.add e₂⟩
  smul_mem' c f hf x := by
    obtain ⟨g, h, e⟩ := hf x
    exact ⟨c • g, h.const_smul c, e.const_smul c⟩

variable {D : WeilDivisor X}

/-- Membership in `divisorSections D U`: near every point of `U` the function agrees with a local
section of `𝒪_D` on `X`. -/
theorem mem_divisorSections_iff {U : Opens X} {f : U → ℂ} :
    f ∈ divisorSections D U ↔
      ∀ x : U, ∃ g : X → ℂ, IsDivisorSectionAt D g x ∧ f =ᶠ[𝓝 x] g ∘ Subtype.val :=
  Iff.rfl

/-- A function on `X` which is a local section of `𝒪_D` at every point of `U` restricts to a section
of `𝒪_D` over `U`. -/
theorem comp_val_mem_divisorSections {U : Opens X} {g : X → ℂ}
    (hg : ∀ x ∈ U, IsDivisorSectionAt D g x) : g ∘ Subtype.val ∈ divisorSections D U :=
  fun x ↦ ⟨g, hg x x.2, EventuallyEq.rfl⟩

/-- A section of `𝒪_D` over `U`, extended by zero to `X`, is a local section of `𝒪_D` at every
point of `U`. -/
theorem isDivisorSectionAt_extend {U : Opens X} {f : U → ℂ} (hf : f ∈ divisorSections D U)
    (x : U) : IsDivisorSectionAt D (Subtype.val.extend f 0) x := by
  obtain ⟨g, hg, e⟩ := hf x
  refine hg.congr ?_
  rw [← U.isOpenEmbedding'.map_nhds_eq x, EventuallyEq, eventually_map]
  filter_upwards [e] with y hy
  rw [Subtype.val_injective.extend_apply, hy, Function.comp_apply]

/-- Sections of `𝒪_D` restrict to smaller open sets. -/
theorem comp_inclusion_mem_divisorSections {U V : Opens X} (h : V ≤ U) {f : U → ℂ}
    (hf : f ∈ divisorSections D U) : f ∘ Opens.inclusion h ∈ divisorSections D V := by
  intro x
  obtain ⟨g, hg, e⟩ := hf (Opens.inclusion h x)
  exact ⟨g, hg, ((continuous_inclusion h).tendsto x).eventually e⟩

/-- A section of `𝒪_D` vanishes at the poles allowed by `D`. -/
theorem apply_eq_zero_of_mem_divisorSections {U : Opens X} {f : U → ℂ}
    (hf : f ∈ divisorSections D U) {x : U} (hx : 0 < D x) : f x = 0 := by
  obtain ⟨g, hg, e⟩ := hf x
  rw [e.self_of_nhds, Function.comp_apply, hg.apply_eq_zero hx]

/-- Membership in `divisorSections D U` is local on `U`. -/
private theorem mem_divisorSections_of_local {U : Opens X} (f : U → ℂ)
    (hf : ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U),
      f ∘ Opens.inclusion i.le ∈ divisorSections D V) : f ∈ divisorSections D U := by
  intro x
  obtain ⟨V, hxV, i, hV⟩ := hf x
  obtain ⟨g, hg, e⟩ := hV ⟨x, hxV⟩
  refine ⟨g, hg, ?_⟩
  have hmap := (Opens.isOpenEmbedding_of_le i.le).map_nhds_eq ⟨x, hxV⟩
  rw [show Set.inclusion i.le ⟨x.1, hxV⟩ = x from rfl] at hmap
  rw [← hmap]
  exact e

/-- Membership in `divisorSections` as a local predicate on functions. -/
private def divisorLocalPredicate (D : WeilDivisor X) :
    TopCat.LocalPredicate (fun _ : TopCat.of X ↦ ℂ) where
  pred {U} f := f ∈ divisorSections D U
  res {_ _} i _ hf := comp_inclusion_mem_divisorSections i.le hf
  locality {_} f hf := mem_divisorSections_of_local f hf

/-- Restriction of sections of `𝒪_D` to a smaller open set. -/
private def divisorRestrict (D : WeilDivisor X) {U V : Opens X} (i : V ⟶ U) :
    divisorSections D U →ₗ[ℂ] divisorSections D V where
  toFun f := ⟨f.1 ∘ Opens.inclusion i.le, comp_inclusion_mem_divisorSections i.le f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The presheaf of complex vector spaces of sections of `𝒪_D`. -/
private def divisorPresheaf (D : WeilDivisor X) :
    TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj U := ModuleCat.of ℂ (divisorSections D U.unop)
  map h := ModuleCat.ofHom (divisorRestrict D h.unop)
  map_id _ := by
    apply ModuleCat.hom_ext
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    rfl

variable (D) in
/-- The sheaf `𝒪_D` of a divisor `D` on a Riemann surface, as a sheaf of complex vector spaces.
Its sections over `U` are the functions of `divisorSections D U`: the normalized representatives
of meromorphic functions on `U` with divisor at least `-D`. -/
def divisorSheaf : TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj := divisorPresheaf D
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{u} ℂ))]
    -- The underlying presheaf of sets is the subsheaf of functions cut out by the predicate.
    exact TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun _ ↦ (Equiv.refl _).toIso)
      fun _ ↦ rfl) (TopCat.subsheafToTypes (divisorLocalPredicate D)).property

/-- The sections of `𝒪_D` over `U` are the sections of the submodule `divisorSections D U`. -/
theorem divisorSheaf_obj (D : WeilDivisor X) (U : Opens X) :
    (divisorSheaf D).obj.obj (op U) = ModuleCat.of ℂ (divisorSections D U) := (rfl)

/-- Read a section of `𝒪_D` over `U` as a function on `U` in `divisorSections D U`. -/
def divisorSheafSectionsEquiv (D : WeilDivisor X) (U : Opens X) :
    (divisorSheaf D).obj.obj (op U) ≃ₗ[ℂ] divisorSections D U :=
  LinearEquiv.refl ℂ _

/-- Restriction of sections of `𝒪_D` is restriction of functions. -/
@[simp]
theorem divisorSheafSectionsEquiv_map (D : WeilDivisor X) {U V : Opens X} (h : V ⟶ U)
    (f : (divisorSheaf D).obj.obj (op U)) :
    (divisorSheafSectionsEquiv D V ((divisorSheaf D).obj.map h.op f)).1 =
      (divisorSheafSectionsEquiv D U f).1 ∘ Opens.inclusion h.le := (rfl)

/-- **Sections of `𝒪_D` are meromorphic functions up to discrete sets.** Two sections of `𝒪_D`
over `U` which agree outside a closed discrete subset of `U` are equal. -/
theorem eq_of_eventuallyEq_codiscrete {U : Opens X} {f g : U → ℂ}
    (hf : f ∈ divisorSections D U) (hg : g ∈ divisorSections D U)
    (h : f =ᶠ[codiscrete U] g) : f = g := by
  funext x
  obtain ⟨f₁, hf₁, ef⟩ := hf x
  obtain ⟨g₁, hg₁, eg⟩ := hg x
  rcases lt_or_ge 0 (D x) with hD | hD
  · rw [ef.self_of_nhds, eg.self_of_nhds, Function.comp_apply, Function.comp_apply,
      hf₁.apply_eq_zero hD, hg₁.apply_eq_zero hD]
  · have hcont {k : U → ℂ} {k₁ : X → ℂ} (hk₁ : IsDivisorSectionAt D k₁ x)
        (ek : k =ᶠ[𝓝 x] k₁ ∘ Subtype.val) : ContinuousAt k x :=
      ((hk₁.contMDiffAt hD).continuousAt.comp continuous_subtype_val.continuousAt).congr ek.symm
    have := (tendsto_chartAt_symm_nhdsNE (H := ℂ) x).neBot
    exact tendsto_nhds_unique_of_eventuallyEq
      ((hcont hf₁ ef).tendsto.mono_left nhdsWithin_le_nhds)
      ((hcont hg₁ eg).tendsto.mono_left nhdsWithin_le_nhds)
      ((eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.1 h x (mem_univ _)).mono
        fun y hy ↦ hy (mem_univ y))

section Holomorphic

variable [IsManifold 𝓘(ℂ) 1 X]

/-- On an open set disjoint from the support of `D`, the sections of `𝒪_D` are the holomorphic
functions. -/
theorem mem_divisorSections_iff_contMDiff {U : Opens X} (hU : ∀ x ∈ U, D x = 0) {f : U → ℂ} :
    f ∈ divisorSections D U ↔ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  refine ⟨fun hf x ↦ ?_, fun hf x ↦ ?_⟩
  · obtain ⟨g, hg, e⟩ := hf x
    exact (contMDiffAt_subtype_iff.2 (hg.contMDiffAt (hU x x.2).le)).congr_of_eventuallyEq e
  · refine ⟨Subtype.val.extend f 0, (isDivisorSectionAt_iff_of_eq_zero (hU x x.2)).2 ?_,
      .of_eq (funext fun y ↦ (Subtype.val_injective.extend_apply f 0 y).symm)⟩
    rw [← contMDiffAt_subtype_iff]
    exact (hf x).congr_of_eventuallyEq
      (.of_eq (funext fun y ↦ Subtype.val_injective.extend_apply f 0 y))

end Holomorphic

/-! ### Increasing the divisor -/

/-- For `D ≤ E`, a section of `𝒪_D` gives a section of `𝒪_E` after its values at the poles
allowed by `E` are set to `0`. -/
theorem indicator_mem_divisorSections {E : WeilDivisor X} (h : D ≤ E) {U : Opens X} {f : U → ℂ}
    (hf : f ∈ divisorSections D U) : {y : U | E y ≤ 0}.indicator f ∈ divisorSections E U := by
  intro x
  obtain ⟨g, hg, e⟩ := hf x
  refine ⟨_, hg.indicator h, ?_⟩
  filter_upwards [e] with y hy
  by_cases hy' : E y ≤ 0
  · simp [hy', hy]
  · simp [hy']

/-- The map `𝒪_D(U) → 𝒪_E(U)` for `D ≤ E`. -/
private def divisorSectionsMapOfLE {E : WeilDivisor X} (h : D ≤ E) (U : Opens X) :
    divisorSections D U →ₗ[ℂ] divisorSections E U where
  toFun f := ⟨{y : U | E y ≤ 0}.indicator f.1, indicator_mem_divisorSections h f.2⟩
  map_add' f g := Subtype.ext (Set.indicator_add _ f.1 g.1)
  map_smul' c f := Subtype.ext (Set.indicator_const_smul _ c f.1)

/-- **The inclusion `𝒪_D ⟶ 𝒪_E` for `D ≤ E`.** On sections it is the identity on meromorphic
functions; as functions, the values at the poles allowed by `E` are set to `0`
(`divisorSheafMapOfLE_app`). -/
def divisorSheafMapOfLE {E : WeilDivisor X} (h : D ≤ E) : divisorSheaf D ⟶ divisorSheaf E where
  hom.app U := ModuleCat.ofHom (divisorSectionsMapOfLE h U.unop)
  hom.naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext y
    rfl

-- Index past the unexposed section carriers, so that simp applies the lemma downstream.
/-- The map of sections underlying `divisorSheafMapOfLE`. -/
@[simp]
theorem divisorSheafMapOfLE_app {E : WeilDivisor X} (h : D ≤ E) (U : Opens X)
    (f : (divisorSheaf D).obj.obj (op U)) :
    (no_index (divisorSheafSectionsEquiv E U ((divisorSheafMapOfLE h).hom.app (op U) f))).1 =
      {y : U | E y ≤ 0}.indicator (divisorSheafSectionsEquiv D U f).1 := (rfl)

/-- The inclusion `𝒪_D ⟶ 𝒪_E` is injective on sections. -/
theorem divisorSheafMapOfLE_app_injective {E : WeilDivisor X} (h : D ≤ E) (U : Opens X) :
    Function.Injective ((divisorSheafMapOfLE h).hom.app (op U)) := by
  intro f g hfg
  apply (divisorSheafSectionsEquiv D U).injective
  apply Subtype.ext
  refine eq_of_eventuallyEq_codiscrete (divisorSheafSectionsEquiv D U f).2
    (divisorSheafSectionsEquiv D U g).2 ?_
  have hfg' := congrArg Subtype.val (congrArg (divisorSheafSectionsEquiv E U) hfg)
  rw [divisorSheafMapOfLE_app, divisorSheafMapOfLE_app] at hfg'
  refine eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun x _ ↦ ?_
  -- Near `x`, every point other than `x` lies off the poles allowed by `E`.
  have hval : Tendsto (Subtype.val : U → X) (𝓝[≠] x) (𝓝[≠] (x : X)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_subtype_val.continuousAt.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hy ↦ Subtype.coe_injective.ne hy)
  have := ChartedSpace.t1Space ℂ X
  have hev : ∀ᶠ y : U in 𝓝[≠] x, E y ≤ 0 :=
    hval.eventually ((E.eventually_eq_zero_nhdsNE x).mono fun _ hy ↦ hy.le)
  filter_upwards [hev] with y hy _
  simpa [Set.indicator_of_mem (s := {y : U | E y ≤ 0}) hy] using congrFun hfg' y

/-- The map `𝒪_D ⟶ 𝒪_D` is the identity. -/
@[simp]
theorem divisorSheafMapOfLE_refl : divisorSheafMapOfLE (le_refl D) = 𝟙 (divisorSheaf D) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (divisorSheafSectionsEquiv D U.unop).injective
  apply Subtype.ext
  rw [divisorSheafMapOfLE_app]
  funext y
  by_cases hy : D y ≤ 0
  · exact Set.indicator_of_mem (show y ∈ {y : U.unop | D y ≤ 0} from hy) _
  · exact (Set.indicator_of_notMem (show y ∉ {y : U.unop | D y ≤ 0} from hy) _).trans
      (apply_eq_zero_of_mem_divisorSections (divisorSheafSectionsEquiv D U.unop f).2
        (not_le.1 hy)).symm

/-- The maps `𝒪_D ⟶ 𝒪_E` compose. -/
@[reassoc (attr := simp)]
theorem divisorSheafMapOfLE_comp {E F : WeilDivisor X} (hDE : D ≤ E) (hEF : E ≤ F) :
    divisorSheafMapOfLE hDE ≫ divisorSheafMapOfLE hEF = divisorSheafMapOfLE (hDE.trans hEF) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (divisorSheafSectionsEquiv F U.unop).injective
  apply Subtype.ext
  rw [TopCat.Sheaf.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, divisorSheafMapOfLE_app,
    divisorSheafMapOfLE_app, divisorSheafMapOfLE_app, Set.indicator_indicator]
  congr 1
  exact Set.inter_eq_left.2 fun z hz ↦ (hEF z).trans hz

/-- The map `𝒪_D ⟶ 𝒪_E` is a monomorphism of sheaves. -/
instance divisorSheafMapOfLE_mono {E : WeilDivisor X} (h : D ≤ E) :
    Mono (divisorSheafMapOfLE h) := by
  have (U : (Opens X)ᵒᵖ) : Mono ((divisorSheafMapOfLE h).hom.app U) :=
    ConcreteCategory.mono_of_injective _ (divisorSheafMapOfLE_app_injective h U.unop)
  exact (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} ℂ)).mono_of_mono_map
    (NatTrans.mono_of_mono_app (divisorSheafMapOfLE h).hom)

end

/-! ### The sheaf of the zero divisor -/

section Zero

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- The sections of `𝒪_0` over `U` are the holomorphic sections of the structure sheaf. -/
private def divisorSectionsZeroEquiv (U : Opens X) :
    divisorSections (0 : WeilDivisor X) U ≃ₗ[ℂ]
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U) where
  toFun f := holomorphicStructureSheafModules.ofContMDiff f.1
    ((mem_divisorSections_iff_contMDiff fun _ _ ↦ rfl).1 f.2)
  invFun s := ⟨s, (mem_divisorSections_iff_contMDiff fun _ _ ↦ rfl).2
    (holomorphicStructureSheafModules.contMDiff s)⟩
  map_add' _ _ := holomorphicStructureSheafModules.ext fun _ ↦ by simp
  map_smul' _ _ := holomorphicStructureSheafModules.ext fun _ ↦ by simp
  left_inv f := Subtype.ext (funext fun _ ↦ by simp)
  right_inv s := holomorphicStructureSheafModules.ext fun _ ↦ by simp

variable (X) in
/-- **`𝒪_0` is the structure sheaf.** The sheaf of the zero divisor is the sheaf of holomorphic
functions. -/
def divisorSheafZeroIso :
    divisorSheaf (0 : WeilDivisor X) ≅ holomorphicStructureSheafModules 𝓘(ℂ) X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun U ↦ (divisorSectionsZeroEquiv U.unop).toModuleIso) fun {U V} h ↦ by
      induction U using Opposite.rec
      induction V using Opposite.rec
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      refine holomorphicStructureSheafModules.ext fun x ↦ ?_
      -- Erase the sheaf-to-presheaf and `ModuleCat` compositions, so that the evaluation lemmas
      -- of the structure sheaf apply.
      change divisorSectionsZeroEquiv _ (divisorRestrict 0 h.unop f) x =
        (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.map h (divisorSectionsZeroEquiv _ f) x
      simp [divisorSectionsZeroEquiv, divisorRestrict]

-- Through the unexposed section carriers, simp uses this lemma when it is given its arguments,
-- as in simp only [divisorSheafZeroIso_hom_app_apply U f x].
/-- The isomorphism `𝒪_0 ≅ 𝒪` does not change the underlying functions of sections. -/
@[simp]
theorem divisorSheafZeroIso_hom_app_apply (U : Opens X)
    (f : (divisorSheaf (0 : WeilDivisor X)).obj.obj (op U)) (x : U) :
    (divisorSheafZeroIso X).hom.hom.app (op U) f x =
      (divisorSheafSectionsEquiv 0 U f).1 x :=
  holomorphicStructureSheafModules.ofContMDiff_apply _ _ x

-- Index past the unexposed section carriers, so that simp applies the lemma downstream.
/-- The inverse of the isomorphism `𝒪_0 ≅ 𝒪` does not change the underlying functions of
sections. -/
@[simp]
theorem divisorSheafZeroIso_inv_app_apply (U : Opens X)
    (s : (holomorphicStructureSheafModules 𝓘(ℂ) X).obj.obj (op U)) :
    (no_index (divisorSheafSectionsEquiv 0 U ((divisorSheafZeroIso X).inv.hom.app (op U) s))).1 =
      s :=
  (rfl)

end Zero

/-- The function `z ↦ z⁻¹`, with Lean's value `0⁻¹ = 0`, is a section over `ℂ` of the sheaf of the
divisor `[0]`: it has a simple pole at `0`. -/
example : (fun z : ℂ ↦ z⁻¹) ∘ Subtype.val ∈
    divisorSections (Finsupp.single 0 1 : WeilDivisor ℂ) (⊤ : Opens ℂ) := by
  refine comp_val_mem_divisorSections fun x _ ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · have hm : _root_.MeromorphicAt (fun z : ℂ ↦ z⁻¹) 0 := (analyticAt_id.meromorphicAt).inv
    exact
    { meromorphicAt := by simpa [meromorphicAt_def] using hm
      neg_le_meromorphicOrderAt := by
        have h : _root_.meromorphicOrderAt (fun z : ℂ ↦ z⁻¹) 0 = -1 := by
          have h := _root_.meromorphicOrderAt_inv (f := fun z : ℂ ↦ z - 0) (x := 0)
          rw [meromorphicOrderAt_id_sub_const] at h
          simpa [Pi.inv_def] using h
        simp [meromorphicOrderAt_def, h]
      contMDiffAt := fun h ↦ by simp at h
      apply_eq_zero := fun _ ↦ inv_zero }
  · exact (isDivisorSectionAt_iff_of_eq_zero (by simp [hx])).2
      (contMDiffAt_iff_contDiffAt.2 (contDiffAt_inv ℂ hx))

end TauCeti.RiemannSurface
