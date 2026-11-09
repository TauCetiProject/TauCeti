/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
public import TauCeti.Analysis.Complex.RiemannSurface.SphereMap
public import Mathlib.Topology.Sheaves.Functors

/-!
# Local trivializations of divisor sheaves

The sheaf of meromorphic functions with poles bounded by a divisor is locally isomorphic to
the holomorphic structure sheaf. In a coordinate neighbourhood meeting the divisor's support
only at its centre, multiplication by a power of the centered coordinate gives the
trivialization. These are isomorphisms of the actual sheaves, compatible with restriction to
arbitrary smaller opens, which need not be connected.

Divisor sections have normalized values at allowed poles. Consequently multiplication is
followed by filling removable singularities and then restoring these normalized values. This
step is essential for the inverse map even when the divisor has a negative coefficient.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §16 (the locally free sheaf associated with a divisor).
-/

public noncomputable section

open CategoryTheory Filter Function IsManifold OnePoint Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]

private def normalizedProduct (E : WeilDivisor X) (h f : X → ℂ) : X → ℂ :=
  {y | E y ≤ 0}.indicator (fun y ↦ affineChart (sphereMap (h * f) y))

private theorem normalizedProduct_eventuallyEq (E : WeilDivisor X) {h f : X → ℂ} {x : X}
    (hh : MeromorphicAt h x) (hf : MeromorphicAt f x) :
    normalizedProduct E h f =ᶠ[𝓝[≠] x] h * f := by
  have := ChartedSpace.t1Space ℂ X
  filter_upwards [E.eventually_eq_zero_nhdsNE x,
    affineChart_sphereMap_eventuallyEq (hh.mul hf)] with y hy heq
  simp [normalizedProduct, hy, heq]

private theorem isDivisorSectionAt_normalizedProduct {D E : WeilDivisor X}
    {h f : X → ℂ} {x : X} (hh : MeromorphicAt h x)
    (ho : meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (hf : IsDivisorSectionAt D f x) :
    IsDivisorSectionAt E (normalizedProduct E h f) x := by
  have hraw := hh.mul hf.meromorphicAt
  have heq := normalizedProduct_eventuallyEq E hh hf.meromorphicAt
  have hbound : ((-E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (h * f) x := by
    rw [meromorphicOrderAt_mul hh hf.meromorphicAt, ho]
    calc
      ((-E x : ℤ) : WithTop ℤ) =
          ((D x - E x : ℤ) : WithTop ℤ) + ((-D x : ℤ) : WithTop ℤ) := by
        norm_cast
        ring
      _ ≤ _ := add_le_add le_rfl hf.neg_le_meromorphicOrderAt
  refine ⟨hraw.congr heq.symm, ?_, ?_, ?_⟩
  · rwa [meromorphicOrderAt_congr heq]
  · intro hx
    have he : (0 : WithTop ℤ) ≤ ((-E x : ℤ) : WithTop ℤ) := by
      exact_mod_cast neg_nonneg.mpr hx
    have hn := he.trans hbound
    apply (contMDiffAt_affineChart_sphereMap hraw hn).congr_of_eventuallyEq
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · have := ChartedSpace.t1Space ℂ X
      filter_upwards [E.eventually_eq_zero_nhdsNE x] with y hy
      simp [normalizedProduct, hy]
    · simp [normalizedProduct, hx]
  · intro hx
    simp [normalizedProduct, not_le.mpr hx]

private def multiplySection {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (f : divisorSections D U) : divisorSections E U :=
  ⟨normalizedProduct E h (Subtype.val.extend f.1 0) ∘ Subtype.val,
    comp_val_mem_divisorSections fun x hx ↦ isDivisorSectionAt_normalizedProduct
      (hh x hx) (ho x hx) (isDivisorSectionAt_extend f.property ⟨x, hx⟩)⟩

private theorem multiplySection_eventuallyEq {D E : WeilDivisor X} {U : Opens X}
    (h : X → ℂ) (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (f : divisorSections D U) (x : U) :
    (multiplySection h hh ho f).1 =ᶠ[𝓝[≠] x] fun y ↦ h y * f.1 y := by
  have ht : Tendsto (Subtype.val : U → X) (𝓝[≠] x) (𝓝[≠] (x : X)) :=
    continuous_subtype_val.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hy hxy ↦ hy (Subtype.ext hxy))
  filter_upwards [(normalizedProduct_eventuallyEq E (hh x x.2)
    (isDivisorSectionAt_extend f.property x).meromorphicAt).comp_tendsto ht] with y hy
  simpa [multiplySection, Subtype.val_injective.extend_apply] using hy

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem section_ext_nhdsNE {D : WeilDivisor X} {U : Opens X}
    {f g : divisorSections D U} (h : ∀ x : U, f.1 =ᶠ[𝓝[≠] x] g.1) : f = g := by
  apply Subtype.ext
  apply eq_of_eventuallyEq_codiscrete f.property g.property
  exact eventually_codiscrete_iff_forall_eventually_nhdsNE.2 h

private def multiplySectionLinearMap {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    divisorSections D U →ₗ[ℂ] divisorSections E U where
  toFun := multiplySection h hh ho
  map_add' f g := section_ext_nhdsNE fun x ↦ by
    filter_upwards [multiplySection_eventuallyEq h hh ho (f + g) x,
      multiplySection_eventuallyEq h hh ho f x,
      multiplySection_eventuallyEq h hh ho g x] with y hfg hf hg
    simp_all [mul_add]
  map_smul' c f := section_ext_nhdsNE fun x ↦ by
    filter_upwards [multiplySection_eventuallyEq h hh ho (c • f) x,
      multiplySection_eventuallyEq h hh ho f x] with y hcf hf
    simp_all [mul_left_comm]

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem inverse_order {D E : WeilDivisor X} {h : X → ℂ} {x : X}
    (ho : meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    meromorphicOrderAt h⁻¹ x = ((E x - D x : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_inv, ho]
  norm_cast
  ring

private def multiplySectionEquiv {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    divisorSections D U ≃ₗ[ℂ] divisorSections E U :=
  LinearEquiv.ofLinearMap (multiplySectionLinearMap h hh ho)
    (multiplySectionLinearMap h⁻¹ (fun x hx ↦ (hh x hx).inv)
      (fun x hx ↦ inverse_order (ho x hx)))
    (by
      ext f : 1
      apply section_ext_nhdsNE
      intro x
      have hn := (hh x x.2).eventually_ne_zero (by rw [ho x x.2]; exact WithTop.coe_ne_top)
      have ht : Tendsto (Subtype.val : U → X) (𝓝[≠] x) (𝓝[≠] (x : X)) :=
        continuous_subtype_val.continuousAt.continuousWithinAt.tendsto_nhdsWithin
          (fun _ hy hxy ↦ hy (Subtype.ext hxy))
      filter_upwards [multiplySection_eventuallyEq h hh ho _ x,
        multiplySection_eventuallyEq h⁻¹ (fun x hx ↦ (hh x hx).inv)
          (fun x hx ↦ inverse_order (ho x hx)) f x, ht.eventually hn] with y hy hy' hn
      -- The linear maps have the explicitly constructed section functions as their values.
      change (multiplySection h hh ho
        (multiplySection h⁻¹ (fun x hx ↦ (hh x hx).inv)
          (fun x hx ↦ inverse_order (ho x hx)) f)).1 y = f.1 y
      rw [hy, hy']
      exact mul_inv_cancel_left₀ hn _)
    (by
      ext f : 1
      apply section_ext_nhdsNE
      intro x
      have hn := (hh x x.2).eventually_ne_zero (by rw [ho x x.2]; exact WithTop.coe_ne_top)
      have ht : Tendsto (Subtype.val : U → X) (𝓝[≠] x) (𝓝[≠] (x : X)) :=
        continuous_subtype_val.continuousAt.continuousWithinAt.tendsto_nhdsWithin
          (fun _ hy hxy ↦ hy (Subtype.ext hxy))
      filter_upwards [multiplySection_eventuallyEq h⁻¹ (fun x hx ↦ (hh x hx).inv)
          (fun x hx ↦ inverse_order (ho x hx)) _ x,
        multiplySection_eventuallyEq h hh ho f x, ht.eventually hn] with y hy hy' hn
      -- The linear maps have the explicitly constructed section functions as their values.
      change (multiplySection h⁻¹ (fun x hx ↦ (hh x hx).inv)
        (fun x hx ↦ inverse_order (ho x hx)) (multiplySection h hh ho f)).1 y = f.1 y
      rw [hy, hy']
      exact inv_mul_cancel_left₀ hn _)

private def multiplyComponent {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    (divisorSheaf D).obj.obj (op U) ≅ (divisorSheaf E).obj.obj (op U) := by
  let e := (divisorSheafSectionsEquiv D U).trans
    ((multiplySectionEquiv h hh ho).trans (divisorSheafSectionsEquiv E U).symm)
  -- Use the actual categorical objects, rather than rebuilding them from their carriers.
  exact
    { hom := ModuleCat.homEquiv.symm e.toLinearMap
      inv := ModuleCat.homEquiv.symm e.symm.toLinearMap
      hom_inv_id := by ext f; exact e.symm_apply_apply f
      inv_hom_id := by ext f; exact e.apply_symm_apply f }

private theorem multiplyComponent_hom_apply {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (f : (divisorSheaf D).obj.obj (op U)) :
    divisorSheafSectionsEquiv E U ((multiplyComponent h hh ho).hom f) =
      multiplySection h hh ho (divisorSheafSectionsEquiv D U f) := by
  simp [multiplyComponent, LinearEquiv.trans_apply, ModuleCat.homEquiv,
    multiplySectionEquiv, multiplySectionLinearMap]

private theorem multiplyComponent_inv_apply {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (f : (divisorSheaf E).obj.obj (op U)) :
    divisorSheafSectionsEquiv D U ((multiplyComponent h hh ho).inv f) =
      multiplySection h⁻¹ (fun x hx ↦ (hh x hx).inv)
        (fun x hx ↦ inverse_order (ho x hx)) (divisorSheafSectionsEquiv E U f) := by
  simp [multiplyComponent, LinearEquiv.trans_apply, ModuleCat.homEquiv,
    multiplySectionEquiv, multiplySectionLinearMap]

/-- Multiplication by a meromorphic function whose order is the difference of two divisors
identifies their sheaves over an open set. Sections are normalized after multiplication. -/
def divisorSheafMulIso (D E : WeilDivisor X) (U : Opens X) (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    ((Opens.isOpenEmbedding (X := TopCat.of X) U).sheafPullback (ModuleCat.{u} ℂ)).obj
        (divisorSheaf D) ≅
      ((Opens.isOpenEmbedding (X := TopCat.of X) U).sheafPullback (ModuleCat.{u} ℂ)).obj
        (divisorSheaf E) := by
  have imageOpen_le (V : Opens ((Opens.toTopCat (TopCat.of X)).obj U)) :
      (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V ≤ U := by
    simpa only [Opens.isOpenEmbedding_obj_top] using
      ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map
        (homOfLE (le_top : V ≤ ⊤))).le
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun V ↦ multiplyComponent
    (U := (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V.unop) h
    (fun x hx ↦ hh x (imageOpen_le V.unop hx))
    (fun x hx ↦ ho x (imageOpen_le V.unop hx))) ?_
  intro V W i
  -- Naive pullback is precomposition with the image-open functor. Name the component
  -- isomorphisms on their original section carriers before applying their equations.
  change (divisorSheaf D).obj.map
      ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map i.unop).op ≫
      (multiplyComponent h (fun x hx ↦ hh x (imageOpen_le W.unop hx))
        (fun x hx ↦ ho x (imageOpen_le W.unop hx))).hom =
    (multiplyComponent h (fun x hx ↦ hh x (imageOpen_le V.unop hx))
      (fun x hx ↦ ho x (imageOpen_le V.unop hx))).hom ≫
      (divisorSheaf E).obj.map
        ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map i.unop).op
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (divisorSheafSectionsEquiv E
    ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj W.unop)).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [multiplyComponent_hom_apply]
  apply section_ext_nhdsNE
  intro x
  -- Both composites are sections over the smaller image open. Their punctured germs are
  -- multiplication by the same function; normalization determines the remaining values.
  let j := (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map i.unop
  have ht : Tendsto (Opens.inclusion j.le)
      (𝓝[≠] x) (𝓝[≠] (Opens.inclusion j.le x)) :=
    (continuous_inclusion _).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hy hxy ↦ hy (Set.inclusion_injective _ hxy))
  filter_upwards [multiplySection_eventuallyEq h _ _ _ x,
    (multiplySection_eventuallyEq h _ _ (divisorSheafSectionsEquiv D
      ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V.unop) f)
      (Opens.inclusion j.le x)).comp_tendsto ht]
    with y hy hy'
  have hres := congrFun (divisorSheafSectionsEquiv_map D
    ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.map i.unop) f) y
  rw [divisorSheafSectionsEquiv_map, multiplyComponent_hom_apply]
  exact hy.trans ((congrArg (h (y : X) * ·) hres).trans hy'.symm)

/-- The forward section map multiplies meromorphic representatives and then fills removable
singularities and sets the values at the target's allowed poles to zero. -/
theorem divisorSheafMulIso_hom_app {D E : WeilDivisor X} (U : Opens X) (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (V : Opens ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : (divisorSheaf D).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V))) :
    (divisorSheafSectionsEquiv E _
      ((divisorSheafMulIso D E U h hh ho).hom.hom.app (op V) f)).1 =
      fun y : (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V ↦
        if E y ≤ 0 then affineChart (sphereMap
        (h * Subtype.val.extend (divisorSheafSectionsEquiv D _ f).1 0) y) else 0 := by
  -- The pullback component is the original section isomorphism at the image open.
  change (divisorSheafSectionsEquiv E _ ((multiplyComponent h _ _).hom f)).1 = _
  rw [multiplyComponent_hom_apply]
  funext y
  simp [multiplySection, normalizedProduct, Set.indicator]

/-- The inverse section map uses multiplication by the reciprocal generator, with the same
normalization. In particular it fills removable values which a pointwise product would lose. -/
theorem divisorSheafMulIso_inv_app {D E : WeilDivisor X} (U : Opens X) (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (V : Opens ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : (divisorSheaf E).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V))) :
    (divisorSheafSectionsEquiv D _
      ((divisorSheafMulIso D E U h hh ho).inv.hom.app (op V) f)).1 =
      fun y : (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V ↦
        if D y ≤ 0 then affineChart (sphereMap
        (h⁻¹ * Subtype.val.extend (divisorSheafSectionsEquiv E _ f).1 0) y) else 0 := by
  -- The pullback component is the original inverse at the image open.
  change (divisorSheafSectionsEquiv D _ ((multiplyComponent h _ _).inv f)).1 = _
  rw [multiplyComponent_inv_apply]
  funext y
  simp [multiplySection, normalizedProduct, Set.indicator]

section Coordinate

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

/-- On a coordinate neighbourhood meeting the support of a divisor only at its centre,
the divisor sheaf is isomorphic to the holomorphic structure sheaf. The forward map multiplies
by the coordinate to the divisor's coefficient, filling removable singularities. -/
def divisorSheafCoordinateIso (D : WeilDivisor Y) (e : OpenPartialHomeomorph Y ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 Y) (x : Y) (U : Opens Y) (hx : x ∈ U)
    (hU : (U : Set Y) ⊆ e.source) (hD : ∀ y ∈ U, y ≠ x → D y = 0) :
    ((Opens.isOpenEmbedding (X := TopCat.of Y) U).sheafPullback (ModuleCat ℂ)).obj
        (divisorSheaf D) ≅
      ((Opens.isOpenEmbedding (X := TopCat.of Y) U).sheafPullback (ModuleCat ℂ)).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) Y) := by
  refine divisorSheafMulIso D 0 U (fun y ↦ (e y - e x) ^ D x)
    (fun y hy ↦ e.meromorphicAt_coordinate_zpow he (e x) (D x) (hU hy)) ?_ ≪≫
    ((Opens.isOpenEmbedding (X := TopCat.of Y) U).sheafPullback (ModuleCat ℂ)).mapIso
      (divisorSheafZeroIso Y)
  intro y hy
  rw [e.meromorphicOrderAt_coordinate_zpow he (e x) (D x) (hU hy)]
  by_cases hyx : y = x
  · simp [hyx]
  · have hne : e y ≠ e x := fun h ↦ hyx (e.injOn (hU hy) (hU hx) h)
    simp [hne, hD y hy hyx]

/-- The coordinate trivialization sends a divisor section to its coordinate-weighted
holomorphic representative, filling removable singularities. -/
theorem divisorSheafCoordinateIso_hom_app_apply (D : WeilDivisor Y)
    (e : OpenPartialHomeomorph Y ℂ) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (x : Y) (U : Opens Y) (hx : x ∈ U) (hU : (U : Set Y) ⊆ e.source)
    (hD : ∀ y ∈ U, y ≠ x → D y = 0)
    (V : Opens ((Opens.toTopCat (TopCat.of Y)).obj U))
    (f : (divisorSheaf D).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of Y) U).functor.obj V)))
    (y : (Opens.isOpenEmbedding (X := TopCat.of Y) U).functor.obj V) :
    holomorphicStructureSheafModules.sectionsLinearEquiv 𝓘(ℂ) Y
      (op ((Opens.isOpenEmbedding (X := TopCat.of Y) U).functor.obj V))
      ((divisorSheafCoordinateIso D e he x U hx hU hD).hom.hom.app (op V) f) y =
      affineChart (sphereMap
        ((fun z ↦ (e z - e x) ^ D x) *
          Subtype.val.extend (divisorSheafSectionsEquiv D _ f).1 0) y) := by
  -- The composite is the multiplication component followed by the existing zero-divisor
  -- identification; retain the native section carriers at this boundary.
  change holomorphicStructureSheafModules.sectionsLinearEquiv 𝓘(ℂ) Y _
    ((divisorSheafZeroIso Y).hom.hom.app _
      ((multiplyComponent (fun z ↦ (e z - e x) ^ D x) _ _).hom f)) y = _
  rw [holomorphicStructureSheafModules.sectionsLinearEquiv_apply,
    divisorSheafZeroIso_hom_app_apply, multiplyComponent_hom_apply]
  simp [multiplySection, normalizedProduct]

/-- The inverse coordinate trivialization multiplies a holomorphic section by the reciprocal
coordinate power, fills removable singularities, and normalizes values at allowed poles. -/
theorem divisorSheafCoordinateIso_inv_app (D : WeilDivisor Y)
    (e : OpenPartialHomeomorph Y ℂ) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (x : Y) (U : Opens Y) (hx : x ∈ U) (hU : (U : Set Y) ⊆ e.source)
    (hD : ∀ y ∈ U, y ≠ x → D y = 0)
    (V : Opens ((Opens.toTopCat (TopCat.of Y)).obj U))
    (f : (holomorphicStructureSheafModules 𝓘(ℂ) Y).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of Y) U).functor.obj V))) :
    (divisorSheafSectionsEquiv D _
      ((divisorSheafCoordinateIso D e he x U hx hU hD).inv.hom.app (op V) f)).1 =
      fun y : (Opens.isOpenEmbedding (X := TopCat.of Y) U).functor.obj V ↦
        if D y ≤ 0 then affineChart (sphereMap
          ((fun z ↦ ((e z - e x) ^ D x)⁻¹) * Subtype.val.extend (fun z ↦ f z) 0) y)
        else 0 := by
  -- The inverse first identifies holomorphic and zero-divisor sections on the same open.
  change (divisorSheafSectionsEquiv D _
    ((multiplyComponent (fun z ↦ (e z - e x) ^ D x) _ _).inv
      ((divisorSheafZeroIso Y).inv.hom.app _ f))).1 = _
  rw [multiplyComponent_inv_apply]
  funext y
  simp only [multiplySection, normalizedProduct, Function.comp_apply,
    divisorSheafZeroIso_inv_app_apply, Set.indicator_apply, mem_ofPred_eq]
  rfl

/-- Every point of a complex curve has a neighbourhood on which its divisor sheaf is
isomorphic to the holomorphic structure sheaf. No compactness or connectedness is required. -/
theorem exists_divisorSheaf_local_iso (D : WeilDivisor Y) (x : Y) :
    ∃ U : Opens Y, x ∈ U ∧ Nonempty
      (((Opens.isOpenEmbedding (X := TopCat.of Y) U).sheafPullback (ModuleCat ℂ)).obj
          (divisorSheaf D) ≅
        ((Opens.isOpenEmbedding (X := TopCat.of Y) U).sheafPullback (ModuleCat ℂ)).obj
          (holomorphicStructureSheafModules 𝓘(ℂ) Y)) := by
  classical
  have := ChartedSpace.t1Space ℂ Y
  let e := chartAt ℂ x
  let U : Opens Y := ⟨e.source \ (D.support.erase x : Set Y),
    e.open_source.sdiff (D.support.erase x).finite_toSet.isClosed⟩
  have hx : x ∈ U := ⟨mem_chart_source ℂ x, by simp⟩
  refine ⟨U, hx, ⟨divisorSheafCoordinateIso D e (chart_mem_maximalAtlas x)
    x U hx (fun _ hy ↦ hy.1) ?_⟩⟩
  intro y hy hyx
  by_contra h
  exact hy.2 (by simp [hyx, Finsupp.mem_support_iff.mpr h])

end Coordinate

end TauCeti.RiemannSurface
