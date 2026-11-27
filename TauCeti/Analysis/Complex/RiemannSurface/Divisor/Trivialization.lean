/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Normalize
public import TauCeti.Analysis.Complex.RiemannSurface.SphereMap
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Local trivializations of divisor sheaves

The sheaf of meromorphic functions with poles bounded by a divisor is locally isomorphic to
the holomorphic structure sheaf. In a coordinate neighbourhood meeting the divisor's support
only at its centre, multiplication by a power of the centered coordinate gives the
trivialization. These are isomorphisms of the actual sheaves, compatible with restriction to
arbitrary smaller opens, which need not be connected.

Multiplication by a function meromorphic on all of `X`, whose order at each point is the
difference `D - E` of two divisors, gives an isomorphism `divisorSheaf D ≅ divisorSheaf E` on
the whole surface (`divisorSheafGlobalMulIso`). It depends only on the punctured germs of the
multiplier, and is compatible with inverses and products of multipliers. This is used for the
invariance of divisor sheaves under linear equivalence. If the order of the multiplier is only
bounded below by `D - E`, multiplication is still a morphism `divisorSheaf D ⟶ divisorSheaf E`
(`divisorSheafGlobalMul`). It is additive in the multiplier, is `c` times the inclusion
`𝒪_D ⟶ 𝒪_E` for a constant multiplier `c`, and commutes with the inclusions of divisor sheaves.

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

private theorem isDivisorSectionAt_toDivisorSection_mul {D E : WeilDivisor X}
    {h f : X → ℂ} {x : X} (hh : MeromorphicAt h x)
    (ho : ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hf : IsDivisorSectionAt D f x) :
    IsDivisorSectionAt E (toDivisorSection E (h * f)) x := by
  refine isDivisorSectionAt_toDivisorSection (hh.mul hf.meromorphicAt) ?_
  rw [meromorphicOrderAt_mul hh hf.meromorphicAt]
  calc
    ((-E x : ℤ) : WithTop ℤ) =
        ((D x - E x : ℤ) : WithTop ℤ) + ((-D x : ℤ) : WithTop ℤ) := by
      norm_cast
      ring
    _ ≤ _ := add_le_add ho hf.neg_le_meromorphicOrderAt

private def multiplySection {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (f : divisorSections D U) : divisorSections E U :=
  ⟨toDivisorSection E (h * Subtype.val.extend f.val 0) ∘ Subtype.val,
    comp_val_mem_divisorSections fun x hx ↦ isDivisorSectionAt_toDivisorSection_mul
      (hh x hx) (ho x hx) (isDivisorSectionAt_extend f.property ⟨x, hx⟩)⟩

private theorem multiplySection_eventuallyEq {D E : WeilDivisor X} {U : Opens X}
    (h : X → ℂ) (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (f : divisorSections D U) (x : U) :
    (multiplySection h hh ho f).val =ᶠ[𝓝[≠] x] fun y ↦ h y * f.val y := by
  filter_upwards [(toDivisorSection_eventuallyEq E ((hh x x.property).mul
    (isDivisorSectionAt_extend f.property x).meromorphicAt)).comp_tendsto
      (tendsto_subtype_val_nhdsNE x)] with y hy
  simpa [multiplySection, Subtype.val_injective.extend_apply] using hy

private theorem section_ext_nhdsNE {D : WeilDivisor X} {U : Opens X}
    {f g : divisorSections D U} (h : ∀ x : U, f.val =ᶠ[𝓝[≠] x] g.val) : f = g := by
  apply Subtype.ext
  apply eq_of_eventuallyEq_codiscrete f.property g.property
  exact eventually_codiscrete_iff_forall_eventually_nhdsNE.2 h

private def multiplySectionLinearMap {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) :
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

private theorem inverse_order {D E : WeilDivisor X} {h : X → ℂ} {x : X}
    (ho : meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    ((E x - D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h⁻¹ x := by
  rw [meromorphicOrderAt_inv, ho]
  norm_cast
  linarith

/-- Multiplication by `h` on the sections of divisor sheaves over `U`, as a morphism of complex
vector spaces. -/
private def multiplyHom {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) :
    (divisorSheaf D).obj.obj (op U) ⟶ (divisorSheaf E).obj.obj (op U) :=
  -- Use the actual categorical objects, rather than rebuilding them from their carriers.
  ModuleCat.homEquiv.symm ((divisorSheafSectionsEquiv E U).symm.toLinearMap ∘ₗ
    multiplySectionLinearMap h hh ho ∘ₗ (divisorSheafSectionsEquiv D U).toLinearMap)

private theorem multiplyHom_apply {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (f : (divisorSheaf D).obj.obj (op U)) :
    divisorSheafSectionsEquiv E U (multiplyHom h hh ho f) =
      multiplySection h hh ho (divisorSheafSectionsEquiv D U f) := by
  simp [multiplyHom, ModuleCat.homEquiv, multiplySectionLinearMap]

private theorem multiplyHom_apply_val {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (f : (divisorSheaf D).obj.obj (op U)) :
    (divisorSheafSectionsEquiv E U (multiplyHom h hh ho f)).val =
      fun y : U ↦ if E y ≤ 0 then affineChart (sphereMap
        (h * Subtype.val.extend (divisorSheafSectionsEquiv D U f).val 0) y) else 0 := by
  rw [multiplyHom_apply]
  funext y
  simp [multiplySection, toDivisorSection_apply]

/-- The multiplication morphisms commute with restriction along an inclusion of opens. -/
private theorem multiplyHom_naturality {D E : WeilDivisor X} {V W : Opens X}
    (i : W ⟶ V) (h : X → ℂ) (hhV : ∀ x ∈ V, MeromorphicAt h x)
    (hoV : ∀ x ∈ V, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hhW : ∀ x ∈ W, MeromorphicAt h x)
    (hoW : ∀ x ∈ W, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) :
    (divisorSheaf D).obj.map i.op ≫ multiplyHom h hhW hoW =
      multiplyHom h hhV hoV ≫ (divisorSheaf E).obj.map i.op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (divisorSheafSectionsEquiv E W).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [multiplyHom_apply]
  apply section_ext_nhdsNE
  intro x
  -- Both composites are sections over the smaller open. Their punctured germs are
  -- multiplication by the same function; normalization determines the remaining values.
  have ht : Tendsto (Opens.inclusion i.le) (𝓝[≠] x) (𝓝[≠] (Opens.inclusion i.le x)) :=
    (continuous_inclusion _).continuousAt.tendsto_nhdsNE (Set.inclusion_injective _)
  filter_upwards [multiplySection_eventuallyEq h _ _ _ x,
    (multiplySection_eventuallyEq h _ _ (divisorSheafSectionsEquiv D V f)
      (Opens.inclusion i.le x)).comp_tendsto ht] with y hy hy'
  have hres := congrFun (divisorSheafSectionsEquiv_map D i f) y
  rw [divisorSheafSectionsEquiv_map, multiplyHom_apply]
  exact hy.trans ((congrArg (h (y : X) * ·) hres).trans hy'.symm)

/-- Multiplication by `k` undoes multiplication by `h` if `k h = 1` on punctured
neighbourhoods. -/
private theorem multiplyHom_comp_multiplyHom {D E : WeilDivisor X} {U : Opens X} {h k : X → ℂ}
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hk : ∀ x ∈ U, MeromorphicAt k x)
    (hok : ∀ x ∈ U, ((E x - D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt k x)
    (hkh : ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, k y * h y = 1) :
    multiplyHom h hh ho ≫ multiplyHom k hk hok = 𝟙 _ := by
  ext f
  apply (divisorSheafSectionsEquiv D U).injective
  rw [ConcreteCategory.comp_apply, ModuleCat.id_apply, multiplyHom_apply, multiplyHom_apply]
  apply section_ext_nhdsNE
  intro x
  filter_upwards [multiplySection_eventuallyEq k hk hok _ x,
    multiplySection_eventuallyEq h hh ho _ x,
    (tendsto_subtype_val_nhdsNE x).eventually (hkh x x.property)] with y hy hy' hkh
  rw [hy, hy', ← mul_assoc, hkh, one_mul]

private def multiplyComponent {D E : WeilDivisor X} {U : Opens X} (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    (divisorSheaf D).obj.obj (op U) ≅ (divisorSheaf E).obj.obj (op U) where
  hom := multiplyHom h hh fun x hx ↦ (ho x hx).ge
  inv := multiplyHom h⁻¹ (fun x hx ↦ (hh x hx).inv) fun x hx ↦ inverse_order (ho x hx)
  hom_inv_id := multiplyHom_comp_multiplyHom _ _ _ _ fun x hx ↦ by
    filter_upwards [(hh x hx).eventually_ne_zero (by rw [ho x hx]; exact WithTop.coe_ne_top)]
      with y hy
    exact inv_mul_cancel₀ hy
  inv_hom_id := multiplyHom_comp_multiplyHom _ _ _ _ fun x hx ↦ by
    filter_upwards [(hh x hx).eventually_ne_zero (by rw [ho x hx]; exact WithTop.coe_ne_top)]
      with y hy
    exact mul_inv_cancel₀ hy


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
  exact multiplyHom_naturality _ h _ _ _ _

/-- The forward section map multiplies meromorphic representatives and then fills removable
singularities and sets the values at the target's allowed poles to zero. -/
theorem divisorSheafMulIso_hom_app {D E : WeilDivisor X} (U : Opens X) (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (V : Opens ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : (divisorSheaf D).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V))) :
    (divisorSheafSectionsEquiv E _
      ((divisorSheafMulIso D E U h hh ho).hom.hom.app (op V) f)).val =
      fun y : (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V ↦
        if E y ≤ 0 then affineChart (sphereMap
        (h * Subtype.val.extend (divisorSheafSectionsEquiv D _ f).val 0) y) else 0 := by
  -- The pullback component is the multiplication component at the image open.
  exact multiplyHom_apply_val h _ _ f

/-- The inverse section map uses multiplication by the reciprocal generator, with the same
normalization. In particular it fills removable values which a pointwise product would lose. -/
theorem divisorSheafMulIso_inv_app {D E : WeilDivisor X} (U : Opens X) (h : X → ℂ)
    (hh : ∀ x ∈ U, MeromorphicAt h x)
    (ho : ∀ x ∈ U, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (V : Opens ((Opens.toTopCat (TopCat.of X)).obj U))
    (f : (divisorSheaf E).obj.obj
      (op ((Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V))) :
    (divisorSheafSectionsEquiv D _
      ((divisorSheafMulIso D E U h hh ho).inv.hom.app (op V) f)).val =
      fun y : (Opens.isOpenEmbedding (X := TopCat.of X) U).functor.obj V ↦
        if D y ≤ 0 then affineChart (sphereMap
        (h⁻¹ * Subtype.val.extend (divisorSheafSectionsEquiv E _ f).val 0) y) else 0 := by
  -- The pullback component is the multiplication component at the image open.
  exact multiplyHom_apply_val h⁻¹ _ _ f

/-- Two morphisms between the presheaves underlying divisor sheaves are equal if, for every
section, their values agree on a punctured neighbourhood of each point. -/
private theorem divisorPresheaf_hom_ext_nhdsNE {D E : WeilDivisor X}
    {φ ψ : (divisorSheaf D).obj ⟶ (divisorSheaf E).obj}
    (h : ∀ (U : Opens X) (f : (divisorSheaf D).obj.obj (op U)) (x : U),
      (divisorSheafSectionsEquiv E U (φ.app (op U) f)).val =ᶠ[𝓝[≠] x]
        (divisorSheafSectionsEquiv E U (ψ.app (op U) f)).val) :
    φ = ψ := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (divisorSheafSectionsEquiv E U.unop).injective
  exact section_ext_nhdsNE (h U.unop f)

/-- Two morphisms of divisor sheaves are equal if, for every section, their values agree on a
punctured neighbourhood of each point. -/
private theorem divisorSheaf_hom_ext_nhdsNE {D E : WeilDivisor X}
    {φ ψ : divisorSheaf D ⟶ divisorSheaf E}
    (h : ∀ (U : Opens X) (f : (divisorSheaf D).obj.obj (op U)) (x : U),
      (divisorSheafSectionsEquiv E U (φ.hom.app (op U) f)).val =ᶠ[𝓝[≠] x]
        (divisorSheafSectionsEquiv E U (ψ.hom.app (op U) f)).val) :
    φ = ψ :=
  Sheaf.hom_ext (divisorPresheaf_hom_ext_nhdsNE h)

/-! ### Multiplication morphisms -/

/-- A constant multiplier satisfies the order bound `D - E` of a multiplication `𝒪_D ⟶ 𝒪_E`
when `D ≤ E`. -/
theorem sub_le_meromorphicOrderAt_const {D E : WeilDivisor X} (hDE : D ≤ E) (c : ℂ) (x : X) :
    ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun _ ↦ c) x := by
  classical
  rw [meromorphicOrderAt_const]
  split_ifs
  · exact le_top
  · exact_mod_cast sub_nonpos.2 (hDE x)

/-- Order bounds of multipliers add up along products: if `h` and `k` satisfy the bounds `D - E`
and `E - F` at `x`, then `h * k` satisfies the bound `D - F`. -/
theorem sub_le_meromorphicOrderAt_mul {D E F : WeilDivisor X} {h k : X → ℂ} {x : X}
    (hh : MeromorphicAt h x) (hk : MeromorphicAt k x)
    (ho : ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hok : ((E x - F x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt k x) :
    ((D x - F x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (h * k) x := by
  rw [meromorphicOrderAt_mul hh hk, ← sub_add_sub_cancel (D x) (E x) (F x), WithTop.coe_add]
  exact add_le_add ho hok

/-- **Multiplication by a meromorphic function as a morphism `𝒪_D ⟶ 𝒪_E`.** If `h` is meromorphic
at every point and its order at each point is at least the difference of the coefficients of `D`
and `E`, multiplication by `h` sends sections of `𝒪_D` to sections of `𝒪_E`. Sections are
normalized after multiplication. Unlike for `divisorSheafGlobalMulIso`, the order of `h` may
exceed `D - E`, and `h` may be zero. -/
def divisorSheafGlobalMul (D E : WeilDivisor X) (h : X → ℂ) (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) :
    divisorSheaf D ⟶ divisorSheaf E where
  hom.app U := multiplyHom (U := U.unop) h (fun x _ ↦ hh x) fun x _ ↦ ho x
  hom.naturality _ _ i := multiplyHom_naturality i.unop h _ _ _ _

/-- The sheaf components of `divisorSheafGlobalMul` are the multiplication morphisms. -/
private theorem divisorSheafGlobalMul_hom_app_eq {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) (U : Opens X) :
    (divisorSheafGlobalMul D E h hh ho).hom.app (op U) =
      multiplyHom h (fun x _ ↦ hh x) fun x _ ↦ ho x :=
  rfl

/-- The section map of `divisorSheafGlobalMul` multiplies meromorphic representatives, fills
removable singularities and sets the values at the target's allowed poles to zero. -/
theorem divisorSheafGlobalMul_hom_app {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) (U : Opens X)
    (f : (divisorSheaf D).obj.obj (op U)) :
    (divisorSheafSectionsEquiv E U ((divisorSheafGlobalMul D E h hh ho).hom.app (op U) f)).val =
      fun y : U ↦ if E y ≤ 0 then affineChart (sphereMap
        (h * Subtype.val.extend (divisorSheafSectionsEquiv D U f).val 0) y) else 0 := by
  rw [divisorSheafGlobalMul_hom_app_eq]
  exact multiplyHom_apply_val h _ _ f

/-- On a punctured neighbourhood of each point, the section map of `divisorSheafGlobalMul` is
pointwise multiplication by `h`. -/
theorem divisorSheafGlobalMul_hom_app_eventuallyEq {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) (U : Opens X)
    (f : (divisorSheaf D).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv E U ((divisorSheafGlobalMul D E h hh ho).hom.app (op U) f)).val
      =ᶠ[𝓝[≠] x] fun y ↦ h y * (divisorSheafSectionsEquiv D U f).val y := by
  rw [divisorSheafGlobalMul_hom_app_eq, multiplyHom_apply]
  exact multiplySection_eventuallyEq h _ _ _ x

/-- `divisorSheafGlobalMul` depends only on the punctured germs of the multiplier. -/
theorem divisorSheafGlobalMul_congr {D E : WeilDivisor X} {h k : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hk : ∀ x, MeromorphicAt k x)
    (hok : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt k x)
    (heq : ∀ x, h =ᶠ[𝓝[≠] x] k) :
    divisorSheafGlobalMul D E h hh ho = divisorSheafGlobalMul D E k hk hok := by
  refine divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_
  filter_upwards [divisorSheafGlobalMul_hom_app_eventuallyEq h hh ho U f x,
    divisorSheafGlobalMul_hom_app_eventuallyEq k hk hok U f x,
    (tendsto_subtype_val_nhdsNE x).eventually (heq x)] with y hy hy' hhk
  rw [hy, hy', hhk]

/-- **Composition.** Multiplying by `h` and then by `k` is multiplication by `h * k`. -/
@[reassoc (attr := simp)]
theorem divisorSheafGlobalMul_comp {D E F : WeilDivisor X} {h k : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hk : ∀ x, MeromorphicAt k x)
    (hok : ∀ x, ((E x - F x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt k x) :
    divisorSheafGlobalMul D E h hh ho ≫ divisorSheafGlobalMul E F k hk hok =
      divisorSheafGlobalMul D F (h * k) (fun x ↦ (hh x).mul (hk x))
        fun x ↦ sub_le_meromorphicOrderAt_mul (hh x) (hk x) (ho x) (hok x) := by
  refine divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_
  rw [TopCat.Sheaf.comp_app, ConcreteCategory.comp_apply]
  filter_upwards [divisorSheafGlobalMul_hom_app_eventuallyEq k hk hok U _ x,
    divisorSheafGlobalMul_hom_app_eventuallyEq h hh ho U f x,
    divisorSheafGlobalMul_hom_app_eventuallyEq (h * k) _ _ U f x] with y hy hy' hy''
  rw [hy, hy', hy'', Pi.mul_apply]
  ring

/-- Multiplication by a function meromorphic at every point, whose order at each point is the
difference of the coefficients of two divisors, identifies their sheaves on the whole surface.
Sections are normalized after multiplication. Unlike `divisorSheafMulIso`, no open subset or
pullback is involved, so the isomorphism can be pushed through any functor of sheaves on `X`. -/
def divisorSheafGlobalMulIso (D E : WeilDivisor X) (h : X → ℂ) (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    divisorSheaf D ≅ divisorSheaf E := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun V ↦ multiplyComponent (U := V.unop) h
    (fun x _ ↦ hh x) (fun x _ ↦ ho x)) ?_
  intro V W i
  exact multiplyHom_naturality i.unop h _ _ _ _

/-- The forward map of `divisorSheafGlobalMulIso` is the multiplication morphism. -/
theorem divisorSheafGlobalMulIso_hom {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) :
    (divisorSheafGlobalMulIso D E h hh ho).hom =
      divisorSheafGlobalMul D E h hh fun x ↦ (ho x).ge := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- The inverse sheaf components of `divisorSheafGlobalMulIso` are multiplication by the
reciprocal of the generator. -/
private theorem divisorSheafGlobalMulIso_inv_hom_app {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) (U : Opens X) :
    (divisorSheafGlobalMulIso D E h hh ho).inv.hom.app (op U) =
      multiplyHom h⁻¹ (fun x _ ↦ (hh x).inv) fun x _ ↦ inverse_order (ho x) :=
  rfl

/-- The forward section map of `divisorSheafGlobalMulIso` multiplies meromorphic
representatives, fills removable singularities and sets the values at the target's allowed
poles to zero. -/
theorem divisorSheafGlobalMulIso_hom_app {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) (U : Opens X)
    (f : (divisorSheaf D).obj.obj (op U)) :
    (divisorSheafSectionsEquiv E U
      ((divisorSheafGlobalMulIso D E h hh ho).hom.hom.app (op U) f)).val =
      fun y : U ↦ if E y ≤ 0 then affineChart (sphereMap
        (h * Subtype.val.extend (divisorSheafSectionsEquiv D U f).val 0) y) else 0 := by
  rw [divisorSheafGlobalMulIso_hom]
  exact divisorSheafGlobalMul_hom_app h hh _ U f

/-- The inverse section map of `divisorSheafGlobalMulIso` multiplies by the reciprocal of the
generator, with the same normalization. -/
theorem divisorSheafGlobalMulIso_inv_app {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) (U : Opens X)
    (f : (divisorSheaf E).obj.obj (op U)) :
    (divisorSheafSectionsEquiv D U
      ((divisorSheafGlobalMulIso D E h hh ho).inv.hom.app (op U) f)).val =
      fun y : U ↦ if D y ≤ 0 then affineChart (sphereMap
        (h⁻¹ * Subtype.val.extend (divisorSheafSectionsEquiv E U f).val 0) y) else 0 := by
  rw [divisorSheafGlobalMulIso_inv_hom_app]
  exact multiplyHom_apply_val h⁻¹ _ _ f

/-- On a punctured neighbourhood of each point, the forward section map of
`divisorSheafGlobalMulIso` is pointwise multiplication by the generator. -/
theorem divisorSheafGlobalMulIso_hom_app_eventuallyEq {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) (U : Opens X)
    (f : (divisorSheaf D).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv E U
        ((divisorSheafGlobalMulIso D E h hh ho).hom.hom.app (op U) f)).val =ᶠ[𝓝[≠] x]
      fun y ↦ h y * (divisorSheafSectionsEquiv D U f).val y := by
  rw [divisorSheafGlobalMulIso_hom]
  exact divisorSheafGlobalMul_hom_app_eventuallyEq h hh _ U f x

/-- On a punctured neighbourhood of each point, the inverse section map of
`divisorSheafGlobalMulIso` is pointwise multiplication by the reciprocal of the generator. -/
theorem divisorSheafGlobalMulIso_inv_app_eventuallyEq {D E : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ)) (U : Opens X)
    (f : (divisorSheaf E).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv D U
        ((divisorSheafGlobalMulIso D E h hh ho).inv.hom.app (op U) f)).val =ᶠ[𝓝[≠] x]
      fun y ↦ (h y)⁻¹ * (divisorSheafSectionsEquiv E U f).val y := by
  rw [divisorSheafGlobalMulIso_inv_hom_app, multiplyHom_apply]
  exact multiplySection_eventuallyEq h⁻¹ _ _ _ x

/-- `divisorSheafGlobalMulIso` depends only on the punctured germs of its generator. -/
theorem divisorSheafGlobalMulIso_congr {D E : WeilDivisor X} {h k : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (hk : ∀ x, MeromorphicAt k x)
    (hok : ∀ x, meromorphicOrderAt k x = ((D x - E x : ℤ) : WithTop ℤ))
    (heq : ∀ x, h =ᶠ[𝓝[≠] x] k) :
    divisorSheafGlobalMulIso D E h hh ho = divisorSheafGlobalMulIso D E k hk hok := by
  refine Iso.ext ?_
  rw [divisorSheafGlobalMulIso_hom, divisorSheafGlobalMulIso_hom]
  exact divisorSheafGlobalMul_congr _ _ _ _ heq

/-- Multiplication by a generator which is `1` on punctured neighbourhoods is the identity of
the divisor sheaf. -/
theorem divisorSheafGlobalMulIso_eq_refl {D : WeilDivisor X} {h : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - D x : ℤ) : WithTop ℤ))
    (h₁ : ∀ x, h =ᶠ[𝓝[≠] x] 1) :
    divisorSheafGlobalMulIso D D h hh ho = Iso.refl _ := by
  refine Iso.ext (divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_)
  filter_upwards [divisorSheafGlobalMulIso_hom_app_eventuallyEq h hh ho U f x,
    (tendsto_subtype_val_nhdsNE x).eventually (h₁ x)] with y hy hy₁
  simp [hy, hy₁]

/-- The inverse of multiplication by `h` is multiplication by any generator which agrees with
`h⁻¹` on punctured neighbourhoods. -/
theorem divisorSheafGlobalMulIso_symm {D E : WeilDivisor X} {h k : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (hk : ∀ x, MeromorphicAt k x)
    (hok : ∀ x, meromorphicOrderAt k x = ((E x - D x : ℤ) : WithTop ℤ))
    (heq : ∀ x, k =ᶠ[𝓝[≠] x] h⁻¹) :
    (divisorSheafGlobalMulIso D E h hh ho).symm = divisorSheafGlobalMulIso E D k hk hok := by
  refine Iso.ext (divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_)
  filter_upwards [divisorSheafGlobalMulIso_inv_app_eventuallyEq h hh ho U f x,
    divisorSheafGlobalMulIso_hom_app_eventuallyEq k hk hok U f x,
    (tendsto_subtype_val_nhdsNE x).eventually (heq x)] with y hy hy' hkh
  rw [Iso.symm_hom, hy, hy', hkh, Pi.inv_apply]

/-- Composing multiplication by `h` and by `g` is multiplication by any generator which agrees
with `h * g` on punctured neighbourhoods. -/
theorem divisorSheafGlobalMulIso_trans {D E F : WeilDivisor X} {h g k : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, meromorphicOrderAt h x = ((D x - E x : ℤ) : WithTop ℤ))
    (hg : ∀ x, MeromorphicAt g x)
    (hog : ∀ x, meromorphicOrderAt g x = ((E x - F x : ℤ) : WithTop ℤ))
    (hk : ∀ x, MeromorphicAt k x)
    (hok : ∀ x, meromorphicOrderAt k x = ((D x - F x : ℤ) : WithTop ℤ))
    (heq : ∀ x, k =ᶠ[𝓝[≠] x] h * g) :
    divisorSheafGlobalMulIso D E h hh ho ≪≫ divisorSheafGlobalMulIso E F g hg hog =
      divisorSheafGlobalMulIso D F k hk hok := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, divisorSheafGlobalMulIso_hom, divisorSheafGlobalMulIso_hom,
    divisorSheafGlobalMulIso_hom, divisorSheafGlobalMul_comp]
  exact divisorSheafGlobalMul_congr _ _ _ _ fun x ↦ (heq x).symm

/-- **Additivity in the multiplier.** The multiplication morphisms by `h` and by `k` add up to
the multiplication morphism by `h + k`. -/
theorem divisorSheafGlobalMul_add {D E : WeilDivisor X} {h k : X → ℂ}
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x)
    (hk : ∀ x, MeromorphicAt k x)
    (hok : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt k x) :
    divisorSheafGlobalMul D E (h + k) (fun x ↦ (hh x).add (hk x))
        (fun x ↦ (le_min (ho x) (hok x)).trans (meromorphicOrderAt_add (hk x))) =
      divisorSheafGlobalMul D E h hh ho + divisorSheafGlobalMul D E k hk hok := by
  refine divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_
  filter_upwards [divisorSheafGlobalMul_hom_app_eventuallyEq h hh ho U f x,
    divisorSheafGlobalMul_hom_app_eventuallyEq k hk hok U f x,
    divisorSheafGlobalMul_hom_app_eventuallyEq (h + k) _ _ U f x] with y hy hy' hy''
  simp only [Sheaf.Hom.add_app, ModuleCat.hom_add, LinearMap.add_apply, map_add,
    Submodule.coe_add, Pi.add_apply]
  rw [hy'', hy, hy', Pi.add_apply, add_mul]

/-- **Constant multipliers.** For `D ≤ E`, multiplication by a constant `c` is `c` times the
inclusion `𝒪_D ⟶ 𝒪_E`. The scalar multiple is taken in the `ℂ`-linear category of presheaves. -/
theorem divisorSheafGlobalMul_const_hom {D E : WeilDivisor X} (hDE : D ≤ E) (c : ℂ) :
    (divisorSheafGlobalMul D E (fun _ ↦ c) (fun x ↦ meromorphicAt_const c x)
      (sub_le_meromorphicOrderAt_const hDE c)).hom = c • (divisorSheafMapOfLE hDE).hom := by
  refine divisorPresheaf_hom_ext_nhdsNE fun U f x ↦ ?_
  filter_upwards [divisorSheafGlobalMul_hom_app_eventuallyEq _ _ _ U f x,
    divisorSheafMapOfLE_app_eventuallyEq hDE U f x] with y hy hy'
  simp only [NatTrans.app_smul, ModuleCat.hom_smul, LinearMap.smul_apply, map_smul,
    Submodule.coe_smul, Pi.smul_apply]
  rw [hy, hy', smul_eq_mul]

/-- Multiplication morphisms commute with the inclusions of divisor sheaves in the source:
restricting multiplication by `h` along `𝒪_D ⟶ 𝒪_{D'}` is multiplication by `h` on `𝒪_D`. -/
@[reassoc (attr := simp)]
theorem divisorSheafMapOfLE_comp_divisorSheafGlobalMul {D D' E : WeilDivisor X} (hDD' : D ≤ D')
    (h : X → ℂ) (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D' x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) :
    divisorSheafMapOfLE hDD' ≫ divisorSheafGlobalMul D' E h hh ho =
      divisorSheafGlobalMul D E h hh
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_right (hDD' x) _)).trans (ho x)) := by
  refine divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_
  rw [TopCat.Sheaf.comp_app, ConcreteCategory.comp_apply]
  filter_upwards [divisorSheafGlobalMul_hom_app_eventuallyEq h hh ho U _ x,
    divisorSheafMapOfLE_app_eventuallyEq hDD' U f x,
    divisorSheafGlobalMul_hom_app_eventuallyEq h hh _ U f x] with y hy hy' hy''
  rw [hy, hy', hy'']

/-- Multiplication morphisms commute with the inclusions of divisor sheaves in the target:
following multiplication by `h` with `𝒪_E ⟶ 𝒪_{E'}` is multiplication by `h` into `𝒪_{E'}`. -/
@[reassoc (attr := simp)]
theorem divisorSheafGlobalMul_comp_divisorSheafMapOfLE {D E E' : WeilDivisor X} (h : X → ℂ)
    (hh : ∀ x, MeromorphicAt h x)
    (ho : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt h x) (hEE' : E ≤ E') :
    divisorSheafGlobalMul D E h hh ho ≫ divisorSheafMapOfLE hEE' =
      divisorSheafGlobalMul D E' h hh
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_left (hEE' x) _)).trans (ho x)) := by
  refine divisorSheaf_hom_ext_nhdsNE fun U f x ↦ ?_
  rw [TopCat.Sheaf.comp_app, ConcreteCategory.comp_apply]
  filter_upwards [divisorSheafMapOfLE_app_eventuallyEq hEE' U _ x,
    divisorSheafGlobalMul_hom_app_eventuallyEq h hh ho U f x,
    divisorSheafGlobalMul_hom_app_eventuallyEq h hh _ U f x] with y hy hy' hy''
  rw [hy, hy', hy'']

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
          Subtype.val.extend (divisorSheafSectionsEquiv D _ f).val 0) y) := by
  -- The composite is the multiplication component followed by the existing zero-divisor
  -- identification; retain the native section carriers at this boundary.
  change holomorphicStructureSheafModules.sectionsLinearEquiv 𝓘(ℂ) Y _
    ((divisorSheafZeroIso Y).hom.hom.app _
      (multiplyHom (fun z ↦ (e z - e x) ^ D x) _ _ f)) y = _
  rw [holomorphicStructureSheafModules.sectionsLinearEquiv_apply,
    divisorSheafZeroIso_hom_app_apply, multiplyHom_apply]
  simp [multiplySection, toDivisorSection_apply]

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
      ((divisorSheafCoordinateIso D e he x U hx hU hD).inv.hom.app (op V) f)).val =
      fun y : (Opens.isOpenEmbedding (X := TopCat.of Y) U).functor.obj V ↦
        if D y ≤ 0 then affineChart (sphereMap
          ((fun z ↦ ((e z - e x) ^ D x)⁻¹) * Subtype.val.extend (fun z ↦ f z) 0) y)
        else 0 := by
  -- The inverse first identifies holomorphic and zero-divisor sections on the same open.
  change (divisorSheafSectionsEquiv D _
    (multiplyHom (fun z ↦ (e z - e x) ^ D x)⁻¹ _ _
      ((divisorSheafZeroIso Y).inv.hom.app _ f))).val = _
  rw [multiplyHom_apply]
  funext y
  simp only [multiplySection, toDivisorSection_apply, Function.comp_apply,
    divisorSheafZeroIso_inv_app_apply]
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
