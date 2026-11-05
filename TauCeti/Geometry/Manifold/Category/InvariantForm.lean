/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed

/-!
# Invariant forms on smooth presentations

For a quiver with smooth source and target on its total arrow manifold, invariant forms are the
forms on objects satisfying `s*ω = t*ω`. They are closed under exterior differentiation and wedge
products. The object and arrow manifolds may have different models; neither properness nor
étaleness is needed for these operations.

A prefunctor smooth on objects and total arrows pulls invariant forms back to invariant forms.
These pullbacks commute with differentiation, reverse composition, and agree for object maps joined
by a smooth family of connecting arrows. In particular this applies to functors joined by a smooth
natural transformation, not just a natural isomorphism. On groupoids it gives the
2-isomorphism invariance needed to compare pullbacks through presentation refinements.

The categorical and manifold carriers are unchanged. In particular no arrows, including
ineffective isotropy, are discarded, and no descent to the coarse space is asserted.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti.Quiver

variable {E H A K C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [Quiver C] [TopologicalSpace C] [TopologicalSpace (_root_.Quiver.Total C)]
  [ChartedSpace H C] [ChartedSpace K (_root_.Quiver.Total C)]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ A K)
  [IsManifold I ∞ C] [IsManifold J ∞ (_root_.Quiver.Total C)]
  (hs : ContMDiff J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C))
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ)

/-- The smooth forms on objects whose source and target pullbacks agree on total arrows. -/
def invariantForms : Submodule ℝ (SmoothForm I C V k) :=
  LinearMap.eqLocus (SmoothForm.mpullback _ hs) (SmoothForm.mpullback _ ht)

variable {I J hs ht V k}

/-- Invariance is equality of the source and target pullbacks. -/
@[simp]
theorem mem_invariantForms_iff {φ : SmoothForm I C V k} :
    φ ∈ invariantForms I J hs ht V k ↔
      SmoothForm.mpullback _ hs φ = SmoothForm.mpullback _ ht φ :=
  LinearMap.mem_eqLocus

/-- The exterior derivative of an invariant form is invariant. -/
theorem mextDerivₗ_mem_invariantForms {φ : SmoothForm I C V k}
    (hφ : φ ∈ invariantForms I J hs ht V k) :
    mextDerivₗ I k φ ∈ invariantForms I J hs ht V (k + 1) := by
  rw [mem_invariantForms_iff] at hφ ⊢
  rw [← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback, hφ]

variable (I J hs ht V k) in
/-- Exterior differentiation restricted to invariant forms. -/
def invariantForms.mextDerivₗ :
    invariantForms I J hs ht V k →ₗ[ℝ] invariantForms I J hs ht V (k + 1) :=
  (TauCeti.mextDerivₗ I k).restrict fun _ ↦ mextDerivₗ_mem_invariantForms

/-- Differentiation of invariant forms is the ordinary exterior derivative on objects. -/
@[simp]
theorem invariantForms.coe_mextDerivₗ (φ : invariantForms I J hs ht V k) :
    (invariantForms.mextDerivₗ I J hs ht V k φ : SmoothForm I C V (k + 1)) =
      TauCeti.mextDerivₗ I k φ := (rfl)

variable (I J hs ht V k) in
/-- The exterior derivative on invariant forms squares to zero. -/
@[simp]
theorem invariantForms.mextDerivₗ_comp_mextDerivₗ :
    (invariantForms.mextDerivₗ I J hs ht V (k + 1)).comp
      (invariantForms.mextDerivₗ I J hs ht V k) = 0 := by
  ext φ : 1
  exact Subtype.ext (LinearMap.congr_fun (TauCeti.mextDerivₗ_comp_mextDerivₗ I k) φ.1)

/-- Wedge products, with any continuous bilinear coefficient pairing, preserve invariance. -/
theorem wedgeWith_mem_invariantForms {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁]
    [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃) {l : ℕ}
    {φ : SmoothForm I C V₁ k} {η : SmoothForm I C V₂ l}
    (hφ : φ ∈ invariantForms I J hs ht V₁ k)
    (hη : η ∈ invariantForms I J hs ht V₂ l) :
    SmoothForm.wedgeWith μ φ η ∈ invariantForms I J hs ht V₃ (k + l) := by
  rw [mem_invariantForms_iff] at hφ hη ⊢
  rw [SmoothForm.mpullback_wedgeWith, SmoothForm.mpullback_wedgeWith, hφ, hη]

/-- Wedge products of invariant real-valued forms are invariant. -/
theorem wedge_mem_invariantForms {l : ℕ} {φ : SmoothForm I C ℝ k}
    {η : SmoothForm I C ℝ l} (hφ : φ ∈ invariantForms I J hs ht ℝ k)
    (hη : η ∈ invariantForms I J hs ht ℝ l) :
    SmoothForm.wedge φ η ∈ invariantForms I J hs ht ℝ (k + l) := by
  rw [SmoothForm.wedge_def]
  exact wedgeWith_mem_invariantForms _ hφ hη

end TauCeti.Quiver

namespace Prefunctor

variable {E H A K E' H' A' K' C D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']
  [Quiver C] [Quiver D] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
  [ChartedSpace H C] [ChartedSpace K (Quiver.Total C)]
  [ChartedSpace H' D] [ChartedSpace K' (Quiver.Total D)]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ A K}
  {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ A' K'}
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]
  {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

open TauCeti

/-- A prefunctor smooth on objects and total arrows pulls back invariant forms. -/
theorem mpullback_mem_invariantForms (Φ : C ⥤q D) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal) {φ : SmoothForm I' D V k}
    (hφ : φ ∈ TauCeti.Quiver.invariantForms I' J' hs' ht' V k) :
    SmoothForm.mpullback Φ.obj hΦ φ ∈ TauCeti.Quiver.invariantForms I J hs ht V k := by
  rw [TauCeti.Quiver.mem_invariantForms_iff] at hφ ⊢
  -- The two composites are equal because a prefunctor preserves the endpoints of each arrow.
  calc
    _ = SmoothForm.mpullback _ hΦ₁ (SmoothForm.mpullback _ hs' φ) := by
      rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
      rfl
    _ = SmoothForm.mpullback _ hΦ₁ (SmoothForm.mpullback _ ht' φ) := by rw [hφ]
    _ = _ := by
      rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
      rfl

/-- Pullback on invariant forms induced by a prefunctor smooth on objects and total arrows. -/
def invariantFormsPullback (Φ : C ⥤q D) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal) :
    TauCeti.Quiver.invariantForms I' J' hs' ht' V k →ₗ[ℝ]
      TauCeti.Quiver.invariantForms I J hs ht V k :=
  (SmoothForm.mpullback Φ.obj hΦ).restrict fun _ ↦ Φ.mpullback_mem_invariantForms hΦ hΦ₁

/-- Pullback of an invariant form is its ordinary pullback on objects. -/
@[simp]
theorem coe_invariantFormsPullback (Φ : C ⥤q D) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal)
    (φ : TauCeti.Quiver.invariantForms I' J' hs' ht' V k) :
    (Φ.invariantFormsPullback (hs := hs) (ht := ht) hΦ hΦ₁ φ : SmoothForm I C V k) =
      SmoothForm.mpullback Φ.obj hΦ φ := (rfl)

/-- Pullback of invariant forms commutes with exterior differentiation. -/
theorem mextDerivₗ_invariantFormsPullback (Φ : C ⥤q D) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal)
    (φ : TauCeti.Quiver.invariantForms I' J' hs' ht' V k) :
    TauCeti.Quiver.invariantForms.mextDerivₗ I J hs ht V k
        (Φ.invariantFormsPullback hΦ hΦ₁ φ) =
      Φ.invariantFormsPullback hΦ hΦ₁
        (TauCeti.Quiver.invariantForms.mextDerivₗ I' J' hs' ht' V k φ) :=
  Subtype.ext (SmoothForm.mextDerivₗ_mpullback _ _ k φ.1)

/-- The identity prefunctor acts identically on invariant forms. -/
@[simp]
theorem invariantFormsPullback_id :
    (𝟭q C).invariantFormsPullback (hs := hs) (ht := ht) (hs' := hs) (ht' := ht)
      (V := V) (k := k) contMDiff_id contMDiff_id = LinearMap.id := by
  ext φ : 1
  exact Subtype.ext (LinearMap.congr_fun SmoothForm.mpullback_id φ.1)

/-- Pullback on invariant forms reverses composition of smooth prefunctors. -/
theorem invariantFormsPullback_comp {E'' H'' A'' K'' B : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    [NormedAddCommGroup A''] [NormedSpace ℝ A''] [TopologicalSpace K'']
    [Quiver B] [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
    [ChartedSpace H'' B] [ChartedSpace K'' (Quiver.Total B)]
    {I'' : ModelWithCorners ℝ E'' H''} {J'' : ModelWithCorners ℝ A'' K''}
    [IsManifold I'' ∞ B] [IsManifold J'' ∞ (Quiver.Total B)]
    {hs'' : ContMDiff J'' I'' ∞ (Quiver.Total.left : Quiver.Total B → B)}
    {ht'' : ContMDiff J'' I'' ∞ (Quiver.Total.right : Quiver.Total B → B)}
    (Φ : C ⥤q D) (Ψ : D ⥤q B) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal) (hΨ : ContMDiff I' I'' ∞ Ψ.obj)
    (hΨ₁ : ContMDiff J' J'' ∞ Ψ.mapTotal) :
    (Φ ⋙q Ψ).invariantFormsPullback (hs := hs) (ht := ht) (hs' := hs'') (ht' := ht'')
        (V := V) (k := k) (hΨ.comp hΦ)
        (Prefunctor.mapTotal_comp Φ Ψ ▸ hΨ₁.comp hΦ₁) =
      (Φ.invariantFormsPullback (hs' := hs') (ht' := ht') hΦ hΦ₁).comp
        (Ψ.invariantFormsPullback hΨ hΨ₁) := by
  ext φ : 1
  exact Subtype.ext (SmoothForm.mpullback_mpullback _ _ hΦ hΨ φ.1).symm

end Prefunctor

namespace TauCeti.Quiver

variable {E H A K E' H' C D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace C] [TopologicalSpace D] [Quiver D]
  [TopologicalSpace (_root_.Quiver.Total D)] [ChartedSpace H C]
  [ChartedSpace H' D] [ChartedSpace K (_root_.Quiver.Total D)]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J' : ModelWithCorners ℝ A K} [IsManifold I ∞ C] [IsManifold I' ∞ D]
  [IsManifold J' ∞ (_root_.Quiver.Total D)]
  {hs' : ContMDiff J' I' ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total D → D)}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- Smooth maps joined by a smooth family of arrows have equal pullbacks on invariant forms. -/
theorem mpullback_eq_of_mem_invariantForms {f g : C → D} (a : ∀ x, f x ⟶ g x)
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    (ha : ContMDiff I J' ∞ fun x ↦ (⟨f x, g x, a x⟩ : _root_.Quiver.Total D))
    {φ : SmoothForm I' D V k} (hφ : φ ∈ invariantForms I' J' hs' ht' V k) :
    SmoothForm.mpullback f hf φ = SmoothForm.mpullback g hg φ := by
  have h := congrArg (SmoothForm.mpullback _ ha) (mem_invariantForms_iff.mp hφ)
  -- The source and target of each connecting arrow are the two object maps.
  simpa only [SmoothForm.mpullback_mpullback, Function.comp_def] using h

end TauCeti.Quiver

namespace CategoryTheory.NatTrans

variable {E H A K E' H' C D : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [Category C] [Category D] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace H C]
  [ChartedSpace H' D] [ChartedSpace K (Quiver.Total D)]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J' : ModelWithCorners ℝ A K} [IsManifold I ∞ C] [IsManifold I' ∞ D]
  [IsManifold J' ∞ (Quiver.Total D)]
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {Φ Ψ : C ⥤ D}

open TauCeti

/-- Smoothly naturally related functors have equal pullbacks on invariant forms. No inverse
transformation is required, and smoothness of the functors on arrows is unnecessary. -/
theorem mpullback_eq_of_mem_invariantForms (η : Φ ⟶ Ψ)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΨ : ContMDiff I I' ∞ Ψ.obj)
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D))
    {φ : SmoothForm I' D V k}
    (hφ : φ ∈ TauCeti.Quiver.invariantForms I' J' hs' ht' V k) :
    SmoothForm.mpullback Φ.obj hΦ φ = SmoothForm.mpullback Ψ.obj hΨ φ :=
  TauCeti.Quiver.mpullback_eq_of_mem_invariantForms η.app hΦ hΨ hη hφ

/-- A smooth natural transformation identifies the linear pullback maps on invariant forms. -/
theorem invariantFormsPullback_eq {B L : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace L] [TopologicalSpace (Quiver.Total C)] [ChartedSpace L (Quiver.Total C)]
    {J : ModelWithCorners ℝ B L} [IsManifold J ∞ (Quiver.Total C)]
    {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
    {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
    (η : Φ ⟶ Ψ) (hΦ : ContMDiff I I' ∞ Φ.obj) (hΨ : ContMDiff I I' ∞ Ψ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ₁ : ContMDiff J J' ∞ Ψ.toPrefunctor.mapTotal)
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D)) :
    Φ.toPrefunctor.invariantFormsPullback (hs := hs) (ht := ht) (hs' := hs') (ht' := ht')
        (V := V) (k := k) hΦ hΦ₁ = Ψ.toPrefunctor.invariantFormsPullback hΨ hΨ₁ := by
  ext φ : 1
  exact Subtype.ext (η.mpullback_eq_of_mem_invariantForms hΦ hΨ hη φ.2)

end CategoryTheory.NatTrans
