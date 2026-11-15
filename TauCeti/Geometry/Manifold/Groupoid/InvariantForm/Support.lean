/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.Groupoid.InvariantForm.Descent
public import TauCeti.Topology.CategoryTheory.Functor.IsomorphismClasses

/-!
# Coarse topological support of differential forms on presentations

For a rough differential form `φ` on the object manifold of a category `C`, its *coarse topological
support* `TauCeti.RoughForm.coarseTSupport φ` is the closure in `Quotient (isIsomorphicSetoid C)`
of the image of the object-level topological support of `φ`. On a smooth groupoid whose source map
is a local diffeomorphism and whose target map is smooth, the object-level support of an invariant
form is saturated under isomorphism, so its coarse image is already closed
(`TauCeti.Quiver.coarseTSupport_eq_image_tsupport`) and pulls back to the exact object-level
support (`TauCeti.Quiver.preimage_coarseTSupport_eq_tsupport`).

Invariant forms with compact coarse support form a submodule
`TauCeti.Quiver.compactlySupportedInvariantForms` closed under exterior differentiation and wedge
products on either side with arbitrary invariant forms. Smooth functors with proper coarse map pull
compact-coarse-support invariant forms back contravariantly
(`CategoryTheory.Functor.compactlySupportedInvariantFormsPullback`), whereas without properness
pullback can fail
(`TauCeti.Quiver.exists_mpullback_notMem_compactlySupportedInvariantForms_of_not_compactSpace`).
Full, essentially surjective étale refinements reflecting isomorphisms induce a linear equivalence
(`CategoryTheory.Functor.compactlySupportedInvariantFormsEquiv`).

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public noncomputable section

open CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace RoughForm

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [Category C] [TopologicalSpace C] [ChartedSpace H C]

section Basic

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {k : ℕ}

/-- The coarse topological support of a rough differential form on the objects of `C`: the closure
in `Quotient (isIsomorphicSetoid C)` of the image of its object-level topological support. -/
def coarseTSupport (φ : RoughForm I C F k) : Set (Quotient (isIsomorphicSetoid C)) :=
  closure (Quotient.mk (isIsomorphicSetoid C) '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)

/-- The coarse topological support is closed in the coarse quotient. -/
theorem isClosed_coarseTSupport (φ : RoughForm I C F k) : IsClosed φ.coarseTSupport :=
  isClosed_closure

/-- The object-level topological support lies in the preimage of the coarse topological support. -/
theorem tsupport_subset_preimage_coarseTSupport (φ : RoughForm I C F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ ⊆
      Quotient.mk (isIsomorphicSetoid C) ⁻¹' φ.coarseTSupport :=
  (Set.subset_preimage_image _ _).trans (Set.preimage_mono subset_closure)

/-- The zero rough form has empty coarse topological support. -/
@[simp]
theorem coarseTSupport_zero : (0 : RoughForm I C F k).coarseTSupport = ∅ := by
  change closure (Quotient.mk (isIsomorphicSetoid C) ''
    _root_.tsupport (0 : C → E [⋀^Fin k]→L[ℝ] F)) = ∅
  simp

/-- The coarse topological support of a rough form is empty if and only if the form is zero. -/
@[simp]
theorem coarseTSupport_eq_empty_iff {φ : RoughForm I C F k} : φ.coarseTSupport = ∅ ↔ φ = 0 := by
  rw [coarseTSupport, closure_empty_iff, Set.image_eq_empty]
  refine ⟨fun h ↦ funext fun x ↦ by_contra fun hx ↦ Set.eq_empty_iff_forall_notMem.mp h x
    (subset_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ hx), ?_⟩
  rintro rfl
  change _root_.tsupport (0 : C → E [⋀^Fin k]→L[ℝ] F) = ∅
  simp

omit [Category C] in
/-- Addition of rough forms does not enlarge topological support beyond the union of supports. -/
theorem tsupport_add_subset [ContinuousAdd F] (φ ψ : RoughForm I C F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) (φ + ψ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ ∪
        _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) ψ := by
  refine closure_minimal (fun x hx ↦ ?_)
    ((_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ).union
      (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] F) ψ))
  by_contra hnot; rw [Set.mem_union, not_or] at hnot; apply hx
  have hφ : φ x = 0 := by by_contra h; exact hnot.1 (subset_tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ h)
  have hψ : ψ x = 0 := by by_contra h; exact hnot.2 (subset_tsupport (α := E [⋀^Fin k]→L[ℝ] F) ψ h)
  change φ x + ψ x = 0; rw [hφ, hψ, add_zero]

/-- Coarse topological support of a sum is contained in the union of the coarse supports. -/
theorem coarseTSupport_add_subset [ContinuousAdd F] (φ ψ : RoughForm I C F k) :
    (φ + ψ).coarseTSupport ⊆ φ.coarseTSupport ∪ ψ.coarseTSupport :=
  closure_minimal ((Set.image_mono (tsupport_add_subset φ ψ)).trans <| by
      rw [Set.image_union]; exact Set.union_subset_union subset_closure subset_closure)
    ((isClosed_coarseTSupport φ).union (isClosed_coarseTSupport ψ))

/-- Scalar multiplication does not enlarge coarse topological support. -/
theorem coarseTSupport_smul_subset [ContinuousConstSMul ℝ F] (c : ℝ) (φ : RoughForm I C F k) :
    (c • φ).coarseTSupport ⊆ φ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_smul_subset c φ))

/-- Multiplication by a nonzero scalar preserves coarse topological support. -/
theorem coarseTSupport_smul [ContinuousConstSMul ℝ F] (c : ℝ) (φ : RoughForm I C F k)
    (hc : c ≠ 0) : (c • φ).coarseTSupport = φ.coarseTSupport := by
  simp only [coarseTSupport, tsupport_smul c φ hc]

end Basic

section DifferentialAndWedge

variable {k l : ℕ}

/-- Exterior differentiation does not enlarge coarse topological support. -/
theorem coarseTSupport_mextDeriv_subset {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : RoughForm I C V k) : (TauCeti.mextDeriv φ).coarseTSupport ⊆ φ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_mextDeriv_subset φ))

/-- Paired wedge product is supported in the coarse support of its left factor. -/
theorem coarseTSupport_wedgeWith_subset_left {V₁ V₂ V₃ : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃) (φ : RoughForm I C V₁ k) (ψ : RoughForm I C V₂ l) :
    (φ.wedgeWith μ ψ).coarseTSupport ⊆ φ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_wedgeWith_subset_left μ φ ψ))

/-- Paired wedge product is supported in the coarse support of its right factor. -/
theorem coarseTSupport_wedgeWith_subset_right {V₁ V₂ V₃ : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃) (φ : RoughForm I C V₁ k) (ψ : RoughForm I C V₂ l) :
    (φ.wedgeWith μ ψ).coarseTSupport ⊆ ψ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_wedgeWith_subset_right μ φ ψ))

end DifferentialAndWedge

end RoughForm

namespace SmoothForm

variable {E H C V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [Category C] [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I 1 C] [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- The coarse topological support of a smooth differential form on the objects of `C`. -/
def coarseTSupport (φ : SmoothForm I C V k) : Set (Quotient (isIsomorphicSetoid C)) :=
  RoughForm.coarseTSupport (F := V) φ.1

/-- The coarse topological support of a smooth form is that of its underlying rough form. -/
theorem coarseTSupport_eq (φ : SmoothForm I C V k) :
    φ.coarseTSupport = RoughForm.coarseTSupport (F := V) φ.1 := (rfl)

/-- The zero smooth form has empty coarse topological support. -/
@[simp]
theorem coarseTSupport_zero : (0 : SmoothForm I C V k).coarseTSupport = ∅ :=
  RoughForm.coarseTSupport_zero

/-- A smooth form has empty coarse topological support if and only if it is zero. -/
@[simp]
theorem coarseTSupport_eq_empty_iff {φ : SmoothForm I C V k} : φ.coarseTSupport = ∅ ↔ φ = 0 := by
  rw [coarseTSupport_eq, RoughForm.coarseTSupport_eq_empty_iff, Submodule.coe_eq_zero]

end SmoothForm

namespace Quiver

variable {E H A K C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [Category C] [TopologicalSpace C] [TopologicalSpace (_root_.Quiver.Total C)]
  [ChartedSpace H C] [ChartedSpace K (_root_.Quiver.Total C)]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ A K)
  [IsManifold I ∞ C] [IsManifold J ∞ (_root_.Quiver.Total C)]

section EtaleSaturation

variable {I J} [IsGroupoid C] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

/-- On a groupoid whose source is a smooth local diffeomorphism and whose target is smooth, the
object-level topological support of an invariant form is saturated under isomorphism. -/
theorem preimage_image_tsupport_eq
    (hs : IsLocalDiffeomorph J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
    {ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C)}
    {φ : SmoothForm I C V k} (hφ : φ ∈ invariantForms I J hs.contMDiff ht V k) :
    Quotient.mk (isIsomorphicSetoid C) ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.1) =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.1 := by
  let := Groupoid.ofIsGroupoid (C := C)
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro y ⟨x, hx, hxy⟩
  obtain ⟨f⟩ := TauCeti.isomorphismClassesMk_eq_iff.mp hxy
  have ha : (⟨x, y, f⟩ : _root_.Quiver.Total C) ∈
      _root_.Quiver.Total.left ⁻¹' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.1 := hx
  rw [← RoughForm.tsupport_mpullback_eq_preimage (F := V) (k := k) φ.1 hs.contMDiff.continuous
    hs.isOpenMap (hs.isInvertible_mfderiv (by simp))] at ha
  have hinv := congrArg Subtype.val (mem_invariantForms_iff.mp hφ)
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback] at hinv
  exact RoughForm.tsupport_mpullback_subset_preimage (F := V) (k := k) ht.continuous φ.1 (hinv ▸ ha)

/-- On a groupoid whose source is a smooth local diffeomorphism and whose target is smooth, the
image in the coarse quotient of the topological support of an invariant form is already closed. -/
theorem coarseTSupport_eq_image_tsupport
    (hs : IsLocalDiffeomorph J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
    {ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C)}
    {φ : SmoothForm I C V k} (hφ : φ ∈ invariantForms I J hs.contMDiff ht V k) :
    φ.coarseTSupport =
      Quotient.mk (isIsomorphicSetoid C) '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.1 := by
  refine IsClosed.closure_eq ((isQuotientMap_quotient_mk' (X := C)
    (s := isIsomorphicSetoid C)).isClosed_preimage.mp ?_)
  change IsClosed (Quotient.mk (isIsomorphicSetoid C) ⁻¹' _)
  rw [preimage_image_tsupport_eq hs hφ]
  exact _root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.1

/-- On a groupoid whose source is a smooth local diffeomorphism and whose target is smooth, pulling
the coarse support of an invariant form back to objects recovers its exact topological support. -/
theorem preimage_coarseTSupport_eq_tsupport
    (hs : IsLocalDiffeomorph J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
    {ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C)}
    {φ : SmoothForm I C V k} (hφ : φ ∈ invariantForms I J hs.contMDiff ht V k) :
    Quotient.mk (isIsomorphicSetoid C) ⁻¹' φ.coarseTSupport =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.1 := by
  rw [coarseTSupport_eq_image_tsupport hs hφ, preimage_image_tsupport_eq hs hφ]

end EtaleSaturation

section Submodule

variable (hs : ContMDiff J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C))
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ)

/-- The submodule of invariant smooth `k`-forms whose coarse topological support is compact in
`Quotient (isIsomorphicSetoid C)`. -/
def compactlySupportedInvariantForms : Submodule ℝ (SmoothForm I C V k) where
  carrier := {φ | φ ∈ invariantForms I J hs ht V k ∧ IsCompact φ.coarseTSupport}
  zero_mem' := ⟨zero_mem _, by rw [SmoothForm.coarseTSupport_zero]; exact isCompact_empty⟩
  add_mem' hφ hψ := ⟨add_mem hφ.1 hψ.1, (hφ.2.union hψ.2).of_isClosed_subset
    (RoughForm.isClosed_coarseTSupport _) (RoughForm.coarseTSupport_add_subset (F := V) _ _)⟩
  smul_mem' c φ hφ := ⟨Submodule.smul_mem _ c hφ.1, hφ.2.of_isClosed_subset
    (RoughForm.isClosed_coarseTSupport _) (RoughForm.coarseTSupport_smul_subset (F := V) c _)⟩

variable {I J hs ht V k}

/-- Membership in `compactlySupportedInvariantForms` means invariance with compact coarse
support. -/
@[simp]
theorem mem_compactlySupportedInvariantForms_iff {φ : SmoothForm I C V k} :
    φ ∈ compactlySupportedInvariantForms I J hs ht V k ↔
      φ ∈ invariantForms I J hs ht V k ∧ IsCompact φ.coarseTSupport := Iff.rfl

/-- Every compact-coarse-support invariant form is an invariant form. -/
theorem compactlySupportedInvariantForms_le_invariantForms :
    compactlySupportedInvariantForms I J hs ht V k ≤ invariantForms I J hs ht V k := fun _ h ↦ h.1

/-- When the coarse space is compact, every invariant form has compact coarse support. -/
@[simp]
theorem compactlySupportedInvariantForms_eq_invariantForms
    [CompactSpace (Quotient (isIsomorphicSetoid C))] :
    compactlySupportedInvariantForms I J hs ht V k = invariantForms I J hs ht V k :=
  le_antisymm compactlySupportedInvariantForms_le_invariantForms fun _ hφ ↦
    ⟨hφ, isCompact_univ.of_isClosed_subset (RoughForm.isClosed_coarseTSupport _)
      (Set.subset_univ _)⟩

/-- Exterior differentiation preserves compact-coarse-support invariant forms. -/
theorem mextDerivₗ_mem_compactlySupportedInvariantForms {φ : SmoothForm I C V k}
    (hφ : φ ∈ compactlySupportedInvariantForms I J hs ht V k) :
    mextDerivₗ I k φ ∈ compactlySupportedInvariantForms I J hs ht V (k + 1) := by
  refine ⟨mextDerivₗ_mem_invariantForms hφ.1,
    hφ.2.of_isClosed_subset (RoughForm.isClosed_coarseTSupport _) ?_⟩
  rw [SmoothForm.coarseTSupport_eq, mextDerivₗ_apply, SmoothForm.coarseTSupport_eq]
  exact RoughForm.coarseTSupport_mextDeriv_subset (V := V) φ.1

variable (I J hs ht V k) in
/-- Exterior differentiation restricted to compact-coarse-support invariant forms. -/
def compactlySupportedInvariantForms.mextDerivₗ :
    compactlySupportedInvariantForms I J hs ht V k →ₗ[ℝ]
      compactlySupportedInvariantForms I J hs ht V (k + 1) :=
  (TauCeti.mextDerivₗ I k).restrict fun _ ↦ mextDerivₗ_mem_compactlySupportedInvariantForms

/-- Exterior differentiation on `compactlySupportedInvariantForms` agrees with the object-level
exterior derivative. -/
@[simp]
theorem compactlySupportedInvariantForms.coe_mextDerivₗ
    (φ : compactlySupportedInvariantForms I J hs ht V k) :
    (compactlySupportedInvariantForms.mextDerivₗ I J hs ht V k φ :
      SmoothForm I C V (k + 1)) = TauCeti.mextDerivₗ I k φ := (rfl)

variable (I J hs ht V k) in
/-- Exterior differentiation on compact-coarse-support invariant forms squares to zero. -/
@[simp]
theorem compactlySupportedInvariantForms.mextDerivₗ_comp_mextDerivₗ :
    (compactlySupportedInvariantForms.mextDerivₗ I J hs ht V (k + 1)).comp
      (compactlySupportedInvariantForms.mextDerivₗ I J hs ht V k) = 0 := by
  ext φ : 1; exact Subtype.ext (LinearMap.congr_fun (TauCeti.mextDerivₗ_comp_mextDerivₗ I k) φ.1)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Paired wedge product of a compact-coarse-support invariant form on the left with any invariant
form on the right has compact coarse support. -/
theorem wedgeWith_mem_compactlySupportedInvariantForms_left {V₁ V₂ V₃ : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃) {l : ℕ}
    {φ : SmoothForm I C V₁ k} {η : SmoothForm I C V₂ l}
    (hφ : φ ∈ compactlySupportedInvariantForms I J hs ht V₁ k)
    (hη : η ∈ invariantForms I J hs ht V₂ l) :
    SmoothForm.wedgeWith μ φ η ∈ compactlySupportedInvariantForms I J hs ht V₃ (k + l) := by
  refine ⟨wedgeWith_mem_invariantForms μ hφ.1 hη,
    hφ.2.of_isClosed_subset (RoughForm.isClosed_coarseTSupport _) ?_⟩
  rw [SmoothForm.coarseTSupport_eq, SmoothForm.coe_wedgeWith, SmoothForm.coarseTSupport_eq]
  exact RoughForm.coarseTSupport_wedgeWith_subset_left μ φ.1 η.1

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Paired wedge product of any invariant form on the left with a compact-coarse-support invariant
form on the right has compact coarse support. -/
theorem wedgeWith_mem_compactlySupportedInvariantForms_right {V₁ V₂ V₃ : Type*}
    [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂] [NormedSpace ℝ V₂]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃) {l : ℕ}
    {φ : SmoothForm I C V₁ k} {η : SmoothForm I C V₂ l}
    (hφ : φ ∈ invariantForms I J hs ht V₁ k)
    (hη : η ∈ compactlySupportedInvariantForms I J hs ht V₂ l) :
    SmoothForm.wedgeWith μ φ η ∈ compactlySupportedInvariantForms I J hs ht V₃ (k + l) := by
  refine ⟨wedgeWith_mem_invariantForms μ hφ hη.1,
    hη.2.of_isClosed_subset (RoughForm.isClosed_coarseTSupport _) ?_⟩
  rw [SmoothForm.coarseTSupport_eq, SmoothForm.coe_wedgeWith, SmoothForm.coarseTSupport_eq]
  exact RoughForm.coarseTSupport_wedgeWith_subset_right μ φ.1 η.1

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Wedge product of a real-valued compact-coarse-support invariant form on the left with any
invariant form has compact coarse support. -/
theorem wedge_mem_compactlySupportedInvariantForms_left {l : ℕ}
    {φ : SmoothForm I C ℝ k} {η : SmoothForm I C ℝ l}
    (hφ : φ ∈ compactlySupportedInvariantForms I J hs ht ℝ k)
    (hη : η ∈ invariantForms I J hs ht ℝ l) :
    SmoothForm.wedge φ η ∈ compactlySupportedInvariantForms I J hs ht ℝ (k + l) :=
  SmoothForm.wedge_def φ η ▸ wedgeWith_mem_compactlySupportedInvariantForms_left _ hφ hη

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Wedge product of any real-valued invariant form on the left with a compact-coarse-support
invariant form on the right has compact coarse support. -/
theorem wedge_mem_compactlySupportedInvariantForms_right {l : ℕ}
    {φ : SmoothForm I C ℝ k} {η : SmoothForm I C ℝ l}
    (hφ : φ ∈ invariantForms I J hs ht ℝ k)
    (hη : η ∈ compactlySupportedInvariantForms I J hs ht ℝ l) :
    SmoothForm.wedge φ η ∈ compactlySupportedInvariantForms I J hs ht ℝ (k + l) :=
  SmoothForm.wedge_def φ η ▸ wedgeWith_mem_compactlySupportedInvariantForms_right _ hφ hη

end Submodule

end Quiver

end TauCeti

section Functoriality

universe v u

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {C D : Type u} [Category.{v} C] [Category.{v} D] [TopologicalSpace C] [TopologicalSpace D]
  [ChartedSpace H C] [ChartedSpace H' D]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {k : ℕ}

namespace CategoryTheory.Functor

section CoarseSupport

open TauCeti

/-- Along a functor with continuous object map, the coarse support of a pulled-back rough form lies
in the preimage of the original coarse support under the induced map on isomorphism classes. -/
theorem coarseTSupport_mpullback_subset_preimage {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (Φ : C ⥤ D) (hΦ : Continuous Φ.obj) (φ : RoughForm I' D F k) :
    (mpullback (F := F) (k := k) I I' Φ.obj φ).coarseTSupport ⊆
      isomorphismClasses.map Φ.toCatHom ⁻¹' φ.coarseTSupport := by
  refine closure_minimal ?_
    ((RoughForm.isClosed_coarseTSupport φ).preimage (Φ.continuous_isomorphismClasses_map hΦ))
  rintro _ ⟨x, hx, rfl⟩
  exact subset_closure ⟨Φ.obj x,
    RoughForm.tsupport_mpullback_subset_preimage (F := F) (k := k) hΦ φ hx, rfl⟩

/-- Along a functor into a groupoid with locally diffeomorphic source and smooth target whose
object map is a local diffeomorphism, the coarse support of the pullback of an invariant form is
the exact preimage of its coarse support. -/
theorem coarseTSupport_mpullback_eq_preimage {A' K' : Type*}
    [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K'] [IsGroupoid D]
    [TopologicalSpace (Quiver.Total D)] [ChartedSpace K' (Quiver.Total D)]
    {J' : ModelWithCorners ℝ A' K'} [IsManifold I ∞ C] [IsManifold I' ∞ D]
    [IsManifold J' ∞ (Quiver.Total D)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : C ⥤ D) (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) {φ : SmoothForm I' D V k}
    (hφ : φ ∈ TauCeti.Quiver.invariantForms I' J' hs'.contMDiff ht' V k) :
    (SmoothForm.mpullback Φ.obj hΦ.contMDiff φ).coarseTSupport =
      isomorphismClasses.map Φ.toCatHom ⁻¹' φ.coarseTSupport := by
  rw [SmoothForm.coarseTSupport_eq, SmoothForm.coe_mpullback]
  refine (Φ.coarseTSupport_mpullback_subset_preimage (I := I) (F := V)
    hΦ.contMDiff.continuous φ.1).antisymm fun q hq ↦ ?_
  induction q using Quotient.inductionOn with
  | h x =>
    have hΦx : Φ.obj x ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] V) φ.1 := by
      rwa [← TauCeti.Quiver.preimage_coarseTSupport_eq_tsupport hs' hφ]
    refine subset_closure ⟨x, ?_, rfl⟩
    rwa [RoughForm.tsupport_mpullback_eq_preimage (F := V) (k := k) φ.1 hΦ.contMDiff.continuous
      hΦ.isOpenMap (hΦ.isInvertible_mfderiv (by simp))]

end CoarseSupport

end CategoryTheory.Functor

section SmoothPresentations

variable {A K A' K' : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']
  [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
  [ChartedSpace K (Quiver.Total C)] [ChartedSpace K' (Quiver.Total D)]
  {J : ModelWithCorners ℝ A K} {J' : ModelWithCorners ℝ A' K'}
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace CategoryTheory.Functor

section ProperPullback

variable {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}

open TauCeti

/-- Smooth pullback preserves compact coarse support whenever the preimage of the form's coarse
support under the induced coarse map is compact. -/
theorem mpullback_mem_compactlySupportedInvariantForms_of_isCompact_preimage (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    {φ : SmoothForm I' D V k} (hφ : φ ∈ TauCeti.Quiver.invariantForms I' J' hs' ht' V k)
    (hc : IsCompact (X := Quotient (isIsomorphicSetoid C))
      (isomorphismClasses.map Φ.toCatHom ⁻¹' φ.coarseTSupport)) :
    SmoothForm.mpullback Φ.obj hΦ φ ∈
      TauCeti.Quiver.compactlySupportedInvariantForms I J hs ht V k := by
  refine ⟨Φ.toPrefunctor.mpullback_mem_invariantForms hΦ hΦ₁ hφ,
    hc.of_isClosed_subset (RoughForm.isClosed_coarseTSupport _) ?_⟩
  rw [SmoothForm.coarseTSupport_eq, SmoothForm.coe_mpullback]
  exact Φ.coarseTSupport_mpullback_subset_preimage (I := I) (F := V) hΦ.continuous φ.1

/-- Smooth pullback along a functor whose induced coarse map is proper preserves compact coarse
support on invariant forms. -/
theorem mpullback_mem_compactlySupportedInvariantForms (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    {φ : SmoothForm I' D V k}
    (hφ : φ ∈ TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs' ht' V k) :
    SmoothForm.mpullback Φ.obj hΦ φ ∈
      TauCeti.Quiver.compactlySupportedInvariantForms I J hs ht V k :=
  Φ.mpullback_mem_compactlySupportedInvariantForms_of_isCompact_preimage hΦ hΦ₁ hφ.1
    (hp.isCompact_preimage hφ.2)

/-- Contravariant pullback on compact-coarse-support invariant forms along a smooth functor whose
induced map on isomorphism classes is proper. -/
def compactlySupportedInvariantFormsPullback (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom)) :
    TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs' ht' V k →ₗ[ℝ]
      TauCeti.Quiver.compactlySupportedInvariantForms I J hs ht V k :=
  (SmoothForm.mpullback Φ.obj hΦ).restrict fun _ ↦
    Φ.mpullback_mem_compactlySupportedInvariantForms hΦ hΦ₁ hp

/-- Pullback of a compact-coarse-support invariant form agrees with object-level smooth pullback. -/
@[simp]
theorem coe_compactlySupportedInvariantFormsPullback (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    (φ : TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs' ht' V k) :
    (Φ.compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht) hΦ hΦ₁ hp φ :
      SmoothForm I C V k) = SmoothForm.mpullback Φ.obj hΦ φ := (rfl)

/-- Pullback of compact-coarse-support invariant forms commutes with exterior differentiation. -/
theorem mextDerivₗ_compactlySupportedInvariantFormsPullback (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    (φ : TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs' ht' V k) :
    TauCeti.Quiver.compactlySupportedInvariantForms.mextDerivₗ I J hs ht V k
        (Φ.compactlySupportedInvariantFormsPullback hΦ hΦ₁ hp φ) =
      Φ.compactlySupportedInvariantFormsPullback hΦ hΦ₁ hp
        (TauCeti.Quiver.compactlySupportedInvariantForms.mextDerivₗ I' J' hs' ht' V k φ) :=
  Subtype.ext (SmoothForm.mextDerivₗ_mpullback _ _ k φ.1)

/-- The identity functor acts as the identity on compact-coarse-support invariant forms. -/
@[simp]
theorem compactlySupportedInvariantFormsPullback_id :
    (𝟭 C).compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht) (hs' := hs) (ht' := ht)
        (V := V) (k := k) contMDiff_id contMDiff_id (by
          change IsProperMap (X := Quotient (isIsomorphicSetoid C))
            (Y := Quotient (isIsomorphicSetoid C)) (isomorphismClasses.map (𝟙 (Cat.of C)))
          rw [isomorphismClasses.map_id]; exact isProperMap_id) = LinearMap.id :=
  LinearMap.ext fun φ ↦ Subtype.ext (LinearMap.congr_fun SmoothForm.mpullback_id φ.1)

/-- Pullback on compact-coarse-support invariant forms reverses composition of smooth functors with
proper coarse maps. -/
theorem compactlySupportedInvariantFormsPullback_comp {E'' H'' A'' K'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    [NormedAddCommGroup A''] [NormedSpace ℝ A''] [TopologicalSpace K'']
    {B : Type u} [Category.{v} B] [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
    [ChartedSpace H'' B] [ChartedSpace K'' (Quiver.Total B)]
    {I'' : ModelWithCorners ℝ E'' H''} {J'' : ModelWithCorners ℝ A'' K''}
    [IsManifold I'' ∞ B] [IsManifold J'' ∞ (Quiver.Total B)]
    {hs'' : ContMDiff J'' I'' ∞ (Quiver.Total.left : Quiver.Total B → B)}
    {ht'' : ContMDiff J'' I'' ∞ (Quiver.Total.right : Quiver.Total B → B)}
    (Φ : C ⥤ D) (Ψ : D ⥤ B)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ : ContMDiff I' I'' ∞ Ψ.obj) (hΨ₁ : ContMDiff J' J'' ∞ Ψ.toPrefunctor.mapTotal)
    (hpΦ : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    (hpΨ : IsProperMap (X := Quotient (isIsomorphicSetoid D))
      (Y := Quotient (isIsomorphicSetoid B)) (isomorphismClasses.map Ψ.toCatHom)) :
    (Φ ⋙ Ψ).compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht)
        (hs' := hs'') (ht' := ht'') (V := V) (k := k) (hΨ.comp hΦ)
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ₁.comp hΦ₁) (by
          change IsProperMap (X := Quotient (isIsomorphicSetoid C))
            (Y := Quotient (isIsomorphicSetoid B))
            (isomorphismClasses.map (Φ.toCatHom ≫ Ψ.toCatHom))
          rw [isomorphismClasses.map_comp]; exact hpΨ.comp hpΦ) =
      (Φ.compactlySupportedInvariantFormsPullback (hs' := hs') (ht' := ht') hΦ hΦ₁ hpΦ).comp
        (Ψ.compactlySupportedInvariantFormsPullback hΨ hΨ₁ hpΨ) :=
  LinearMap.ext fun φ ↦ Subtype.ext (SmoothForm.mpullback_mpullback _ _ hΦ hΨ φ.1).symm

end ProperPullback

section EtaleEquiv

variable [IsGroupoid D] [TauCeti.IsTopologicalGroupoid D]

open TauCeti

/-- Descent of an invariant form along an étale refinement transports its coarse support by the
induced map on isomorphism classes. -/
theorem coarseTSupport_invariantFormsEquiv_symm (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k) :
    ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).1.coarseTSupport =
      isomorphismClasses.map Φ.toCatHom '' α.1.coarseTSupport := by
  let β := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α
  have hpre : isomorphismClasses.map Φ.toCatHom ⁻¹' β.1.coarseTSupport = α.1.coarseTSupport := by
    rw [← Φ.coarseTSupport_mpullback_eq_preimage hs' hΦ β.2,
      Φ.mpullback_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ α]
  exact hpre ▸ (Φ.isomorphismClasses_map_surjective.image_preimage _).symm

/-- **Étale-refinement descent of compact-coarse-support invariant forms.** A full, essentially
surjective étale refinement reflecting isomorphisms induces a coarse homeomorphism and therefore a
linear equivalence on invariant forms with compact coarse support. -/
def compactlySupportedInvariantFormsEquiv (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs'.contMDiff ht'.contMDiff V k ≃ₗ[ℝ]
      TauCeti.Quiver.compactlySupportedInvariantForms I J hs.contMDiff ht V k :=
  LinearEquiv.ofBijective
    (Φ.compactlySupportedInvariantFormsPullback hΦ.contMDiff hΦ₁
      (coe_isomorphismClassesHomeomorphOfEssSurj Φ hΦ.contMDiff.continuous hΦ.isOpenMap
        hs'.contMDiff.continuous ht'.isOpenMap ▸
        (Φ.isomorphismClassesHomeomorphOfEssSurj hΦ.contMDiff.continuous hΦ.isOpenMap
          hs'.contMDiff.continuous ht'.isOpenMap).isProperMap))
    ⟨fun φ ψ h ↦ by
        have hpull : Φ.toPrefunctor.invariantFormsPullback (hs := hs.contMDiff) (ht := ht)
            hΦ.contMDiff hΦ₁ ⟨φ.1, φ.2.1⟩ =
          Φ.toPrefunctor.invariantFormsPullback hΦ.contMDiff hΦ₁ ⟨ψ.1, ψ.2.1⟩ := by
          apply Subtype.ext
          rw [Prefunctor.coe_invariantFormsPullback, Prefunctor.coe_invariantFormsPullback]
          exact congrArg Subtype.val h
        exact Subtype.ext (congrArg (Subtype.val :
          TauCeti.Quiver.invariantForms I' J' hs'.contMDiff ht'.contMDiff V k →
            SmoothForm I' D V k) (Φ.invariantFormsPullback_injective hΦ hΦ₁ ht' hpull)),
      fun α ↦ by
        let β := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm ⟨α.1, α.2.1⟩
        refine ⟨⟨β.1, β.2, ?_⟩,
          Subtype.ext (Φ.mpullback_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ ⟨α.1, α.2.1⟩)⟩
        rw [Φ.coarseTSupport_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ ⟨α.1, α.2.1⟩]
        exact α.2.2.image (Φ.continuous_isomorphismClasses_map hΦ.contMDiff.continuous)⟩

/-- Applying `compactlySupportedInvariantFormsEquiv` computes object-level smooth pullback. -/
@[simp]
theorem coe_compactlySupportedInvariantFormsEquiv_apply (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (φ : TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs'.contMDiff ht'.contMDiff V k) :
    (Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁ φ : SmoothForm I C V k) =
      SmoothForm.mpullback Φ.obj hΦ.contMDiff φ := (rfl)

/-- Descent of compact-coarse-support invariant forms commutes with exterior differentiation. -/
theorem compactlySupportedInvariantFormsEquiv_symm_mextDerivₗ (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : TauCeti.Quiver.compactlySupportedInvariantForms I J hs.contMDiff ht V k) :
    (Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm
        (TauCeti.Quiver.compactlySupportedInvariantForms.mextDerivₗ I J hs.contMDiff ht V k α) =
      TauCeti.Quiver.compactlySupportedInvariantForms.mextDerivₗ
        I' J' hs'.contMDiff ht'.contMDiff V k
        ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α) := by
  refine (LinearEquiv.symm_apply_eq _).mpr <| Subtype.ext ?_
  rw [coe_compactlySupportedInvariantFormsEquiv_apply,
    TauCeti.Quiver.compactlySupportedInvariantForms.coe_mextDerivₗ,
    TauCeti.Quiver.compactlySupportedInvariantForms.coe_mextDerivₗ,
    ← SmoothForm.mextDerivₗ_mpullback]
  exact congrArg (TauCeti.mextDerivₗ I k) (by
    simpa only [coe_compactlySupportedInvariantFormsEquiv_apply] using congrArg Subtype.val
      ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).apply_symm_apply α).symm)

end EtaleEquiv

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {Φ Ψ : C ⥤ D}

/-- Smoothly naturally related functors with proper coarse maps induce equal pullbacks on
compact-coarse-support invariant forms. -/
theorem compactlySupportedInvariantFormsPullback_eq (η : Φ ⟶ Ψ)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΨ : ContMDiff I I' ∞ Ψ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ₁ : ContMDiff J J' ∞ Ψ.toPrefunctor.mapTotal)
    (hpΦ : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    (hpΨ : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Ψ.toCatHom))
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D)) :
    Φ.compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht) (hs' := hs') (ht' := ht')
        (V := V) (k := k) hΦ hΦ₁ hpΦ =
      Ψ.compactlySupportedInvariantFormsPullback hΨ hΨ₁ hpΨ :=
  LinearMap.ext fun φ ↦ Subtype.ext (η.mpullback_eq_of_mem_invariantForms hΦ hΨ hη φ.2.1)

end CategoryTheory.NatTrans

end SmoothPresentations

end Functoriality

namespace TauCeti

/-- If the coarse space of `C` is noncompact while the coarse space of `D` is compact, then for any
nontrivial coefficient space `V` and any smooth functor `Φ : C ⥤ D`, some compact-coarse-support
invariant `0`-form on `D` pulls back to an invariant `0`-form on `C` without compact coarse
support. -/
theorem Quiver.exists_mpullback_notMem_compactlySupportedInvariantForms_of_not_compactSpace
    {E H A K E' H' A' K' C D V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']
    [Category C] [Category D] [TopologicalSpace C] [TopologicalSpace D]
    [TopologicalSpace (_root_.Quiver.Total C)] [TopologicalSpace (_root_.Quiver.Total D)]
    [ChartedSpace H C] [ChartedSpace K (_root_.Quiver.Total C)]
    [ChartedSpace H' D] [ChartedSpace K' (_root_.Quiver.Total D)]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ A K}
    {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ A' K'}
    [IsManifold I ∞ C] [IsManifold J ∞ (_root_.Quiver.Total C)]
    [IsManifold I' ∞ D] [IsManifold J' ∞ (_root_.Quiver.Total D)]
    (hs : ContMDiff J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C))
    (hs' : ContMDiff J' I' ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total D → D))
    (ht' : ContMDiff J' I' ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total D → D))
    [CompactSpace (Quotient (isIsomorphicSetoid D))]
    (hnc : ¬ CompactSpace (Quotient (isIsomorphicSetoid C)))
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]
    (Φ : C ⥤ D) (hΦ : ContMDiff I I' ∞ Φ.obj) :
    ∃ φ ∈ Quiver.compactlySupportedInvariantForms I' J' hs' ht' V 0,
      SmoothForm.mpullback Φ.obj hΦ φ ∉
        Quiver.compactlySupportedInvariantForms I J hs ht V 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let φ : SmoothForm I' D V 0 := SmoothForm.ofFunction ⟨fun _ ↦ v, contMDiff_const⟩
  have hφ_coe : (φ : RoughForm I' D V 0) = RoughForm.ofFunction I' fun _ ↦ v :=
    SmoothForm.coe_ofFunction ⟨fun _ ↦ v, contMDiff_const⟩
  have hφ_inv : φ ∈ Quiver.invariantForms I' J' hs' ht' V 0 := by
    rw [Quiver.mem_invariantForms_iff]
    refine Subtype.ext ?_
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, hφ_coe,
      mpullback_ofFunction, mpullback_ofFunction]
    rfl
  refine ⟨φ, by rwa [Quiver.compactlySupportedInvariantForms_eq_invariantForms],
    fun hmem ↦ hnc ⟨?_⟩⟩
  have huniv : (SmoothForm.mpullback Φ.obj hΦ φ).coarseTSupport = Set.univ :=
    Set.eq_univ_iff_forall.mpr <| Quotient.ind fun x ↦
      subset_closure ⟨x, subset_tsupport (α := E [⋀^Fin 0]→L[ℝ] V) _ fun h0 ↦ hv <| by
        have hp : ((SmoothForm.mpullback Φ.obj hΦ φ).1 x : E [⋀^Fin 0]→L[ℝ] V) 0 = v := by
          rw [SmoothForm.coe_mpullback, hφ_coe, mpullback_ofFunction]
          exact RoughForm.ofFunction_apply (I := I) (fun _ ↦ v) x 0
        exact hp.symm.trans (congrArg (· 0) h0), rfl⟩
  exact huniv ▸ hmem.2

end TauCeti
