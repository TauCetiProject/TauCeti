/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.Groupoid.InvariantForm.Descent
public import TauCeti.Topology.CategoryTheory.Functor.IsomorphismClasses
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses

/-!
# Coarse topological support of differential forms on presentations

When an orbifold is presented by an étale Lie groupoid `C`, requiring compact support on the
object manifold `C` fails to reflect the geometry of the orbifold: object-level compact support
can exclude relevant invariant forms (even those supported over compact regions of the coarse
space) and is not invariant under étale atlas refinements. Instead, we measure compactness in the
coarse space `Quotient (isIsomorphicSetoid C)`.

For a rough or smooth differential form `φ` on the object manifold of a category `C`, its *coarse
topological support* `TauCeti.RoughForm.coarseTSupport φ` (`TauCeti.SmoothForm.coarseTSupport φ`)
is the closure in `Quotient (isIsomorphicSetoid C)` of the image of its object-level topological
support. On a smooth category whose source map is a local diffeomorphism and whose target map is
smooth, the object-level support of an invariant form is saturated under isomorphism, so its coarse
image is already closed (`TauCeti.Quiver.coarseTSupport_eq_image_tsupport`) and pulls back to the
exact object-level support (`TauCeti.Quiver.preimage_coarseTSupport_eq_tsupport`).

Invariant forms with compact coarse support form a submodule
`TauCeti.Quiver.compactlySupportedInvariantForms` closed under exterior differentiation and wedge
products on either side with arbitrary invariant forms; this submodule is preserved across étale
refinements and feeds compactly supported invariant de Rham cohomology and orbifold integration.
Smooth functors with proper coarse map pull compact-coarse-support invariant forms back
contravariantly (`CategoryTheory.Functor.compactlySupportedInvariantFormsPullback`), whereas
without properness pullback along a smooth object map can fail
(`TauCeti.Quiver.exists_mpullback_notMem_compactlySupportedInvariantForms_of_not_compactSpace`).
Full, essentially surjective étale refinements reflecting isomorphisms into a topological smooth
groupoid induce a linear equivalence
(`CategoryTheory.Functor.compactlySupportedInvariantFormsEquiv`) compatible with exterior
differentiation, two-sided wedge products, functoriality, and smooth natural transformations.

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

/-- The coarse topological support of a rough form on `C`: the closure in
`Quotient (isIsomorphicSetoid C)` of the image of its object-level topological support. -/
def coarseTSupport (φ : RoughForm I C F k) : Set (Quotient (isIsomorphicSetoid C)) :=
  closure (Quotient.mk (isIsomorphicSetoid C) '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)

/-- Definitional unfolding of the coarse topological support of a rough differential form. -/
theorem coarseTSupport_def (φ : RoughForm I C F k) :
    φ.coarseTSupport = closure (Quotient.mk (isIsomorphicSetoid C) ''
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ) := (rfl)

/-- The coarse topological support is closed in the coarse quotient. -/
theorem isClosed_coarseTSupport (φ : RoughForm I C F k) : IsClosed φ.coarseTSupport :=
  isClosed_closure

/-- The object-level topological support lies in the preimage of the coarse topological support. -/
theorem tsupport_subset_preimage_coarseTSupport (φ : RoughForm I C F k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ ⊆
      Quotient.mk (isIsomorphicSetoid C) ⁻¹' φ.coarseTSupport :=
  (Set.subset_preimage_image _ _).trans (Set.preimage_mono subset_closure)

/-- The coarse topological support of a rough form is empty if and only if the form is zero. -/
@[simp]
theorem coarseTSupport_eq_empty_iff {φ : RoughForm I C F k} : φ.coarseTSupport = ∅ ↔ φ = 0 := by
  rw [coarseTSupport_def, closure_empty_iff, Set.image_eq_empty]
  exact _root_.tsupport_eq_empty_iff (α := E [⋀^Fin k]→L[ℝ] F) (f := φ)

/-- The zero rough form has empty coarse topological support. -/
@[simp]
theorem coarseTSupport_zero : (0 : RoughForm I C F k).coarseTSupport = ∅ :=
  coarseTSupport_eq_empty_iff.mpr rfl

/-- Coarse topological support of a sum is contained in the union of the coarse supports. -/
theorem coarseTSupport_add_subset [ContinuousAdd F] (φ ψ : RoughForm I C F k) :
    (φ + ψ).coarseTSupport ⊆ φ.coarseTSupport ∪ ψ.coarseTSupport := by
  refine (closure_mono
    (Set.image_mono (_root_.tsupport_add (α := E [⋀^Fin k]→L[ℝ] F) φ ψ))).trans_eq ?_
  rw [Set.image_union, closure_union]; rfl

/-- Scalar multiplication does not enlarge coarse topological support. -/
theorem coarseTSupport_smul_subset [ContinuousConstSMul ℝ F] (c : ℝ) (φ : RoughForm I C F k) :
    (c • φ).coarseTSupport ⊆ φ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_smul_subset c φ))

/-- Multiplication by a nonzero scalar preserves coarse topological support. -/
theorem coarseTSupport_smul [ContinuousConstSMul ℝ F] (c : ℝ) (φ : RoughForm I C F k)
    (hc : c ≠ 0) : (c • φ).coarseTSupport = φ.coarseTSupport := by
  simp only [coarseTSupport_def, tsupport_smul c φ hc]

end Basic

section DifferentialAndWedge

variable {k l : ℕ}

/-- Exterior differentiation does not enlarge coarse topological support. -/
theorem coarseTSupport_mextDeriv_subset {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : RoughForm I C V k) : (TauCeti.mextDeriv φ).coarseTSupport ⊆ φ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_mextDeriv_subset φ))

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂]
  [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃)

/-- Paired wedge product is supported in the coarse support of its left factor. -/
theorem coarseTSupport_wedgeWith_subset_left (φ : RoughForm I C V₁ k) (ψ : RoughForm I C V₂ l) :
    (φ.wedgeWith μ ψ).coarseTSupport ⊆ φ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_wedgeWith_subset_left μ φ ψ))

/-- Paired wedge product is supported in the coarse support of its right factor. -/
theorem coarseTSupport_wedgeWith_subset_right (φ : RoughForm I C V₁ k) (ψ : RoughForm I C V₂ l) :
    (φ.wedgeWith μ ψ).coarseTSupport ⊆ ψ.coarseTSupport :=
  closure_mono (Set.image_mono (tsupport_wedgeWith_subset_right μ φ ψ))

end DifferentialAndWedge

end RoughForm

namespace SmoothForm

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [Category C] [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I 1 C] {k l : ℕ}

section SingleCoeff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The coarse topological support of a smooth differential form on the objects of `C`. -/
def coarseTSupport (φ : SmoothForm I C V k) : Set (Quotient (isIsomorphicSetoid C)) :=
  RoughForm.coarseTSupport (F := V) φ.val

/-- The coarse topological support of a smooth form is that of its underlying rough form. -/
theorem coarseTSupport_def (φ : SmoothForm I C V k) :
    φ.coarseTSupport = RoughForm.coarseTSupport (F := V) φ.val := (rfl)

/-- The coarse topological support of a smooth form is closed in the coarse quotient. -/
theorem isClosed_coarseTSupport (φ : SmoothForm I C V k) : _root_.IsClosed φ.coarseTSupport := by
  rw [coarseTSupport_def]; exact RoughForm.isClosed_coarseTSupport (I := I) (F := V) φ.val

/-- The object-level topological support of a smooth form lies in the preimage of its coarse
topological support. -/
theorem tsupport_subset_preimage_coarseTSupport (φ : SmoothForm I C V k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val ⊆
      Quotient.mk (isIsomorphicSetoid C) ⁻¹' φ.coarseTSupport :=
  RoughForm.tsupport_subset_preimage_coarseTSupport (I := I) (F := V) φ.val

/-- The zero smooth form has empty coarse topological support. -/
@[simp]
theorem coarseTSupport_zero : (0 : SmoothForm I C V k).coarseTSupport = ∅ :=
  RoughForm.coarseTSupport_zero

/-- A smooth form has empty coarse topological support if and only if it is zero. -/
@[simp]
theorem coarseTSupport_eq_empty_iff {φ : SmoothForm I C V k} : φ.coarseTSupport = ∅ ↔ φ = 0 := by
  rw [coarseTSupport_def, RoughForm.coarseTSupport_eq_empty_iff, Submodule.coe_eq_zero]

/-- Coarse topological support of a sum of smooth forms lies in the union of their supports. -/
theorem coarseTSupport_add_subset (φ ψ : SmoothForm I C V k) :
    (φ + ψ).coarseTSupport ⊆ φ.coarseTSupport ∪ ψ.coarseTSupport := by
  have h : ((φ + ψ : SmoothForm I C V k) : RoughForm I C V k) =
      (φ.val : RoughForm I C V k) + ψ.val :=
    funext fun _ ↦ ContinuousAlternatingMap.ext fun _ ↦ rfl
  simpa only [coarseTSupport_def, h] using RoughForm.coarseTSupport_add_subset (F := V) φ.val ψ.val

/-- Scalar multiplication does not enlarge the coarse topological support of a smooth form. -/
theorem coarseTSupport_smul_subset (c : ℝ) (φ : SmoothForm I C V k) :
    (c • φ).coarseTSupport ⊆ φ.coarseTSupport := by
  have h : ((c • φ : SmoothForm I C V k) : RoughForm I C V k) = c • (φ.val : RoughForm I C V k) :=
    funext fun _ ↦ ContinuousAlternatingMap.ext fun _ ↦ rfl
  simpa only [coarseTSupport_def, h] using RoughForm.coarseTSupport_smul_subset (F := V) c φ.val

/-- Multiplication by a nonzero scalar preserves the coarse support of a smooth form. -/
theorem coarseTSupport_smul (c : ℝ) (φ : SmoothForm I C V k) (hc : c ≠ 0) :
    (c • φ).coarseTSupport = φ.coarseTSupport := by
  have h : ((c • φ : SmoothForm I C V k) : RoughForm I C V k) = c • (φ.val : RoughForm I C V k) :=
    funext fun _ ↦ ContinuousAlternatingMap.ext fun _ ↦ rfl
  simpa only [coarseTSupport_def, h] using RoughForm.coarseTSupport_smul (F := V) c φ.val hc

/-- Exterior differentiation does not enlarge the coarse support of a smooth form. -/
theorem coarseTSupport_mextDerivₗ_subset [IsManifold I 2 C] (φ : SmoothForm I C V k) :
    (TauCeti.mextDerivₗ I k φ).coarseTSupport ⊆ φ.coarseTSupport := by
  rw [coarseTSupport_def, coarseTSupport_def, TauCeti.mextDerivₗ_apply]
  exact RoughForm.coarseTSupport_mextDeriv_subset (V := V) φ.val

end SingleCoeff

section Wedge

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂]
  [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃)

/-- Paired wedge product of smooth forms is supported in the coarse support of its left factor. -/
theorem coarseTSupport_wedgeWith_subset_left (φ : SmoothForm I C V₁ k) (ψ : SmoothForm I C V₂ l) :
    (SmoothForm.wedgeWith μ φ ψ).coarseTSupport ⊆ φ.coarseTSupport := by
  rw [coarseTSupport_def, coarseTSupport_def, SmoothForm.coe_wedgeWith]
  exact RoughForm.coarseTSupport_wedgeWith_subset_left μ φ.val ψ.val

/-- Paired wedge product of smooth forms is supported in the coarse support of its right factor. -/
theorem coarseTSupport_wedgeWith_subset_right (φ : SmoothForm I C V₁ k) (ψ : SmoothForm I C V₂ l) :
    (SmoothForm.wedgeWith μ φ ψ).coarseTSupport ⊆ ψ.coarseTSupport := by
  rw [coarseTSupport_def, coarseTSupport_def, SmoothForm.coe_wedgeWith]
  exact RoughForm.coarseTSupport_wedgeWith_subset_right μ φ.val ψ.val

end Wedge

/-- Wedge product of real-valued smooth forms is supported in its left factor's coarse support. -/
theorem coarseTSupport_wedge_subset_left (φ : SmoothForm I C ℝ k) (ψ : SmoothForm I C ℝ l) :
    (SmoothForm.wedge φ ψ).coarseTSupport ⊆ φ.coarseTSupport :=
  SmoothForm.wedge_def φ ψ ▸ coarseTSupport_wedgeWith_subset_left _ φ ψ

/-- Wedge product of real-valued smooth forms is supported in its right factor's coarse support. -/
theorem coarseTSupport_wedge_subset_right (φ : SmoothForm I C ℝ k) (ψ : SmoothForm I C ℝ l) :
    (SmoothForm.wedge φ ψ).coarseTSupport ⊆ ψ.coarseTSupport :=
  SmoothForm.wedge_def φ ψ ▸ coarseTSupport_wedgeWith_subset_right _ φ ψ

end SmoothForm

namespace Quiver

variable {E H A K C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [Category C] [TopologicalSpace C] [TopologicalSpace (_root_.Quiver.Total C)]
  [ChartedSpace H C] [ChartedSpace K (_root_.Quiver.Total C)]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ A K)
  [IsManifold I ∞ C] [IsManifold J ∞ (_root_.Quiver.Total C)]

section EtaleSaturation

variable {I J} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  (hs : IsLocalDiffeomorph J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
  {ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C)}
  {φ : SmoothForm I C V k} (hφ : φ ∈ invariantForms I J hs.contMDiff ht V k)

include hφ

/-- On a smooth category whose source is a local diffeomorphism and whose target is smooth, the
object-level topological support of an invariant form is saturated under isomorphism. -/
theorem preimage_image_tsupport_eq :
    Quotient.mk (isIsomorphicSetoid C) ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val) =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro y ⟨x, hx, hxy⟩
  -- Only a category structure is assumed, so unpack `Quotient.exact` rather than groupoid helpers.
  obtain ⟨e⟩ := Quotient.exact hxy
  have ha : (⟨x, y, e.hom⟩ : _root_.Quiver.Total C) ∈
      _root_.Quiver.Total.left ⁻¹' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val := hx
  rw [← RoughForm.tsupport_mpullback_eq_preimage (F := V) (k := k) φ.val hs.contMDiff.continuous
    hs.isOpenMap (hs.isInvertible_mfderiv (by simp))] at ha
  have hinv := congrArg Subtype.val (mem_invariantForms_iff.mp hφ)
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback] at hinv
  exact RoughForm.tsupport_mpullback_subset_preimage (F := V) (k := k) ht.continuous φ.val
    (hinv ▸ ha)

/-- On a smooth category whose source is a local diffeomorphism and whose target is smooth, the
image in the coarse quotient of the topological support of an invariant form is already closed. -/
theorem coarseTSupport_eq_image_tsupport :
    φ.coarseTSupport =
      Quotient.mk (isIsomorphicSetoid C) '' _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val :=
  IsClosed.closure_eq ((isQuotientMap_quotient_mk' (X := C)
    (s := isIsomorphicSetoid C)).isClosed_preimage.mp <|
      (preimage_image_tsupport_eq hs hφ).symm ▸
        _root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val)

/-- On a smooth category whose source is a local diffeomorphism and whose target is smooth, pulling
the coarse support of an invariant form back to objects recovers its exact topological support. -/
theorem preimage_coarseTSupport_eq_tsupport :
    Quotient.mk (isIsomorphicSetoid C) ⁻¹' φ.coarseTSupport =
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] V) φ.val := by
  rw [coarseTSupport_eq_image_tsupport hs hφ, preimage_image_tsupport_eq hs hφ]

end EtaleSaturation

section Submodule

variable (hs : ContMDiff J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C))

section SingleCoeff

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ)

/-- The submodule of invariant smooth `k`-forms whose coarse topological support is compact in
`Quotient (isIsomorphicSetoid C)`. -/
def compactlySupportedInvariantForms : Submodule ℝ (SmoothForm I C V k) where
  carrier := {φ | φ ∈ invariantForms I J hs ht V k ∧ IsCompact φ.coarseTSupport}
  zero_mem' := ⟨zero_mem _, by rw [SmoothForm.coarseTSupport_zero]; exact isCompact_empty⟩
  add_mem' hφ hψ := ⟨add_mem hφ.1 hψ.1, (hφ.2.union hψ.2).of_isClosed_subset
    (SmoothForm.isClosed_coarseTSupport _) (SmoothForm.coarseTSupport_add_subset _ _)⟩
  smul_mem' c φ hφ := ⟨Submodule.smul_mem _ c hφ.1, hφ.2.of_isClosed_subset
    (SmoothForm.isClosed_coarseTSupport _) (SmoothForm.coarseTSupport_smul_subset c _)⟩

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
    ⟨hφ, isCompact_univ.of_isClosed_subset (SmoothForm.isClosed_coarseTSupport _) (subset_univ _)⟩

/-- Exterior differentiation preserves compact-coarse-support invariant forms. -/
theorem mextDerivₗ_mem_compactlySupportedInvariantForms {φ : SmoothForm I C V k}
    (hφ : φ ∈ compactlySupportedInvariantForms I J hs ht V k) :
    mextDerivₗ I k φ ∈ compactlySupportedInvariantForms I J hs ht V (k + 1) :=
  ⟨mextDerivₗ_mem_invariantForms hφ.1, hφ.2.of_isClosed_subset
    (SmoothForm.isClosed_coarseTSupport _) (SmoothForm.coarseTSupport_mextDerivₗ_subset φ)⟩

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
  ext φ : 1
  exact Subtype.ext (LinearMap.congr_fun (TauCeti.mextDerivₗ_comp_mextDerivₗ I k) φ.val)

end SingleCoeff

variable {I J hs ht} {k l : ℕ}

section Wedge

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂]
  [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃)

/-- Paired wedge product of a compact-coarse-support invariant form on the left with any invariant
form on the right has compact coarse support. -/
theorem wedgeWith_mem_compactlySupportedInvariantForms_left {φ : SmoothForm I C V₁ k}
    {η : SmoothForm I C V₂ l} (hφ : φ ∈ compactlySupportedInvariantForms I J hs ht V₁ k)
    (hη : η ∈ invariantForms I J hs ht V₂ l) :
    SmoothForm.wedgeWith μ φ η ∈ compactlySupportedInvariantForms I J hs ht V₃ (k + l) :=
  ⟨wedgeWith_mem_invariantForms μ hφ.1 hη, hφ.2.of_isClosed_subset
    (SmoothForm.isClosed_coarseTSupport _) (SmoothForm.coarseTSupport_wedgeWith_subset_left μ φ η)⟩

/-- Paired wedge product of any invariant form on the left with a compact-coarse-support invariant
form on the right has compact coarse support. -/
theorem wedgeWith_mem_compactlySupportedInvariantForms_right {φ : SmoothForm I C V₁ k}
    {η : SmoothForm I C V₂ l} (hφ : φ ∈ invariantForms I J hs ht V₁ k)
    (hη : η ∈ compactlySupportedInvariantForms I J hs ht V₂ l) :
    SmoothForm.wedgeWith μ φ η ∈ compactlySupportedInvariantForms I J hs ht V₃ (k + l) :=
  ⟨wedgeWith_mem_invariantForms μ hφ hη.1, hη.2.of_isClosed_subset
    (SmoothForm.isClosed_coarseTSupport _)
    (SmoothForm.coarseTSupport_wedgeWith_subset_right μ φ η)⟩

end Wedge

/-- Wedge product of a real-valued compact-coarse-support invariant form on the left with any
invariant form has compact coarse support. -/
theorem wedge_mem_compactlySupportedInvariantForms_left {φ : SmoothForm I C ℝ k}
    {η : SmoothForm I C ℝ l} (hφ : φ ∈ compactlySupportedInvariantForms I J hs ht ℝ k)
    (hη : η ∈ invariantForms I J hs ht ℝ l) :
    SmoothForm.wedge φ η ∈ compactlySupportedInvariantForms I J hs ht ℝ (k + l) :=
  SmoothForm.wedge_def φ η ▸ wedgeWith_mem_compactlySupportedInvariantForms_left _ hφ hη

/-- Wedge product of any real-valued invariant form on the left with a compact-coarse-support
invariant form on the right has compact coarse support. -/
theorem wedge_mem_compactlySupportedInvariantForms_right {φ : SmoothForm I C ℝ k}
    {η : SmoothForm I C ℝ l} (hφ : φ ∈ invariantForms I J hs ht ℝ k)
    (hη : η ∈ compactlySupportedInvariantForms I J hs ht ℝ l) :
    SmoothForm.wedge φ η ∈ compactlySupportedInvariantForms I J hs ht ℝ (k + l) :=
  SmoothForm.wedge_def φ η ▸ wedgeWith_mem_compactlySupportedInvariantForms_right _ hφ hη

end Submodule

end Quiver

end TauCeti

section Functoriality

universe v u

open TauCeti
open TauCeti.Quiver (invariantForms compactlySupportedInvariantForms
  compactlySupportedInvariantForms_le_invariantForms
  wedgeWith_mem_compactlySupportedInvariantForms_left
  wedgeWith_mem_compactlySupportedInvariantForms_right
  wedge_mem_compactlySupportedInvariantForms_left
  wedge_mem_compactlySupportedInvariantForms_right)

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {C D : Type u} [Category.{v} C] [Category.{v} D] [TopologicalSpace C] [TopologicalSpace D]
  [ChartedSpace H C] [ChartedSpace H' D]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {k : ℕ}

namespace CategoryTheory.Functor

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

/-- Along a functor into a smooth category with locally diffeomorphic source and smooth target whose
object map is a local diffeomorphism, the coarse support of the pullback of an invariant form is
the exact preimage of its coarse support. -/
theorem coarseTSupport_mpullback_eq_preimage {A' K' : Type*}
    [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']
    [TopologicalSpace (Quiver.Total D)] [ChartedSpace K' (Quiver.Total D)]
    {J' : ModelWithCorners ℝ A' K'} [IsManifold I ∞ C] [IsManifold I' ∞ D]
    [IsManifold J' ∞ (Quiver.Total D)] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : C ⥤ D) (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) {φ : SmoothForm I' D V k}
    (hφ : φ ∈ invariantForms I' J' hs'.contMDiff ht' V k) :
    (SmoothForm.mpullback Φ.obj hΦ.contMDiff φ).coarseTSupport =
      isomorphismClasses.map Φ.toCatHom ⁻¹' φ.coarseTSupport := by
  rw [SmoothForm.coarseTSupport_def, SmoothForm.coe_mpullback]
  refine (Φ.coarseTSupport_mpullback_subset_preimage (I := I) (F := V)
    hΦ.contMDiff.continuous φ.val).antisymm fun q hq ↦ ?_
  induction q using Quotient.inductionOn with
  | h x =>
    have hΦx : Φ.obj x ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] V) φ.val := by
      rwa [← TauCeti.Quiver.preimage_coarseTSupport_eq_tsupport hs' hφ]
    refine subset_closure ⟨x, ?_, rfl⟩
    rwa [RoughForm.tsupport_mpullback_eq_preimage (F := V) (k := k) φ.val hΦ.contMDiff.continuous
      hΦ.isOpenMap (hΦ.isInvertible_mfderiv (by simp))]

end CategoryTheory.Functor

namespace TauCeti.SmoothForm

/-- Along a functor with smooth object map, the coarse support of a pulled-back smooth form lies in
the preimage of the original coarse support under the induced map on isomorphism classes. -/
theorem coarseTSupport_mpullback_subset_preimage [IsManifold I 1 C] [IsManifold I' 1 D]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : C ⥤ D) (hΦ : ContMDiff I I' ∞ Φ.obj) (φ : SmoothForm I' D V k) :
    (SmoothForm.mpullback Φ.obj hΦ φ).coarseTSupport ⊆
      isomorphismClasses.map Φ.toCatHom ⁻¹' φ.coarseTSupport := by
  rw [SmoothForm.coarseTSupport_def, SmoothForm.coe_mpullback]
  exact Φ.coarseTSupport_mpullback_subset_preimage (I := I) (F := V) hΦ.continuous φ.val

end TauCeti.SmoothForm

section SmoothPresentations

variable {A K A' K' : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']
  [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
  [ChartedSpace K (Quiver.Total C)] [ChartedSpace K' (Quiver.Total D)]
  {J : ModelWithCorners ℝ A K} {J' : ModelWithCorners ℝ A' K'}
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]

namespace CategoryTheory.Functor

section ProperPullback

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}

/-- Smooth pullback preserves compact coarse support whenever the preimage of the form's coarse
support under the induced coarse map is compact. -/
theorem mpullback_mem_compactlySupportedInvariantForms_of_isCompact_preimage (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    {φ : SmoothForm I' D V k} (hφ : φ ∈ invariantForms I' J' hs' ht' V k)
    (hc : IsCompact (X := Quotient (isIsomorphicSetoid C))
      (isomorphismClasses.map Φ.toCatHom ⁻¹' φ.coarseTSupport)) :
    SmoothForm.mpullback Φ.obj hΦ φ ∈ compactlySupportedInvariantForms I J hs ht V k :=
  ⟨Φ.toPrefunctor.mpullback_mem_invariantForms hΦ hΦ₁ hφ,
    hc.of_isClosed_subset (SmoothForm.isClosed_coarseTSupport _)
      (SmoothForm.coarseTSupport_mpullback_subset_preimage Φ hΦ φ)⟩

section SingleProper

variable (Φ : C ⥤ D) (hΦ : ContMDiff I I' ∞ Φ.obj)
  (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
  (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
    (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))

include Φ hΦ hΦ₁ hp

/-- Smooth pullback along a functor whose induced coarse map is proper preserves compact coarse
support on invariant forms. -/
theorem mpullback_mem_compactlySupportedInvariantForms {φ : SmoothForm I' D V k}
    (hφ : φ ∈ compactlySupportedInvariantForms I' J' hs' ht' V k) :
    SmoothForm.mpullback Φ.obj hΦ φ ∈ compactlySupportedInvariantForms I J hs ht V k :=
  Φ.mpullback_mem_compactlySupportedInvariantForms_of_isCompact_preimage hΦ hΦ₁ hφ.1
    (hp.isCompact_preimage hφ.2)

/-- Contravariant pullback on compact-coarse-support invariant forms along a smooth functor whose
induced map on isomorphism classes is proper. -/
def compactlySupportedInvariantFormsPullback :
    compactlySupportedInvariantForms I' J' hs' ht' V k →ₗ[ℝ]
      compactlySupportedInvariantForms I J hs ht V k :=
  (SmoothForm.mpullback Φ.obj hΦ).restrict fun _ ↦
    Φ.mpullback_mem_compactlySupportedInvariantForms hΦ hΦ₁ hp

/-- Pullback of a compact-coarse-support invariant form agrees with object-level smooth pullback. -/
@[simp]
theorem coe_compactlySupportedInvariantFormsPullback
    (φ : compactlySupportedInvariantForms I' J' hs' ht' V k) :
    (Φ.compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht) hΦ hΦ₁ hp φ :
      SmoothForm I C V k) = SmoothForm.mpullback Φ.obj hΦ φ := (rfl)

/-- Pullback of compact-coarse-support invariant forms commutes with exterior differentiation. -/
theorem mextDerivₗ_compactlySupportedInvariantFormsPullback
    (φ : compactlySupportedInvariantForms I' J' hs' ht' V k) :
    compactlySupportedInvariantForms.mextDerivₗ I J hs ht V k
        (Φ.compactlySupportedInvariantFormsPullback hΦ hΦ₁ hp φ) =
      Φ.compactlySupportedInvariantFormsPullback hΦ hΦ₁ hp
        (compactlySupportedInvariantForms.mextDerivₗ I' J' hs' ht' V k φ) :=
  Subtype.ext (SmoothForm.mextDerivₗ_mpullback _ _ k φ.val)

end SingleProper

/-- The identity functor acts as the identity on compact-coarse-support invariant forms. -/
@[simp]
theorem compactlySupportedInvariantFormsPullback_id :
    (𝟭 C).compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht) (hs' := hs) (ht' := ht)
        (V := V) (k := k) contMDiff_id contMDiff_id isProperMap_isomorphismClasses_map_id =
      LinearMap.id :=
  LinearMap.ext fun φ ↦ Subtype.ext (LinearMap.congr_fun SmoothForm.mpullback_id φ.val)

end ProperPullback

section EtaleEquiv

variable [IsGroupoid D] [TauCeti.IsTopologicalGroupoid D]

/-- Descent of an invariant form along an étale refinement transports its coarse support by the
induced map on isomorphism classes. -/
theorem coarseTSupport_invariantFormsEquiv_symm {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (α : invariantForms I J hs.contMDiff ht V k) :
    ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val.coarseTSupport =
      isomorphismClasses.map Φ.toCatHom '' α.val.coarseTSupport := by
  let β := (Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α
  have hpre :
      isomorphismClasses.map Φ.toCatHom ⁻¹' β.val.coarseTSupport = α.val.coarseTSupport := by
    rw [← Φ.coarseTSupport_mpullback_eq_preimage hs' hΦ β.property,
      Φ.mpullback_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ α]
  exact hpre ▸ (Φ.isomorphismClasses_map_surjective.image_preimage _).symm

section EquivAPI

variable (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
  (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
  (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
  (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
  (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)

section SingleCoeff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Étale-refinement descent of compact-coarse-support invariant forms.** A full, essentially
surjective étale refinement reflecting isomorphisms into a topological smooth groupoid induces a
coarse homeomorphism and therefore a linear equivalence on invariant forms with compact coarse
support. -/
def compactlySupportedInvariantFormsEquiv :
    compactlySupportedInvariantForms I' J' hs'.contMDiff ht'.contMDiff V k ≃ₗ[ℝ]
      compactlySupportedInvariantForms I J hs.contMDiff ht V k :=
  let e := Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁
  let p := (compactlySupportedInvariantForms I' J' hs'.contMDiff ht'.contMDiff V k).submoduleOf
    (invariantForms I' J' hs'.contMDiff ht'.contMDiff V k)
  let q := (compactlySupportedInvariantForms I J hs.contMDiff ht V k).submoduleOf
    (invariantForms I J hs.contMDiff ht V k)
  let hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom) :=
    Φ.isProperMap_isomorphismClasses_map_of_essSurj hΦ.contMDiff.continuous hΦ.isOpenMap
      (@TauCeti.isOpenQuotientMap_isomorphismClassesMk _ Groupoid.ofIsGroupoid _ _
        hs'.contMDiff.continuous ht'.isOpenMap).isOpenMap
  have hmap : p.map (e : _ →ₗ[ℝ] _) = q := by
    refine le_antisymm ?_ ?_
    · rintro α ⟨φ, hφ, rfl⟩
      change (e φ).val ∈ compactlySupportedInvariantForms I J hs.contMDiff ht V k
      dsimp only [e]
      rw [invariantFormsEquiv_apply, Prefunctor.coe_invariantFormsPullback]
      exact Φ.mpullback_mem_compactlySupportedInvariantForms hΦ.contMDiff hΦ₁ hp hφ
    · intro α hα
      refine ⟨e.symm α, ⟨(e.symm α).property, ?_⟩, e.apply_symm_apply α⟩
      change ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val.coarseTSupport |> IsCompact
      rw [Φ.coarseTSupport_invariantFormsEquiv_symm hs ht hs' ht' hΦ hΦ₁ α]
      exact hα.2.image (Φ.continuous_isomorphismClasses_map hΦ.contMDiff.continuous)
  (Submodule.submoduleOfEquivOfLe compactlySupportedInvariantForms_le_invariantForms).symm.trans
    ((e.ofSubmodules p q hmap).trans
      (Submodule.submoduleOfEquivOfLe compactlySupportedInvariantForms_le_invariantForms))

/-- Applying `compactlySupportedInvariantFormsEquiv` computes pullback along `Φ`. -/
@[simp]
theorem compactlySupportedInvariantFormsEquiv_apply
    (φ : compactlySupportedInvariantForms I' J' hs'.contMDiff ht'.contMDiff V k) :
    Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁ φ =
      Φ.compactlySupportedInvariantFormsPullback hΦ.contMDiff hΦ₁
        (Φ.isProperMap_isomorphismClasses_map_of_essSurj hΦ.contMDiff.continuous hΦ.isOpenMap
          (@TauCeti.isOpenQuotientMap_isomorphismClassesMk _ Groupoid.ofIsGroupoid _ _
            hs'.contMDiff.continuous ht'.isOpenMap).isOpenMap) φ := by
  apply Subtype.ext
  change ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁
    ⟨φ.val, compactlySupportedInvariantForms_le_invariantForms φ.property⟩ :
      invariantForms I J hs.contMDiff ht V k) : SmoothForm I C V k) = _
  rw [Φ.invariantFormsEquiv_apply, Prefunctor.coe_invariantFormsPullback,
    coe_compactlySupportedInvariantFormsPullback]; rfl

/-- The descended compact-coarse-support form has the same underlying smooth form as ordinary
invariant-form descent. -/
@[simp]
theorem coe_compactlySupportedInvariantFormsEquiv_symm
    (α : compactlySupportedInvariantForms I J hs.contMDiff ht V k) :
    ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α :
        SmoothForm I' D V k) =
      ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm
        ⟨α.val, compactlySupportedInvariantForms_le_invariantForms α.property⟩).val :=
  congrArg Subtype.val (LinearEquiv.ofSubmodules_symm_apply
    (e := Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁) _
    ⟨⟨α.val, compactlySupportedInvariantForms_le_invariantForms α.property⟩, α.property⟩)

/-- Pulling a descended compact-coarse-support form back along `Φ` recovers the original form. -/
theorem mpullback_compactlySupportedInvariantFormsEquiv_symm
    (α : compactlySupportedInvariantForms I J hs.contMDiff ht V k) :
    SmoothForm.mpullback Φ.obj hΦ.contMDiff
      ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val = α.val := by
  rw [coe_compactlySupportedInvariantFormsEquiv_symm, mpullback_invariantFormsEquiv_symm]

/-- Descent of a compact-coarse-support invariant form transports its coarse support by the induced
map on isomorphism classes. -/
theorem coarseTSupport_compactlySupportedInvariantFormsEquiv_symm
    (α : compactlySupportedInvariantForms I J hs.contMDiff ht V k) :
    ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val.coarseTSupport =
      isomorphismClasses.map Φ.toCatHom '' α.val.coarseTSupport := by
  rw [coe_compactlySupportedInvariantFormsEquiv_symm, coarseTSupport_invariantFormsEquiv_symm]

/-- Descent of compact-coarse-support invariant forms commutes with exterior differentiation. -/
theorem compactlySupportedInvariantFormsEquiv_symm_mextDerivₗ
    (α : compactlySupportedInvariantForms I J hs.contMDiff ht V k) :
    (Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm
        (compactlySupportedInvariantForms.mextDerivₗ I J hs.contMDiff ht V k α) =
      compactlySupportedInvariantForms.mextDerivₗ I' J' hs'.contMDiff ht'.contMDiff V k
        ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α) := by
  rw [LinearEquiv.symm_apply_eq, compactlySupportedInvariantFormsEquiv_apply,
    ← Φ.mextDerivₗ_compactlySupportedInvariantFormsPullback hΦ.contMDiff hΦ₁,
    ← Φ.compactlySupportedInvariantFormsEquiv_apply hs ht hs' ht' hΦ hΦ₁,
    LinearEquiv.apply_symm_apply]

end SingleCoeff

section Wedge

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [NormedAddCommGroup V₂]
  [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] {l : ℕ}
  (μ : V₁ →L[ℝ] V₂ →L[ℝ] V₃)

/-- Descent commutes with pairing a compact-coarse-support form on the left with any invariant form
on the right. -/
theorem compactlySupportedInvariantFormsEquiv_symm_wedgeWith_left
    (α : compactlySupportedInvariantForms I J hs.contMDiff ht V₁ k)
    (β : invariantForms I J hs.contMDiff ht V₂ l) :
    (((Φ.compactlySupportedInvariantFormsEquiv (V := V₃) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedgeWith μ α.val β.val,
          wedgeWith_mem_compactlySupportedInvariantForms_left μ α.property β.property⟩).val :
        SmoothForm I' D V₃ (k + l)) =
      SmoothForm.wedgeWith μ
        ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).val := by
  rw [coe_compactlySupportedInvariantFormsEquiv_symm,
    coe_compactlySupportedInvariantFormsEquiv_symm]
  exact Φ.invariantFormsEquiv_symm_wedgeWith hs ht hs' ht' hΦ hΦ₁ μ ⟨α.val, α.property.1⟩ β

/-- Descent commutes with pairing any invariant form on the left with a compact-coarse-support form
on the right. -/
theorem compactlySupportedInvariantFormsEquiv_symm_wedgeWith_right
    (α : invariantForms I J hs.contMDiff ht V₁ k)
    (β : compactlySupportedInvariantForms I J hs.contMDiff ht V₂ l) :
    (((Φ.compactlySupportedInvariantFormsEquiv (V := V₃) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedgeWith μ α.val β.val,
          wedgeWith_mem_compactlySupportedInvariantForms_right μ α.property β.property⟩).val :
        SmoothForm I' D V₃ (k + l)) =
      SmoothForm.wedgeWith μ ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val
        ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).val := by
  rw [coe_compactlySupportedInvariantFormsEquiv_symm,
    coe_compactlySupportedInvariantFormsEquiv_symm]
  exact Φ.invariantFormsEquiv_symm_wedgeWith hs ht hs' ht' hΦ hΦ₁ μ α ⟨β.val, β.property.1⟩

end Wedge

/-- Descent commutes with wedging a real-valued compact-coarse-support invariant form on the left
with any invariant form on the right. -/
theorem compactlySupportedInvariantFormsEquiv_symm_wedge_left {l : ℕ}
    (α : compactlySupportedInvariantForms I J hs.contMDiff ht ℝ k)
    (β : invariantForms I J hs.contMDiff ht ℝ l) :
    (((Φ.compactlySupportedInvariantFormsEquiv (V := ℝ) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedge α.val β.val,
          wedge_mem_compactlySupportedInvariantForms_left α.property β.property⟩).val :
        SmoothForm I' D ℝ (k + l)) =
      SmoothForm.wedge ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val
        ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).val := by
  simp only [SmoothForm.wedge_def]
  exact Φ.compactlySupportedInvariantFormsEquiv_symm_wedgeWith_left hs ht hs' ht' hΦ hΦ₁ _ α β

/-- Descent commutes with wedging any real-valued invariant form on the left with a
compact-coarse-support invariant form on the right. -/
theorem compactlySupportedInvariantFormsEquiv_symm_wedge_right {l : ℕ}
    (α : invariantForms I J hs.contMDiff ht ℝ k)
    (β : compactlySupportedInvariantForms I J hs.contMDiff ht ℝ l) :
    (((Φ.compactlySupportedInvariantFormsEquiv (V := ℝ) (k := k + l) hs ht hs' ht' hΦ hΦ₁).symm
        ⟨SmoothForm.wedge α.val β.val,
          wedge_mem_compactlySupportedInvariantForms_right α.property β.property⟩).val :
        SmoothForm I' D ℝ (k + l)) =
      SmoothForm.wedge ((Φ.invariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm α).val
        ((Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁).symm β).val := by
  simp only [SmoothForm.wedge_def]
  exact Φ.compactlySupportedInvariantFormsEquiv_symm_wedgeWith_right hs ht hs' ht' hΦ hΦ₁ _ α β

end EquivAPI

/-- The identity refinement induces the identity equivalence on compact-coarse-support invariant
forms. -/
@[simp]
theorem compactlySupportedInvariantFormsEquiv_id {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [IsGroupoid C] [TauCeti.IsTopologicalGroupoid C]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (h : IsLocalDiffeomorph I I ∞ (𝟭 C).obj)
    (h₁ : ContMDiff J J ∞ (𝟭 C).toPrefunctor.mapTotal) :
    (𝟭 C).compactlySupportedInvariantFormsEquiv (V := V) (k := k) hs ht.contMDiff hs ht h h₁ =
      LinearEquiv.refl ℝ _ :=
  LinearEquiv.ext fun φ ↦ by
    simp only [compactlySupportedInvariantFormsEquiv_apply,
      compactlySupportedInvariantFormsPullback_id, LinearMap.id_apply, LinearEquiv.refl_apply]

end EtaleEquiv

section Comp

variable {E'' H'' A'' K'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] [NormedAddCommGroup A''] [NormedSpace ℝ A''] [TopologicalSpace K'']
  {B : Type u} [Category.{v} B] [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
  [ChartedSpace H'' B] [ChartedSpace K'' (Quiver.Total B)]
  {I'' : ModelWithCorners ℝ E'' H''} {J'' : ModelWithCorners ℝ A'' K''}
  [IsManifold I'' ∞ B] [IsManifold J'' ∞ (Quiver.Total B)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pullback on compact-coarse-support invariant forms reverses composition of smooth functors with
proper coarse maps. -/
theorem compactlySupportedInvariantFormsPullback_comp
    {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
    {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
    {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
    {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
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
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ₁.comp hΦ₁)
        (isProperMap_isomorphismClasses_map_comp Φ Ψ hpΦ hpΨ) =
      (Φ.compactlySupportedInvariantFormsPullback (hs' := hs') (ht' := ht') hΦ hΦ₁ hpΦ).comp
        (Ψ.compactlySupportedInvariantFormsPullback hΨ hΨ₁ hpΨ) :=
  LinearMap.ext fun φ ↦ Subtype.ext (SmoothForm.mpullback_mpullback _ _ hΦ hΨ φ.val).symm

/-- Composing étale refinements reflecting isomorphisms reverses composition of their equivalences
on compact-coarse-support invariant forms. -/
theorem compactlySupportedInvariantFormsEquiv_comp [IsGroupoid D] [TauCeti.IsTopologicalGroupoid D]
    [IsGroupoid B] [TauCeti.IsTopologicalGroupoid B] (Φ : C ⥤ D) (Ψ : D ⥤ B)
    [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms] [Ψ.Full] [Ψ.EssSurj] [Ψ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hs'' : IsLocalDiffeomorph J'' I'' ∞ (Quiver.Total.left : Quiver.Total B → B))
    (ht'' : IsLocalDiffeomorph J'' I'' ∞ (Quiver.Total.right : Quiver.Total B → B))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ : IsLocalDiffeomorph I' I'' ∞ Ψ.obj) (hΨ₁ : ContMDiff J' J'' ∞ Ψ.toPrefunctor.mapTotal) :
    (Φ ⋙ Ψ).compactlySupportedInvariantFormsEquiv (V := V) (k := k) hs ht hs'' ht''
        (fun x ↦ (hΦ x).comp I'' B (hΨ (Φ.obj x)))
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ₁.comp hΦ₁) =
      (Ψ.compactlySupportedInvariantFormsEquiv hs' ht'.contMDiff hs'' ht'' hΨ hΨ₁).trans
        (Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁) :=
  LinearEquiv.ext fun φ ↦ Subtype.ext <| by
    rw [(Φ ⋙ Ψ).compactlySupportedInvariantFormsEquiv_apply hs ht hs'' ht''
        (fun x ↦ (hΦ x).comp I'' B (hΨ (Φ.obj x)))
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ₁.comp hΦ₁),
      LinearEquiv.trans_apply,
      Ψ.compactlySupportedInvariantFormsEquiv_apply hs' ht'.contMDiff hs'' ht'' hΨ hΨ₁,
      Φ.compactlySupportedInvariantFormsEquiv_apply hs ht hs' ht' hΦ hΦ₁]
    exact (SmoothForm.mpullback_mpullback _ _ hΦ.contMDiff hΨ.contMDiff φ.val).symm

end Comp

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ Ψ : C ⥤ D}

/-- Smoothly naturally related functors with proper coarse maps induce equal pullbacks on
compact-coarse-support invariant forms. -/
theorem compactlySupportedInvariantFormsPullback_eq
    {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
    {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
    {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
    {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)} (η : Φ ⟶ Ψ)
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
  LinearMap.ext fun φ ↦ Subtype.ext (η.mpullback_eq_of_mem_invariantForms hΦ hΨ hη φ.property.1)

/-- Smoothly naturally related étale refinements reflecting isomorphisms induce the same
equivalence on compact-coarse-support invariant forms. -/
theorem compactlySupportedInvariantFormsEquiv_eq [IsGroupoid D] [TauCeti.IsTopologicalGroupoid D]
    [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
    [Ψ.Full] [Ψ.EssSurj] [Ψ.ReflectsIsomorphisms] (η : Φ ⟶ Ψ)
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΨ : IsLocalDiffeomorph I I' ∞ Ψ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ₁ : ContMDiff J J' ∞ Ψ.toPrefunctor.mapTotal)
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D)) :
    Φ.compactlySupportedInvariantFormsEquiv (V := V) (k := k) hs ht hs' ht' hΦ hΦ₁ =
      Ψ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΨ hΨ₁ :=
  LinearEquiv.ext fun φ ↦ Subtype.ext <| by
    simp only [Functor.compactlySupportedInvariantFormsEquiv_apply,
      Functor.coe_compactlySupportedInvariantFormsPullback]
    exact η.mpullback_eq_of_mem_invariantForms hΦ.contMDiff hΨ.contMDiff hη φ.property.1

end CategoryTheory.NatTrans

end SmoothPresentations

end Functoriality

namespace TauCeti

/-- If the coarse space of `C` is noncompact while the coarse space of `D` is compact, then for any
nontrivial coefficient space `V` and any smooth map `f : C → D`, some compact-coarse-support
invariant `0`-form on `D` pulls back along `f` to a `0`-form on `C` without compact coarse
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
    (f : C → D) (hf : ContMDiff I I' ∞ f) :
    ∃ φ ∈ Quiver.compactlySupportedInvariantForms I' J' hs' ht' V 0,
      SmoothForm.mpullback f hf φ ∉ Quiver.compactlySupportedInvariantForms I J hs ht V 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let φ : SmoothForm I' D V 0 := SmoothForm.ofFunction ⟨fun _ ↦ v, contMDiff_const⟩
  have hφ_coe : (φ : RoughForm I' D V 0) = RoughForm.ofFunction I' fun _ ↦ v :=
    SmoothForm.coe_ofFunction ⟨fun _ ↦ v, contMDiff_const⟩
  have hφ_inv : φ ∈ Quiver.invariantForms I' J' hs' ht' V 0 := by
    rw [Quiver.mem_invariantForms_iff]; refine Subtype.ext ?_
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, hφ_coe,
      mpullback_ofFunction, mpullback_ofFunction]; rfl
  refine ⟨φ, by rwa [Quiver.compactlySupportedInvariantForms_eq_invariantForms],
    fun hmem ↦ hnc ⟨?_⟩⟩
  have huniv : (SmoothForm.mpullback f hf φ).coarseTSupport = Set.univ :=
    Set.eq_univ_iff_forall.mpr <| Quotient.ind fun x ↦
      subset_closure ⟨x, subset_tsupport (α := E [⋀^Fin 0]→L[ℝ] V) _ fun h0 ↦ hv <| by
        have hp : ((SmoothForm.mpullback f hf φ).val x : E [⋀^Fin 0]→L[ℝ] V) 0 = v := by
          rw [SmoothForm.coe_mpullback, hφ_coe, mpullback_ofFunction]
          exact RoughForm.ofFunction_apply (I := I) (fun _ ↦ v) x 0
        exact hp.symm.trans (congrArg (· 0) h0), rfl⟩
  exact huniv ▸ hmem.2

end TauCeti
