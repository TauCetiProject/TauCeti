/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.Compression
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Small
import TauCeti.Analysis.InnerProductSpace.PartialIsometry
import TauCeti.Topology.Algebra.Module.Span

/-!
# Hilbert subrepresentations and universe bounds for star-algebra representations

Let `π` be a representation of a (unital or nonunital) star algebra `A` over `𝕜` (`[RCLike 𝕜]`) by
bounded operators on a Hilbert space `H`, and let `V : K →ₗᵢ[𝕜] H` be a linear isometry whose range
is invariant under every `π a`. Compressing `π a` to `V† (π a) V` defines a representation on `K`
(`NonUnitalStarAlgHom.restrictLinearIsometry` and `StarAlgHom.restrictLinearIsometry`), intertwined
with `π` by `V` and bounded in operator norm by `‖π a‖`. No norm or topology is required on `A`.

When `A` is `w`-small, every vector `ξ : H` lies in the range of a `π`-invariant linear isometry
from `lp (fun _ : ι => 𝕜) 2` for some index type `ι : Type w`, whatever the universe of `H`
(`NonUnitalStarAlgHom.exists_linearIsometry_mapsTo_mem_range` and
`StarAlgHom.exists_linearIsometry_mapsTo_mem_range`). Indeed, the closed linear span of
`{ξ} ∪ {π a ξ | a : A}` is `π`-invariant, contains `ξ`, and is the closure of the span of a
`w`-small set, so it is `w`-small and admits an orthonormal Hilbert basis indexed in universe `w`.
Consequently, operator-norm suprema over all Hilbert-space representations of `A` are already
attained on `ℓ²` spaces indexed in `A`'s universe.

## Main definitions

* `NonUnitalStarAlgHom.restrictLinearIsometry`: compression of `π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)` along a
  `π`-invariant linear isometry `V : K →ₗᵢ[𝕜] H`.
* `StarAlgHom.restrictLinearIsometry`: unital counterpart for `π : A →⋆ₐ[𝕜] (H →L[𝕜] H)`.

## Main statements

* `NonUnitalStarAlgHom.restrictLinearIsometry_apply` and `StarAlgHom.restrictLinearIsometry_apply`:
  `V` intertwines the compressed representation with `π`.
* `NonUnitalStarAlgHom.exists_linearIsometry_mapsTo_mem_range` and
  `StarAlgHom.exists_linearIsometry_mapsTo_mem_range`: for `[Small.{w} A]`, every `ξ : H` lies in a
  `π`-invariant subspace isometric to `lp (fun _ : ι => 𝕜) 2` with `ι : Type w`.

## References

* J. Dixmier, *C*-Algebras*, §2.3 (subrepresentations and cyclic subspaces).
* D. Williams, *Crossed Products of C*-Algebras*, Chapter 2 (reduction of universal norms to small
  cyclic representations).
-/

public section

noncomputable section

open scoped InnerProductSpace

universe w

namespace NonUnitalStarAlgHom

section Restrict

variable {𝕜 A H K : Type*} [RCLike 𝕜] [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  (π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)) {V : K →ₗᵢ[𝕜] H}
  (hπ : ∀ a, Set.MapsTo (π a) (Set.range V) (Set.range V))

/-- Compress a nonunital star-algebra representation `π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)` along a linear
isometry `V : K →ₗᵢ[𝕜] H` whose range is `π`-invariant. -/
def restrictLinearIsometry : A →⋆ₙₐ[𝕜] (K →L[𝕜] K) where
  toFun a := (π a).compression V.toContinuousLinearMap
  map_smul' c a := by simp
  map_zero' := by simp
  map_add' a b := by simp
  map_mul' a b := by
    simp only [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.compression_def]
    exact V.isPartialIsometry_toContinuousLinearMap.adjoint_comp_comp_comp_of_mapsTo _ (hπ b)
  map_star' a := by
    simp only [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_compression]

theorem restrictLinearIsometry_def (a : A) :
    π.restrictLinearIsometry hπ a = (π a).compression V.toContinuousLinearMap :=
  (rfl)

/-- The invariant linear isometry `V` intertwines `π.restrictLinearIsometry hπ` with `π`. -/
@[simp]
theorem restrictLinearIsometry_apply (a : A) (x : K) :
    V (π.restrictLinearIsometry hπ a x) = π a (V x) :=
  (congrArg V ((π a).compression_apply V.toContinuousLinearMap x)).trans
    (V.apply_adjoint_apply_of_mem_range (hπ a ⟨x, rfl⟩))

/-- Compressing a representation along an invariant linear isometry does not increase operator
norms. -/
theorem norm_restrictLinearIsometry_le (a : A) :
    ‖π.restrictLinearIsometry hπ a‖ ≤ ‖π a‖ :=
  (π.restrictLinearIsometry hπ a).opNorm_le_bound (norm_nonneg (π a)) fun x => by
    rw [← V.norm_map (π.restrictLinearIsometry hπ a x), π.restrictLinearIsometry_apply hπ,
      ← V.norm_map x]
    exact (π a).le_opNorm (V x)

end Restrict

/-- If `A` is `w`-small and `𝕜` is `w`-small (for instance `𝕜 = ℂ` or `𝕜 = ℝ` in any universe
`w`), every vector `ξ : H` lies in the range of a `π`-invariant linear isometry from
`lp (fun _ : ι => 𝕜) 2` for some `ι : Type w`, regardless of the universe of `H`. -/
theorem exists_linearIsometry_mapsTo_mem_range {𝕜 A H : Type*} [RCLike 𝕜]
    [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Small.{w} A] [Small.{w} 𝕜]
    (π : A →⋆ₙₐ[𝕜] (H →L[𝕜] H)) (ξ : H) :
    ∃ (ι : Type w) (V : lp (fun _ : ι => 𝕜) 2 →ₗᵢ[𝕜] H),
      (∀ a, Set.MapsTo (π a) (Set.range V) (Set.range V)) ∧ ξ ∈ Set.range V := by
  let gen : Option A → H := fun o => o.elim ξ fun a => π a ξ
  have : Small.{w} (Option A) := ⟨Option (Shrink.{w} A), ⟨Equiv.optionCongr (equivShrink.{w} A)⟩⟩
  have : Small.{w} (Set.range gen) := small_range.{w} gen
  obtain ⟨ι, V, hV⟩ :=
    TauCeti.exists_linearIsometry_range_eq_topologicalClosure_span.{w} 𝕜 (Set.range gen)
  refine ⟨ι, V, fun a => ?_, ?_⟩
  · rw [hV]
    refine LinearMap.mapsTo_topologicalClosure_span (f := (π a : H →ₗ[𝕜] H)) (π a).continuous ?_
    rintro _ ⟨o, rfl⟩
    cases o with
    | none => exact Submodule.subset_span ⟨some a, rfl⟩
    | some b => exact Submodule.subset_span ⟨some (a * b), by simp [gen, map_mul]⟩
  · rw [hV]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨none, rfl⟩)

end NonUnitalStarAlgHom

namespace StarAlgHom

section Restrict

variable {𝕜 A H K : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [Algebra 𝕜 A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  (π : A →⋆ₐ[𝕜] (H →L[𝕜] H)) {V : K →ₗᵢ[𝕜] H}
  (hπ : ∀ a, Set.MapsTo (π a) (Set.range V) (Set.range V))

/-- Compress a unital star-algebra representation `π : A →⋆ₐ[𝕜] (H →L[𝕜] H)` along a linear
isometry `V : K →ₗᵢ[𝕜] H` whose range is `π`-invariant. -/
def restrictLinearIsometry : A →⋆ₐ[𝕜] (K →L[𝕜] K) where
  toFun a := (π a).compression V.toContinuousLinearMap
  map_one' := by simp
  map_mul' a b := (π.toNonUnitalStarAlgHom.restrictLinearIsometry hπ).map_mul' a b
  map_zero' := by simp
  map_add' a b := by simp
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := (π.toNonUnitalStarAlgHom.restrictLinearIsometry hπ).map_star' a

@[simp]
theorem toNonUnitalStarAlgHom_restrictLinearIsometry :
    (π.restrictLinearIsometry hπ).toNonUnitalStarAlgHom =
      π.toNonUnitalStarAlgHom.restrictLinearIsometry hπ :=
  (rfl)

theorem restrictLinearIsometry_def (a : A) :
    π.restrictLinearIsometry hπ a = (π a).compression V.toContinuousLinearMap :=
  (rfl)

/-- The invariant linear isometry `V` intertwines `π.restrictLinearIsometry hπ` with `π`. -/
@[simp]
theorem restrictLinearIsometry_apply (a : A) (x : K) :
    V (π.restrictLinearIsometry hπ a x) = π a (V x) :=
  π.toNonUnitalStarAlgHom.restrictLinearIsometry_apply hπ a x

/-- Compressing a unital representation along an invariant linear isometry does not increase
operator norms. -/
theorem norm_restrictLinearIsometry_le (a : A) :
    ‖π.restrictLinearIsometry hπ a‖ ≤ ‖π a‖ :=
  π.toNonUnitalStarAlgHom.norm_restrictLinearIsometry_le hπ a

end Restrict

/-- If `A` is `w`-small and `𝕜` is `w`-small (for instance `𝕜 = ℂ` or `𝕜 = ℝ` in any universe
`w`), every vector `ξ : H` lies in the range of a `π`-invariant linear isometry from
`lp (fun _ : ι => 𝕜) 2` for some `ι : Type w`, regardless of the universe of `H`. -/
theorem exists_linearIsometry_mapsTo_mem_range {𝕜 A H : Type*} [RCLike 𝕜]
    [Semiring A] [StarRing A] [Algebra 𝕜 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Small.{w} A] [Small.{w} 𝕜]
    (π : A →⋆ₐ[𝕜] (H →L[𝕜] H)) (ξ : H) :
    ∃ (ι : Type w) (V : lp (fun _ : ι => 𝕜) 2 →ₗᵢ[𝕜] H),
      (∀ a, Set.MapsTo (π a) (Set.range V) (Set.range V)) ∧ ξ ∈ Set.range V :=
  π.toNonUnitalStarAlgHom.exists_linearIsometry_mapsTo_mem_range ξ

end StarAlgHom
