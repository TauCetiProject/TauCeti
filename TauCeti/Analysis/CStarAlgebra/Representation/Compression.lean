/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compression
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Small
import TauCeti.Topology.Sequences.Small

/-!
# Compressions of ⋆-representations to invariant subspaces

Let `ρ` be a ⋆-representation of a ⋆-algebra `D` on a Hilbert space `H`, and let `V : K → H` be a
linear isometry from another Hilbert space whose range is invariant under every `ρ x`. Then the
compressions `V† ρ(x) V` form a ⋆-representation of `D` on `K`, `NonUnitalStarAlgHom.compression`
(unital when `ρ` is, `StarAlgHom.compression`), and `V` intertwines it with `ρ`.

Every vector `ξ ∈ H` lies in such an invariant range with `K` in the universe of `D`, whatever the
universe of `H`, `AlgHom.exists_isometry_mapsTo_mem_range`: the closure of the orbit `D ξ` is
invariant, and it is small in the universe of `D`, so it has a Hilbert basis indexed there. This is
the universe control for universal C⋆-norms defined as suprema over representations.
-/

public section

noncomputable section

variable {D H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace NonUnitalStarAlgHom

variable [NonUnitalNonAssocSemiring D] [Module ℂ D] [Star D]
  (ρ : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (V : K →ₗᵢ[ℂ] H)
  (hV : ∀ x, Set.MapsTo (ρ x) (Set.range V) (Set.range V))

/-- The compression `x ↦ V† ρ(x) V` of a ⋆-representation `ρ` along a linear isometry `V` whose
range is invariant under `ρ`. -/
def compression : D →⋆ₙₐ[ℂ] (K →L[ℂ] K) where
  toFun x := (ρ x).compression V.toContinuousLinearMap
  map_smul' c x := by simp
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    simp only [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.compression_def]
    exact V.isPartialIsometry_toContinuousLinearMap.adjoint_comp_comp_comp_of_mapsTo _ (hV y)
  map_star' x := by
    simp only [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_compression]

theorem compression_apply (x : D) :
    ρ.compression V hV x = (ρ x).compression V.toContinuousLinearMap :=
  (rfl)

/-- The isometry intertwines the compression with the original representation. -/
@[simp]
theorem apply_compression_apply (x : D) (y : K) : V (ρ.compression V hV x y) = ρ x (V y) :=
  (congrArg V ((ρ x).compression_apply V.toContinuousLinearMap y)).trans
    (V.apply_adjoint_apply_of_mem_range (hV x ⟨y, rfl⟩))

end NonUnitalStarAlgHom

namespace StarAlgHom

variable [Semiring D] [Algebra ℂ D] [Star D]
  (ρ : D →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →ₗᵢ[ℂ] H)
  (hV : ∀ x, Set.MapsTo (ρ x) (Set.range V) (Set.range V))

/-- The compression `x ↦ V† ρ(x) V` of a unital ⋆-representation `ρ` along a linear isometry `V`
whose range is invariant under `ρ`; it is unital since `V† V = 1`. -/
def compression : D →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun x := (ρ x).compression V.toContinuousLinearMap
  map_one' := by
    rw [map_one, ContinuousLinearMap.compression_one]
  map_mul' := map_mul (ρ.toNonUnitalStarAlgHom.compression V hV)
  map_zero' := map_zero (ρ.toNonUnitalStarAlgHom.compression V hV)
  map_add' := map_add (ρ.toNonUnitalStarAlgHom.compression V hV)
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.compression_smul]
  map_star' := map_star (ρ.toNonUnitalStarAlgHom.compression V hV)

theorem compression_apply (x : D) :
    ρ.compression V hV x = (ρ x).compression V.toContinuousLinearMap :=
  (rfl)

/-- The isometry intertwines the compression with the original representation. -/
@[simp]
theorem apply_compression_apply (x : D) (y : K) : V (ρ.compression V hV x y) = ρ x (V y) :=
  ρ.toNonUnitalStarAlgHom.apply_compression_apply V hV x y

end StarAlgHom

namespace AlgHom

universe u w

/-- Every vector of a representation `ρ` of an algebra `D : Type u` on a Hilbert space in any
universe lies in the range of a linear isometry from a Hilbert space in the universe `u` whose
range is invariant under `ρ`: the closure of the orbit `D ξ` of the vector. -/
theorem exists_isometry_mapsTo_mem_range {D : Type u} {H : Type w} [Semiring D] [Algebra ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : D →ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (V : K →ₗᵢ[ℂ] H),
        (∀ x, Set.MapsTo (ρ x) (Set.range V) (Set.range V)) ∧ ξ ∈ Set.range V := by
  -- `S` is the orbit `D ξ`, a submodule, and `W` its closure.
  let S := LinearMap.range
    ((ContinuousLinearMap.apply ℂ H ξ : (H →L[ℂ] H) →ₗ[ℂ] H) ∘ₗ (ρ : D →ₗ[ℂ] (H →L[ℂ] H)))
  let W := S.topologicalClosure
  have hS (x) : Set.MapsTo (ρ x) S S := by
    rintro _ ⟨y, rfl⟩
    exact ⟨x * y, by simp⟩
  have : Small.{u} (W : Set H) := by
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range]
    exact Set.small_closure _
  obtain ⟨K, _, _, _, V, hV⟩ := W.exists_linearIsometry_range_eq
  refine ⟨K, inferInstance, inferInstance, inferInstance, V, fun x => ?_, ?_⟩
  all_goals rw [hV]
  · simpa [W, Submodule.topologicalClosure_coe] using (hS x).closure (ρ x).continuous
  · exact S.le_topologicalClosure ⟨1, by simp⟩

end AlgHom
