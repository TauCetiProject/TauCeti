/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Local Sobolev maps under biholomorphisms of the source

Let `f : X' → X` be a biholomorphism of Riemann surfaces, given as a `C^n` diffeomorphism for the
models `𝓘(ℂ)` with `1 ≤ n`. A map `u : X → M` is in the local Sobolev class `W^{k,p}_loc` on
`s ⊆ X` exactly when `u ∘ f` is in it on `f ⁻¹' s`, for every order `k` and exponent `p`
(`Diffeomorph.memWkpLocMapOn_comp_diffeomorph_iff`).

No change of variables is involved: the class tests every chart of the maximal holomorphic atlas,
and the holomorphic charts of `X'` are exactly the charts `f ≫ φ` for holomorphic charts `φ` of
`X`. In such a pair of charts the coordinate expressions of `u` and of `u ∘ f` are the same map on
the same set. Composition on the target side is `Diffeomorph.memWkpLocMapOn_diffeomorph_comp_iff`.

## Main results

* `TauCeti.MemWkpLocMapOn.comp_diffeomorph`, `TauCeti.MemWkpLocMap.comp_diffeomorph`: the
  class is preserved by precomposition with a biholomorphism.
* `Diffeomorph.memWkpLocMapOn_comp_diffeomorph_iff`,
  `Diffeomorph.memWkpLocMap_comp_diffeomorph_iff`: and reflected.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set
open scoped Manifold ContDiff

noncomputable section

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {m n : WithTop ℕ∞}

/-- A chart `φ` of the maximal `C^m` atlas of `N` pulls back along a `C^n` diffeomorphism
`f : M → N`, for `m ≤ n`, to a chart `φ'` of the maximal `C^m` atlas of `M` with the same target
and with `f ∘ φ'⁻¹ = φ⁻¹`, namely `f ≫ φ`. -/
theorem exists_mem_maximalAtlas_comp_symm_eq [IsManifold I m M] (f : M ≃ₘ^n⟮I, I⟯ N)
    (hmn : m ≤ n) {φ : OpenPartialHomeomorph N H} (hφ : φ ∈ IsManifold.maximalAtlas I m N) :
    ∃ φ' ∈ IsManifold.maximalAtlas I m M, φ'.target = φ.target ∧ f ∘ φ'.symm = φ.symm := by
  have hΦ : (f.toPartialDiffeomorph.ofLE hmn).toOpenPartialHomeomorph =
      f.toHomeomorph.toOpenPartialHomeomorph :=
    OpenPartialHomeomorph.toPartialEquiv_injective (by
      dsimp only
      rw [PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
        PartialDiffeomorph.ofLE_toPartialEquiv, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
      rfl)
  have hφ' := (f.toPartialDiffeomorph.ofLE hmn).trans_mem_maximalAtlas hφ
  rw [hΦ] at hφ'
  refine ⟨_, hφ', ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_target]
    exact inter_univ _
  · rw [OpenPartialHomeomorph.coe_trans_symm]
    funext z
    exact f.apply_symm_apply _

end Diffeomorph

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace ℂ X']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X} {n : WithTop ℕ∞}

/-- **Precomposition with a biholomorphism.** If `u` is a local Sobolev map on `s` and
`f : X' → X` is a biholomorphism, then `u ∘ f` is a local Sobolev map on `f ⁻¹' s`, of the same
order and exponent. -/
theorem MemWkpLocMapOn.comp_diffeomorph (hu : MemWkpLocMapOn I p k u s)
    (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) : MemWkpLocMapOn I p k (u ∘ f) (f ⁻¹' s) := by
  refine memWkpLocMapOn_iff.2
    ⟨hu.continuousOn.comp f.continuous.continuousOn (mapsTo_preimage _ _), fun φ' hφ' ψ hψ ↦ ?_⟩
  -- A chart `φ` of `X` with `f⁻¹ ∘ φ⁻¹ = φ'⁻¹` reads `u` exactly as `φ'` reads `u ∘ f`.
  obtain ⟨φ, hφ, htarget, hcomp⟩ := f.symm.exists_mem_maximalAtlas_comp_symm_eq hn hφ'
  have hsymm : ⇑φ.symm = f ∘ φ'.symm := by
    rw [← hcomp]
    funext z
    exact (f.apply_symm_apply _).symm
  have h := hu.memWkpLoc_chart hφ hψ
  rw [htarget, hsymm] at h
  exact h

/-- **Precomposition with a biholomorphism.** If `u` is a local Sobolev map and `f : X' → X` is a
biholomorphism, then `u ∘ f` is a local Sobolev map of the same order and exponent. -/
theorem MemWkpLocMap.comp_diffeomorph (hu : MemWkpLocMap I p k u)
    (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) : MemWkpLocMap I p k (u ∘ f) := by
  have h : MemWkpLocMapOn I p k u univ := memWkpLocMapOnGroupoid_univ.2 hu
  simpa only [preimage_univ, memWkpLocMapOnGroupoid_univ] using h.comp_diffeomorph f hn

end TauCeti

namespace Diffeomorph

open TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {X' : Type*} [TopologicalSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) 1 X']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X} {n : WithTop ℕ∞}

/-- **Invariance under biholomorphisms of the source.** For a biholomorphism `f : X' → X`, a map
`u : X → M` is a local Sobolev map on `s` exactly when `u ∘ f` is one on `f ⁻¹' s`, for every
order `k` and exponent `p`. -/
theorem memWkpLocMapOn_comp_diffeomorph_iff (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    MemWkpLocMapOn I p k (u ∘ f) (f ⁻¹' s) ↔ MemWkpLocMapOn I p k u s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_diffeomorph f hn⟩
  simpa [Function.comp_def, preimage_preimage] using h.comp_diffeomorph f.symm hn

/-- **Invariance under biholomorphisms of the source.** For a biholomorphism `f : X' → X`, a map
`u : X → M` is a local Sobolev map exactly when `u ∘ f` is one, for every order `k` and exponent
`p`. -/
theorem memWkpLocMap_comp_diffeomorph_iff (f : X' ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ X) (hn : 1 ≤ n) :
    MemWkpLocMap I p k (u ∘ f) ↔ MemWkpLocMap I p k u := by
  simpa only [preimage_univ, memWkpLocMapOnGroupoid_univ] using
    f.memWkpLocMapOn_comp_diffeomorph_iff (I := I) (p := p) (k := k) (u := u) (s := univ) hn

end Diffeomorph
