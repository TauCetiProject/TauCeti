/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Hypersurfaces transverse to a tangent vector

Let `M` be a smooth manifold with finite-dimensional real model space `E` of dimension `m + 1`, and
let `v` be a nonzero tangent vector at an interior point `x` of `M`. This file constructs a smooth
map `ι : ℝᵐ → M`, defined on the whole Euclidean space `EuclideanSpace ℝ (Fin m)`, with `ι 0 = x`,
injective differential at `0` and `v` not in the image of that differential
(`TauCeti.exists_contMDiff_notMem_range_mfderiv`). So near `0` it parametrizes a hypersurface
through `x` transverse to `v`.

Such slices are the starting point of flow-box arguments: flowing out of a hypersurface transverse
to a vector field gives coordinates in which the field is a coordinate vector field. The map is
defined on the whole Euclidean space, so it can be fed to constructions which require a globally
smooth map, such as the local flow map `(s, t) ↦ φₜ(ι s)` of a vector field.

The construction composes a global parametrization of a neighbourhood of `x` by `ℝᵐ⁺¹`
(`TauCeti.exists_opens_diffeomorph_euclideanSpace`), whose differential at the preimage `y₀` of
`x` is a linear isomorphism `A`, with an affine map `y ↦ y₀ + L y`, where `L` is a linear
isomorphism of `ℝᵐ` onto a complement of the line through `A⁻¹ v`.
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Hypersurfaces transverse to a tangent vector.** Let `v` be a nonzero tangent vector at an
interior point `x` of a manifold of dimension `m + 1`. Then some smooth map `ι : ℝᵐ → M` sends `0`
to `x`, has injective differential at `0`, and `v` does not lie in the image of that
differential. -/
theorem exists_contMDiff_notMem_range_mfderiv {m : ℕ} (hm : m + 1 = finrank ℝ E) {x : M}
    (hx : I.IsInteriorPoint x) {v : TangentSpace I x} (hv : v ≠ 0) :
    ∃ ι : EuclideanSpace ℝ (Fin m) → M, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ ι ∧
      ι 0 = x ∧ Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ι 0) ∧
      v ∉ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ι 0).range := by
  set N := EuclideanSpace ℝ (Fin (finrank ℝ E))
  obtain ⟨U, hxU, ⟨D⟩⟩ := exists_opens_diffeomorph_euclideanSpace (n := ⊤) hx
  -- A global smooth parametrization `ψ` of the neighbourhood `U` of `x`, a local diffeomorphism.
  set ψ : N → M := Subtype.val ∘ D.symm
  have hψ : IsLocalDiffeomorph 𝓘(ℝ, N) I ∞ ψ := fun y ↦
    (D.symm.isLocalDiffeomorph y).comp (hg := isLocalDiffeomorph_subtype_val (D.symm y))
  set y₀ : N := D ⟨x, hxU⟩
  -- The differential of `ψ` at `y₀` is a linear isomorphism `A`; pull `v` back along it.
  set A : N ≃L[ℝ] TangentSpace I (ψ y₀) := hψ.mfderivToContinuousLinearEquiv (by simp) y₀
  have hA : (A : N →L[ℝ] TangentSpace I (ψ y₀)) = mfderiv 𝓘(ℝ, N) I ψ y₀ :=
    hψ.mfderivToContinuousLinearEquiv_coe _ y₀
  set w : N := A.symm v
  have hw : w ≠ 0 := (map_ne_zero_iff _ A.symm.injective).2 hv
  -- A complement `K` of the line through `w`, of dimension `m`.
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl (ℝ ∙ w)
  have hKdim : finrank ℝ K = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hK
    rw [finrank_span_singleton hw, finrank_euclideanSpace_fin] at h
    omega
  set L : EuclideanSpace ℝ (Fin m) →L[ℝ] N := K.subtypeL ∘L
    (LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin m)) K
      (by rw [finrank_euclideanSpace_fin, hKdim])).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : Function.Injective L := fun a b hab ↦ by simpa [L] using hab
  have hLK (a : EuclideanSpace ℝ (Fin m)) : L a ∈ K := by simp [L]
  -- The slice is `ι y = ψ (y₀ + L y)`, with differential `A ∘ L` at `0`.
  have hshift : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, N) ∞ (fun y ↦ y₀ + L y) :=
    (contDiff_const.add L.contDiff).contMDiff
  have hd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I (ψ ∘ fun y ↦ y₀ + L y) 0 =
      (mfderiv 𝓘(ℝ, N) I ψ y₀).comp L := by
    rw [mfderiv_comp (0 : EuclideanSpace ℝ (Fin m))
      ((hψ.contMDiff.mdifferentiable (by simp)) _) (hshift.mdifferentiable (by simp) 0),
      mfderiv_eq_fderiv, map_zero, add_zero]
    congr 1
    have hfd : fderiv ℝ (fun y ↦ y₀ + L y) 0 = L :=
      ((hasFDerivAt_const y₀ (0 : EuclideanSpace ℝ (Fin m))).add L.hasFDerivAt).fderiv.trans
        (by simp)
    rw [hfd]
    -- The `NormedSpace.fromTangentSpace` identifications around `L` are identities.
    rfl
  refine ⟨ψ ∘ fun y ↦ y₀ + L y, hψ.contMDiff.comp hshift, by simp [ψ, y₀], ?_, ?_⟩
  · rw [hd, ← hA]
    exact A.injective.comp hL
  · -- A preimage `a` of `v` under `A ∘ L` would put `w = L a` in `K`, which meets the line through
    -- `w` only in `0`.
    rintro ⟨a, ha⟩
    rw [hd, ← hA] at ha
    have hwa : w = L a := by
      simp only [w, ← ha]
      exact A.symm_apply_apply (L a)
    have : w ∈ (ℝ ∙ w) ⊓ K := ⟨Submodule.mem_span_singleton_self w, hwa ▸ hLK a⟩
    rw [hK.inf_eq_bot, Submodule.mem_bot] at this
    exact hw this

end TauCeti
