/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic

/-!
# Uniqueness of minimal realizations

Any two minimal realizations of the same matrix are isomorphic: there is a linear equivalence of
the ambient spaces carrying each simple coroot to the corresponding simple coroot and each simple
root to the corresponding simple root. This is the uniqueness half of Kac's Proposition 1.1.

The isomorphism is obtained from a more general embedding statement. A *compatible* linear map
from one realization to another is one carrying coroots to coroots and pulling roots back to roots.
Such maps exist between any two realizations of the same matrix
(`CartanRealization.exists_linearMap_coroot_root`), and every compatible map out of a minimal
realization is injective (`CartanRealization.IsMinimal.injective_of_coroot_root`). Thus a minimal
realization embeds into every realization of the same matrix, and between two
minimal realizations a compatible map is an isomorphism
(`CartanRealization.IsMinimal.exists_map_eq`). Conversely every transport of a minimal realization
is minimal, so the minimal realizations of a matrix form a single isomorphism class
(`CartanRealization.IsMinimal.isMinimal_iff_exists_map_eq`).

The isomorphism is not unique when the matrix is singular: adding to the identity any linear map
that kills the coroot span and takes values in the Cartan center gives another one. In affine type
`A₁⁽¹⁾`, for instance, the degree element `d` may be sent to `d + c`, with `c = h₀ + h₁` central.

The mathematical source is V. G. Kac, *Infinite-dimensional Lie algebras*, third edition,
§1.1 and Proposition 1.1.
-/

public section

open Module

namespace TauCeti.CartanRealization

variable {I K H H' : Type*} [Fintype I] [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup H'] [Module K H'] {A : Matrix I I K} (R : CartanRealization A H)
  (S : CartanRealization A H')

omit [Fintype I] in
/-- Every realization admits a compatible linear map to any realization of the same matrix:
coroots go to coroots and roots pull back to roots. Neither ambient space need be
finite-dimensional. -/
theorem exists_linearMap_coroot_root [Finite I] :
    ∃ f : H →ₗ[K] H', (∀ i, f (R.coroot i) = S.coroot i) ∧
      ∀ i h, S.root i (f h) = R.root i h := by
  let := Fintype.ofFinite I
  obtain ⟨r, hr⟩ := R.corootMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr R.corootMap_injective)
  obtain ⟨σ, hσ⟩ := S.rootEvaluation.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr S.rootEvaluation_surjective)
  -- A map compatible with the roots, through a right inverse of the root evaluation of `S`.
  obtain ⟨g, hg⟩ : ∃ g : H →ₗ[K] H', ∀ h i, S.root i (g h) = R.root i h :=
    ⟨σ ∘ₗ R.rootEvaluation, fun h i => by
      simpa using congrFun (LinearMap.congr_fun hσ (R.rootEvaluation h)) i⟩
  -- Correct `g` on the coroot span through the left inverse `r` of the coroot embedding;
  -- the correction term is killed by every root.
  have hrc (c : I → K) : r (R.corootMap c) = c := LinearMap.congr_fun hr c
  refine ⟨g + (S.corootMap - g ∘ₗ R.corootMap) ∘ₗ r, fun i => ?_, fun i h => ?_⟩
  · classical
    have hri : r (R.coroot i) = Pi.single i 1 := by
      rw [← hrc (Pi.single i 1), corootMap_single, one_smul]
    simp [hri]
  · have hSr := congrFun (S.rootEvaluation_corootMap (r h)) i
    have hRr := congrFun (R.rootEvaluation_corootMap (r h)) i
    simp only [rootEvaluation_apply] at hSr hRr
    simp [hg, hSr, hRr]

variable {R S}

/-- Every compatible linear map out of a minimal realization is injective. -/
theorem IsMinimal.injective_of_coroot_root (hR : R.IsMinimal) {f : H →ₗ[K] H'}
    (hc : ∀ i, f (R.coroot i) = S.coroot i) (hr : ∀ i h, S.root i (f h) = R.root i h) :
    Function.Injective f := by
  have := hR.finiteDimensional
  have hcm (c : I → K) : f (R.corootMap c) = S.corootMap c := by
    simp [corootMap_apply, hc]
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  have hx' : x ∈ R.cartanCenter := (R.mem_cartanCenter_iff x).mpr fun i => by
    rw [← hr, hx, map_zero]
  obtain ⟨c, rfl⟩ := (R.mem_corootSpan_iff x).mp
    ((R.isMinimal_iff_cartanCenter_le_corootSpan.mp hR) hx')
  rw [hcm] at hx
  rw [S.corootMap_injective (hx.trans (map_zero S.corootMap).symm), map_zero]

/-- A minimal realization embeds into every realization of the same matrix, compatibly with the
coroots and the roots. -/
theorem IsMinimal.exists_injective_linearMap (hR : R.IsMinimal) (S : CartanRealization A H') :
    ∃ f : H →ₗ[K] H', Function.Injective f ∧ (∀ i, f (R.coroot i) = S.coroot i) ∧
      ∀ i h, S.root i (f h) = R.root i h := by
  obtain ⟨f, hc, hr⟩ := R.exists_linearMap_coroot_root S
  exact ⟨f, hR.injective_of_coroot_root hc hr, hc, hr⟩

/-- Any two minimal realizations of the same matrix are isomorphic: one is the transport of the
other along a linear equivalence of the ambient spaces. The equivalence is not unique in general. -/
theorem IsMinimal.exists_map_eq (hR : R.IsMinimal) (hS : S.IsMinimal) :
    ∃ e : H ≃ₗ[K] H', R.map e = S := by
  have := hR.finiteDimensional
  have := hS.finiteDimensional
  obtain ⟨f, hf, hc, hr⟩ := hR.exists_injective_linearMap S
  let e := f.linearEquivOfInjective hf (hR.finrank_eq.trans hS.finrank_eq.symm)
  have he (h : H) : e h = f h := LinearMap.linearEquivOfInjective_apply _ _ h
  refine ⟨e, ext _ (fun i => by rw [map_coroot, he, hc]) fun i => LinearMap.ext fun h => ?_⟩
  rw [map_root_apply, ← hr, ← he, e.apply_symm_apply]

/-- Up to isomorphism a minimal realization is the only one: a realization of the same matrix is
minimal exactly when it is a transport of a given minimal one. -/
theorem IsMinimal.isMinimal_iff_exists_map_eq (hR : R.IsMinimal) :
    S.IsMinimal ↔ ∃ e : H ≃ₗ[K] H', R.map e = S := by
  refine ⟨hR.exists_map_eq, ?_⟩
  rintro ⟨e, rfl⟩
  exact (isMinimal_map R e).mpr hR

end TauCeti.CartanRealization
