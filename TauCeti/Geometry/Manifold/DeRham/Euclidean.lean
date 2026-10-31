/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Geometry.Manifold.DeRham.ExtendByZero
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DeRham.Sphere
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Compactly supported de Rham cohomology of `ℝⁿ` below the top degree

On a finite-dimensional real normed space `E` of dimension `n`, the compactly supported de Rham
cohomology `H^k_c(E)` vanishes in every degree `k ≠ n`
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`). In degree zero and above
the dimension this is already known on every connected noncompact manifold, respectively on every
`n`-manifold; the content is the range `0 < k < n`. Compact supports are not homotopy invariant,
so this does not follow from the vanishing of `H^k_dR(E)` in positive degrees.

The proof transfers to an inner product space and runs through the complement of a large closed
ball. Let `ω` be a compactly supported closed `k`-form with `0 < k < n`, supported in the closed
ball of radius `r`. By the Poincaré lemma `ω = dη` for a smooth `(k - 1)`-form `η`, which is closed
on the complement `E \ B̄(0, r)`. That complement deformation retracts onto the sphere `Sⁿ⁻¹`
(`TauCeti.deRhamCohomology.closedBallComplEquivSphere`), whose cohomology vanishes in degrees
strictly between `0` and `n - 1`, and it is connected for `n ≥ 2`. So `η` is exact on it when
`k ≥ 2`, and constant on it when `k = 1`. A cut-off at infinity then turns `η` into a compactly
supported primitive of `ω`
(`TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms` and its
degree-zero form).

The top degree `H^n_c(E) ≅ ℝ`, through integration, is not treated here.

## Main results

* `TauCeti.subsingleton_compactlySupportedDeRhamCohomology_normedSpace`: `H^k_c(E) = 0` for
  `k ≠ dim E`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, *Cohomology with Compact
  Support*, Theorem 17.28 (the compactly supported cohomology of `ℝⁿ`).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set TopologicalSpace Metric Module Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth function on the open subset `⊤` of `E` that vanishes near the closed ball of radius
`R` and equals one off a larger ball: one minus a bump function. -/
private theorem exists_cutoff_compl_closedBall (R : ℝ) :
    ∃ ρ : (⊤ : Opens E) → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ ∧
      (∀ x : (⊤ : Opens E), (x : E) ∉
          (⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩ : Opens E) →
        ∀ᶠ y in 𝓝 x, ρ y = 0) ∧
      HasCompactSupport fun x ↦ 1 - ρ x := by
  let b : ContDiffBump (0 : E) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun x ↦ 1 - b x, contMDiff_const.sub (b.contDiff.contMDiff.comp contMDiff_subtype_val),
    fun x hx ↦ ?_, ?_⟩
  · have hxb : (x : E) ∈ ball (0 : E) (max R 0 + 1) := by
      simp only [Opens.mem_mk, mem_compl_iff, not_not, mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      linarith [le_max_left R 0]
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds hxb)] with y hy
    simp [b.one_of_mem_closedBall (ball_subset_closedBall hy)]
  · simpa [Function.comp_def] using b.hasCompactSupport.comp_homeomorph
      (Diffeomorph.ofTop (I := 𝓘(ℝ, E)) (n := ∞) ⊤ rfl).toHomeomorph

/-- On a finite-dimensional real inner product space `E`, read as the open subset `⊤` of itself,
every compactly supported closed form of degree `0 < k < dim E` is the exterior derivative of a
compactly supported form. -/
private theorem mem_exactCompactlySupportedForms_top {k : ℕ} (hk : 0 < k)
    (hkE : k < finrank ℝ E) {φ : SmoothForm 𝓘(ℝ, E) (⊤ : Opens E) ℝ k}
    (hφ : φ ∈ compactlySupportedClosedForms 𝓘(ℝ, E) (⊤ : Opens E) k) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, E) (⊤ : Opens E) k := by
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ E = n + 1 := ⟨finrank ℝ E - 1, by omega⟩
  have : Fact (finrank ℝ E = n + 1) := ⟨hn⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hφc, hφd⟩ := (mem_compactlySupportedClosedForms _).mp hφ
  -- `⊤` is diffeomorphic to `E`, so by the Poincaré lemma `φ = dη` for a smooth form `η`.
  let Φ : (⊤ : Opens E) ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E := Diffeomorph.ofTop _ rfl
  have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) (j + 1)) :=
    have := subsingleton_deRhamCohomology_normedSpace E j
    (deRhamCohomology.equivOfDiffeomorph Φ (j + 1)).symm.toEquiv.subsingleton
  have hφe := (deRhamCohomology.mk_eq_zero_iff _ _ ⟨φ, hφd⟩).mp (Subsingleton.elim _ _)
  rw [exactForms_succ] at hφe
  obtain ⟨η, rfl⟩ := hφe
  -- `dη` is supported in a closed ball of radius `R ≥ 0`; let `U` be its complement.
  obtain ⟨r, hr⟩ := (((mem_compactlySupportedForms _).mp hφc).image
    continuous_subtype_val).isBounded.subset_closedBall 0
  set R := max r 0
  have hR : 0 ≤ R := le_max_right r 0
  let U : Opens E := ⟨(closedBall (0 : E) R)ᶜ, isClosed_closedBall.isOpen_compl⟩
  have hUW : U ≤ ⊤ := le_top
  -- The form `η` is closed on `U`, where `dη` vanishes.
  have hηU : SmoothForm.mpullback (Opens.inclusion hUW) (contMDiff_inclusion hUW) η ∈
      closedForms 𝓘(ℝ, E) U j := by
    rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback]
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [SmoothForm.coe_mpullback, mpullback_inclusion_apply]
    -- The value of `dη` vanishes off its support; the two zeros differ only through the
    -- identification of the fibre at `x` with the model fibre.
    refine (image_eq_zero_of_notMem_tsupport fun hx ↦ x.2 ?_).trans rfl
    exact closedBall_subset_closedBall (le_max_left r 0) (hr ⟨_, hx, rfl⟩)
  obtain ⟨ρ, hρ, hρU, hρc⟩ := exists_cutoff_compl_closedBall (E := E) R
  rcases j with _ | j
  · -- In degree one, `η` is a function, constant on the connected set `U`.
    have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp <|
      isPreconnected_compl_closedBall (by rw [← finrank_eq_rank]; exact_mod_cast hkE) 0 R
    have hUc : IsCompact {x : (⊤ : Opens E) | (x : E) ∉ U} := by
      have : {x : (⊤ : Opens E) | (x : E) ∉ U} = Φ ⁻¹' closedBall 0 R := by
        ext x
        simp [U, Φ]
      rw [this]
      exact Φ.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 R)
    exact mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_closedForms hUW hUc hηU
  · -- In degree `j + 2 < dim E`, the class of `η` on `U ≃ Sⁿ` vanishes.
    have : Subsingleton (deRhamCohomology 𝓘(ℝ, E) U (j + 1)) :=
      have := subsingleton_deRhamCohomology_sphere (E := E) (n := n) (k := j + 1) j.succ_pos
        (by omega)
      (deRhamCohomology.closedBallComplEquivSphere E n hR (j + 1)).toEquiv.subsingleton
    exact mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms hUW hρ hρU hρc
      ((deRhamCohomology.mk_eq_zero_iff _ _ ⟨_, hηU⟩).mp (Subsingleton.elim _ _))

/-- `H^k_c(E) = 0` for `0 < k < dim E`, on a finite-dimensional real inner product space `E`. -/
private theorem subsingleton_compactlySupportedDeRhamCohomology_innerProductSpace {k : ℕ}
    (hk : 0 < k) (hkE : k < finrank ℝ E) :
    Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) := by
  have : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) (⊤ : Opens E) k) := by
    refine subsingleton_of_forall_eq 0 fun c ↦ ?_
    obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ k c
    exact (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ k φ).mpr
      (mem_exactCompactlySupportedForms_top hk hkE φ.2)
  exact (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop (⊤ : Opens E) rfl) k).toEquiv.subsingleton

end InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The compactly supported de Rham cohomology of `ℝⁿ` vanishes outside the top degree.** On a
finite-dimensional real normed space `E`, `H^k_c(E) = 0` for every `k ≠ dim E`. -/
theorem subsingleton_compactlySupportedDeRhamCohomology_normedSpace {k : ℕ}
    (hk : k ≠ finrank ℝ E) : Subsingleton (compactlySupportedDeRhamCohomology 𝓘(ℝ, E) E k) := by
  rcases hk.lt_or_gt with hk | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · have : Nontrivial E := Module.nontrivial_of_finrank_pos hk
      exact subsingleton_compactlySupportedDeRhamCohomology_zero 𝓘(ℝ, E) E
    -- Transfer from the Euclidean space of the same dimension.
    have := subsingleton_compactlySupportedDeRhamCohomology_innerProductSpace
      (E := EuclideanSpace ℝ (Fin (finrank ℝ E))) hk₀ (by rwa [finrank_euclideanSpace_fin])
    exact (compactlySupportedDeRhamCohomology.equivOfDiffeomorph
      (toEuclidean (E := E)).toDiffeomorph k).symm.toEquiv.subsingleton
  · exact subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt 𝓘(ℝ, E) E hk

end TauCeti
